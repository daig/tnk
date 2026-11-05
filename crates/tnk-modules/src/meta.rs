//! META-LEVEL and LEXICAL descent implementation.
//!
//! A [`MetaOp`] redex enters through the kernel's [`MetaCtx`] seam. [`MetaDescent`] combines the
//! module/view databases, shared interner, and session state needed to down-translate a meta-module into
//! an ordinary [`LoadedModule`], decode terms in that module, run the requested engine operation, and
//! construct the up-translated result in the caller's engine.
//!
//! Supported groups include reduction, rewriting, matching, application and search; unification,
//! variants and narrowing; SMT checking/search and variant satisfiability; module/sort queries and
//! well-formedness; module/view/term reflection; syntax and lexical operations; and strategic rewriting
//! plus strategy declaration/definition reflection. Inline and named meta-modules share the normal
//! flatten-and-build path. Flat reflection inlines an import closure; non-flat reflection uses the
//! module's own declarations and imports.
//!
//! Dispatch covers every [`MetaOp`]. Inputs outside a handler's current contract leave the redex
//! unreduced; finite enumerations use their protocol-specific failure constructors.

use std::cmp::Ordering;
use std::collections::{BTreeSet, HashMap};
use std::rc::Rc;

use tnk_core::dag::{DagId, NaValue, NodeRepr};
use tnk_core::descent::{DescentOps, MetaCtx};
use tnk_core::engine::Engine;
use tnk_core::host::{HostFunctionCatalog, ReducerFault};
use tnk_core::search::Arrow;
use tnk_core::smt::{ConfiguredSmtEngine, SmtEngine, SmtNumber, SmtResult};
use tnk_core::sort::SortId;
use tnk_core::symbol::{MetaHooks, MetaOp, SymbolId};
use tnk_core::term::{ConditionFragment, Equation, Membership, Term};
use tnk_core::variant_sat::{
    ConstructorAnalysis, Decision as VariantSatDecision, EligibilityRejection, Formula,
    Literal as VariantSatLiteral, SortOverrides, VariantSatQuery, decide as decide_variant_sat,
};
use tnk_frontend::build_term::{VarIndex, unquote_string};
use tnk_frontend::lex::{Interner, Sym, Token, tokenize};
use tnk_frontend::load::{
    InternerNames, LoadedModule, LoadedModuleBuildError, StatementTraceRef, StmtTrace,
    build_command_dag, build_logic_command_parses, command_parse_furthest,
    executable_variant_equations, maude_variable_name_rank, parse_command_term,
    parse_statement_trace, try_build_loaded_module_homed_traced_with_host_functions,
    try_build_loaded_module_with_host_functions,
    try_build_loaded_module_with_host_functions_and_inline_statements,
};
use tnk_frontend::pretty::{
    PrintOptions, print_qid_tokens_with_options, print_raw, print_term, print_with_options,
    render_float, render_string,
};
use tnk_frontend::sig::build_sig::{canonical_name, first_kind_component};
use tnk_frontend::sig::syntax::{BuiltModule, EqTrace, MbTrace, RlTrace};
use tnk_frontend::strategy::{StratSolution, StrategicRewriteError, srewrite_dag};
use tnk_frontend::surface::ast::{
    Attrs, GatherElem, IdSide, Import, ImportMode, ModuleExpr, ModuleKind, OpDecl, OpMap,
    Parameter, PreModule, RenameItem, SpecialSpec, Statement, StratDecl, StratDef, StratExpr,
    StratSugar, TestKind, ViewDecl,
};

use crate::db::ModuleDb;
use crate::flatten::{flatten, flatten_pre, flatten_with_homes};
use crate::view::ViewDb;

const META_CACHE_CAPACITY: usize = 4;

type MetaXapplySolution = (
    Vec<usize>,
    usize,
    Vec<DagId>,
    DagId,
    Option<(Vec<DagId>, Vec<DagId>)>,
);
/// Last transferred symbolic rewrite subcounts for a resumable cached engine.
#[derive(Default)]
struct SymbolicRewriteCheckpoint {
    variant_narrowing: u64,
    narrowing: u64,
}

fn take_symbolic_subcounts(
    engine: &Engine,
    checkpoint: &mut SymbolicRewriteCheckpoint,
) -> (u64, u64) {
    let (_, _, variant_narrowing, narrowing) = engine.rewrite_breakdown();
    let delta = (
        variant_narrowing.saturating_sub(checkpoint.variant_narrowing),
        narrowing.saturating_sub(checkpoint.narrowing),
    );
    checkpoint.variant_narrowing = variant_narrowing;
    checkpoint.narrowing = narrowing;
    delta
}

fn capture_reducer_fault<T>(
    slot: &mut Option<ReducerFault>,
    result: Result<T, ReducerFault>,
) -> Option<T> {
    match result {
        Ok(value) => Some(value),
        Err(fault) => {
            debug_assert!(slot.is_none());
            *slot = Some(fault);
            None
        }
    }
}
fn capture_loaded_module_build<T>(
    slot: &mut Option<ReducerFault>,
    result: Result<T, LoadedModuleBuildError>,
    invalid: impl FnOnce(&str),
) -> Option<T> {
    match result {
        Ok(value) => Some(value),
        Err(LoadedModuleBuildError::Reducer(fault)) => {
            debug_assert!(slot.is_none());
            *slot = Some(fault);
            None
        }
        Err(LoadedModuleBuildError::Invalid(error)) => {
            invalid(&error);
            None
        }
    }
}

fn capture_variant_error<T>(
    slot: &mut Option<ReducerFault>,
    result: Result<T, tnk_core::variant::VariantSearchError>,
) -> Option<T> {
    match result {
        Ok(value) => Some(value),
        Err(tnk_core::variant::VariantSearchError::Reducer(fault)) => {
            debug_assert!(slot.is_none());
            *slot = Some(fault);
            None
        }
        Err(tnk_core::variant::VariantSearchError::Invalid(_)) => None,
    }
}

fn capture_narrow_error<T>(
    slot: &mut Option<ReducerFault>,
    result: Result<T, tnk_core::narrow::NarrowSearchError>,
) -> Option<T> {
    match result {
        Ok(value) => Some(value),
        Err(tnk_core::narrow::NarrowSearchError::Reducer(fault)) => {
            debug_assert!(slot.is_none());
            *slot = Some(fault);
            None
        }
        Err(tnk_core::narrow::NarrowSearchError::Invalid(_)) => None,
    }
}

fn transfer_symbolic_subcounts(
    ctx: &mut MetaCtx,
    engine: &Engine,
    checkpoint: &mut SymbolicRewriteCheckpoint,
) {
    let (variant_narrowing, narrowing) = take_symbolic_subcounts(engine, checkpoint);
    ctx.add_variant_narrowing_subcount(variant_narrowing);
    ctx.add_narrowing_subcount(narrowing);
}

struct ReflectedModule {
    root: tnk_core::root::RootGuard,
    source: String,
    flat: bool,
}

/// Session state for resumable metalevel searches and recognized module reflections.
/// Rooted DAG keys are discarded when the owning [`MetaCtx`] changes.
#[derive(Default)]
pub struct MetaState {
    caches: Vec<MetaCache>,
    reflected_modules: Vec<ReflectedModule>,
    context_id: Option<usize>,
}

impl MetaState {
    /// Drop all cached searches and reflected-module roots tied to the current metalevel context.
    pub fn clear(&mut self) {
        self.caches.clear();
        self.reflected_modules.clear();
        self.context_id = None;
    }

    fn ensure_context(&mut self, ctx: &MetaCtx) {
        let context_id = ctx.context_id();
        if self.context_id != Some(context_id) {
            self.clear();
            self.context_id = Some(context_id);
        }
    }

    fn remember_reflection(
        &mut self,
        ctx: &mut MetaCtx,
        module: DagId,
        source: String,
        flat: bool,
    ) {
        self.reflected_modules
            .retain(|entry| !ctx.deep_equal(entry.root.get(), module));
        if self.reflected_modules.len() == META_CACHE_CAPACITY {
            self.reflected_modules.remove(0);
        }
        self.reflected_modules.push(ReflectedModule {
            root: ctx.root(module),
            source,
            flat,
        });
    }

    fn reflected_source(&self, ctx: &MetaCtx, module: DagId) -> Option<(String, bool)> {
        self.reflected_modules
            .iter()
            .rev()
            .find(|entry| ctx.deep_equal(entry.root.get(), module))
            .map(|entry| (entry.source.clone(), entry.flat))
    }

    fn take_get_variant(
        &mut self,
        key: &MetaGetVariantCacheKey,
        ctx: &MetaCtx,
        requested: usize,
    ) -> Option<MetaGetVariantCache> {
        let index = self.caches.iter().position(
            |entry| matches!(entry, MetaCache::Get(cache) if cache.key.matches(key, ctx)),
        )?;
        let MetaCache::Get(cache) = self.caches.remove(index) else {
            unreachable!("cache kind checked above")
        };
        cache
            .last_solution
            .is_none_or(|last| last <= requested)
            .then_some(cache)
    }

    fn take_variant_unify(
        &mut self,
        key: &MetaVariantUnifyCacheKey,
        ctx: &MetaCtx,
        requested: usize,
    ) -> Option<MetaVariantUnifyCache> {
        let index = self.caches.iter().position(
            |entry| matches!(entry, MetaCache::Unify(cache) if cache.key.matches(key, ctx)),
        )?;
        let MetaCache::Unify(cache) = self.caches.remove(index) else {
            unreachable!("cache kind checked above")
        };
        cache
            .last_solution
            .is_none_or(|last| last <= requested)
            .then_some(cache)
    }

    fn take_narrow_apply(
        &mut self,
        key: &MetaNarrowApplyCacheKey,
        ctx: &MetaCtx,
        requested: usize,
    ) -> Option<MetaNarrowApplyCache> {
        let index = self.caches.iter().position(
            |entry| matches!(entry, MetaCache::NarrowApply(cache) if cache.key.matches(key, ctx)),
        )?;
        let MetaCache::NarrowApply(cache) = self.caches.remove(index) else {
            unreachable!("cache kind checked above")
        };
        cache
            .last_solution
            .is_none_or(|last| last <= requested)
            .then_some(cache)
    }

    fn take_narrow_search(
        &mut self,
        key: &MetaNarrowSearchCacheKey,
        ctx: &MetaCtx,
        requested: usize,
    ) -> Option<MetaNarrowSearchCache> {
        let index = self.caches.iter().position(
            |entry| matches!(entry, MetaCache::NarrowSearch(cache) if cache.key.matches(key, ctx)),
        )?;
        let MetaCache::NarrowSearch(cache) = self.caches.remove(index) else {
            unreachable!("cache kind checked above")
        };
        cache
            .last_solution
            .is_none_or(|last| last <= requested)
            .then_some(cache)
    }

    fn take_narrow_result(
        &mut self,
        key: &MetaNarrowResultCacheKey,
        ctx: &MetaCtx,
        requested: usize,
    ) -> Option<MetaNarrowResultCache> {
        let index = self.caches.iter().position(
            |entry| matches!(entry, MetaCache::NarrowResult(cache) if cache.key.matches(key, ctx)),
        )?;
        let MetaCache::NarrowResult(cache) = self.caches.remove(index) else {
            unreachable!("cache kind checked above")
        };
        cache
            .last_solution
            .is_none_or(|last| last <= requested)
            .then_some(cache)
    }

    fn take_srewrite(
        &mut self,
        key: &MetaSrewriteCacheKey,
        ctx: &MetaCtx,
        requested: usize,
    ) -> Option<MetaSrewriteCache> {
        let index = self.caches.iter().position(
            |entry| matches!(entry, MetaCache::Srewrite(cache) if cache.key.matches(key, ctx)),
        )?;
        let MetaCache::Srewrite(cache) = self.caches.remove(index) else {
            unreachable!("cache kind checked above")
        };
        cache
            .last_solution
            .is_none_or(|last| last <= requested)
            .then_some(cache)
    }

    fn take_smt_search(
        &mut self,
        key: &MetaSmtSearchCacheKey,
        ctx: &MetaCtx,
        requested: usize,
    ) -> Option<MetaSmtSearchCache> {
        let index = self.caches.iter().position(
            |entry| matches!(entry, MetaCache::SmtSearch(cache) if cache.key.matches(key, ctx)),
        )?;
        let MetaCache::SmtSearch(cache) = self.caches.remove(index) else {
            unreachable!("cache kind checked above")
        };
        cache
            .last_solution_index
            .is_none_or(|last| last <= requested)
            .then_some(cache)
    }

    fn variant_sat_result(&self, key: &MetaVariantSatCacheKey, ctx: &MetaCtx) -> Option<bool> {
        self.caches.iter().find_map(|entry| match entry {
            MetaCache::VariantSat(cache) if cache.key.matches(key, ctx) => Some(cache.result),
            _ => None,
        })
    }

    fn insert(&mut self, cache: MetaCache) {
        if self.caches.len() == META_CACHE_CAPACITY {
            self.caches.remove(0);
        }
        self.caches.push(cache);
    }
}

enum MetaCache {
    Get(MetaGetVariantCache),
    Unify(MetaVariantUnifyCache),
    NarrowApply(MetaNarrowApplyCache),
    NarrowSearch(MetaNarrowSearchCache),
    NarrowResult(MetaNarrowResultCache),
    Srewrite(MetaSrewriteCache),
    SmtSearch(MetaSmtSearchCache),
    VariantSat(MetaVariantSatCache),
}

#[derive(Clone)]
struct MetaVariantSatCacheKey {
    module: DagId,
    formula: DagId,
    finite_sorts: Option<DagId>,
    infinite_sorts: Option<DagId>,
    validity: bool,
}

impl MetaVariantSatCacheKey {
    fn matches(&self, other: &Self, ctx: &MetaCtx) -> bool {
        self.validity == other.validity
            && ctx.deep_equal(self.module, other.module)
            && ctx.deep_equal(self.formula, other.formula)
            && match (self.finite_sorts, other.finite_sorts) {
                (Some(lhs), Some(rhs)) => ctx.deep_equal(lhs, rhs),
                (None, None) => true,
                _ => false,
            }
            && match (self.infinite_sorts, other.infinite_sorts) {
                (Some(lhs), Some(rhs)) => ctx.deep_equal(lhs, rhs),
                (None, None) => true,
                _ => false,
            }
    }
}

struct MetaVariantSatCache {
    key: MetaVariantSatCacheKey,
    _key_roots: Vec<tnk_core::root::RootGuard>,
    result: bool,
}

#[derive(Clone)]
struct MetaSmtSearchCacheKey {
    module: DagId,
    initial: DagId,
    goal: DagId,
    condition: DagId,
    arrow: Arrow,
    fresh_base: String,
    max_depth: Option<u32>,
}

impl MetaSmtSearchCacheKey {
    fn matches(&self, other: &Self, ctx: &MetaCtx) -> bool {
        self.arrow == other.arrow
            && self.fresh_base == other.fresh_base
            && self.max_depth == other.max_depth
            && ctx.deep_equal(self.module, other.module)
            && ctx.deep_equal(self.initial, other.initial)
            && ctx.deep_equal(self.goal, other.goal)
            && ctx.deep_equal(self.condition, other.condition)
    }
}

struct MetaSmtSearchCache {
    key: MetaSmtSearchCacheKey,
    _key_roots: Vec<tnk_core::root::RootGuard>,
    loaded: LoadedModule,
    search: tnk_core::smt_search::SmtSearch,
    goal_variables: VarIndex,
    target_variable_count: u32,
    last_solution_index: Option<usize>,
    last_solution: Option<tnk_core::smt_search::SmtSolution>,
}

#[derive(Clone)]
struct MetaNarrowApplyCacheKey {
    module: DagId,
    roots: Vec<DagId>,
    family: tnk_core::fresh::VariableFamily,
    filtered: bool,
    delayed: bool,
}

impl MetaNarrowApplyCacheKey {
    fn matches(&self, other: &Self, ctx: &MetaCtx) -> bool {
        self.family == other.family
            && self.filtered == other.filtered
            && self.delayed == other.delayed
            && ctx.deep_equal(self.module, other.module)
            && self.roots.len() == other.roots.len()
            && self
                .roots
                .iter()
                .zip(&other.roots)
                .all(|(&lhs, &rhs)| ctx.deep_equal(lhs, rhs))
    }
}

struct MetaNarrowApplyCache {
    key: MetaNarrowApplyCacheKey,
    _key_roots: Vec<tnk_core::root::RootGuard>,
    loaded: LoadedModule,
    search: tnk_core::narrow::NarrowSearch,
    variable_names: Vec<String>,
    target_variable_count: usize,
    states: Vec<usize>,
    last_solution: Option<usize>,
    rewrite_checkpoint: u64,
    breakdown_checkpoint: SymbolicRewriteCheckpoint,
}

#[derive(Clone)]
struct MetaNarrowSearchCacheKey {
    module: DagId,
    subject: DagId,
    goal: DagId,
    search_type: tnk_core::narrow::NarrowSearchType,
    max_depth: Option<usize>,
    fold: tnk_core::narrow::NarrowFold,
    filtered: bool,
    delayed: bool,
    path: bool,
}

impl MetaNarrowSearchCacheKey {
    fn matches(&self, other: &Self, ctx: &MetaCtx) -> bool {
        self.search_type == other.search_type
            && self.max_depth == other.max_depth
            && self.fold == other.fold
            && self.filtered == other.filtered
            && self.delayed == other.delayed
            && self.path == other.path
            && ctx.deep_equal(self.module, other.module)
            && ctx.deep_equal(self.subject, other.subject)
            && ctx.deep_equal(self.goal, other.goal)
    }
}

struct RootedNarrowingSolution {
    solution: tnk_core::narrow::NarrowingSolution,
    _roots: Vec<tnk_core::root::RootGuard>,
}

struct MetaNarrowSearchCache {
    key: MetaNarrowSearchCacheKey,
    _key_roots: Vec<tnk_core::root::RootGuard>,
    loaded: LoadedModule,
    search: tnk_core::narrow::NarrowSearch,
    initial_variable_names: Vec<String>,
    initial_variable_count: usize,
    solutions: Vec<RootedNarrowingSolution>,
    last_solution: Option<usize>,
    rewrite_checkpoint: u64,
    breakdown_checkpoint: SymbolicRewriteCheckpoint,
}

#[derive(Clone)]
struct MetaNarrowResultCacheKey {
    module: DagId,
    subject: DagId,
    goal: DagId,
    search_type: tnk_core::narrow::NarrowSearchType,
    max_depth: Option<usize>,
}

impl MetaNarrowResultCacheKey {
    fn matches(&self, other: &Self, ctx: &MetaCtx) -> bool {
        self.search_type == other.search_type
            && self.max_depth == other.max_depth
            && ctx.deep_equal(self.module, other.module)
            && ctx.deep_equal(self.subject, other.subject)
            && ctx.deep_equal(self.goal, other.goal)
    }
}

struct MetaNarrowResultCache {
    key: MetaNarrowResultCacheKey,
    _key_roots: Vec<tnk_core::root::RootGuard>,
    loaded: LoadedModule,
    search: tnk_core::narrow::NarrowSearch,
    goal_variables: Vec<(u32, SortId, String)>,
    solutions: Vec<RootedNarrowingSolution>,
    last_solution: Option<usize>,
    rewrite_checkpoint: u64,
    breakdown_checkpoint: SymbolicRewriteCheckpoint,
}

#[derive(Clone)]
struct MetaSrewriteCacheKey {
    module: DagId,
    subject: DagId,
    strategy: DagId,
    depth_first: bool,
}

impl MetaSrewriteCacheKey {
    fn matches(&self, other: &Self, ctx: &MetaCtx) -> bool {
        self.depth_first == other.depth_first
            && ctx.deep_equal(self.module, other.module)
            && ctx.deep_equal(self.subject, other.subject)
            && ctx.deep_equal(self.strategy, other.strategy)
    }
}

struct RootedStratSolution {
    solution: StratSolution,
    _root: tnk_core::root::RootGuard,
}

struct MetaSrewriteCache {
    key: MetaSrewriteCacheKey,
    _key_roots: Vec<tnk_core::root::RootGuard>,
    loaded: LoadedModule,
    solutions: Vec<RootedStratSolution>,
    total_rewrites: u64,
    last_solution: Option<usize>,
    rewrite_checkpoint: u64,
}

/// Executes metalevel descent against module/view databases with session-scoped caches and reflection
/// state.
pub struct MetaDescent<'a> {
    pub interner: &'a mut Interner,
    pub db: &'a ModuleDb,
    pub views: &'a ViewDb,
    host_functions: HostFunctionCatalog,
    unify_cache: Option<MetaUnifyCache>,
    state: &'a mut MetaState,
    interpreter_manager_accounting: bool,
    reducer_fault: Option<ReducerFault>,
}

#[derive(Clone, PartialEq, Eq)]
struct MetaUnifyCacheKey {
    module: DagId,
    roots: Vec<DagId>,
    family_root: &'static str,
    base: String,
    disjoint: bool,
}

struct MetaUnifyCache {
    key: MetaUnifyCacheKey,
    limit: usize,
    loaded: LoadedModule,
    specs_raw: Vec<(String, SortId)>,
    n_lhs: usize,
    original_order: Vec<usize>,
    unifiers: Vec<Vec<DagId>>,
    exhausted: bool,
    incomplete: bool,
}

#[derive(Clone)]
struct MetaGetVariantCacheKey {
    module: DagId,
    roots: Vec<DagId>,
    family: Option<tnk_core::fresh::VariableFamily>,
    base: String,
    irredundant: bool,
    nat_family: bool,
}

impl MetaGetVariantCacheKey {
    fn matches(&self, other: &Self, ctx: &MetaCtx) -> bool {
        self.family == other.family
            && self.base == other.base
            && self.irredundant == other.irredundant
            && self.nat_family == other.nat_family
            && ctx.deep_equal(self.module, other.module)
            && self.roots.len() == other.roots.len()
            && self
                .roots
                .iter()
                .zip(&other.roots)
                .all(|(&lhs, &rhs)| ctx.deep_equal(lhs, rhs))
    }
}

struct MetaGetVariantCache {
    key: MetaGetVariantCacheKey,
    _key_roots: Vec<tnk_core::root::RootGuard>,
    loaded: LoadedModule,
    search: tnk_core::variant::VariantSearch,
    variable_names: Vec<String>,
    variants: Vec<tnk_core::variant::VariantResult>,
    exhausted: bool,
    last_solution: Option<usize>,
    rewrite_checkpoint: u64,
    breakdown_checkpoint: SymbolicRewriteCheckpoint,
    rewrite_charge: u64,
}

#[derive(Clone)]
struct MetaVariantUnifyCacheKey {
    module: DagId,
    roots: Vec<DagId>,
    family: Option<tnk_core::fresh::VariableFamily>,
    base: String,
    disjoint: bool,
    nat_family: bool,
    matching: bool,
    filtered: bool,
    delayed: bool,
}

impl MetaVariantUnifyCacheKey {
    fn matches(&self, other: &Self, ctx: &MetaCtx) -> bool {
        self.family == other.family
            && (self.matching || self.base == other.base)
            && self.disjoint == other.disjoint
            && self.nat_family == other.nat_family
            && self.filtered == other.filtered
            && self.delayed == other.delayed
            && self.matching == other.matching
            && ctx.deep_equal(self.module, other.module)
            && self.roots.len() == other.roots.len()
            && self
                .roots
                .iter()
                .zip(&other.roots)
                .all(|(&lhs, &rhs)| ctx.deep_equal(lhs, rhs))
    }
}

struct MetaVariantUnifyCache {
    key: MetaVariantUnifyCacheKey,
    _key_roots: Vec<tnk_core::root::RootGuard>,
    loaded: LoadedModule,
    search: tnk_core::variant::VariantSearch,
    pair_count: usize,
    specs_raw: Vec<(String, SortId)>,
    canonical_order: Vec<usize>,
    n_lhs: usize,
    upfront: bool,
    prepared: bool,
    exhausted: bool,
    rewrite_checkpoint: u64,
    breakdown_checkpoint: SymbolicRewriteCheckpoint,
    rewrite_charge: u64,
    stream: tnk_core::variant::FilteredVariantUnifierStream,
    answers: Vec<usize>,
    deferred_variant: Option<tnk_core::variant::VariantResult>,
    restorations: Vec<(DagId, DagId)>,
    last_solution: Option<usize>,
}

impl MetaVariantUnifyCache {
    fn advance(&mut self, env: &mut tnk_core::unify::UnifyEnv<'_>) -> Result<(), ReducerFault> {
        if self.exhausted {
            return Ok(());
        }
        let pending_before = self.stream.pending_len();
        if self.key.matching {
            self.advance_matching(env)?;
        } else if let Some(variant) = self.search.try_find_next(env)? {
            debug_assert!(variant.unifier);
            let mut bindings = variant.substitution;
            if !self.restorations.is_empty() {
                for binding in &mut bindings {
                    *binding = tnk_core::variant::restore_subject_variables(
                        env.e,
                        *binding,
                        &self.restorations,
                    );
                }
            }
            let equations = self.search.variant_equations();
            let rewrites = env.e.rewrites();
            self.stream
                .try_insert(env, bindings, variant.family, rewrites, &equations)?;
        } else {
            self.exhausted = true;
        }
        if !self.upfront {
            let rewrites = env.e.rewrites();
            if self.stream.pending_len() > pending_before {
                // Direct descent charges work skipped before each surviving candidate. A terminal failure
                // leaves additional work beyond the checkpoint; interpreter-managed accounting transfers
                // that tail when reporting exhaustion.
                self.rewrite_charge += rewrites.saturating_sub(self.rewrite_checkpoint);
                self.rewrite_checkpoint = rewrites;
            }
        }
        Ok(())
    }

    fn advance_matching(
        &mut self,
        env: &mut tnk_core::unify::UnifyEnv<'_>,
    ) -> Result<(), ReducerFault> {
        let next = match self.deferred_variant.take() {
            Some(variant) => Some(variant),
            None => self.search.try_find_next(env)?,
        };
        let Some(mut variant) = next else {
            self.exhausted = true;
            return Ok(());
        };
        let root_identity = variant.index == 0
            && env
                .e
                .node(variant.term)
                .children()
                .collect::<Vec<_>>()
                .chunks_exact(2)
                .all(|pair| env.e.deep_equal(pair[0], pair[1]));
        let family = self
            .key
            .family
            .expect("metalevel variant matching has a family");
        let mut completed = Vec::new();
        loop {
            completed.extend(tnk_core::variant::try_complete_variant_unifier(
                env,
                &variant,
                self.pair_count,
                family,
                &self.key.base,
            )?);
            if root_identity {
                break;
            }
            if variant.more_in_layer {
                variant = self.search.try_find_next(env)?.expect("same variant layer");
            } else {
                self.deferred_variant = self.search.try_find_next(env)?;
                break;
            }
        }
        if !self.restorations.is_empty() {
            for bindings in &mut completed {
                for binding in bindings {
                    *binding = tnk_core::variant::restore_subject_variables(
                        env.e,
                        *binding,
                        &self.restorations,
                    );
                }
            }
        }
        let mut accepted = Vec::with_capacity(completed.len());
        for bindings in completed {
            if self
                .search
                .try_accepts_completed_unifier(env.e, &bindings)?
            {
                accepted.push(bindings);
            }
        }
        let completed = if self.stream.is_filtered() {
            accepted
        } else {
            let mut survivors: Vec<Vec<DagId>> = Vec::new();
            'candidate: for bindings in accepted {
                for retained in &survivors {
                    if tnk_core::variant::try_unifier_subsumes(env.e, retained, &bindings)? {
                        continue 'candidate;
                    }
                }
                let mut kept = Vec::with_capacity(survivors.len() + 1);
                for retained in survivors.drain(..) {
                    if !tnk_core::variant::try_unifier_subsumes(env.e, &bindings, &retained)? {
                        kept.push(retained);
                    }
                }
                kept.push(bindings);
                survivors = kept;
            }
            survivors
        };
        for bindings in completed {
            let equations = self.search.variant_equations();
            let rewrites = env.e.rewrites();
            self.stream
                .try_insert(env, bindings, family, rewrites, &equations)?;
        }
        if root_identity || self.deferred_variant.is_none() {
            self.exhausted = true;
        }
        Ok(())
    }

    fn prepare(&mut self, env: &mut tnk_core::unify::UnifyEnv<'_>) -> Result<(), ReducerFault> {
        if self.prepared {
            return Ok(());
        }
        while !self.exhausted {
            self.advance(env)?;
        }
        self.stream.finish();
        self.prepared = true;

        let rewrites = env.e.rewrites();
        if !self.stream.pending_is_empty() {
            // DELAY constructs and exhausts the filtered search before its first result. The first
            // successful extraction transfers the whole completed subcontext count.
            self.rewrite_charge += rewrites.saturating_sub(self.rewrite_checkpoint);
        }
        self.rewrite_checkpoint = rewrites;
        Ok(())
    }

    fn take_rewrite_charge(&mut self) -> u64 {
        std::mem::take(&mut self.rewrite_charge)
    }
    fn pop_pending(&mut self) -> Option<usize> {
        self.stream.pop_pending()
    }
}

impl<'a> MetaDescent<'a> {
    pub fn new(
        interner: &'a mut Interner,
        db: &'a ModuleDb,
        views: &'a ViewDb,
        state: &'a mut MetaState,
    ) -> Self {
        Self {
            interner,
            db,
            views,
            host_functions: HostFunctionCatalog::default(),
            unify_cache: None,
            state,
            reducer_fault: None,
            interpreter_manager_accounting: false,
        }
    }
    /// Use the same immutable host capability catalog as the owning Session.
    pub fn with_host_functions(mut self, host_functions: HostFunctionCatalog) -> Self {
        self.host_functions = host_functions;
        self
    }
    fn capture_semantic<T>(&mut self, result: Result<T, ReducerFault>) -> Option<T> {
        match result {
            Ok(value) => Some(value),
            Err(fault) => {
                debug_assert!(self.reducer_fault.is_none());
                self.reducer_fault = Some(fault);
                None
            }
        }
    }

    /// Enable interpreter-managed rewrite accounting. A terminal filtered-unifier failure then reports
    /// work spent proving exhaustion; direct descent reports only through the last surviving candidate.
    pub fn with_interpreter_manager_accounting(mut self) -> Self {
        self.interpreter_manager_accounting = true;
        self
    }
}

impl DescentOps for MetaDescent<'_> {
    fn descend(
        &mut self,
        ctx: &mut MetaCtx,
        op: MetaOp,
        hooks: &MetaHooks,
        redex: DagId,
    ) -> Result<Option<DagId>, ReducerFault> {
        self.state.ensure_context(ctx);
        debug_assert!(self.reducer_fault.is_none());
        let result = (|| match op {
            // `metaReduce` runs the module's equations to normal form; `metaNormalize` normalizes modulo
            // the STRUCTURAL AXIOMS ONLY (AC order, id/idem collapse — no user equations).
            MetaOp::Reduce => self.meta_reduce(ctx, hooks, redex),
            MetaOp::Normalize => self.meta_normalize(ctx, hooks, redex),
            // Rewriting, matching, application, and search.
            MetaOp::Rewrite => self.meta_rewrite(ctx, hooks, redex, false),
            MetaOp::Frewrite => self.meta_rewrite(ctx, hooks, redex, true),
            MetaOp::Match => self.meta_match(ctx, hooks, redex),
            MetaOp::Search => self.meta_search(ctx, hooks, redex),
            MetaOp::Apply => self.meta_apply(ctx, hooks, redex),
            MetaOp::Xmatch => self.meta_xmatch(ctx, hooks, redex),
            MetaOp::Xapply => self.meta_xapply(ctx, hooks, redex),
            MetaOp::SearchPath => self.meta_search_path(ctx, hooks, redex),
            // SMT check only translates the decoded Boolean formula and asks the configured backend;
            // unlike object reduction/search it contributes no inner rewrite count.
            MetaOp::Check => self.meta_check(ctx, hooks, redex),
            MetaOp::SmtSearch => self.meta_smt_search(ctx, hooks, redex),
            MetaOp::VariantSat {
                validity,
                explicit_sorts,
            } => self.meta_variant_sat(ctx, hooks, redex, validity, explicit_sorts),
            MetaOp::VariantSatWellFormed => self.meta_variant_sat_well_formed(ctx, hooks, redex),
            // Sort and kind queries.
            MetaOp::SortLeq => self.meta_sort_leq(ctx, hooks, redex),
            MetaOp::SameKind => self.meta_same_kind(ctx, hooks, redex),
            MetaOp::LeastSort => self.meta_least_sort(ctx, hooks, redex),
            MetaOp::LesserSorts => self.meta_lesser_sorts(ctx, hooks, redex),
            MetaOp::GlbSorts => self.meta_glb_sorts(ctx, hooks, redex),
            MetaOp::CompleteName => self.meta_complete_name(ctx, hooks, redex),
            MetaOp::GetKind => self.meta_get_kind(ctx, hooks, redex),
            MetaOp::GetKinds => self.meta_get_kinds(ctx, hooks, redex),
            MetaOp::MaximalSorts => self.meta_maximal_sorts(ctx, hooks, redex),
            MetaOp::MinimalSorts => self.meta_minimal_sorts(ctx, hooks, redex),
            MetaOp::MaximalAritySet => self.meta_maximal_arity_set(ctx, hooks, redex),
            // Well-formedness checks.
            MetaOp::WellFormedModule => self.meta_well_formed_module(ctx, hooks, redex),
            MetaOp::WellFormedTerm => self.meta_well_formed_term(ctx, hooks, redex),
            MetaOp::WellFormedSubstitution => self.meta_well_formed_subst(ctx, hooks, redex),
            // Module and term reflection.
            MetaOp::UpModule => self.meta_up_module(ctx, hooks, redex),
            MetaOp::UpImports => self.meta_up_imports(ctx, hooks, redex),
            MetaOp::UpSorts => self.meta_up_part(ctx, hooks, redex, UpPart::Sorts),
            MetaOp::UpSubsortDecls => self.meta_up_part(ctx, hooks, redex, UpPart::Subsorts),
            MetaOp::UpOpDecls => self.meta_up_part(ctx, hooks, redex, UpPart::Ops),
            MetaOp::UpMbs => self.meta_up_part(ctx, hooks, redex, UpPart::Mbs),
            MetaOp::UpEqs => self.meta_up_part(ctx, hooks, redex, UpPart::Eqs),
            MetaOp::UpRls => self.meta_up_part(ctx, hooks, redex, UpPart::Rls),
            MetaOp::UpTerm => {
                let arg = *ctx.children(redex).first()?;
                Some(up_term_ctx(ctx, hooks, arg))
            }
            MetaOp::DownTerm => {
                let kids = ctx.children(redex);
                let meta = *kids.first()?;
                let default = *kids.get(1)?;
                Some(down_term_ctx(ctx, hooks, meta).unwrap_or(default))
            }
            MetaOp::UpView => self.meta_up_view(ctx, hooks, redex),
            // Parse and pretty-print against a module's syntax.
            MetaOp::Parse => self.meta_parse(ctx, hooks, redex),
            MetaOp::PrettyPrint => self.meta_pretty_print(ctx, hooks, redex, false),
            MetaOp::PrintToString => self.meta_pretty_print(ctx, hooks, redex, true),
            // LEXICAL's quoted-identifier hooks also descend: their scanner owns the shared frontend
            // interner, while their inputs/results remain ordinary String/Qid NA nodes in this engine.
            MetaOp::Tokenize => self.lexical_tokenize(ctx, hooks, redex),
            MetaOp::PrintTokens => self.lexical_print_tokens(ctx, hooks, redex),
            // Strategy declaration/definition reflection shares the same mappers as `upModule`.
            MetaOp::UpStratDecls | MetaOp::UpSds => {
                let kids = ctx.children(redex);
                let name = qid_text(ctx, *kids.first()?)?;
                let flat = down_bool(ctx, *kids.get(1)?)?;
                let mut pieces = self.module_pieces(hooks, &name, flat)?;
                match op {
                    MetaOp::UpStratDecls => up_strat_decls_dag(ctx, hooks, &pieces.strat_decls),
                    _ => up_strat_defs_dag(
                        ctx,
                        hooks,
                        &mut pieces.loaded,
                        self.interner,
                        &pieces.strat_defs,
                    ),
                }
            }
            MetaOp::Unify {
                disjoint,
                irredundant,
            } => self.meta_unify(ctx, hooks, redex, disjoint, irredundant),
            // Variant operations have distinct dispatch identities so they cannot silently fall through
            // to an unrelated descent function. Their concrete handlers are wired with the variant engine.
            MetaOp::GetVariant {
                irredundant,
                nat_family,
            } => self.meta_get_variant(ctx, hooks, redex, irredundant, nat_family),
            MetaOp::VariantUnify {
                disjoint,
                nat_family,
            } => self.meta_variant_unify(ctx, hooks, redex, disjoint, nat_family),
            MetaOp::VariantMatch => self.meta_variant_match(ctx, hooks, redex),
            MetaOp::NarrowingApply => self.meta_narrowing_apply(ctx, hooks, redex),
            MetaOp::NarrowingSearch { path } => self.meta_narrowing_search(ctx, hooks, redex, path),
            MetaOp::Narrow { state_only: false } => self.meta_narrow(ctx, hooks, redex),
            // `metaNarrow2` is recognized but inert.
            MetaOp::Narrow { state_only: true } => None,
            MetaOp::Srewrite { depth_first } => self.meta_srewrite(ctx, hooks, redex, depth_first),
            MetaOp::Unknown => None,
        })();
        match self.reducer_fault.take() {
            Some(fault) => Err(fault),
            None => Ok(result),
        }
    }
}

impl MetaDescent<'_> {
    /// Return the `(n+1)`-th strategic rewrite result while retaining the completed search.
    /// The search computes its solution stream eagerly. The cache charges only the cumulative prefix
    /// through result `n`, then charges the remaining tail when a caller requests exhaustion.
    fn meta_srewrite(
        &mut self,
        ctx: &mut MetaCtx,
        hooks: &MetaHooks,
        redex: DagId,
        depth_first: bool,
    ) -> Option<DagId> {
        let kids = ctx.children(redex);
        if kids.len() != 4 {
            return None;
        }
        let requested = usize::try_from(down_nat(ctx, kids[3])?).ok()?;
        let key = MetaSrewriteCacheKey {
            module: kids[0],
            subject: kids[1],
            strategy: kids[2],
            depth_first,
        };
        let mut cache = if let Some(cache) = self.state.take_srewrite(&key, ctx, requested) {
            cache
        } else {
            let key_roots = [key.module, key.subject, key.strategy]
                .into_iter()
                .map(|dag| ctx.root(dag))
                .collect();
            let mut loaded = self.down_module(ctx, hooks, key.module)?;
            let attempt = try_down_term(ctx, hooks, key.subject, &mut loaded.built, self.interner);
            let subject = capture_reducer_fault(&mut self.reducer_fault, attempt)??;
            let attempt =
                try_down_strategy(ctx, hooks, key.strategy, &mut loaded.built, self.interner);
            let strategy = capture_reducer_fault(&mut self.reducer_fault, attempt)??;
            let (solutions, total_rewrites) =
                match srewrite_dag(&mut loaded, self.interner, subject, &strategy, depth_first) {
                    Ok(result) => result,
                    Err(StrategicRewriteError::Invalid(_)) => return None,
                    Err(StrategicRewriteError::Reducer(fault)) => {
                        debug_assert!(self.reducer_fault.is_none());
                        self.reducer_fault = Some(fault);
                        return None;
                    }
                };
            let solutions = solutions
                .into_iter()
                .map(|solution| RootedStratSolution {
                    _root: loaded.built.engine.root(solution.term),
                    solution,
                })
                .collect();
            MetaSrewriteCache {
                key: key.clone(),
                _key_roots: key_roots,
                loaded,
                solutions,
                total_rewrites,
                last_solution: None,
                rewrite_checkpoint: 0,
            }
        };

        let result = if let Some((term, cumulative)) = cache
            .solutions
            .get(requested)
            .map(|rooted| (rooted.solution.term, rooted.solution.rewrites))
        {
            let work = cumulative.saturating_sub(cache.rewrite_checkpoint);
            cache.rewrite_checkpoint = cumulative;
            cache.last_solution = Some(requested);
            ctx.add_rewrites(work);
            let up_term = up_parsed_term(ctx, hooks, &cache.loaded.built, self.interner, term);
            let up_type = up_sort(ctx, hooks, &cache.loaded.built, term);
            ctx.app(*hooks.ops.get("resultPairSymbol")?, vec![up_term, up_type])
        } else {
            let work = cache
                .total_rewrites
                .saturating_sub(cache.rewrite_checkpoint);
            cache.rewrite_checkpoint = cache.total_rewrites;
            ctx.add_rewrites(work);
            ctx.app(*hooks.ops.get("noMatchSubstSymbol")?, Vec::new())
        };
        self.state.insert(MetaCache::Srewrite(cache));
        Some(result)
    }
}

impl MetaDescent<'_> {
    /// `metaCheck(M, T)` reduces to `(true).Bool` for satisfiable formulas and `(false).Bool` for
    /// unsatisfiable formulas. Unavailable, indeterminate, or non-SMT inputs leave the redex unreduced.
    ///
    /// Solver translation and checking do not perform object rewrites. The successful descent itself is
    /// therefore the only rewrite charged by `try_special`; reductions of the two meta arguments have
    /// already been counted in the outer engine.
    fn meta_check(&mut self, ctx: &mut MetaCtx, hooks: &MetaHooks, redex: DagId) -> Option<DagId> {
        let kids = ctx.children(redex);
        if kids.len() != 2 {
            return None;
        }
        let mut loaded = self.down_module(ctx, hooks, kids[0])?;
        let mut variables = VarIndex::new();
        let formula = down_term_to_term(ctx, hooks, kids[1], &loaded.built, &mut variables)?;
        let bindings: Vec<DagId> = (0..variables.count())
            .map(|slot| {
                let source = variables.name(slot);
                let base = source.split_once(':').map_or(source, |(base, _)| base);
                let name = self.interner.intern(base).index();
                loaded
                    .built
                    .engine
                    .make_var(variables.sort(slot), name, slot)
            })
            .collect();
        let formula = loaded
            .built
            .engine
            .instantiate_bindings(&formula, &bindings);
        let mut solver = ConfiguredSmtEngine::default();
        let result = solver.check_dag(&loaded.built.engine, formula);
        match result {
            SmtResult::Sat => up_bool(ctx, true),
            SmtResult::Unsat => up_bool(ctx, false),
            SmtResult::Unknown | SmtResult::BadDag => None,
        }
    }

    fn meta_variant_sat(
        &mut self,
        ctx: &mut MetaCtx,
        hooks: &MetaHooks,
        redex: DagId,
        validity: bool,
        explicit_sorts: bool,
    ) -> Option<DagId> {
        let kids = ctx.children(redex);
        let (module, finite_arg, infinite_arg, formula_arg) =
            match (explicit_sorts, kids.as_slice()) {
                (false, [module, formula]) => (*module, None, None, *formula),
                (true, [module, finite, infinite, formula]) => {
                    (*module, Some(*finite), Some(*infinite), *formula)
                }
                _ => return None,
            };
        let key = MetaVariantSatCacheKey {
            module,
            formula: formula_arg,
            finite_sorts: finite_arg,
            infinite_sorts: infinite_arg,
            validity,
        };
        if let Some(result) = self.state.variant_sat_result(&key, ctx) {
            return up_bool(ctx, result);
        }

        let mut loaded = self.down_variant_sat_module(ctx, hooks, module)?;
        let finite = match finite_arg {
            Some(sorts) => down_variant_sort_set(ctx, hooks, sorts, &loaded.built)?,
            None => Vec::new(),
        };
        let infinite = match infinite_arg {
            Some(sorts) => down_variant_sort_set(ctx, hooks, sorts, &loaded.built)?,
            None => Vec::new(),
        };
        let mut vars = VarIndex::new();
        let formula = down_variant_sat_formula(ctx, hooks, formula_arg, &loaded.built, &mut vars)?;
        let formula = if validity { formula.negated() } else { formula };
        let variables = (0..vars.count())
            .map(|slot| {
                let source = vars.name(slot);
                let base = source.split_once(':').map_or(source, |(base, _)| base);
                let code = self.interner.intern(base).index();
                tnk_core::unify::problem::VarSpec {
                    sort: vars.sort(slot),
                    name: maude_variable_name_rank(base, code),
                }
            })
            .collect();
        let variant_equations = executable_variant_equations(&mut loaded.built, self.interner);
        let has_memberships = !loaded.built.mb_traces.is_empty()
            || loaded
                .built
                .statements
                .iter()
                .any(|statement| matches!(statement, Statement::Mb { .. }));
        let query = VariantSatQuery {
            formula,
            variables,
            variant_equations,
            overrides: SortOverrides {
                finite,
                infinite,
                explicit: explicit_sorts,
            },
            has_memberships,
        };
        let decision = {
            let mut names = InternerNames(self.interner);
            match decide_variant_sat(&mut loaded.built.engine, &mut names, query) {
                Ok(decision) => decision,
                Err(fault) => {
                    debug_assert!(self.reducer_fault.is_none());
                    self.reducer_fault = Some(fault);
                    return None;
                }
            }
        };
        let result = match (validity, decision) {
            (false, VariantSatDecision::Sat) | (true, VariantSatDecision::Unsat) => true,
            (false, VariantSatDecision::Unsat) | (true, VariantSatDecision::Sat) => false,
            (_, VariantSatDecision::Rejected(_)) => return None,
        };
        let key_roots = std::iter::once(module)
            .chain(std::iter::once(formula_arg))
            .chain(finite_arg)
            .chain(infinite_arg)
            .map(|dag| ctx.root(dag))
            .collect();
        self.state
            .insert(MetaCache::VariantSat(MetaVariantSatCache {
                key,
                _key_roots: key_roots,
                result,
            }));
        up_bool(ctx, result)
    }

    fn meta_variant_sat_well_formed(
        &mut self,
        ctx: &mut MetaCtx,
        hooks: &MetaHooks,
        redex: DagId,
    ) -> Option<DagId> {
        let kids = ctx.children(redex);
        let [module] = kids.as_slice() else {
            return None;
        };
        let mut loaded = self.down_variant_sat_module(ctx, hooks, *module)?;
        let has_memberships = !loaded.built.mb_traces.is_empty()
            || loaded
                .built
                .statements
                .iter()
                .any(|statement| matches!(statement, Statement::Mb { .. }));
        let result = match ConstructorAnalysis::build(
            &mut loaded.built.engine,
            &SortOverrides::default(),
            has_memberships,
        ) {
            Ok(_) | Err(EligibilityRejection::IdentityClassificationRequiresOverride { .. }) => {
                true
            }
            Err(_) => false,
        };
        up_bool(ctx, result)
    }

    /// Resolve `upModule(Q, flat)` variant-satisfiability arguments directly from the module database
    /// after validating the Boolean `flat` argument. This supports named builtin modules whose
    /// `special`/`poly` declarations cannot be encoded by the general reflection path. Explicit reflected
    /// constructors and `[M]` import expressions still use [`Self::down_module`].
    fn down_variant_sat_module(
        &mut self,
        ctx: &mut MetaCtx,
        hooks: &MetaHooks,
        module: DagId,
    ) -> Option<LoadedModule> {
        if ctx.name(ctx.top(module)) == "upModule" {
            let kids = ctx.children(module);
            let name = qid_text(ctx, *kids.first()?)?;
            down_bool(ctx, *kids.get(1)?)?;
            let flat = flatten(&name, self.db, self.views, self.interner).ok()?;
            let attempt = try_build_loaded_module_with_host_functions(
                &flat,
                self.interner,
                &self.host_functions,
            );
            return capture_loaded_module_build(&mut self.reducer_fault, attempt, |_| {});
        }
        self.down_module(ctx, hooks, module)
    }

    /// `metaReduce(M, T)` returns the reduced term and its least sort. Object rewrites contribute to the
    /// current command's total.
    fn meta_reduce(&mut self, ctx: &mut MetaCtx, hooks: &MetaHooks, redex: DagId) -> Option<DagId> {
        let kids = ctx.children(redex);
        if kids.len() != 2 {
            return None;
        }
        let mut loaded = self.down_module(ctx, hooks, kids[0])?;
        let attempt = try_down_term(ctx, hooks, kids[1], &mut loaded.built, self.interner);
        let subj = capture_reducer_fault(&mut self.reducer_fault, attempt)??;
        loaded.built.engine.reset_rewrites();
        let attempt = loaded.built.engine.try_reduce(subj);
        let result = self.capture_semantic(attempt)?;
        ctx.add_rewrites(loaded.built.engine.rewrites());
        let ut = up_parsed_term(ctx, hooks, &loaded.built, self.interner, result);
        let us = up_sort(ctx, hooks, &loaded.built, result);
        let rp = *hooks.ops.get("resultPairSymbol")?;
        Some(ctx.app(rp, vec![ut, us]))
    }

    /// `metaNormalize(M, T)` returns the term normalized by structural axioms only: associative flattening
    /// and ordering, identity/idempotence collapse, and iteration folding. It does not apply user equations
    /// or charge object rewrites.
    fn meta_normalize(
        &mut self,
        ctx: &mut MetaCtx,
        hooks: &MetaHooks,
        redex: DagId,
    ) -> Option<DagId> {
        let kids = ctx.children(redex);
        if kids.len() != 2 {
            return None;
        }
        let mut loaded = self.down_module(ctx, hooks, kids[0])?;
        // Eager theory normalization only; unlike `reduce`, this never applies user equations.
        let attempt = try_down_term(ctx, hooks, kids[1], &mut loaded.built, self.interner);
        let subj = capture_reducer_fault(&mut self.reducer_fault, attempt)??;
        let attempt = loaded.built.engine.try_normalize_for_unify(subj);
        let subj = self.capture_semantic(attempt)?;
        let ut = up_parsed_term(ctx, hooks, &loaded.built, self.interner, subj);
        let us = up_sort(ctx, hooks, &loaded.built, subj);
        let rp = *hooks.ops.get("resultPairSymbol")?;
        Some(ctx.app(rp, vec![ut, us]))
    }

    /// `metaRewrite(M, T, B)` / `metaFrewrite(M, T, B, gas)` → `{up(t'), up(leastSort(t'))}` where `t'` is
    /// `down(T)` rule-rewritten (rule-fair / position-fair) in `down(M)` for up to bound `B` rule steps.
    /// The object run's rewrites (equation reductions + rule applications) fold into the command count.
    fn meta_rewrite(
        &mut self,
        ctx: &mut MetaCtx,
        hooks: &MetaHooks,
        redex: DagId,
        position_fair: bool,
    ) -> Option<DagId> {
        let kids = ctx.children(redex);
        let mut loaded = self.down_module(ctx, hooks, *kids.first()?)?;
        let attempt = try_down_term(ctx, hooks, *kids.get(1)?, &mut loaded.built, self.interner);
        let subj = capture_reducer_fault(&mut self.reducer_fault, attempt)??;
        let bound = down_bound(ctx, hooks, *kids.get(2)?);
        loaded.built.engine.reset_rewrites();
        let result = if position_fair {
            // The fourth argument is per-position gas.
            let gas = down_nat64(ctx, *kids.get(3)?)?;
            let mut rw = loaded.built.engine.frewrite(subj, gas);
            let attempt = rw.try_run(&mut loaded.built.engine, bound);
            self.capture_semantic(attempt)?.term
        } else {
            let mut rw = loaded.built.engine.rewrite(subj);
            let attempt = rw.try_run(&mut loaded.built.engine, bound);
            self.capture_semantic(attempt)?.term
        };
        ctx.add_rewrites(loaded.built.engine.rewrites());
        let ut = up_parsed_term(ctx, hooks, &loaded.built, self.interner, result);
        let us = up_sort(ctx, hooks, &loaded.built, result);
        let rp = *hooks.ops.get("resultPairSymbol")?;
        Some(ctx.app(rp, vec![ut, us]))
    }

    /// `metaMatch(M, P, S, C, n)` returns the `(n+1)`th top-match substitution, or `noMatch`.
    /// Non-empty `C` conditions are currently unsupported and produce no descent result.
    fn meta_match(&mut self, ctx: &mut MetaCtx, hooks: &MetaHooks, redex: DagId) -> Option<DagId> {
        let kids = ctx.children(redex);
        let mut loaded = self.down_module(ctx, hooks, *kids.first()?)?;
        let mut vars = VarIndex::new();
        let pattern = down_term_to_term(ctx, hooks, *kids.get(1)?, &loaded.built, &mut vars)?;
        let attempt = try_down_term(ctx, hooks, *kids.get(2)?, &mut loaded.built, self.interner);
        let subj = capture_reducer_fault(&mut self.reducer_fault, attempt)??;
        // Only the empty such-that condition is supported.
        if !is_nil_condition(ctx, hooks, *kids.get(3)?) {
            return None;
        }
        let sol_nr = down_nat64(ctx, *kids.get(4)?)? as usize;
        let nr = vars.count();
        loaded.built.engine.reset_rewrites();
        let attempt = loaded.built.engine.try_reduce(subj);
        let subj = self.capture_semantic(attempt)?; // Match against the reduced subject.
        ctx.add_rewrites(loaded.built.engine.rewrites());
        // Capture the (n+1)-th solution's bindings while the matcher stream borrows the engine.
        let bindings = nth_match(&mut loaded.built.engine, pattern, nr, subj, false, sol_nr);
        let result = match bindings {
            Some(b) => up_substitution(
                ctx,
                hooks,
                &loaded.built,
                self.interner,
                &var_names(&vars),
                &b,
            ),
            None => ctx.app(*hooks.ops.get("noMatchSubstSymbol")?, vec![]),
        };
        Some(result)
    }

    /// Return the `(n+1)`-th unifier for `metaUnify`, `metaDisjointUnify`, or their irredundant forms.
    /// With a Qid third argument, the result pair/triple ends in the selected fresh-family Qid; with a Nat
    /// third argument, it ends in the next free-variable index. Exhaustion returns
    /// `noUnifier`/`noUnifierIncomplete`. Disjoint forms rename the two sides apart; irredundant forms
    /// filter to most-general unifiers before indexing.
    fn meta_unify(
        &mut self,
        ctx: &mut MetaCtx,
        hooks: &MetaHooks,
        redex: DagId,
        disjoint: bool,
        irredundant: bool,
    ) -> Option<DagId> {
        use tnk_core::fresh::VariableFamily;
        use tnk_core::unify::UnifyEnv;
        use tnk_core::unify::problem::{UnifyProblem, VarSpec};

        let kids = ctx.children(redex);
        // Qid-family and Nat-family declarations share a name and arity, so the symbol table carries a
        // single hook. Select the result shape from the observable third argument.
        let nat_family = !matches!(ctx.repr(*kids.get(2)?), NodeRepr::Qid(_));

        // A Qid argument selects a fresh variable family and returns that family as a Qid. A Nat argument
        // supplies an unbounded base for `#`-family numbering and returns the next free index as a Nat.
        // Nat-family safe-name checking has no reserved input family.
        let (used_family, base, ok_family) = if nat_family {
            // Preserve the unbounded natural base as decimal text.
            let base = down_nat_decimal(ctx, *kids.get(2)?)?;
            (VariableFamily::Unify, base, None)
        } else {
            let incoming = VariableFamily::of_root(&qid_text(ctx, *kids.get(2)?)?)?;
            let used = if incoming == VariableFamily::Unify {
                VariableFamily::Variant
            } else {
                VariableFamily::Unify
            };
            (used, "0".to_string(), Some(incoming))
        };
        let family_root = match used_family {
            VariableFamily::Unify => "#",
            VariableFamily::Variant => "%",
            VariableFamily::Narrow => "@",
        };
        let sol_nr = down_nat64(ctx, *kids.get(3)?)? as usize;
        // A meta-level consumer may request indices 0, 1, 2, … by repeatedly rebuilding the same redex.
        // Cache an exponentially grown Qid-family prefix: each growth enumerates from scratch, but total
        // work remains O(n). Nat-family counters and irredundant filtering use one-shot enumeration.
        let cache_key = if !nat_family && !irredundant {
            Some(MetaUnifyCacheKey {
                module: *kids.first()?,
                roots: meta_unification_roots(ctx, hooks, *kids.get(1)?)?,
                family_root,
                base: base.clone(),
                disjoint,
            })
        } else {
            None
        };
        if let Some(key) = &cache_key
            && let Some(cache) = self.unify_cache.as_ref().filter(|cache| &cache.key == key)
            && (sol_nr < cache.unifiers.len() || cache.exhausted)
        {
            return render_cached_meta_unifier(ctx, hooks, cache, self.interner, sol_nr);
        }
        let enumeration_limit = cache_key.as_ref().map_or(sol_nr + 1, |key| {
            self.unify_cache
                .as_ref()
                .filter(|cache| &cache.key == key)
                .map_or(sol_nr + 1, |cache| {
                    cache.limit.saturating_mul(2).max(sol_nr + 1)
                })
        });
        let mut loaded = self.down_module(ctx, hooks, *kids.first()?)?;

        // Down-translate the problem into (lhs, rhs) Term pairs + the original variables' (name, sort) in
        // slot order; `n_lhs` is the disjoint split point (lhs-side variables occupy slots `0..n_lhs`).
        let mut specs_raw: Vec<(String, SortId)> = Vec::new();
        let (pairs, n_lhs) = down_unification_problem(
            ctx,
            hooks,
            *kids.get(1)?,
            &loaded.built,
            &mut specs_raw,
            disjoint,
        )?;
        let n_vars = specs_raw.len();

        // Split variable qids such as `L:Bag` and derive ordering from the bare name's token code. Disjoint
        // rhs variables set the reserved flag bit while retaining that order.
        const FLAGGED_CODE_BIT: u32 = 0x4000_0000;
        let codes: Vec<u32> = (0..n_vars)
            .map(|k| {
                let bare = specs_raw[k]
                    .0
                    .split_once(':')
                    .map_or(specs_raw[k].0.as_str(), |(name, _)| name);
                let code = self.interner.intern(bare).index();
                if disjoint && k >= n_lhs {
                    code | FLAGGED_CODE_BIT
                } else {
                    code
                }
            })
            .collect();

        // Genuine Var-leaf dags per slot; instantiate each side and theory-normalize (the `unify`
        // command's pipeline; one-sided-id collapse is a no-op for every metaUnify operator).
        let bindings: Vec<DagId> = (0..n_vars)
            .map(|k| {
                loaded
                    .built
                    .engine
                    .make_var(specs_raw[k].1, codes[k], k as u32)
            })
            .collect();
        let mut equations: Vec<(DagId, DagId)> = Vec::new();
        for (l, r) in &pairs {
            let ld = loaded.built.engine.instantiate_bindings(l, &bindings);
            let attempt = loaded.built.engine.try_normalize_for_unify(ld);
            let ld = capture_reducer_fault(&mut self.reducer_fault, attempt)?;
            let rd = loaded.built.engine.instantiate_bindings(r, &bindings);
            let attempt = loaded.built.engine.try_normalize_for_unify(rd);
            let rd = capture_reducer_fault(&mut self.reducer_fault, attempt)?;
            equations.push((ld, rd));
        }
        let specs: Vec<VarSpec> = (0..n_vars)
            .map(|k| VarSpec {
                sort: specs_raw[k].1,
                name: codes[k],
            })
            .collect();

        // A problem variable that looks like a generated fresh name conflicts unless it belongs to the
        // accepted incoming family. Conflicts leave the meta operation unreduced.
        let namegen = tnk_core::fresh::FreshVariableGenerator::new();
        for (name, _) in &specs_raw {
            let bare = name.split(':').next().unwrap_or("");
            if namegen.variable_name_conflict(bare, ok_family) {
                return None;
            }
        }

        // Enumerate. Irredundant: collect all, filter, then index. Current non-irredundant calls grow
        // an outer-command cache exponentially; other calls enumerate exactly through the requested index.
        let mut collected: Vec<Vec<DagId>> = Vec::new();
        let mut exhausted = false;
        let incomplete;
        let last_var_index; // Nat-family result: base + free variables in the selected unifier
        let original_order;
        {
            let mut names = InternerNames(self.interner);
            let mut env = UnifyEnv {
                e: &mut loaded.built.engine,
                names: &mut names,
            };
            let attempt = UnifyProblem::try_new(&mut env, equations, specs, used_family, &base);
            let mut prob = capture_reducer_fault(&mut self.reducer_fault, attempt)?;
            original_order = prob.original_variable_order().to_vec();
            if !prob.problem_okay() {
                return None; // unsupported-theory screen: no reduction
            }
            if irredundant {
                while let Some(u) =
                    capture_reducer_fault(&mut self.reducer_fault, prob.try_find_next(&mut env))?
                {
                    collected.push(u);
                }
                exhausted = true;
            } else {
                for _ in 0..enumeration_limit {
                    match capture_reducer_fault(
                        &mut self.reducer_fault,
                        prob.try_find_next(&mut env),
                    )? {
                        Some(b) => collected.push(b),
                        None => {
                            exhausted = true;
                            break;
                        }
                    }
                }
            }
            incomplete = prob.is_incomplete();
            last_var_index = prob.last_var_index_decimal();
        }
        let unifiers = if irredundant {
            let attempt =
                tnk_core::unify::filter::try_irredundant(&mut loaded.built.engine, collected);
            capture_reducer_fault(&mut self.reducer_fault, attempt)?
        } else {
            collected
        };
        if let Some(key) = cache_key {
            self.unify_cache = Some(MetaUnifyCache {
                key,
                limit: enumeration_limit,
                loaded,
                specs_raw,
                n_lhs,
                original_order,
                unifiers,
                exhausted,
                incomplete,
            });
            let cache = self.unify_cache.as_ref()?;
            return render_cached_meta_unifier(ctx, hooks, cache, self.interner, sol_nr);
        }

        // The third component is a family Qid or the Nat-family next free-variable index.
        let result = match unifiers.get(sol_nr) {
            None => {
                let hook = match (disjoint, incomplete) {
                    (true, false) => "noUnifierTripleSymbol",
                    (true, true) => "noUnifierIncompleteTripleSymbol",
                    (false, false) => "noUnifierPairSymbol",
                    (false, true) => "noUnifierIncompletePairSymbol",
                };
                ctx.app(*hooks.ops.get(hook)?, vec![])
            }
            Some(bindings) => {
                // The kernel returns bindings in its post-normalization slot order. Restore the
                // down-translator's original order before pairing names and, for disjoint
                // unification, before splitting the contiguous lhs/rhs slot ranges.
                let mut bindings_original = bindings.clone();
                for (new_slot, &old_slot) in original_order.iter().enumerate() {
                    bindings_original[old_slot] = bindings[new_slot];
                }
                let bindings = &bindings_original;
                let third = if nat_family {
                    up_nat_big(ctx, &last_var_index)?
                } else {
                    ctx.make_na(hooks.ops["qidSymbol"], NaValue::Qid(family_root.into()))
                };
                if disjoint {
                    let (lhs_b, rhs_b) = bindings.split_at(n_lhs);
                    let lhs_names: Vec<&str> =
                        specs_raw[..n_lhs].iter().map(|(n, _)| n.as_str()).collect();
                    let rhs_names: Vec<&str> =
                        specs_raw[n_lhs..].iter().map(|(n, _)| n.as_str()).collect();
                    let sl = up_unifier_substitution(
                        ctx,
                        hooks,
                        &loaded.built,
                        self.interner,
                        &lhs_names,
                        lhs_b,
                    );
                    let sr = up_unifier_substitution(
                        ctx,
                        hooks,
                        &loaded.built,
                        self.interner,
                        &rhs_names,
                        rhs_b,
                    );
                    let hook = if nat_family {
                        "legacyUnificationTripleSymbol"
                    } else {
                        "unificationTripleSymbol"
                    };
                    ctx.app(*hooks.ops.get(hook)?, vec![sl, sr, third])
                } else {
                    let names: Vec<&str> = specs_raw.iter().map(|(n, _)| n.as_str()).collect();
                    let sub = up_unifier_substitution(
                        ctx,
                        hooks,
                        &loaded.built,
                        self.interner,
                        &names,
                        bindings,
                    );
                    // `{_,_}:Substitution Qid` shares `matchPairSymbol`; the Nat-indexed pair has a
                    // dedicated constructor.
                    let hook = if nat_family {
                        "legacyUnificationPairSymbol"
                    } else {
                        "matchPairSymbol"
                    };
                    ctx.app(*hooks.ops.get(hook)?, vec![sub, third])
                }
            }
        };
        Some(result)
    }

    /// One-step variant narrowing. The incoming family is preserved on the subject; each rule
    /// unifier chooses the next protected family. Equal/forward solution requests resume the same
    /// structurally keyed search, while a backward request starts a fresh search.
    fn meta_narrowing_apply(
        &mut self,
        ctx: &mut MetaCtx,
        hooks: &MetaHooks,
        redex: DagId,
    ) -> Option<DagId> {
        use tnk_core::fresh::VariableFamily;
        use tnk_core::narrow::{NarrowFold, NarrowOptions, NarrowSearch, NarrowSearchType};
        use tnk_core::unify::problem::VarSpec;

        let kids = ctx.children(redex);
        if kids.len() != 6 {
            return None;
        }
        let family = VariableFamily::of_root(&qid_text(ctx, kids[3])?)?;
        let (filtered, delayed) = down_variant_options(ctx, kids[4]);
        let blocker_roots = down_term_list_roots(ctx, hooks, kids[2])?;
        let mut roots = Vec::with_capacity(blocker_roots.len() + 1);
        roots.push(kids[1]);
        roots.extend(blocker_roots.iter().copied());
        let key = MetaNarrowApplyCacheKey {
            module: kids[0],
            roots,
            family,
            filtered,
            delayed,
        };
        let sol_nr = down_nat64(ctx, kids[5])? as usize;

        let mut cache = if let Some(cache) = self.state.take_narrow_apply(&key, ctx, sol_nr) {
            cache
        } else {
            let mut loaded = self.down_module(ctx, hooks, kids[0])?;
            let mut vars = VarIndex::new();
            let target_term = down_term_to_term(ctx, hooks, kids[1], &loaded.built, &mut vars)?;
            let target_variable_count = vars.count() as usize;
            let blocker_terms: Vec<Term> = blocker_roots
                .iter()
                .map(|&root| down_term_to_term(ctx, hooks, root, &loaded.built, &mut vars))
                .collect::<Option<_>>()?;
            let variable_names = (0..target_variable_count)
                .map(|slot| vars.name(slot as u32).to_string())
                .collect();
            let codes: Vec<u32> = (0..vars.count())
                .map(|slot| {
                    let source = vars.name(slot);
                    let bare = source.split_once(':').map_or(source, |(bare, _)| bare);
                    self.interner.intern(bare).index()
                })
                .collect();
            let bindings: Vec<DagId> = (0..vars.count())
                .map(|slot| {
                    loaded
                        .built
                        .engine
                        .make_var(vars.sort(slot), codes[slot as usize], slot)
                })
                .collect();
            let target = loaded
                .built
                .engine
                .instantiate_bindings(&target_term, &bindings);
            let blockers = blocker_terms
                .iter()
                .map(|term| loaded.built.engine.instantiate_bindings(term, &bindings))
                .collect();
            let specs: Vec<VarSpec> = (0..vars.count())
                .map(|slot| VarSpec {
                    sort: vars.sort(slot),
                    name: codes[slot as usize],
                })
                .collect();
            let equations = executable_variant_equations(&mut loaded.built, self.interner);
            let rules = loaded.built.engine.narrowing_rules().to_vec();
            loaded.built.engine.reset_rewrites();
            let options = NarrowOptions {
                search_type: NarrowSearchType::One,
                max_depth: Some(1),
                filter: filtered,
                delay: delayed,
                fold: NarrowFold::None,
                keep_history: true,
                keep_paths: false,
                respect_frozen: true,
            };
            let mut names = InternerNames(self.interner);
            let mut env = tnk_core::unify::UnifyEnv {
                e: &mut loaded.built.engine,
                names: &mut names,
            };
            let attempt = NarrowSearch::new_preserving(
                &mut env, target, specs, family, blockers, &rules, equations, "0", options,
            );
            let search = capture_narrow_error(&mut self.reducer_fault, attempt)?;
            let key_roots = std::iter::once(key.module)
                .chain(key.roots.iter().copied())
                .map(|dag| ctx.root(dag))
                .collect();
            MetaNarrowApplyCache {
                key: key.clone(),
                _key_roots: key_roots,
                loaded,
                search,
                variable_names,
                target_variable_count,
                states: Vec::new(),
                last_solution: None,
                rewrite_checkpoint: 0,
                breakdown_checkpoint: SymbolicRewriteCheckpoint::default(),
            }
        };

        let mut rewrite_charge = 0;
        let mut successful_steps = 0u64;
        while cache.states.len() <= sol_nr {
            let next = {
                let mut names = InternerNames(self.interner);
                let mut env = tnk_core::unify::UnifyEnv {
                    e: &mut cache.loaded.built.engine,
                    names: &mut names,
                };
                let attempt = cache.search.try_next_interesting_state(&mut env);
                capture_reducer_fault(&mut self.reducer_fault, attempt)?
            };
            let rewrites = cache.loaded.built.engine.rewrites();
            rewrite_charge += rewrites.saturating_sub(cache.rewrite_checkpoint);
            cache.rewrite_checkpoint = rewrites;
            let Some(state) = next else {
                // A reply charges at most one successful narrowing step: skipped steps are excluded, and
                // a failure excludes every successful step visited while seeking the requested ordinal.
                ctx.add_rewrites(rewrite_charge.saturating_sub(successful_steps));
                let (variant_narrowing, _) = take_symbolic_subcounts(
                    &cache.loaded.built.engine,
                    &mut cache.breakdown_checkpoint,
                );
                ctx.add_variant_narrowing_subcount(variant_narrowing);
                let hook = if cache.search.is_incomplete() {
                    "narrowingApplyFailureIncompleteSymbol"
                } else {
                    "narrowingApplyFailureSymbol"
                };
                return Some(ctx.app(*hooks.ops.get(hook)?, vec![]));
            };
            successful_steps += 1;
            cache.states.push(state);
        }
        ctx.add_rewrites(rewrite_charge.saturating_sub(successful_steps.saturating_sub(1)));
        let (variant_narrowing, _) =
            take_symbolic_subcounts(&cache.loaded.built.engine, &mut cache.breakdown_checkpoint);
        ctx.add_variant_narrowing_subcount(variant_narrowing);
        ctx.add_narrowing_subcount(u64::from(successful_steps != 0));

        let state = cache.states[sol_nr];
        let (term, substitution, family, _) = {
            let (term, substitution, family, depth) = cache.search.state(state);
            (term, substitution.to_vec(), family, depth)
        };
        let parent = cache.search.parent(state)?;
        let parent_term = cache.search.state(parent).0;
        let (rule_index, path, source_substitution) = {
            let step = cache.search.step(state)?;
            (
                step.rule_index,
                step.path.clone(),
                step.source_substitution.clone(),
            )
        };
        let rule = cache
            .loaded
            .built
            .engine
            .narrowing_rules()
            .get(rule_index)?
            .clone();
        let term_meta = up_parsed_term(ctx, hooks, &cache.loaded.built, self.interner, term);
        let sort_meta = up_type(
            ctx,
            hooks,
            &cache.loaded.built,
            cache.loaded.built.engine.sort_of(term),
        );
        let context_meta = up_context(
            ctx,
            hooks,
            &cache.loaded.built,
            self.interner,
            parent_term,
            &path,
        );
        let label_meta = ctx.make_na(
            hooks.ops["qidSymbol"],
            NaValue::Qid(rule.label.unwrap_or_default().into()),
        );
        let subject_substitution = up_substitution(
            ctx,
            hooks,
            &cache.loaded.built,
            self.interner,
            &cache.variable_names,
            &substitution[..cache.target_variable_count],
        );
        let rule_variable_names: Vec<String> = rule
            .variable_names
            .iter()
            .zip(&rule.variables)
            .map(|(name, spec)| {
                if name.contains(':') {
                    name.clone()
                } else {
                    format!(
                        "{name}:{}",
                        cache.loaded.built.engine.sorts().name(spec.sort)
                    )
                }
            })
            .collect();
        let rule_substitution = up_substitution(
            ctx,
            hooks,
            &cache.loaded.built,
            self.interner,
            &rule_variable_names,
            &source_substitution,
        );
        let family_meta = ctx.make_na(
            hooks.ops["qidSymbol"],
            NaValue::Qid(variant_family_root(family).into()),
        );
        let result = ctx.app(
            *hooks.ops.get("narrowingApplyResultSymbol")?,
            vec![
                term_meta,
                sort_meta,
                context_meta,
                label_meta,
                subject_substitution,
                rule_substitution,
                family_meta,
            ],
        );
        cache.last_solution = Some(sol_nr);
        self.state.insert(MetaCache::NarrowApply(cache));
        Some(result)
    }

    /// `metaNarrow` searches the narrowing graph, composes the final goal unifier into the reached state,
    /// and returns a `ResultTriple` containing only bindings for variables introduced by the goal.
    fn meta_narrow(&mut self, ctx: &mut MetaCtx, hooks: &MetaHooks, redex: DagId) -> Option<DagId> {
        use tnk_core::narrow::{
            NarrowFold, NarrowGoal, NarrowOptions, NarrowSearch, NarrowSearchType,
        };
        use tnk_core::unify::problem::VarSpec;

        let kids = ctx.children(redex);
        if kids.len() != 6 {
            return None;
        }
        let search_type = match qid_text(ctx, kids[3])?.as_str() {
            "1" => NarrowSearchType::One,
            "+" => NarrowSearchType::AtLeastOne,
            "*" => NarrowSearchType::Any,
            "!" => NarrowSearchType::NormalForm,
            _ => return None,
        };
        let max_depth = down_bound(ctx, hooks, kids[4]).map(|bound| bound as usize);
        let key = MetaNarrowResultCacheKey {
            module: kids[0],
            subject: kids[1],
            goal: kids[2],
            search_type,
            max_depth,
        };
        let sol_nr = down_nat64(ctx, kids[5])? as usize;

        let mut cache = if let Some(cache) = self.state.take_narrow_result(&key, ctx, sol_nr) {
            cache
        } else {
            let mut loaded = self.down_module(ctx, hooks, kids[0])?;
            let mut vars = VarIndex::new();
            let subject_term = down_term_to_term(ctx, hooks, kids[1], &loaded.built, &mut vars)?;
            let initial_variable_count = vars.count() as usize;
            let goal_term = down_term_to_term(ctx, hooks, kids[2], &loaded.built, &mut vars)?;
            let codes: Vec<u32> = (0..vars.count())
                .map(|slot| {
                    let source = vars.name(slot);
                    let bare = source.split_once(':').map_or(source, |(bare, _)| bare);
                    self.interner.intern(bare).index()
                })
                .collect();
            let goal_variables: Vec<_> = (initial_variable_count..vars.count() as usize)
                .map(|slot| {
                    (
                        codes[slot],
                        vars.sort(slot as u32),
                        vars.name(slot as u32).to_string(),
                    )
                })
                .collect();
            let bindings: Vec<DagId> = (0..vars.count())
                .map(|slot| {
                    loaded
                        .built
                        .engine
                        .make_var(vars.sort(slot), codes[slot as usize], slot)
                })
                .collect();
            let mut subject = loaded
                .built
                .engine
                .instantiate_bindings(&subject_term, &bindings);
            let mut goal = loaded
                .built
                .engine
                .instantiate_bindings(&goal_term, &bindings);
            let mut specs: Vec<VarSpec> = (0..vars.count())
                .map(|slot| VarSpec {
                    sort: vars.sort(slot),
                    name: codes[slot as usize],
                })
                .collect();
            let mut variable_order =
                tnk_core::variant::variables_in_dag(&loaded.built.engine, subject);
            for slot in tnk_core::variant::variables_in_dag(&loaded.built.engine, goal) {
                if !variable_order.contains(&slot) {
                    variable_order.push(slot);
                }
            }
            if variable_order.len() != specs.len() {
                return None;
            }
            let mut new_slot = vec![0u32; specs.len()];
            for (new, &old) in variable_order.iter().enumerate() {
                new_slot[old] = new as u32;
            }
            let remapping: Vec<_> = specs
                .iter()
                .enumerate()
                .map(|(old, spec)| {
                    Some(
                        loaded
                            .built
                            .engine
                            .make_var(spec.sort, spec.name, new_slot[old]),
                    )
                })
                .collect();
            subject = tnk_core::unify::instantiate(&mut loaded.built.engine, &remapping, subject)
                .unwrap_or(subject);
            goal = tnk_core::unify::instantiate(&mut loaded.built.engine, &remapping, goal)
                .unwrap_or(goal);
            specs = variable_order.iter().map(|&old| specs[old]).collect();

            let equations = executable_variant_equations(&mut loaded.built, self.interner);
            let rules = loaded.built.engine.narrowing_rules().to_vec();
            loaded.built.engine.reset_rewrites();
            let options = NarrowOptions {
                search_type,
                max_depth,
                filter: false,
                delay: false,
                fold: NarrowFold::None,
                keep_history: false,
                keep_paths: false,
                respect_frozen: true,
            };
            let mut names = InternerNames(self.interner);
            let mut env = tnk_core::unify::UnifyEnv {
                e: &mut loaded.built.engine,
                names: &mut names,
            };
            let attempt = NarrowSearch::new(
                &mut env,
                subject,
                specs[..initial_variable_count].to_vec(),
                &rules,
                equations,
                "0",
                options,
            );
            let mut search = capture_narrow_error(&mut self.reducer_fault, attempt)?;
            search.set_goal(NarrowGoal::new(env.e, goal, specs, initial_variable_count));
            let key_roots = [key.module, key.subject, key.goal]
                .into_iter()
                .map(|dag| ctx.root(dag))
                .collect();
            MetaNarrowResultCache {
                key: key.clone(),
                _key_roots: key_roots,
                loaded,
                search,
                goal_variables,
                solutions: Vec::new(),
                last_solution: None,
                rewrite_checkpoint: 0,
                breakdown_checkpoint: SymbolicRewriteCheckpoint::default(),
            }
        };

        while cache.solutions.len() <= sol_nr {
            let next = {
                let mut names = InternerNames(self.interner);
                let mut env = tnk_core::unify::UnifyEnv {
                    e: &mut cache.loaded.built.engine,
                    names: &mut names,
                };
                let attempt = cache.search.try_find_next(&mut env);
                capture_reducer_fault(&mut self.reducer_fault, attempt)?
            };
            let rewrites = cache.loaded.built.engine.rewrites();
            ctx.add_rewrites(rewrites.saturating_sub(cache.rewrite_checkpoint));
            cache.rewrite_checkpoint = rewrites;
            transfer_symbolic_subcounts(
                ctx,
                &cache.loaded.built.engine,
                &mut cache.breakdown_checkpoint,
            );
            let Some(solution) = next else {
                let hook = if cache.search.is_incomplete() {
                    "failureIncomplete3Symbol"
                } else {
                    "failure3Symbol"
                };
                return Some(ctx.app(*hooks.ops.get(hook)?, vec![]));
            };
            let roots = solution
                .bindings
                .iter()
                .map(|&dag| cache.loaded.built.engine.root(dag))
                .collect();
            cache.solutions.push(RootedNarrowingSolution {
                solution,
                _roots: roots,
            });
        }

        let solution = &cache.solutions[sol_nr].solution;
        let alpha =
            narrowing_result_alpha_map(&mut cache.loaded.built.engine, self.interner, solution);
        let state_term = cache.search.state(solution.state).0;
        let term =
            instantiate_narrowing_solution(&mut cache.loaded.built.engine, state_term, solution);
        let term = tnk_core::unify::instantiate(&mut cache.loaded.built.engine, &alpha, term)
            .unwrap_or(term);
        let mut goal_names = Vec::with_capacity(cache.goal_variables.len());
        let mut goal_bindings = Vec::with_capacity(cache.goal_variables.len());
        for (name, sort, display) in &cache.goal_variables {
            let slot = solution
                .variables
                .iter()
                .position(|spec| spec.name == *name && spec.sort == *sort)?;
            goal_names.push(display.clone());
            let binding = solution.bindings[slot];
            let binding =
                tnk_core::unify::instantiate(&mut cache.loaded.built.engine, &alpha, binding)
                    .unwrap_or(binding);
            goal_bindings.push(binding);
        }
        let term_meta = up_parsed_term(ctx, hooks, &cache.loaded.built, self.interner, term);
        let type_meta = up_type(
            ctx,
            hooks,
            &cache.loaded.built,
            cache.loaded.built.engine.sort_of(term),
        );
        let substitution_meta = up_substitution(
            ctx,
            hooks,
            &cache.loaded.built,
            self.interner,
            &goal_names,
            &goal_bindings,
        );
        let result = ctx.app(
            *hooks.ops.get("resultTripleSymbol")?,
            vec![term_meta, type_meta, substitution_meta],
        );
        cache.last_solution = Some(sol_nr);
        self.state.insert(MetaCache::NarrowResult(cache));
        Some(result)
    }

    /// Variant-based narrowing search. Equal and forward ordinal requests resume the structurally keyed
    /// search; backward requests restart it. The path form retains and returns the complete step trace.
    fn meta_narrowing_search(
        &mut self,
        ctx: &mut MetaCtx,
        hooks: &MetaHooks,
        redex: DagId,
        path: bool,
    ) -> Option<DagId> {
        use tnk_core::narrow::{
            NarrowFold, NarrowGoal, NarrowOptions, NarrowSearch, NarrowSearchType,
        };
        use tnk_core::unify::problem::VarSpec;

        let kids = ctx.children(redex);
        if kids.len() != 8 {
            return None;
        }
        let search_type = match qid_text(ctx, kids[3])?.as_str() {
            "1" => NarrowSearchType::One,
            "+" => NarrowSearchType::AtLeastOne,
            "*" => NarrowSearchType::Any,
            "!" => NarrowSearchType::NormalForm,
            _ => return None,
        };
        let max_depth = down_bound(ctx, hooks, kids[4]).map(|bound| bound as usize);
        let fold = match qid_text(ctx, kids[5])?.as_str() {
            "none" => NarrowFold::None,
            "match" => NarrowFold::Match,
            "variant" => NarrowFold::Variant,
            _ => return None,
        };
        let (filtered, delayed) = down_variant_options(ctx, kids[6]);
        let key = MetaNarrowSearchCacheKey {
            module: kids[0],
            subject: kids[1],
            goal: kids[2],
            search_type,
            max_depth,
            fold,
            filtered,
            delayed,
            path,
        };
        let sol_nr = down_nat64(ctx, kids[7])? as usize;

        let mut cache = if let Some(cache) = self.state.take_narrow_search(&key, ctx, sol_nr) {
            cache
        } else {
            let mut loaded = self.down_module(ctx, hooks, kids[0])?;
            let mut vars = VarIndex::new();
            let subject_term = down_term_to_term(ctx, hooks, kids[1], &loaded.built, &mut vars)?;
            let initial_variable_count = vars.count() as usize;
            let goal_term = down_term_to_term(ctx, hooks, kids[2], &loaded.built, &mut vars)?;
            let source_names: Vec<String> = (0..vars.count())
                .map(|slot| vars.name(slot).to_string())
                .collect();
            let codes: Vec<u32> = (0..vars.count())
                .map(|slot| {
                    let source = vars.name(slot);
                    let bare = source.split_once(':').map_or(source, |(bare, _)| bare);
                    self.interner.intern(bare).index()
                })
                .collect();
            let bindings: Vec<DagId> = (0..vars.count())
                .map(|slot| {
                    loaded
                        .built
                        .engine
                        .make_var(vars.sort(slot), codes[slot as usize], slot)
                })
                .collect();
            let mut subject = loaded
                .built
                .engine
                .instantiate_bindings(&subject_term, &bindings);
            let mut goal = loaded
                .built
                .engine
                .instantiate_bindings(&goal_term, &bindings);
            let mut specs: Vec<VarSpec> = (0..vars.count())
                .map(|slot| VarSpec {
                    sort: vars.sort(slot),
                    name: codes[slot as usize],
                })
                .collect();

            // Index source variables by canonical subject-DAG order, then append variables found only in the
            // goal. Initial renaming and accumulated substitutions expose this order.
            let mut variable_order =
                tnk_core::variant::variables_in_dag(&loaded.built.engine, subject);
            for slot in tnk_core::variant::variables_in_dag(&loaded.built.engine, goal) {
                if !variable_order.contains(&slot) {
                    variable_order.push(slot);
                }
            }
            if variable_order.len() != specs.len() {
                return None;
            }
            let mut new_slot = vec![0u32; specs.len()];
            for (new, &old) in variable_order.iter().enumerate() {
                new_slot[old] = new as u32;
            }
            let remapping: Vec<_> = specs
                .iter()
                .enumerate()
                .map(|(old, spec)| {
                    Some(
                        loaded
                            .built
                            .engine
                            .make_var(spec.sort, spec.name, new_slot[old]),
                    )
                })
                .collect();
            subject = tnk_core::unify::instantiate(&mut loaded.built.engine, &remapping, subject)
                .unwrap_or(subject);
            goal = tnk_core::unify::instantiate(&mut loaded.built.engine, &remapping, goal)
                .unwrap_or(goal);
            specs = variable_order.iter().map(|&old| specs[old]).collect();
            let initial_variable_names = variable_order
                .iter()
                .take(initial_variable_count)
                .map(|&old| source_names[old].clone())
                .collect();

            let equations = executable_variant_equations(&mut loaded.built, self.interner);
            let rules = loaded.built.engine.narrowing_rules().to_vec();
            loaded.built.engine.reset_rewrites();
            let options = NarrowOptions {
                search_type,
                max_depth,
                filter: filtered,
                delay: delayed,
                fold,
                keep_history: path,
                keep_paths: path,
                respect_frozen: true,
            };
            let mut names = InternerNames(self.interner);
            let mut env = tnk_core::unify::UnifyEnv {
                e: &mut loaded.built.engine,
                names: &mut names,
            };
            let attempt = NarrowSearch::new(
                &mut env,
                subject,
                specs[..initial_variable_count].to_vec(),
                &rules,
                equations,
                "0",
                options,
            );
            let mut search = capture_narrow_error(&mut self.reducer_fault, attempt)?;
            search.set_goal(NarrowGoal::new(env.e, goal, specs, initial_variable_count));
            let key_roots = [key.module, key.subject, key.goal]
                .into_iter()
                .map(|dag| ctx.root(dag))
                .collect();
            MetaNarrowSearchCache {
                key: key.clone(),
                _key_roots: key_roots,
                loaded,
                search,
                initial_variable_names,
                initial_variable_count,
                solutions: Vec::new(),
                last_solution: None,
                rewrite_checkpoint: 0,
                breakdown_checkpoint: SymbolicRewriteCheckpoint::default(),
            }
        };

        while cache.solutions.len() <= sol_nr {
            let next = {
                let mut names = InternerNames(self.interner);
                let mut env = tnk_core::unify::UnifyEnv {
                    e: &mut cache.loaded.built.engine,
                    names: &mut names,
                };
                let attempt = cache.search.try_find_next(&mut env);
                capture_reducer_fault(&mut self.reducer_fault, attempt)?
            };
            let rewrites = cache.loaded.built.engine.rewrites();
            ctx.add_rewrites(rewrites.saturating_sub(cache.rewrite_checkpoint));
            cache.rewrite_checkpoint = rewrites;
            transfer_symbolic_subcounts(
                ctx,
                &cache.loaded.built.engine,
                &mut cache.breakdown_checkpoint,
            );
            let Some(solution) = next else {
                let hook = match (path, cache.search.is_incomplete()) {
                    (false, false) => "narrowingSearchFailureSymbol",
                    (false, true) => "narrowingSearchFailureIncompleteSymbol",
                    (true, false) => "narrowingSearchPathFailureSymbol",
                    (true, true) => "narrowingSearchPathFailureIncompleteSymbol",
                };
                return Some(ctx.app(*hooks.ops.get(hook)?, vec![]));
            };
            let roots = solution
                .bindings
                .iter()
                .map(|&dag| cache.loaded.built.engine.root(dag))
                .collect();
            cache.solutions.push(RootedNarrowingSolution {
                solution,
                _roots: roots,
            });
        }

        let solution = &cache.solutions[sol_nr].solution;
        let result = if path {
            let (initial_term, initial_substitution, _, _) = cache.search.state(0);
            let initial_term_meta =
                up_parsed_term(ctx, hooks, &cache.loaded.built, self.interner, initial_term);
            let initial_type_meta = up_type(
                ctx,
                hooks,
                &cache.loaded.built,
                cache.loaded.built.engine.sort_of(initial_term),
            );
            let initial_substitution_meta = up_substitution(
                ctx,
                hooks,
                &cache.loaded.built,
                self.interner,
                &cache.initial_variable_names,
                &initial_substitution[..cache.initial_variable_count],
            );
            let mut trace_steps = Vec::new();
            for state in cache
                .search
                .path_indices(solution.state)
                .into_iter()
                .skip(1)
            {
                let parent = cache.search.parent(state)?;
                let parent_term = cache.search.state(parent).0;
                let (new_term, accumulated, _, _) = cache.search.state(state);
                let (rule_index, step_path, state_unifier, source_substitution, step_family) = {
                    let step = cache.search.step(state)?;
                    (
                        step.rule_index,
                        step.path.clone(),
                        step.state_unifier.clone(),
                        step.source_substitution.clone(),
                        step.family,
                    )
                };
                let rule = cache
                    .loaded
                    .built
                    .engine
                    .narrowing_rules()
                    .get(rule_index)?;
                let mut unifier_names = meta_variable_spec_names(
                    &cache.loaded.built.engine,
                    self.interner,
                    cache.search.state_variables(parent),
                );
                unifier_names.extend(meta_rule_variable_names(
                    &cache.loaded.built.engine,
                    &rule.variable_names,
                    &rule.variables,
                ));
                let mut unifier_bindings = state_unifier;
                unifier_bindings.extend(source_substitution);
                let context_meta = up_context(
                    ctx,
                    hooks,
                    &cache.loaded.built,
                    self.interner,
                    parent_term,
                    &step_path,
                );
                let label_meta = ctx.make_na(
                    hooks.ops["qidSymbol"],
                    NaValue::Qid(rule.label.clone().unwrap_or_default().into()),
                );
                let unifier_meta = up_substitution(
                    ctx,
                    hooks,
                    &cache.loaded.built,
                    self.interner,
                    &unifier_names,
                    &unifier_bindings,
                );
                let family_meta = ctx.make_na(
                    hooks.ops["qidSymbol"],
                    NaValue::Qid(variant_family_root(step_family).into()),
                );
                let new_term_meta =
                    up_parsed_term(ctx, hooks, &cache.loaded.built, self.interner, new_term);
                let new_type_meta = up_type(
                    ctx,
                    hooks,
                    &cache.loaded.built,
                    cache.loaded.built.engine.sort_of(new_term),
                );
                let accumulated_meta = up_substitution(
                    ctx,
                    hooks,
                    &cache.loaded.built,
                    self.interner,
                    &cache.initial_variable_names,
                    &accumulated[..cache.initial_variable_count],
                );
                trace_steps.push(ctx.app(
                    *hooks.ops.get("narrowingStepSymbol")?,
                    vec![
                        context_meta,
                        label_meta,
                        unifier_meta,
                        family_meta,
                        new_term_meta,
                        new_type_meta,
                        accumulated_meta,
                    ],
                ));
            }
            let trace = match trace_steps.len() {
                0 => ctx.app(*hooks.ops.get("nilNarrowingTraceSymbol")?, vec![]),
                1 => trace_steps[0],
                _ => ctx.app(*hooks.ops.get("narrowingTraceSymbol")?, trace_steps),
            };
            let goal_names = meta_variable_spec_names(
                &cache.loaded.built.engine,
                self.interner,
                &solution.variables,
            );
            let goal_substitution = up_substitution(
                ctx,
                hooks,
                &cache.loaded.built,
                self.interner,
                &goal_names,
                &solution.bindings,
            );
            let goal_family = ctx.make_na(
                hooks.ops["qidSymbol"],
                NaValue::Qid(variant_family_root(solution.family).into()),
            );
            ctx.app(
                *hooks.ops.get("narrowingSearchPathResultSymbol")?,
                vec![
                    initial_term_meta,
                    initial_type_meta,
                    initial_substitution_meta,
                    trace,
                    goal_substitution,
                    goal_family,
                ],
            )
        } else {
            let (term, accumulated, family, _) = cache.search.state(solution.state);
            let term_meta = up_parsed_term(ctx, hooks, &cache.loaded.built, self.interner, term);
            let type_meta = up_type(
                ctx,
                hooks,
                &cache.loaded.built,
                cache.loaded.built.engine.sort_of(term),
            );
            let accumulated_meta = up_substitution(
                ctx,
                hooks,
                &cache.loaded.built,
                self.interner,
                &cache.initial_variable_names,
                &accumulated[..cache.initial_variable_count],
            );
            let state_family = ctx.make_na(
                hooks.ops["qidSymbol"],
                NaValue::Qid(variant_family_root(family).into()),
            );
            let goal_names = meta_variable_spec_names(
                &cache.loaded.built.engine,
                self.interner,
                &solution.variables,
            );
            let goal_substitution = up_substitution(
                ctx,
                hooks,
                &cache.loaded.built,
                self.interner,
                &goal_names,
                &solution.bindings,
            );
            let goal_family = ctx.make_na(
                hooks.ops["qidSymbol"],
                NaValue::Qid(variant_family_root(solution.family).into()),
            );
            ctx.app(
                *hooks.ops.get("narrowingSearchResultSymbol")?,
                vec![
                    term_meta,
                    type_meta,
                    accumulated_meta,
                    state_family,
                    goal_substitution,
                    goal_family,
                ],
            )
        };
        cache.last_solution = Some(sol_nr);
        self.state.insert(MetaCache::NarrowSearch(cache));
        Some(result)
    }

    /// `metaGetVariant(M, T, TL, F, n)` returns the `n`th folding variant of `T`. Equal indices reuse the
    /// cached result, forward indices resume the live search, and backward requests restart it.
    fn meta_get_variant(
        &mut self,
        ctx: &mut MetaCtx,
        hooks: &MetaHooks,
        redex: DagId,
        irredundant: bool,
        nat_family: bool,
    ) -> Option<DagId> {
        use tnk_core::fresh::{FreshVariableGenerator, VariableFamily};
        use tnk_core::unify::problem::VarSpec;
        use tnk_core::variant::{VariantMode, VariantSearch};

        let kids = ctx.children(redex);
        if kids.len() != 5 {
            return None;
        }
        let (incoming_family, base) = if nat_family {
            (None, down_nat_decimal(ctx, kids[3])?)
        } else {
            (
                Some(VariableFamily::of_root(&qid_text(ctx, kids[3])?)?),
                "0".to_string(),
            )
        };
        let blocker_roots = down_term_list_roots(ctx, hooks, kids[2])?;
        let mut roots = Vec::with_capacity(blocker_roots.len() + 1);
        roots.push(kids[1]);
        roots.extend(blocker_roots.iter().copied());
        let key = MetaGetVariantCacheKey {
            module: kids[0],
            roots,
            family: incoming_family,
            base: base.clone(),
            irredundant,
            nat_family,
        };
        let sol_nr = down_nat64(ctx, kids[4])? as usize;

        let mut cache = if let Some(cache) = self.state.take_get_variant(&key, ctx, sol_nr) {
            cache
        } else {
            let mut loaded = self.down_module(ctx, hooks, kids[0])?;
            let mut vars = VarIndex::new();
            let target_term = down_term_to_term(ctx, hooks, kids[1], &loaded.built, &mut vars)?;
            let target_variables = vars.count() as usize;
            let blocker_terms: Vec<Term> = blocker_roots
                .iter()
                .map(|&root| down_term_to_term(ctx, hooks, root, &loaded.built, &mut vars))
                .collect::<Option<_>>()?;

            let variable_names: Vec<String> = (0..target_variables)
                .map(|slot| vars.name(slot as u32).to_string())
                .collect();
            let namegen = FreshVariableGenerator::new();
            if variable_names.iter().any(|name| {
                let bare = name.split_once(':').map_or(name.as_str(), |(bare, _)| bare);
                namegen.variable_name_conflict(bare, incoming_family)
            }) {
                return Some(ctx.app(*hooks.ops.get("noVariantSymbol")?, vec![]));
            }

            let codes: Vec<u32> = (0..vars.count())
                .map(|slot| {
                    let source = vars.name(slot);
                    let bare = source.split_once(':').map_or(source, |(bare, _)| bare);
                    self.interner.intern(bare).index()
                })
                .collect();
            let bindings: Vec<DagId> = (0..vars.count())
                .map(|slot| {
                    loaded
                        .built
                        .engine
                        .make_var(vars.sort(slot), codes[slot as usize], slot)
                })
                .collect();
            let target = loaded
                .built
                .engine
                .instantiate_bindings(&target_term, &bindings);
            let blockers = blocker_terms
                .iter()
                .map(|term| loaded.built.engine.instantiate_bindings(term, &bindings))
                .collect();
            let specs: Vec<VarSpec> = (0..target_variables)
                .map(|slot| {
                    let source = vars.name(slot as u32);
                    let bare = source.split_once(':').map_or(source, |(bare, _)| bare);
                    VarSpec {
                        sort: vars.sort(slot as u32),
                        name: maude_variable_name_rank(bare, codes[slot]),
                    }
                })
                .collect();
            let equations = executable_variant_equations(&mut loaded.built, self.interner);
            loaded.built.engine.reset_rewrites();
            let mut names = InternerNames(self.interner);
            let mut env = tnk_core::unify::UnifyEnv {
                e: &mut loaded.built.engine,
                names: &mut names,
            };
            let mode = if irredundant {
                VariantMode::Irredundant
            } else {
                VariantMode::Incremental
            };
            let attempt = VariantSearch::new(
                &mut env,
                target,
                specs,
                blockers,
                equations,
                mode,
                incoming_family,
                &base,
            );
            let search = capture_variant_error(&mut self.reducer_fault, attempt)?;
            let variable_names = search
                .original_variable_order()
                .iter()
                .map(|&old| variable_names[old].clone())
                .collect();
            let key_roots = std::iter::once(key.module)
                .chain(key.roots.iter().copied())
                .map(|dag| ctx.root(dag))
                .collect();
            MetaGetVariantCache {
                key: key.clone(),
                _key_roots: key_roots,
                loaded,
                search,
                variable_names,
                variants: Vec::new(),
                exhausted: false,
                last_solution: None,
                rewrite_checkpoint: 0,
                breakdown_checkpoint: SymbolicRewriteCheckpoint::default(),
                rewrite_charge: 0,
            }
        };

        while cache.variants.len() <= sol_nr && !cache.exhausted {
            let next = {
                let mut names = InternerNames(self.interner);
                let mut env = tnk_core::unify::UnifyEnv {
                    e: &mut cache.loaded.built.engine,
                    names: &mut names,
                };
                let attempt = cache.search.try_find_next(&mut env);
                capture_reducer_fault(&mut self.reducer_fault, attempt)?
            };
            let rewrites = cache.loaded.built.engine.rewrites();
            if let Some(variant) = next {
                cache.rewrite_charge += rewrites.saturating_sub(cache.rewrite_checkpoint);
                cache.rewrite_checkpoint = rewrites;
                cache.variants.push(variant);
            } else {
                cache.rewrite_charge += rewrites.saturating_sub(cache.rewrite_checkpoint);
                cache.rewrite_checkpoint = rewrites;
                cache.exhausted = true;
            }
        }
        ctx.add_rewrites(std::mem::take(&mut cache.rewrite_charge));
        transfer_symbolic_subcounts(
            ctx,
            &cache.loaded.built.engine,
            &mut cache.breakdown_checkpoint,
        );

        if cache.variants.get(sol_nr).is_none() {
            let hook = if cache.search.is_incomplete() {
                "noVariantIncompleteSymbol"
            } else {
                "noVariantSymbol"
            };
            return Some(ctx.app(*hooks.ops.get(hook)?, vec![]));
        }
        let result = {
            let variant = &cache.variants[sol_nr];
            let term = up_parsed_term(ctx, hooks, &cache.loaded.built, self.interner, variant.term);
            let names: Vec<&str> = cache.variable_names.iter().map(String::as_str).collect();
            let subst = up_unifier_substitution(
                ctx,
                hooks,
                &cache.loaded.built,
                self.interner,
                &names,
                &variant.substitution,
            );
            let family = if nat_family {
                nat_family_variant_next_index(
                    ctx,
                    &cache.loaded.built.engine,
                    self.interner,
                    variant,
                    &base,
                )?
            } else {
                let root = variant_family_root(variant.family);
                ctx.make_na(hooks.ops["qidSymbol"], NaValue::Qid(root.into()))
            };
            let parent = match variant.parent {
                Some(parent) => up_nat_exact(ctx, parent as u64)?,
                None => ctx.app(*hooks.ops.get("noParentSymbol")?, vec![]),
            };
            let more = up_bool(ctx, variant.more_in_layer)?;
            let hook = if nat_family {
                "legacyVariantSymbol"
            } else {
                "variantSymbol"
            };
            ctx.app(
                *hooks.ops.get(hook)?,
                vec![term, subst, family, parent, more],
            )
        };
        cache.last_solution = Some(sol_nr);
        self.state.insert(MetaCache::Get(cache));
        Some(result)
    }

    fn meta_variant_unify(
        &mut self,
        ctx: &mut MetaCtx,
        hooks: &MetaHooks,
        redex: DagId,
        disjoint: bool,
        nat_family: bool,
    ) -> Option<DagId> {
        use tnk_core::fresh::{FreshVariableGenerator, VariableFamily};
        use tnk_core::unify::problem::VarSpec;
        use tnk_core::variant::{VariantMode, VariantSearch};

        let kids = ctx.children(redex);
        let (incoming_family, base, filtered, delayed, sol_nr) = if nat_family {
            if kids.len() != 5 {
                return None;
            }
            (
                None,
                down_nat_decimal(ctx, kids[3])?,
                false,
                false,
                down_nat64(ctx, kids[4])? as usize,
            )
        } else {
            if kids.len() != 6 {
                return None;
            }
            let family = VariableFamily::of_root(&qid_text(ctx, kids[3])?)?;
            let (filtered, delayed) = down_variant_options(ctx, kids[4]);
            (
                Some(family),
                "0".to_string(),
                filtered,
                delayed,
                down_nat64(ctx, kids[5])? as usize,
            )
        };
        let blocker_roots = down_term_list_roots(ctx, hooks, kids[2])?;
        let mut roots = Vec::with_capacity(blocker_roots.len() + 1);
        roots.push(kids[1]);
        roots.extend(blocker_roots.iter().copied());
        let key = MetaVariantUnifyCacheKey {
            module: kids[0],
            roots,
            family: incoming_family,
            base: base.clone(),
            disjoint,
            nat_family,
            matching: false,
            filtered,
            delayed,
        };

        let mut cache = if let Some(cache) = self.state.take_variant_unify(&key, ctx, sol_nr) {
            cache
        } else {
            let mut loaded = self.down_module(ctx, hooks, kids[0])?;
            let mut specs_raw: Vec<(String, SortId)> = Vec::new();
            let (pairs, n_lhs) = down_unification_problem(
                ctx,
                hooks,
                kids[1],
                &loaded.built,
                &mut specs_raw,
                disjoint,
            )?;
            if pairs.is_empty() {
                return None;
            }
            let pair_count = pairs.len();
            let range = specs_raw.first().map(|(_, sort)| *sort)?;
            let target_term = if pair_count == 1 {
                let pair_sym =
                    loaded
                        .built
                        .engine
                        .add_op("$metaVariantUnifyPair", vec![range; 2], range);
                let (lhs, rhs) = pairs.into_iter().next().unwrap();
                Term::Op {
                    symbol: pair_sym,
                    args: vec![lhs, rhs],
                }
            } else {
                let lhs_sym = loaded.built.engine.add_op(
                    "$metaVariantUnifyLhs",
                    vec![range; pair_count],
                    range,
                );
                let rhs_sym = loaded.built.engine.add_op(
                    "$metaVariantUnifyRhs",
                    vec![range; pair_count],
                    range,
                );
                let pair_sym =
                    loaded
                        .built
                        .engine
                        .add_op("$metaVariantUnifyPair", vec![range; 2], range);
                let mut lhs = Vec::with_capacity(pair_count);
                let mut rhs = Vec::with_capacity(pair_count);
                for (left, right) in pairs {
                    lhs.push(left);
                    rhs.push(right);
                }
                Term::Op {
                    symbol: pair_sym,
                    args: vec![
                        Term::Op {
                            symbol: lhs_sym,
                            args: lhs,
                        },
                        Term::Op {
                            symbol: rhs_sym,
                            args: rhs,
                        },
                    ],
                }
            };
            let mut blocker_vars = VarIndex::new();
            let blocker_shared = if disjoint {
                &specs_raw[..n_lhs]
            } else {
                specs_raw.as_slice()
            };
            for (name, sort) in blocker_shared {
                blocker_vars.index_of(name, *sort);
            }
            let blocker_terms: Vec<Term> = blocker_roots
                .iter()
                .map(|&root| down_term_to_term(ctx, hooks, root, &loaded.built, &mut blocker_vars))
                .collect::<Option<_>>()?;
            if blocker_vars.count() as usize != blocker_shared.len() {
                return None;
            }
            let namegen = FreshVariableGenerator::new();
            if specs_raw.iter().any(|(name, _)| {
                let bare = name.split_once(':').map_or(name.as_str(), |(bare, _)| bare);
                namegen.variable_name_conflict(bare, incoming_family)
            }) {
                let hook = if disjoint {
                    "noUnifierTripleSymbol"
                } else {
                    "noUnifierPairSymbol"
                };
                return Some(ctx.app(*hooks.ops.get(hook)?, vec![]));
            }
            const FLAGGED_CODE_BIT: u32 = 0x4000_0000;
            let codes: Vec<u32> = specs_raw
                .iter()
                .enumerate()
                .map(|(slot, (name, _))| {
                    let bare = name.split_once(':').map_or(name.as_str(), |(bare, _)| bare);
                    let code = self.interner.intern(bare).index();
                    if disjoint && slot >= n_lhs {
                        code | FLAGGED_CODE_BIT
                    } else {
                        code
                    }
                })
                .collect();
            let bindings: Vec<DagId> = specs_raw
                .iter()
                .enumerate()
                .map(|(slot, (_, sort))| {
                    loaded
                        .built
                        .engine
                        .make_var(*sort, codes[slot], slot as u32)
                })
                .collect();
            let target = loaded
                .built
                .engine
                .instantiate_bindings(&target_term, &bindings);
            let attempt = loaded.built.engine.try_normalize_for_unify(target);
            let target = capture_reducer_fault(&mut self.reducer_fault, attempt)?;
            let blockers = blocker_terms
                .iter()
                .map(|term| loaded.built.engine.instantiate_bindings(term, &bindings))
                .collect();
            let specs: Vec<VarSpec> = specs_raw
                .iter()
                .enumerate()
                .map(|(slot, (source, sort))| {
                    let bare = source
                        .split_once(':')
                        .map_or(source.as_str(), |(bare, _)| bare);
                    VarSpec {
                        sort: *sort,
                        name: maude_variable_name_rank(bare, codes[slot]),
                    }
                })
                .collect();
            let equations = executable_variant_equations(&mut loaded.built, self.interner);
            loaded.built.engine.reset_rewrites();
            let mut names = InternerNames(self.interner);
            let mut env = tnk_core::unify::UnifyEnv {
                e: &mut loaded.built.engine,
                names: &mut names,
            };
            let attempt = VariantSearch::new(
                &mut env,
                target,
                specs,
                blockers,
                equations,
                VariantMode::Incremental,
                incoming_family,
                &base,
            );
            let mut search = capture_variant_error(&mut self.reducer_fault, attempt)?;
            search.enable_unification(env.e, pair_count);
            let canonical_order = search.original_variable_order().to_vec();
            let key_roots = std::iter::once(key.module)
                .chain(key.roots.iter().copied())
                .map(|dag| ctx.root(dag))
                .collect();
            MetaVariantUnifyCache {
                key: key.clone(),
                _key_roots: key_roots,
                loaded,
                search,
                pair_count,
                specs_raw,
                canonical_order,
                n_lhs,
                stream: tnk_core::variant::FilteredVariantUnifierStream::new(filtered),
                upfront: delayed,
                prepared: false,
                exhausted: false,
                rewrite_checkpoint: 0,
                breakdown_checkpoint: SymbolicRewriteCheckpoint::default(),
                rewrite_charge: 0,
                answers: Vec::new(),
                deferred_variant: None,
                restorations: Vec::new(),
                last_solution: None,
            }
        };

        let mut engine = std::mem::take(&mut cache.loaded.built.engine);
        let drive_result = {
            let mut names = InternerNames(self.interner);
            let mut env = tnk_core::unify::UnifyEnv {
                e: &mut engine,
                names: &mut names,
            };
            (|| -> Result<(), ReducerFault> {
                if cache.upfront {
                    cache.prepare(&mut env)?;
                }
                while cache.answers.len() <= sol_nr {
                    if let Some(index) = cache.pop_pending() {
                        cache.answers.push(index);
                        continue;
                    }
                    if cache.exhausted {
                        break;
                    }
                    cache.advance(&mut env)?;
                }
                Ok(())
            })()
        };
        let mut rewrite_charge = cache.take_rewrite_charge();
        if self.interpreter_manager_accounting
            && cache.stream.is_filtered()
            && cache.answers.get(sol_nr).is_none()
        {
            rewrite_charge += engine.rewrites().saturating_sub(cache.rewrite_checkpoint);
        }
        ctx.add_rewrites(rewrite_charge);
        transfer_symbolic_subcounts(ctx, &engine, &mut cache.breakdown_checkpoint);
        cache.loaded.built.engine = engine;
        capture_reducer_fault(&mut self.reducer_fault, drive_result)?;

        let Some(&answer) = cache.answers.get(sol_nr) else {
            let incomplete = cache.search.is_incomplete();
            let hook = match (disjoint, incomplete) {
                (true, false) => "noUnifierTripleSymbol",
                (true, true) => "noUnifierIncompleteTripleSymbol",
                (false, false) => "noUnifierPairSymbol",
                (false, true) => "noUnifierIncompletePairSymbol",
            };
            return Some(ctx.app(*hooks.ops.get(hook)?, vec![]));
        };
        let result_dag = {
            let result_bindings = cache.stream.bindings(answer);
            let mut bindings_original = result_bindings.to_vec();
            for (new_slot, &old_slot) in cache.canonical_order.iter().enumerate() {
                bindings_original[old_slot] = result_bindings[new_slot];
            }
            let third = if nat_family {
                nat_family_unifier_next_index(
                    ctx,
                    &cache.loaded.built.engine,
                    self.interner,
                    &bindings_original,
                    &base,
                )?
            } else {
                ctx.make_na(
                    hooks.ops["qidSymbol"],
                    NaValue::Qid(variant_family_root(cache.stream.family(answer)).into()),
                )
            };
            if disjoint {
                let (lhs_b, rhs_b) = bindings_original.split_at(cache.n_lhs);
                let lhs_names: Vec<&str> = cache.specs_raw[..cache.n_lhs]
                    .iter()
                    .map(|(name, _)| name.as_str())
                    .collect();
                let rhs_names: Vec<&str> = cache.specs_raw[cache.n_lhs..]
                    .iter()
                    .map(|(name, _)| name.as_str())
                    .collect();
                let lhs = up_unifier_substitution(
                    ctx,
                    hooks,
                    &cache.loaded.built,
                    self.interner,
                    &lhs_names,
                    lhs_b,
                );
                let rhs = up_unifier_substitution(
                    ctx,
                    hooks,
                    &cache.loaded.built,
                    self.interner,
                    &rhs_names,
                    rhs_b,
                );
                let hook = if nat_family {
                    "legacyUnificationTripleSymbol"
                } else {
                    "unificationTripleSymbol"
                };
                ctx.app(*hooks.ops.get(hook)?, vec![lhs, rhs, third])
            } else {
                let names: Vec<&str> = cache
                    .specs_raw
                    .iter()
                    .map(|(name, _)| name.as_str())
                    .collect();
                let subst = up_unifier_substitution(
                    ctx,
                    hooks,
                    &cache.loaded.built,
                    self.interner,
                    &names,
                    &bindings_original,
                );
                let hook = if nat_family {
                    "legacyUnificationPairSymbol"
                } else {
                    "matchPairSymbol"
                };
                ctx.app(*hooks.ops.get(hook)?, vec![subst, third])
            }
        };
        cache.last_solution = Some(sol_nr);
        self.state.insert(MetaCache::Unify(cache));
        Some(result_dag)
    }

    fn meta_variant_match(
        &mut self,
        ctx: &mut MetaCtx,
        hooks: &MetaHooks,
        redex: DagId,
    ) -> Option<DagId> {
        use tnk_core::fresh::{FreshVariableGenerator, VariableFamily};
        use tnk_core::unify::problem::VarSpec;
        use tnk_core::variant::{VariantMode, VariantSearch};

        let kids = ctx.children(redex);
        if kids.len() != 6 {
            return None;
        }
        let incoming_family = VariableFamily::of_root(&qid_text(ctx, kids[3])?)?;
        let (filtered, delayed) = down_variant_options(ctx, kids[4]);
        let sol_nr = down_nat64(ctx, kids[5])? as usize;
        let blocker_roots = down_term_list_roots(ctx, hooks, kids[2])?;
        let mut roots = Vec::with_capacity(blocker_roots.len() + 1);
        roots.push(kids[1]);
        roots.extend(blocker_roots.iter().copied());
        let key = MetaVariantUnifyCacheKey {
            module: kids[0],
            roots,
            family: Some(incoming_family),
            base: "0".to_string(),
            disjoint: false,
            nat_family: false,
            matching: true,
            filtered,
            delayed,
        };
        let mut cache = if let Some(cache) = self.state.take_variant_unify(&key, ctx, sol_nr) {
            cache
        } else {
            let mut loaded = self.down_module(ctx, hooks, kids[0])?;
            let conjunction = hooks.ops.get("matchingConjunctionSymbol").copied();
            let pair_symbol = *hooks.ops.get("patternSubjectPairSymbol")?;
            let pair_dags = if Some(ctx.top(kids[1])) == conjunction {
                ctx.children(kids[1])
            } else {
                vec![kids[1]]
            };
            if pair_dags.is_empty() {
                return None;
            }
            let pair_count = pair_dags.len();
            let mut pattern_vars = VarIndex::new();
            let mut subject_vars = VarIndex::new();
            let mut pattern_terms = Vec::with_capacity(pair_count);
            let mut subject_terms = Vec::with_capacity(pair_count);
            for pair in pair_dags {
                if ctx.top(pair) != pair_symbol {
                    return None;
                }
                let pair_kids = ctx.children(pair);
                pattern_terms.push(down_term_to_term(
                    ctx,
                    hooks,
                    *pair_kids.first()?,
                    &loaded.built,
                    &mut pattern_vars,
                )?);
                subject_terms.push(down_term_to_term(
                    ctx,
                    hooks,
                    *pair_kids.get(1)?,
                    &loaded.built,
                    &mut subject_vars,
                )?);
            }
            let target_variables = pattern_vars.count() as usize;
            let specs_raw: Vec<(String, SortId)> = (0..pattern_vars.count())
                .map(|slot| (pattern_vars.name(slot).to_string(), pattern_vars.sort(slot)))
                .collect();
            let namegen = FreshVariableGenerator::new();
            if specs_raw.iter().any(|(name, _)| {
                let bare = name.split_once(':').map_or(name.as_str(), |(bare, _)| bare);
                namegen.variable_name_conflict(bare, Some(incoming_family))
            }) {
                return Some(ctx.app(*hooks.ops.get("noMatchSubstSymbol")?, vec![]));
            }
            let pattern_codes: Vec<u32> = specs_raw
                .iter()
                .map(|(name, _)| {
                    let bare = name.split_once(':').map_or(name.as_str(), |(bare, _)| bare);
                    self.interner.intern(bare).index()
                })
                .collect();
            let pattern_bindings: Vec<DagId> = specs_raw
                .iter()
                .enumerate()
                .map(|(slot, (_, sort))| {
                    loaded
                        .built
                        .engine
                        .make_var(*sort, pattern_codes[slot], slot as u32)
                })
                .collect();
            let pattern_dags: Vec<DagId> = pattern_terms
                .iter()
                .map(|term| {
                    loaded
                        .built
                        .engine
                        .instantiate_bindings(term, &pattern_bindings)
                })
                .collect();

            let subject_codes: Vec<u32> = (0..subject_vars.count())
                .map(|slot| {
                    let source = subject_vars.name(slot);
                    let bare = source.split_once(':').map_or(source, |(bare, _)| bare);
                    self.interner.intern(bare).index()
                })
                .collect();
            let subject_bindings: Vec<DagId> = (0..subject_vars.count())
                .map(|slot| {
                    loaded.built.engine.make_var(
                        subject_vars.sort(slot),
                        subject_codes[slot as usize],
                        slot,
                    )
                })
                .collect();
            let subject_dags: Vec<DagId> = subject_terms
                .iter()
                .map(|term| {
                    loaded
                        .built
                        .engine
                        .instantiate_bindings(term, &subject_bindings)
                })
                .collect();
            let subject_domains: Vec<SortId> = subject_dags
                .iter()
                .map(|&dag| {
                    let sort = loaded.built.engine.sort_of(dag);
                    let kind = loaded.built.engine.sorts().kind_of(sort);
                    loaded.built.engine.sorts().error_sort(kind)
                })
                .collect();
            let subject_pack = loaded.built.engine.add_op(
                "$metaVariantMatchSubjects",
                subject_domains.clone(),
                subject_domains[0],
            );
            let packed = loaded.built.engine.make_free(subject_pack, subject_dags);
            let (packed, restorations) =
                tnk_core::variant::ground_subject_variables(&mut loaded.built.engine, packed);
            let grounded_subjects: Vec<DagId> =
                loaded.built.engine.node(packed).children().collect();

            let mut blocker_vars = VarIndex::new();
            for (name, sort) in &specs_raw {
                blocker_vars.index_of(name, *sort);
            }
            let blocker_terms: Vec<Term> = blocker_roots
                .iter()
                .map(|&root| down_term_to_term(ctx, hooks, root, &loaded.built, &mut blocker_vars))
                .collect::<Option<_>>()?;
            if blocker_vars.count() as usize != target_variables {
                return None;
            }
            let blockers: Vec<DagId> = blocker_terms
                .iter()
                .map(|term| {
                    loaded
                        .built
                        .engine
                        .instantiate_bindings(term, &pattern_bindings)
                })
                .collect();

            let mut target_args = Vec::with_capacity(pair_count * 2);
            for (pattern, subject) in pattern_dags.into_iter().zip(grounded_subjects) {
                target_args.push(pattern);
                target_args.push(subject);
            }
            let domains: Vec<SortId> = target_args
                .iter()
                .map(|&dag| {
                    let sort = loaded.built.engine.sort_of(dag);
                    let kind = loaded.built.engine.sorts().kind_of(sort);
                    loaded.built.engine.sorts().error_sort(kind)
                })
                .collect();
            let target_symbol =
                loaded
                    .built
                    .engine
                    .add_op("$metaVariantMatchingPair", domains.clone(), domains[0]);
            let target = loaded.built.engine.make_free(target_symbol, target_args);
            let specs: Vec<VarSpec> = specs_raw
                .iter()
                .enumerate()
                .map(|(slot, (source, sort))| {
                    let bare = source
                        .split_once(':')
                        .map_or(source.as_str(), |(bare, _)| bare);
                    VarSpec {
                        sort: *sort,
                        name: maude_variable_name_rank(bare, pattern_codes[slot]),
                    }
                })
                .collect();
            let base = (0..subject_vars.count())
                .filter_map(|slot| {
                    subject_vars
                        .name(slot)
                        .split_once(':')
                        .map_or(subject_vars.name(slot), |(bare, _)| bare)
                        .strip_prefix('#')
                        .and_then(|digits| digits.parse::<u64>().ok())
                })
                .max()
                .unwrap_or(0)
                .to_string();
            let equations = executable_variant_equations(&mut loaded.built, self.interner);
            loaded.built.engine.reset_rewrites();
            let mut names = InternerNames(self.interner);
            let mut env = tnk_core::unify::UnifyEnv {
                e: &mut loaded.built.engine,
                names: &mut names,
            };
            let attempt = VariantSearch::new(
                &mut env,
                target,
                specs,
                blockers,
                equations,
                VariantMode::Irredundant,
                Some(incoming_family),
                &base,
            );
            let mut search = capture_variant_error(&mut self.reducer_fault, attempt)?;
            search.skip_root_position();
            let canonical_order = search.original_variable_order().to_vec();
            let mut stored_key = key.clone();
            stored_key.base = base;
            let key_roots = std::iter::once(key.module)
                .chain(key.roots.iter().copied())
                .map(|dag| ctx.root(dag))
                .collect();
            MetaVariantUnifyCache {
                key: stored_key,
                _key_roots: key_roots,
                loaded,
                search,
                pair_count,
                specs_raw,
                canonical_order,
                n_lhs: 0,
                stream: tnk_core::variant::FilteredVariantUnifierStream::new(filtered),
                upfront: true,
                prepared: false,
                exhausted: false,
                rewrite_checkpoint: 0,
                breakdown_checkpoint: SymbolicRewriteCheckpoint::default(),
                rewrite_charge: 0,
                answers: Vec::new(),
                deferred_variant: None,
                restorations,
                last_solution: None,
            }
        };

        let mut engine = std::mem::take(&mut cache.loaded.built.engine);
        let drive_result = {
            let mut names = InternerNames(self.interner);
            let mut env = tnk_core::unify::UnifyEnv {
                e: &mut engine,
                names: &mut names,
            };
            let result = cache.prepare(&mut env);
            if result.is_ok() {
                while cache.answers.len() <= sol_nr {
                    let Some(index) = cache.pop_pending() else {
                        break;
                    };
                    cache.answers.push(index);
                }
            }
            result
        };
        ctx.add_rewrites(cache.take_rewrite_charge());
        transfer_symbolic_subcounts(ctx, &engine, &mut cache.breakdown_checkpoint);
        cache.loaded.built.engine = engine;
        capture_reducer_fault(&mut self.reducer_fault, drive_result)?;

        let Some(&answer) = cache.answers.get(sol_nr) else {
            let hook = if cache.search.is_incomplete() {
                "noMatchIncompleteSubstSymbol"
            } else {
                "noMatchSubstSymbol"
            };
            return Some(ctx.app(*hooks.ops.get(hook)?, vec![]));
        };
        let result_dag = {
            let result_bindings = cache.stream.bindings(answer);
            let mut bindings_original = result_bindings.to_vec();
            for (new_slot, &old_slot) in cache.canonical_order.iter().enumerate() {
                bindings_original[old_slot] = result_bindings[new_slot];
            }
            let names: Vec<&str> = cache
                .specs_raw
                .iter()
                .map(|(name, _)| name.as_str())
                .collect();
            up_unifier_substitution(
                ctx,
                hooks,
                &cache.loaded.built,
                self.interner,
                &names,
                &bindings_original,
            )
        };
        cache.last_solution = Some(sol_nr);
        self.state.insert(MetaCache::Unify(cache));
        Some(result_dag)
    }

    /// `metaSmtSearch(M, S, P, C, kind, fresh, B, n)` performs resumable symbolic rewriting modulo SMT.
    /// The cache key excludes only the requested solution number; each consumed solution charges one outer
    /// rewrite.
    fn meta_smt_search(
        &mut self,
        ctx: &mut MetaCtx,
        hooks: &MetaHooks,
        redex: DagId,
    ) -> Option<DagId> {
        let kids = ctx.children(redex);
        let [
            module_arg,
            initial_arg,
            goal_arg,
            condition_arg,
            arrow_arg,
            fresh_arg,
            bound_arg,
            solution_arg,
        ] = kids.as_slice()
        else {
            return None;
        };
        let module_arg = *module_arg;
        let initial_arg = *initial_arg;
        let goal_arg = *goal_arg;
        let condition_arg = *condition_arg;
        let arrow = down_arrow(ctx, *arrow_arg)?;
        if arrow == Arrow::Bang {
            return None;
        }
        let fresh_base = down_nat_decimal(ctx, *fresh_arg)?;
        let max_depth = if Some(ctx.top(*bound_arg)) == hooks.ops.get("unboundedSymbol").copied() {
            None
        } else {
            Some(u32::try_from(down_nat64(ctx, *bound_arg)?).ok()?)
        };
        let solution_number = usize::try_from(down_nat64(ctx, *solution_arg)?).ok()?;
        let key = MetaSmtSearchCacheKey {
            module: module_arg,
            initial: initial_arg,
            goal: goal_arg,
            condition: condition_arg,
            arrow,
            fresh_base: fresh_base.clone(),
            max_depth,
        };

        let mut cache = if let Some(cache) = self.state.take_smt_search(&key, ctx, solution_number)
        {
            cache
        } else {
            let mut loaded = self.down_module(ctx, hooks, module_arg)?;
            if !loaded.smt_rewrite_valid {
                return None;
            }

            let mut subject_variables = VarIndex::new();
            let initial_attempt = try_down_term_inner(
                ctx,
                hooks,
                initial_arg,
                &mut loaded.built,
                &mut subject_variables,
                self.interner,
            );
            let initial = self.capture_semantic(initial_attempt)??;
            let mut goal_variables = VarIndex::new();
            let goal = down_term_to_term(ctx, hooks, goal_arg, &loaded.built, &mut goal_variables)?;
            let initial_kind = loaded
                .built
                .engine
                .sorts()
                .kind_of(loaded.built.engine.sort_of(initial));
            let goal_kind = loaded
                .built
                .engine
                .sorts()
                .kind_of(loaded.built.engine.term_sort(&goal));
            if initial_kind != goal_kind || !loaded.built.engine.valid_smt_goal(&goal) {
                return None;
            }

            let target_variable_count = goal_variables.count();
            let mut bound_set: BTreeSet<u32> = (0..target_variable_count).collect();
            let condition = down_condition(
                ctx,
                hooks,
                condition_arg,
                &loaded.built,
                &mut goal_variables,
                &mut bound_set,
            )?;

            let subject_variable_count = subject_variables.count();
            let mut variable_names = var_names(&subject_variables);
            let mut goal_variable_dags = Vec::with_capacity(goal_variables.count() as usize);
            for slot in 0..goal_variables.count() {
                let source = goal_variables.name(slot);
                let base = source.split_once(':').map_or(source, |(base, _)| base);
                let name = self.interner.intern(base).index();
                let global_slot = subject_variable_count + slot;
                goal_variable_dags.push(loaded.built.engine.make_var(
                    goal_variables.sort(slot),
                    name,
                    global_slot,
                ));
                variable_names.push(source.to_string());
            }
            let initial_constraint = loaded
                .built
                .engine
                .make_smt_constraint(&condition, &goal_variable_dags)
                .ok()?;
            let goal_smt_variables = (0..target_variable_count)
                .filter(|&slot| {
                    loaded
                        .built
                        .engine
                        .smt_type(goal_variables.sort(slot))
                        .is_some()
                })
                .map(|slot| (slot, goal_variable_dags[slot as usize]))
                .collect();
            loaded.built.engine.reset_rewrites();
            let search = loaded.built.engine.smt_search_with_fresh_base(
                initial,
                initial_constraint,
                goal,
                target_variable_count,
                goal_smt_variables,
                arrow,
                max_depth,
                variable_names,
                &fresh_base,
            )?;
            let key_roots = [module_arg, initial_arg, goal_arg, condition_arg]
                .into_iter()
                .map(|dag| ctx.root(dag))
                .collect();
            MetaSmtSearchCache {
                key: key.clone(),
                _key_roots: key_roots,
                loaded,
                search,
                goal_variables,
                target_variable_count,
                last_solution_index: None,
                last_solution: None,
            }
        };

        let next_solution = cache
            .last_solution_index
            .map_or(0, |last| last.saturating_add(1));
        for current in next_solution..=solution_number {
            let Some(solution) = cache.search.next_solution(&mut cache.loaded.built.engine) else {
                return Some(ctx.app(*hooks.ops.get("smtFailureSymbol")?, Vec::new()));
            };
            ctx.add_rewrites(1);
            cache.last_solution_index = Some(current);
            cache.last_solution = Some(solution);
        }

        let solution = cache.last_solution.as_ref()?;
        let state = cache.search.state_term(solution.state)?;
        let variable_names = cache.search.variable_names().to_vec();
        let up_state = up_smt_term(
            ctx,
            hooks,
            &cache.loaded.built,
            self.interner,
            &variable_names,
            state,
        );
        let up_substitution = up_smt_substitution(
            ctx,
            hooks,
            &cache.loaded.built,
            self.interner,
            &cache.goal_variables,
            cache.target_variable_count,
            &variable_names,
            &solution.bindings,
        );
        let up_constraint = up_smt_term(
            ctx,
            hooks,
            &cache.loaded.built,
            self.interner,
            &variable_names,
            solution.constraint,
        );
        let max_fresh = solution.max_variable_number.to_decimal();
        let succ = *hooks.ops.get("succSymbol")?;
        let zero = ctx.iter_zero(succ)?;
        let up_max_fresh = if max_fresh == "0" {
            zero
        } else {
            ctx.make_iter_decimal(succ, &max_fresh, zero)?
        };
        let result = ctx.app(
            *hooks.ops.get("smtResultSymbol")?,
            vec![up_state, up_substitution, up_constraint, up_max_fresh],
        );
        self.state.insert(MetaCache::SmtSearch(cache));
        Some(result)
    }

    /// `metaSearch(M, S, P, C, kind, B, n)` → the `(n+1)`-th solution `{up(state), up(type), subst}` of
    /// searching from `S` for a state matching `P` (such that `C`) under reachability `kind` (`'*`/`'+`/
    /// `'!`/`'1`) within depth bound `B`, or `failure` (`ResultTriple?`). The object search's rewrite count
    /// at that solution folds into the command count.
    fn meta_search(&mut self, ctx: &mut MetaCtx, hooks: &MetaHooks, redex: DagId) -> Option<DagId> {
        let kids = ctx.children(redex);
        let mut loaded = self.down_module(ctx, hooks, *kids.first()?)?;
        let attempt = try_down_term(ctx, hooks, *kids.get(1)?, &mut loaded.built, self.interner);
        let subj = capture_reducer_fault(&mut self.reducer_fault, attempt)??;
        let mut vars = VarIndex::new();
        let pattern = down_term_to_term(ctx, hooks, *kids.get(2)?, &loaded.built, &mut vars)?;
        let mut bound_set: BTreeSet<u32> = (0..vars.count()).collect();
        let cond = down_condition(
            ctx,
            hooks,
            *kids.get(3)?,
            &loaded.built,
            &mut vars,
            &mut bound_set,
        )?;
        let arrow = down_arrow(ctx, *kids.get(4)?)?;
        let max_depth = down_bound(ctx, hooks, *kids.get(5)?).map(|d| d as u32);
        let sol_nr = down_nat64(ctx, *kids.get(6)?)? as usize;
        let nr = vars.count();
        loaded.built.engine.reset_rewrites();
        let attempt = loaded
            .built
            .engine
            .try_search(subj, pattern, nr, cond, arrow, max_depth);
        let mut search = self.capture_semantic(attempt)?;
        let mut sol = None;
        for _ in 0..=sol_nr {
            let attempt = search.try_next_solution(&mut loaded.built.engine);
            sol = self.capture_semantic(attempt)?;
            if sol.is_none() {
                break;
            }
        }
        let result = match sol {
            Some(s) => {
                // Charge the solution state's rewrite snapshot, not later sibling exploration.
                ctx.add_rewrites(s.rewrites);
                let state = search.state_term(s.state)?;
                let ut = up_parsed_term(ctx, hooks, &loaded.built, self.interner, state);
                let us = up_sort(ctx, hooks, &loaded.built, state);
                let subst = up_substitution(
                    ctx,
                    hooks,
                    &loaded.built,
                    self.interner,
                    &var_names(&vars),
                    &s.bindings,
                );
                ctx.app(*hooks.ops.get("resultTripleSymbol")?, vec![ut, us, subst])
            }
            None => {
                ctx.add_rewrites(loaded.built.engine.rewrites());
                ctx.app(*hooks.ops.get("failure3Symbol")?, vec![])
            }
        };
        Some(result)
    }

    /// `metaApply(M, T, L, σ, n)` returns the `(n+1)`th top application of rule `L` to reduced `T`,
    /// extending σ. The application adds one rewrite beyond subject and result reductions. Labelled rules
    /// must currently be unconditional.
    fn meta_apply(&mut self, ctx: &mut MetaCtx, hooks: &MetaHooks, redex: DagId) -> Option<DagId> {
        let kids = ctx.children(redex);
        let mut loaded = self.down_module(ctx, hooks, *kids.first()?)?;
        let attempt = try_down_term(ctx, hooks, *kids.get(1)?, &mut loaded.built, self.interner);
        let subj = capture_reducer_fault(&mut self.reducer_fault, attempt)??;
        let label = match ctx.repr(*kids.get(2)?) {
            NodeRepr::Qid(s) => s.to_string(),
            _ => return None,
        };
        let attempt = try_down_partial_substitution(
            ctx,
            hooks,
            &mut loaded.built,
            *kids.get(3)?,
            self.interner,
        );
        let partial = capture_reducer_fault(&mut self.reducer_fault, attempt)??;
        let sol_nr = down_nat64(ctx, *kids.get(4)?)? as usize;
        // The labelled rules (cloned out before mutating the engine). Conditional rules need the condition
        // solver — bail rather than misapply (a conditional rule whose condition fails must not fire).
        let rules: Vec<(Term, Term, Vec<String>, u32)> = loaded
            .built
            .rl_traces
            .iter()
            .filter(|t| t.label.as_deref() == Some(label.as_str()))
            .map(|t| {
                (
                    t.lhs.clone(),
                    t.rhs.clone(),
                    t.var_names.clone(),
                    t.var_names.len() as u32,
                )
            })
            .collect();
        if loaded
            .built
            .rl_traces
            .iter()
            .any(|t| t.label.as_deref() == Some(label.as_str()) && !t.condition.is_empty())
        {
            return None;
        }
        loaded.built.engine.reset_rewrites();
        let attempt = loaded.built.engine.try_reduce(subj);
        let subj = self.capture_semantic(attempt)?;
        // Enumerate top matches across the labelled rules (in declaration order), pick the (n+1)-th.
        let mut all: Vec<(usize, Vec<DagId>)> = Vec::new();
        for (ri, (lhs, _, names, nr)) in rules.iter().enumerate() {
            let Some(initial) = rule_initial_bindings(names, &partial) else {
                continue;
            };
            let mut sols = loaded.built.engine.match_solutions_with_bindings(
                lhs.clone(),
                *nr,
                subj,
                false,
                &initial,
            );
            while sols.advance() {
                let b: Vec<DagId> = (0..*nr)
                    .map(|k| sols.binding(k).expect("matcher binds every var"))
                    .collect();
                all.push((ri, b));
            }
        }
        let result = match all.get(sol_nr) {
            Some((ri, bindings)) => {
                let (_, rhs, names, _) = &rules[*ri];
                let res = loaded.built.engine.instantiate_bindings(rhs, bindings);
                let attempt = loaded.built.engine.try_reduce(res);
                let res = self.capture_semantic(attempt)?;
                // subject reduce + result reduce + the rule application (1).
                ctx.add_rewrites(loaded.built.engine.rewrites() + 1);
                let ut = up_parsed_term(ctx, hooks, &loaded.built, self.interner, res);
                let us = up_sort(ctx, hooks, &loaded.built, res);
                let subst =
                    up_substitution(ctx, hooks, &loaded.built, self.interner, names, bindings);
                ctx.app(*hooks.ops.get("resultTripleSymbol")?, vec![ut, us, subst])
            }
            None => {
                ctx.add_rewrites(loaded.built.engine.rewrites());
                ctx.app(*hooks.ops.get("failure3Symbol")?, vec![])
            }
        };
        Some(result)
    }

    /// `metaXmatch(M, P, S, C, minD, maxD, n)` returns the `(n+1)`th top extension match and its context.
    /// Whole-subject matches use the bare hole `[]`. Partial AC matches remain inert rather than returning
    /// an invalid residue context. `C` must be `nil`.
    fn meta_xmatch(&mut self, ctx: &mut MetaCtx, hooks: &MetaHooks, redex: DagId) -> Option<DagId> {
        let kids = ctx.children(redex);
        let mut loaded = self.down_module(ctx, hooks, *kids.first()?)?;
        let mut vars = VarIndex::new();
        let pattern = down_term_to_term(ctx, hooks, *kids.get(1)?, &loaded.built, &mut vars)?;
        let attempt = try_down_term(ctx, hooks, *kids.get(2)?, &mut loaded.built, self.interner);
        let subj = capture_reducer_fault(&mut self.reducer_fault, attempt)??;
        if !is_nil_condition(ctx, hooks, *kids.get(3)?) {
            return None;
        }
        let min_d = down_nat64(ctx, *kids.get(4)?)? as usize;
        let max_d = down_bound(ctx, hooks, *kids.get(5)?);
        let sol_nr = down_nat64(ctx, *kids.get(6)?)? as usize;
        let nr = vars.count();
        loaded.built.engine.reset_rewrites();
        let attempt = loaded.built.engine.try_reduce(subj);
        let subj = self.capture_semantic(attempt)?;
        let mut positions = Vec::new();
        collect_positions(
            &loaded.built.engine,
            subj,
            0,
            &mut Vec::new(),
            min_d,
            max_d,
            &mut positions,
        );
        let mut found = None;
        let mut seen = 0;
        'positions: for path in positions {
            let subterm = subterm_at(&loaded.built.engine, subj, &path);
            let mut solutions =
                loaded
                    .built
                    .engine
                    .match_solutions(pattern.clone(), nr, subterm, true);
            while solutions.advance() {
                if seen == sol_nr {
                    let bindings: Vec<DagId> = (0..nr)
                        .map(|slot| {
                            solutions
                                .binding(slot)
                                .expect("the matcher binds every pattern variable")
                        })
                        .collect();
                    let ordered = solutions
                        .ordered_context_parts()
                        .map(|(prefix, suffix)| (prefix.to_vec(), suffix.to_vec()));
                    let matched = solutions.matched_portion();
                    found = Some((path, bindings, matched, ordered));
                    break 'positions;
                }
                seen += 1;
            }
        }
        let result = match found {
            Some((path, bindings, matched, ordered)) => {
                let subst = up_substitution(
                    ctx,
                    hooks,
                    &loaded.built,
                    self.interner,
                    &var_names(&vars),
                    &bindings,
                );
                let context = up_context_with_portion(
                    ctx,
                    hooks,
                    &loaded.built,
                    self.interner,
                    subj,
                    &path,
                    matched,
                    ordered
                        .as_ref()
                        .map(|(prefix, suffix)| (prefix.as_slice(), suffix.as_slice())),
                );
                ctx.app(*hooks.ops.get("matchPairSymbol")?, vec![subst, context])
            }
            None => ctx.app(*hooks.ops.get("noMatchPairSymbol")?, vec![]),
        };
        ctx.add_rewrites(loaded.built.engine.rewrites());
        Some(result)
    }

    /// `metaXapply(M, T, L, σ, minD, maxD, n)` → the `(n+1)`-th application of a rule labelled `L` at **any
    /// position** of the reduced `T` whose depth is in `[minD, maxD]` → `{up(whole result), up(type),
    /// up(match), context}` (`Result4Tuple`), or `failure`. The context is the subject with the rewritten
    /// position replaced by the hole `[]` (`'f[[]]`, …). Positions are enumerated outermost-first.
    /// The labelled rules must currently be unconditional; supplied partial bindings constrain each
    /// candidate match.
    fn meta_xapply(&mut self, ctx: &mut MetaCtx, hooks: &MetaHooks, redex: DagId) -> Option<DagId> {
        let kids = ctx.children(redex);
        let mut loaded = self.down_module(ctx, hooks, *kids.first()?)?;
        let attempt = try_down_term(ctx, hooks, *kids.get(1)?, &mut loaded.built, self.interner);
        let subj0 = capture_reducer_fault(&mut self.reducer_fault, attempt)??;
        let label = match ctx.repr(*kids.get(2)?) {
            NodeRepr::Qid(s) => s.to_string(),
            _ => return None,
        };
        let attempt = try_down_partial_substitution(
            ctx,
            hooks,
            &mut loaded.built,
            *kids.get(3)?,
            self.interner,
        );
        let partial = capture_reducer_fault(&mut self.reducer_fault, attempt)??;
        let min_d = down_nat64(ctx, *kids.get(4)?)? as usize;
        let max_d = down_bound(ctx, hooks, *kids.get(5)?);
        let sol_nr = down_nat64(ctx, *kids.get(6)?)? as usize;
        let rules: Vec<(Term, Term, Vec<String>, u32)> = loaded
            .built
            .rl_traces
            .iter()
            .filter(|t| t.label.as_deref() == Some(label.as_str()))
            .map(|t| {
                (
                    t.lhs.clone(),
                    t.rhs.clone(),
                    t.var_names.clone(),
                    t.var_names.len() as u32,
                )
            })
            .collect();
        if loaded
            .built
            .rl_traces
            .iter()
            .any(|t| t.label.as_deref() == Some(label.as_str()) && !t.condition.is_empty())
        {
            return None;
        }
        loaded.built.engine.reset_rewrites();
        let attempt = loaded.built.engine.try_reduce(subj0);
        let subj = self.capture_semantic(attempt)?;
        // Positions within the depth band, outermost-first; at each, every labelled rule's top matches.
        let mut positions = Vec::new();
        collect_positions(
            &loaded.built.engine,
            subj,
            0,
            &mut Vec::new(),
            min_d,
            max_d,
            &mut positions,
        );
        let mut all: Vec<MetaXapplySolution> = Vec::new();
        for path in &positions {
            let subterm = subterm_at(&loaded.built.engine, subj, path);
            for (ri, (lhs, _, names, nr)) in rules.iter().enumerate() {
                let Some(initial) = rule_initial_bindings(names, &partial) else {
                    continue;
                };
                let mut sols = loaded.built.engine.match_solutions_with_bindings(
                    lhs.clone(),
                    *nr,
                    subterm,
                    true,
                    &initial,
                );
                while sols.advance() {
                    let bindings: Vec<DagId> = (0..*nr)
                        .map(|k| sols.binding(k).expect("matcher binds every var"))
                        .collect();
                    let ordered = sols
                        .ordered_context_parts()
                        .map(|(prefix, suffix)| (prefix.to_vec(), suffix.to_vec()));
                    let matched = sols.matched_portion();
                    all.push((path.clone(), ri, bindings, matched, ordered));
                }
            }
        }
        let result = match all.get(sol_nr) {
            Some((path, ri, bindings, matched, ordered)) => {
                let (_, rhs, names, _) = &rules[*ri];
                let target = subterm_at(&loaded.built.engine, subj, path);
                let new_sub = loaded.built.engine.instantiate_bindings(rhs, bindings);
                let replacement =
                    replace_matched_portion(&mut loaded.built.engine, target, *matched, new_sub);
                let whole = replace_at(&mut loaded.built.engine, subj, path, replacement);
                let attempt = loaded.built.engine.try_reduce(whole);
                let whole = self.capture_semantic(attempt)?;
                ctx.add_rewrites(loaded.built.engine.rewrites() + 1);
                let ut = up_parsed_term(ctx, hooks, &loaded.built, self.interner, whole);
                let us = up_sort(ctx, hooks, &loaded.built, whole);
                let subst =
                    up_substitution(ctx, hooks, &loaded.built, self.interner, names, bindings);
                let context = up_context_with_portion(
                    ctx,
                    hooks,
                    &loaded.built,
                    self.interner,
                    subj,
                    path,
                    *matched,
                    ordered
                        .as_ref()
                        .map(|(prefix, suffix)| (prefix.as_slice(), suffix.as_slice())),
                );
                ctx.app(
                    *hooks.ops.get("result4TupleSymbol")?,
                    vec![ut, us, subst, context],
                )
            }
            None => {
                ctx.add_rewrites(loaded.built.engine.rewrites());
                ctx.app(*hooks.ops.get("failure4Symbol")?, vec![])
            }
        };
        Some(result)
    }

    /// `metaSearchPath(M, S, P, C, kind, B, n)` → the `Trace` of the breadth-first path to the `(n+1)`-th
    /// search solution: one `{up(state), up(type), up(rule)}` `TraceStep` per arc (the state and the rule
    /// that leaves it), joined by `__`, or `nil` for a zero-length path; `failure` (`Trace?`) when there is
    /// no such solution. Reuses the same search as [`meta_search`](Self::meta_search); the rules are
    /// up-translated by [`up_rule`] (unconditional here — see its note).
    fn meta_search_path(
        &mut self,
        ctx: &mut MetaCtx,
        hooks: &MetaHooks,
        redex: DagId,
    ) -> Option<DagId> {
        let kids = ctx.children(redex);
        let mut loaded = self.down_module(ctx, hooks, *kids.first()?)?;
        let attempt = try_down_term(ctx, hooks, *kids.get(1)?, &mut loaded.built, self.interner);
        let subj = capture_reducer_fault(&mut self.reducer_fault, attempt)??;
        let mut vars = VarIndex::new();
        let pattern = down_term_to_term(ctx, hooks, *kids.get(2)?, &loaded.built, &mut vars)?;
        let mut bound_set: BTreeSet<u32> = (0..vars.count()).collect();
        let cond = down_condition(
            ctx,
            hooks,
            *kids.get(3)?,
            &loaded.built,
            &mut vars,
            &mut bound_set,
        )?;
        let arrow = down_arrow(ctx, *kids.get(4)?)?;
        let max_depth = down_bound(ctx, hooks, *kids.get(5)?).map(|d| d as u32);
        let sol_nr = down_nat64(ctx, *kids.get(6)?)? as usize;
        let nr = vars.count();
        loaded.built.engine.reset_rewrites();
        let attempt = loaded
            .built
            .engine
            .try_search(subj, pattern, nr, cond, arrow, max_depth);
        let mut search = self.capture_semantic(attempt)?;
        let mut sol = None;
        for _ in 0..=sol_nr {
            let attempt = search.try_next_solution(&mut loaded.built.engine);
            sol = self.capture_semantic(attempt)?;
            if sol.is_none() {
                break;
            }
        }
        let Some(s) = sol else {
            ctx.add_rewrites(loaded.built.engine.rewrites());
            return Some(ctx.app(*hooks.ops.get("failureTraceSymbol")?, vec![]));
        };
        ctx.add_rewrites(s.rewrites);
        let steps = search.path(s.state);
        // One TraceStep per arc: state `steps[i]` and the rule that produced its successor `steps[i+1]`.
        let mut trace_steps = Vec::new();
        for i in 0..steps.len().saturating_sub(1) {
            let rule_id = steps[i + 1].via? as usize;
            let ut = up_parsed_term(ctx, hooks, &loaded.built, self.interner, steps[i].term);
            let us = up_sort(ctx, hooks, &loaded.built, steps[i].term);
            let rule = up_rule(ctx, hooks, &loaded.built, &loaded.built.rl_traces[rule_id])?;
            trace_steps.push(ctx.app(*hooks.ops.get("traceStepSymbol")?, vec![ut, us, rule]));
        }
        Some(match trace_steps.len() {
            0 => ctx.app(*hooks.ops.get("nilTraceSymbol")?, vec![]),
            1 => trace_steps.into_iter().next().unwrap(),
            _ => ctx.app(*hooks.ops.get("traceSymbol")?, trace_steps),
        })
    }

    // ---- sort and kind queries ----

    /// `sortLeq(M, T1, T2)` is true exactly when both types share a kind and `T1` is a subsort of `T2`.
    fn meta_sort_leq(
        &mut self,
        ctx: &mut MetaCtx,
        hooks: &MetaHooks,
        redex: DagId,
    ) -> Option<DagId> {
        let kids = ctx.children(redex);
        let loaded = self.down_module(ctx, hooks, *kids.first()?)?;
        let s1 = down_type(ctx, &loaded.built, *kids.get(1)?)?;
        let s2 = down_type(ctx, &loaded.built, *kids.get(2)?)?;
        let sorts = loaded.built.engine.sorts();
        let r = sorts.same_kind(s1, s2) && sorts.leq(s1, s2);
        up_bool(ctx, r)
    }

    /// `sameKind(M, T1, T2)` → `Bool` — whether the two types share a connected component.
    fn meta_same_kind(
        &mut self,
        ctx: &mut MetaCtx,
        hooks: &MetaHooks,
        redex: DagId,
    ) -> Option<DagId> {
        let kids = ctx.children(redex);
        let loaded = self.down_module(ctx, hooks, *kids.first()?)?;
        let s1 = down_type(ctx, &loaded.built, *kids.get(1)?)?;
        let s2 = down_type(ctx, &loaded.built, *kids.get(2)?)?;
        let r = loaded.built.engine.sorts().same_kind(s1, s2);
        up_bool(ctx, r)
    }

    /// `leastSort(M, T)` returns the construction-time least sort of the down-translated term without
    /// reducing it.
    fn meta_least_sort(
        &mut self,
        ctx: &mut MetaCtx,
        hooks: &MetaHooks,
        redex: DagId,
    ) -> Option<DagId> {
        let kids = ctx.children(redex);
        let mut loaded = self.down_module(ctx, hooks, *kids.first()?)?;
        let attempt = try_down_term(ctx, hooks, *kids.get(1)?, &mut loaded.built, self.interner);
        let t = capture_reducer_fault(&mut self.reducer_fault, attempt)??;
        let s = loaded.built.engine.sort_of(t);
        Some(up_type(ctx, hooks, &loaded.built, s))
    }

    /// `lesserSorts(M, T)` → the `SortSet` of sorts strictly below `T` in its component.
    fn meta_lesser_sorts(
        &mut self,
        ctx: &mut MetaCtx,
        hooks: &MetaHooks,
        redex: DagId,
    ) -> Option<DagId> {
        let kids = ctx.children(redex);
        let loaded = self.down_module(ctx, hooks, *kids.first()?)?;
        let s = down_type(ctx, &loaded.built, *kids.get(1)?)?;
        let sorts = loaded.built.engine.sorts();
        let kid = sorts.kind_of(s);
        let lesser: Vec<SortId> = sorts
            .kind(kid)
            .members
            .iter()
            .copied()
            .filter(|&x| x != s && sorts.leq(x, s))
            .collect();
        Some(up_sort_set(ctx, hooks, &loaded.built, &lesser))
    }

    /// `glbSorts(M, T1, T2)` → the `TypeSet` of maximal common lower bounds (greatest lower bounds);
    /// empty when the two types are in different components.
    fn meta_glb_sorts(
        &mut self,
        ctx: &mut MetaCtx,
        hooks: &MetaHooks,
        redex: DagId,
    ) -> Option<DagId> {
        let kids = ctx.children(redex);
        let loaded = self.down_module(ctx, hooks, *kids.first()?)?;
        let query: Vec<SortId> = kids[1..]
            .iter()
            .map(|&type_| down_type(ctx, &loaded.built, type_))
            .collect::<Option<_>>()?;
        let sorts = loaded.built.engine.sorts();
        let glb: Vec<SortId> = match query.as_slice() {
            [] => Vec::new(),
            [only] => vec![*only],
            [first, rest @ ..]
                if rest
                    .iter()
                    .all(|&candidate| sorts.same_kind(*first, candidate)) =>
            {
                let kid = sorts.kind_of(*first);
                let lowers: Vec<SortId> = sorts
                    .kind(kid)
                    .members
                    .iter()
                    .copied()
                    .filter(|&candidate| query.iter().all(|&upper| sorts.leq(candidate, upper)))
                    .collect();
                // Keep the maximal elements of the common lower set (the greatest lower bounds).
                lowers
                    .iter()
                    .copied()
                    .filter(|&candidate| {
                        !lowers
                            .iter()
                            .any(|&other| other != candidate && sorts.leq(candidate, other))
                    })
                    .collect()
            }
            _ => Vec::new(),
        };
        Some(up_sort_set(ctx, hooks, &loaded.built, &glb))
    }

    /// `completeName(M, T)` returns the resolved type when `T` names a sort or kind of `M`.
    fn meta_complete_name(
        &mut self,
        ctx: &mut MetaCtx,
        hooks: &MetaHooks,
        redex: DagId,
    ) -> Option<DagId> {
        let kids = ctx.children(redex);
        let loaded = self.down_module(ctx, hooks, *kids.first()?)?;
        let s = down_type(ctx, &loaded.built, *kids.get(1)?)?;
        Some(up_type(ctx, hooks, &loaded.built, s))
    }

    /// `getKind(M, T)` → the `Kind` (error/top sort) of `T`'s connected component.
    fn meta_get_kind(
        &mut self,
        ctx: &mut MetaCtx,
        hooks: &MetaHooks,
        redex: DagId,
    ) -> Option<DagId> {
        let kids = ctx.children(redex);
        let loaded = self.down_module(ctx, hooks, *kids.first()?)?;
        let s = down_type(ctx, &loaded.built, *kids.get(1)?)?;
        let sorts = loaded.built.engine.sorts();
        let err = sorts.error_sort(sorts.kind_of(s));
        Some(up_type(ctx, hooks, &loaded.built, err))
    }

    /// `getKinds(M)` → the `KindSet` of every connected component's `Kind` (error sort).
    fn meta_get_kinds(
        &mut self,
        ctx: &mut MetaCtx,
        hooks: &MetaHooks,
        redex: DagId,
    ) -> Option<DagId> {
        let kids = ctx.children(redex);
        let loaded = self.down_sort_module(ctx, hooks, *kids.first()?)?;
        let sorts = loaded.built.engine.sorts();
        let errs: Vec<SortId> = sorts.kinds().map(|k| sorts.error_sort(k)).collect();
        Some(up_sort_set(ctx, hooks, &loaded.built, &errs))
    }

    /// `maximalSorts(M, K)` returns the maximal sorts of kind `K`, or remains inert unless `K` is a kind.
    fn meta_maximal_sorts(
        &mut self,
        ctx: &mut MetaCtx,
        hooks: &MetaHooks,
        redex: DagId,
    ) -> Option<DagId> {
        let kids = ctx.children(redex);
        let loaded = self.down_module(ctx, hooks, *kids.first()?)?;
        let k = down_type(ctx, &loaded.built, *kids.get(1)?)?;
        let sorts = loaded.built.engine.sorts();
        if !sorts.sort(k).is_error {
            return None; // not a kind
        }
        let members = &sorts.kind(sorts.kind_of(k)).members;
        let maximal: Vec<SortId> = members
            .iter()
            .copied()
            .filter(|&s| !members.iter().any(|&t| t != s && sorts.leq(s, t)))
            .collect();
        Some(up_sort_set(ctx, hooks, &loaded.built, &maximal))
    }

    /// `minimalSorts(M, K)` → the `SortSet` of `K`'s minimal sorts (those with no proper subsort).
    fn meta_minimal_sorts(
        &mut self,
        ctx: &mut MetaCtx,
        hooks: &MetaHooks,
        redex: DagId,
    ) -> Option<DagId> {
        let kids = ctx.children(redex);
        let loaded = self.down_module(ctx, hooks, *kids.first()?)?;
        let k = down_type(ctx, &loaded.built, *kids.get(1)?)?;
        let sorts = loaded.built.engine.sorts();
        if !sorts.sort(k).is_error {
            return None;
        }
        let members = &sorts.kind(sorts.kind_of(k)).members;
        let minimal: Vec<SortId> = members
            .iter()
            .copied()
            .filter(|&s| !members.iter().any(|&t| t != s && sorts.leq(t, s)))
            .collect();
        Some(up_sort_set(ctx, hooks, &loaded.built, &minimal))
    }

    /// `maximalAritySet(M, Q, D, S)` returns maximal argument-sort lists of arity `|D|` whose components
    /// match `D` and whose range is at most `S`. A domain is maximal when no candidate is pointwise greater.
    fn meta_maximal_arity_set(
        &mut self,
        ctx: &mut MetaCtx,
        hooks: &MetaHooks,
        redex: DagId,
    ) -> Option<DagId> {
        let kids = ctx.children(redex);
        let loaded = self.down_module(ctx, hooks, *kids.first()?)?;
        let op_name = qid_text(ctx, *kids.get(1)?)?;
        let dom_dags = flatten_set(
            ctx,
            *kids.get(2)?,
            hooks.ops.get("nilQidListSymbol").copied(),
            hooks.ops.get("qidListSymbol").copied(),
        );
        let dom_sorts: Vec<SortId> = dom_dags
            .iter()
            .map(|&d| down_type(ctx, &loaded.built, d))
            .collect::<Option<_>>()?;
        let target = down_type(ctx, &loaded.built, *kids.get(3)?)?;
        let sym = *loaded.built.ops.get(&(op_name, dom_sorts.len()))?;
        let sorts = loaded.built.engine.sorts();
        // Candidate declarations: range <= target and each argument in the requested component.
        let candidates: Vec<Vec<SortId>> = loaded
            .built
            .engine
            .symbol_declarations(sym)
            .into_iter()
            .filter(|(dom, range)| {
                sorts.leq(*range, target)
                    && dom.len() == dom_sorts.len()
                    && dom
                        .iter()
                        .zip(&dom_sorts)
                        .all(|(&d, &q)| sorts.same_kind(d, q))
            })
            .map(|(dom, _)| dom)
            .collect();
        // Keep the maximal domains (no other candidate dominates them argument-wise).
        let dominates = |big: &[SortId], small: &[SortId]| {
            big != small && big.iter().zip(small).all(|(&b, &s)| sorts.leq(s, b))
        };
        let maximal: Vec<Vec<SortId>> = candidates
            .iter()
            .filter(|d| !candidates.iter().any(|o| dominates(o, d)))
            .cloned()
            .collect();
        let type_lists: Vec<DagId> = maximal
            .iter()
            .map(|dom| up_type_list(ctx, hooks, &loaded.built, dom))
            .collect();
        // A `TypeListSet` joins type-lists with `_;_`; a single list stays itself (always >= 1 here).
        Some(match type_lists.len() {
            1 => type_lists.into_iter().next().unwrap(),
            _ => ctx.app(hooks.ops["sortSetSymbol"], type_lists),
        })
    }

    /// `wellFormed(M)` reports whether the module meta-term builds.
    fn meta_well_formed_module(
        &mut self,
        ctx: &mut MetaCtx,
        hooks: &MetaHooks,
        redex: DagId,
    ) -> Option<DagId> {
        let kids = ctx.children(redex);
        let ok = self.down_module(ctx, hooks, *kids.first()?).is_some();
        up_bool(ctx, ok)
    }

    /// `wellFormed(M, T)` reports whether `T` builds with argument kinds matching each operator domain.
    /// An invalid module leaves the operation inert.
    fn meta_well_formed_term(
        &mut self,
        ctx: &mut MetaCtx,
        hooks: &MetaHooks,
        redex: DagId,
    ) -> Option<DagId> {
        let kids = ctx.children(redex);
        let mut loaded = self.down_module(ctx, hooks, *kids.first()?)?;
        let attempt = try_down_term(ctx, hooks, *kids.get(1)?, &mut loaded.built, self.interner);
        let ok = match capture_reducer_fault(&mut self.reducer_fault, attempt)? {
            Some(t) => term_well_formed(&loaded.built, t),
            None => false,
        };
        up_bool(ctx, ok)
    }

    /// `wellFormed(M, S)` checks each substitution value and its kind against the variable sort. An invalid
    /// module leaves the operation inert.
    fn meta_well_formed_subst(
        &mut self,
        ctx: &mut MetaCtx,
        hooks: &MetaHooks,
        redex: DagId,
    ) -> Option<DagId> {
        let kids = ctx.children(redex);
        let mut loaded = self.down_module(ctx, hooks, *kids.first()?)?;
        let attempt =
            try_subst_well_formed(ctx, hooks, &mut loaded.built, *kids.get(1)?, self.interner);
        let ok = capture_reducer_fault(&mut self.reducer_fault, attempt)?;
        up_bool(ctx, ok)
    }

    // ---- module reflection ----

    /// `upModule(Q, flat)` reflects module `Q`. Flat mode inlines the import closure and emits a nil import
    /// list; non-flat mode lists imports and only root-owned declarations.
    fn meta_up_module(
        &mut self,
        ctx: &mut MetaCtx,
        hooks: &MetaHooks,
        redex: DagId,
    ) -> Option<DagId> {
        let kids = ctx.children(redex);
        let name = qid_text(ctx, *kids.first()?)?;
        let flat = down_bool(ctx, *kids.get(1)?)?;
        let (module, _) = self.up_module_named(ctx, hooks, &name, flat)?;
        self.state
            .remember_reflection(ctx, module, name.to_string(), flat);
        Some(module)
    }

    /// Build the canonical reflection of a database module and retain the compiled module used to produce
    /// it. The paired value lets `down_module_impl` recognize an unchanged `upModule` result and preserve
    /// symbol/variable creation order instead of reconstructing that unobservable order from declaration
    /// sets.
    fn up_module_named(
        &mut self,
        ctx: &mut MetaCtx,
        hooks: &MetaHooks,
        name: &str,
        flat: bool,
    ) -> Option<(DagId, ModulePieces)> {
        let mut p = self.module_pieces(hooks, name, flat)?;

        let name_qid = ctx.make_na(hooks.ops["qidSymbol"], NaValue::Qid(name.into()));
        // Parameterized non-flat headers carry their parameter list; other forms use the bare name Qid.
        let header = if flat || p.params.is_empty() {
            name_qid
        } else {
            up_header(ctx, hooks, name_qid, &p.params)?
        };

        let imports = up_imports(ctx, hooks, &p.imports)?;
        let sorts = up_sorts_dag(ctx, hooks, &p.sorts);
        let subsorts = up_subsorts_dag(ctx, hooks, &p.subsorts, p.subsort_own_start);
        let ops = up_ops_dag(ctx, hooks, &mut p.loaded, self.interner, &p.ops)?;
        let mbs = up_membs_dag(ctx, hooks, &p.loaded.built, &p.mbs, p.mb_own_end)?;
        let attempt = up_eqs_dag(
            ctx,
            hooks,
            &mut p.loaded.built,
            self.interner,
            &p.eqs,
            p.eq_own_end,
        );
        let eqs = self.capture_semantic(attempt)?;

        let mut args = vec![header, imports, sorts, subsorts, ops, mbs, eqs];
        let ctor = if p.kind == ModuleKind::System {
            args.push(up_rls_dag(
                ctx,
                hooks,
                &p.loaded.built,
                &p.rls,
                p.rl_own_end,
            )?);
            if p.is_strategy {
                args.push(up_strat_decls_dag(ctx, hooks, &p.strat_decls)?);
                let strat_defs = p.strat_defs.clone();
                args.push(up_strat_defs_dag(
                    ctx,
                    hooks,
                    &mut p.loaded,
                    self.interner,
                    &strat_defs,
                )?);
                if p.is_theory {
                    "sthSymbol"
                } else {
                    "smodSymbol"
                }
            } else if p.is_theory {
                "thSymbol"
            } else {
                "modSymbol"
            }
        } else if p.is_theory {
            "fthSymbol"
        } else {
            "fmodSymbol"
        };

        let module = ctx.app(*hooks.ops.get(ctor)?, args);
        Some((module, p))
    }

    /// `upImports(Q)` → the `ImportList` of the module named `Q` (always the module's own imports).
    fn meta_up_imports(
        &mut self,
        ctx: &mut MetaCtx,
        hooks: &MetaHooks,
        redex: DagId,
    ) -> Option<DagId> {
        let kids = ctx.children(redex);
        let name = qid_text(ctx, *kids.first()?)?;
        let pm = self.db.get(&name)?;
        let imports = pm.imports.clone();
        up_imports(ctx, hooks, &imports)
    }

    /// `upView(Q)` → the `View` meta-rep of the view named `Q`: `view Q from <from> to <to> is <sort maps>
    /// <op maps> <strat maps> endv`. Operator-to-term maps are parsed in the source/target signatures and
    /// reified as meta-terms; strategy maps remain unmodelled (empty).
    fn meta_up_view(
        &mut self,
        ctx: &mut MetaCtx,
        hooks: &MetaHooks,
        redex: DagId,
    ) -> Option<DagId> {
        let kids = ctx.children(redex);
        let name = qid_text(ctx, *kids.first()?)?;
        let v = self.views.get(&name)?.clone();
        let qid = hooks.ops["qidSymbol"];

        let mut source_variables = HashMap::new();
        let mut target_variables = HashMap::new();
        for declaration in &v.vars {
            let target_sort = v
                .sort_maps
                .iter()
                .find_map(|(source, target)| (source == &declaration.sort).then_some(target))
                .unwrap_or(&declaration.sort);
            for variable in &declaration.names {
                source_variables.insert(variable.clone(), declaration.sort.clone());
                target_variables.insert(variable.clone(), target_sort.clone());
            }
        }
        let has_term_map = v
            .op_maps
            .iter()
            .any(|mapping| matches!(mapping, OpMap::Term { .. }));
        let mut term_modules = if has_term_map {
            let source_name = module_expr_root_name(&v.from)?;
            let target_name = module_expr_root_name(&v.to)?;
            Some((
                self.module_pieces(hooks, source_name, true)?.loaded,
                self.module_pieces(hooks, target_name, true)?.loaded,
            ))
        } else {
            None
        };
        let op_term_mapping = if has_term_map {
            Some(
                hooks
                    .ops
                    .get("opTermMappingSymbol")
                    .copied()
                    .or_else(|| ctx.resolve_op("op_to`term_.", 2))?,
            )
        } else {
            None
        };

        let header_name = ctx.make_na(qid, NaValue::Qid(name.into()));
        let header = if v.params.is_empty() {
            header_name
        } else {
            up_header(ctx, hooks, header_name, &v.params)?
        };
        let from = up_module_expr(ctx, hooks, &v.from)?;
        let to = up_module_expr(ctx, hooks, &v.to)?;
        let mut sm = Vec::with_capacity(v.sort_maps.len());
        for (a, b) in &v.sort_maps {
            let aq = ctx.make_na(qid, NaValue::Qid(a.as_str().into()));
            let bq = ctx.make_na(qid, NaValue::Qid(b.as_str().into()));
            sm.push(ctx.app(hooks.ops["sortMappingSymbol"], vec![aq, bq]));
        }
        let sort_maps = up_set(
            ctx,
            sm,
            hooks.ops["emptySortMappingSetSymbol"],
            hooks.ops["sortMappingSetSymbol"],
        );

        let mut om = Vec::with_capacity(v.op_maps.len());
        for mapping in &v.op_maps {
            match mapping {
                OpMap::Op {
                    from,
                    to,
                    dom_range,
                } => {
                    let from = canonical_name(from, self.interner);
                    let to = canonical_name(to, self.interner);
                    let from = ctx.make_na(qid, NaValue::Qid(from.into()));
                    let to = ctx.make_na(qid, NaValue::Qid(to.into()));
                    if let Some((domain, range)) = dom_range {
                        let domain = up_type_name_list(ctx, hooks, domain);
                        let range = ctx.make_na(qid, NaValue::Qid(range.as_str().into()));
                        om.push(ctx.app(
                            hooks.ops["opSpecificMappingSymbol"],
                            vec![from, domain, range, to],
                        ));
                    } else {
                        om.push(ctx.app(hooks.ops["opMappingSymbol"], vec![from, to]));
                    }
                }
                OpMap::Term { from, to, .. } => {
                    let (source, target) = term_modules.as_mut()?;
                    let from = qualify_view_variables(from, &source_variables, self.interner);
                    let to = qualify_view_variables(to, &target_variables, self.interner);
                    let (from_term, from_vars, _) =
                        build_logic_command_parses(source, self.interner, &from)
                            .ok()?
                            .into_iter()
                            .next()?;
                    let (to_term, to_vars, _) =
                        build_logic_command_parses(target, self.interner, &to)
                            .ok()?
                            .into_iter()
                            .next()?;
                    let from_names: Vec<String> = (0..from_vars.count())
                        .map(|slot| from_vars.name(slot).to_string())
                        .collect();
                    let to_names: Vec<String> = (0..to_vars.count())
                        .map(|slot| to_vars.name(slot).to_string())
                        .collect();
                    let from = up_pattern(ctx, hooks, &source.built, &from_term, &from_names);
                    let to = up_pattern(ctx, hooks, &target.built, &to_term, &to_names);
                    om.push(ctx.app(op_term_mapping?, vec![from, to]));
                }
            }
        }
        let op_maps = up_set(
            ctx,
            om,
            hooks.ops["emptyOpMappingSetSymbol"],
            hooks.ops["opMappingSetSymbol"],
        );
        let strat_maps = ctx.app(hooks.ops["emptyStratMappingSetSymbol"], vec![]);
        Some(ctx.app(
            hooks.ops["viewSymbol"],
            vec![header, from, to, sort_maps, op_maps, strat_maps],
        ))
    }

    /// The individual declaration-set projections `upSorts`/`upSubsortDecls`/`upOpDecls`/`upMbs`/`upEqs`/
    /// `upRls` — each `(Qid, Bool) ~> <Set>`, the corresponding piece of [`meta_up_module`](Self::meta_up_module).
    fn meta_up_part(
        &mut self,
        ctx: &mut MetaCtx,
        hooks: &MetaHooks,
        redex: DagId,
        part: UpPart,
    ) -> Option<DagId> {
        let kids = ctx.children(redex);
        let name = qid_text(ctx, *kids.first()?)?;
        let flat = down_bool(ctx, *kids.get(1)?)?;
        let mut p = self.module_pieces(hooks, &name, flat)?;
        match part {
            UpPart::Sorts => Some(up_sorts_dag(ctx, hooks, &p.sorts)),
            UpPart::Subsorts => Some(up_subsorts_dag(
                ctx,
                hooks,
                &p.subsorts,
                p.subsort_own_start,
            )),
            UpPart::Ops => up_ops_dag(ctx, hooks, &mut p.loaded, self.interner, &p.ops),
            UpPart::Mbs => up_membs_dag(ctx, hooks, &p.loaded.built, &p.mbs, p.mb_own_end),
            UpPart::Eqs => {
                let attempt = up_eqs_dag(
                    ctx,
                    hooks,
                    &mut p.loaded.built,
                    self.interner,
                    &p.eqs,
                    p.eq_own_end,
                );
                self.capture_semantic(attempt)
            }
            UpPart::Rls => up_rls_dag(ctx, hooks, &p.loaded.built, &p.rls, p.rl_own_end),
        }
    }

    /// `metaParse(M, VS, QL, T?)` → `{up(parsed term), up(least sort)}` (`ResultPair`) after parsing the
    /// token list `QL` in `M`'s grammar, or `noParse(n)` at the furthest token reached by a valid partial
    /// parse. Parsing does not reduce. `VS` supplies typed variables whose names may be abbreviated in
    /// `QL` (`'A:List` lets `'A` name that variable); an explicit token type remains authoritative.
    fn meta_parse(&mut self, ctx: &mut MetaCtx, hooks: &MetaHooks, redex: DagId) -> Option<DagId> {
        let kids = ctx.children(redex);
        let mut loaded = self.down_module(ctx, hooks, *kids.first()?)?;
        let variables = qidset_texts(ctx, hooks, *kids.get(1)?)?;
        let mut texts = qidlist_texts(ctx, hooks, *kids.get(2)?)?;
        for text in &mut texts {
            if text.contains(':') {
                continue;
            }
            if let Some(typed) = variables
                .iter()
                .find(|typed| typed.split_once(':').is_some_and(|(name, _)| name == text))
            {
                text.clone_from(typed);
            }
        }
        let tokens = tokenize(&texts.join(" "), self.interner);
        let result = match build_logic_command_parses(&mut loaded, self.interner, &tokens) {
            Ok(parses) => {
                let mut pairs = Vec::with_capacity(parses.len());
                for (term, vars, dag) in parses {
                    let names: Vec<String> = (0..vars.count())
                        .map(|slot| vars.name(slot).to_string())
                        .collect();
                    let up_term = up_parsed_pattern(ctx, hooks, &loaded.built, &term, &names);
                    let up_sort = up_sort(ctx, hooks, &loaded.built, dag);
                    pairs
                        .push(ctx.app(*hooks.ops.get("resultPairSymbol")?, vec![up_term, up_sort]));
                }
                match pairs.as_slice() {
                    [pair] => *pair,
                    [first, second] => {
                        ctx.app(*hooks.ops.get("ambiguitySymbol")?, vec![*first, *second])
                    }
                    _ => return None,
                }
            }
            Err(_) => {
                // Report the furthest token reached by a valid partial parse.
                let pos = command_parse_furthest(&loaded, self.interner, &tokens);
                let n = up_nat(ctx, pos as u64)?;
                ctx.app(*hooks.ops.get("noParseSymbol")?, vec![n])
            }
        };
        Some(result)
    }

    /// `metaPrettyPrint(M, VS, T, opts, Q)` → the `QidList` of tokens rendering `T` in `M`'s grammar, or (if
    /// `to_string`) `metaPrintToString` → the `String` of the rendered text. Every META-LEVEL print option
    /// is independent; omitting one disables that presentation rule. `None` if `T` does not down-translate.
    fn meta_pretty_print(
        &mut self,
        ctx: &mut MetaCtx,
        hooks: &MetaHooks,
        redex: DagId,
        to_string: bool,
    ) -> Option<DagId> {
        let kids = ctx.children(redex);
        let option_set = *kids.get(3)?;
        let options = PrintOptions {
            mixfix: has_option(ctx, option_set, "mixfix"),
            with_parens: has_option(ctx, option_set, "with-parens"),
            with_sorts: has_option(ctx, option_set, "with-sorts"),
            flat: has_option(ctx, option_set, "flat"),
            format: has_option(ctx, option_set, "format"),
            number: has_option(ctx, option_set, "number"),
            rational: has_option(ctx, option_set, "rat"),
        };
        let mut loaded = self.down_module(ctx, hooks, *kids.first()?)?;
        let attempt = try_down_term(ctx, hooks, *kids.get(2)?, &mut loaded.built, self.interner);
        let term = capture_reducer_fault(&mut self.reducer_fault, attempt)??;
        if to_string {
            let printed = print_with_options(&loaded.built, self.interner, term, options);
            // A string value is raw bytes; the printed ASCII text becomes those bytes.
            return Some(ctx.make_na(
                hooks.ops["stringSymbol"],
                NaValue::Str(printed.into_bytes().into()),
            ));
        }
        let texts = print_qid_tokens_with_options(&loaded.built, self.interner, term, options);
        let qid = hooks.ops["qidSymbol"];
        let qids: Vec<DagId> = texts
            .iter()
            .map(|w| ctx.make_na(qid, NaValue::Qid(w.as_str().into())))
            .collect();
        Some(up_set(
            ctx,
            qids,
            hooks.ops["nilQidListSymbol"],
            hooks.ops["qidListSymbol"],
        ))
    }

    /// `tokenize(S)` scans raw bytes with LEXICAL's dedicated scanner, separate from the module-language
    /// lexer. Whitespace, controls, and unrecognized bytes are skipped; punctuation splits unless
    /// backquoted and is returned as a Qid. An identifier containing invalid UTF-8 leaves the partial hook
    /// unreduced because Qids store UTF-8 text.
    fn lexical_tokenize(
        &mut self,
        ctx: &mut MetaCtx,
        hooks: &MetaHooks,
        redex: DagId,
    ) -> Option<DagId> {
        let arg = *ctx.children(redex).first()?;
        let NodeRepr::Str(input) = ctx.repr(arg) else {
            return None;
        };
        let words = lexical_tokens(input)?;
        let qid_sym = *hooks.ops.get("quotedIdentifierSymbol")?;
        let mut qids = Vec::with_capacity(words.len());
        for word in words {
            let sym = self.interner.intern(&word);
            qids.push(ctx.make_na(qid_sym, NaValue::Qid(self.interner.resolve(sym).into())));
        }
        Some(up_set(
            ctx,
            qids,
            *hooks.ops.get("nilQidListSymbol")?,
            *hooks.ops.get("qidListSymbol")?,
        ))
    }

    /// `printTokens(QL)` formats a token list with punctuation-sensitive spacing. The
    /// `\n`/`\t`/`\s`/`\\` control Qids emit observable String bytes; this byte-level format is separate
    /// from the ordinary term pretty-printer.
    fn lexical_print_tokens(
        &mut self,
        ctx: &mut MetaCtx,
        hooks: &MetaHooks,
        redex: DagId,
    ) -> Option<DagId> {
        let arg = *ctx.children(redex).first()?;
        let words = qidlist_texts(ctx, hooks, arg)?;
        let output = print_lexical_tokens(&words);
        Some(ctx.make_na(*hooks.ops.get("stringSymbol")?, NaValue::Str(output.into())))
    }

    /// Build reflected pieces for module `name`: surface declarations, imports, and membership/equation/
    /// rule trace ranges. `flat` selects the complete flattened declaration set with no imports; otherwise
    /// only the module-owned declarations are returned and imports stay explicit. Root-owned statements
    /// occupy the prefix of the flattened statement and trace vectors.
    fn module_pieces(&mut self, hooks: &MetaHooks, name: &str, flat: bool) -> Option<ModulePieces> {
        let pm = self.db.get(name)?.clone();
        let (flat_pm, statement_homes) =
            flatten_with_homes(name, self.db, self.views, self.interner)
                .map_err(|error| eprintln!("module_pieces {name} flatten: {error}"))
                .ok()?;

        // Imported statements must be parsed in their defining grammar. Build statement-free home
        // signatures first, then remap those grammars onto the flattened symbol table; otherwise variable
        // aliases from the root can make imported equations drop, leaving reflection traces misaligned.
        let mut home_modules = HashMap::<String, LoadedModule>::new();
        for home in statement_homes.iter().flatten() {
            if home_modules.contains_key(home) {
                continue;
            }
            let mut shell = flatten(home, self.db, self.views, self.interner)
                .map_err(|error| eprintln!("module_pieces {name} home {home} flatten: {error}"))
                .ok()?;
            shell.statements.clear();
            let attempt = try_build_loaded_module_with_host_functions(
                &shell,
                self.interner,
                &self.host_functions,
            );
            let built = capture_loaded_module_build(&mut self.reducer_fault, attempt, |error| {
                eprintln!("module_pieces {name} home {home} build: {error}")
            })?;
            home_modules.insert(home.clone(), built);
        }

        let attempt = try_build_loaded_module_homed_traced_with_host_functions(
            &flat_pm,
            &statement_homes,
            &|home| home_modules.get(home),
            self.interner,
            &self.host_functions,
        );
        let (mut loaded, statement_trace_refs) =
            capture_loaded_module_build(&mut self.reducer_fault, attempt, |error| {
                eprintln!("module_pieces {name} build: {error}")
            })?;

        let (sorts, subsorts, raw_ops, imports, subsort_own_start, op_own_start) = if flat {
            let subsort_own_start = flat_pm.subsorts.len().checked_sub(pm.subsorts.len())?;
            let op_own_start = flat_pm.ops.len().checked_sub(pm.ops.len())?;
            (
                flat_pm.sorts.clone(),
                flat_pm.subsorts.clone(),
                flat_pm.ops.clone(),
                Vec::new(),
                subsort_own_start,
                op_own_start,
            )
        } else {
            (
                pm.sorts.clone(),
                pm.subsorts.clone(),
                pm.ops.clone(),
                pm.imports.clone(),
                0,
                0,
            )
        };
        let mut ops: Vec<UpOp> = Vec::with_capacity(raw_ops.len());
        for (op_index, od) in raw_ops.iter().enumerate() {
            let name = canonical_name(&od.name, self.interner);
            let mut decl = od.clone();
            if od.attrs.ditto
                && let Some(primary) = flat_pm.ops.iter().find(|candidate| {
                    !candidate.attrs.ditto
                        && same_compiled_op_profile(&loaded, self.interner, od, candidate)
                })
            {
                // `ditto` is only source shorthand. Reflection emits the inherited symbol-wide
                // attributes on each declaration.
                decl.attrs = primary.attrs.clone();
            }
            let symbol = resolve_source_operator(&loaded, &name, &decl.domain);
            let identity = if decl.attrs.id.is_some() {
                if symbol.is_none() {
                    eprintln!(
                        "module_pieces {} unresolved identity op {} {:?} -> {}",
                        pm.name, name, decl.domain, decl.range
                    );
                }
                let attempt = loaded.built.engine.try_symbol_identity_dag(symbol?);
                capture_reducer_fault(&mut self.reducer_fault, attempt)?
            } else {
                None
            };
            ops.push(UpOp {
                name,
                identity,
                decl,
                ditto: od.attrs.ditto,
                own: op_index >= op_own_start,
            });
        }
        // Statements are root-own first, unlike the import-first signature declarations. Record each
        // own prefix length so the up-map can uniquize only the already-flattened imported suffix.
        let own_trace_refs = statement_trace_refs.get(..pm.statements.len())?;
        let own_rule_slots_and_ids: Vec<(usize, u32)> = own_trace_refs
            .iter()
            .enumerate()
            .filter_map(|(slot, trace)| match trace {
                Some(StatementTraceRef::Rule(id)) => Some((slot, *id as u32)),
                _ => None,
            })
            .collect();
        let own_rule_slots = own_rule_slots_and_ids
            .iter()
            .map(|&(slot, _)| slot)
            .collect::<Vec<_>>();
        let own_rule_ids = own_rule_slots_and_ids
            .iter()
            .map(|&(_, id)| id)
            .collect::<Vec<_>>();
        let own_traces =
            merge_statement_traces(&pm.statements, &loaded, self.interner, own_trace_refs);
        let own_trace_ends = (own_traces.0.len(), own_traces.1.len(), own_traces.2.len());
        let (mbs, eqs, rls) = if flat {
            merge_statement_traces(
                &flat_pm.statements,
                &loaded,
                self.interner,
                &statement_trace_refs,
            )
        } else {
            own_traces
        };
        let reflected_rule_ids = if flat {
            (0..loaded.built.rl_traces.len() as u32).collect::<Vec<_>>()
        } else {
            own_rule_ids.clone()
        };
        let attempt = reorder_rules_like_reflection(
            hooks,
            &mut loaded.built,
            self.interner,
            &reflected_rule_ids,
        );
        let canonical_rule_ids = capture_reducer_fault(&mut self.reducer_fault, attempt)?;
        let canonical_own_rule_ids = if flat { Vec::new() } else { canonical_rule_ids };
        Some(ModulePieces {
            kind: flat_pm.kind,
            is_theory: flat_pm.is_theory,
            is_strategy: flat_pm.is_strategy,
            params: pm.params.clone(),
            sorts,
            subsorts,
            subsort_own_start,
            ops,
            imports,
            mb_own_end: own_trace_ends.0,
            eq_own_end: own_trace_ends.1,
            rl_own_end: own_trace_ends.2,
            own_rule_slots,
            own_rule_ids,
            canonical_own_rule_ids,
            mbs,
            eqs,
            rls,
            strat_decls: if flat {
                flat_pm.strat_decls.clone()
            } else {
                pm.strat_decls.clone()
            },
            strat_defs: if flat {
                flat_pm.strat_defs.clone()
            } else {
                pm.strat_defs.clone()
            },
            loaded,
        })
    }

    /// Build only a reflected module's sort signature. `getKinds` needs the component order created by
    /// the flat meta-module's canonical `SubsortDeclSet`; operators and statements are intentionally absent.
    fn down_sort_module(
        &mut self,
        ctx: &MetaCtx,
        hooks: &MetaHooks,
        m: DagId,
    ) -> Option<LoadedModule> {
        let ctor = ctx.name(ctx.top(m)).to_string();
        if ctor == "upModule" {
            let kids = ctx.children(m);
            let name = qid_text(ctx, *kids.first()?)?;
            let flat = down_bool(ctx, *kids.get(1)?)?;
            return Some(self.module_pieces(hooks, &name, flat)?.loaded);
        }
        let (kind, is_theory, is_strategy, is_object) = module_shape(&ctor)?;
        let kids = ctx.children(m);
        let pm = PreModule {
            name: "%META-SORTS%".to_string(),
            source_line: None,
            diagnostics: Vec::new(),
            kind,
            is_theory,
            is_strategy,
            is_object,
            params: Vec::new(),
            imports: down_imports(ctx, hooks, *kids.get(1)?)?,
            sorts: down_sorts(ctx, hooks, *kids.get(2)?),
            subsorts: down_subsorts(ctx, hooks, *kids.get(3)?),
            ops: Vec::new(),
            vars: Vec::new(),
            statements: Vec::new(),
            strat_decls: Vec::new(),
            strat_defs: Vec::new(),
        };
        let flat = flatten_pre(&pm, self.db, self.views, self.interner).ok()?;
        let attempt =
            try_build_loaded_module_with_host_functions(&flat, self.interner, &self.host_functions);
        capture_loaded_module_build(&mut self.reducer_fault, attempt, |_| {})
    }

    /// Down-translate a meta-module term to an object [`LoadedModule`]: reconstruct its `PreModule`
    /// (imports + sorts + subsorts + ops), run the ordinary flatten (against the db) + build, then
    /// install its inline memberships/equations/rules by down-translating their meta-terms directly into
    /// the built engine. Handles both the **import-expression** form (`[Q]` — sorts/ops/equations all
    /// `none`) and a module with **inline declarations** (what `upModule` emits, or a hand-written one).
    pub fn down_module(
        &mut self,
        ctx: &mut MetaCtx,
        hooks: &MetaHooks,
        m: DagId,
    ) -> Option<LoadedModule> {
        self.down_module_impl(ctx, hooks, m, false)
            .map(|(_, loaded)| loaded)
    }

    /// Down-translate a reflected module while retaining a source [`PreModule`] suitable for insertion
    /// into a [`ModuleDb`]. Ordinary META descent needs only the compiled module and therefore uses
    /// [`Self::down_module`], avoiding the source-term rendering and tokenization performed here.
    pub fn down_module_with_source(
        &mut self,
        ctx: &mut MetaCtx,
        hooks: &MetaHooks,
        m: DagId,
    ) -> Option<(PreModule, LoadedModule)> {
        let (source, loaded) = self.down_module_impl(ctx, hooks, m, true)?;
        Some((source?, loaded))
    }

    fn down_module_impl(
        &mut self,
        ctx: &mut MetaCtx,
        hooks: &MetaHooks,
        m: DagId,
        retain_source: bool,
    ) -> Option<(Option<PreModule>, LoadedModule)> {
        if !retain_source && let Some((name, flat)) = self.state.reflected_source(ctx, m) {
            let loaded = self.module_pieces(hooks, &name, flat)?.loaded;
            return Some((None, loaded));
        }
        let ctor = ctx.name(ctx.top(m)).to_string();
        // A source-backed `upModule(Q, flat)` may remain unreduced when its reflected surface contains a
        // module expression that this up-map cannot encode. Resolve that deferred payload directly through
        // the same module database instead of requiring a lossy reflect/down-translate round trip.
        if ctor == "upModule" {
            let kids = ctx.children(m);
            let name = qid_text(ctx, *kids.first()?)?;
            let flat = down_bool(ctx, *kids.get(1)?)?;
            let loaded = self.module_pieces(hooks, &name, flat)?.loaded;
            let source = retain_source.then(|| self.db.get(&name).cloned()).flatten();
            return Some((source, loaded));
        }
        let (kind, is_theory, is_strategy, is_object) = module_shape(&ctor)?;
        let kids = ctx.children(m);
        // Constructor layout: [0]=Header(Qid), [1]=ImportList, [2]=SortSet, [3]=SubsortDeclSet,
        // [4]=OpDeclSet, [5]=MembAxSet, [6]=EquationSet, [7]=RuleSet (system only), [8,9]=Strat* (smod).
        let (name, params) = down_header(ctx, hooks, *kids.first()?)?;
        // `upModule` stores declarations in idempotent AC sets. Normalization may remove duplicate imported
        // declarations, so a normalized reflection is not generally DAG-equal to a freshly built one.
        // At insertion, compare modulo those sets and reuse the database module to retain object-completion
        // and statement metadata. Its executable rules still adopt the reflected RuleSet's canonical order
        // because child interpreters rebuild dependents from the retained module.
        let mut source_op_order = None;
        if self.db.get(&name).is_some() {
            for flat in [true, false] {
                if let Some((candidate, pieces)) = self.up_module_named(ctx, hooks, &name, flat)
                    && reflected_modules_equal(ctx, hooks, candidate, m)
                {
                    if retain_source && !flat {
                        // `insertModule(upModule(..., false))` retains source-only metadata, but the
                        // engine and retained source must adopt the canonical OpDeclSet/RuleSet order
                        // carried by the reflected value. Rebuild from the original declarations in
                        // that order rather than down-translating statement bodies (which loses
                        // source compilation metadata and changes rewrite accounting).
                        let reflected_ops = down_ops(ctx, hooks, *kids.get(4)?, self.interner)?;
                        let op_order: HashMap<(String, Vec<String>, String), usize> = reflected_ops
                            .iter()
                            .enumerate()
                            .map(|(index, op)| {
                                (
                                    (
                                        canonical_name(&op.name, self.interner),
                                        op.domain.clone(),
                                        op.range.clone(),
                                    ),
                                    index,
                                )
                            })
                            .collect();
                        let mut source = self.db.get(&name)?.clone();
                        // Sort and subsort declarations are idempotent AC sets at META-LEVEL. Retain
                        // their decoded canonical form so a later `upModule` in the child does not
                        // recreate source duplicates and charge an extra normalization rewrite.
                        source.imports = down_imports(ctx, hooks, *kids.get(1)?)?;
                        source.sorts = down_sorts(ctx, hooks, *kids.get(2)?);
                        source.subsorts = down_subsorts(ctx, hooks, *kids.get(3)?);
                        // `ditto` is positional source shorthand. Materialize the inherited attributes
                        // before canonical sorting can separate an overload from its primary declaration.
                        for (op, reflected) in source.ops.iter_mut().zip(&pieces.ops) {
                            if op.attrs.ditto {
                                op.attrs = reflected.decl.attrs.clone();
                            }
                        }
                        source.ops.sort_by_key(|op| {
                            op_order
                                .get(&(
                                    canonical_name(&op.name, self.interner),
                                    op.domain.clone(),
                                    op.range.clone(),
                                ))
                                .copied()
                                .unwrap_or(usize::MAX)
                        });
                        // The signature builder resolves identities eagerly. Retain reflected order within
                        // each arity class while making nullary identities available first.
                        source.ops.sort_by_key(|op| !op.domain.is_empty());
                        reorder_source_rules(
                            &mut source,
                            &pieces.own_rule_slots,
                            &pieces.own_rule_ids,
                            &pieces.canonical_own_rule_ids,
                        );
                        // Imported statements must still parse in their defining grammar. Reuse the
                        // homed build path from `module_pieces`, but against a temporary database whose
                        // root entry is the canonically reordered retained source.
                        let mut reordered_db = self.db.clone();
                        reordered_db.insert(source.clone());
                        let (flattened, statement_homes) =
                            flatten_with_homes(&name, &reordered_db, self.views, self.interner)
                                .ok()?;
                        let mut home_modules = HashMap::<String, LoadedModule>::new();
                        for home in statement_homes.iter().flatten() {
                            if home_modules.contains_key(home) {
                                continue;
                            }
                            let mut shell =
                                flatten(home, &reordered_db, self.views, self.interner).ok()?;
                            shell.statements.clear();
                            let attempt = try_build_loaded_module_with_host_functions(
                                &shell,
                                self.interner,
                                &self.host_functions,
                            );
                            let built = capture_loaded_module_build(
                                &mut self.reducer_fault,
                                attempt,
                                |_| {},
                            )?;
                            home_modules.insert(home.clone(), built);
                        }
                        let attempt = try_build_loaded_module_homed_traced_with_host_functions(
                            &flattened,
                            &statement_homes,
                            &|home| home_modules.get(home),
                            self.interner,
                            &self.host_functions,
                        );
                        let (loaded, _) =
                            capture_loaded_module_build(&mut self.reducer_fault, attempt, |_| {})?;
                        return Some((Some(source), loaded));
                    }
                    let mut order = HashMap::new();
                    for (index, op) in pieces.ops.iter().enumerate() {
                        order
                            .entry((
                                op.name.clone(),
                                op.decl.domain.clone(),
                                op.decl.range.clone(),
                            ))
                            .or_insert(index);
                    }
                    source_op_order = Some(order);
                    break;
                }
            }
        }
        let imports = down_imports(ctx, hooks, *kids.get(1)?)?;
        let sorts = down_sorts(ctx, hooks, *kids.get(2)?);
        let subsorts = down_subsorts(ctx, hooks, *kids.get(3)?);
        let mut ops = down_ops(ctx, hooks, *kids.get(4)?, self.interner)?;
        if let Some(order) = &source_op_order {
            ops.sort_by_key(|op| {
                order
                    .get(&(
                        canonical_name(&op.name, self.interner),
                        op.domain.clone(),
                        op.range.clone(),
                    ))
                    .copied()
                    .unwrap_or(usize::MAX)
            });
        }

        // Declare constants (arity 0) first: `build_module` resolves an `id(c)`/`left-id`/`right-id`
        // identity against the *already-declared* ops. This stable partition preserves the recovered
        // same-arity source order while ensuring every identity constant precedes its operator.
        ops.sort_by_key(|o| !o.domain.is_empty());
        let mut pm = PreModule {
            name,
            source_line: None,
            diagnostics: Vec::new(),
            kind,
            is_theory,
            is_strategy,
            // Object declarations are already lowered in the reflected signature. Retaining this bit is
            // still required so object-pattern completion runs when an inserted module is rebuilt.
            is_object,
            params,
            imports,
            sorts,
            subsorts,
            ops,
            vars: Vec::new(),
            statements: Vec::new(), // inline statements are down-translated post-build (below)
            strat_decls: Vec::new(),
            strat_defs: Vec::new(),
        };
        let flat = match flatten_pre(&pm, self.db, self.views, self.interner) {
            Ok(flat) => flat,
            Err(_) => return None,
        };
        // Install every reflected statement in the loader's pre-binding transaction. Signature building
        // validates and resolves HostFunctionSymbol attachments against the configured catalog, but their
        // one-way bindings are committed only after this callback succeeds. In particular, ordinary and
        // owise equations must reach a strict host operator before binding seals its top symbol.
        let mut source_statements = retain_source.then(Vec::new);
        let mut loaded = match try_build_loaded_module_with_host_functions_and_inline_statements(
            &flat,
            self.interner,
            &self.host_functions,
            |built, interner| {
                // A named module's declared variables materialize its per-sort VariableSymbols in
                // declaration order. Reproduce that module-lifetime order on every meta down-translation;
                // otherwise independent `metaNormalize` calls can AC-sort the same variables differently.
                for var in &flat.vars {
                    let sort = if let Some(inner) = var
                        .sort
                        .strip_prefix('[')
                        .and_then(|name| name.strip_suffix(']'))
                    {
                        let first = inner
                            .split(',')
                            .next()
                            .ok_or_else(|| "empty reflected kind variable sort".to_string())?
                            .trim();
                        let member = *built
                            .sorts
                            .get(first)
                            .ok_or_else(|| format!("unknown reflected variable sort `{first}`"))?;
                        let kind = built.engine.sorts().kind_of(member);
                        built.engine.sorts().error_sort(kind)
                    } else {
                        *built.sorts.get(&var.sort).ok_or_else(|| {
                            format!("unknown reflected variable sort `{}`", var.sort)
                        })?
                    };
                    built.engine.variable_symbol(sort);
                }

                // Imported statements were loaded from `flat` immediately before this callback. Decode
                // the reflected module's own statements directly into the same still-unbound engine.
                install_membs(
                    ctx,
                    hooks,
                    *kids
                        .get(5)
                        .ok_or_else(|| "reflected module has no membership set".to_string())?,
                    built,
                    source_statements.as_mut(),
                    interner,
                )
                .ok_or_else(|| "invalid reflected membership set".to_string())?;

                install_eqs(
                    ctx,
                    hooks,
                    *kids
                        .get(6)
                        .ok_or_else(|| "reflected module has no equation set".to_string())?,
                    built,
                    source_statements.as_mut(),
                    interner,
                )
                .ok_or_else(|| "invalid reflected equation set".to_string())?;

                if kind == ModuleKind::System {
                    install_rules(
                        ctx,
                        hooks,
                        *kids
                            .get(7)
                            .ok_or_else(|| "reflected system module has no rule set".to_string())?,
                        built,
                        interner,
                        source_statements.as_mut(),
                    )
                    .map_err(LoadedModuleBuildError::Reducer)?
                    .ok_or_else(|| "invalid reflected rule set".to_string())?;
                }
                Ok(())
            },
        ) {
            Ok(loaded) => loaded,
            Err(LoadedModuleBuildError::Reducer(fault)) => {
                debug_assert!(self.reducer_fault.is_none());
                self.reducer_fault = Some(fault);
                return None;
            }
            Err(LoadedModuleBuildError::Invalid(_)) => return None,
        };

        if is_strategy {
            pm.strat_decls = down_strat_decls(ctx, hooks, *kids.get(8)?)?;
            let attempt =
                try_down_strat_defs(ctx, hooks, *kids.get(9)?, &mut loaded.built, self.interner);
            pm.strat_defs = capture_reducer_fault(&mut self.reducer_fault, attempt)??;
            loaded.built.strat_defs.clone_from(&pm.strat_defs);
        }

        if let Some(statements) = source_statements {
            pm.statements = statements;
        }
        // `build_loaded_module` saw an intentionally statement-free shell. Inline meta statements
        // are installed above, so refresh the restriction bit only after the final engine exists.
        loaded.refresh_smt_rewrite_valid(&pm);
        Some((retain_source.then_some(pm), loaded))
    }

    /// Decode the reflected `View` representation emitted by `upView` for insertion into a child
    /// interpreter's live view database.
    pub fn down_view(&mut self, ctx: &MetaCtx, hooks: &MetaHooks, view: DagId) -> Option<ViewDecl> {
        if hooks.ops.get("viewSymbol") != Some(&ctx.top(view))
            && !ctx.name(ctx.top(view)).starts_with("view")
        {
            return None;
        }
        let kids = ctx.children(view);
        let header = kids.first().copied()?;
        let (name, params) = down_header(ctx, hooks, header)?;
        let from = kids
            .get(1)
            .copied()
            .and_then(|node| down_module_expr(ctx, hooks, node))?;
        let to = kids
            .get(2)
            .copied()
            .and_then(|node| down_module_expr(ctx, hooks, node))?;

        let sort_maps = flatten_set(
            ctx,
            *kids.get(3)?,
            hooks.ops.get("emptySortMappingSetSymbol").copied(),
            hooks.ops.get("sortMappingSetSymbol").copied(),
        )
        .into_iter()
        .map(|mapping| {
            if hooks.ops.get("sortMappingSymbol") != Some(&ctx.top(mapping)) {
                return None;
            }
            let args = ctx.children(mapping);
            Some((
                qid_text(ctx, *args.first()?)?,
                qid_text(ctx, *args.get(1)?)?,
            ))
        })
        .collect::<Option<Vec<_>>>()?;

        let mappings = flatten_set(
            ctx,
            *kids.get(4)?,
            hooks.ops.get("emptyOpMappingSetSymbol").copied(),
            hooks.ops.get("opMappingSetSymbol").copied(),
        );
        let is_term_map = |mapping: DagId| {
            hooks.ops.get("opTermMappingSymbol") == Some(&ctx.top(mapping))
                || ctx.name(ctx.top(mapping)) == "op_to`term_."
        };
        let has_term_map = mappings.iter().copied().any(is_term_map);
        let mut term_modules = if has_term_map {
            let source_name = module_expr_root_name(&from)?;
            let target_name = module_expr_root_name(&to)?;

            Some((
                self.module_pieces(hooks, source_name, true)?.loaded,
                self.module_pieces(hooks, target_name, true)?.loaded,
            ))
        } else {
            None
        };
        let is_specific_map = |mapping: DagId| {
            hooks.ops.get("opSpecificMappingSymbol") == Some(&ctx.top(mapping))
                || ctx.name(ctx.top(mapping)) == "op_:_->_to_."
        };
        let mut op_maps = Vec::with_capacity(mappings.len());
        for mapping in mappings {
            let args = ctx.children(mapping);
            if is_specific_map(mapping) {
                let from = qid_text(ctx, *args.first()?)?;
                let domain = down_typelist(ctx, hooks, *args.get(1)?);
                let range = qid_text(ctx, *args.get(2)?)?;
                let to = qid_text(ctx, *args.get(3)?)?;
                op_maps.push(OpMap::Op {
                    from: tokenize(&from, self.interner),
                    to: tokenize(&to, self.interner),
                    dom_range: Some((domain, range)),
                });
            } else if hooks.ops.get("opMappingSymbol") == Some(&ctx.top(mapping)) {
                let from = qid_text(ctx, *args.first()?)?;
                let to = qid_text(ctx, *args.get(1)?)?;
                op_maps.push(OpMap::Op {
                    from: tokenize(&from, self.interner),
                    to: tokenize(&to, self.interner),
                    dom_range: None,
                });
            } else if is_term_map(mapping) {
                let (source, target) = term_modules.as_mut()?;

                let mut from_vars = VarIndex::new();
                let from_term = match down_term_to_term(
                    ctx,
                    hooks,
                    *args.first()?,
                    &source.built,
                    &mut from_vars,
                ) {
                    Some(term) => term,
                    None => {
                        return None;
                    }
                };
                let from_names: Vec<String> = (0..from_vars.count())
                    .map(|slot| from_vars.name(slot).to_string())
                    .collect();
                let mut to_vars = VarIndex::new();
                let to_term =
                    match down_term_to_term(ctx, hooks, *args.get(1)?, &target.built, &mut to_vars)
                    {
                        Some(term) => term,
                        None => {
                            return None;
                        }
                    };
                let to_names: Vec<String> = (0..to_vars.count())
                    .map(|slot| to_vars.name(slot).to_string())
                    .collect();
                op_maps.push(OpMap::Term {
                    from: source_term_tokens(&source.built, self.interner, &from_term, &from_names),
                    to: source_term_tokens(&target.built, self.interner, &to_term, &to_names),
                    dom_range: None,
                });
            } else {
                return None;
            }
        }

        Some(ViewDecl {
            name,
            source_line: None,
            params,
            from,
            to,
            vars: Vec::new(),
            sort_maps,
            op_maps,
        })
    }
}

/// Add explicit sorts to a view mapping's declared variables without otherwise disturbing its token
/// structure. META-MODULE's operator-to-term mapping carries terms, not the view's variable declarations.
fn qualify_view_variables(
    tokens: &[Token],
    variables: &HashMap<String, String>,
    interner: &mut Interner,
) -> Vec<Token> {
    let mut qualified = Vec::with_capacity(tokens.len());
    for token in tokens {
        let text = interner.resolve(token.sym);
        if !text.contains(':')
            && let Some(sort) = variables.get(text)
        {
            qualified.extend(tokenize(&format!("{text}:{sort}"), interner));
        } else {
            qualified.push(*token);
        }
    }
    qualified
}

/// The semantic shape of a reflected module-constructor operator name.
fn module_shape(ctor: &str) -> Option<(ModuleKind, bool, bool, bool)> {
    if ctor.starts_with("fmod") {
        Some((ModuleKind::Functional, false, false, false))
    } else if ctor.starts_with("fth") {
        Some((ModuleKind::Functional, true, false, false))
    } else if ctor.starts_with("smod") {
        Some((ModuleKind::System, false, true, false))
    } else if ctor.starts_with("sth") || ctor.starts_with("ssth") {
        Some((ModuleKind::System, true, true, false))
    } else if ctor.starts_with("omod") {
        Some((ModuleKind::System, false, false, true))
    } else if ctor.starts_with("oth") {
        Some((ModuleKind::System, true, false, true))
    } else if ctor.starts_with("mod") {
        Some((ModuleKind::System, false, false, false))
    } else if ctor.starts_with("th") {
        Some((ModuleKind::System, true, false, false))
    } else {
        None
    }
}

/// Compare reflected modules modulo the idempotence of their top-level declaration sets. `upModule`
/// constructs those sets before META-LEVEL's equations remove duplicate imported declarations, so plain
/// DAG equality cannot recognize the normalized value later delivered to `insertModule`.
fn reflected_modules_equal(ctx: &MetaCtx, hooks: &MetaHooks, left: DagId, right: DagId) -> bool {
    if ctx.top(left) != ctx.top(right) {
        return false;
    }
    let left_kids = ctx.children(left);
    let right_kids = ctx.children(right);
    if left_kids.len() != right_kids.len()
        || left_kids.len() < 7
        || !ctx.deep_equal(left_kids[0], right_kids[0])
        || !ctx.deep_equal(left_kids[1], right_kids[1])
    {
        return false;
    }

    let mut sets = vec![
        (2, "emptySortSetSymbol", "sortSetSymbol"),
        (3, "emptySubsortDeclSetSymbol", "subsortDeclSetSymbol"),
        (4, "emptyOpDeclSetSymbol", "opDeclSetSymbol"),
        (5, "emptyMembAxSetSymbol", "membAxSetSymbol"),
        (6, "emptyEquationSetSymbol", "equationSetSymbol"),
    ];
    if left_kids.len() >= 8 {
        sets.push((7, "emptyRuleSetSymbol", "ruleSetSymbol"));
    }
    if left_kids.len() >= 10 {
        sets.push((8, "emptyStratDeclSetSymbol", "stratDeclSetSymbol"));
        sets.push((9, "emptyStratDefSetSymbol", "stratDefSetSymbol"));
    }

    sets.into_iter().all(|(index, empty, join)| {
        reflected_sets_equal(
            ctx,
            left_kids[index],
            right_kids[index],
            hooks.ops.get(empty).copied(),
            hooks.ops.get(join).copied(),
        )
    })
}

fn reflected_sets_equal(
    ctx: &MetaCtx,
    left: DagId,
    right: DagId,
    empty: Option<SymbolId>,
    join: Option<SymbolId>,
) -> bool {
    let left = flatten_set(ctx, left, empty, join);
    let right = flatten_set(ctx, right, empty, join);
    let mut left_by_hash: HashMap<u64, Vec<DagId>> = HashMap::new();
    let mut right_by_hash: HashMap<u64, Vec<DagId>> = HashMap::new();
    for item in left {
        left_by_hash
            .entry(ctx.dag_hash(item))
            .or_default()
            .push(item);
    }
    for item in right {
        right_by_hash
            .entry(ctx.dag_hash(item))
            .or_default()
            .push(item);
    }
    let contains_all = |needles: &HashMap<u64, Vec<DagId>>, haystack: &HashMap<u64, Vec<DagId>>| {
        needles.iter().all(|(hash, items)| {
            haystack.get(hash).is_some_and(|candidates| {
                items
                    .iter()
                    .all(|&item| candidates.iter().any(|&other| ctx.deep_equal(item, other)))
            })
        })
    };
    contains_all(&left_by_hash, &right_by_hash) && contains_all(&right_by_hash, &left_by_hash)
}

// ---- inline declaration down-translation (sorts / subsorts / ops / membs / eqs / rules) ----

/// The text of a `Qid` leaf (a meta sort/op/variable name), or `None` if `d` is not a `Qid`.
fn qid_text(ctx: &MetaCtx, d: DagId) -> Option<String> {
    match ctx.repr(d) {
        NodeRepr::Qid(s) => Some(s.to_string()),
        _ => None,
    }
}

/// Decode a plain or parameterized reflected module/view header.
fn down_header(
    ctx: &MetaCtx,
    hooks: &MetaHooks,
    header: DagId,
) -> Option<(String, Vec<Parameter>)> {
    if let Some(name) = qid_text(ctx, header) {
        return Some((name, Vec::new()));
    }
    let header_symbol = hooks.ops.get("headerSymbol").copied();
    if Some(ctx.top(header)) != header_symbol && ctx.name(ctx.top(header)) != "_{_}" {
        return None;
    }
    let kids = ctx.children(header);
    let name = qid_text(ctx, *kids.first()?)?;
    let decl_list = *kids.get(1)?;
    let join = hooks.ops.get("parameterDeclListSymbol").copied();
    let decl_symbol = hooks.ops.get("parameterDeclSymbol").copied();
    let mut params = Vec::new();
    for decl in flatten_set(ctx, decl_list, None, join) {
        if Some(ctx.top(decl)) != decl_symbol && ctx.name(ctx.top(decl)) != "_::_" {
            return None;
        }
        let args = ctx.children(decl);
        let parameter = qid_text(ctx, *args.first()?)?;
        let theory = match down_module_expr(ctx, hooks, *args.get(1)?)? {
            ModuleExpr::Named(theory) => theory,
            _ => return None,
        };
        params.push(Parameter {
            name: parameter,
            theory,
        });
    }
    Some((name, params))
}

/// Flatten a meta declaration set joined by a binary constructor `join` (`__`/`_;_`) into its element
/// DAGs in left-to-right order, dropping the `empty` constant (`none`/`nil`). A single element, the empty
/// constant, or a (AU/ACU-canonicalized) tree of `join` all collapse to a flat element list.
fn flatten_set(
    ctx: &MetaCtx,
    d: DagId,
    empty: Option<SymbolId>,
    join: Option<SymbolId>,
) -> Vec<DagId> {
    fn go(
        ctx: &MetaCtx,
        d: DagId,
        empty: Option<SymbolId>,
        join: Option<SymbolId>,
        out: &mut Vec<DagId>,
    ) {
        let sym = Some(ctx.top(d));
        if sym == empty
            || (ctx.name(ctx.top(d)) == "none"
                && ctx.children(d).is_empty()
                && !matches!(ctx.repr(d), NodeRepr::Qid(_)))
        {
            return;
        }
        if sym == join || join.is_some_and(|join| ctx.name(ctx.top(d)) == ctx.name(join)) {
            for c in ctx.children(d) {
                go(ctx, c, empty, join, out);
            }
            return;
        }
        out.push(d);
    }
    let mut out = Vec::new();
    go(ctx, d, empty, join, &mut out);
    out
}

/// A meta `QidList` (`nil` | `__`-joined `Qid`s, or a single `Qid`) → the token text strings, in order —
/// `metaParse`'s token sequence.
fn qidlist_texts(ctx: &MetaCtx, hooks: &MetaHooks, d: DagId) -> Option<Vec<String>> {
    let empty = hooks.ops.get("nilQidListSymbol").copied();
    let join = hooks.ops.get("qidListSymbol").copied();
    flatten_set(ctx, d, empty, join)
        .iter()
        .map(|&x| qid_text(ctx, x))
        .collect()
}

/// A meta `QidSet` (`none` | `_;_`-joined `Qid`s, or a single `Qid`) → its texts. `VariableSet` is a
/// subsort of `QidSet`, so META-LEVEL's shared hooks are the canonical flattening symbols.
fn qidset_texts(ctx: &MetaCtx, hooks: &MetaHooks, d: DagId) -> Option<Vec<String>> {
    let empty = hooks.ops.get("emptyQidSetSymbol").copied();
    let join = hooks.ops.get("qidSetSymbol").copied();
    flatten_set(ctx, d, empty, join)
        .iter()
        .map(|&x| qid_text(ctx, x))
        .collect()
}

/// Scanner backing LEXICAL `tokenize`, separate from module-language tokenization. Comments and dots have
/// no special meaning; bad/control bytes are skipped; punctuation splits unless backquoted. Returned Qids
/// omit syntactic backquotes before punctuation while retaining semantic backquote separators.
fn lexical_tokens(input: &[u8]) -> Option<Vec<String>> {
    fn control(b: u8) -> bool {
        b < b' ' || b == 0x7f
    }
    fn punct(b: u8) -> bool {
        matches!(b, b'(' | b')' | b'[' | b']' | b'{' | b'}' | b',')
    }
    fn normal_atom(input: &[u8], at: usize) -> Option<usize> {
        let b = *input.get(at)?;
        if b == b'"' {
            let mut i = at + 1;
            while let Some(&c) = input.get(i) {
                match c {
                    b'"' => return Some(i + 1),
                    b'\\' => {
                        let &next = input.get(i + 1)?;
                        if control(next) && next != b'\n' {
                            return None;
                        }
                        i += 2;
                    }
                    _ if control(c) => return None,
                    _ => i += 1,
                }
            }
            return None;
        }
        (!control(b)
            && !matches!(
                b,
                b' ' | b'(' | b')' | b'[' | b']' | b'{' | b'}' | b',' | b'`' | b'_' | b'"'
            ))
        .then_some(at + 1)
    }

    let mut result = Vec::new();
    let mut at = 0;
    while at < input.len() {
        if punct(input[at]) {
            result.push(String::from_utf8(vec![input[at]]).expect("ASCII punctuation"));
            at += 1;
            continue;
        }

        let start = at;
        let mut token = Vec::new();
        loop {
            if input.get(at) == Some(&b'_') {
                token.push(b'_');
                at += 1;
                continue;
            }
            if input.get(at) == Some(&b'`') && input.get(at + 1).is_some_and(|&b| punct(b)) {
                token.push(input[at + 1]);
                at += 2;
                continue;
            }
            let Some(end) = normal_atom(input, at) else {
                break;
            };
            token.extend_from_slice(&input[at..end]);
            at = end;
            // A backquote joins two `normal` atoms inside one normalSeq and remains in the token's
            // canonical spelling. Module-syntax operator-name blank handling follows different rules.
            while input.get(at) == Some(&b'`') {
                let Some(end) = normal_atom(input, at + 1) else {
                    break;
                };
                token.push(b'`');
                token.extend_from_slice(&input[at + 1..end]);
                at = end;
            }
        }
        if at == start {
            at += 1; // Discard one unrecognized byte.
            continue;
        }
        // Remove backslash-newline continuations after scanning.
        let mut fixed = Vec::with_capacity(token.len());
        let mut i = 0;
        while i < token.len() {
            if token.get(i) == Some(&b'\\') && token.get(i + 1) == Some(&b'\n') {
                i += 2;
            } else {
                fixed.push(token[i]);
                i += 1;
            }
        }
        result.push(String::from_utf8(fixed).ok()?);
    }
    Some(result)
}

/// Render lexical tokens as bytes with punctuation-sensitive spacing.
fn print_lexical_tokens(words: &[String]) -> Vec<u8> {
    let mut output = Vec::new();
    let mut need_space = false;
    for word in words {
        let bytes = word.as_bytes();
        if let [c] = bytes
            && matches!(c, b'(' | b')' | b'[' | b']' | b'{' | b'}' | b',')
        {
            // Every punctuation mark except `{` takes this branch: `a (b )c`, `a ,b`, but `a{ b }c`.
            if *c != b'{' {
                if need_space {
                    output.push(b' ');
                }
                need_space = false;
            } else {
                need_space = true;
            }
            output.push(*c);
            continue;
        }
        if let [b'\\', c] = bytes {
            match c {
                b'n' => {
                    output.push(b'\n');
                    need_space = false;
                    continue;
                }
                b't' => {
                    output.push(b'\t');
                    need_space = false;
                    continue;
                }
                b's' => {
                    output.push(b' ');
                    need_space = false;
                    continue;
                }
                b'\\' => {
                    if need_space {
                        output.push(b' ');
                    }
                    output.push(b'\\');
                    need_space = true;
                    continue;
                }
                // ANSI-control Qids emit no bytes in this non-TTY formatter and leave spacing unchanged.
                b'!' | b'?' | b'u' | b'f' | b'x' | b'h' | b'p' | b'r' | b'g' | b'y' | b'b'
                | b'm' | b'c' | b'w' | b'P' | b'R' | b'G' | b'Y' | b'B' | b'M' | b'C' | b'W'
                | b'o' => continue,
                _ => {}
            }
        }
        if need_space {
            output.push(b' ');
        }
        output.extend_from_slice(bytes);
        need_space = true;
    }
    output
}

/// A meta `SortSet` (`none` | `_;_`-joined sort `Qid`s) → the sort name strings.
fn down_sorts(ctx: &MetaCtx, hooks: &MetaHooks, d: DagId) -> Vec<String> {
    let empty = hooks.ops.get("emptySortSetSymbol").copied();
    let join = hooks.ops.get("sortSetSymbol").copied();
    flatten_set(ctx, d, empty, join)
        .iter()
        .filter_map(|&x| qid_text(ctx, x))
        .collect()
}

/// A meta `SubsortDeclSet` (`none` | `__`-joined `subsort A < B .`) → the surface chain form (each decl a
/// two-level chain `[[A], [B]]`).
fn down_subsorts(ctx: &MetaCtx, hooks: &MetaHooks, d: DagId) -> Vec<Vec<Vec<String>>> {
    let empty = hooks.ops.get("emptySubsortDeclSetSymbol").copied();
    let join = hooks.ops.get("subsortDeclSetSymbol").copied();
    let subsort = hooks.ops.get("subsortSymbol").copied();
    let mut out = Vec::new();
    for decl in flatten_set(ctx, d, empty, join) {
        if Some(ctx.top(decl)) != subsort {
            continue;
        }
        let kids = ctx.children(decl);
        if let (Some(a), Some(b)) = (
            kids.first().and_then(|&x| qid_text(ctx, x)),
            kids.get(1).and_then(|&x| qid_text(ctx, x)),
        ) {
            out.push(vec![vec![a], vec![b]]);
        }
    }
    out
}

/// A meta `OpDeclSet` (`none` | `__`-joined `op N : D -> R [A] .`) → surface [`OpDecl`]s. `None` on an
/// unexpected element or an op-attribute we do not reconstruct for an own-op (see [`down_attrs`]).
fn down_ops(ctx: &MetaCtx, hooks: &MetaHooks, d: DagId, i: &mut Interner) -> Option<Vec<OpDecl>> {
    let empty = hooks.ops.get("emptyOpDeclSetSymbol").copied();
    let join = hooks.ops.get("opDeclSetSymbol").copied();
    let opdecl = hooks.ops.get("opDeclSymbol").copied();
    let mut out = Vec::new();
    for decl in flatten_set(ctx, d, empty, join) {
        if Some(ctx.top(decl)) != opdecl {
            return None;
        }
        let kids = ctx.children(decl); // [name, typelist, range, attrset]
        let name_str = strip_op_blanks(&qid_text(ctx, *kids.first()?)?);
        let domain = down_typelist(ctx, hooks, *kids.get(1)?);
        let range = qid_text(ctx, *kids.get(2)?)?;
        let attrs = down_attrs(ctx, hooks, *kids.get(3)?, i)?;
        out.push(OpDecl {
            name: tokenize(&name_str, i),
            domain,
            range,
            partial: false,
            attrs,
        });
    }
    Some(out)
}

/// A meta `TypeList` (`nil` | `__`-joined type `Qid`s) → the sort/kind name strings.
fn down_typelist(ctx: &MetaCtx, hooks: &MetaHooks, d: DagId) -> Vec<String> {
    // `nil` is overloaded across META-MODULE list sorts; a reflected TypeList can resolve through a
    // declaration clone distinct from the QidList hook captured in `MetaHooks`.
    if ctx.name(ctx.top(d)) == "nil" && ctx.children(d).is_empty() {
        return Vec::new();
    }
    let empty = hooks.ops.get("nilQidListSymbol").copied();
    let join = hooks.ops.get("qidListSymbol").copied();
    flatten_set(ctx, d, empty, join)
        .iter()
        .filter_map(|&x| qid_text(ctx, x))
        .collect()
}

/// A meta `AttrSet` → surface [`Attrs`]. Reconstructs the semantic attributes needed when a reflected
/// builtin module is inserted into a child session; print/metadata-only attributes are dropped.
fn down_attrs(ctx: &MetaCtx, hooks: &MetaHooks, d: DagId, i: &mut Interner) -> Option<Attrs> {
    let empty = hooks.ops.get("emptyAttrSetSymbol").copied();
    let join = hooks.ops.get("attrSetSymbol").copied();
    let mut a = Attrs::default();
    for attr in flatten_set(ctx, d, empty, join) {
        let sym = ctx.top(attr);
        let is = |name: &str| {
            hooks
                .ops
                .get(name)
                .copied()
                .is_some_and(|hook| hook == sym || ctx.name(hook) == ctx.name(sym))
        };

        if is("ctorSymbol") {
            a.ctor = true;
        } else if is("assocSymbol") {
            a.assoc = true;
        } else if is("commSymbol") {
            a.comm = true;
        } else if is("idemSymbol") {
            a.idem = true;
        } else if is("iterSymbol") {
            a.iter = true;
        } else if is("configSymbol") {
            a.config = true;
        } else if is("objectSymbol") {
            a.object = true;
        } else if is("msgSymbol") {
            a.message = true;
        } else if is("portalSymbol") {
            a.portal = true;
        } else if is("pconstSymbol") {
            a.pconst = true;
        } else if is("idSymbol") || is("leftIdSymbol") || is("rightIdSymbol") {
            a.id = Some(id_bubble(ctx, hooks, *ctx.children(attr).first()?, i)?);
            a.id_side = if is("leftIdSymbol") {
                IdSide::Left
            } else if is("rightIdSymbol") {
                IdSide::Right
            } else {
                IdSide::Both
            };
        } else if is("precSymbol") {
            a.prec = down_nat(ctx, *ctx.children(attr).first()?);
        } else if is("gatherSymbol") {
            let words = qidlist_texts(ctx, hooks, *ctx.children(attr).first()?)?;
            a.gather = Some(
                words
                    .iter()
                    .map(|word| match word.as_str() {
                        "e" => Some(GatherElem::Weak),
                        "E" => Some(GatherElem::Strong),
                        "&" => Some(GatherElem::Any),
                        _ => None,
                    })
                    .collect::<Option<Vec<_>>>()?,
            );
        } else if is("formatSymbol") {
            a.format = Some(qidlist_texts(ctx, hooks, *ctx.children(attr).first()?)?);
        } else if is("stratSymbol") {
            // `strat(<NatList>)` — the per-op evaluation strategy (1-based arg positions, `0` = whole
            // term). Reconstructed like an object-level `strat` declaration; `build_sig` applies it via
            // `set_strategy` when the down-translated module is built.
            a.strat = Some(down_nat_list(ctx, hooks, *ctx.children(attr).first()?)?);
        } else if is("frozenSymbol") {
            a.frozen = Some(down_nat_list(ctx, hooks, *ctx.children(attr).first()?)?);
        } else if is("polySymbol") {
            a.poly = Some(down_nat_list(ctx, hooks, *ctx.children(attr).first()?)?);
        } else if is("specialSymbol") {
            a.special = Some(down_special(ctx, hooks, attr, i)?);
        } else if is("metadataSymbol")
            || is("latexSymbol")
            || is("memoSymbol")
            || is("printSymbol")
            || is("dittoSymbol")
        {
            // printing / metadata / memo — no effect on reduction; safe to drop.
        } else {
            return None; // unknown semantic attributes make the reflected operator unsupported
        }
    }
    Some(a)
}

/// Decode META-LEVEL's `special(HookList)` back to the source hook specification consumed by `build_sig`.
fn down_special(
    ctx: &MetaCtx,
    hooks: &MetaHooks,
    special: DagId,
    interner: &mut Interner,
) -> Option<SpecialSpec> {
    let list = *ctx.children(special).first()?;
    let mut spec = SpecialSpec::default();
    for hook in flatten_set(ctx, list, None, hooks.ops.get("hookListSymbol").copied()) {
        let children = ctx.children(hook);
        let symbol = ctx.top(hook);
        if hooks.ops.get("idHookSymbol").copied() == Some(symbol) {
            let class = qid_text(ctx, *children.first()?)?;
            let data = down_typelist(ctx, hooks, *children.get(1)?);
            spec.id_hook = Some((class, data));
        } else if hooks.ops.get("opHookSymbol").copied() == Some(symbol) {
            let purpose = qid_text(ctx, *children.first()?)?;
            let name = strip_op_blanks(&qid_text(ctx, *children.get(1)?)?);
            let domain = down_typelist(ctx, hooks, *children.get(2)?);
            let range = qid_text(ctx, *children.get(3)?)?;
            let signature = if domain.is_empty() {
                format!("{name} : ~> {range}")
            } else {
                format!("{name} : {} ~> {range}", domain.join(" "))
            };
            spec.op_hooks
                .push((purpose, tokenize(&signature, interner)));
        } else if hooks.ops.get("termHookSymbol").copied() == Some(symbol) {
            let purpose = qid_text(ctx, *children.first()?)?;
            let term = hook_term_bubble(ctx, hooks, *children.get(1)?, interner)?;
            spec.term_hooks.push((purpose, term));
        } else {
            return None;
        }
    }
    (!spec.op_hooks.is_empty() || !spec.term_hooks.is_empty() || spec.id_hook.is_some())
        .then_some(spec)
}

/// Rebuild a special `term-hook` bubble. Unlike an identity, hook resolution needs the operator name,
/// not a sort-qualified constant, because `build_sig` resolves the hook through its symbol table.
fn hook_term_bubble(
    ctx: &MetaCtx,
    hooks: &MetaHooks,
    term: DagId,
    interner: &mut Interner,
) -> Option<Vec<Token>> {
    fn text(ctx: &MetaCtx, hooks: &MetaHooks, term: DagId) -> Option<String> {
        if ctx.top(term) == hooks.ops["metaTermSymbol"] {
            let children = ctx.children(term);
            let head = strip_op_blanks(&qid_text(ctx, *children.first()?)?);
            let arglist = *children.get(1)?;
            let args: Vec<DagId> = if ctx.top(arglist) == hooks.ops["metaArgSymbol"] {
                ctx.children(arglist).to_vec()
            } else {
                vec![arglist]
            };
            let rendered: Option<Vec<String>> =
                args.into_iter().map(|arg| text(ctx, hooks, arg)).collect();
            return Some(format!("{head}({})", rendered?.join(",")));
        }
        let atom = qid_text(ctx, term)?;
        let name = atom
            .rsplit_once('.')
            .map_or(atom.as_str(), |(name, _)| name);
        Some(strip_op_blanks(name))
    }
    Some(tokenize(&text(ctx, hooks, term)?, interner))
}

/// Reconstruct a ground identity meta-term as a prefix-form object term bubble.
fn id_bubble(
    ctx: &MetaCtx,
    hooks: &MetaHooks,
    term: DagId,
    interner: &mut Interner,
) -> Option<Vec<tnk_frontend::lex::Token>> {
    fn text(ctx: &MetaCtx, hooks: &MetaHooks, term: DagId) -> Option<String> {
        if ctx.top(term) == hooks.ops["metaTermSymbol"] {
            let children = ctx.children(term);
            let head = strip_op_blanks(&qid_text(ctx, *children.first()?)?);
            let arglist = *children.get(1)?;
            let args: Vec<DagId> = if ctx.top(arglist) == hooks.ops["metaArgSymbol"] {
                ctx.children(arglist).to_vec()
            } else {
                vec![arglist]
            };
            let rendered: Option<Vec<String>> =
                args.into_iter().map(|arg| text(ctx, hooks, arg)).collect();
            return Some(format!("{head}({})", rendered?.join(",")));
        }
        let atom = qid_text(ctx, term)?;
        match atom.rsplit_once('.') {
            // Keep the meta-term's resolved sort qualification. A bare constant name is not an identity:
            // two copied/imported overloads may share that spelling, while `(c).S` selects the exact target
            // symbol/kind when the down-translated signature parses and owns the rebuilt ground term. The
            // qualifier grammar spells only user sorts, so a kind-level constant (`'e.`[Foo`]`) is
            // qualified by its kind's first named sort, which selects the same kind.
            Some((name, sort)) => {
                let sort = sort
                    .strip_prefix('[')
                    .and_then(|kind| kind.strip_suffix(']'))
                    .map_or(sort, |inner| first_kind_component(inner).trim());
                Some(format!("({}).{sort}", strip_op_blanks(name)))
            }
            None => Some(strip_op_blanks(&atom)),
        }
    }
    Some(tokenize(&text(ctx, hooks, term)?, interner))
}

/// A meta `NatList` (a single `Nat`, or `__`/`natListSymbol`-joined `Nat`s) → the `u32` position list —
/// the inverse of [`up_nat_list`] (a `strat(…)` op attribute's argument).
fn down_nat_list(ctx: &MetaCtx, hooks: &MetaHooks, d: DagId) -> Option<Vec<u32>> {
    if Some(ctx.top(d)) == hooks.ops.get("natListSymbol").copied() {
        ctx.children(d).iter().map(|&c| down_nat(ctx, c)).collect()
    } else {
        Some(vec![down_nat(ctx, d)?])
    }
}

/// A meta `Nat` (`'0.Zero`, `'s_^n['0.Zero]`, or a NAT numeral) → its `u32` value (for `prec`).
fn down_nat(ctx: &MetaCtx, d: DagId) -> Option<u32> {
    match ctx.repr(d) {
        NodeRepr::Iter { count, .. } => count.parse().ok(),
        _ => Some(0), // the zero constant
    }
}

/// Whether a meta `AttrSet` contains the attribute with hook purpose `hook` (`owiseSymbol`/`nonexecSymbol`).
fn attrset_has(ctx: &MetaCtx, hooks: &MetaHooks, d: DagId, hook: &str) -> bool {
    let empty = hooks.ops.get("emptyAttrSetSymbol").copied();
    let join = hooks.ops.get("attrSetSymbol").copied();
    let target = hooks.ops.get(hook).copied();
    target.is_some()
        && flatten_set(ctx, d, empty, join)
            .iter()
            .any(|&x| Some(ctx.top(x)) == target)
}

/// The `label(Q)` of a rule's meta `AttrSet`, if present.
fn attrset_label(ctx: &MetaCtx, hooks: &MetaHooks, d: DagId) -> Option<String> {
    let empty = hooks.ops.get("emptyAttrSetSymbol").copied();
    let join = hooks.ops.get("attrSetSymbol").copied();
    let label = hooks.ops.get("labelSymbol").copied();
    for attr in flatten_set(ctx, d, empty, join) {
        if Some(ctx.top(attr)) == label {
            return qid_text(ctx, *ctx.children(attr).first()?);
        }
    }
    None
}

/// A reflected module has no surface `var` declarations: every variable occurrence must therefore carry
/// its sort in the transient source bubbles used to instantiate/flatten it. Rebuild that spelling from
/// the decoded slot sort rather than trusting the trace display name (which may contain only `A`).
fn typed_source_var_names(m: &BuiltModule, vars: &VarIndex) -> Vec<String> {
    (0..vars.count())
        .map(|slot| {
            let raw = vars.name(slot);
            let base = raw.split_once(':').map_or(raw, |(base, _)| base);
            format!("{base}:{}", m.engine.sorts().name(vars.sort(slot)))
        })
        .collect()
}

fn source_term_tokens(
    m: &BuiltModule,
    interner: &mut Interner,
    term: &Term,
    vars: &[String],
) -> Vec<Token> {
    let text = print_term(m, interner, term, vars, false);
    tokenize(&text, interner)
}

fn source_condition_tokens(
    m: &BuiltModule,
    interner: &mut Interner,
    condition: &[ConditionFragment],
    vars: &[String],
) -> Vec<Token> {
    let mut text = String::new();
    for (index, fragment) in condition.iter().enumerate() {
        if index != 0 {
            text.push_str(" /\\ ");
        }
        match fragment {
            ConditionFragment::Equality { lhs, rhs } => {
                text.push_str(&print_term(m, interner, lhs, vars, false));
                text.push_str(" = ");
                text.push_str(&print_term(m, interner, rhs, vars, false));
            }
            ConditionFragment::SortTest { term, sort } => {
                text.push_str(&print_term(m, interner, term, vars, false));
                text.push_str(" : ");
                text.push_str(m.engine.sorts().name(*sort));
            }
            ConditionFragment::Matching {
                pattern, subject, ..
            } => {
                text.push_str(&print_term(m, interner, pattern, vars, false));
                text.push_str(" := ");
                text.push_str(&print_term(m, interner, subject, vars, false));
            }
            ConditionFragment::Rewrite { lhs, pattern, .. } => {
                text.push_str(&print_term(m, interner, lhs, vars, false));
                text.push_str(" => ");
                text.push_str(&print_term(m, interner, pattern, vars, false));
            }
        }
    }
    tokenize(&text, interner)
}

/// Install a meta `MembAxSet`'s memberships into the built engine (down-translating each `mb`/`cmb`).
fn install_membs(
    ctx: &MetaCtx,
    hooks: &MetaHooks,
    d: DagId,
    m: &mut BuiltModule,
    mut source: Option<&mut Vec<Statement>>,
    interner: &mut Interner,
) -> Option<()> {
    let empty = hooks.ops.get("emptyMembAxSetSymbol").copied();
    let join = hooks.ops.get("membAxSetSymbol").copied();
    let mb = hooks.ops.get("mbSymbol").copied();
    let cmb = hooks.ops.get("cmbSymbol").copied();
    for stmt in flatten_set(ctx, d, empty, join) {
        let sym = Some(ctx.top(stmt));
        let kids = ctx.children(stmt);
        let mut vars = VarIndex::new();
        let (lhs, sort_id, condition, attrs) = if sym == mb {
            // mb lhs : Sort [attrs]
            let lhs = down_term_to_term(ctx, hooks, *kids.first()?, m, &mut vars)?;
            let sort = *m.sorts.get(&qid_text(ctx, *kids.get(1)?)?)?;
            (lhs, sort, Vec::new(), *kids.get(2)?)
        } else if sym == cmb {
            // cmb lhs : Sort if cond [attrs]
            let lhs = down_term_to_term(ctx, hooks, *kids.first()?, m, &mut vars)?;
            let sort = *m.sorts.get(&qid_text(ctx, *kids.get(1)?)?)?;
            let mut bound: BTreeSet<u32> = (0..vars.count()).collect();
            let cond = down_condition(ctx, hooks, *kids.get(2)?, m, &mut vars, &mut bound)?;
            (lhs, sort, cond, *kids.get(3)?)
        } else {
            return None;
        };
        let nonexec = attrset_has(ctx, hooks, attrs, "nonexecSymbol");
        let nr = vars.count();
        let var_names: Vec<String> = (0..nr).map(|k| vars.name(k).to_string()).collect();
        let label = attrset_label(ctx, hooks, attrs);
        if let Some(source) = source.as_deref_mut() {
            let source_names = typed_source_var_names(m, &vars);
            source.push(Statement::Mb {
                lhs: source_term_tokens(m, interner, &lhs, &source_names),
                sort: tokenize(m.engine.sorts().name(sort_id), interner),
                cond: (!condition.is_empty())
                    .then(|| source_condition_tokens(m, interner, &condition, &source_names)),
                nonexec,
                label: label.clone(),
            });
        }
        if nonexec {
            continue;
        }
        // Down-installed statements are executable (nonexec skipped above); retain the label from the meta
        // `AttrSet` (as the rule path does) so a down∘up round-trip preserves it.
        let trace = MbTrace {
            lhs: lhs.clone(),
            sort: sort_id,
            condition: condition.clone(),
            var_names,
            label,
            nonexec: false,
        };
        let id = if condition.is_empty() {
            m.engine.add_membership(Membership {
                lhs,
                sort: sort_id,
                nr_vars: nr,
            })
        } else {
            m.engine
                .add_conditional_membership(lhs, sort_id, nr, condition)
        };
        assert_eq!(
            id as usize,
            m.mb_traces.len(),
            "membership id is the dense mb_traces index"
        );
        m.mb_traces.push(trace);
    }
    Some(())
}

/// Install a meta `EquationSet`'s equations into the built engine (down-translating each `eq`/`ceq`).
fn install_eqs(
    ctx: &MetaCtx,
    hooks: &MetaHooks,
    d: DagId,
    m: &mut BuiltModule,
    mut source: Option<&mut Vec<Statement>>,
    interner: &mut Interner,
) -> Option<()> {
    let empty = hooks.ops.get("emptyEquationSetSymbol").copied();
    let join = hooks.ops.get("equationSetSymbol").copied();
    let eq = hooks.ops.get("eqSymbol").copied();
    let ceq = hooks.ops.get("ceqSymbol").copied();
    for stmt in flatten_set(ctx, d, empty, join) {
        let sym = Some(ctx.top(stmt));
        let kids = ctx.children(stmt);
        let mut vars = VarIndex::new();

        // Build lhs, condition, then rhs while sharing one variable index.
        let (lhs, rhs, condition, attrs) = if sym == eq {
            let lhs = down_term_to_term(ctx, hooks, *kids.first()?, m, &mut vars);
            let rhs = down_term_to_term(ctx, hooks, *kids.get(1)?, m, &mut vars);

            (lhs?, rhs?, Vec::new(), *kids.get(2)?)
        } else if sym == ceq {
            let lhs = down_term_to_term(ctx, hooks, *kids.first()?, m, &mut vars)?;
            let mut bound: BTreeSet<u32> = (0..vars.count()).collect();
            let cond = down_condition(ctx, hooks, *kids.get(2)?, m, &mut vars, &mut bound)?;
            let rhs = down_term_to_term(ctx, hooks, *kids.get(1)?, m, &mut vars)?;
            (lhs, rhs, cond, *kids.get(3)?)
        } else {
            return None;
        };
        let nonexec = attrset_has(ctx, hooks, attrs, "nonexecSymbol");
        let owise = attrset_has(ctx, hooks, attrs, "owiseSymbol");
        let variant = attrset_has(ctx, hooks, attrs, "variantAttrSymbol");
        let nr = vars.count();
        let var_names: Vec<String> = (0..nr).map(|k| vars.name(k).to_string()).collect();
        let label = attrset_label(ctx, hooks, attrs);
        if let Some(source) = source.as_deref_mut() {
            let source_names = typed_source_var_names(m, &vars);
            source.push(Statement::Eq {
                lhs: source_term_tokens(m, interner, &lhs, &source_names),
                rhs: source_term_tokens(m, interner, &rhs, &source_names),
                cond: (!condition.is_empty())
                    .then(|| source_condition_tokens(m, interner, &condition, &source_names)),
                owise,
                variant,
                nonexec,
                label: label.clone(),
            });
        }
        if nonexec {
            continue;
        }
        let trace = EqTrace {
            lhs: lhs.clone(),
            rhs: rhs.clone(),
            condition: condition.clone(),
            var_names,
            owise,
            variant,
            label,
            nonexec: false,
        };
        let id = if variant {
            m.engine
                .add_variant_equation(lhs, rhs, nr, condition, owise)
        } else if owise {
            m.engine.add_owise_equation(lhs, rhs, nr, condition)
        } else if condition.is_empty() {
            m.engine.add_equation(Equation {
                lhs,
                rhs,
                nr_vars: nr,
            })
        } else {
            m.engine.add_conditional_equation(lhs, rhs, nr, condition)
        };
        assert_eq!(
            id as usize,
            m.eq_traces.len(),
            "equation id is the dense eq_traces index"
        );
        m.eq_traces.push(trace);
    }
    Some(())
}

/// The exact meta-DAG shape produced by `upTerm` for a normalized symbolic statement pattern. We compare
/// these keys without allocating temporary nodes in the caller's META engine.
#[derive(Debug)]
enum ReflectedPatternKey {
    Qid {
        text: String,
        variable_rank: Option<u32>,
    },
    App {
        operator: String,
        args: Vec<ReflectedPatternKey>,
    },
}

fn reflected_pattern_key(
    source: &BuiltModule,
    interner: &Interner,
    variable_names: &[String],
    node: DagId,
    qid_symbol: SymbolId,
    meta_term_symbol: SymbolId,
    meta_arg_symbol: SymbolId,
) -> ReflectedPatternKey {
    let engine = &source.engine;
    let qid = |text| ReflectedPatternKey::Qid {
        text,
        variable_rank: None,
    };
    match engine.node(node).repr() {
        NodeRepr::App => {
            let symbol = engine.node(node).symbol();
            let operator = meta_symbol_name(source, symbol);
            let children: Vec<DagId> = engine.node(node).children().collect();
            if children.is_empty() {
                qid(format!(
                    "{operator}.{}",
                    engine.sorts().name(engine.sort_of(node))
                ))
            } else {
                let mut args: Vec<_> = children
                    .into_iter()
                    .map(|child| {
                        reflected_pattern_key(
                            source,
                            interner,
                            variable_names,
                            child,
                            qid_symbol,
                            meta_term_symbol,
                            meta_arg_symbol,
                        )
                    })
                    .collect();
                // The source DAG uses symbol-based child order; reflected RuleSets use the emitted Qid and
                // application keys. Re-sort commutative children by the latter before installation.
                if engine.symbol_is_commutative(symbol) {
                    args.sort_by(|left, right| {
                        compare_reflected_pattern_keys(
                            left,
                            right,
                            qid_symbol,
                            meta_term_symbol,
                            meta_arg_symbol,
                        )
                    });
                }
                ReflectedPatternKey::App { operator, args }
            }
        }
        NodeRepr::Iter { count, arg } => {
            let base = meta_symbol_name(source, engine.node(node).symbol());
            let operator = if count == "1" {
                base
            } else {
                format!("{base}^{count}")
            };
            ReflectedPatternKey::App {
                operator,
                args: vec![reflected_pattern_key(
                    source,
                    interner,
                    variable_names,
                    arg,
                    qid_symbol,
                    meta_term_symbol,
                    meta_arg_symbol,
                )],
            }
        }
        NodeRepr::SmtNum(number) => {
            let sort = engine.sort_of(node);
            let kind = engine
                .smt_type(sort)
                .expect("SMT number without sort metadata");
            qid(format!(
                "{}.{}",
                number.to_maude(kind),
                engine.sorts().name(sort)
            ))
        }
        NodeRepr::Qid(value) => qid(format!(
            "'{value}.{}",
            engine.sorts().name(engine.sort_of(node))
        )),
        NodeRepr::Str(value) => qid(format!(
            "{}.{}",
            render_string(value),
            engine.sorts().name(engine.sort_of(node))
        )),
        NodeRepr::Float(value) => qid(format!(
            "{}.{}",
            render_float(value),
            engine.sorts().name(engine.sort_of(node))
        )),
        NodeRepr::Var { name } => {
            let text = engine
                .node(node)
                .variable_index()
                .and_then(|slot| variable_names.get(slot as usize))
                .map(String::as_str)
                .unwrap_or_else(|| interner.resolve_index(name));
            let sort = engine.sorts().name(engine.sort_of(node));
            let typed = match text.rsplit_once(':') {
                Some((base, declared)) if !base.is_empty() && declared == sort => text.to_string(),
                _ => format!("{text}:{sort}"),
            };
            let base = text.split_once(':').map_or(text, |(base, _)| base);
            let fallback = interner.get(base).map_or(name, |symbol| symbol.index());
            ReflectedPatternKey::Qid {
                text: typed,
                variable_rank: Some(maude_variable_name_rank(base, fallback)),
            }
        }
    }
}

enum ReflectedKeyNode<'a> {
    Pattern(&'a ReflectedPatternKey),
    ArgList(&'a [ReflectedPatternKey]),
}

fn compare_reflected_pattern_keys(
    left: &ReflectedPatternKey,
    right: &ReflectedPatternKey,
    qid: SymbolId,
    meta_term: SymbolId,
    meta_arg: SymbolId,
) -> Ordering {
    compare_reflected_key_nodes(
        ReflectedKeyNode::Pattern(left),
        ReflectedKeyNode::Pattern(right),
        qid,
        meta_term,
        meta_arg,
    )
}

fn compare_reflected_key_nodes(
    left: ReflectedKeyNode<'_>,
    right: ReflectedKeyNode<'_>,
    qid: SymbolId,
    meta_term: SymbolId,
    meta_arg: SymbolId,
) -> Ordering {
    let top = |node: &ReflectedKeyNode<'_>| match node {
        ReflectedKeyNode::Pattern(ReflectedPatternKey::Qid { .. }) => (0, qid),
        ReflectedKeyNode::Pattern(ReflectedPatternKey::App { .. }) => (2, meta_term),
        ReflectedKeyNode::ArgList(_) => (2, meta_arg),
    };
    match top(&left).cmp(&top(&right)) {
        Ordering::Equal => {}
        order => return order,
    }
    match (left, right) {
        (
            ReflectedKeyNode::Pattern(ReflectedPatternKey::Qid {
                text: left,
                variable_rank: left_rank,
            }),
            ReflectedKeyNode::Pattern(ReflectedPatternKey::Qid {
                text: right,
                variable_rank: right_rank,
            }),
        ) => match (left_rank, right_rank) {
            (Some(left_rank), Some(right_rank)) => {
                left_rank.cmp(right_rank).then_with(|| left.cmp(right))
            }
            _ => left.cmp(right),
        },
        (
            ReflectedKeyNode::Pattern(ReflectedPatternKey::App {
                operator: left_operator,
                args: left_args,
            }),
            ReflectedKeyNode::Pattern(ReflectedPatternKey::App {
                operator: right_operator,
                args: right_args,
            }),
        ) => left_operator.cmp(right_operator).then_with(|| {
            let left = if left_args.len() == 1 {
                ReflectedKeyNode::Pattern(&left_args[0])
            } else {
                ReflectedKeyNode::ArgList(left_args)
            };
            let right = if right_args.len() == 1 {
                ReflectedKeyNode::Pattern(&right_args[0])
            } else {
                ReflectedKeyNode::ArgList(right_args)
            };
            compare_reflected_key_nodes(left, right, qid, meta_term, meta_arg)
        }),
        (ReflectedKeyNode::ArgList(left), ReflectedKeyNode::ArgList(right)) => {
            left.len().cmp(&right.len()).then_with(|| {
                left.iter()
                    .zip(right)
                    .map(|(left, right)| {
                        compare_reflected_pattern_keys(left, right, qid, meta_term, meta_arg)
                    })
                    .find(|order| *order != Ordering::Equal)
                    .unwrap_or(Ordering::Equal)
            })
        }
        // Equal top keys across different node variants would require two META hooks to resolve to the
        // same symbol, which a valid META-LEVEL signature cannot do.
        _ => Ordering::Equal,
    }
}

/// Apply reflected RuleSet order to a source-built executable rule table. Deferred payloads bypass the
/// meta-term round trip but must still use canonical RuleSet order.
fn reorder_rules_like_reflection(
    hooks: &MetaHooks,
    m: &mut BuiltModule,
    interner: &mut Interner,
    selected_ids: &[u32],
) -> Result<Vec<u32>, ReducerFault> {
    if selected_ids.is_empty() {
        return Ok(Vec::new());
    }
    let qid = hooks.ops["qidSymbol"];
    let meta_term = hooks.ops["metaTermSymbol"];
    let meta_arg = hooks.ops["metaArgSymbol"];
    let mut ordered = Vec::with_capacity(selected_ids.len());
    for &id in selected_ids {
        let Some(trace) = m.rl_traces.get(id as usize).cloned() else {
            continue;
        };
        let variable_codes: Vec<u32> = trace
            .var_names
            .iter()
            .map(|name| {
                let base = name.split_once(':').map_or(name.as_str(), |(base, _)| base);
                interner.intern(base).index()
            })
            .collect();
        let lhs = m
            .engine
            .try_normalize_pattern_for_reflection(&trace.lhs, &variable_codes)?;
        let key =
            reflected_pattern_key(m, interner, &trace.var_names, lhs, qid, meta_term, meta_arg);
        ordered.push((!trace.condition.is_empty(), key, id));
    }
    ordered.sort_by(|left, right| {
        left.0
            .cmp(&right.0)
            .then_with(|| {
                compare_reflected_pattern_keys(&left.1, &right.1, qid, meta_term, meta_arg)
            })
            .then_with(|| left.2.cmp(&right.2))
    });

    // A non-flat reflection contains only this module's own rules. Reorder those rules in their existing
    // slots while leaving imported rules in place; a flat reflection selects every slot.
    let mut selected = vec![false; m.rl_traces.len()];
    for &id in selected_ids {
        if let Some(slot) = selected.get_mut(id as usize) {
            *slot = true;
        }
    }
    let canonical_ids = ordered.iter().map(|(_, _, id)| *id).collect::<Vec<_>>();
    let mut sorted = canonical_ids.iter().copied();
    let full_order: Vec<u32> = (0..m.rl_traces.len() as u32)
        .map(|id| {
            if selected[id as usize] {
                sorted.next().unwrap_or(id)
            } else {
                id
            }
        })
        .collect();
    m.engine.reorder_rules(&full_order);
    Ok(canonical_ids)
}

/// Reorder retained source rules to their reflected RuleSet order so child interpreters preserve the
/// executable-table ordering.
fn reorder_source_rules(
    source: &mut PreModule,
    rule_slots: &[usize],
    source_ids: &[u32],
    canonical_ids: &[u32],
) {
    if rule_slots.len() != source_ids.len() || source_ids.len() != canonical_ids.len() {
        return;
    }
    let mut source_set = source_ids.to_vec();
    let mut canonical_set = canonical_ids.to_vec();
    source_set.sort_unstable();
    canonical_set.sort_unstable();
    if source_set != canonical_set {
        return;
    }

    let positions: HashMap<u32, usize> = source_ids
        .iter()
        .copied()
        .zip(rule_slots.iter().copied())
        .collect();
    if positions.len() != source_ids.len()
        || rule_slots
            .iter()
            .any(|&slot| slot >= source.statements.len())
    {
        return;
    }

    let mut statements = std::mem::take(&mut source.statements)
        .into_iter()
        .map(Some)
        .collect::<Vec<_>>();
    let mut replacements = Vec::with_capacity(rule_slots.len());
    for (&target, &id) in rule_slots.iter().zip(canonical_ids) {
        let source_slot = positions[&id];
        replacements.push((
            target,
            statements[source_slot]
                .take()
                .expect("canonical rule ids form a permutation"),
        ));
    }
    for (target, statement) in replacements {
        debug_assert!(statements[target].is_none());
        statements[target] = Some(statement);
    }
    source.statements = statements
        .into_iter()
        .map(|statement| statement.expect("only executable rule slots were moved"))
        .collect();
}

/// Install a meta `RuleSet`'s rules into the built engine (down-translating each `rl`/`crl`).
fn install_rules(
    ctx: &MetaCtx,
    hooks: &MetaHooks,
    d: DagId,
    m: &mut BuiltModule,
    interner: &mut Interner,
    mut source: Option<&mut Vec<Statement>>,
) -> Result<Option<()>, ReducerFault> {
    let mut reducer_fault = None;
    let result = (|| {
        let empty = hooks.ops.get("emptyRuleSetSymbol").copied();
        let join = hooks.ops.get("ruleSetSymbol").copied();
        let rl = hooks.ops.get("rlSymbol").copied();
        let crl = hooks.ops.get("crlSymbol").copied();
        // A meta RuleSet is AC, so its iteration order is semantic. Source traces retain unnormalized patterns;
        // rebuild each lhs as a normalized symbolic DAG for ordering while decoding from the original statement.
        let qid = hooks.ops["qidSymbol"];
        let meta_term = hooks.ops["metaTermSymbol"];
        let meta_arg = hooks.ops["metaArgSymbol"];
        let statements = flatten_set(ctx, d, empty, join);
        let mut symbol_ranks = Vec::new();
        let mut ordered = Vec::with_capacity(statements.len());
        for (index, stmt) in statements.into_iter().enumerate() {
            let symbol = ctx.top(stmt);
            let symbol_rank = if let Some(rank) = symbol_ranks
                .iter()
                .position(|&candidate| candidate == symbol)
            {
                rank
            } else {
                symbol_ranks.push(symbol);
                symbol_ranks.len() - 1
            };
            let mut vars = VarIndex::new();
            let lhs = down_term_to_term(ctx, hooks, *ctx.children(stmt).first()?, m, &mut vars)?;
            let variable_codes: Vec<u32> = (0..vars.count())
                .map(|slot| {
                    let name = vars.name(slot);
                    let base = name.split_once(':').map_or(name, |(base, _)| base);
                    interner.intern(base).index()
                })
                .collect();
            let names: Vec<String> = (0..vars.count())
                .map(|slot| vars.name(slot).to_string())
                .collect();
            let lhs = match m
                .engine
                .try_normalize_pattern_for_reflection(&lhs, &variable_codes)
            {
                Ok(lhs) => lhs,
                Err(fault) => {
                    reducer_fault = Some(fault);
                    return None;
                }
            };
            let key = reflected_pattern_key(m, interner, &names, lhs, qid, meta_term, meta_arg);
            ordered.push((symbol_rank, key, index, stmt));
        }
        ordered.sort_by(|left, right| {
            left.0
                .cmp(&right.0)
                .then_with(|| {
                    compare_reflected_pattern_keys(&left.1, &right.1, qid, meta_term, meta_arg)
                })
                .then_with(|| left.2.cmp(&right.2))
        });
        for (_, _, _, stmt) in ordered {
            let sym = Some(ctx.top(stmt));
            let kids = ctx.children(stmt);
            let mut vars = VarIndex::new();
            let (lhs, rhs, condition, attrs) = if sym == rl {
                let lhs = down_term_to_term(ctx, hooks, *kids.first()?, m, &mut vars)?;
                let rhs = down_term_to_term(ctx, hooks, *kids.get(1)?, m, &mut vars)?;
                (lhs, rhs, Vec::new(), *kids.get(2)?)
            } else if sym == crl {
                let lhs = down_term_to_term(ctx, hooks, *kids.first()?, m, &mut vars)?;
                let mut bound: BTreeSet<u32> = (0..vars.count()).collect();
                let cond = down_condition(ctx, hooks, *kids.get(2)?, m, &mut vars, &mut bound)?;
                let rhs = down_term_to_term(ctx, hooks, *kids.get(1)?, m, &mut vars)?;
                (lhs, rhs, cond, *kids.get(3)?)
            } else {
                return None;
            };
            let nonexec = attrset_has(ctx, hooks, attrs, "nonexecSymbol");
            let narrowing = attrset_has(ctx, hooks, attrs, "narrowingSymbol");
            let label = attrset_label(ctx, hooks, attrs);
            let nr = vars.count();
            let var_names: Vec<String> = (0..nr).map(|k| vars.name(k).to_string()).collect();
            if let Some(source) = source.as_deref_mut() {
                let source_names = typed_source_var_names(m, &vars);
                source.push(Statement::Rule {
                    label: label.clone(),
                    lhs: source_term_tokens(m, interner, &lhs, &source_names),
                    rhs: source_term_tokens(m, interner, &rhs, &source_names),
                    cond: (!condition.is_empty())
                        .then(|| source_condition_tokens(m, interner, &condition, &source_names)),
                    nonexec,
                    narrowing,
                });
            }
            if narrowing && !condition.is_empty() {
                continue;
            }
            let variable_specs = (0..nr)
                .map(|slot| {
                    let source = vars.name(slot);
                    let base = source.split_once(':').map_or(source, |(base, _)| base);
                    tnk_core::unify::problem::VarSpec {
                        sort: vars.sort(slot),
                        name: maude_variable_name_rank(base, interner.intern(base).index()),
                    }
                })
                .collect();
            // Statements are installed after `build_loaded_module`. Register their dedicated SMT descriptors,
            // including `[nonexec]` rules, so restriction checks inspect the complete reflected rule set.
            m.engine.add_smt_rule(
                lhs.clone(),
                rhs.clone(),
                (0..nr).map(|slot| vars.sort(slot)).collect(),
                var_names.clone(),
                condition.clone(),
            );
            if narrowing {
                m.engine.add_narrowing_rule(
                    lhs.clone(),
                    rhs.clone(),
                    variable_specs,
                    var_names.clone(),
                    condition.clone(),
                    label.clone(),
                    nonexec,
                );
            }
            if nonexec || lhs.top_symbol().is_none() {
                continue;
            }
            let shared_label = label.as_deref().map(std::rc::Rc::<str>::from);
            let trace = RlTrace {
                lhs: lhs.clone(),
                rhs: rhs.clone(),
                condition: condition.clone(),
                var_names,
                label: shared_label.clone(),
                nonexec: false,
                narrowing,
            };
            let id = if condition.is_empty() {
                m.engine.add_labelled_rule(lhs, rhs, nr, shared_label)
            } else {
                m.engine
                    .add_labelled_conditional_rule(lhs, rhs, nr, condition, shared_label)
            };
            assert_eq!(
                id as usize,
                m.rl_traces.len(),
                "rule id is the dense rl_traces index"
            );
            m.rl_traces.push(trace);
        }
        Some(())
    })();
    match reducer_fault {
        Some(fault) => Err(fault),
        None => Ok(result),
    }
}

/// Down-translate a meta `Condition`/`EqCondition` into kernel [`ConditionFragment`]s. `nil` is the empty
/// condition; `_/\_` conjoins; each fragment is `_=_`/`_:_`/`_:=_`/`_=>_`. Shares the statement's `vars`;
/// a `:=`/`=>` fragment's fresh variables are those its pattern introduces (not already in `bound`).
fn down_condition(
    ctx: &MetaCtx,
    hooks: &MetaHooks,
    d: DagId,
    m: &BuiltModule,
    vars: &mut VarIndex,
    bound: &mut BTreeSet<u32>,
) -> Option<Vec<ConditionFragment>> {
    let nil = hooks.ops.get("noConditionSymbol").copied();
    let conj = hooks.ops.get("conjunctionSymbol").copied();
    let eq_c = hooks.ops.get("equalityConditionSymbol").copied();
    let sort_c = hooks.ops.get("sortTestConditionSymbol").copied();
    let match_c = hooks.ops.get("matchConditionSymbol").copied();
    let rw_c = hooks.ops.get("rewriteConditionSymbol").copied();
    let fragments = flatten_set(ctx, d, nil, conj);
    let mut out = Vec::with_capacity(fragments.len());
    for f in fragments {
        let sym = Some(ctx.top(f));
        let kids = ctx.children(f);
        let frag = if sym == eq_c {
            ConditionFragment::Equality {
                lhs: down_term_to_term(ctx, hooks, *kids.first()?, m, vars)?,
                rhs: down_term_to_term(ctx, hooks, *kids.get(1)?, m, vars)?,
            }
        } else if sym == sort_c {
            let term = down_term_to_term(ctx, hooks, *kids.first()?, m, vars)?;
            let sort = *m.sorts.get(&qid_text(ctx, *kids.get(1)?)?)?;
            ConditionFragment::SortTest { term, sort }
        } else if sym == match_c {
            let pattern = down_term_to_term(ctx, hooks, *kids.first()?, m, vars)?;
            let subject = down_term_to_term(ctx, hooks, *kids.get(1)?, m, vars)?;
            let fresh = fresh_vars(&pattern, bound);
            ConditionFragment::Matching {
                pattern,
                subject,
                fresh_vars: fresh,
            }
        } else if sym == rw_c {
            let lhs = down_term_to_term(ctx, hooks, *kids.first()?, m, vars)?;
            let pattern = down_term_to_term(ctx, hooks, *kids.get(1)?, m, vars)?;
            let fresh = fresh_vars(&pattern, bound);
            ConditionFragment::Rewrite {
                lhs,
                pattern,
                fresh_vars: fresh,
            }
        } else {
            return None;
        };
        out.push(frag);
    }
    Some(out)
}

fn down_variant_sat_formula(
    ctx: &MetaCtx,
    hooks: &MetaHooks,
    d: DagId,
    target: &BuiltModule,
    vars: &mut VarIndex,
) -> Option<Formula> {
    let symbol = ctx.top(d);
    let kids = ctx.children(d);
    let has_hook = |purpose: &str| hooks.ops.get(purpose).copied() == Some(symbol);
    if has_hook("eqFormulaSymbol") || has_hook("neqFormulaSymbol") {
        if kids.len() != 2 {
            return None;
        }
        return Some(Formula::Literal(VariantSatLiteral {
            lhs: down_term_to_term(ctx, hooks, kids[0], target, vars)?,
            rhs: down_term_to_term(ctx, hooks, kids[1], target, vars)?,
            positive: has_hook("eqFormulaSymbol"),
        }));
    }
    let is_and = [
        "formulaAndPosSymbol",
        "formulaAndNegSymbol",
        "formulaAndConjSymbol",
        "formulaAndFormSymbol",
    ]
    .iter()
    .any(|purpose| has_hook(purpose));
    if is_and {
        return kids
            .into_iter()
            .map(|kid| down_variant_sat_formula(ctx, hooks, kid, target, vars))
            .collect::<Option<Vec<_>>>()
            .map(Formula::And);
    }
    let is_or = ["formulaOrDnfSymbol", "formulaOrFormSymbol"]
        .iter()
        .any(|purpose| has_hook(purpose));
    if is_or {
        return kids
            .into_iter()
            .map(|kid| down_variant_sat_formula(ctx, hooks, kid, target, vars))
            .collect::<Option<Vec<_>>>()
            .map(Formula::Or);
    }
    if kids.len() == 1 && has_hook("formulaNotSymbol") {
        return Some(Formula::Not(Box::new(down_variant_sat_formula(
            ctx, hooks, kids[0], target, vars,
        )?)));
    }
    if kids.len() == 2 && has_hook("formulaImpliesSymbol") {
        return Some(Formula::Implies(
            Box::new(down_variant_sat_formula(ctx, hooks, kids[0], target, vars)?),
            Box::new(down_variant_sat_formula(ctx, hooks, kids[1], target, vars)?),
        ));
    }
    if kids.len() == 2 && has_hook("formulaIffSymbol") {
        return Some(Formula::Iff(
            Box::new(down_variant_sat_formula(ctx, hooks, kids[0], target, vars)?),
            Box::new(down_variant_sat_formula(ctx, hooks, kids[1], target, vars)?),
        ));
    }
    None
}

fn down_variant_sort_set(
    ctx: &MetaCtx,
    hooks: &MetaHooks,
    d: DagId,
    target: &BuiltModule,
) -> Option<Vec<SortId>> {
    let empty = hooks.ops.get("emptySortSetSymbol").copied();
    let join = hooks.ops.get("sortSetSymbol").copied();
    flatten_set(ctx, d, empty, join)
        .into_iter()
        .map(|item| target.sorts.get(&qid_text(ctx, item)?).copied())
        .collect()
}

/// The pattern's variable indices not already in `bound` (the fresh ones a `:=`/`=>` fragment binds);
/// extends `bound` with all of them.
fn fresh_vars(pat: &Term, bound: &mut BTreeSet<u32>) -> Vec<u32> {
    let mut idx = Vec::new();
    term_var_indices(pat, &mut idx);
    let fresh: Vec<u32> = idx.iter().copied().filter(|v| !bound.contains(v)).collect();
    bound.extend(idx);
    fresh
}

/// Collect a term's distinct variable indices, in first-seen order.
fn term_var_indices(t: &Term, out: &mut Vec<u32>) {
    match t {
        Term::Var(v) => {
            if !out.contains(&v.index) {
                out.push(v.index);
            }
        }
        Term::Na { .. } => {}
        Term::Iter { arg, .. } => term_var_indices(arg, out),
        Term::Op { args, .. } => {
            for a in args {
                term_var_indices(a, out);
            }
        }
    }
}

/// Down-translate a meta-term into a kernel [`Term`] (a pattern / statement side) over `target`. Like
/// [`down_term`] but yields a static `Term`: a meta variable `'X:Sort` becomes an indexed `Term::Var`
/// (tracked in `vars`, keyed by the full meta name so `'X:Nat` and `'X:Int` stay distinct), a constant
/// `'c.S` an arity-0 `Term::Op`, an application `'f[args]` a `Term::Op`, and the iterated `'s_^n[t]` a
/// compact [`Term::Iter`] carrying the arbitrary-size count as scalar data.
fn down_term_to_term(
    ctx: &MetaCtx,
    hooks: &MetaHooks,
    t: DagId,
    target: &BuiltModule,
    vars: &mut VarIndex,
) -> Option<Term> {
    let meta_term = hooks.ops.get("metaTermSymbol").copied();
    match ctx.repr(t) {
        NodeRepr::Qid(text) => down_leaf_to_term(text, target, vars),
        NodeRepr::App if Some(ctx.top(t)) == meta_term => {
            let kids = ctx.children(t);
            let head = qid_text(ctx, *kids.first()?)?;
            let args = down_arglist_to_term(ctx, hooks, *kids.get(1)?, target, vars)?;
            build_app_term(&head, args, target)
        }
        _ => None,
    }
}

/// A meta-term leaf `'X:Sort` (variable) or `'c.Sort` (constant) → a kernel [`Term`].
fn down_leaf_to_term(text: &str, target: &BuiltModule, vars: &mut VarIndex) -> Option<Term> {
    let colon = text.rfind(':');
    let dot = text.rfind('.');
    if let Some(dot) = dot
        && colon.is_none_or(|colon| dot > colon)
    {
        // Constant: use the final `.` separator. Quoted identifiers may themselves contain `:` or `.`,
        // e.g. `'<_:_|_>.Qid`, so testing for a colon before the sort suffix misclassifies them as vars.
        let raw_name = &text[..dot];
        let name = strip_op_blanks(raw_name);
        let sort = resolve_meta_sort_name(target, &text[dot + 1..])?;

        if let Some(kind) = target.engine.smt_type(sort)
            && let Some(number) = SmtNumber::parse(&name, kind)
        {
            let component = target.engine.sorts().kind_of(sort);
            let symbol = target.engine.smt_info().number_symbol(component)?;
            return Some(Term::Na {
                symbol,
                value: NaValue::SmtNum(Rc::new(number)),
            });
        }
        if let Some((symbol, value)) = decode_na_literal(raw_name, sort, target) {
            return Some(Term::Na { symbol, value });
        }
        let sym = target.engine.resolve_constant_at_sort(&name, sort)?;
        Some(Term::constant(sym))
    } else if let Some(colon) = colon {
        // Variable: the final `:` separates its name from its sort.
        let sort = resolve_meta_sort_name(target, &text[colon + 1..])?;
        Some(Term::var(vars.index_of(text, sort), sort))
    } else {
        None
    }
}

fn resolve_meta_sort_name(target: &BuiltModule, name: &str) -> Option<SortId> {
    let name = strip_op_blanks(name);
    if let Some(inner) = name
        .strip_prefix('[')
        .and_then(|name| name.strip_suffix(']'))
    {
        let first = inner.split(',').next()?.trim();
        let member = *target.sorts.get(first)?;
        let kind = target.engine.sorts().kind_of(member);
        Some(target.engine.sorts().error_sort(kind))
    } else {
        target.sorts.get(&name).copied()
    }
}

/// Decode a reflected atomic literal. Its textual spelling alone is insufficient (`0.Nat` and
/// `0.FiniteFloat` both carry `0`), so the marker symbol and requested result sort must share a kind.
fn decode_na_literal(
    name: &str,
    sort: SortId,
    target: &BuiltModule,
) -> Option<(SymbolId, NaValue)> {
    let (marker, value) = if let Some(value) = name.strip_prefix('\'') {
        ("<Qids>", NaValue::Qid(Rc::from(value)))
    } else if name.starts_with('"') && name.ends_with('"') {
        ("<Strings>", NaValue::Str(Rc::from(unquote_string(name))))
    } else {
        let value = name.parse::<f64>().ok()?;
        if value.is_nan() {
            return None;
        }
        let value = if value == 0.0 { 0.0 } else { value };
        ("<Floats>", NaValue::Float(value.to_bits()))
    };
    let symbol = target.engine.resolve_constant_at_sort(marker, sort);

    let symbol = symbol?;
    Some((symbol, value))
}

/// Down-translate a `metaTermSymbol` argument list (a `metaArgSymbol` `_,_` flattens to its elements;
/// anything else is a single argument) to kernel [`Term`]s.
fn down_arglist_to_term(
    ctx: &MetaCtx,
    hooks: &MetaHooks,
    list: DagId,
    target: &BuiltModule,
    vars: &mut VarIndex,
) -> Option<Vec<Term>> {
    let arg_sym = hooks.ops.get("metaArgSymbol").copied();
    if Some(ctx.top(list)) == arg_sym {
        ctx.children(list)
            .into_iter()
            .map(|c| down_term_to_term(ctx, hooks, c, target, vars))
            .collect()
    } else {
        Some(vec![down_term_to_term(ctx, hooks, list, target, vars)?])
    }
}

/// Build a kernel [`Term`] application from a meta op-name + down-translated args: an iterated name
/// `base^n` becomes one compact [`Term::Iter`]; otherwise the operator is `(name, arity)`.
fn build_app_term(head: &str, args: Vec<Term>, target: &BuiltModule) -> Option<Term> {
    let head = strip_op_blanks(head); // normalize a meta Qid's backtick-blanks to the canonical op name
    if let Some((base, count)) = head.rsplit_once('^') {
        let sym = *target.ops.get(&(base.to_string(), 1))?;
        if args.len() != 1 {
            return None;
        }
        return Term::iter_decimal(sym, count, args.into_iter().next()?);
    }
    let argument_sorts: Vec<SortId> = args
        .iter()
        .map(|argument| target.engine.term_sort(argument))
        .collect();
    let sym = target
        .engine
        .resolve_operator_for_sorts(&head, &argument_sorts)
        .or_else(|| {
            target
                .engine
                .resolve_operator_for_kinds(&head, &argument_sorts)
        })?;
    Some(Term::op(sym, args))
}

/// Down-translate an `ImportList` (`__`-flattened `including_.`/`protecting_.`/`extending_.` of a module
/// expression) to a list of [`Import`]s. Only a **named** module expression (a `Qid`) is handled.
fn down_imports(ctx: &MetaCtx, hooks: &MetaHooks, list: DagId) -> Option<Vec<Import>> {
    let nil = hooks.ops.get("nilImportListSymbol").copied();
    let cons = hooks.ops.get("importListSymbol").copied();
    let mut out = Vec::new();
    let mut stack = vec![list];
    while let Some(d) = stack.pop() {
        let sym = ctx.top(d);
        if Some(sym) == nil {
            continue;
        }
        if Some(sym) == cons {
            // `__` import list — recurse into its elements (children are already flattened by the AU rep).
            stack.extend(ctx.children(d));
            continue;
        }
        out.push(down_import(ctx, hooks, d)?);
    }
    out.reverse();
    Some(out)
}

/// Down-translate one import `including_./protecting_./extending_.(ModuleExpr)`.
fn down_import(ctx: &MetaCtx, hooks: &MetaHooks, imp: DagId) -> Option<Import> {
    let sym = ctx.top(imp);
    let mode = if hooks.ops.get("protectingSymbol") == Some(&sym) {
        ImportMode::Protecting
    } else if hooks.ops.get("extendingSymbol") == Some(&sym) {
        ImportMode::Extending
    } else if hooks.ops.get("includingSymbol") == Some(&sym)
        || hooks.ops.get("generatedBySymbol") == Some(&sym)
    {
        ImportMode::Including
    } else {
        return None;
    };
    let expr = *ctx.children(imp).first()?;
    Some(Import {
        mode,
        expr: down_module_expr(ctx, hooks, expr)?,
    })
}

/// Root named module of an expression, through instantiation and renaming spines. A sum has no single
/// signature against which a reflected operator-to-term mapping can be parsed.
fn module_expr_root_name(expr: &ModuleExpr) -> Option<&str> {
    match expr {
        ModuleExpr::Named(name) => Some(name),
        ModuleExpr::Instantiation(base, _) | ModuleExpr::Rename(base, _) => {
            module_expr_root_name(base)
        }
        ModuleExpr::Sum(_, _) => None,
    }
}

/// Down-translate the module-expression constructors emitted by [`up_module_expr`].
fn down_module_expr(ctx: &MetaCtx, hooks: &MetaHooks, e: DagId) -> Option<ModuleExpr> {
    if let NodeRepr::Qid(name) = ctx.repr(e) {
        return Some(ModuleExpr::Named(name.to_string()));
    }
    let symbol = ctx.top(e);
    let kids = ctx.children(e);
    if hooks.ops.get("sumSymbol") == Some(&symbol) || ctx.name(symbol) == "_+_" {
        let mut expressions = kids
            .iter()
            .map(|&child| down_module_expr(ctx, hooks, child));
        let first = expressions.next()??;
        return expressions.try_fold(first, |left, right| {
            Some(ModuleExpr::Sum(Box::new(left), Box::new(right?)))
        });
    }
    if hooks.ops.get("instantiationSymbol") == Some(&symbol) || ctx.name(symbol) == "_{_}" {
        let base = Box::new(down_module_expr(ctx, hooks, *kids.first()?)?);
        let list = *kids.get(1)?;
        let join = hooks.ops.get("parameterDeclListSymbol").copied();
        let arguments = flatten_set(ctx, list, None, join)
            .into_iter()
            .map(|argument| down_module_expr(ctx, hooks, argument))
            .collect::<Option<Vec<_>>>()?;
        return (!arguments.is_empty()).then_some(ModuleExpr::Instantiation(base, arguments));
    }
    if hooks.ops.get("renamingSymbol") == Some(&symbol) || ctx.name(symbol) == "_*(_)" {
        let base = Box::new(down_module_expr(ctx, hooks, *kids.first()?)?);
        let renaming = *kids.get(1)?;
        let join = hooks.ops.get("renamingSetSymbol").copied();
        let mut items = Vec::new();
        for mapping in flatten_set(ctx, renaming, None, join) {
            let mapping_symbol = ctx.top(mapping);
            let mapping_kids = ctx.children(mapping);
            let is = |hook: &str| {
                hooks.ops.get(hook).copied().is_some_and(|candidate| {
                    candidate == mapping_symbol || ctx.name(candidate) == ctx.name(mapping_symbol)
                })
            };
            if is("sortRenamingSymbol") {
                items.push(RenameItem::Sort {
                    from: qid_text(ctx, *mapping_kids.first()?)?,
                    to: qid_text(ctx, *mapping_kids.get(1)?)?,
                });
            } else if is("labelRenamingSymbol") {
                items.push(RenameItem::Label {
                    from: qid_text(ctx, *mapping_kids.first()?)?,
                    to: qid_text(ctx, *mapping_kids.get(1)?)?,
                });
            } else if is("opRenamingSymbol") {
                items.push(RenameItem::Op {
                    from: qid_text(ctx, *mapping_kids.first()?)?,
                    to: qid_text(ctx, *mapping_kids.get(1)?)?,
                    dom_range: None,
                    attrs: down_renaming_attrs(ctx, hooks, *mapping_kids.get(2)?)?,
                });
            } else if is("opRenamingSymbol2") {
                items.push(RenameItem::Op {
                    from: qid_text(ctx, *mapping_kids.first()?)?,
                    to: qid_text(ctx, *mapping_kids.get(3)?)?,
                    dom_range: Some((
                        down_typelist(ctx, hooks, *mapping_kids.get(1)?),
                        qid_text(ctx, *mapping_kids.get(2)?)?,
                    )),
                    attrs: down_renaming_attrs(ctx, hooks, *mapping_kids.get(4)?)?,
                });
            } else {
                return None;
            }
        }
        return (!items.is_empty()).then_some(ModuleExpr::Rename(base, items));
    }
    None
}

/// Decode the precedence, gather, and format overrides allowed on an operator renaming.
fn down_renaming_attrs(ctx: &MetaCtx, hooks: &MetaHooks, d: DagId) -> Option<Attrs> {
    let empty = hooks.ops.get("emptyAttrSetSymbol").copied();
    let join = hooks.ops.get("attrSetSymbol").copied();
    let mut attrs = Attrs::default();
    for attr in flatten_set(ctx, d, empty, join) {
        let symbol = ctx.top(attr);
        let is = |hook: &str| {
            hooks.ops.get(hook).copied().is_some_and(|candidate| {
                candidate == symbol || ctx.name(candidate) == ctx.name(symbol)
            })
        };
        if is("precSymbol") {
            attrs.prec = down_nat(ctx, *ctx.children(attr).first()?);
        } else if is("gatherSymbol") {
            let words = qidlist_texts(ctx, hooks, *ctx.children(attr).first()?)?;
            attrs.gather = Some(
                words
                    .iter()
                    .map(|word| match word.as_str() {
                        "e" => Some(GatherElem::Weak),
                        "E" => Some(GatherElem::Strong),
                        "&" => Some(GatherElem::Any),
                        _ => None,
                    })
                    .collect::<Option<Vec<_>>>()?,
            );
        } else if is("formatSymbol") {
            attrs.format = Some(qidlist_texts(ctx, hooks, *ctx.children(attr).first()?)?);
        } else {
            return None;
        }
    }
    Some(attrs)
}

// ---- down/up of terms ----

/// Down-translate a meta-term into a DAG in `target` (the object module). Handles a constant `'c.S`
/// (a `Qid` leaf), an application `'f[args]` (a `metaTermSymbol` node), and the iterated form `'s_^n[t]`.
///
/// # Panics
///
/// Panics if a strict reducer fails while theory-aware construction materializes an identity. Fallible
/// semantic owners must use [`try_down_term`].
pub fn down_term(
    ctx: &MetaCtx,
    hooks: &MetaHooks,
    t: DagId,
    target: &mut BuiltModule,
    interner: &mut Interner,
) -> Option<DagId> {
    try_down_term(ctx, hooks, t, target, interner)
        .unwrap_or_else(|fault| panic!("meta-term construction failed: {fault}"))
}

/// Fallible meta-term down-translation for semantic owners that must preserve strict reducer faults
/// raised while a theory-aware application materializes an attached identity.
pub fn try_down_term(
    ctx: &MetaCtx,
    hooks: &MetaHooks,
    t: DagId,
    target: &mut BuiltModule,
    interner: &mut Interner,
) -> Result<Option<DagId>, ReducerFault> {
    let mut vars = VarIndex::new();
    try_down_term_inner(ctx, hooks, t, target, &mut vars, interner)
}

fn try_down_term_inner(
    ctx: &MetaCtx,
    hooks: &MetaHooks,
    t: DagId,
    target: &mut BuiltModule,
    vars: &mut VarIndex,
    interner: &mut Interner,
) -> Result<Option<DagId>, ReducerFault> {
    let meta_term = hooks.ops.get("metaTermSymbol").copied();
    match ctx.repr(t) {
        NodeRepr::Qid(text) => Ok(down_leaf_to_dag(text, target, vars, interner)),
        NodeRepr::App
            if Some(ctx.top(t)) == meta_term
                || (ctx.name(ctx.top(t)) == "_[_]" && ctx.children(t).len() == 2) =>
        {
            let kids = ctx.children(t);
            let Some(&head) = kids.first() else {
                return Ok(None);
            };
            let head = match ctx.repr(head) {
                NodeRepr::Qid(s) => s.to_string(),
                _ => return Ok(None),
            };
            let Some(&args) = kids.get(1) else {
                return Ok(None);
            };
            let Some(args) = try_down_arglist(ctx, hooks, args, target, vars, interner)? else {
                return Ok(None);
            };
            try_build_app(&head, args, target)
        }
        _ => Ok(None),
    }
}

/// Down-translate a `metaTermSymbol` argument list — a `metaArgSymbol` (`_,_`) AU node flattens to its
/// elements; anything else is a single argument.
fn try_down_arglist(
    ctx: &MetaCtx,
    hooks: &MetaHooks,
    list: DagId,
    target: &mut BuiltModule,
    vars: &mut VarIndex,
    interner: &mut Interner,
) -> Result<Option<Vec<DagId>>, ReducerFault> {
    let arg_sym = hooks.ops.get("metaArgSymbol").copied();
    // A hand-written meta-term can resolve `_,_` through a declaration clone distinct from the symbol
    // captured by META-LEVEL's hook table. The enclosing `_[_]` fixes this child at `TermList`, so the
    // constructor name is an unambiguous fallback across that module boundary.
    let is_arg_list = Some(ctx.top(list)) == arg_sym
        || (ctx.name(ctx.top(list)) == "_,_" && ctx.children(list).len() >= 2);
    if is_arg_list {
        let children = ctx.children(list);
        let mut args = Vec::with_capacity(children.len());
        for child in children {
            let Some(arg) = try_down_term_inner(ctx, hooks, child, target, vars, interner)? else {
                return Ok(None);
            };
            args.push(arg);
        }
        Ok(Some(args))
    } else {
        let Some(arg) = try_down_term_inner(ctx, hooks, list, target, vars, interner)? else {
            return Ok(None);
        };
        Ok(Some(vec![arg]))
    }
}

/// Build a variable or constant meta-term leaf into a dynamic kernel DAG.
fn down_leaf_to_dag(
    text: &str,
    target: &mut BuiltModule,
    vars: &mut VarIndex,
    interner: &mut Interner,
) -> Option<DagId> {
    if let Some(colon) = text.find(':') {
        let sort = resolve_meta_sort_name(target, &text[colon + 1..])?;
        let index = vars.index_of(text, sort);
        let name = interner.intern(&text[..colon]).index();
        Some(target.engine.make_var(sort, name, index))
    } else {
        down_constant(text, target)
    }
}
/// Build a constant from a meta `'name.sort` (a `Qid` leaf): look up the arity-0 operator `name`.
fn down_constant(text: &str, target: &mut BuiltModule) -> Option<DagId> {
    let (raw_name, sort_name) = text.rsplit_once('.')?;
    let name = strip_op_blanks(raw_name);
    let sort = resolve_meta_sort_name(target, sort_name)?;
    if let Some(kind) = target.engine.smt_type(sort)
        && let Some(number) = SmtNumber::parse(&name, kind)
    {
        let component = target.engine.sorts().kind_of(sort);
        let symbol = target.engine.smt_info().number_symbol(component)?;
        return Some(target.engine.make_smt_number(symbol, number));
    }
    if let Some((symbol, value)) = decode_na_literal(raw_name, sort, target) {
        return Some(match value {
            NaValue::Str(value) => target.engine.make_string(symbol, &value),
            NaValue::Qid(value) => target.engine.make_qid(symbol, &value),
            NaValue::Float(bits) => target.engine.make_float(symbol, f64::from_bits(bits)),
            NaValue::SmtNum(_) => unreachable!("SMT literals are decoded above"),
        });
    }
    let symbol = target.engine.resolve_constant_at_sort(&name, sort)?;
    Some(target.engine.make_const(symbol))
}

/// Build an application from a meta op-name + down-translated args. An iterated name `base^n` builds the
/// `iter` successor `base^n(arg)`; otherwise the operator is looked up by `(name, arity)`.
fn try_build_app(
    head: &str,
    args: Vec<DagId>,
    target: &mut BuiltModule,
) -> Result<Option<DagId>, ReducerFault> {
    let head = strip_op_blanks(head);
    if let Some((base, count)) = head.rsplit_once('^')
        && let Ok(n) = count.parse::<u64>()
    {
        if args.len() != 1 {
            return Ok(None);
        }
        let Some(&sym) = target.ops.get(&(base.to_string(), 1)) else {
            return Ok(None);
        };
        return Ok(Some(target.engine.make_iter(sym, n, args[0])));
    }
    let argument_sorts: Vec<SortId> = args
        .iter()
        .map(|&argument| target.engine.sort_of(argument))
        .collect();
    let Some(sym) = target
        .engine
        .resolve_operator_for_sorts(&head, &argument_sorts)
        .or_else(|| {
            target
                .engine
                .resolve_operator_for_kinds(&head, &argument_sorts)
        })
    else {
        return Ok(None);
    };
    Ok(Some(target.engine.try_make_node(sym, args)?))
}

/// Encode an operator name as a META Qid, prefixing splitting punctuation with backticks. Canonical
/// inter-token blanks are already backticks and pass through.
fn meta_op_name(name: &str) -> String {
    let mut out = String::with_capacity(name.len());
    let mut escaped = false;
    for ch in name.chars() {
        if ch == '`' {
            if !escaped {
                out.push('`');
            }
            escaped = true;
        } else if matches!(ch, '(' | ')' | '[' | ']' | '{' | '}' | ',') {
            if !escaped {
                out.push('`');
            }
            out.push(ch);
            escaped = false;
        } else {
            out.push(ch);
            escaped = false;
        }
    }
    out
}

/// Mark the reserved class-attribute suffix as `` `:_ `` without changing ordinary `name:_` operators.
fn meta_attribute_name(name: &str, is_attribute: bool) -> String {
    let mut encoded = meta_op_name(name);
    if is_attribute && encoded.ends_with(":_") && !encoded.ends_with("`:_") {
        encoded.insert(encoded.len() - 2, '`');
    }
    encoded
}

fn meta_symbol_name(source: &BuiltModule, symbol: SymbolId) -> String {
    let syntax = source.syntax.get(&symbol);
    let is_attribute = source.engine.is_constructor(symbol)
        && syntax.is_some_and(|syntax| source.engine.sorts().name(syntax.range) == "Attribute");
    meta_attribute_name(source.engine.symbol(symbol).name(), is_attribute)
}

/// The inverse of [`meta_op_name`] for resolving a **down**-translated operator name to its canonical op
/// table key: strip only the backtick-blanks a meta Qid carries *around a split char* (`` bal`:_ `` →
/// `bal:_`, `` _`,_ `` → `_,_`) — the ones [`meta_op_name`] synthesizes and the canonical name omits. A
/// backtick before a *normal* char is a genuine inter-token blank that [`canonical_name`] keeps in the key
/// (`` a`b ``, `` c`d_ ``), so it is preserved here rather than stripped.
fn strip_op_blanks(name: &str) -> String {
    let is_split = |c: char| matches!(c, '_' | ':' | '(' | ')' | '[' | ']' | '{' | '}' | ',');
    let mut out = String::new();
    let mut chars = name.chars().peekable();
    while let Some(ch) = chars.next() {
        if ch == '`' {
            match chars.peek() {
                Some(&next) if is_split(next) => {
                    out.push(next); // a synthesized split-char blank — drop the backtick, keep the char
                    chars.next();
                }
                _ => out.push('`'), // a real text-text blank — part of the canonical key
            }
        } else {
            out.push(ch);
        }
    }
    out
}

/// Up-translate an object DAG `t` (in `source`) into a meta-term built in `ctx`.
pub fn up_term(ctx: &mut MetaCtx, hooks: &MetaHooks, source: &BuiltModule, t: DagId) -> DagId {
    up_term_inner(ctx, hooks, source, None, None, false, t)
}

/// Up-translate a symbolic object DAG, preserving variable leaves as typed variable Qids. The session
/// interner resolves the name token stored on each kernel variable.
pub fn up_parsed_term(
    ctx: &mut MetaCtx,
    hooks: &MetaHooks,
    source: &BuiltModule,
    interner: &Interner,
    t: DagId,
) -> DagId {
    up_term_inner(ctx, hooks, source, Some(interner), None, true, t)
}

/// Up-translate an SMT-search DAG using the search session's slot-indexed display names. Fresh
/// variables use synthetic kernel name codes, so consulting the ordinary interner would misname them.
fn up_smt_term(
    ctx: &mut MetaCtx,
    hooks: &MetaHooks,
    source: &BuiltModule,
    interner: &Interner,
    variable_names: &[String],
    t: DagId,
) -> DagId {
    up_term_inner(
        ctx,
        hooks,
        source,
        Some(interner),
        Some(variable_names),
        true,
        t,
    )
}

fn up_term_inner(
    ctx: &mut MetaCtx,
    hooks: &MetaHooks,
    source: &BuiltModule,
    interner: Option<&Interner>,
    variable_names: Option<&[String]>,
    rank_variable_qids: bool,
    t: DagId,
) -> DagId {
    let qid = hooks.ops["qidSymbol"];
    match source.engine.node(t).repr() {
        NodeRepr::App => {
            let sym = source.engine.node(t).symbol();
            let name = meta_symbol_name(source, sym);
            let kids: Vec<DagId> = source.engine.node(t).children().collect();
            if kids.is_empty() {
                // a constant → `'name.sort`
                let sort = source
                    .engine
                    .sorts()
                    .name(source.engine.sort_of(t))
                    .to_string();
                ctx.make_na(qid, NaValue::Qid(format!("{name}.{sort}").into()))
            } else {
                let up_args: Vec<DagId> = kids
                    .iter()
                    .map(|&k| {
                        up_term_inner(
                            ctx,
                            hooks,
                            source,
                            interner,
                            variable_names,
                            rank_variable_qids,
                            k,
                        )
                    })
                    .collect();
                let arglist = up_arglist(ctx, hooks, up_args);
                let opqid = ctx.make_na(qid, NaValue::Qid(name.into()));
                ctx.app(hooks.ops["metaTermSymbol"], vec![opqid, arglist])
            }
        }
        NodeRepr::Iter { count, arg } => {
            // `'base^count[up(arg)]` — `^count` only when count > 1 (`s^1` is `'s_[…]`).
            let base = meta_symbol_name(source, source.engine.node(t).symbol());
            let head = if count == "1" {
                base
            } else {
                format!("{base}^{count}")
            };
            let up_arg = up_term_inner(
                ctx,
                hooks,
                source,
                interner,
                variable_names,
                rank_variable_qids,
                arg,
            );
            let opqid = ctx.make_na(qid, NaValue::Qid(head.into()));
            ctx.app(hooks.ops["metaTermSymbol"], vec![opqid, up_arg])
        }
        NodeRepr::SmtNum(number) => {
            let sort = source.engine.sort_of(t);
            let kind = source
                .engine
                .smt_type(sort)
                .expect("SMT number without sort metadata");
            let text = number.to_maude(kind);
            let sort = source.engine.sorts().name(sort);
            ctx.make_na(qid, NaValue::Qid(format!("{text}.{sort}").into()))
        }
        NodeRepr::Qid(value) => {
            // A Qid literal is quoted once more inside its META representation: object `'NAT : Sort`
            // becomes the meta constant `''NAT.Sort` (whose stored Qid text starts with one quote).
            let sort = source.engine.sorts().name(source.engine.sort_of(t));
            ctx.make_na(qid, NaValue::Qid(format!("'{value}.{sort}").into()))
        }
        NodeRepr::Str(value) => {
            let sort = source.engine.sorts().name(source.engine.sort_of(t));
            let rendered = render_string(value);
            ctx.make_na(qid, NaValue::Qid(format!("{rendered}.{sort}").into()))
        }
        NodeRepr::Float(value) => {
            let sort = source.engine.sorts().name(source.engine.sort_of(t));
            let rendered = render_float(value);
            ctx.make_na(qid, NaValue::Qid(format!("{rendered}.{sort}").into()))
        }
        NodeRepr::Var { name } => {
            let text = source
                .engine
                .node(t)
                .variable_index()
                .and_then(|slot| variable_names.and_then(|names| names.get(slot as usize)))
                .map(String::as_str)
                .unwrap_or_else(|| {
                    interner
                        .expect("symbolic DAG reached ordinary up_term")
                        .resolve(Sym::from_raw(name))
                });
            let sort = source.engine.sorts().name(source.engine.sort_of(t));
            let typed = match text.rsplit_once(':') {
                Some((base, declared)) if !base.is_empty() && declared == sort => text.to_string(),
                _ => format!("{text}:{sort}"),
            };
            if rank_variable_qids {
                ctx.rank_qid(&typed);
            }
            ctx.make_na(qid, NaValue::Qid(typed.into()))
        }
    }
}

/// Join up-translated arguments into a `metaTermSymbol` argument list: a single argument stays itself; two
/// or more become a `metaArgSymbol` (`_,_`) list.
fn up_arglist(ctx: &mut MetaCtx, hooks: &MetaHooks, args: Vec<DagId>) -> DagId {
    if args.len() == 1 {
        args.into_iter().next().unwrap()
    } else {
        ctx.app(hooks.ops["metaArgSymbol"], args)
    }
}

// ---- Object-term translation over the module selected by MetaCtx ----

/// The snapshot of an object DAG node needed to up-translate it, taken with immutable `MetaCtx` reads
/// before the (mutable) result build — so `up_term_ctx` can recurse without a borrow conflict.
enum NodeShape {
    Leaf(String), // a constant `'name.sort` or NA literal `'"s".String` / `''q.Qid` / `'f.Float`
    App(String, Vec<DagId>), // an application `'name[args]`
    Iter(String, Vec<DagId>), // the iter head `name`/`name^count` + the single argument
}

/// Up-translate an already-reduced object DAG from the current engine into a meta `Term`. Handles
/// constants, applications, iterated successors, and nonalgebraic literals.
fn up_term_ctx(ctx: &mut MetaCtx, hooks: &MetaHooks, t: DagId) -> DagId {
    let qid = hooks.ops["qidSymbol"];
    let sort = ctx.sort_name(ctx.sort_of(t)).to_string();
    let shape = match ctx.repr(t) {
        NodeRepr::App => {
            let raw = ctx.name(ctx.top(t));
            let command_variable = ctx.symbol_is_command_variable(ctx.top(t));
            let kids = ctx.children(t);
            let variable_base = raw
                .rsplit_once(':')
                .filter(|(base, declared)| {
                    !base.is_empty() && !base.contains('`') && strip_op_blanks(declared) == sort
                })
                .map(|(base, _)| base)
                .or_else(|| {
                    sort.starts_with('[')
                        .then(|| raw.rsplit_once('.'))
                        .flatten()
                        .filter(|(base, declared)| {
                            !base.is_empty() && strip_op_blanks(declared) == sort
                        })
                        .map(|(base, _)| base)
                })
                .or_else(|| {
                    (sort.starts_with('[')
                        && raw.as_bytes().first().is_some_and(|byte| {
                            byte.is_ascii_uppercase() || matches!(*byte, b'#' | b'%' | b'@')
                        }))
                    .then_some(raw)
                })
                .or_else(|| command_variable.then_some(raw));
            if kids.is_empty()
                && let Some(base) = variable_base
            {
                // Kind variables are represented by the command parser as `X.[Kind]`; ordinary
                // variables use `X:Sort`. Both up-translate to the meta Qid `X:Type`.
                NodeShape::Leaf(format!("{}:{sort}", strip_op_blanks(base)))
            } else {
                let name = meta_attribute_name(
                    raw,
                    ctx.is_constructor(ctx.top(t)) && ctx.sort_name(ctx.sort_of(t)) == "Attribute",
                );
                if kids.is_empty() {
                    NodeShape::Leaf(format!("{name}.{sort}"))
                } else {
                    NodeShape::App(name, kids)
                }
            }
        }
        NodeRepr::Iter { count, arg } => {
            let base = meta_op_name(ctx.name(ctx.top(t)));
            let head = if count == "1" {
                base
            } else {
                format!("{base}^{count}")
            };
            NodeShape::Iter(head, vec![arg])
        }
        NodeRepr::Str(s) => NodeShape::Leaf(format!("{}.{sort}", render_string(s))),
        NodeRepr::Qid(q) => NodeShape::Leaf(format!("'{q}.{sort}")),
        NodeRepr::Float(f) => NodeShape::Leaf(format!("{}.{sort}", render_float(f))),
        NodeRepr::SmtNum(number) => {
            let kind = ctx
                .smt_type(ctx.sort_of(t))
                .expect("SMT number without sort metadata");
            NodeShape::Leaf(format!("{}.{sort}", number.to_maude(kind)))
        }
        // upTerm's argument is an eagerly-reduced object DAG of the current module — genuine
        // variable leaves exist only inside symbolic-engine problems (see `up_term`'s Var arm).
        NodeRepr::Var { .. } => {
            unreachable!("Var leaf reached up_term_ctx outside the metaUnify result path")
        }
    };
    match shape {
        NodeShape::Leaf(text) => ctx.make_na(qid, NaValue::Qid(text.into())),
        NodeShape::App(name, kids) => {
            let up_args: Vec<DagId> = kids.iter().map(|&k| up_term_ctx(ctx, hooks, k)).collect();
            let arglist = up_arglist(ctx, hooks, up_args);
            let opqid = ctx.make_na(qid, NaValue::Qid(name.into()));
            ctx.app(hooks.ops["metaTermSymbol"], vec![opqid, arglist])
        }
        NodeShape::Iter(head, arg) => {
            let up_arg = up_term_ctx(ctx, hooks, arg[0]);
            let opqid = ctx.make_na(qid, NaValue::Qid(head.into()));
            ctx.app(hooks.ops["metaTermSymbol"], vec![opqid, up_arg])
        }
    }
}

/// Down-translate a meta `Term` into the current module. Unresolvable operators and constants return
/// `None`, allowing the caller's default argument to win.
fn down_term_ctx(ctx: &mut MetaCtx, hooks: &MetaHooks, t: DagId) -> Option<DagId> {
    let meta_term = hooks.ops.get("metaTermSymbol").copied();
    // Snapshot the head + children with immutable reads before building.
    enum DShape {
        Const(String),
        App(String, Vec<DagId>),
    }
    let shape = match ctx.repr(t) {
        NodeRepr::Qid(text) => DShape::Const(text.to_string()),
        NodeRepr::App if Some(ctx.top(t)) == meta_term => {
            let kids = ctx.children(t);
            let NodeRepr::Qid(head) = ctx.repr(*kids.first()?) else {
                return None;
            };
            DShape::App(
                head.to_string(),
                down_arg_dags_ctx(ctx, hooks, *kids.get(1)?),
            )
        }
        _ => {
            return None;
        }
    };
    match shape {
        DShape::Const(text) => {
            let (name, sort) = text.rsplit_once('.')?;
            let name = strip_op_blanks(name);
            let sort = strip_op_blanks(sort);
            if let Some(constant) = ctx.constant_at_sort(&name, &sort) {
                return Some(constant);
            }
            let sym = ctx.resolve_op(&name, 0)?;
            Some(ctx.app(sym, vec![]))
        }
        DShape::App(head, arg_dags) => {
            let args: Vec<DagId> = arg_dags
                .iter()
                .map(|&a| down_term_ctx(ctx, hooks, a))
                .collect::<Option<_>>()?;
            if let Some((base, count)) = head.rsplit_once('^')
                && let Ok(n) = count.parse::<u64>()
            {
                let name = strip_op_blanks(base);
                let sym = ctx.resolve_op_for_args(&name, &args)?;
                return Some(ctx.make_iter(sym, n, *args.first()?));
            }
            let name = strip_op_blanks(&head);
            // Resolve by the actual argument sorts. A flat (≥3-arg) reflected ACU/AU application still
            // selects its binary associative declaration; `ctx.app` canonicalizes the flat argument list.
            let sym = ctx.resolve_op_for_args(&name, &args)?;
            Some(ctx.app(sym, args))
        }
    }
}

/// The DAG children of a `metaTermSymbol` argument list (`metaArgSymbol` flattens to its elements; anything
/// else is a single argument) — the raw arg DAGs, down-translated by the caller.
fn down_arg_dags_ctx(ctx: &MetaCtx, hooks: &MetaHooks, list: DagId) -> Vec<DagId> {
    if Some(ctx.top(list)) == hooks.ops.get("metaArgSymbol").copied() {
        ctx.children(list)
    } else {
        vec![list]
    }
}

/// Up-translate the least sort of `t` (in `source`) to its meta `Type` — a `Qid` of the sort name.
pub fn up_sort(ctx: &mut MetaCtx, hooks: &MetaHooks, source: &BuiltModule, t: DagId) -> DagId {
    let qid = hooks.ops["qidSymbol"];
    let sort = source
        .engine
        .sorts()
        .name(source.engine.sort_of(t))
        .to_string();
    ctx.make_na(qid, NaValue::Qid(sort.into()))
}

// ---- Sort and kind queries ----

/// Down-translate a meta `Type` (`'Sort` or `'[Kind]`) into the object module's [`SortId`]. A bracketed
/// `'[Max,…]` is a kind → the component's error sort (resolved from the first maximal sort named); a bare
/// name is a sort. `None` if the named sort is not in `m`.
fn down_type(ctx: &MetaCtx, m: &BuiltModule, d: DagId) -> Option<SortId> {
    let text = qid_text(ctx, d)?;
    if let Some(inner) = text.strip_prefix('[').and_then(|s| s.strip_suffix(']')) {
        // A kind name `[Max]` / `[A,B]` — resolve via the component of the first maximal sort named.
        let first = inner.split(',').next()?.trim();
        let s = *m.sorts.get(first)?;
        Some(m.engine.sorts().error_sort(m.engine.sorts().kind_of(s)))
    } else {
        m.sorts.get(&text).copied()
    }
}

/// Up-translate a [`SortId`] to its meta `Type` — a `Qid` of the sort name (an error sort's name is the
/// bracketed `[Kind]` form, which prints back-quoted).
fn up_type(ctx: &mut MetaCtx, hooks: &MetaHooks, m: &BuiltModule, s: SortId) -> DagId {
    let name = m.engine.sorts().name(s).to_string();
    ctx.make_na(hooks.ops["qidSymbol"], NaValue::Qid(name.into()))
}

/// Up-translate already-spelled sort names to a meta `TypeList`.
fn up_type_name_list(ctx: &mut MetaCtx, hooks: &MetaHooks, sorts: &[String]) -> DagId {
    let qid = hooks.ops["qidSymbol"];
    let elems = sorts
        .iter()
        .map(|sort| ctx.make_na(qid, NaValue::Qid(sort.as_str().into())))
        .collect();
    up_set(
        ctx,
        elems,
        hooks.ops["nilQidListSymbol"],
        hooks.ops["qidListSymbol"],
    )
}

/// Up-translate a sort list to a meta `TypeList` (`__`-joined `Qid`s; a singleton stays a `Type`, empty is
/// `nil`) — `maximalAritySet`'s argument-sort lists.
fn up_type_list(ctx: &mut MetaCtx, hooks: &MetaHooks, m: &BuiltModule, sorts: &[SortId]) -> DagId {
    let qid = hooks.ops["qidSymbol"];
    let elems: Vec<DagId> = sorts
        .iter()
        .map(|&s| ctx.make_na(qid, NaValue::Qid(m.engine.sorts().name(s).into())))
        .collect();
    up_set(
        ctx,
        elems,
        hooks.ops["nilQidListSymbol"],
        hooks.ops["qidListSymbol"],
    )
}

/// Build a META-LEVEL `Bool` result (`true`/`false`), resolved by name in the current module. `None` if
/// the current module has no boolean (it always does — META-LEVEL imports `BOOL`).
fn up_bool(ctx: &mut MetaCtx, b: bool) -> Option<DagId> {
    let sym = ctx.resolve_op(if b { "true" } else { "false" }, 0)?;
    Some(ctx.app(sym, vec![]))
}

/// Up-translate a set of sorts to a meta `SortSet`/`KindSet`/`TypeSet` — each as a `Qid`, joined by the
/// `_;_` ACU constructor; an empty set is `none`. The sort names are sorted so the (commutative) result is
/// deterministic; the kernel's ACU canonicalization then fixes the printed order.
fn up_sort_set(ctx: &mut MetaCtx, hooks: &MetaHooks, m: &BuiltModule, sorts: &[SortId]) -> DagId {
    let mut names: Vec<String> = sorts
        .iter()
        .map(|&s| m.engine.sorts().name(s).to_string())
        .collect();
    names.sort();
    let qids: Vec<DagId> = names
        .iter()
        .map(|n| ctx.make_na(hooks.ops["qidSymbol"], NaValue::Qid(n.as_str().into())))
        .collect();
    match qids.len() {
        0 => ctx.app(hooks.ops["emptySortSetSymbol"], vec![]),
        1 => qids.into_iter().next().unwrap(),
        _ => ctx.app(hooks.ops["sortSetSymbol"], qids),
    }
}

/// Check every application's argument kinds against its declared domain. Construction is permissive at
/// kind level, so `wellFormed(M, T)` performs this explicit validation.
fn term_well_formed(m: &BuiltModule, t: DagId) -> bool {
    let sym = m.engine.node(t).symbol();
    let kids: Vec<DagId> = m.engine.node(t).children().collect();
    if let Some(syntax) = m.syntax.get(&sym)
        && syntax.domain.len() == kids.len()
    {
        let sorts = m.engine.sorts();
        for (k, &dom) in kids.iter().zip(&syntax.domain) {
            if !sorts.same_kind(m.engine.sort_of(*k), dom) {
                return false;
            }
        }
    }
    kids.iter().all(|&k| term_well_formed(m, k))
}

/// Whether meta `Substitution` `d` is well-formed in `m`: every assignment `'X:Sort <- value` has a
/// value that down-translates to a well-formed term whose kind matches the variable's sort. Strict
/// reducer faults raised during construction remain distinct from malformed substitutions.
fn try_subst_well_formed(
    ctx: &MetaCtx,
    hooks: &MetaHooks,
    m: &mut BuiltModule,
    d: DagId,
    interner: &mut Interner,
) -> Result<bool, ReducerFault> {
    let empty = hooks.ops.get("emptySubstitutionSymbol").copied();
    let join = hooks.ops.get("substitutionSymbol").copied();
    let assign = hooks.ops.get("assignmentSymbol").copied();
    for a in flatten_set(ctx, d, empty, join) {
        if Some(ctx.top(a)) != assign {
            return Ok(false);
        }
        let kids = ctx.children(a);
        let Some((_, sort_name)) = kids.first().and_then(|&k| qid_text(ctx, k)).and_then(|t| {
            t.split_once(':')
                .map(|(n, s)| (n.to_string(), s.to_string()))
        }) else {
            return Ok(false);
        };
        let Some(&var_sort) = m.sorts.get(&sort_name) else {
            return Ok(false);
        };
        let Some(&val) = kids.get(1) else {
            return Ok(false);
        };
        let Some(value) = try_down_term(ctx, hooks, val, m, interner)? else {
            return Ok(false);
        };
        if !term_well_formed(m, value)
            || !m
                .engine
                .sorts()
                .same_kind(m.engine.sort_of(value), var_sort)
        {
            return Ok(false);
        }
    }
    Ok(true)
}

// ---- Declaration projections into the meta representation ----

/// Which declaration-set an individual `up*` projection emits.
#[derive(Clone, Copy)]
enum UpPart {
    Sorts,
    Subsorts,
    Ops,
    Mbs,
    Eqs,
    Rls,
}

/// Up-translate strategy declarations to a `StratDeclSet`; each element records its name, domain, subject
/// sort, and empty attribute set.
fn up_strat_decls_dag(
    ctx: &mut MetaCtx,
    hooks: &MetaHooks,
    declarations: &[StratDecl],
) -> Option<DagId> {
    let mut elements = Vec::with_capacity(declarations.len());
    for declaration in declarations {
        let name = ctx.make_na(
            hooks.ops["qidSymbol"],
            NaValue::Qid(declaration.name.as_str().into()),
        );
        let domain = declaration
            .domain
            .iter()
            .map(|sort| ctx.make_na(hooks.ops["qidSymbol"], NaValue::Qid(sort.as_str().into())))
            .collect();
        let domain = up_set(
            ctx,
            domain,
            hooks.ops["nilQidListSymbol"],
            hooks.ops["qidListSymbol"],
        );
        let subject = ctx.make_na(
            hooks.ops["qidSymbol"],
            NaValue::Qid(declaration.subject.as_str().into()),
        );
        let attrs = ctx.app(hooks.ops["emptyAttrSetSymbol"], Vec::new());
        elements.push(ctx.app(
            hooks.ops["stratDeclSymbol"],
            vec![name, domain, subject, attrs],
        ));
    }
    Some(up_set(
        ctx,
        elements,
        hooks.ops["emptyStratDeclSetSymbol"],
        hooks.ops["stratDeclSetSymbol"],
    ))
}

fn up_strategy_term(
    ctx: &mut MetaCtx,
    hooks: &MetaHooks,
    loaded: &mut LoadedModule,
    interner: &mut Interner,
    tokens: &[Token],
) -> Option<DagId> {
    let (term, vars, _) = build_logic_command_parses(loaded, interner, tokens)
        .ok()?
        .into_iter()
        .next()?;
    let names = typed_source_var_names(&loaded.built, &vars);
    Some(up_pattern(ctx, hooks, &loaded.built, &term, &names))
}

fn up_call_strategy(
    ctx: &mut MetaCtx,
    hooks: &MetaHooks,
    loaded: &mut LoadedModule,
    interner: &mut Interner,
    name: &str,
    args: &[Vec<Token>],
) -> Option<DagId> {
    let name = ctx.make_na(hooks.ops["qidSymbol"], NaValue::Qid(name.into()));
    let mut terms = Vec::with_capacity(args.len());
    for arg in args {
        terms.push(up_strategy_term(ctx, hooks, loaded, interner, arg)?);
    }
    let terms = if terms.is_empty() {
        ctx.app(hooks.ops["emptyTermListSymbol"], Vec::new())
    } else {
        up_arglist(ctx, hooks, terms)
    };
    Some(ctx.app(hooks.ops["callStratSymbol"], vec![name, terms]))
}

fn up_strategy(
    ctx: &mut MetaCtx,
    hooks: &MetaHooks,
    loaded: &mut LoadedModule,
    interner: &mut Interner,
    strategy: &StratExpr,
) -> Option<DagId> {
    match strategy {
        StratExpr::Idle => Some(ctx.app(hooks.ops["idleStratSymbol"], Vec::new())),
        StratExpr::Fail => Some(ctx.app(hooks.ops["failStratSymbol"], Vec::new())),
        StratExpr::All => Some(ctx.app(hooks.ops["allStratSymbol"], Vec::new())),
        StratExpr::Apply {
            label,
            subst,
            substrats,
        } => {
            if !subst.is_empty() {
                return None;
            }
            let label = ctx.make_na(hooks.ops["qidSymbol"], NaValue::Qid(label.as_str().into()));
            let subst = ctx.app(hooks.ops["emptySubstitutionSymbol"], Vec::new());
            let mut children = Vec::with_capacity(substrats.len());
            for child in substrats {
                children.push(up_strategy(ctx, hooks, loaded, interner, child)?);
            }
            let children = up_set(
                ctx,
                children,
                hooks.ops["emptyStratListSymbol"],
                hooks.ops["stratListSymbol"],
            );
            Some(ctx.app(
                hooks.ops["applicationStratSymbol"],
                vec![label, subst, children],
            ))
        }
        StratExpr::Top(child) => {
            let child = up_strategy(ctx, hooks, loaded, interner, child)?;
            Some(ctx.app(hooks.ops["topStratSymbol"], vec![child]))
        }
        StratExpr::One(child) => {
            let child = up_strategy(ctx, hooks, loaded, interner, child)?;
            Some(ctx.app(hooks.ops["oneStratSymbol"], vec![child]))
        }
        StratExpr::Seq(left, right) | StratExpr::Union(left, right) => {
            let left = up_strategy(ctx, hooks, loaded, interner, left)?;
            let right = up_strategy(ctx, hooks, loaded, interner, right)?;
            let hook = if matches!(strategy, StratExpr::Seq(_, _)) {
                "concatStratSymbol"
            } else {
                "unionStratSymbol"
            };
            Some(ctx.app(hooks.ops[hook], vec![left, right]))
        }
        StratExpr::Star(child) | StratExpr::Plus(child) | StratExpr::Normalize(child) => {
            let child = up_strategy(ctx, hooks, loaded, interner, child)?;
            let hook = match strategy {
                StratExpr::Star(_) => "starStratSymbol",
                StratExpr::Plus(_) => "plusStratSymbol",
                _ => "normalizationStratSymbol",
            };
            Some(ctx.app(hooks.ops[hook], vec![child]))
        }
        StratExpr::Branch {
            test,
            success,
            failure,
        } => {
            let test = up_strategy(ctx, hooks, loaded, interner, test)?;
            let success = up_strategy(ctx, hooks, loaded, interner, success)?;
            let failure = up_strategy(ctx, hooks, loaded, interner, failure)?;
            Some(ctx.app(
                hooks.ops["conditionalStratSymbol"],
                vec![test, success, failure],
            ))
        }
        StratExpr::Sugar { kind, args } => {
            let expected = if *kind == StratSugar::OrElse { 2 } else { 1 };
            if args.len() != expected {
                return None;
            }
            let mut children = Vec::with_capacity(args.len());
            for child in args {
                children.push(up_strategy(ctx, hooks, loaded, interner, child)?);
            }
            let hook = match kind {
                StratSugar::Try => "tryStratSymbol",
                StratSugar::NotS => "notStratSymbol",
                StratSugar::TestS => "testStratSymbol",
                StratSugar::OrElse => "orelseStratSymbol",
            };
            Some(ctx.app(hooks.ops[hook], children))
        }
        StratExpr::Call { name, args } => {
            up_call_strategy(ctx, hooks, loaded, interner, name, args)
        }
        StratExpr::Test {
            kind,
            pattern,
            cond,
        } => {
            // The empty condition is represented by the nullary identity of META-CONDITION's
            // conjunction. Conditioned tests need one shared VarIndex across pattern and condition.
            if cond.is_some() {
                return None;
            }
            let pattern = up_strategy_term(ctx, hooks, loaded, interner, pattern)?;
            let condition = ctx.app(hooks.ops["conjunctionSymbol"], Vec::new());
            let hook = match kind {
                TestKind::Match => "matchStratSymbol",
                TestKind::XMatch => "xmatchStratSymbol",
                TestKind::AMatch => "amatchStratSymbol",
            };
            Some(ctx.app(hooks.ops[hook], vec![pattern, condition]))
        }
        StratExpr::MatchRew { .. } => None,
    }
}

fn up_strat_defs_dag(
    ctx: &mut MetaCtx,
    hooks: &MetaHooks,
    loaded: &mut LoadedModule,
    interner: &mut Interner,
    definitions: &[StratDef],
) -> Option<DagId> {
    let mut elements = Vec::with_capacity(definitions.len());
    for definition in definitions {
        if definition.cond.is_some() {
            return None;
        }
        let call = up_call_strategy(
            ctx,
            hooks,
            loaded,
            interner,
            &definition.name,
            &definition.params,
        )?;
        let body = up_strategy(ctx, hooks, loaded, interner, &definition.body)?;
        let attrs = ctx.app(hooks.ops["emptyAttrSetSymbol"], Vec::new());
        elements.push(ctx.app(hooks.ops["sdSymbol"], vec![call, body, attrs]));
    }
    Some(up_set(
        ctx,
        elements,
        hooks.ops["emptyStratDefSetSymbol"],
        hooks.ops["stratDefSetSymbol"],
    ))
}

/// Decomposition used by module reflection. Signature declarations are import-first and statements
/// root-first; boundary fields deduplicate imports while retaining root/import overlaps.
struct ModulePieces {
    kind: ModuleKind,
    is_theory: bool,
    is_strategy: bool,
    /// Formal parameters `{X :: T, …}` of a parameterized module (empty otherwise) — emitted in the
    /// `upModule` header (`fmod 'LIST{'X :: 'TRIV} is`) for the non-flat form.
    params: Vec<Parameter>,
    sorts: Vec<String>,
    subsorts: Vec<Vec<Vec<String>>>,
    /// First root-owned subsort chain; the preceding flat-import prefix is already a declaration set.
    subsort_own_start: usize,
    ops: Vec<UpOp>,
    imports: Vec<Import>,
    mbs: Vec<MbTrace>,
    eqs: Vec<EqTrace>,
    rls: Vec<RlTrace>,
    strat_decls: Vec<StratDecl>,
    strat_defs: Vec<StratDef>,
    /// End of each root-owned statement prefix; the remaining flat-import suffix is already a set.
    mb_own_end: usize,
    eq_own_end: usize,
    rl_own_end: usize,
    /// `PreModule` statement slots and engine rule IDs for this module's executable rules, plus their
    /// canonical reflected order. Used when retaining a recognized non-flat database reflection.
    own_rule_slots: Vec<usize>,
    own_rule_ids: Vec<u32>,
    canonical_own_rule_ids: Vec<u32>,
    loaded: LoadedModule,
}

/// Partition statements into membership, equation, and rule traces in declaration order. Executable
/// statements clone the engine traces selected by `trace_refs`; `[nonexec]` statements are parsed on
/// demand because they have no engine trace. Statements whose trace cannot be recovered are omitted.
fn merge_statement_traces(
    stmts: &[Statement],
    loaded: &LoadedModule,
    i: &Interner,
    trace_refs: &[Option<StatementTraceRef>],
) -> (Vec<MbTrace>, Vec<EqTrace>, Vec<RlTrace>) {
    let b = &loaded.built;
    let (mut mbs, mut eqs, mut rls) = (Vec::new(), Vec::new(), Vec::new());
    for (stmt_index, stmt) in stmts.iter().enumerate() {
        match stmt {
            Statement::Mb { nonexec, .. } => {
                if *nonexec {
                    if let Ok(StmtTrace::Mb(t)) = parse_statement_trace(stmt, b, &loaded.grammar, i)
                    {
                        mbs.push(t);
                    }
                } else if let Some(StatementTraceRef::Membership(index)) =
                    trace_refs.get(stmt_index).copied().flatten()
                    && let Some(trace) = b.mb_traces.get(index)
                {
                    mbs.push(trace.clone());
                }
            }
            Statement::Eq { nonexec, .. } => {
                if *nonexec {
                    if let Ok(StmtTrace::Eq(t)) = parse_statement_trace(stmt, b, &loaded.grammar, i)
                    {
                        eqs.push(t);
                    }
                } else if let Some(StatementTraceRef::Equation(index)) =
                    trace_refs.get(stmt_index).copied().flatten()
                    && let Some(trace) = b.eq_traces.get(index)
                {
                    eqs.push(trace.clone());
                }
            }
            Statement::Rule { nonexec, .. } => {
                if *nonexec {
                    if let Ok(StmtTrace::Rl(t)) = parse_statement_trace(stmt, b, &loaded.grammar, i)
                    {
                        rls.push(t);
                    }
                } else if let Some(StatementTraceRef::Rule(index)) =
                    trace_refs.get(stmt_index).copied().flatten()
                    && let Some(trace) = b.rl_traces.get(index)
                {
                    rls.push(trace.clone());
                }
            }
        }
    }
    (mbs, eqs, rls)
}

/// One operator to up-translate: canonical name, normalized identity DAG, and surface declaration.
struct UpOp {
    name: String,
    identity: Option<DagId>,
    decl: OpDecl,
    /// Whether this declaration used `[ditto]`. Expanded semantic attributes exclude declaration-local
    /// presentation metadata such as `format`.
    ditto: bool,
    /// Root-owned declarations stay verbatim; inherited declarations are uniquized before reflection.
    own: bool,
}

fn resolve_source_operator(lm: &LoadedModule, name: &str, domain: &[String]) -> Option<SymbolId> {
    let argument_sorts: Vec<SortId> = domain
        .iter()
        .map(|sort| resolve_reflected_sort(lm, sort))
        .collect::<Option<_>>()?;
    lm.built
        .engine
        .resolve_operator_for_sorts(name, &argument_sorts)
}

/// Whether two declarations compile into one symbol: name, arity, and domain/range components agree.
fn same_compiled_op_profile(
    lm: &LoadedModule,
    interner: &Interner,
    left: &OpDecl,
    right: &OpDecl,
) -> bool {
    if canonical_name(&left.name, interner) != canonical_name(&right.name, interner)
        || left.domain.len() != right.domain.len()
    {
        return false;
    }
    let sorts = lm.built.engine.sorts();
    let domains_match = left.domain.iter().zip(&right.domain).all(|(left, right)| {
        resolve_reflected_sort(lm, left)
            .zip(resolve_reflected_sort(lm, right))
            .is_some_and(|(left, right)| sorts.kind_of(left) == sorts.kind_of(right))
    });
    domains_match
        && resolve_reflected_sort(lm, &left.range)
            .zip(resolve_reflected_sort(lm, &right.range))
            .is_some_and(|(left, right)| sorts.kind_of(left) == sorts.kind_of(right))
}

/// A meta `Bool` (`true`/`false`) → its value, by the constant's operator name.
fn down_bool(ctx: &MetaCtx, d: DagId) -> Option<bool> {
    match ctx.name(ctx.top(d)) {
        "true" => Some(true),
        "false" => Some(false),
        _ => None,
    }
}

/// Whether a meta `PrintOptionSet` (a `__`-joined tree of option constants) contains the option named
/// `name` (e.g. `mixfix`) — a structural walk over the option set.
fn has_option(ctx: &MetaCtx, d: DagId, name: &str) -> bool {
    ctx.name(ctx.top(d)) == name || ctx.children(d).iter().any(|&c| has_option(ctx, c, name))
}

/// Join meta-rep set elements with an ACU/AU constructor: an empty set is `empty`, a singleton stays
/// itself, two or more are joined by `join` (the kernel canonicalizes the assoc/comm order).
fn up_set(ctx: &mut MetaCtx, elems: Vec<DagId>, empty: SymbolId, join: SymbolId) -> DagId {
    match elems.len() {
        0 => ctx.app(empty, vec![]),
        1 => elems.into_iter().next().unwrap(),
        _ => ctx.app(join, elems),
    }
}
/// Deduplicate declarations within the flattened import closure while retaining every root declaration.
/// A root/import overlap remains for META-LEVEL's idempotence equation to consume.
fn retain_import_set_elements(ctx: &MetaCtx, elems: Vec<(DagId, bool)>) -> Vec<DagId> {
    let mut imported: HashMap<u64, Vec<DagId>> = HashMap::new();
    let mut retained = Vec::with_capacity(elems.len());
    for (elem, own) in elems {
        if own {
            retained.push(elem);
            continue;
        }
        let bucket = imported.entry(ctx.dag_hash(elem)).or_default();
        if bucket
            .iter()
            .any(|&prior| prior == elem || ctx.deep_equal(prior, elem))
        {
            continue;
        }
        bucket.push(elem);
        retained.push(elem);
    }
    retained
}

/// Up-translate a parameterized header and its parameter declarations. Returns `None` when the required
/// header symbols are absent.
fn up_header(
    ctx: &mut MetaCtx,
    hooks: &MetaHooks,
    name_qid: DagId,
    params: &[Parameter],
) -> Option<DagId> {
    let qid = hooks.ops["qidSymbol"];
    let decl_sym = *hooks.ops.get("parameterDeclSymbol")?;
    let decls: Vec<DagId> = params
        .iter()
        .map(|p| {
            let pname = ctx.make_na(qid, NaValue::Qid(p.name.as_str().into()));
            let theory = ctx.make_na(qid, NaValue::Qid(p.theory.as_str().into()));
            ctx.app(decl_sym, vec![pname, theory])
        })
        .collect();
    let decl_list = match decls.len() {
        1 => decls.into_iter().next().unwrap(),
        _ => ctx.app(*hooks.ops.get("parameterDeclListSymbol")?, decls),
    };
    Some(ctx.app(*hooks.ops.get("headerSymbol")?, vec![name_qid, decl_list]))
}

/// Up-translate an import list (`including_./protecting_./extending_.` of each module expression, joined by
/// `__`).
fn up_imports(ctx: &mut MetaCtx, hooks: &MetaHooks, imports: &[Import]) -> Option<DagId> {
    let mut elems = Vec::with_capacity(imports.len());
    for imp in imports {
        let expression = up_module_expr(ctx, hooks, &imp.expr)?;
        let ctor = match imp.mode {
            ImportMode::Protecting => "protectingSymbol",
            ImportMode::Extending => "extendingSymbol",
            ImportMode::Including => "includingSymbol",
        };
        elems.push(ctx.app(*hooks.ops.get(ctor)?, vec![expression]));
    }
    Some(up_set(
        ctx,
        elems,
        hooks.ops["nilImportListSymbol"],
        hooks.ops["importListSymbol"],
    ))
}

/// Up-translate a source module expression to META-MODULE's constructor representation.
fn up_module_expr(ctx: &mut MetaCtx, hooks: &MetaHooks, e: &ModuleExpr) -> Option<DagId> {
    match e {
        ModuleExpr::Named(name) => {
            Some(ctx.make_na(hooks.ops["qidSymbol"], NaValue::Qid(name.as_str().into())))
        }
        ModuleExpr::Sum(left, right) => {
            let left = up_module_expr(ctx, hooks, left)?;
            let right = up_module_expr(ctx, hooks, right)?;
            Some(ctx.app(*hooks.ops.get("sumSymbol")?, vec![left, right]))
        }
        ModuleExpr::Instantiation(base, arguments) => {
            let base = up_module_expr(ctx, hooks, base)?;
            let mut arguments: Vec<DagId> = arguments
                .iter()
                .map(|argument| up_module_expr(ctx, hooks, argument))
                .collect::<Option<_>>()?;
            let parameters = match arguments.len() {
                0 => return None,
                1 => arguments.pop().unwrap(),
                _ => {
                    let symbol = ctx.resolve_op_for_args("_,_", &arguments[..2])?;
                    let mut joined = ctx.app(symbol, arguments.drain(..2).collect());
                    for argument in arguments {
                        let args = vec![joined, argument];
                        let symbol = ctx.resolve_op_for_args("_,_", &args)?;
                        joined = ctx.app(symbol, args);
                    }
                    joined
                }
            };
            Some(ctx.app(
                *hooks.ops.get("instantiationSymbol")?,
                vec![base, parameters],
            ))
        }
        ModuleExpr::Rename(base, items) => {
            let base = up_module_expr(ctx, hooks, base)?;
            let renaming = up_renaming(ctx, hooks, items)?;
            Some(ctx.app(*hooks.ops.get("renamingSymbol")?, vec![base, renaming]))
        }
    }
}

/// Up-translate a source renaming to META-MODULE's nonempty `RenamingSet`.
fn up_renaming(ctx: &mut MetaCtx, hooks: &MetaHooks, items: &[RenameItem]) -> Option<DagId> {
    let qid = hooks.ops["qidSymbol"];
    let mut mappings = Vec::with_capacity(items.len());
    for item in items {
        let mapping = match item {
            RenameItem::Sort { from, to } => {
                let from = ctx.make_na(qid, NaValue::Qid(from.as_str().into()));
                let to = ctx.make_na(qid, NaValue::Qid(to.as_str().into()));
                ctx.app(*hooks.ops.get("sortRenamingSymbol")?, vec![from, to])
            }
            RenameItem::Label { from, to } => {
                let from = ctx.make_na(qid, NaValue::Qid(from.as_str().into()));
                let to = ctx.make_na(qid, NaValue::Qid(to.as_str().into()));
                ctx.app(*hooks.ops.get("labelRenamingSymbol")?, vec![from, to])
            }
            RenameItem::Op {
                from,
                to,
                dom_range,
                attrs,
            } => {
                let from = ctx.make_na(qid, NaValue::Qid(from.as_str().into()));
                let to = ctx.make_na(qid, NaValue::Qid(to.as_str().into()));
                let attrs = up_renaming_attrs(ctx, hooks, attrs)?;
                if let Some((domain, range)) = dom_range {
                    let domain = domain
                        .iter()
                        .map(|sort| ctx.make_na(qid, NaValue::Qid(sort.as_str().into())))
                        .collect();
                    let domain = up_set(
                        ctx,
                        domain,
                        hooks.ops["nilQidListSymbol"],
                        hooks.ops["qidListSymbol"],
                    );
                    let range = ctx.make_na(qid, NaValue::Qid(range.as_str().into()));
                    ctx.app(
                        *hooks.ops.get("opRenamingSymbol2")?,
                        vec![from, domain, range, to, attrs],
                    )
                } else {
                    ctx.app(*hooks.ops.get("opRenamingSymbol")?, vec![from, to, attrs])
                }
            }
        };
        mappings.push(mapping);
    }
    match mappings.len() {
        0 => None,
        1 => mappings.pop(),
        _ => Some(ctx.app(*hooks.ops.get("renamingSetSymbol")?, mappings)),
    }
}

fn up_renaming_attrs(ctx: &mut MetaCtx, hooks: &MetaHooks, attrs: &Attrs) -> Option<DagId> {
    let mut elements = Vec::new();
    if let Some(prec) = attrs.prec {
        let value = up_nat(ctx, prec as u64)?;
        elements.push(ctx.app(hooks.ops["precSymbol"], vec![value]));
    }
    if let Some(gather) = &attrs.gather {
        elements.push(up_gather(ctx, hooks, gather));
    }
    if let Some(format) = &attrs.format {
        let qid = hooks.ops["qidSymbol"];
        let words = format
            .iter()
            .map(|word| ctx.make_na(qid, NaValue::Qid(word.as_str().into())))
            .collect();
        let words = up_set(
            ctx,
            words,
            hooks.ops["nilQidListSymbol"],
            hooks.ops["qidListSymbol"],
        );
        elements.push(ctx.app(hooks.ops["formatSymbol"], vec![words]));
    }
    Some(up_set(
        ctx,
        elements,
        hooks.ops["emptyAttrSetSymbol"],
        hooks.ops["attrSetSymbol"],
    ))
}

/// Up-translate a sort-name list to a `SortSet` (`;`-joined `Qid`s, sorted for a deterministic ACU result).
fn up_sorts_dag(ctx: &mut MetaCtx, hooks: &MetaHooks, sorts: &[String]) -> DagId {
    let qid = hooks.ops["qidSymbol"];
    let mut names: Vec<&str> = sorts.iter().map(|s| s.as_str()).collect();
    names.sort_unstable();
    let elems: Vec<DagId> = names
        .iter()
        .map(|n| ctx.make_na(qid, NaValue::Qid((*n).into())))
        .collect();
    up_set(
        ctx,
        elems,
        hooks.ops["emptySortSetSymbol"],
        hooks.ops["sortSetSymbol"],
    )
}

/// Up-translate the subsort chains to a `SubsortDeclSet` — one `subsort A < B .` per consecutive pair of a
/// chain `A … < B … < C` (every member of one group below every member of the next), joined by `__`.
fn up_subsorts_dag(
    ctx: &mut MetaCtx,
    hooks: &MetaHooks,
    chains: &[Vec<Vec<String>>],
    own_start: usize,
) -> DagId {
    let qid = hooks.ops["qidSymbol"];
    let subsort = hooks.ops["subsortSymbol"];
    let mut imported: HashMap<u64, Vec<DagId>> = HashMap::new();
    let mut elems = Vec::new();
    for (chain_index, chain) in chains.iter().enumerate() {
        let own = chain_index >= own_start;
        let mut chain_elems = Vec::new();
        for pair in chain.windows(2) {
            for sub in &pair[0] {
                for sup in &pair[1] {
                    let a = ctx.make_na(qid, NaValue::Qid(sub.as_str().into()));
                    let b = ctx.make_na(qid, NaValue::Qid(sup.as_str().into()));
                    chain_elems.push(ctx.app(subsort, vec![a, b]));
                }
            }
        }

        // Drop a fully redundant imported chain. Retain any chain contributing a new edge in its entirety,
        // including duplicate edges consumed by META-LEVEL's idempotence equation. Always retain root chains.
        if !own
            && !chain_elems.iter().any(|&elem| {
                imported.get(&ctx.dag_hash(elem)).is_none_or(|bucket| {
                    !bucket
                        .iter()
                        .any(|&prior| prior == elem || ctx.deep_equal(prior, elem))
                })
            })
        {
            continue;
        }
        if !own {
            for &elem in &chain_elems {
                let bucket = imported.entry(ctx.dag_hash(elem)).or_default();
                if !bucket
                    .iter()
                    .any(|&prior| prior == elem || ctx.deep_equal(prior, elem))
                {
                    bucket.push(elem);
                }
            }
        }
        elems.extend(chain_elems);
    }
    up_set(
        ctx,
        elems,
        hooks.ops["emptySubsortDeclSetSymbol"],
        hooks.ops["subsortDeclSetSymbol"],
    )
}

/// Up-translate operator declarations in canonical-name order, including polymorph and hook attributes.
fn up_ops_dag(
    ctx: &mut MetaCtx,
    hooks: &MetaHooks,
    lm: &mut LoadedModule,
    interner: &Interner,
    ops: &[UpOp],
) -> Option<DagId> {
    let mut sorted: Vec<&UpOp> = ops.iter().collect();
    sorted.sort_by(|a, b| a.name.cmp(&b.name));
    let mut elems = Vec::with_capacity(sorted.len());
    for op in sorted {
        // `[ditto]` inherits the symbol-wide attributes from its primary declaration. Reflection emits
        // expanded attributes on every subsort overload rather than the source's bare `[ctor ditto]`.
        let attr_op = if op.ditto {
            ops.iter()
                .find(|candidate| {
                    !candidate.ditto
                        && same_compiled_op_profile(lm, interner, &op.decl, &candidate.decl)
                })
                .unwrap_or(op)
        } else {
            op
        };
        elems.push((up_op_decl(ctx, hooks, lm, interner, op, attr_op)?, op.own));
    }
    let elems = retain_import_set_elements(ctx, elems);
    Some(up_set(
        ctx,
        elems,
        hooks.ops["emptyOpDeclSetSymbol"],
        hooks.ops["opDeclSetSymbol"],
    ))
}

/// Up-translate one operator declaration `op N : D -> R [A] .` (`opDeclSymbol`): the name `Qid`, the
/// domain as a `TypeList` (`__`-joined sort `Qid`s, `nil` for a constant), the range `Type`, the `AttrSet`.
/// `op` supplies the name/domain/range; `attr_op` supplies the attribute set (they differ only for a
/// `ditto` overload, whose attributes come from the operator's primary declaration).
fn up_op_decl(
    ctx: &mut MetaCtx,
    hooks: &MetaHooks,
    lm: &mut LoadedModule,
    interner: &Interner,
    op: &UpOp,
    attr_op: &UpOp,
) -> Option<DagId> {
    let qid = hooks.ops["qidSymbol"];
    let name = ctx.make_na(
        qid,
        NaValue::Qid(
            meta_attribute_name(&op.name, op.decl.attrs.ctor && op.decl.range == "Attribute")
                .into(),
        ),
    );
    let domain_names: Vec<String> = op
        .decl
        .domain
        .iter()
        .map(|s| reflected_decl_type(lm, s, op.decl.partial))
        .collect();
    let dom_elems: Vec<DagId> = domain_names
        .iter()
        .map(|s| ctx.make_na(qid, NaValue::Qid(s.as_str().into())))
        .collect();
    let domain = up_set(
        ctx,
        dom_elems,
        hooks.ops["nilQidListSymbol"],
        hooks.ops["qidListSymbol"],
    );
    let range_name = reflected_decl_type(lm, &op.decl.range, op.decl.partial);
    let range = ctx.make_na(qid, NaValue::Qid(range_name.into()));
    let attrs = up_attrs(ctx, hooks, lm, interner, op, attr_op)?;
    Some(ctx.app(hooks.ops["opDeclSymbol"], vec![name, domain, range, attrs]))
}

/// The compiled type represented by one source declaration position. A `~>` declaration promotes
/// every position to its kind; ordinary declarations retain the named sort.
fn reflected_decl_type(lm: &LoadedModule, name: &str, partial: bool) -> String {
    let Some(sort) = resolve_reflected_sort(lm, name) else {
        return name.to_string();
    };
    let sorts = lm.built.engine.sorts();
    if !partial && sorts.component_index(sort) != 0 {
        return name.to_string();
    }
    let reflected = if partial {
        sorts.error_sort(sorts.kind_of(sort))
    } else {
        sort
    };
    sorts.name(reflected).to_string()
}

/// Up-translate an operator's surface [`Attrs`] to a meta `AttrSet`, including the `special` hook list and
/// `poly` positions needed to reflect and reinsert builtin modules. The set is ACU, so build order does not
/// fix the printed order.
fn up_attrs(
    ctx: &mut MetaCtx,
    hooks: &MetaHooks,
    lm: &mut LoadedModule,
    interner: &Interner,
    op: &UpOp,
    attr_op: &UpOp,
) -> Option<DagId> {
    let a = &attr_op.decl.attrs;
    let mut elems = Vec::new();
    let flag = |name: &str, on: bool, ctx: &mut MetaCtx, elems: &mut Vec<DagId>| {
        // Tolerant of a META-LEVEL that predates a given attribute symbol: skip rather than panic.
        if on && let Some(&s) = hooks.ops.get(name) {
            elems.push(ctx.app(s, vec![]));
        }
    };
    flag("ctorSymbol", a.ctor, ctx, &mut elems);
    flag("assocSymbol", a.assoc, ctx, &mut elems);
    flag("commSymbol", a.comm, ctx, &mut elems);
    flag("idemSymbol", a.idem, ctx, &mut elems);
    flag("iterSymbol", a.iter, ctx, &mut elems);
    // Object-system attributes carried by desugared object-module operators and emitted by `upModule`.
    flag("configSymbol", a.config, ctx, &mut elems);
    flag("objectSymbol", a.object, ctx, &mut elems);
    flag("msgSymbol", a.message, ctx, &mut elems);
    flag("portalSymbol", a.portal, ctx, &mut elems);
    flag("pconstSymbol", a.pconst, ctx, &mut elems);
    if let Some(prec) = a.prec {
        let n = up_nat(ctx, prec as u64)?;
        elems.push(ctx.app(hooks.ops["precSymbol"], vec![n]));
    }
    if let Some(gather) = &a.gather {
        elems.push(up_gather(ctx, hooks, gather));
    }
    if !op.ditto
        && let Some(format) = &op.decl.attrs.format
    {
        let qid = hooks.ops["qidSymbol"];
        let words: Vec<DagId> = format
            .iter()
            .map(|w| ctx.make_na(qid, NaValue::Qid(w.as_str().into())))
            .collect();
        let list = up_set(
            ctx,
            words,
            hooks.ops["nilQidListSymbol"],
            hooks.ops["qidListSymbol"],
        );
        elems.push(ctx.app(hooks.ops["formatSymbol"], vec![list]));
    }
    if let Some(identity) = attr_op.identity {
        let term = up_term(ctx, hooks, &lm.built, identity);
        let hook = match a.id_side {
            IdSide::Both => "idSymbol",
            IdSide::Left => "leftIdSymbol",
            IdSide::Right => "rightIdSymbol",
        };
        elems.push(ctx.app(hooks.ops[hook], vec![term]));
    }
    if let Some(strat) = &a.strat {
        let n = up_nat_list(ctx, hooks, strat)?;
        elems.push(ctx.app(hooks.ops["stratSymbol"], vec![n]));
    }
    if let Some(frozen) = &a.frozen {
        let positions: Vec<u32> = if frozen.is_empty() {
            (1..=op.decl.domain.len() as u32).collect()
        } else {
            frozen.clone()
        };
        let n = up_nat_list(ctx, hooks, &positions)?;
        elems.push(ctx.app(hooks.ops["frozenSymbol"], vec![n]));
    }
    if let Some(poly) = &a.poly {
        let positions = up_nat_list(ctx, hooks, poly)?;
        elems.push(ctx.app(hooks.ops["polySymbol"], vec![positions]));
    }
    if let Some(special) = &a.special {
        elems.push(up_special(ctx, hooks, lm, interner, special)?);
    }
    Some(up_set(
        ctx,
        elems,
        hooks.ops["emptyAttrSetSymbol"],
        hooks.ops["attrSetSymbol"],
    ))
}

/// Resolved metalevel constructor attachments emit in this canonical order rather than declaration
/// order. `HookList` is associative but noncommutative, so reflection and reinsertion preserve it.
const META_LEVEL_OP_HOOK_ORDER: &[&str] = &[
    "qidSymbol",
    "metaTermSymbol",
    "metaArgSymbol",
    "emptyTermListSymbol",
    "assignmentSymbol",
    "emptySubstitutionSymbol",
    "substitutionSymbol",
    "holeSymbol",
    "noConditionSymbol",
    "equalityConditionSymbol",
    "sortTestConditionSymbol",
    "matchConditionSymbol",
    "rewriteConditionSymbol",
    "conjunctionSymbol",
    "failStratSymbol",
    "idleStratSymbol",
    "allStratSymbol",
    "applicationStratSymbol",
    "topStratSymbol",
    "matchStratSymbol",
    "xmatchStratSymbol",
    "amatchStratSymbol",
    "unionStratSymbol",
    "concatStratSymbol",
    "orelseStratSymbol",
    "plusStratSymbol",
    "conditionalStratSymbol",
    "matchrewStratSymbol",
    "xmatchrewStratSymbol",
    "amatchrewStratSymbol",
    "callStratSymbol",
    "oneStratSymbol",
    "starStratSymbol",
    "normalizationStratSymbol",
    "notStratSymbol",
    "testStratSymbol",
    "tryStratSymbol",
    "usingStratSymbol",
    "usingListStratSymbol",
    "emptyStratListSymbol",
    "stratListSymbol",
    "headerSymbol",
    "parameterDeclSymbol",
    "parameterDeclListSymbol",
    "protectingSymbol",
    "extendingSymbol",
    "includingSymbol",
    "generatedBySymbol",
    "nilImportListSymbol",
    "importListSymbol",
    "emptySortSetSymbol",
    "sortSetSymbol",
    "subsortSymbol",
    "emptySubsortDeclSetSymbol",
    "subsortDeclSetSymbol",
    "nilQidListSymbol",
    "qidListSymbol",
    "emptyQidSetSymbol",
    "qidSetSymbol",
    "succSymbol",
    "natListSymbol",
    "unboundedSymbol",
    "noParentSymbol",
    "stringSymbol",
    "sortRenamingSymbol",
    "opRenamingSymbol",
    "opRenamingSymbol2",
    "labelRenamingSymbol",
    "stratRenamingSymbol",
    "stratRenamingSymbol2",
    "renamingSetSymbol",
    "sumSymbol",
    "renamingSymbol",
    "instantiationSymbol",
    "termHookSymbol",
    "hookListSymbol",
    "idHookSymbol",
    "opHookSymbol",
    "assocSymbol",
    "commSymbol",
    "idemSymbol",
    "iterSymbol",
    "idSymbol",
    "leftIdSymbol",
    "rightIdSymbol",
    "stratSymbol",
    "memoSymbol",
    "precSymbol",
    "gatherSymbol",
    "formatSymbol",
    "latexSymbol",
    "ctorSymbol",
    "frozenSymbol",
    "polySymbol",
    "configSymbol",
    "objectSymbol",
    "msgSymbol",
    "portalSymbol",
    "pconstSymbol",
    "rpoSymbol",
    "specialSymbol",
    "labelSymbol",
    "metadataSymbol",
    "owiseSymbol",
    "variantAttrSymbol",
    "narrowingSymbol",
    "nonexecSymbol",
    "printSymbol",
    "emptyAttrSetSymbol",
    "attrSetSymbol",
    "opDeclSymbol",
    "opDeclSetSymbol",
    "emptyOpDeclSetSymbol",
    "mbSymbol",
    "cmbSymbol",
    "emptyMembAxSetSymbol",
    "membAxSetSymbol",
    "eqSymbol",
    "ceqSymbol",
    "emptyEquationSetSymbol",
    "equationSetSymbol",
    "rlSymbol",
    "crlSymbol",
    "emptyRuleSetSymbol",
    "ruleSetSymbol",
    "stratDeclSymbol",
    "emptyStratDeclSetSymbol",
    "stratDeclSetSymbol",
    "sdSymbol",
    "csdSymbol",
    "emptyStratDefSetSymbol",
    "stratDefSetSymbol",
    "fmodSymbol",
    "fthSymbol",
    "modSymbol",
    "thSymbol",
    "smodSymbol",
    "sthSymbol",
    "sortMappingSymbol",
    "emptySortMappingSetSymbol",
    "sortMappingSetSymbol",
    "opMappingSymbol",
    "opSpecificMappingSymbol",
    "opTermMappingSymbol",
    "emptyOpMappingSetSymbol",
    "opMappingSetSymbol",
    "stratMappingSymbol",
    "stratSpecificMappingSymbol",
    "stratExprMappingSymbol",
    "emptyStratMappingSetSymbol",
    "stratMappingSetSymbol",
    "viewSymbol",
    "anyTypeSymbol",
    "unificandPairSymbol",
    "unificationConjunctionSymbol",
    "patternSubjectPairSymbol",
    "matchingConjunctionSymbol",
    "resultPairSymbol",
    "resultTripleSymbol",
    "result4TupleSymbol",
    "matchPairSymbol",
    "unificationTripleSymbol",
    "variantSymbol",
    "narrowingApplyResultSymbol",
    "narrowingSearchResultSymbol",
    "traceStepSymbol",
    "nilTraceSymbol",
    "traceSymbol",
    "narrowingStepSymbol",
    "nilNarrowingTraceSymbol",
    "narrowingTraceSymbol",
    "narrowingSearchPathResultSymbol",
    "smtResultSymbol",
    "noParseSymbol",
    "ambiguitySymbol",
    "failure2Symbol",
    "failure3Symbol",
    "failureIncomplete3Symbol",
    "failure4Symbol",
    "noUnifierPairSymbol",
    "noUnifierTripleSymbol",
    "noUnifierIncompletePairSymbol",
    "noUnifierIncompleteTripleSymbol",
    "noVariantSymbol",
    "noVariantIncompleteSymbol",
    "narrowingApplyFailureSymbol",
    "narrowingApplyFailureIncompleteSymbol",
    "narrowingSearchFailureSymbol",
    "narrowingSearchFailureIncompleteSymbol",
    "narrowingSearchPathFailureSymbol",
    "narrowingSearchPathFailureIncompleteSymbol",
    "noMatchSubstSymbol",
    "noMatchIncompleteSubstSymbol",
    "noMatchPairSymbol",
    "failureTraceSymbol",
    "smtFailureSymbol",
    "noStratParseSymbol",
    "stratAmbiguitySymbol",
    "mixfixSymbol",
    "withParensSymbol",
    "withSortsSymbol",
    "flatSymbol",
    "formatPrintOptionSymbol",
    "numberSymbol",
    "ratSymbol",
    "emptyPrintOptionSetSymbol",
    "printOptionSetSymbol",
    "delaySymbol",
    "filterSymbol",
    "emptyVariantOptionSetSymbol",
    "variantOptionSetSymbol",
    "breadthFirstSymbol",
    "depthFirstSymbol",
    "legacyUnificationPairSymbol",
    "legacyUnificationTripleSymbol",
    "legacyVariantSymbol",
];

/// Reify a source `special (...)` specification into META-LEVEL's nonempty `HookList`.
fn up_special(
    ctx: &mut MetaCtx,
    hooks: &MetaHooks,
    lm: &mut LoadedModule,
    interner: &Interner,
    spec: &SpecialSpec,
) -> Option<DagId> {
    let qid_symbol = hooks.ops["qidSymbol"];
    let qid_list = |ctx: &mut MetaCtx, values: &[String]| {
        let elems = values
            .iter()
            .map(|value| ctx.make_na(qid_symbol, NaValue::Qid(value.as_str().into())))
            .collect();
        up_set(
            ctx,
            elems,
            hooks.ops["nilQidListSymbol"],
            hooks.ops["qidListSymbol"],
        )
    };
    let mut out = Vec::new();
    if let Some((class, data)) = &spec.id_hook {
        let class = ctx.make_na(qid_symbol, NaValue::Qid(class.as_str().into()));
        let data = qid_list(ctx, data);
        out.push(ctx.app(hooks.ops["idHookSymbol"], vec![class, data]));
    }
    let mut op_hooks: Vec<_> = spec.op_hooks.iter().collect();
    if spec
        .id_hook
        .as_ref()
        .is_some_and(|(class, _)| class == "MetaLevelOpSymbol")
    {
        op_hooks.sort_by_key(|(purpose, _)| {
            META_LEVEL_OP_HOOK_ORDER
                .iter()
                .position(|candidate| candidate == purpose)
                .unwrap_or(usize::MAX)
        });
    }
    for (purpose, signature) in op_hooks {
        let (name, source_domain, source_range) = hook_signature_parts(signature, interner)?;
        let (domain, range) = reflected_hook_signature(lm, &name, &source_domain, &source_range)
            .unwrap_or((source_domain, source_range));
        let purpose = ctx.make_na(qid_symbol, NaValue::Qid(purpose.as_str().into()));
        let name = ctx.make_na(qid_symbol, NaValue::Qid(meta_op_name(&name).into()));
        let domain = qid_list(ctx, &domain);
        let range = ctx.make_na(qid_symbol, NaValue::Qid(range.into()));
        out.push(ctx.app(
            hooks.ops["opHookSymbol"],
            vec![purpose, name, domain, range],
        ));
    }
    for (purpose, term) in &spec.term_hooks {
        let parsed = parse_command_term(lm, interner, term).ok()?;
        let object_term = build_command_dag(lm, interner, &parsed).ok()?;
        let object_term = up_term(ctx, hooks, &lm.built, object_term);
        let purpose = ctx.make_na(qid_symbol, NaValue::Qid(purpose.as_str().into()));
        out.push(ctx.app(hooks.ops["termHookSymbol"], vec![purpose, object_term]));
    }
    let hook_list = match out.len() {
        0 => return None,
        1 => out.pop().unwrap(),
        _ => ctx.app(hooks.ops["hookListSymbol"], out),
    };
    Some(ctx.app(hooks.ops["specialSymbol"], vec![hook_list]))
}

/// Decode an `op-hook` source signature into its canonical name, domain sort names, and range sort.
fn hook_signature_parts(
    signature: &[Token],
    interner: &Interner,
) -> Option<(String, Vec<String>, String)> {
    let text = |token: &Token| interner.resolve(token.sym);
    let colon = signature.iter().position(|token| text(token) == ":")?;
    let arrow = signature
        .iter()
        .enumerate()
        .skip(colon + 1)
        .find_map(|(index, token)| matches!(text(token), "->" | "~>").then_some(index))?;
    let join = |tokens: &[Token]| tokens.iter().map(&text).collect::<String>();
    let consume_type = |start: usize, limit: usize| -> Option<usize> {
        if start >= limit {
            return None;
        }
        let mut index = start;
        let opener = text(&signature[index]);
        if opener == "[" {
            let mut depth = 0i32;
            while index < limit {
                match text(&signature[index]) {
                    "[" => depth += 1,
                    "]" => depth -= 1,
                    _ => {}
                }
                index += 1;
                if depth == 0 {
                    break;
                }
            }
            (depth == 0).then_some(index)
        } else {
            index += 1;
            while index < limit && text(&signature[index]) == "{" {
                let mut depth = 0i32;
                while index < limit {
                    match text(&signature[index]) {
                        "{" => depth += 1,
                        "}" => depth -= 1,
                        _ => {}
                    }
                    index += 1;
                    if depth == 0 {
                        break;
                    }
                }
                if depth != 0 {
                    return None;
                }
            }
            Some(index)
        }
    };

    let name = canonical_name(&signature[..colon], interner);
    let range_start = arrow + 1;
    let range_end = consume_type(range_start, signature.len())?;
    let range = join(&signature[range_start..range_end]);
    if name.is_empty() || range.is_empty() {
        return None;
    }
    let mut domain = Vec::new();
    let mut index = colon + 1;
    while index < arrow {
        let start = index;
        index = consume_type(start, arrow)?;
        domain.push(join(&signature[start..index]));
    }
    Some((name, domain, range))
}

/// Reflect the exact declaration selected by an `op-hook`, representing kind positions by component
/// sort 1.
fn reflected_hook_signature(
    lm: &LoadedModule,
    name: &str,
    source_domain: &[String],
    source_range: &str,
) -> Option<(Vec<String>, String)> {
    let argument_sorts: Vec<SortId> = source_domain
        .iter()
        .map(|name| resolve_reflected_sort(lm, name))
        .collect::<Option<_>>()?;
    // Resolving the range too prevents a malformed source signature from selecting an unrelated symbol
    // that merely has an applicable domain.
    let source_range = resolve_reflected_sort(lm, source_range)?;
    let symbol =
        lm.built
            .engine
            .resolve_operator_for_kind_profile(name, &argument_sorts, source_range)?;
    let (domain, range) = lm
        .built
        .engine
        .symbol_declarations(symbol)
        .into_iter()
        .find(|(domain, range)| domain == &argument_sorts && *range == source_range)?;
    let domain = domain
        .into_iter()
        .map(|sort| hook_sort_name(lm, sort))
        .collect();
    Some((domain, hook_sort_name(lm, range)))
}

fn resolve_reflected_sort(lm: &LoadedModule, name: &str) -> Option<SortId> {
    if let Some(&sort) = lm.built.sorts.get(name) {
        return Some(sort);
    }
    let inner = name.strip_prefix('[')?.strip_suffix(']')?;
    let member_name = inner.split(',').next()?.trim();
    let member = *lm.built.sorts.get(member_name)?;
    let sorts = lm.built.engine.sorts();
    Some(sorts.error_sort(sorts.kind_of(member)))
}

fn hook_sort_name(lm: &LoadedModule, sort: SortId) -> String {
    let sorts = lm.built.engine.sorts();
    let selected = if sorts.component_index(sort) == 0 {
        sorts.kind(sorts.kind_of(sort)).index_order[1]
    } else {
        sort
    };
    sorts.name(selected).to_string()
}

/// Up-translate a `gather (…)` pattern (`gatherSymbol` of a `QidList` of `'e`/`'E`/`'&`).
fn up_gather(ctx: &mut MetaCtx, hooks: &MetaHooks, gather: &[GatherElem]) -> DagId {
    let qid = hooks.ops["qidSymbol"];
    let words: Vec<DagId> = gather
        .iter()
        .map(|g| {
            let s = match g {
                GatherElem::Weak => "e",
                GatherElem::Strong => "E",
                GatherElem::Any => "&",
            };
            ctx.make_na(qid, NaValue::Qid(s.into()))
        })
        .collect();
    let list = up_set(
        ctx,
        words,
        hooks.ops["nilQidListSymbol"],
        hooks.ops["qidListSymbol"],
    );
    ctx.app(hooks.ops["gatherSymbol"], vec![list])
}

/// Up-translate a `u64` to a meta `Nat` — `'0.Zero` for 0, else the `iter` successor `s_^n(0)`, built in
/// the current module (META-LEVEL imports `NAT`). `None` if `NAT`'s `0`/`s_` are not in scope.
fn up_nat(ctx: &mut MetaCtx, n: u64) -> Option<DagId> {
    let zero = ctx.app(ctx.resolve_op("0", 0)?, vec![]);
    if n == 0 {
        Some(zero)
    } else {
        Some(ctx.make_iter(ctx.resolve_op("s_", 1)?, n, zero))
    }
}

/// Build an unbounded Nat-family `metaUnify` index that may exceed `u64`: `s_^count(0)`, or `0` when
/// `count` is `"0"`.
fn up_nat_big(ctx: &mut MetaCtx, count: &str) -> Option<DagId> {
    let zero = ctx.app(ctx.resolve_op("0", 0)?, vec![]);
    if count == "0" {
        Some(zero)
    } else {
        ctx.make_iter_decimal(ctx.resolve_op("s_", 1)?, count, zero)
    }
}

/// Up-translate a 1-based position list to a meta `NatList` (`__`-joined `Nat`s; a singleton stays a `Nat`).
fn up_nat_list(ctx: &mut MetaCtx, hooks: &MetaHooks, positions: &[u32]) -> Option<DagId> {
    let nats: Vec<DagId> = positions
        .iter()
        .map(|&p| up_nat(ctx, p as u64))
        .collect::<Option<_>>()?;
    Some(match nats.len() {
        1 => nats.into_iter().next().unwrap(),
        _ => ctx.app(hooks.ops["natListSymbol"], nats),
    })
}

/// Build a statement `AttrSet` from the enabled `owise`, `variant`, `narrowing`, and `nonexec` flags plus
/// an optional `label(Q)`. The returned set uses the protocol's order-independent ACU representation.
fn stmt_attr_set(
    ctx: &mut MetaCtx,
    hooks: &MetaHooks,
    owise: bool,
    variant: bool,
    narrowing: bool,
    nonexec: bool,
    label: Option<&str>,
) -> DagId {
    let mut elems = Vec::new();
    if owise && let Some(&s) = hooks.ops.get("owiseSymbol") {
        elems.push(ctx.app(s, vec![]));
    }
    if nonexec && let Some(&s) = hooks.ops.get("nonexecSymbol") {
        elems.push(ctx.app(s, vec![]));
    }
    if variant && let Some(&s) = hooks.ops.get("variantAttrSymbol") {
        elems.push(ctx.app(s, vec![]));
    }
    if narrowing && let Some(&s) = hooks.ops.get("narrowingSymbol") {
        elems.push(ctx.app(s, vec![]));
    }
    if let Some(l) = label {
        let lqid = ctx.make_na(hooks.ops["qidSymbol"], NaValue::Qid(l.into()));
        elems.push(ctx.app(hooks.ops["labelSymbol"], vec![lqid]));
    }
    up_set(
        ctx,
        elems,
        hooks.ops["emptyAttrSetSymbol"],
        hooks.ops["attrSetSymbol"],
    )
}

/// Up-translate membership traces to a `MembAxSet` (`mb`/`cmb` joined by `__`), preserving `nonexec` and
/// optional `label(Q)` attributes.
fn up_membs_dag(
    ctx: &mut MetaCtx,
    hooks: &MetaHooks,
    m: &BuiltModule,
    traces: &[MbTrace],
    own_end: usize,
) -> Option<DagId> {
    let mut elems = Vec::new();
    for (index, t) in traces.iter().enumerate() {
        let lhs = up_pattern(ctx, hooks, m, &t.lhs, &t.var_names);
        let sort = up_type(ctx, hooks, m, t.sort);
        let attrs = stmt_attr_set(
            ctx,
            hooks,
            false,
            false,
            false,
            t.nonexec,
            t.label.as_deref(),
        );
        let mb = if t.condition.is_empty() {
            ctx.app(hooks.ops["mbSymbol"], vec![lhs, sort, attrs])
        } else {
            let cond = up_condition(ctx, hooks, m, &t.condition, &t.var_names);
            ctx.app(hooks.ops["cmbSymbol"], vec![lhs, sort, cond, attrs])
        };
        elems.push((mb, index < own_end));
    }
    let elems = retain_import_set_elements(ctx, elems);
    Some(up_set(
        ctx,
        elems,
        hooks.ops["emptyMembAxSetSymbol"],
        hooks.ops["membAxSetSymbol"],
    ))
}

/// Up-translate equation traces to an `EquationSet` (`eq`/`ceq` joined by `__`), preserving enabled
/// `owise`, `variant`, `nonexec`, and optional `label(Q)` attributes.
fn up_eqs_dag(
    ctx: &mut MetaCtx,
    hooks: &MetaHooks,
    m: &mut BuiltModule,
    interner: &mut Interner,
    traces: &[EqTrace],
    own_end: usize,
) -> Result<DagId, ReducerFault> {
    let mut elems = Vec::new();
    for (index, t) in traces.iter().enumerate() {
        let (lhs, rhs) = if t.variant {
            (
                up_normalized_pattern(ctx, hooks, m, interner, &t.lhs, &t.var_names)?,
                up_normalized_pattern(ctx, hooks, m, interner, &t.rhs, &t.var_names)?,
            )
        } else {
            (
                up_pattern(ctx, hooks, m, &t.lhs, &t.var_names),
                up_pattern(ctx, hooks, m, &t.rhs, &t.var_names),
            )
        };
        let attrs = stmt_attr_set(
            ctx,
            hooks,
            t.owise,
            t.variant,
            false,
            t.nonexec,
            t.label.as_deref(),
        );
        let eq = if t.condition.is_empty() {
            ctx.app(hooks.ops["eqSymbol"], vec![lhs, rhs, attrs])
        } else {
            let cond = up_condition(ctx, hooks, m, &t.condition, &t.var_names);
            ctx.app(hooks.ops["ceqSymbol"], vec![lhs, rhs, cond, attrs])
        };
        elems.push((eq, index < own_end));
    }
    let elems = retain_import_set_elements(ctx, elems);
    Ok(up_set(
        ctx,
        elems,
        hooks.ops["emptyEquationSetSymbol"],
        hooks.ops["equationSetSymbol"],
    ))
}

/// Up-translate rule traces to a `RuleSet` (`rl`/`crl` joined by `__`), preserving `narrowing`, `nonexec`,
/// and optional `label(Q)` attributes.
fn up_rls_dag(
    ctx: &mut MetaCtx,
    hooks: &MetaHooks,
    m: &BuiltModule,
    traces: &[RlTrace],
    own_end: usize,
) -> Option<DagId> {
    let mut elems = Vec::new();
    for (index, t) in traces.iter().enumerate() {
        elems.push((up_rule(ctx, hooks, m, t)?, index < own_end));
    }
    let elems = retain_import_set_elements(ctx, elems);
    Some(up_set(
        ctx,
        elems,
        hooks.ops["emptyRuleSetSymbol"],
        hooks.ops["ruleSetSymbol"],
    ))
}

/// Up-translate a condition (the inverse of [`down_condition`]): one fragment stays itself, several are
/// `_/\_`-conjoined. Each fragment is `_=_`/`_:_`/`_:=_`/`_=>_`.
fn up_condition(
    ctx: &mut MetaCtx,
    hooks: &MetaHooks,
    m: &BuiltModule,
    frags: &[ConditionFragment],
    names: &[String],
) -> DagId {
    let ups: Vec<DagId> = frags
        .iter()
        .map(|f| up_condition_fragment(ctx, hooks, m, f, names))
        .collect();
    match ups.len() {
        1 => ups.into_iter().next().unwrap(),
        _ => ctx.app(hooks.ops["conjunctionSymbol"], ups),
    }
}

/// Up-translate one condition fragment to its meta constructor.
fn up_condition_fragment(
    ctx: &mut MetaCtx,
    hooks: &MetaHooks,
    m: &BuiltModule,
    f: &ConditionFragment,
    names: &[String],
) -> DagId {
    match f {
        ConditionFragment::Equality { lhs, rhs } => {
            let l = up_pattern(ctx, hooks, m, lhs, names);
            let r = up_pattern(ctx, hooks, m, rhs, names);
            ctx.app(hooks.ops["equalityConditionSymbol"], vec![l, r])
        }
        ConditionFragment::SortTest { term, sort } => {
            let t = up_pattern(ctx, hooks, m, term, names);
            let s = up_type(ctx, hooks, m, *sort);
            ctx.app(hooks.ops["sortTestConditionSymbol"], vec![t, s])
        }
        ConditionFragment::Matching {
            pattern, subject, ..
        } => {
            let p = up_pattern(ctx, hooks, m, pattern, names);
            let s = up_pattern(ctx, hooks, m, subject, names);
            ctx.app(hooks.ops["matchConditionSymbol"], vec![p, s])
        }
        ConditionFragment::Rewrite { lhs, pattern, .. } => {
            let l = up_pattern(ctx, hooks, m, lhs, names);
            let p = up_pattern(ctx, hooks, m, pattern, names);
            ctx.app(hooks.ops["rewriteConditionSymbol"], vec![l, p])
        }
    }
}

fn instantiate_narrowing_solution(
    engine: &mut Engine,
    term: DagId,
    solution: &tnk_core::narrow::NarrowingSolution,
) -> DagId {
    let mut values = Vec::new();
    let mut work = vec![term];
    while let Some(dag) = work.pop() {
        let node = engine.node(dag);
        if let (Some(index), NodeRepr::Var { name }) = (node.variable_index(), node.repr()) {
            if let Some(slot) = solution
                .variables
                .iter()
                .position(|spec| spec.name == name && spec.sort == engine.sort_of(dag))
            {
                let index = index as usize;
                if values.len() <= index {
                    values.resize(index + 1, None);
                }
                values[index] = Some(solution.bindings[slot]);
            }
        } else {
            work.extend(node.children());
        }
    }
    tnk_core::unify::instantiate(engine, &values, term).unwrap_or(term)
}

/// The `metaNarrow` result names goal-match variables by reached-state ordinals. The goal unifier may
/// alpha-permute those variables (for example `@1 -> %2`, `@2 -> %1`), so compose the inverse
/// ordinal-preserving alpha map into the result.
fn narrowing_result_alpha_map(
    engine: &mut Engine,
    interner: &mut Interner,
    solution: &tnk_core::narrow::NarrowingSolution,
) -> Vec<Option<DagId>> {
    let mut values = Vec::new();
    for (spec, &binding) in solution.variables.iter().zip(&solution.bindings) {
        let source_name = interner.resolve_index(spec.name).to_string();
        let source_bytes = source_name.as_bytes();
        if !matches!(source_bytes.first(), Some(b'#' | b'%' | b'@')) {
            continue;
        }
        let node = engine.node(binding);
        let (Some(index), NodeRepr::Var { name }) = (node.variable_index(), node.repr()) else {
            continue;
        };
        let target_name = interner.resolve_index(name).to_string();
        let target_bytes = target_name.as_bytes();
        if !matches!(target_bytes.first(), Some(b'#' | b'%' | b'@')) {
            continue;
        }
        let desired = format!("{}{}", target_bytes[0] as char, &source_name[1..]);
        let desired_code = interner.intern(&desired).index();
        let renamed = engine.make_var(engine.sort_of(binding), desired_code, index);
        let index = index as usize;
        if values.len() <= index {
            values.resize(index + 1, None);
        }
        values[index] = Some(renamed);
    }
    values
}

fn meta_variable_spec_names(
    engine: &Engine,
    interner: &Interner,
    specs: &[tnk_core::unify::problem::VarSpec],
) -> Vec<String> {
    specs
        .iter()
        .map(|spec| {
            format!(
                "{}:{}",
                interner.resolve_index(spec.name),
                engine.sorts().name(spec.sort)
            )
        })
        .collect()
}

fn meta_rule_variable_names(
    engine: &Engine,
    names: &[String],
    specs: &[tnk_core::unify::problem::VarSpec],
) -> Vec<String> {
    names
        .iter()
        .zip(specs)
        .map(|(name, spec)| {
            if name.contains(':') {
                name.clone()
            } else {
                format!("{name}:{}", engine.sorts().name(spec.sort))
            }
        })
        .collect()
}

/// Up-translate a solution substitution: each bound variable `'X:Sort` becomes
/// `'X:Sort <- up(value)`, joined by `_;_`; an all-ground match is the empty `none`. Full typed variable
/// names come from a `VarIndex` key or rule trace, and bindings with no value are omitted as unconstrained.
fn up_substitution(
    ctx: &mut MetaCtx,
    hooks: &MetaHooks,
    source: &BuiltModule,
    interner: &Interner,
    names: &[String],
    bindings: &[DagId],
) -> DagId {
    let qid = hooks.ops["qidSymbol"];
    let assign = hooks.ops["assignmentSymbol"];
    let mut assigns = Vec::new();
    for (k, name) in names.iter().enumerate() {
        let Some(&val) = bindings.get(k) else {
            continue;
        };
        let var_qid = ctx.make_na(qid, NaValue::Qid(name.as_str().into()));
        let up_val = up_parsed_term(ctx, hooks, source, interner, val);
        assigns.push(ctx.app(assign, vec![var_qid, up_val]));
    }
    match assigns.len() {
        0 => ctx.app(hooks.ops["emptySubstitutionSymbol"], vec![]),
        1 => assigns.into_iter().next().unwrap(),
        _ => ctx.app(hooks.ops["substitutionSymbol"], assigns),
    }
}

/// SMT-search substitutions contain only non-SMT variables from the target pattern. SMT target
/// variables are represented by equalities in the final constraint instead.
#[allow(clippy::too_many_arguments)]
fn up_smt_substitution(
    ctx: &mut MetaCtx,
    hooks: &MetaHooks,
    source: &BuiltModule,
    interner: &Interner,
    variables: &VarIndex,
    target_variable_count: u32,
    variable_names: &[String],
    bindings: &[DagId],
) -> DagId {
    let qid = hooks.ops["qidSymbol"];
    let assign = hooks.ops["assignmentSymbol"];
    let mut assigns = Vec::new();
    for slot in 0..target_variable_count {
        if source.engine.smt_type(variables.sort(slot)).is_some() {
            continue;
        }
        let Some(&value) = bindings.get(slot as usize) else {
            continue;
        };
        let variable = ctx.make_na(qid, NaValue::Qid(variables.name(slot).to_string().into()));
        let value = up_smt_term(ctx, hooks, source, interner, variable_names, value);
        assigns.push(ctx.app(assign, vec![variable, value]));
    }
    match assigns.len() {
        0 => ctx.app(hooks.ops["emptySubstitutionSymbol"], vec![]),
        1 => assigns.into_iter().next().unwrap(),
        _ => ctx.app(hooks.ops["substitutionSymbol"], assigns),
    }
}

/// The `VarIndex`'s variable names as the `&[String]` [`up_substitution`] expects.
fn var_names(vars: &VarIndex) -> Vec<String> {
    (0..vars.count())
        .map(|k| vars.name(k).to_string())
        .collect()
}

/// Down-translate a meta `UnificationProblem` (`_=?_` unificand pairs, optionally joined by the `_/\_`
/// conjunction) into kernel `(lhs, rhs)` [`Term`] pairs. `specs` is filled with each original variable's
/// `(name, sort)` in slot order; the returned `n_lhs` is the disjoint split point (lhs-side variables at
/// slots `0..n_lhs`, rhs-side at `n_lhs..`). A non-disjoint problem shares variables by name across the
/// two sides; a disjoint one gives the rhs its own slots (renamed apart) — its Terms' variable indices
/// shifted up by `n_lhs`.
fn meta_unification_roots(ctx: &MetaCtx, hooks: &MetaHooks, problem: DagId) -> Option<Vec<DagId>> {
    let conj = hooks.ops.get("unificationConjunctionSymbol").copied();
    let pair_sym = hooks.ops.get("unificandPairSymbol").copied();
    let pairs = if Some(ctx.top(problem)) == conj {
        ctx.children(problem)
    } else {
        vec![problem]
    };
    let mut roots = Vec::with_capacity(pairs.len() * 2);
    for pair in pairs {
        if Some(ctx.top(pair)) != pair_sym {
            return None;
        }
        let kids = ctx.children(pair);
        roots.push(*kids.first()?);
        roots.push(*kids.get(1)?);
    }
    Some(roots)
}

fn render_cached_meta_unifier(
    ctx: &mut MetaCtx,
    hooks: &MetaHooks,
    cache: &MetaUnifyCache,
    interner: &Interner,
    sol_nr: usize,
) -> Option<DagId> {
    let Some(bindings) = cache.unifiers.get(sol_nr) else {
        if !cache.exhausted {
            return None;
        }
        let hook = match (cache.key.disjoint, cache.incomplete) {
            (true, false) => "noUnifierTripleSymbol",
            (true, true) => "noUnifierIncompleteTripleSymbol",
            (false, false) => "noUnifierPairSymbol",
            (false, true) => "noUnifierIncompletePairSymbol",
        };
        return Some(ctx.app(*hooks.ops.get(hook)?, vec![]));
    };

    let mut bindings_original = bindings.clone();
    for (new_slot, &old_slot) in cache.original_order.iter().enumerate() {
        bindings_original[old_slot] = bindings[new_slot];
    }
    let third = ctx.make_na(
        hooks.ops["qidSymbol"],
        NaValue::Qid(cache.key.family_root.into()),
    );
    if cache.key.disjoint {
        let (lhs_b, rhs_b) = bindings_original.split_at(cache.n_lhs);
        let lhs_names: Vec<&str> = cache.specs_raw[..cache.n_lhs]
            .iter()
            .map(|(name, _)| name.as_str())
            .collect();
        let rhs_names: Vec<&str> = cache.specs_raw[cache.n_lhs..]
            .iter()
            .map(|(name, _)| name.as_str())
            .collect();
        let lhs =
            up_unifier_substitution(ctx, hooks, &cache.loaded.built, interner, &lhs_names, lhs_b);
        let rhs =
            up_unifier_substitution(ctx, hooks, &cache.loaded.built, interner, &rhs_names, rhs_b);
        Some(ctx.app(hooks.ops["unificationTripleSymbol"], vec![lhs, rhs, third]))
    } else {
        let names: Vec<&str> = cache
            .specs_raw
            .iter()
            .map(|(name, _)| name.as_str())
            .collect();
        let subst = up_unifier_substitution(
            ctx,
            hooks,
            &cache.loaded.built,
            interner,
            &names,
            &bindings_original,
        );
        Some(ctx.app(hooks.ops["matchPairSymbol"], vec![subst, third]))
    }
}

fn down_unification_problem(
    ctx: &MetaCtx,
    hooks: &MetaHooks,
    problem: DagId,
    target: &BuiltModule,
    specs: &mut Vec<(String, SortId)>,
    disjoint: bool,
) -> Option<(Vec<(Term, Term)>, usize)> {
    let conj = hooks.ops.get("unificationConjunctionSymbol").copied();
    let pair_sym = hooks.ops.get("unificandPairSymbol").copied();
    let pair_dags: Vec<DagId> = if Some(ctx.top(problem)) == conj {
        ctx.children(problem)
    } else {
        vec![problem]
    };

    let mut vars_l = VarIndex::new();
    let mut vars_r = VarIndex::new(); // disjoint only
    let mut lhs_terms = Vec::new();
    let mut rhs_terms = Vec::new();
    for pd in &pair_dags {
        if Some(ctx.top(*pd)) != pair_sym {
            return None;
        }
        let k = ctx.children(*pd);
        let l = down_term_to_term(ctx, hooks, *k.first()?, target, &mut vars_l)?;
        let r_vars = if disjoint { &mut vars_r } else { &mut vars_l };
        let r = down_term_to_term(ctx, hooks, *k.get(1)?, target, r_vars)?;
        lhs_terms.push(l);
        rhs_terms.push(r);
    }
    let n_lhs = vars_l.count() as usize;
    for k in 0..vars_l.count() {
        specs.push((vars_l.name(k).to_string(), vars_l.sort(k)));
    }
    let pairs = if disjoint {
        for k in 0..vars_r.count() {
            specs.push((vars_r.name(k).to_string(), vars_r.sort(k)));
        }
        lhs_terms
            .into_iter()
            .zip(rhs_terms)
            .map(|(l, r)| (l, shift_term_vars(&r, n_lhs as u32)))
            .collect()
    } else {
        lhs_terms.into_iter().zip(rhs_terms).collect()
    };
    Some((pairs, n_lhs))
}

/// A copy of `t` with every variable index shifted up by `offset` (re-slotting a disjoint unification
/// problem's rhs variables into their own range).
fn shift_term_vars(t: &Term, offset: u32) -> Term {
    match t {
        Term::Var(v) => Term::var(v.index + offset, v.sort),
        Term::Na { symbol, value } => Term::Na {
            symbol: *symbol,
            value: value.clone(),
        },
        Term::Op { symbol, args } => Term::op(
            *symbol,
            args.iter().map(|a| shift_term_vars(a, offset)).collect(),
        ),
        Term::Iter { symbol, count, arg } => {
            Term::iter(*symbol, count.clone(), shift_term_vars(arg, offset))
        }
    }
}

/// Up-translate a unifier's bindings into a meta `Substitution` (`'X:Sort <- up(value) ; …`), like
/// [`up_substitution`] but the values may contain fresh **variable** leaves (a unifier is not a ground
/// match), so it uses [`up_meta_term_sym`]. `names[k]` is the `k`-th variable's meta-Qid text.
fn up_unifier_substitution(
    ctx: &mut MetaCtx,
    hooks: &MetaHooks,
    source: &BuiltModule,
    interner: &Interner,
    names: &[&str],
    bindings: &[DagId],
) -> DagId {
    let qid = hooks.ops["qidSymbol"];
    let assign = hooks.ops["assignmentSymbol"];
    let mut assigns = Vec::new();
    for (k, name) in names.iter().enumerate() {
        let Some(&val) = bindings.get(k) else {
            continue;
        };
        let var_qid = ctx.make_na(qid, NaValue::Qid((*name).into()));
        let up_val = up_meta_term_sym(ctx, hooks, source, interner, val);
        assigns.push(ctx.app(assign, vec![var_qid, up_val]));
    }
    match assigns.len() {
        0 => ctx.app(hooks.ops["emptySubstitutionSymbol"], vec![]),
        1 => assigns.into_iter().next().unwrap(),
        _ => ctx.app(hooks.ops["substitutionSymbol"], assigns),
    }
}

/// [`up_term`] extended to render genuine variable leaves (`'name:Sort`, the name resolved through the
/// session `interner`) — the metaUnify result path, whose substitution values carry fresh variables.
fn up_meta_term_sym(
    ctx: &mut MetaCtx,
    hooks: &MetaHooks,
    source: &BuiltModule,
    interner: &Interner,
    t: DagId,
) -> DagId {
    let qid = hooks.ops["qidSymbol"];
    match source.engine.node(t).repr() {
        NodeRepr::Var { name } => {
            let bare = interner
                .resolve(Sym::from_raw(name & !0x4000_0000))
                .to_string();
            let sort = source.engine.sorts().name(source.engine.sort_of(t));
            ctx.make_na(qid, NaValue::Qid(format!("{bare}:{sort}").into()))
        }
        NodeRepr::App => {
            let sym = source.engine.node(t).symbol();
            let opname = meta_symbol_name(source, sym);
            let kids: Vec<DagId> = source.engine.node(t).children().collect();
            if kids.is_empty() {
                let sort = source.engine.sorts().name(source.engine.sort_of(t));
                ctx.make_na(qid, NaValue::Qid(format!("{opname}.{sort}").into()))
            } else {
                let up_args: Vec<DagId> = kids
                    .iter()
                    .map(|&c| up_meta_term_sym(ctx, hooks, source, interner, c))
                    .collect();
                let arglist = up_arglist(ctx, hooks, up_args);
                let opqid = ctx.make_na(qid, NaValue::Qid(opname.into()));
                ctx.app(hooks.ops["metaTermSymbol"], vec![opqid, arglist])
            }
        }
        NodeRepr::Iter { count, arg } => {
            let base = meta_symbol_name(source, source.engine.node(t).symbol());
            let head = if count == "1" {
                base
            } else {
                format!("{base}^{count}")
            };
            let up_arg = up_meta_term_sym(ctx, hooks, source, interner, arg);
            let opqid = ctx.make_na(qid, NaValue::Qid(head.into()));
            ctx.app(hooks.ops["metaTermSymbol"], vec![opqid, up_arg])
        }
        NodeRepr::SmtNum(number) => {
            let sort = source.engine.sort_of(t);
            let kind = source
                .engine
                .smt_type(sort)
                .expect("SMT number without sort metadata");
            let text = number.to_maude(kind);
            let sort = source.engine.sorts().name(sort);
            ctx.make_na(qid, NaValue::Qid(format!("{text}.{sort}").into()))
        }
        NodeRepr::Str(_) | NodeRepr::Qid(_) | NodeRepr::Float(_) => {
            let sort = source.engine.sorts().name(source.engine.sort_of(t));
            ctx.make_na(qid, NaValue::Qid(format!("?.{sort}").into()))
        }
    }
}

/// Up-translate `node` (in `source`) into a meta `Context` — its [`up_term`], except the subterm at `path`
/// becomes the hole `[]` (`holeSymbol`). Handles the free-theory application spine (the path component is a
/// child index); the rewritten/hole position itself is reached when `path` is exhausted.
fn up_context(
    ctx: &mut MetaCtx,
    hooks: &MetaHooks,
    source: &BuiltModule,
    interner: &Interner,
    node: DagId,
    path: &[usize],
) -> DagId {
    up_context_impl(ctx, hooks, source, interner, node, path, None, None)
}

/// As [`up_context`], but `matched` can be a proper associative portion of the node at `path`.
#[allow(clippy::too_many_arguments)]
fn up_context_with_portion(
    ctx: &mut MetaCtx,
    hooks: &MetaHooks,
    source: &BuiltModule,
    interner: &Interner,
    node: DagId,
    path: &[usize],
    matched: DagId,
    ordered: Option<(&[DagId], &[DagId])>,
) -> DagId {
    up_context_impl(
        ctx,
        hooks,
        source,
        interner,
        node,
        path,
        Some(matched),
        ordered,
    )
}

#[allow(clippy::too_many_arguments)]
fn up_context_impl(
    ctx: &mut MetaCtx,
    hooks: &MetaHooks,
    source: &BuiltModule,
    interner: &Interner,
    node: DagId,
    path: &[usize],
    matched: Option<DagId>,
    ordered: Option<(&[DagId], &[DagId])>,
) -> DagId {
    let Some((&head, rest)) = path.split_first() else {
        if let Some((prefix, suffix)) = ordered
            && (!prefix.is_empty() || !suffix.is_empty())
        {
            let symbol = source.engine.node(node).symbol();
            let mut args = Vec::with_capacity(prefix.len() + suffix.len() + 1);
            args.extend(
                prefix
                    .iter()
                    .map(|&part| up_parsed_term(ctx, hooks, source, interner, part)),
            );
            args.push(ctx.app(hooks.ops["holeSymbol"], vec![]));
            args.extend(
                suffix
                    .iter()
                    .map(|&part| up_parsed_term(ctx, hooks, source, interner, part)),
            );
            let arglist = up_arglist(ctx, hooks, args);
            let name = source.engine.symbol(symbol).name().to_string();
            let opqid = ctx.make_na(hooks.ops["qidSymbol"], NaValue::Qid(name.into()));
            return ctx.app(hooks.ops["metaTermSymbol"], vec![opqid, arglist]);
        }
        if let Some(matched) = matched
            && let Some(residue) = associative_residue(&source.engine, node, matched)
            && !residue.is_empty()
        {
            let symbol = source.engine.node(node).symbol();
            let mut args: Vec<DagId> = residue
                .into_iter()
                .map(|part| up_parsed_term(ctx, hooks, source, interner, part))
                .collect();
            args.push(ctx.app(hooks.ops["holeSymbol"], vec![]));
            let arglist = up_arglist(ctx, hooks, args);
            let name = source.engine.symbol(symbol).name().to_string();
            let opqid = ctx.make_na(hooks.ops["qidSymbol"], NaValue::Qid(name.into()));
            return ctx.app(hooks.ops["metaTermSymbol"], vec![opqid, arglist]);
        }
        return ctx.app(hooks.ops["holeSymbol"], vec![]);
    };
    let sym = source.engine.node(node).symbol();
    let name = source.engine.symbol(sym).name().to_string();
    let children: Vec<DagId> = source.engine.node(node).children().collect();
    let matched_whole_child =
        matched.is_none_or(|portion| source.engine.deep_equal(children[head], portion));
    let up_args: Vec<DagId> =
        if rest.is_empty() && source.engine.symbol_is_assoc(sym) && matched_whole_child {
            // AC/AU extension contexts place residue arguments before the final hole.
            let mut args: Vec<DagId> = children
                .iter()
                .enumerate()
                .filter(|&(i, _)| i != head)
                .map(|(_, &child)| up_parsed_term(ctx, hooks, source, interner, child))
                .collect();
            args.push(ctx.app(hooks.ops["holeSymbol"], vec![]));
            args
        } else {
            children
                .iter()
                .enumerate()
                .map(|(i, &child)| {
                    if i == head {
                        up_context_impl(ctx, hooks, source, interner, child, rest, matched, ordered)
                    } else {
                        up_parsed_term(ctx, hooks, source, interner, child)
                    }
                })
                .collect()
        };
    let arglist = up_arglist(ctx, hooks, up_args);
    let opqid = ctx.make_na(hooks.ops["qidSymbol"], NaValue::Qid(name.into()));
    ctx.app(hooks.ops["metaTermSymbol"], vec![opqid, arglist])
}

/// Up-translate a kernel [`Term`] (a rule side, with variables) into a meta-term — the inverse of
/// [`down_term_to_term`], used to show a rule in a `metaSearchPath` trace. A `Var` becomes `'name:Sort`
/// (its trace name's base + sort), a constant `'c.Sort` (the operator's range sort), an application
/// `'f[args]`. (Iter-chain collapse to `'s_^n[…]` and built-in literals are refinements the `up*` family /
/// `upModule` adds — a search trace's rules here are over the free/constant fragment.)
fn up_parsed_pattern(
    ctx: &mut MetaCtx,
    hooks: &MetaHooks,
    source: &BuiltModule,
    term: &Term,
    names: &[String],
) -> DagId {
    up_pattern_inner(ctx, hooks, source, term, names, false, false)
}

/// Up-translate a statement pattern after eager theory normalization: flatten AC/ACU arguments and order
/// variables by name-token code rather than parser position.
fn up_normalized_pattern(
    ctx: &mut MetaCtx,
    hooks: &MetaHooks,
    source: &mut BuiltModule,
    interner: &mut Interner,
    term: &Term,
    names: &[String],
) -> Result<DagId, ReducerFault> {
    let variable_codes: Vec<u32> = names
        .iter()
        .map(|name| {
            let base = name.split_once(':').map_or(name.as_str(), |(base, _)| base);
            interner.intern(base).index()
        })
        .collect();
    let normalized = source
        .engine
        .try_normalize_pattern_for_reflection(term, &variable_codes)?;
    Ok(up_term_inner(
        ctx,
        hooks,
        source,
        Some(interner),
        None,
        false,
        normalized,
    ))
}

fn up_pattern(
    ctx: &mut MetaCtx,
    hooks: &MetaHooks,
    source: &BuiltModule,
    term: &Term,
    names: &[String],
) -> DagId {
    up_pattern_inner(ctx, hooks, source, term, names, false, true)
}

fn up_pattern_inner(
    ctx: &mut MetaCtx,
    hooks: &MetaHooks,
    source: &BuiltModule,
    term: &Term,
    names: &[String],
    flatten_associative: bool,
    canonicalize_commutative: bool,
) -> DagId {
    let qid = hooks.ops["qidSymbol"];
    match term {
        Term::Var(v) => {
            let base = names
                .get(v.index as usize)
                .map_or("V", |s| s.split(':').next().unwrap_or(s));
            let sort = source.engine.sorts().name(v.sort);
            ctx.make_na(qid, NaValue::Qid(format!("{base}:{sort}").into()))
        }
        Term::Na { symbol, value } => {
            let rendered = match value {
                NaValue::Str(s) => render_string(s),
                NaValue::Qid(q) => format!("'{q}"),
                NaValue::Float(b) => render_float(f64::from_bits(*b)),
                NaValue::SmtNum(number) => {
                    let kind = source
                        .engine
                        .smt_type(source.syntax[symbol].range)
                        .expect("SMT number without sort metadata");
                    number.to_maude(kind)
                }
            };
            let sort = source.engine.term_sort(term);
            ctx.make_na(
                qid,
                NaValue::Qid(format!("{rendered}.{}", source.engine.sorts().name(sort)).into()),
            )
        }
        Term::Iter { symbol, count, arg } => {
            let base = meta_symbol_name(source, *symbol);
            let decimal = count.to_decimal();
            let head = if decimal == "1" {
                base
            } else {
                format!("{base}^{decimal}")
            };
            let up_inner = up_pattern_inner(
                ctx,
                hooks,
                source,
                arg,
                names,
                flatten_associative,
                canonicalize_commutative,
            );
            let opqid = ctx.make_na(qid, NaValue::Qid(head.into()));
            ctx.app(hooks.ops["metaTermSymbol"], vec![opqid, up_inner])
        }
        Term::Op { symbol, args } if args.is_empty() => {
            let name = meta_symbol_name(source, *symbol);
            let sort = source.engine.term_sort(term);
            ctx.make_na(
                qid,
                NaValue::Qid(format!("{name}.{}", source.engine.sorts().name(sort)).into()),
            )
        }
        // Iter-chain collapse: a successor chain `s(s(…x))` stored as nested unary `iter` operations prints
        // as `'s_^n[up(x)]`, the compact representation also used for DAG iteration nodes.
        Term::Op { symbol, args } if Some(*symbol) == source.nat_succ && args.len() == 1 => {
            let mut count = 1u64;
            let mut inner = &args[0];
            while let Term::Op {
                symbol: s2,
                args: a2,
            } = inner
            {
                if Some(*s2) == source.nat_succ && a2.len() == 1 {
                    count += 1;
                    inner = &a2[0];
                } else {
                    break;
                }
            }
            let base = meta_symbol_name(source, *symbol);
            let head = if count == 1 {
                base
            } else {
                format!("{base}^{count}")
            };
            let up_inner = up_pattern_inner(
                ctx,
                hooks,
                source,
                inner,
                names,
                flatten_associative,
                canonicalize_commutative,
            );
            let opqid = ctx.make_na(qid, NaValue::Qid(head.into()));
            ctx.app(hooks.ops["metaTermSymbol"], vec![opqid, up_inner])
        }
        Term::Op { symbol, args } => {
            let name = meta_symbol_name(source, *symbol);
            // Flatten nested associative patterns into the meta form. Preserve source order unless
            // commutative canonicalization is explicitly requested; added attribute sets are ordered when
            // constructed.
            let mut flat: Vec<&Term> = Vec::new();
            if flatten_associative && source.engine.symbol_is_assoc(*symbol) {
                flatten_assoc_args(*symbol, args, &mut flat);
            } else {
                flat.extend(args.iter());
            }
            if canonicalize_commutative && source.engine.symbol_is_commutative(*symbol) {
                // Order immediate static AC/C arguments by arity. Preserve source order for equal arities,
                // whose variable tie-break follows token encounter order.
                flat.sort_by_key(|term| match term {
                    Term::Var(_) | Term::Na { .. } => 0,
                    Term::Iter { .. } => 1,
                    Term::Op { symbol, .. } => source.engine.symbol(*symbol).arity(),
                });
            }
            let up_args: Vec<DagId> = flat
                .iter()
                .map(|a| {
                    up_pattern_inner(
                        ctx,
                        hooks,
                        source,
                        a,
                        names,
                        flatten_associative,
                        canonicalize_commutative,
                    )
                })
                .collect();
            let arglist = up_arglist(ctx, hooks, up_args);
            let opqid = ctx.make_na(qid, NaValue::Qid(name.into()));
            ctx.app(hooks.ops["metaTermSymbol"], vec![opqid, arglist])
        }
    }
}

/// Flatten nested same-symbol associative applications into one argument sequence.
fn flatten_assoc_args<'t>(symbol: SymbolId, args: &'t [Term], out: &mut Vec<&'t Term>) {
    for a in args {
        match a {
            Term::Op {
                symbol: s2,
                args: a2,
            } if *s2 == symbol => flatten_assoc_args(symbol, a2, out),
            _ => out.push(a),
        }
    }
}

/// Up-translate a rule trace to `rl` or `crl`, preserving its condition and its `narrowing`, `nonexec`,
/// and optional `label(Q)` attributes.
fn up_rule(
    ctx: &mut MetaCtx,
    hooks: &MetaHooks,
    source: &BuiltModule,
    trace: &RlTrace,
) -> Option<DagId> {
    // Rule traces retain binary associative parse trees. Flatten those spines before reflection so RuleSet
    // order and conditional-rule scheduling use normalized patterns.
    let up_lhs = up_pattern_inner(ctx, hooks, source, &trace.lhs, &trace.var_names, true, true);
    let up_rhs = up_pattern_inner(ctx, hooks, source, &trace.rhs, &trace.var_names, true, true);
    let attrs = stmt_attr_set(
        ctx,
        hooks,
        false,
        false,
        trace.narrowing,
        trace.nonexec,
        trace.label.as_deref(),
    );
    Some(if trace.condition.is_empty() {
        ctx.app(hooks.ops["rlSymbol"], vec![up_lhs, up_rhs, attrs])
    } else {
        let cond = up_condition(ctx, hooks, source, &trace.condition, &trace.var_names);
        ctx.app(hooks.ops["crlSymbol"], vec![up_lhs, up_rhs, cond, attrs])
    })
}

/// Collect the subterm positions of `node` whose depth is in `[min_d, max_d]`, as child-index paths in
/// outermost-first (pre-order) order — `metaXapply`'s application-position enumeration.
fn collect_positions(
    engine: &Engine,
    node: DagId,
    depth: usize,
    path: &mut Vec<usize>,
    min_d: usize,
    max_d: Option<u64>,
    out: &mut Vec<Vec<usize>>,
) {
    if max_d.is_some_and(|m| depth as u64 > m) {
        return;
    }
    if depth >= min_d {
        out.push(path.clone());
    }
    let children: Vec<DagId> = engine.node(node).children().collect();
    for (i, &c) in children.iter().enumerate() {
        path.push(i);
        collect_positions(engine, c, depth + 1, path, min_d, max_d, out);
        path.pop();
    }
}

/// The subterm of `root` at child-index `path`.
fn subterm_at(engine: &Engine, root: DagId, path: &[usize]) -> DagId {
    let mut node = root;
    for &i in path {
        node = engine
            .node(node)
            .children()
            .nth(i)
            .expect("valid position path");
    }
    node
}

/// `root` with the subterm at child-index `path` replaced by `new` (rebuilding the spine, theory-aware).
fn replace_at(engine: &mut Engine, root: DagId, path: &[usize], new: DagId) -> DagId {
    let Some((&head, rest)) = path.split_first() else {
        return new;
    };
    let sym = engine.node(root).symbol();
    let mut children: Vec<DagId> = engine.node(root).children().collect();
    children[head] = replace_at(engine, children[head], rest, new);
    engine.make_node(sym, children)
}

/// Remove one associative matched portion from `whole`, preserving every unmatched argument.
/// `children()` expands ACU multiplicities, so repeated elements are removed one occurrence at a time.
fn associative_residue(engine: &Engine, whole: DagId, matched: DagId) -> Option<Vec<DagId>> {
    if engine.deep_equal(whole, matched) {
        return Some(Vec::new());
    }
    let symbol = engine.node(whole).symbol();
    if !engine.symbol_is_assoc(symbol) {
        return None;
    }
    let matched_parts: Vec<DagId> = if engine.node(matched).symbol() == symbol {
        engine.node(matched).children().collect()
    } else {
        vec![matched]
    };
    let mut residue: Vec<DagId> = engine.node(whole).children().collect();
    for part in matched_parts {
        let position = residue
            .iter()
            .position(|&candidate| engine.deep_equal(candidate, part))?;
        residue.remove(position);
    }
    Some(residue)
}

/// Replace an associative extension match while retaining its residue. A whole match is the ordinary
/// replacement; a proper AC/AU match rebuilds `residue ⊕ replacement` through the theory-aware funnel.
fn replace_matched_portion(
    engine: &mut Engine,
    whole: DagId,
    matched: DagId,
    replacement: DagId,
) -> DagId {
    let symbol = engine.node(whole).symbol();
    match associative_residue(engine, whole, matched) {
        Some(residue) if residue.is_empty() => replacement,
        Some(mut residue) => {
            residue.push(replacement);
            engine.make_node(symbol, residue)
        }
        None => replacement,
    }
}

// ---- meta argument decoders (Bound / Nat / search arrow / empty condition) ----

/// A meta `Bound` (`unbounded` | a `Nat`) → the engine driver bound (`None` = unbounded, `Some(n)` = ≤ n).
fn down_bound(ctx: &MetaCtx, hooks: &MetaHooks, d: DagId) -> Option<u64> {
    if Some(ctx.top(d)) == hooks.ops.get("unboundedSymbol").copied() {
        return None;
    }
    down_nat64(ctx, d)
}

/// A meta `Nat` (`'0.Zero`, `'s_^n['0.Zero]`, or a NAT numeral) → its `u64` value.
fn down_nat64(ctx: &MetaCtx, d: DagId) -> Option<u64> {
    match ctx.repr(d) {
        NodeRepr::Iter { count, .. } => count.parse().ok(),
        _ => Some(0), // the zero constant
    }
}

/// A meta `Nat` as its decimal string (`s_^count(0)` → `count`; the zero constant → `"0"`) — for the
/// unbounded (bignum) `metaUnify` base index, which need not fit `u64`.
fn down_nat_decimal(ctx: &MetaCtx, d: DagId) -> Option<String> {
    match ctx.repr(d) {
        NodeRepr::Iter { count, .. } => {
            let c = count.to_string();
            c.bytes().all(|b| b.is_ascii_digit()).then_some(c)
        }
        _ => Some("0".to_string()), // the zero constant
    }
}

/// A meta search-type `Qid` (`'*`/`'+`/`'!`/`'1`) → the reachability [`Arrow`].
fn down_arrow(ctx: &MetaCtx, d: DagId) -> Option<Arrow> {
    match ctx.repr(d) {
        NodeRepr::Qid("*") => Some(Arrow::Star),
        NodeRepr::Qid("+") => Some(Arrow::Plus),
        NodeRepr::Qid("!") => Some(Arrow::Bang),
        NodeRepr::Qid("1") => Some(Arrow::One),
        _ => None,
    }
}

/// Whether a meta `Condition` is the empty `nil` (the only condition the matching descent handles so far).
fn is_nil_condition(ctx: &MetaCtx, hooks: &MetaHooks, d: DagId) -> bool {
    Some(ctx.top(d)) == hooks.ops.get("noConditionSymbol").copied()
}

/// Down-translate a META partial substitution, preserving strict reducer faults raised while a value
/// materializes a theory identity.
fn try_down_partial_substitution(
    ctx: &MetaCtx,
    hooks: &MetaHooks,
    module: &mut BuiltModule,
    d: DagId,
    interner: &mut Interner,
) -> Result<Option<HashMap<String, DagId>>, ReducerFault> {
    let empty = hooks.ops.get("emptySubstitutionSymbol").copied();
    let join = hooks.ops.get("substitutionSymbol").copied();
    let Some(assign) = hooks.ops.get("assignmentSymbol").copied() else {
        return Ok(None);
    };
    let mut bindings = HashMap::new();
    for assignment in flatten_set(ctx, d, empty, join) {
        if ctx.top(assignment) != assign {
            return Ok(None);
        }
        let kids = ctx.children(assignment);
        if kids.len() != 2 {
            return Ok(None);
        }
        let Some(name) = qid_text(ctx, kids[0]) else {
            return Ok(None);
        };
        let Some(value) = try_down_term(ctx, hooks, kids[1], module, interner)? else {
            return Ok(None);
        };
        if bindings.insert(name, value).is_some() {
            return Ok(None);
        }
    }
    Ok(Some(bindings))
}

/// Align a name-keyed partial substitution with one compiled rule's dense variable slots.
/// A labelled overload that does not declare every supplied variable is not a candidate.
fn rule_initial_bindings(
    names: &[String],
    partial: &HashMap<String, DagId>,
) -> Option<Vec<Option<DagId>>> {
    let mut initial = vec![None; names.len()];
    for (name, &value) in partial {
        let slot = names.iter().position(|candidate| candidate == name)?;
        initial[slot] = Some(value);
    }
    Some(initial)
}

/// The `(n+1)`-th match solution's bindings (`0..nr`) of `pattern` against `subj`, or `None` if there are
/// fewer than `n+1`. `extension` allows the pattern to match a sub-part (`xmatch`).
fn nth_match(
    engine: &mut Engine,
    pattern: Term,
    nr: u32,
    subj: DagId,
    extension: bool,
    n: usize,
) -> Option<Vec<DagId>> {
    let mut sols = engine.match_solutions(pattern, nr, subj, extension);
    let mut count = 0;
    while sols.advance() {
        if count == n {
            return Some(
                (0..nr)
                    .map(|k| {
                        sols.binding(k)
                            .expect("the matcher binds every pattern variable")
                    })
                    .collect(),
            );
        }
        count += 1;
    }
    None
}

fn variant_family_root(family: tnk_core::fresh::VariableFamily) -> &'static str {
    match family {
        tnk_core::fresh::VariableFamily::Unify => "#",
        tnk_core::fresh::VariableFamily::Variant => "%",
        tnk_core::fresh::VariableFamily::Narrow => "@",
    }
}

fn down_strat_decls(
    ctx: &MetaCtx,
    hooks: &MetaHooks,
    declarations: DagId,
) -> Option<Vec<StratDecl>> {
    let elements = flatten_set(
        ctx,
        declarations,
        hooks.ops.get("emptyStratDeclSetSymbol").copied(),
        hooks.ops.get("stratDeclSetSymbol").copied(),
    );
    let mut result = Vec::with_capacity(elements.len());
    for element in elements {
        if Some(ctx.top(element)) != hooks.ops.get("stratDeclSymbol").copied() {
            return None;
        }
        let kids = ctx.children(element);
        if kids.len() != 4 {
            return None;
        }
        result.push(StratDecl {
            name: qid_text(ctx, kids[0])?,
            domain: down_typelist(ctx, hooks, kids[1]),
            subject: qid_text(ctx, kids[2])?,
            origin: None,
            source_index: None,
            home: None,
        });
    }
    Some(result)
}

fn try_down_strat_defs(
    ctx: &MetaCtx,
    hooks: &MetaHooks,
    definitions: DagId,
    module: &mut BuiltModule,
    interner: &mut Interner,
) -> Result<Option<Vec<StratDef>>, ReducerFault> {
    let elements = flatten_set(
        ctx,
        definitions,
        hooks.ops.get("emptyStratDefSetSymbol").copied(),
        hooks.ops.get("stratDefSetSymbol").copied(),
    );
    let mut result = Vec::with_capacity(elements.len());
    for element in elements {
        let top = ctx.top(element);
        let is_sd = Some(top) == hooks.ops.get("sdSymbol").copied();
        let is_csd = Some(top) == hooks.ops.get("csdSymbol").copied();
        let kids = ctx.children(element);
        if (!is_sd && !is_csd) || kids.len() != if is_sd { 3 } else { 4 } {
            return Ok(None);
        }
        let call = kids[0];
        if Some(ctx.top(call)) != hooks.ops.get("callStratSymbol").copied() {
            return Ok(None);
        }
        let call_kids = ctx.children(call);
        if call_kids.len() != 2 {
            return Ok(None);
        }
        let mut vars = VarIndex::new();
        let Some(param_roots) = down_term_list_roots(ctx, hooks, call_kids[1]) else {
            return Ok(None);
        };
        let Some(params) = param_roots
            .into_iter()
            .map(|term| down_term_to_term(ctx, hooks, term, module, &mut vars))
            .collect::<Option<Vec<_>>>()
        else {
            return Ok(None);
        };
        let mut bound: BTreeSet<u32> = (0..vars.count()).collect();
        let condition = if is_csd {
            let Some(condition) =
                down_condition(ctx, hooks, kids[2], module, &mut vars, &mut bound)
            else {
                return Ok(None);
            };
            Some(condition)
        } else {
            None
        };
        let names = typed_source_var_names(module, &vars);
        let params = params
            .iter()
            .map(|term| source_term_tokens(module, interner, term, &names))
            .collect();
        let condition = condition
            .as_deref()
            .map(|condition| source_condition_tokens(module, interner, condition, &names));
        let Some(body) = try_down_strategy(ctx, hooks, kids[1], module, interner)? else {
            return Ok(None);
        };
        let Some(name) = qid_text(ctx, call_kids[0]) else {
            return Ok(None);
        };
        result.push(StratDef {
            name,
            params,
            body,
            cond: condition,
            origin: None,
            source_index: None,
            home: None,
        });
    }
    Ok(Some(result))
}

/// Down-translate the constructor subset used by META-INTERPRETER's `srewriteTerm`, preserving strict
/// reducer faults raised while named-call arguments materialize theory identities.
fn try_down_strategy(
    ctx: &MetaCtx,
    hooks: &MetaHooks,
    dag: DagId,
    module: &mut BuiltModule,
    interner: &mut Interner,
) -> Result<Option<StratExpr>, ReducerFault> {
    let top = ctx.top(dag);
    let kids = ctx.children(dag);
    let is = |hook: &str| Some(top) == hooks.ops.get(hook).copied();
    if is("failStratSymbol") {
        return Ok(Some(StratExpr::Fail));
    }
    if is("idleStratSymbol") {
        return Ok(Some(StratExpr::Idle));
    }
    if is("allStratSymbol") {
        return Ok(Some(StratExpr::All));
    }
    if is("applicationStratSymbol") {
        if kids.len() != 3 {
            return Ok(None);
        }
        let substitutions = flatten_set(
            ctx,
            kids[1],
            hooks.ops.get("emptySubstitutionSymbol").copied(),
            hooks.ops.get("substitutionSymbol").copied(),
        );
        if !substitutions.is_empty() {
            return Ok(None);
        }
        let children = flatten_set(
            ctx,
            kids[2],
            hooks.ops.get("emptyStratListSymbol").copied(),
            hooks.ops.get("stratListSymbol").copied(),
        );
        let mut substrats = Vec::with_capacity(children.len());
        for child in children {
            let Some(strategy) = try_down_strategy(ctx, hooks, child, module, interner)? else {
                return Ok(None);
            };
            substrats.push(strategy);
        }
        let Some(label) = qid_text(ctx, kids[0]) else {
            return Ok(None);
        };
        return Ok(Some(StratExpr::Apply {
            label,
            subst: Vec::new(),
            substrats,
        }));
    }
    if is("callStratSymbol") {
        if kids.len() != 2 {
            return Ok(None);
        }
        let Some(roots) = down_term_list_roots(ctx, hooks, kids[1]) else {
            return Ok(None);
        };
        let mut args = Vec::with_capacity(roots.len());
        for root in roots {
            let Some(term) = try_down_term(ctx, hooks, root, module, interner)? else {
                return Ok(None);
            };
            let text = print_raw(module, interner, term);
            args.push(tokenize(&text, interner));
        }
        let Some(name) = qid_text(ctx, kids[0]) else {
            return Ok(None);
        };
        return Ok(Some(StratExpr::Call { name, args }));
    }
    if is("topStratSymbol")
        || is("oneStratSymbol")
        || is("starStratSymbol")
        || is("plusStratSymbol")
        || is("normalizationStratSymbol")
        || is("notStratSymbol")
        || is("testStratSymbol")
        || is("tryStratSymbol")
    {
        let Some(&kid) = kids.first() else {
            return Ok(None);
        };
        let Some(child) = try_down_strategy(ctx, hooks, kid, module, interner)? else {
            return Ok(None);
        };
        let child = Box::new(child);
        return Ok(Some(if is("topStratSymbol") {
            StratExpr::Top(child)
        } else if is("oneStratSymbol") {
            StratExpr::One(child)
        } else if is("starStratSymbol") {
            StratExpr::Star(child)
        } else if is("plusStratSymbol") {
            StratExpr::Plus(child)
        } else if is("normalizationStratSymbol") {
            StratExpr::Normalize(child)
        } else {
            let kind = if is("notStratSymbol") {
                StratSugar::NotS
            } else if is("testStratSymbol") {
                StratSugar::TestS
            } else {
                StratSugar::Try
            };
            StratExpr::Sugar {
                kind,
                args: vec![*child],
            }
        }));
    }
    if is("conditionalStratSymbol") {
        if kids.len() != 3 {
            return Ok(None);
        }
        let Some(test) = try_down_strategy(ctx, hooks, kids[0], module, interner)? else {
            return Ok(None);
        };
        let Some(success) = try_down_strategy(ctx, hooks, kids[1], module, interner)? else {
            return Ok(None);
        };
        let Some(failure) = try_down_strategy(ctx, hooks, kids[2], module, interner)? else {
            return Ok(None);
        };
        return Ok(Some(StratExpr::Branch {
            test: Box::new(test),
            success: Box::new(success),
            failure: Box::new(failure),
        }));
    }
    if is("orelseStratSymbol") {
        if kids.len() != 2 {
            return Ok(None);
        }
        let mut args = Vec::with_capacity(kids.len());
        for child in kids {
            let Some(strategy) = try_down_strategy(ctx, hooks, child, module, interner)? else {
                return Ok(None);
            };
            args.push(strategy);
        }
        return Ok(Some(StratExpr::Sugar {
            kind: StratSugar::OrElse,
            args,
        }));
    }
    if is("unionStratSymbol") || is("concatStratSymbol") {
        let union = is("unionStratSymbol");
        let mut children = kids.into_iter();
        let Some(first) = children.next() else {
            return Ok(None);
        };
        let Some(mut expression) = try_down_strategy(ctx, hooks, first, module, interner)? else {
            return Ok(None);
        };
        for child in children {
            let Some(right) = try_down_strategy(ctx, hooks, child, module, interner)? else {
                return Ok(None);
            };
            expression = if union {
                StratExpr::Union(Box::new(expression), Box::new(right))
            } else {
                StratExpr::Seq(Box::new(expression), Box::new(right))
            };
        }
        return Ok(Some(expression));
    }
    Ok(None)
}

fn down_variant_options(ctx: &MetaCtx, options: DagId) -> (bool, bool) {
    let mut filtered = false;
    let mut delayed = false;
    let mut work = vec![options];
    while let Some(option) = work.pop() {
        match ctx.name(ctx.top(option)) {
            "filter" => filtered = true,
            "delay" => delayed = true,
            _ => work.extend(ctx.children(option)),
        }
    }
    (filtered, delayed)
}

/// Flatten a META-LEVEL `TermList`; a bare `Term` represents a singleton list.
fn down_term_list_roots(ctx: &MetaCtx, hooks: &MetaHooks, list: DagId) -> Option<Vec<DagId>> {
    let top = ctx.top(list);
    let children = ctx.children(list);
    if (Some(top) == hooks.ops.get("emptyTermListSymbol").copied()
        || (ctx.name(top) == "empty" && children.is_empty()))
        && !matches!(ctx.repr(list), NodeRepr::Qid(_))
    {
        Some(Vec::new())
    } else if Some(top) == hooks.ops.get("termListSymbol").copied()
        || Some(top) == hooks.ops.get("metaArgSymbol").copied()
        || ctx.name(top) == "_,_"
    {
        Some(children)
    } else {
        Some(vec![list])
    }
}

fn up_nat_exact(ctx: &mut MetaCtx, count: u64) -> Option<DagId> {
    let succ = ctx.resolve_iter("s_")?;
    let zero = ctx.iter_zero(succ)?;
    if count == 0 {
        Some(zero)
    } else {
        Some(ctx.make_iter(succ, count, zero))
    }
}

fn up_nat_big_exact(ctx: &mut MetaCtx, count: &str) -> Option<DagId> {
    let succ = ctx.resolve_iter("s_")?;
    let zero = ctx.iter_zero(succ)?;
    if count == "0" {
        Some(zero)
    } else {
        ctx.make_iter_decimal(succ, count, zero)
    }
}

/// Nat-family variant results carry the greatest fresh-variable index rather than a family Qid.
fn nat_family_variant_next_index(
    ctx: &mut MetaCtx,
    engine: &Engine,
    interner: &Interner,
    variant: &tnk_core::variant::VariantResult,
    base: &str,
) -> Option<DagId> {
    let mut greatest = base.trim_start_matches('0').to_string();
    if greatest.is_empty() {
        greatest.push('0');
    }
    let mut work = Vec::with_capacity(variant.substitution.len() + 1);
    work.push(variant.term);
    work.extend(variant.substitution.iter().copied());
    while let Some(dag) = work.pop() {
        let node = engine.node(dag);
        if let NodeRepr::Var { name } = node.repr() {
            let text = interner.resolve_index(name);
            if matches!(text.as_bytes().first(), Some(b'#' | b'%' | b'@')) {
                let digits = text[1..].trim_start_matches('0');
                let digits = if digits.is_empty() { "0" } else { digits };
                if digits.len() > greatest.len()
                    || (digits.len() == greatest.len() && digits > greatest.as_str())
                {
                    greatest = digits.to_string();
                }
            }
        }
        work.extend(node.children());
    }
    up_nat_big_exact(ctx, &greatest)
}

fn nat_family_unifier_next_index(
    ctx: &mut MetaCtx,
    engine: &Engine,
    interner: &Interner,
    bindings: &[DagId],
    base: &str,
) -> Option<DagId> {
    let mut greatest = base.trim_start_matches('0').to_string();
    if greatest.is_empty() {
        greatest.push('0');
    }
    let mut work = bindings.to_vec();
    while let Some(dag) = work.pop() {
        let node = engine.node(dag);
        if let NodeRepr::Var { name } = node.repr() {
            let text = interner.resolve_index(name);
            if matches!(text.as_bytes().first(), Some(b'#' | b'%' | b'@')) {
                let digits = text[1..].trim_start_matches('0');
                let digits = if digits.is_empty() { "0" } else { digits };
                if digits.len() > greatest.len()
                    || (digits.len() == greatest.len() && digits > greatest.as_str())
                {
                    greatest = digits.to_string();
                }
            }
        }
        work.extend(node.children());
    }
    up_nat_big_exact(ctx, &greatest)
}
