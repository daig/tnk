//! Variant-based narrowing: source-rule descriptors and the symbolic state graph.
//!
//! The frontend registers every unconditional `[narrowing]` rule here, including `[nonexec]`
//! rules that ordinary rewriting deliberately omits. Search owns DAG roots; the signature keeps only
//! static source terms and metadata.

use std::collections::{HashSet, VecDeque};
use std::fmt;

use crate::dag::{DagId, NodeTerm};
use crate::engine::{Engine, SemanticCheckpoint};
use crate::fresh::{FreshVariableGenerator, VariableFamily};
use crate::host::ReducerFault;
use crate::num::Nat;
use crate::root::RootGuard;
use crate::term::{ConditionFragment, Term, Var};
use crate::unify::problem::VarSpec;
use crate::unify::{
    UnifyEnv, instantiate, instantiate_preserving_representation,
    replace_and_instantiate_preserving_representation,
};
use crate::variant::{
    FilteredVariantUnifierStream, PreparedVariantNarrowingState, VariantMode,
    VariantNarrowingSource, VariantSearch, VariantSearchError, compile_variant_equation_for_build,
    prepare_variant_narrowing_state,
};

/// Construction failure for a narrowing search.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum NarrowSearchError {
    Invalid(String),
    Reducer(ReducerFault),
}

impl fmt::Display for NarrowSearchError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Invalid(message) => f.write_str(message),
            Self::Reducer(fault) => fault.fmt(f),
        }
    }
}

impl std::error::Error for NarrowSearchError {}

impl From<String> for NarrowSearchError {
    fn from(message: String) -> Self {
        Self::Invalid(message)
    }
}

impl From<&str> for NarrowSearchError {
    fn from(message: &str) -> Self {
        Self::Invalid(message.to_owned())
    }
}

impl From<VariantSearchError> for NarrowSearchError {
    fn from(error: VariantSearchError) -> Self {
        match error {
            VariantSearchError::Invalid(message) => Self::Invalid(message),
            VariantSearchError::Reducer(fault) => Self::Reducer(fault),
        }
    }
}

impl From<ReducerFault> for NarrowSearchError {
    fn from(fault: ReducerFault) -> Self {
        Self::Reducer(fault)
    }
}

impl From<NarrowSearchError> for String {
    fn from(error: NarrowSearchError) -> Self {
        error.to_string()
    }
}

/// One source rule eligible for variant-based narrowing, in flattened module order.
#[derive(Clone)]
pub struct NarrowingRule {
    pub id: u32,
    pub lhs: Term,
    pub rhs: Term,
    pub variables: Vec<VarSpec>,
    pub variable_names: Vec<String>,
    pub condition: Vec<ConditionFragment>,
    pub label: Option<String>,
    pub nonexec: bool,
    pub narrowing: bool,
}

impl VariantNarrowingSource for NarrowingRule {
    fn lhs(&self) -> &Term {
        &self.lhs
    }

    fn rhs(&self) -> &Term {
        &self.rhs
    }

    fn variables(&self) -> &[VarSpec] {
        &self.variables
    }
}

fn remap_term(term: &Term, slots: &[u32]) -> Term {
    match term {
        Term::Var(variable) => Term::Var(Var {
            index: slots[variable.index as usize],
            sort: variable.sort,
        }),
        Term::Op { symbol, args } => Term::Op {
            symbol: *symbol,
            args: args.iter().map(|arg| remap_term(arg, slots)).collect(),
        },
        Term::Iter { symbol, count, arg } => Term::Iter {
            symbol: *symbol,
            count: count.clone(),
            arg: Box::new(remap_term(arg, slots)),
        },
        Term::Na { symbol, value } => Term::Na {
            symbol: *symbol,
            value: value.clone(),
        },
    }
}

fn remap_condition(fragment: &ConditionFragment, slots: &[u32]) -> ConditionFragment {
    match fragment {
        ConditionFragment::Equality { lhs, rhs } => ConditionFragment::Equality {
            lhs: remap_term(lhs, slots),
            rhs: remap_term(rhs, slots),
        },
        ConditionFragment::SortTest { term, sort } => ConditionFragment::SortTest {
            term: remap_term(term, slots),
            sort: *sort,
        },
        ConditionFragment::Matching {
            pattern,
            subject,
            fresh_vars,
        } => ConditionFragment::Matching {
            pattern: remap_term(pattern, slots),
            subject: remap_term(subject, slots),
            fresh_vars: fresh_vars
                .iter()
                .map(|&slot| slots[slot as usize])
                .collect(),
        },
        ConditionFragment::Rewrite {
            lhs,
            pattern,
            fresh_vars,
        } => ConditionFragment::Rewrite {
            lhs: remap_term(lhs, slots),
            pattern: remap_term(pattern, slots),
            fresh_vars: fresh_vars
                .iter()
                .map(|&slot| slots[slot as usize])
                .collect(),
        },
    }
}

/// Normalize/index a narrowing rule with the same lhs-first layout used by variant equations.
#[allow(clippy::too_many_arguments)]
pub(crate) fn compile_narrowing_rule(
    e: &mut Engine,
    id: u32,
    lhs: Term,
    rhs: Term,
    variables: Vec<VarSpec>,
    variable_names: Vec<String>,
    condition: Vec<ConditionFragment>,
    label: Option<String>,
    nonexec: bool,
) -> NarrowingRule {
    let compiled = compile_variant_equation_for_build(e, id, &lhs, &rhs, variables.clone());
    let mut old_to_new = vec![0; variables.len()];
    let mut names = Vec::with_capacity(variables.len());
    for (new_slot, spec) in compiled.variables.iter().enumerate() {
        let old_slot = variables
            .iter()
            .position(|source| source.sort == spec.sort && source.name == spec.name)
            .expect("compiled narrowing variable came from source rule");
        old_to_new[old_slot] = new_slot as u32;
        names.push(variable_names[old_slot].clone());
    }
    NarrowingRule {
        id,
        lhs: compiled.lhs,
        rhs: compiled.rhs,
        variables: compiled.variables,
        variable_names: names,
        condition: condition
            .iter()
            .map(|fragment| remap_condition(fragment, &old_to_new))
            .collect(),
        label,
        nonexec,
        narrowing: true,
    }
}

struct PairUnifier {
    bindings: Vec<DagId>,
    family: VariableFamily,
}

/// One variant-unification search plus the shared optional minimal-unifier filter.
struct PairUnifierSearch {
    search: VariantSearch,
    equations: Vec<crate::variant::VariantEquation>,
    canonical_order: Vec<usize>,
    stream: FilteredVariantUnifierStream,
    filtered: bool,
    delayed: bool,
    prepared: bool,
    exhausted: bool,
}

impl PairUnifierSearch {
    #[allow(clippy::too_many_arguments)]
    fn new(
        env: &mut UnifyEnv,
        target: DagId,
        specs: Vec<VarSpec>,
        blockers: Vec<DagId>,
        equations: Vec<crate::variant::VariantEquation>,
        incoming_family: VariableFamily,
        base: &str,
        filtered: bool,
        delayed: bool,
    ) -> Result<Self, NarrowSearchError> {
        let mut search = VariantSearch::new(
            env,
            target,
            specs,
            blockers,
            equations.clone(),
            VariantMode::Incremental,
            Some(incoming_family),
            base,
        )?;
        search.enable_unification(env.e, 1);
        let canonical_order = search.original_variable_order().to_vec();
        Ok(Self {
            search,
            equations,
            canonical_order,
            stream: FilteredVariantUnifierStream::new(filtered),
            filtered,
            delayed,
            prepared: false,
            exhausted: false,
        })
    }

    fn advance(&mut self, env: &mut UnifyEnv) {
        if self.exhausted {
            return;
        }
        match self.search.try_find_next(env) {
            Ok(Some(result)) => {
                debug_assert!(result.unifier);
                let rewrites = env.e.rewrites();
                if let Err(fault) = self.stream.try_insert(
                    env,
                    result.substitution,
                    result.family,
                    rewrites,
                    &self.equations,
                ) {
                    env.e.defer_reducer_fault(fault);
                    self.exhausted = true;
                }
            }
            Ok(None) => self.exhausted = true,
            Err(fault) => {
                env.e.defer_reducer_fault(fault);
                self.exhausted = true;
            }
        }
    }

    fn prepare(&mut self, env: &mut UnifyEnv) {
        if self.prepared {
            return;
        }
        while !self.exhausted {
            self.advance(env);
        }
        self.stream.finish();
        self.prepared = true;
    }

    fn next(&mut self, env: &mut UnifyEnv) -> Option<PairUnifier> {
        if !self.filtered {
            let result = match self.search.try_find_next(env) {
                Ok(result) => result?,
                Err(fault) => {
                    env.e.defer_reducer_fault(fault);
                    return None;
                }
            };
            return Some(PairUnifier {
                bindings: result.substitution,
                family: result.family,
            });
        }
        if self.delayed {
            self.prepare(env);
        }
        loop {
            if let Some(index) = self.stream.pop_pending() {
                return Some(PairUnifier {
                    bindings: self.stream.bindings(index).to_vec(),
                    family: self.stream.family(index),
                });
            }
            if self.exhausted {
                return None;
            }
            self.advance(env);
        }
    }

    fn is_incomplete(&self) -> bool {
        self.search.is_incomplete() || self.stream.is_incomplete()
    }

    fn restore_input_order(&self, bindings: &[DagId]) -> Vec<DagId> {
        if bindings.is_empty() {
            return Vec::new();
        }
        let mut restored = vec![bindings[0]; bindings.len()];
        for (new_slot, &old_slot) in self.canonical_order.iter().enumerate() {
            restored[old_slot] = bindings[new_slot];
        }
        restored
    }
}

#[derive(Clone, Copy)]
enum PairBinding {
    Source(usize),
    State(usize),
}

struct RuleUnifier {
    source_bindings: Vec<DagId>,
    state_bindings: Vec<DagId>,
    family: VariableFamily,
    _roots: Vec<RootGuard>,
}

struct RuleVariantUnifierSearch {
    pair: PairUnifierSearch,
    pair_bindings: Vec<PairBinding>,
    source_specs: Vec<VarSpec>,
    state_specs: Vec<VarSpec>,
    base: String,
}

impl RuleVariantUnifierSearch {
    #[allow(clippy::too_many_arguments)]
    fn new(
        env: &mut UnifyEnv,
        state: &PreparedVariantNarrowingState,
        redex: DagId,
        rule: &NarrowingRule,
        blockers: &[DagId],
        equations: Vec<crate::variant::VariantEquation>,
        incoming_family: VariableFamily,
        base: &str,
        filtered: bool,
        delayed: bool,
    ) -> Result<Self, NarrowSearchError> {
        let source_slots = term_variable_slots(&rule.lhs);
        let state_slots = dag_variable_slots(env.e, redex);
        let mut source_map = vec![0; rule.variables.len()];
        let mut state_map = vec![0; state.variables.len()];
        let mut specs = Vec::with_capacity(source_slots.len() + state_slots.len());
        let mut pair_bindings = Vec::with_capacity(source_slots.len() + state_slots.len());
        for source_slot in source_slots {
            source_map[source_slot] = specs.len() as u32;
            specs.push(rule.variables[source_slot]);
            pair_bindings.push(PairBinding::Source(source_slot));
        }
        for &state_slot in &state_slots {
            state_map[state_slot] = specs.len() as u32;
            specs.push(state.variables[state_slot]);
            pair_bindings.push(PairBinding::State(state_slot));
        }
        let lhs = remap_term(&rule.lhs, &source_map);
        let range = env
            .e
            .sorts()
            .error_sort(env.e.sorts().kind_of(env.e.sort_of(redex)));
        let pair_symbol = env
            .e
            .add_op("$narrowing-unification-pair", vec![range, range], range);
        let variables: Vec<_> = specs
            .iter()
            .enumerate()
            .map(|(slot, spec)| env.e.make_var(spec.sort, spec.name, slot as u32))
            .collect();
        let lhs_target = env.e.instantiate_bindings(&lhs, &variables);
        let state_target = env.e.remap_variable_slots(redex, &state_map);
        let pair_target = env.e.make_node(pair_symbol, vec![lhs_target, state_target]);
        let mut blocker_map = state_map;
        let mut next_blocker_slot = specs.len() as u32;
        for (slot, mapped) in blocker_map.iter_mut().enumerate() {
            if !state_slots.contains(&slot) {
                *mapped = next_blocker_slot;
                next_blocker_slot += 1;
            }
        }
        let blockers = blockers
            .iter()
            .map(|&blocker| env.e.remap_variable_slots(blocker, &blocker_map))
            .collect();
        let pair = PairUnifierSearch::new(
            env,
            pair_target,
            specs,
            blockers,
            equations,
            incoming_family,
            base,
            filtered,
            delayed,
        )?;
        Ok(Self {
            pair,
            pair_bindings,
            source_specs: rule.variables.clone(),
            state_specs: state.variables.clone(),
            base: base.to_string(),
        })
    }

    fn next(&mut self, env: &mut UnifyEnv) -> Option<RuleUnifier> {
        let result = self.pair.next(env)?;
        let mut input_bindings = vec![None; self.pair_bindings.len()];
        for (new_slot, &old_slot) in self.pair.canonical_order.iter().enumerate() {
            input_bindings[old_slot] = Some(result.bindings[new_slot]);
        }
        let mut source_bindings = vec![None; self.source_specs.len()];
        let mut state_bindings = vec![None; self.state_specs.len()];
        for (binding, target) in input_bindings.into_iter().zip(&self.pair_bindings) {
            match *target {
                PairBinding::Source(slot) => source_bindings[slot] = binding,
                PairBinding::State(slot) => state_bindings[slot] = binding,
            }
        }

        let mut variable_keys = Vec::new();
        for &binding in &result.bindings {
            collect_variable_keys(env.e, binding, &mut variable_keys);
        }
        let mut next_fresh = variable_keys.len();
        let mut generator = FreshVariableGenerator::with_base(
            Nat::from_decimal(&self.base).unwrap_or_else(Nat::zero),
        );
        for (slot, binding) in source_bindings.iter_mut().enumerate() {
            if binding.is_none() {
                let spec = self.source_specs[slot];
                let name = env
                    .names
                    .code(generator.fresh_name(next_fresh, result.family));
                *binding = Some(env.e.make_var(spec.sort, name, next_fresh as u32));
                next_fresh += 1;
            }
        }
        for (slot, binding) in state_bindings.iter_mut().enumerate() {
            if binding.is_none() {
                let spec = self.state_specs[slot];
                let name = env
                    .names
                    .code(generator.fresh_name(next_fresh, result.family));
                *binding = Some(env.e.make_var(spec.sort, name, next_fresh as u32));
                next_fresh += 1;
            }
        }
        let source_bindings: Vec<_> = source_bindings
            .into_iter()
            .map(|binding| binding.expect("source binding"))
            .collect();
        let state_bindings: Vec<_> = state_bindings
            .into_iter()
            .map(|binding| binding.expect("state binding"))
            .collect();
        let roots = source_bindings
            .iter()
            .chain(&state_bindings)
            .map(|&dag| env.e.root(dag))
            .collect();
        Some(RuleUnifier {
            source_bindings,
            state_bindings,
            family: result.family,
            _roots: roots,
        })
    }

    fn is_incomplete(&self) -> bool {
        self.pair.is_incomplete()
    }
}

fn term_variable_slots(term: &Term) -> Vec<usize> {
    let mut result = Vec::new();
    let mut work = vec![term];
    while let Some(term) = work.pop() {
        match term {
            Term::Var(variable) => {
                let slot = variable.index as usize;
                if !result.contains(&slot) {
                    result.push(slot);
                }
            }
            Term::Op { args, .. } => work.extend(args.iter().rev()),
            Term::Iter { arg, .. } => work.push(arg),
            Term::Na { .. } => {}
        }
    }
    result
}

fn dag_variable_slots(e: &Engine, root: DagId) -> Vec<usize> {
    let mut result = Vec::new();
    let mut work = vec![root];
    while let Some(dag) = work.pop() {
        match &e.node(dag).term {
            NodeTerm::Var { index, .. } => {
                let slot = *index as usize;
                if !result.contains(&slot) {
                    result.push(slot);
                }
            }
            _ => {
                let children: Vec<_> = e.node(dag).children().collect();
                work.extend(children.into_iter().rev());
            }
        }
    }
    result
}

fn collect_variable_keys(e: &Engine, root: DagId, keys: &mut Vec<(u32, crate::sort::SortId)>) {
    let mut work = vec![root];
    while let Some(dag) = work.pop() {
        match &e.node(dag).term {
            NodeTerm::Var { name, .. } => {
                let key = (*name, e.sort_of(dag));
                if !keys.contains(&key) {
                    keys.push(key);
                }
            }
            _ => {
                let children: Vec<_> = e.node(dag).children().collect();
                work.extend(children.into_iter().rev());
            }
        }
    }
}

/// The non-frozen positions of `root`, breadth-first, as child-index paths with their subterms.
///
/// The copies of a repeated element of an associative-commutative node are one position. Equal
/// arguments of a free, associative, or non-commutative identity/idempotent operator are distinct
/// positions, even when they are one shared node (for example an instantiated `f(Y, Y)` or a ground
/// `f(g(a), g(a))`). When the two arguments of a commutative operator are one shared node, only the
/// first is narrowed: the second yields the same unifiers, and states equal to the first's modulo
/// commutativity. Separately built equal arguments of a commutative operator are both narrowed.
fn narrowing_positions(e: &Engine, root: DagId) -> Vec<(Vec<usize>, DagId)> {
    let mut result = Vec::new();
    let mut queue = VecDeque::from([(Vec::new(), root)]);
    while let Some((path, dag)) = queue.pop_front() {
        result.push((path.clone(), dag));
        let symbol = e.node(dag).symbol();
        let commutative_pair =
            matches!(e.node(dag).term, NodeTerm::Cui { .. }) && e.symbol(symbol).is_commutative();
        let mut previous = None;
        for (index, child) in e.redex_arguments(dag, |index| e.is_frozen_arg(symbol, index)) {
            if commutative_pair && previous == Some(child) {
                continue;
            }
            previous = Some(child);
            let mut child_path = path.clone();
            child_path.push(index);
            queue.push_back((child_path, child));
        }
    }
    result
}

fn apply_rule_unifier(
    e: &mut Engine,
    state: &PreparedVariantNarrowingState,
    path: &[usize],
    rule: &NarrowingRule,
    unifier: &RuleUnifier,
) -> PreparedVariantNarrowingState {
    let state_values: Vec<_> = unifier.state_bindings.iter().copied().map(Some).collect();
    let mut accumulated = Vec::with_capacity(state.substitution.len());
    for dag in state.substitution.iter().copied() {
        let dag = instantiate(e, &state_values, dag).unwrap_or(dag);
        let dag = e.normalize_for_unify_or_defer_fault(dag);
        accumulated.push(dag);
    }
    let replacement = e.instantiate_bindings(&rule.rhs, &unifier.source_bindings);
    let rebuilt = replace_and_instantiate_preserving_representation(
        e,
        state.term,
        path,
        replacement,
        &state_values,
    );
    e.count_narrowing_step();
    let reduced = e.reduce_or_defer_fault(rebuilt);
    prepare_variant_narrowing_state(e, reduced, &accumulated)
}

/// Search arrow selected by `=>1`, `=>+`, `=>*`, or `=>!`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NarrowSearchType {
    One,
    AtLeastOne,
    Any,
    NormalForm,
}

/// State-folding relation selected by `{fold}` or `{vfold}`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NarrowFold {
    None,
    Match,
    Variant,
}

#[derive(Debug, Clone)]
pub struct NarrowOptions {
    pub search_type: NarrowSearchType,
    pub max_depth: Option<usize>,
    pub filter: bool,
    pub delay: bool,
    pub fold: NarrowFold,
    pub keep_history: bool,
    pub keep_paths: bool,
    pub respect_frozen: bool,
}

impl Default for NarrowOptions {
    fn default() -> Self {
        Self {
            search_type: NarrowSearchType::Any,
            max_depth: None,
            filter: false,
            delay: false,
            fold: NarrowFold::None,
            keep_history: false,
            keep_paths: false,
            respect_frozen: true,
        }
    }
}

#[derive(Debug, Clone)]
pub enum FoldingEvent {
    Subsumed {
        state: usize,
        by: usize,
        ancestor: bool,
    },
    Evicted {
        state: usize,
        by: usize,
    },
}

pub struct NarrowingStepRecord {
    pub rule_id: u32,
    pub rule_index: usize,
    pub path: Vec<usize>,
    pub source_substitution: Vec<DagId>,
    pub state_unifier: Vec<DagId>,
    pub family: VariableFamily,
}

struct StoredNarrowingState {
    prepared: PreparedVariantNarrowingState,
    family: VariableFamily,
    parent: Option<usize>,
    depth: usize,
    root_index: usize,
    alive: bool,
    locked: bool,
    expanded: bool,
    has_successor: bool,
    step: Option<NarrowingStepRecord>,
    roots: Vec<RootGuard>,
}

impl StoredNarrowingState {
    fn new(
        e: &mut Engine,
        prepared: PreparedVariantNarrowingState,
        family: VariableFamily,
        parent: Option<usize>,
        depth: usize,
        root_index: usize,
        step: Option<NarrowingStepRecord>,
    ) -> Self {
        let roots = std::iter::once(prepared.term)
            .chain(prepared.substitution.iter().copied())
            .chain(
                step.iter()
                    .flat_map(|step| step.source_substitution.iter().chain(&step.state_unifier))
                    .copied(),
            )
            .map(|dag| e.root(dag))
            .collect();
        Self {
            prepared,
            family,
            parent,
            depth,
            root_index,
            alive: true,
            locked: false,
            expanded: false,
            has_successor: false,
            step,
            roots,
        }
    }

    fn release(&mut self) {
        self.alive = false;
        if !self.locked {
            self.roots.clear();
            self.prepared.substitution.clear();
            if let Some(step) = &mut self.step {
                step.source_substitution.clear();
                step.state_unifier.clear();
            }
        }
    }
}

struct PendingNarrowingStep {
    source_index: usize,
    path: Vec<usize>,
    unifier: RuleUnifier,
}

pub struct NarrowGoal {
    pub term: DagId,
    pub variables: Vec<VarSpec>,
    pub initial_variable_count: usize,
    _root: Option<RootGuard>,
}

impl NarrowGoal {
    pub fn new(
        e: &mut Engine,
        term: DagId,
        variables: Vec<VarSpec>,
        initial_variable_count: usize,
    ) -> Self {
        Self {
            term,
            variables,
            initial_variable_count,
            _root: Some(e.root(term)),
        }
    }
}

pub struct NarrowingSolution {
    pub state: usize,
    pub bindings: Vec<DagId>,
    pub variables: Vec<VarSpec>,
    pub family: VariableFamily,
}

struct ActiveGoalSearch {
    state: usize,
    variables: Vec<VarSpec>,
    search: PairUnifierSearch,
}

struct StateExpansion {
    state_index: usize,
    positions: Vec<(Vec<usize>, DagId)>,

    position_index: usize,
    rule_index: usize,
    current: Option<RuleVariantUnifierSearch>,
    incomplete: bool,
}

impl StateExpansion {
    fn new(e: &Engine, state_index: usize, state: &StoredNarrowingState) -> Self {
        Self {
            state_index,
            positions: narrowing_positions(e, state.prepared.term),
            position_index: 0,
            rule_index: 0,
            current: None,
            incomplete: false,
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn next(
        &mut self,
        env: &mut UnifyEnv,
        state: &StoredNarrowingState,
        rules: &[NarrowingRule],
        blockers: &[DagId],
        equations: &[crate::variant::VariantEquation],
        options: &NarrowOptions,
        base: &str,
    ) -> Result<Option<PendingNarrowingStep>, ReducerFault> {
        loop {
            if let Some(search) = &mut self.current {
                let unifier = search.next(env);
                env.e.check_deferred_reducer_fault()?;
                if let Some(unifier) = unifier {
                    return Ok(Some(PendingNarrowingStep {
                        source_index: self.rule_index - 1,
                        path: self.positions[self.position_index].0.clone(),
                        unifier,
                    }));
                }
                self.incomplete |= search.is_incomplete();
                self.current = None;
            }
            if self.position_index >= self.positions.len() {
                return Ok(None);
            }
            let redex = self.positions[self.position_index].1;
            if matches!(env.e.node(redex).term, NodeTerm::Var { .. }) {
                self.position_index += 1;
                self.rule_index = 0;
                continue;
            }
            let redex_kind = env.e.symbol_kind(env.e.node(redex).symbol());
            while self.rule_index < rules.len() {
                let index = self.rule_index;
                self.rule_index += 1;
                let rule = &rules[index];
                if !rule.narrowing || !rule.condition.is_empty() {
                    continue;
                }
                let lhs_kind = match &rule.lhs {
                    Term::Var(variable) => env.e.sorts().kind_of(variable.sort),
                    Term::Op { symbol, .. }
                    | Term::Iter { symbol, .. }
                    | Term::Na { symbol, .. } => env.e.symbol_kind(*symbol),
                };
                if lhs_kind != redex_kind {
                    continue;
                }
                match RuleVariantUnifierSearch::new(
                    env,
                    &state.prepared,
                    redex,
                    rule,
                    blockers,
                    equations.to_vec(),
                    state.family,
                    base,
                    options.filter,
                    options.delay,
                ) {
                    Ok(search) => {
                        self.current = Some(search);
                        break;
                    }
                    Err(NarrowSearchError::Invalid(_)) => continue,
                    Err(NarrowSearchError::Reducer(fault)) => return Err(fault),
                }
            }
            if self.current.is_some() {
                continue;
            }
            self.position_index += 1;
            self.rule_index = 0;
        }
    }
}

struct NarrowStateCheckpoint {
    alive: bool,
    locked: bool,
    expanded: bool,
    has_successor: bool,
    substitution: Vec<DagId>,
    step_values: Option<(Vec<DagId>, Vec<DagId>)>,
    roots: Vec<RootGuard>,
}

struct NarrowSearchCheckpoint {
    states_len: usize,
    states: Vec<NarrowStateCheckpoint>,
    expand_cursor: usize,
    untried_initials: std::ops::Range<usize>,
    exhausted: bool,
    incomplete: bool,
    states_expanded: usize,
    folding_events_len: usize,
}

/// Resumable breadth-first symbolic narrowing graph.
pub struct NarrowSearch {
    states: Vec<StoredNarrowingState>,
    rules: Vec<NarrowingRule>,
    equations: Vec<crate::variant::VariantEquation>,
    options: NarrowOptions,
    blockers: Vec<DagId>,
    _blocker_roots: Vec<RootGuard>,
    base: String,
    expansion: Option<StateExpansion>,
    expand_cursor: usize,
    untried_initials: std::ops::Range<usize>,
    exhausted: bool,
    incomplete: bool,
    states_expanded: usize,
    folding_events: Vec<FoldingEvent>,
    goal: Option<NarrowGoal>,
    goal_search: Option<ActiveGoalSearch>,
    fault: Option<ReducerFault>,
}

impl NarrowSearch {
    #[allow(clippy::too_many_arguments)]
    pub fn new(
        env: &mut UnifyEnv,
        initial: DagId,
        initial_variables: Vec<VarSpec>,
        rules: &[NarrowingRule],
        equations: Vec<crate::variant::VariantEquation>,
        base: &str,
        options: NarrowOptions,
    ) -> Result<Self, NarrowSearchError> {
        Self::new_many(
            env,
            vec![(initial, initial_variables)],
            rules,
            equations,
            base,
            options,
        )
    }

    /// Construct one graph from a disjunction of independently scoped initial states.
    ///
    /// Disjuncts may not share variables. Each is indexed and freshened independently, so every root
    /// restarts numbering above `base` and its accumulated substitution contains only that root's variables.
    #[allow(clippy::too_many_arguments)]
    pub fn new_many(
        env: &mut UnifyEnv,
        initials: Vec<(DagId, Vec<VarSpec>)>,
        rules: &[NarrowingRule],
        equations: Vec<crate::variant::VariantEquation>,
        base: &str,
        options: NarrowOptions,
    ) -> Result<Self, NarrowSearchError> {
        let checkpoint = env.e.semantic_checkpoint();
        let result = Self::new_many_inner(env, initials, rules, equations, base, options);
        if matches!(&result, Err(NarrowSearchError::Reducer(_))) {
            env.e.restore_semantic_checkpoint(checkpoint);
        }
        result
    }

    fn new_many_inner(
        env: &mut UnifyEnv,
        initials: Vec<(DagId, Vec<VarSpec>)>,
        rules: &[NarrowingRule],
        equations: Vec<crate::variant::VariantEquation>,
        base: &str,
        mut options: NarrowOptions,
    ) -> Result<Self, NarrowSearchError> {
        if initials.is_empty() {
            return Err("narrowing requires at least one initial state".into());
        }
        if options.search_type == NarrowSearchType::One {
            options.max_depth = Some(1);
        }
        let untried_initials = if options.search_type == NarrowSearchType::Any {
            0..initials.len()
        } else {
            0..0
        };
        let mut search = Self {
            states: Vec::with_capacity(initials.len()),
            rules: rules.to_vec(),
            equations,
            options,
            blockers: Vec::new(),
            _blocker_roots: Vec::new(),
            base: base.to_string(),
            expansion: None,
            expand_cursor: 0,
            untried_initials,
            exhausted: false,
            incomplete: false,
            states_expanded: 0,
            folding_events: Vec::new(),
            goal: None,
            goal_search: None,
            fault: None,
        };
        for (root_index, (initial, initial_variables)) in initials.into_iter().enumerate() {
            let mut generator = FreshVariableGenerator::with_base(
                Nat::from_decimal(base).unwrap_or_else(Nat::zero),
            );
            let mut renaming = Vec::with_capacity(initial_variables.len());
            for (slot, spec) in initial_variables.iter().enumerate() {
                let name = env
                    .names
                    .code(generator.fresh_name(slot, VariableFamily::Unify));
                renaming.push(env.e.make_var(spec.sort, name, slot as u32));
            }
            let renamed = if renaming.is_empty() {
                initial
            } else {
                instantiate(
                    env.e,
                    &renaming.iter().copied().map(Some).collect::<Vec<_>>(),
                    initial,
                )
                .unwrap_or(initial)
            };
            let reduced = env.e.reduce_or_defer_fault(renamed);
            env.e
                .check_deferred_reducer_fault()
                .map_err(NarrowSearchError::Reducer)?;
            let prepared = prepare_variant_narrowing_state(env.e, reduced, &renaming);
            let initial = StoredNarrowingState::new(
                env.e,
                prepared,
                VariableFamily::Unify,
                None,
                0,
                root_index,
                None,
            );
            search.insert_state(env, initial)?;
        }
        Ok(search)
    }

    /// Construct a single narrowing graph without renaming the incoming state variables.
    ///
    /// META-LEVEL callers use this path because their `family` argument names the protected
    /// variable family already present in the down-translated state. `blockers` are irreducibility
    /// constraints over the same original variable slots; each rule-unification search receives
    /// their image under the state's accumulated substitution.
    #[allow(clippy::too_many_arguments)]
    pub fn new_preserving(
        env: &mut UnifyEnv,
        initial: DagId,
        initial_variables: Vec<VarSpec>,
        family: VariableFamily,
        blockers: Vec<DagId>,
        rules: &[NarrowingRule],
        equations: Vec<crate::variant::VariantEquation>,
        base: &str,
        options: NarrowOptions,
    ) -> Result<Self, NarrowSearchError> {
        let checkpoint = env.e.semantic_checkpoint();
        let result = Self::new_preserving_inner(
            env,
            initial,
            initial_variables,
            family,
            blockers,
            rules,
            equations,
            base,
            options,
        );
        if matches!(&result, Err(NarrowSearchError::Reducer(_))) {
            env.e.restore_semantic_checkpoint(checkpoint);
        }
        result
    }

    #[allow(clippy::too_many_arguments)]
    fn new_preserving_inner(
        env: &mut UnifyEnv,
        initial: DagId,
        initial_variables: Vec<VarSpec>,
        family: VariableFamily,
        blockers: Vec<DagId>,
        rules: &[NarrowingRule],
        equations: Vec<crate::variant::VariantEquation>,
        base: &str,
        mut options: NarrowOptions,
    ) -> Result<Self, NarrowSearchError> {
        if options.search_type == NarrowSearchType::One {
            options.max_depth = Some(1);
        }
        let untried_initials = 0..usize::from(options.search_type == NarrowSearchType::Any);
        let blocker_roots = blockers.iter().map(|&dag| env.e.root(dag)).collect();
        let mut substitution = Vec::with_capacity(initial_variables.len());
        for (slot, spec) in initial_variables.iter().enumerate() {
            substitution.push(env.e.make_var(spec.sort, spec.name, slot as u32));
        }
        let reduced = env.e.reduce_or_defer_fault(initial);
        env.e
            .check_deferred_reducer_fault()
            .map_err(NarrowSearchError::Reducer)?;
        let prepared = prepare_variant_narrowing_state(env.e, reduced, &substitution);
        let initial = StoredNarrowingState::new(env.e, prepared, family, None, 0, 0, None);
        let mut search = Self {
            states: Vec::with_capacity(1),
            rules: rules.to_vec(),
            blockers,
            _blocker_roots: blocker_roots,
            equations,
            options,
            base: base.to_string(),
            expansion: None,
            expand_cursor: 0,
            untried_initials,
            exhausted: false,
            incomplete: false,
            states_expanded: 0,
            folding_events: Vec::new(),
            goal: None,
            goal_search: None,
            fault: None,
        };
        search.insert_state(env, initial)?;
        Ok(search)
    }

    pub fn set_goal(&mut self, goal: NarrowGoal) {
        self.goal = Some(goal);
        self.goal_search = None;
    }

    /// Return the next solution, advancing the narrowing graph as needed.
    ///
    /// # Panics
    ///
    /// Panics if a configured strict reducer reports a [`ReducerFault`]. Use
    /// [`try_find_next`](Self::try_find_next) to preserve the fault.
    pub fn find_next(&mut self, env: &mut UnifyEnv) -> Option<NarrowingSolution> {
        self.try_find_next(env)
            .unwrap_or_else(|fault| panic!("{fault}"))
    }

    pub fn try_find_next(
        &mut self,
        env: &mut UnifyEnv,
    ) -> Result<Option<NarrowingSolution>, ReducerFault> {
        if let Some(fault) = &self.fault {
            return Err(fault.clone());
        }
        let search_checkpoint = self.state_checkpoint(env.e);
        let checkpoint = env.e.semantic_checkpoint();
        if let Err(fault) = env.e.check_deferred_reducer_fault() {
            return self.poison(env.e, checkpoint, search_checkpoint, fault);
        }
        let result = self.find_next_deferred(env);
        match env.e.check_deferred_reducer_fault() {
            Ok(()) => Ok(result),
            Err(fault) => self.poison(env.e, checkpoint, search_checkpoint, fault),
        }
    }

    fn find_next_deferred(&mut self, env: &mut UnifyEnv) -> Option<NarrowingSolution> {
        loop {
            if let Some(active) = &mut self.goal_search {
                if let Some(result) = active.search.next(env) {
                    let bindings = active.search.restore_input_order(&result.bindings);
                    let solution = NarrowingSolution {
                        state: active.state,
                        bindings,
                        variables: active.variables.clone(),
                        family: result.family,
                    };
                    if self.options.keep_paths {
                        self.lock_path(solution.state);
                    }
                    return Some(solution);
                }
                self.incomplete |= active.search.is_incomplete();
                self.goal_search = None;
            }
            let state = self.next_interesting_state_deferred(env)?;
            let Some(goal) = &self.goal else {
                return Some(NarrowingSolution {
                    state,
                    bindings: Vec::new(),
                    variables: Vec::new(),
                    family: self.states[state].family,
                });
            };
            let mut values = vec![None; goal.variables.len()];
            for (slot, &dag) in self.states[state]
                .prepared
                .substitution
                .iter()
                .take(goal.initial_variable_count)
                .enumerate()
            {
                values[slot] = Some(dag);
            }
            let instantiated_goal =
                instantiate_preserving_representation(env.e, &values, goal.term)
                    .unwrap_or(goal.term);
            let state_term = self.states[state].prepared.term;
            match build_goal_search(
                env,
                instantiated_goal,
                state_term,
                self.equations.clone(),
                self.states[state].family,
                &self.base,
                self.options.filter,
                self.options.delay,
            ) {
                Ok((variables, search)) => {
                    self.goal_search = Some(ActiveGoalSearch {
                        state,
                        variables,
                        search,
                    });
                }
                Err(NarrowSearchError::Reducer(fault)) => {
                    env.e.defer_reducer_fault(fault);
                    return None;
                }
                Err(NarrowSearchError::Invalid(_)) => continue,
            }
        }
    }

    /// Next state to test against the goal. State ids follow creation order.
    ///
    /// # Panics
    ///
    /// Panics if a configured strict reducer reports a [`ReducerFault`]. Use
    /// [`try_next_interesting_state`](Self::try_next_interesting_state) to preserve the fault.
    pub fn next_interesting_state(&mut self, env: &mut UnifyEnv) -> Option<usize> {
        self.try_next_interesting_state(env)
            .unwrap_or_else(|fault| panic!("{fault}"))
    }

    pub fn try_next_interesting_state(
        &mut self,
        env: &mut UnifyEnv,
    ) -> Result<Option<usize>, ReducerFault> {
        if let Some(fault) = &self.fault {
            return Err(fault.clone());
        }
        let search_checkpoint = self.state_checkpoint(env.e);
        let checkpoint = env.e.semantic_checkpoint();
        if let Err(fault) = env.e.check_deferred_reducer_fault() {
            return self.poison(env.e, checkpoint, search_checkpoint, fault);
        }
        let result = self.next_interesting_state_deferred(env);
        match env.e.check_deferred_reducer_fault() {
            Ok(()) => Ok(result),
            Err(fault) => self.poison(env.e, checkpoint, search_checkpoint, fault),
        }
    }

    fn state_checkpoint(&self, e: &Engine) -> NarrowSearchCheckpoint {
        NarrowSearchCheckpoint {
            states_len: self.states.len(),
            states: self
                .states
                .iter()
                .map(|state| {
                    let roots = if state.roots.is_empty() {
                        Vec::new()
                    } else {
                        std::iter::once(state.prepared.term)
                            .chain(state.prepared.substitution.iter().copied())
                            .chain(
                                state
                                    .step
                                    .iter()
                                    .flat_map(|step| {
                                        step.source_substitution.iter().chain(&step.state_unifier)
                                    })
                                    .copied(),
                            )
                            .map(|dag| e.root(dag))
                            .collect()
                    };
                    NarrowStateCheckpoint {
                        alive: state.alive,
                        locked: state.locked,
                        expanded: state.expanded,
                        has_successor: state.has_successor,
                        substitution: state.prepared.substitution.clone(),
                        step_values: state.step.as_ref().map(|step| {
                            (step.source_substitution.clone(), step.state_unifier.clone())
                        }),
                        roots,
                    }
                })
                .collect(),
            expand_cursor: self.expand_cursor,
            untried_initials: self.untried_initials.clone(),
            exhausted: self.exhausted,
            incomplete: self.incomplete,
            states_expanded: self.states_expanded,
            folding_events_len: self.folding_events.len(),
        }
    }

    fn poison<T>(
        &mut self,
        e: &mut Engine,
        checkpoint: SemanticCheckpoint,
        search_checkpoint: NarrowSearchCheckpoint,
        fault: ReducerFault,
    ) -> Result<T, ReducerFault> {
        e.restore_semantic_checkpoint(checkpoint);
        self.states.truncate(search_checkpoint.states_len);
        for (state, saved) in self.states.iter_mut().zip(search_checkpoint.states) {
            state.alive = saved.alive;
            state.locked = saved.locked;
            state.expanded = saved.expanded;
            state.has_successor = saved.has_successor;
            state.prepared.substitution = saved.substitution;
            if let (Some(step), Some((source, unifier))) = (&mut state.step, saved.step_values) {
                step.source_substitution = source;
                step.state_unifier = unifier;
            }
            state.roots = saved.roots;
        }
        self.expand_cursor = search_checkpoint.expand_cursor;
        self.untried_initials = search_checkpoint.untried_initials;
        self.exhausted = search_checkpoint.exhausted;
        self.incomplete = search_checkpoint.incomplete;
        self.states_expanded = search_checkpoint.states_expanded;
        self.folding_events
            .truncate(search_checkpoint.folding_events_len);
        self.expansion = None;
        self.goal_search = None;
        self.untried_initials = 0..0;
        self.exhausted = true;
        self.fault = Some(fault.clone());
        Err(fault)
    }

    fn next_interesting_state_deferred(&mut self, env: &mut UnifyEnv) -> Option<usize> {
        for index in self.untried_initials.by_ref() {
            if self.states[index].alive {
                return Some(index);
            }
        }
        loop {
            if let Some(expansion) = &mut self.expansion {
                let state_index = expansion.state_index;
                let parent_depth = self.states[state_index].depth;
                let at_bound = self
                    .options
                    .max_depth
                    .is_some_and(|bound| parent_depth >= bound);
                let state_values: Vec<_> = self.states[state_index]
                    .prepared
                    .substitution
                    .iter()
                    .copied()
                    .map(Some)
                    .collect();
                let instantiated_blockers: Vec<_> = self
                    .blockers
                    .iter()
                    .map(|&blocker| {
                        instantiate_preserving_representation(env.e, &state_values, blocker)
                            .unwrap_or(blocker)
                    })
                    .collect();
                let pending = match expansion.next(
                    env,
                    &self.states[state_index],
                    &self.rules,
                    &instantiated_blockers,
                    &self.equations,
                    &self.options,
                    &self.base,
                ) {
                    Ok(pending) => pending,
                    Err(fault) => {
                        env.e.defer_reducer_fault(fault);
                        return None;
                    }
                };
                if let Some(pending) = pending {
                    self.states[state_index].has_successor = true;
                    if at_bound {
                        self.states[state_index].expanded = false;
                        self.incomplete |= expansion.incomplete;
                        self.expansion = None;
                        continue;
                    }
                    let source = &self.rules[pending.source_index];
                    let prepared = apply_rule_unifier(
                        env.e,
                        &self.states[state_index].prepared,
                        &pending.path,
                        source,
                        &pending.unifier,
                    );
                    let step = NarrowingStepRecord {
                        rule_id: source.id,
                        rule_index: pending.source_index,
                        path: pending.path,
                        source_substitution: pending.unifier.source_bindings,
                        state_unifier: pending.unifier.state_bindings,
                        family: pending.unifier.family,
                    };
                    let candidate = StoredNarrowingState::new(
                        env.e,
                        prepared,
                        pending.unifier.family,
                        Some(state_index),
                        parent_depth + 1,
                        self.states[state_index].root_index,
                        Some(step),
                    );
                    let index = match self.insert_state(env, candidate) {
                        Ok(index) => index,
                        Err(fault) => {
                            env.e.defer_reducer_fault(fault);
                            return None;
                        }
                    };
                    if self.states[index].alive
                        && self.options.search_type != NarrowSearchType::NormalForm
                    {
                        return Some(index);
                    }
                    continue;
                }
                self.incomplete |= expansion.incomplete;
                let state_index = expansion.state_index;
                self.states[state_index].expanded = true;
                self.expansion = None;
                if self.options.search_type == NarrowSearchType::NormalForm
                    && self.states[state_index].alive
                    && !self.states[state_index].has_successor
                {
                    return Some(state_index);
                }
                continue;
            }

            while self.expand_cursor < self.states.len() {
                let index = self.expand_cursor;
                self.expand_cursor += 1;
                if !self.states[index].alive {
                    continue;
                }
                if self.options.max_depth.is_some_and(|bound| {
                    let depth = self.states[index].depth;
                    depth > bound
                        || (depth == bound
                            && self.options.search_type != NarrowSearchType::NormalForm)
                }) {
                    continue;
                }
                self.states[index].locked = true;
                self.expansion = Some(StateExpansion::new(env.e, index, &self.states[index]));
                self.states_expanded += 1;
                break;
            }
            if self.expansion.is_none() {
                self.exhausted = true;
                return None;
            }
        }
    }

    fn insert_state(
        &mut self,
        env: &mut UnifyEnv,
        mut candidate: StoredNarrowingState,
    ) -> Result<usize, ReducerFault> {
        let index = self.states.len();
        if self.options.fold != NarrowFold::None {
            let existing: Vec<_> = self
                .states
                .iter()
                .enumerate()
                .filter_map(|(index, state)| state.alive.then_some(index))
                .collect();
            for &retained in &existing {
                if self.state_subsumes(env, retained, &candidate)? {
                    let ancestor = self.is_ancestor(retained, candidate.parent);
                    self.folding_events.push(FoldingEvent::Subsumed {
                        state: index,
                        by: retained,
                        ancestor,
                    });
                    candidate.release();
                    self.states.push(candidate);
                    return Ok(index);
                }
            }
            let mut victims = HashSet::new();
            for retained in existing {
                if self.candidate_subsumes(env, &candidate, retained)? {
                    victims.insert(retained);
                    for descendant in retained + 1..self.states.len() {
                        if self.is_ancestor(retained, Some(descendant)) {
                            victims.insert(descendant);
                        }
                    }
                }
            }
            let mut victims: Vec<_> = victims.into_iter().collect();
            victims.sort_unstable();
            for victim in victims {
                if self.states[victim].alive {
                    self.folding_events.push(FoldingEvent::Evicted {
                        state: victim,
                        by: index,
                    });
                    self.states[victim].release();
                }
            }
        }
        if self.options.keep_history {
            candidate.locked = true;
        }
        self.states.push(candidate);
        Ok(index)
    }

    fn state_subsumes(
        &self,
        env: &mut UnifyEnv,
        retained: usize,
        candidate: &StoredNarrowingState,
    ) -> Result<bool, ReducerFault> {
        match self.options.fold {
            NarrowFold::None => Ok(false),
            NarrowFold::Match => crate::variant::try_unifier_subsumes(
                env.e,
                &[self.states[retained].prepared.term],
                &[candidate.prepared.term],
            ),
            NarrowFold::Variant => {
                let checkpoint = env.e.rewrite_checkpoint();
                let result = crate::variant::try_unifier_subsumes_modulo_variants(
                    env,
                    &[self.states[retained].prepared.term],
                    &[candidate.prepared.term],
                    self.equations.clone(),
                    self.states[retained].family,
                );
                env.e.restore_rewrite_checkpoint(checkpoint);
                result
            }
        }
    }

    fn candidate_subsumes(
        &self,
        env: &mut UnifyEnv,
        candidate: &StoredNarrowingState,
        retained: usize,
    ) -> Result<bool, ReducerFault> {
        match self.options.fold {
            NarrowFold::None => Ok(false),
            NarrowFold::Match => crate::variant::try_unifier_subsumes(
                env.e,
                &[candidate.prepared.term],
                &[self.states[retained].prepared.term],
            ),
            NarrowFold::Variant => {
                let checkpoint = env.e.rewrite_checkpoint();
                let result = crate::variant::try_unifier_subsumes_modulo_variants(
                    env,
                    &[candidate.prepared.term],
                    &[self.states[retained].prepared.term],
                    self.equations.clone(),
                    candidate.family,
                );
                env.e.restore_rewrite_checkpoint(checkpoint);
                result
            }
        }
    }

    fn is_ancestor(&self, ancestor: usize, mut state: Option<usize>) -> bool {
        while let Some(index) = state {
            if index == ancestor {
                return true;
            }
            state = self.states[index].parent;
        }
        false
    }

    /// Return the term, substitution, variable family, and depth for one state.
    ///
    /// # Panics
    ///
    /// Panics if `index >= self.state_count()`.
    pub fn state(&self, index: usize) -> (DagId, &[DagId], VariableFamily, usize) {
        let state = &self.states[index];
        (
            state.prepared.term,
            &state.prepared.substitution,
            state.family,
            state.depth,
        )
    }

    /// Return the indexed state's variable table.
    ///
    /// # Panics
    ///
    /// Panics if `index >= self.state_count()`.
    pub fn state_variables(&self, index: usize) -> &[VarSpec] {
        &self.states[index].prepared.variables
    }

    /// Return the indexed state's parent.
    ///
    /// # Panics
    ///
    /// Panics if `index >= self.state_count()`.
    pub fn parent(&self, index: usize) -> Option<usize> {
        self.states[index].parent
    }

    /// Return the disjunct root index that produced the indexed state.
    ///
    /// # Panics
    ///
    /// Panics if `index >= self.state_count()`.
    pub fn root_index(&self, index: usize) -> usize {
        self.states[index].root_index
    }

    /// Return the narrowing step that produced the indexed state.
    ///
    /// # Panics
    ///
    /// Panics if `index >= self.state_count()`.
    pub fn step(&self, index: usize) -> Option<&NarrowingStepRecord> {
        self.states[index].step.as_ref()
    }

    pub fn state_count(&self) -> usize {
        self.states.len()
    }

    pub fn states_expanded(&self) -> usize {
        self.states_expanded
    }

    pub fn is_incomplete(&self) -> bool {
        self.incomplete
    }

    pub fn is_exhausted(&self) -> bool {
        self.exhausted
    }

    pub fn alive_states(&self) -> impl Iterator<Item = usize> + '_ {
        self.states
            .iter()
            .enumerate()
            .filter_map(|(index, state)| state.alive.then_some(index))
    }

    pub fn frontier_states(&self) -> impl Iterator<Item = usize> + '_ {
        self.states
            .iter()
            .enumerate()
            .filter_map(|(index, state)| (state.alive && !state.expanded).then_some(index))
    }

    pub fn take_folding_events(&mut self) -> Vec<FoldingEvent> {
        std::mem::take(&mut self.folding_events)
    }

    /// Retain the roots for `state` and each of its ancestors.
    ///
    /// # Panics
    ///
    /// Panics if `state >= self.state_count()`.
    pub fn lock_path(&mut self, state: usize) {
        let mut cursor = Some(state);
        while let Some(index) = cursor {
            self.states[index].locked = true;
            cursor = self.states[index].parent;
        }
    }

    pub fn path_indices(&self, state: usize) -> Vec<usize> {
        if state >= self.states.len() || self.states[state].roots.is_empty() {
            return Vec::new();
        }
        let mut path = Vec::new();
        let mut cursor = Some(state);
        while let Some(index) = cursor {
            path.push(index);
            cursor = self.states[index].parent;
        }
        path.reverse();
        path
    }
}

/// Map an existing DAG's variable slots into the shared `(name, sort)` namespace of a synthetic
/// unification pair. This preserves already-reduced sub-DAGs and their rewrite accounting instead of
/// converting the state through [`Term`].
fn dag_to_keyed_slot_map(
    e: &Engine,
    dag: DagId,
    keys: &mut Vec<(u32, crate::sort::SortId)>,
) -> Vec<u32> {
    let mut map = Vec::new();
    let mut work = vec![dag];
    while let Some(node) = work.pop() {
        match &e.node(node).term {
            NodeTerm::Var { name, index, .. } => {
                let key = (*name, e.sort_of(node));
                let slot = keys
                    .iter()
                    .position(|candidate| *candidate == key)
                    .unwrap_or_else(|| {
                        keys.push(key);
                        keys.len() - 1
                    }) as u32;
                let index = *index as usize;
                if map.len() <= index {
                    map.resize(index + 1, 0);
                }
                map[index] = slot;
            }
            _ => {
                let children: Vec<_> = e.node(node).children().collect();
                work.extend(children.into_iter().rev());
            }
        }
    }
    map
}

#[allow(clippy::too_many_arguments)]
fn build_goal_search(
    env: &mut UnifyEnv,
    goal: DagId,
    state: DagId,
    equations: Vec<crate::variant::VariantEquation>,
    incoming_family: VariableFamily,
    base: &str,
    filtered: bool,
    delayed: bool,
) -> Result<(Vec<VarSpec>, PairUnifierSearch), NarrowSearchError> {
    let state_sort = env.e.sort_of(state);
    let mut keys = Vec::new();
    let goal_slots = dag_to_keyed_slot_map(env.e, goal, &mut keys);
    let state_slots = dag_to_keyed_slot_map(env.e, state, &mut keys);
    let specs: Vec<_> = keys
        .iter()
        .map(|&(name, sort)| VarSpec { sort, name })
        .collect();
    let range = env.e.sorts().error_sort(env.e.sorts().kind_of(state_sort));
    let pair_symbol = env
        .e
        .add_op("$narrowing-goal-pair", vec![range, range], range);
    let goal_target = env
        .e
        .remap_variable_slots_preserving_representation(goal, &goal_slots);
    let state_target = env
        .e
        .remap_variable_slots_preserving_representation(state, &state_slots);
    let target = env
        .e
        .make_node(pair_symbol, vec![goal_target, state_target]);
    let search = PairUnifierSearch::new(
        env,
        target,
        specs.clone(),
        Vec::new(),
        equations,
        incoming_family,
        base,
        filtered,
        delayed,
    )?;
    Ok((specs, search))
}
