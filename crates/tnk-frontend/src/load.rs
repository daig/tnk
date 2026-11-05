//! End-to-end loading of module text. The surface parser records declarations and raw term bubbles;
//! each module then builds its signature, per-module mixfix grammar, identities, statements, rules,
//! memberships, and strategies. Command helpers parse against a selected loaded module and open the
//! corresponding reduce, rewrite, search, match, strategy, SMT, variant, or narrowing operation.
//! Session state and presentation remain in `tnk-session`.

use crate::build_term::{VarIndex, build_dag, build_logic_dag, build_term};
use crate::cfparser::compile::CompiledGrammar;
use crate::cfparser::forest::PTree;
use crate::cfparser::{ParseEffort, earley, forest};
use crate::grammar::build::build_grammar;
use crate::grammar::{Action, GSym, Nt, NtType, Terminal};
use crate::lex::{Frag, Interner, TokKind, Token, tokenize};
use crate::oo_complete;
use crate::pretty::{print_pretty, print_pretty_with_variables, print_term};
use crate::sig::build_sig::build_module_with_host_functions;
use crate::sig::syntax::{BuiltModule, EqTrace, MbTrace, RlTrace};
use crate::surface::ast::{Command, Diagnostic, PreModule, SearchArrow, Source, Statement};
use crate::surface::parser::Parser;
use std::borrow::Cow;
use std::collections::{BTreeSet, HashMap};
use std::fmt;
use tnk_core::dag::DagId;
use tnk_core::engine::MatchedPortion;
use tnk_core::host::{HostFunctionCatalog, ReducerFault};
use tnk_core::rewrite::Rewriting;
use tnk_core::search::{Arrow, Search};
use tnk_core::smt_search::SmtSearch;
use tnk_core::sort::{KindId, SortId};
use tnk_core::symbol::SymbolId;
use tnk_core::term::{ConditionFragment, Equation, Membership, Term};
use tnk_core::variant::{
    VariantEquation, VariantMode, VariantSearch, compile_variant_equation, term_from_dag_slots,
};

/// A fully loaded module: its kernel state (signature + statements) and its mixfix grammar (for parsing
/// command/REPL terms).
pub struct LoadedModule {
    pub built: BuiltModule,
    pub grammar: CompiledGrammar,
    /// Nonfatal parse/build diagnostics, rendered only by the owning Session.
    pub diagnostics: Vec<Diagnostic>,
    /// Imported strategy-definition home grammars, with semantic actions remapped to `built`. A strategy
    /// definition carrying a distinct `home` is executable only when this map contains that home.
    pub strategy_grammars: HashMap<String, CompiledGrammar>,
    /// Cached module-wide SMT-rewrite eligibility.
    pub smt_rewrite_valid: bool,
}

/// Typed failure from the reflected-module build transaction. Ordinary syntax/build diagnostics remain
/// textual; strict reducer failures preserve the original fault for semantic owners.
#[derive(Debug)]
pub enum LoadedModuleBuildError {
    Invalid(String),
    Reducer(ReducerFault),
}

impl fmt::Display for LoadedModuleBuildError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Invalid(error) => f.write_str(error),
            Self::Reducer(fault) => write!(f, "{fault}"),
        }
    }
}

impl std::error::Error for LoadedModuleBuildError {}

impl From<String> for LoadedModuleBuildError {
    fn from(error: String) -> Self {
        Self::Invalid(error)
    }
}

/// Dense engine-trace slot produced by one source statement. The surrounding `Option` used by the
/// homed loader is `None` for a non-executable or rejected statement, preserving source alignment.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum StatementTraceRef {
    Membership(usize),
    Equation(usize),
    Rule(usize),
}

impl LoadedModule {
    /// Recompute SMT-rewrite eligibility after callers install statements directly into the engine.
    pub fn refresh_smt_rewrite_valid(&mut self, pm: &PreModule) {
        self.smt_rewrite_valid =
            self.built.engine.valid_for_smt_rewriting() && !has_regular_collapse_axiom(pm);
    }
}

fn has_regular_collapse_axiom(pm: &PreModule) -> bool {
    pm.ops
        .iter()
        .any(|op| op.attrs.poly.is_none() && (op.attrs.idem || op.attrs.id.is_some()))
}

/// A loaded source: the shared interner, the modules (file order), and the commands tagged with the
/// module-index they run against.
pub struct Loaded {
    pub interner: Interner,
    pub modules: Vec<LoadedModule>,
    pub commands: Vec<(usize, Command)>,
}

/// Build one `PreModule` into a runnable [`LoadedModule`]: signature (`build_module_with_host_functions`),
/// mixfix grammar (`build_grammar`), and statements (`load_statements`). The module system (`tnk-modules`) supplies a
/// flattened `PreModule` whose import closure has already been merged, so kernel loading remains
/// import-independent.
pub fn build_loaded_module(
    pm: &PreModule,
    interner: &mut Interner,
) -> Result<LoadedModule, String> {
    build_loaded_module_with_host_functions(pm, interner, &HostFunctionCatalog::default())
}

/// Build one import-free module against the supplied immutable strict-reducer capability catalog.
///
/// This compatibility boundary renders typed build failures as text.
pub fn build_loaded_module_with_host_functions(
    pm: &PreModule,
    interner: &mut Interner,
    host_functions: &HostFunctionCatalog,
) -> Result<LoadedModule, String> {
    try_build_loaded_module_with_host_functions(pm, interner, host_functions)
        .map_err(|error| error.to_string())
}

/// Typed configured module build. Equations and inline statements are installed before host attachment;
/// identity preparation runs only after attachment commits.
///
/// # Errors
///
/// Returns [`LoadedModuleBuildError::Invalid`] for syntax, signature, statement, or attachment
/// diagnostics and [`LoadedModuleBuildError::Reducer`] with the original strict reducer fault when
/// post-binding identity or trace normalization fails.
pub fn try_build_loaded_module_with_host_functions(
    pm: &PreModule,
    interner: &mut Interner,
    host_functions: &HostFunctionCatalog,
) -> Result<LoadedModule, LoadedModuleBuildError> {
    try_build_loaded_module_with_host_functions_and_inline_statements(
        pm,
        interner,
        host_functions,
        |_, _| Ok(()),
    )
}

/// Build one import-free module while installing already-resolved inline statements after source
/// statements and before validated strict-reducer attachments are committed.
///
/// Reflected modules decode their inline statements only after signature construction. Keeping that
/// installation inside this build transaction preserves the ordinary attachment validation path while
/// ensuring a host operator's equation table is complete before its binding seals the top symbol.
pub fn build_loaded_module_with_host_functions_and_inline_statements<F>(
    pm: &PreModule,
    interner: &mut Interner,
    host_functions: &HostFunctionCatalog,
    install_inline_statements: F,
) -> Result<LoadedModule, String>
where
    F: FnOnce(&mut BuiltModule, &mut Interner) -> Result<(), String>,
{
    try_build_loaded_module_with_host_functions_and_inline_statements(
        pm,
        interner,
        host_functions,
        |built, interner| {
            install_inline_statements(built, interner).map_err(LoadedModuleBuildError::Invalid)
        },
    )
    .map_err(|error| error.to_string())
}

/// Typed form of [`build_loaded_module_with_host_functions_and_inline_statements`]. Reflected semantic
/// owners use this boundary so identity preparation cannot erase a strict reducer fault into text.
pub fn try_build_loaded_module_with_host_functions_and_inline_statements<F>(
    pm: &PreModule,
    interner: &mut Interner,
    host_functions: &HostFunctionCatalog,
    install_inline_statements: F,
) -> Result<LoadedModule, LoadedModuleBuildError>
where
    F: FnOnce(&mut BuiltModule, &mut Interner) -> Result<(), LoadedModuleBuildError>,
{
    let mut built = build_module_with_host_functions(pm, interner, host_functions)?;
    let grammar = CompiledGrammar::compile(&build_grammar(&built, interner));
    install_identities(&mut built, &grammar, interner)?;
    let diagnostics = load_statements_before_host_bindings(pm, &mut built, &grammar, interner)?;
    install_inline_statements(&mut built, interner)?;
    bind_pending_host_functions(&mut built)?;
    normalize_narrowing_traces(&mut built, interner).map_err(LoadedModuleBuildError::Reducer)?;
    built
        .engine
        .try_prepare_identities()
        .map_err(LoadedModuleBuildError::Reducer)?;
    let smt_rewrite_valid =
        built.engine.valid_for_smt_rewriting() && !has_regular_collapse_axiom(pm);
    Ok(LoadedModule {
        built,
        grammar,
        diagnostics,
        strategy_grammars: HashMap::new(),
        smt_rewrite_valid,
    })
}

/// Build a flattened `PreModule` with per-import statement reparsing. A statement whose flattened grammar
/// is ambiguous is reparsed against its home module's grammar; see [`load_statements_homed`]. `homes`,
/// parallel to `pm.statements`, identifies each statement's home, and `home_mod` resolves an already-built
/// home module from the loader or REPL cache. The module system routes flattened modules through this entry.
pub fn build_loaded_module_homed<'m>(
    pm: &PreModule,
    homes: &[Option<String>],
    home_mod: &dyn Fn(&str) -> Option<&'m LoadedModule>,
    interner: &mut Interner,
) -> Result<LoadedModule, String> {
    build_loaded_module_homed_with_host_functions(
        pm,
        homes,
        home_mod,
        interner,
        &HostFunctionCatalog::default(),
    )
}

/// Build one flattened module with home-grammar fallback and a strict-reducer capability catalog.
pub fn build_loaded_module_homed_with_host_functions<'m>(
    pm: &PreModule,
    homes: &[Option<String>],
    home_mod: &dyn Fn(&str) -> Option<&'m LoadedModule>,
    interner: &mut Interner,
    host_functions: &HostFunctionCatalog,
) -> Result<LoadedModule, String> {
    build_loaded_module_homed_traced_with_host_functions(
        pm,
        homes,
        home_mod,
        interner,
        host_functions,
    )
    .map(|(loaded, _)| loaded)
}

/// The homed build plus a source-aligned map to dense executable trace vectors. Rejected and non-executable
/// statements occupy `None` slots so later axioms retain their source positions even though trace vectors
/// contain only registered statements.
pub fn build_loaded_module_homed_traced<'m>(
    pm: &PreModule,
    homes: &[Option<String>],
    home_mod: &dyn Fn(&str) -> Option<&'m LoadedModule>,
    interner: &mut Interner,
) -> Result<(LoadedModule, Vec<Option<StatementTraceRef>>), String> {
    build_loaded_module_homed_traced_with_host_functions(
        pm,
        homes,
        home_mod,
        interner,
        &HostFunctionCatalog::default(),
    )
}

/// Build one flattened module with statement tracing and a strict-reducer capability catalog.
///
/// This compatibility boundary renders typed build failures as text.
pub fn build_loaded_module_homed_traced_with_host_functions<'m>(
    pm: &PreModule,
    homes: &[Option<String>],
    home_mod: &dyn Fn(&str) -> Option<&'m LoadedModule>,
    interner: &mut Interner,
    host_functions: &HostFunctionCatalog,
) -> Result<(LoadedModule, Vec<Option<StatementTraceRef>>), String> {
    try_build_loaded_module_homed_traced_with_host_functions(
        pm,
        homes,
        home_mod,
        interner,
        host_functions,
    )
    .map_err(|error| error.to_string())
}

/// Typed homed configured build. Home-grammar statements and all equations are installed before
/// configured attachments commit; identity and narrowing-trace normalization then run on the sealed
/// signature.
///
/// # Errors
///
/// Returns [`LoadedModuleBuildError::Invalid`] for ordinary flatten/build/statement diagnostics and
/// [`LoadedModuleBuildError::Reducer`] with the original strict reducer fault from post-binding
/// normalization.
pub fn try_build_loaded_module_homed_traced_with_host_functions<'m>(
    pm: &PreModule,
    homes: &[Option<String>],
    home_mod: &dyn Fn(&str) -> Option<&'m LoadedModule>,
    interner: &mut Interner,
    host_functions: &HostFunctionCatalog,
) -> Result<(LoadedModule, Vec<Option<StatementTraceRef>>), LoadedModuleBuildError> {
    let mut built = build_module_with_host_functions(pm, interner, host_functions)?;
    let grammar = CompiledGrammar::compile(&build_grammar(&built, interner));
    install_identities(&mut built, &grammar, interner)?;
    let (trace_refs, diagnostics) =
        load_statements_homed(pm, &mut built, &grammar, homes, home_mod, interner)?;
    normalize_narrowing_traces(&mut built, interner).map_err(LoadedModuleBuildError::Reducer)?;
    built
        .engine
        .try_prepare_identities()
        .map_err(LoadedModuleBuildError::Reducer)?;
    let strategy_grammars = pm
        .strat_defs
        .iter()
        .filter_map(|def| def.home.as_deref())
        .filter(|home| *home != pm.name)
        .collect::<BTreeSet<_>>()
        .into_iter()
        .filter_map(|home| {
            home_mod(home)
                .and_then(|module| remap_home_grammar(module, &built))
                .map(|grammar| (home.to_string(), grammar))
        })
        .collect();
    let smt_rewrite_valid =
        built.engine.valid_for_smt_rewriting() && !has_regular_collapse_axiom(pm);
    Ok((
        LoadedModule {
            built,
            grammar,
            diagnostics,
            strategy_grammars,
            smt_rewrite_valid,
        },
        trace_refs,
    ))
}

fn install_identities(
    built: &mut BuiltModule,
    grammar: &CompiledGrammar,
    interner: &Interner,
) -> Result<(), String> {
    let specs = std::mem::take(&mut built.identity_specs);
    for spec in specs {
        let mut vars = VarIndex::new();
        let kind = built.engine.sorts().kind_of(spec.sort);
        let tree = parse_forest_at(
            &spec.tokens,
            grammar,
            interner,
            Nt::Comp(kind, NtType::Term),
        )
        .map_err(|e| format!("bad identity term: {e}"))?;
        let term = build_term(&tree, grammar, built, &spec.tokens, interner, &mut vars)
            .map_err(|e| format!("bad identity term: {e}"))?;
        if vars.count() != 0 {
            return Err("identity term must be ground".to_string());
        }
        match spec.side {
            crate::surface::ast::IdSide::Both => built.engine.set_identity_term(spec.symbol, term),
            crate::surface::ast::IdSide::Left | crate::surface::ast::IdSide::Right => {
                built.engine.set_one_sided_identity_term(spec.symbol, term);
            }
        }
    }
    Ok(())
}

/// Clone `home`'s compiled grammar and remap its semantic **actions** to symbols and sorts in `flat`.
/// Parsing still uses the home grammar's nonterminals, terminals, and precedence, while term construction
/// targets the flattened module.
///
/// Operators match by `(name, domain kinds, range kind)`, the same intrinsic key used by `build_module`.
/// Kinds map from home to flat through a shared declared sort name; declared sorts map by name, while
/// error sorts map by kind. A plain import supplies every matching sort and operator profile. Returns
/// `None` if an action cannot resolve to a flattened symbol or sort, such as after a renamed donation;
/// callers then retain the flattened grammar rather than attaching an incorrect action.
pub fn remap_home_grammar(home: &LoadedModule, flat: &BuiltModule) -> Option<CompiledGrammar> {
    let hsorts = home.built.engine.sorts();
    let fsorts = flat.engine.sorts();
    // home kind → flat kind, via any declared sort the two modules share by name (a plain import copies
    // home's sorts verbatim, so every home kind has such a witness).
    let mut kind_map: HashMap<KindId, KindId> = HashMap::new();
    for (name, &hsort) in &home.built.sorts {
        if let Some(&fsort) = flat.sorts.get(name) {
            kind_map
                .entry(hsorts.kind_of(hsort))
                .or_insert_with(|| fsorts.kind_of(fsort));
        }
    }
    // flat operator table keyed by intrinsic identity (name, domain kinds, range kind).
    let mut flat_by_profile: HashMap<(&str, Vec<KindId>, KindId), SymbolId> = HashMap::new();
    for (&fsym, syn) in &flat.syntax {
        let name = flat.engine.symbol(fsym).name();
        let dom: Vec<KindId> = syn.domain.iter().map(|&s| fsorts.kind_of(s)).collect();
        flat_by_profile.insert((name, dom, fsorts.kind_of(syn.range)), fsym);
    }
    let map_sort = |hs: SortId| -> Option<SortId> {
        // A declared sort maps by name; an error/kind sort by its kind (its name isn't in the `sorts` map).
        let name = hsorts.name(hs);
        if let Some(&f) = flat.sorts.get(name) {
            return Some(f);
        }
        Some(fsorts.error_sort(*kind_map.get(&hsorts.kind_of(hs))?))
    };
    let map_sym = |hsym: SymbolId| -> Option<SymbolId> {
        let syn = home.built.syntax.get(&hsym)?;
        let name = home.built.engine.symbol(hsym).name();
        let dom: Vec<KindId> = syn
            .domain
            .iter()
            .map(|&s| kind_map.get(&hsorts.kind_of(s)).copied())
            .collect::<Option<_>>()?;
        let rng = *kind_map.get(&hsorts.kind_of(syn.range))?;
        flat_by_profile.get(&(name, dom, rng)).copied()
    };
    let remap = |a: Action| -> Option<Action> {
        Some(match a {
            Action::MakeTerm(s) => Action::MakeTerm(map_sym(s)?),
            Action::MakeVariable(s) => Action::MakeVariable(map_sort(s)?),
            Action::MakeNatural(s) => Action::MakeNatural(map_sym(s)?),
            Action::MakeInteger(s) => Action::MakeInteger(map_sym(s)?),
            Action::MakeIter(s) => Action::MakeIter(map_sym(s)?),
            Action::MakeString(s) => Action::MakeString(map_sym(s)?),
            Action::MakeQid(s) => Action::MakeQid(map_sym(s)?),
            Action::MakeFloat(s) => Action::MakeFloat(map_sym(s)?),
            Action::MakeRational { division, minus } => Action::MakeRational {
                division: map_sym(division)?,
                minus: map_sym(minus)?,
            },
            Action::MakeSmtNumber { symbol, kind } => Action::MakeSmtNumber {
                symbol: map_sym(symbol)?,
                kind,
            },
            keep @ (Action::PassThru | Action::AssocList | Action::Nop) => keep,
        })
    };
    let mut g = home.grammar.clone();
    for prod in &mut g.prods {
        prod.action = remap(prod.action)?;
    }
    Some(g)
}

/// Surface-parse `src`, then build every module (signature + grammar + statements). This loader builds
/// each module **standalone** (no import resolution); a module with `imports` is rejected — use the
/// `tnk-modules` `load_program`, which flattens first. (Keeps the frontend's own import-free tests here.)
pub fn load_source(src: &str) -> Result<Loaded, String> {
    load_source_with_host_functions(src, &HostFunctionCatalog::default())
}

/// Parse and build import-free source against the supplied strict-reducer capability catalog.
pub fn load_source_with_host_functions(
    src: &str,
    host_functions: &HostFunctionCatalog,
) -> Result<Loaded, String> {
    let mut interner = Interner::new();
    let toks = tokenize(src, &mut interner);
    // The frontend loader is import-free and view-free (the module system, `tnk-modules`, handles both);
    // any `view` in the source is ignored here.
    let Source {
        modules: pre,
        commands,
        ..
    } = Parser::new(&toks, &interner).parse_source()?;

    let mut modules = Vec::with_capacity(pre.len());
    for pm in &pre {
        if !pm.imports.is_empty() {
            return Err(format!(
                "module `{}` has imports — load it through tnk-modules `load_program` (which flattens)",
                pm.name
            ));
        }
        modules.push(build_loaded_module_with_host_functions(
            pm,
            &mut interner,
            host_functions,
        )?);
    }
    Ok(Loaded {
        interner,
        modules,
        commands,
    })
}

fn statement_kind(statement: &Statement) -> &'static str {
    match statement {
        Statement::Eq { .. } => "equation",
        Statement::Mb { .. } => "membership",
        Statement::Rule { .. } => "rule",
    }
}

fn statement_line(statement: &Statement) -> Option<u32> {
    match statement {
        Statement::Eq { lhs, rhs, cond, .. } | Statement::Rule { lhs, rhs, cond, .. } => lhs
            .first()
            .or_else(|| rhs.first())
            .or_else(|| cond.as_ref().and_then(|tokens| tokens.first())),
        Statement::Mb {
            lhs, sort, cond, ..
        } => lhs
            .first()
            .or_else(|| sort.first())
            .or_else(|| cond.as_ref().and_then(|tokens| tokens.first())),
    }
    .map(|token| token.line)
}

fn dropped_statement_warning(module: &str, statement: &Statement, error: &str) -> Diagnostic {
    let kind = statement_kind(statement);
    Diagnostic::warning(
        module,
        statement_line(statement),
        kind,
        format!("dropped {kind}: {error}"),
    )
}

fn load_statements_before_host_bindings(
    pm: &PreModule,
    m: &mut BuiltModule,
    g: &CompiledGrammar,
    i: &Interner,
) -> Result<Vec<Diagnostic>, String> {
    load_statements_homed_before_host_bindings(pm, m, g, &[], &|_| None, i)
        .map(|(_, diagnostics)| diagnostics)
}

fn bind_pending_host_functions(m: &mut BuiltModule) -> Result<(), String> {
    for binding in std::mem::take(&mut m.pending_host_bindings) {
        m.engine
            .bind_host_function(binding.symbol, &binding.key, binding.hooks)
            .map_err(|error| error.to_string())?;
    }
    Ok(())
}

/// Parse + build + add each statement in its defining module's grammar. Imported statements are parsed
/// against their **home** grammar first, remapped onto the flattened module's symbol table by
/// [`remap_home_grammar`]. This preserves the sorts of home variables when an importer declares
/// same-named variables (a flattened parse can succeed while silently selecting the importer's
/// declaration). The flattened grammar remains the fallback when the home is unavailable or its remapped
/// grammar cannot parse the statement; a statement that the home grammar builds but rejects at the
/// statement boundary is dropped without a flattened retry. `homes[k]` is the home-module name of
/// `pm.statements[k]` (from `flatten_with_homes`); `None` or the flattened module's own name selects the
/// flattened grammar directly.
pub fn load_statements_homed<'m>(
    pm: &PreModule,
    m: &mut BuiltModule,
    g: &CompiledGrammar,
    homes: &[Option<String>],
    home_mod: &dyn Fn(&str) -> Option<&'m LoadedModule>,
    i: &Interner,
) -> Result<(Vec<Option<StatementTraceRef>>, Vec<Diagnostic>), String> {
    let result = load_statements_homed_before_host_bindings(pm, m, g, homes, home_mod, i)?;
    bind_pending_host_functions(m)?;
    Ok(result)
}

fn load_statements_homed_before_host_bindings<'m>(
    pm: &PreModule,
    m: &mut BuiltModule,
    g: &CompiledGrammar,
    homes: &[Option<String>],
    home_mod: &dyn Fn(&str) -> Option<&'m LoadedModule>,
    i: &Interner,
) -> Result<(Vec<Option<StatementTraceRef>>, Vec<Diagnostic>), String> {
    // Resolve object-pattern completion context once: its CONFIGURATION object constructor, AttributeSet
    // operator, and class sorts. It applies to the statements selected by
    // `PreModule::completes_object_patterns`: all of a flattened object module's statements, and an
    // object module's statements under any importer. No context means no completion.
    let oo = (pm.is_object || pm.object_statements.contains(&true))
        .then(|| m.engine.oo_info())
        .flatten();
    let no_oo = None;
    // Cache home-module grammars remapped onto this flattened module's symbols. Imported statements use
    // these first; `None` means the home is unavailable or cannot be remapped, so the flat grammar is used.
    let mut home_grammars: HashMap<String, Option<CompiledGrammar>> = HashMap::new();
    let mut trace_refs = Vec::with_capacity(pm.statements.len());
    let mut diagnostics = pm.diagnostics.clone();

    for (idx, stmt) in pm.statements.iter().enumerate() {
        // Ordinary nonexec equations/memberships are proof obligations. Rules still pass through:
        // `[nonexec narrowing]` feeds symbolic narrowing, and an SMT-capable module retains every rule
        // in its dedicated root-rewrite table without making it ordinarily executable.
        if stmt_is_nonexec(stmt) && !matches!(stmt, Statement::Rule { .. }) {
            trace_refs.push(None);
            continue;
        }
        let trace_ref = match stmt {
            Statement::Mb { .. } => StatementTraceRef::Membership(m.mb_traces.len()),
            Statement::Eq { .. } => StatementTraceRef::Equation(m.eq_traces.len()),
            Statement::Rule { .. } => StatementTraceRef::Rule(m.rl_traces.len()),
        };
        let stmt_oo = if pm.completes_object_patterns(idx) {
            &oo
        } else {
            &no_oo
        };
        // Imported statements belong to their defining grammar. Trying the flattened grammar first is
        // unsafe even when it parses: importer declarations can shadow a home variable name and change
        // its sort without producing an error.
        if let Some(home) = homes.get(idx).and_then(|h| h.as_deref())
            && home != m.name
        {
            if !home_grammars.contains_key(home) {
                let remapped = home_mod(home).and_then(|lm| remap_home_grammar(lm, m));
                home_grammars.insert(home.to_string(), remapped);
            }
            if let Some(hg) = home_grammars.get(home).and_then(Option::as_ref) {
                match load_one_stmt(stmt, m, hg, true, false, stmt_oo, i) {
                    Ok(registered) => {
                        trace_refs.push(registered.then_some(trace_ref));
                        continue;
                    }
                    // The home grammar built the statement, so its boundary verdict is final. A flattened
                    // reparse could only accept it by reading an importer declaration (for example a
                    // constant named like a home variable) into the statement.
                    Err(StatementLoadError::Invalid(error)) => {
                        trace_refs.push(None);
                        diagnostics.push(dropped_statement_warning(home, stmt, &error));
                        continue;
                    }
                    Err(StatementLoadError::Parse(_)) => {}
                }
            }
        }
        let own_statement = homes
            .get(idx)
            .and_then(|home| home.as_deref())
            .is_some_and(|home| home == m.name);
        // Home parsing was not applicable or failed. A statement whose flattened parse/build fails is
        // dropped with an owned diagnostic; nothing is registered before the last fallible check.
        match load_one_stmt(stmt, m, g, false, own_statement, stmt_oo, i) {
            Ok(registered) => {
                trace_refs.push(registered.then_some(trace_ref));
            }
            Err(error) => {
                trace_refs.push(None);
                let home = homes
                    .get(idx)
                    .and_then(|home| home.as_deref())
                    .unwrap_or(&pm.name);
                diagnostics.push(dropped_statement_warning(home, stmt, error.message()));
            }
        }
    }

    // Root statements precede imported statements in the flattened stream. Within each source module,
    // line order interleaves parser-time and build-time diagnostics deterministically.
    let mut source_order: HashMap<Option<String>, usize> = HashMap::new();
    for diagnostic in &diagnostics {
        let next = source_order.len();
        source_order
            .entry(diagnostic.module.clone())
            .or_insert(next);
    }
    diagnostics.sort_by_key(|diagnostic| {
        (
            source_order
                .get(&diagnostic.module)
                .copied()
                .unwrap_or(usize::MAX),
            diagnostic.line.unwrap_or(u32::MAX),
        )
    });
    Ok((trace_refs, diagnostics))
}

/// Normalize a symbolic statement term through the kernel's theory canonicalizer, then recover its
/// pre-normalization variable slots for source-form rendering. `[narrowing]` rules in `show path` use
/// normalized `Term`s, so AC and ACU arguments follow canonical rather than parser order.
fn normalize_trace_term(
    m: &mut BuiltModule,
    i: &mut Interner,
    vars: &VarIndex,
    term: &Term,
) -> Result<Term, ReducerFault> {
    let bindings: Vec<_> = (0..vars.count())
        .map(|slot| {
            let source = vars.name(slot);
            let base = source.split_once(':').map_or(source, |(base, _)| base);
            let name = i.intern(base).index();
            m.engine.make_var(vars.sort(slot), name, slot)
        })
        .collect();
    normalize_trace_term_with_bindings(m, term, &bindings)
}

fn normalize_trace_term_with_bindings(
    m: &mut BuiltModule,
    term: &Term,
    bindings: &[DagId],
) -> Result<Term, ReducerFault> {
    let dag = m.engine.instantiate_bindings(term, bindings);
    let dag = m.engine.try_normalize_for_unify(dag)?;
    Ok(term_from_dag_slots(&m.engine, dag))
}

/// Finalize narrowing display traces only after every source and inline equation has been installed and
/// pending host attachments have committed. Public symbolic normalization therefore seals a complete
/// signature rather than blocking its first attachment.
///
/// A variable's base name need not have been lexed on its own: the lexer interns an on-the-fly `X:S` as
/// one token, and object completion introduces names such as `V2` or `Atts`. Such base names are
/// interned here, as the narrowing command path interns its variables' base names.
fn normalize_narrowing_traces(
    m: &mut BuiltModule,
    interner: &mut Interner,
) -> Result<(), ReducerFault> {
    let pending: Vec<_> = m
        .rl_traces
        .iter()
        .enumerate()
        .filter(|(_, trace)| trace.narrowing)
        .map(|(index, trace)| {
            (
                index,
                trace.lhs.clone(),
                trace.rhs.clone(),
                trace.var_names.clone(),
            )
        })
        .collect();
    for (index, lhs, rhs, names) in pending {
        let mut sorts = Vec::new();
        collect_term_variable_sorts(&lhs, &mut sorts);
        collect_term_variable_sorts(&rhs, &mut sorts);
        let bindings: Vec<_> = sorts
            .into_iter()
            .enumerate()
            .map(|(slot, sort)| {
                let source = names
                    .get(slot)
                    .expect("narrowing trace names cover every variable slot");
                let base = source
                    .split_once(':')
                    .map_or(source.as_str(), |(base, _)| base);
                let name = interner.intern(base).index();
                m.engine.make_var(
                    sort.expect("narrowing trace variable occurs in its lhs or rhs"),
                    name,
                    slot as u32,
                )
            })
            .collect();
        let lhs = normalize_trace_term_with_bindings(m, &lhs, &bindings)?;
        let rhs = normalize_trace_term_with_bindings(m, &rhs, &bindings)?;
        m.rl_traces[index].lhs = lhs;
        m.rl_traces[index].rhs = rhs;
    }
    Ok(())
}
/// Static AC normalization preserves the source positions of direct variables relative to nonvariables
/// until a genuine adjacent inversion forces a sort. The runtime DAG canonicalizer always sorts the
/// whole soup. Restore that observable partition while retaining the kernel's canonical order within
/// the variable and nonvariable groups (notably `M:Marking a c` versus `N' + M + K`).
fn restore_echo_variable_positions(m: &BuiltModule, source: &Term, normalized: Term) -> Term {
    fn source_soup<'a>(symbol: SymbolId, term: &'a Term, out: &mut Vec<&'a Term>) {
        if let Term::Op {
            symbol: child_symbol,
            args,
        } = term
            && *child_symbol == symbol
        {
            for arg in args {
                source_soup(symbol, arg, out);
            }
        } else {
            out.push(term);
        }
    }

    fn normalized_soup(symbol: SymbolId, term: Term, out: &mut Vec<Term>) {
        match term {
            Term::Op {
                symbol: child_symbol,
                args,
            } if child_symbol == symbol => {
                for arg in args {
                    normalized_soup(symbol, arg, out);
                }
            }
            term => out.push(term),
        }
    }
    fn source_shape(
        symbol: SymbolId,
        source: &Term,
        leaves: &mut std::vec::IntoIter<Term>,
    ) -> Term {
        if let Term::Op {
            symbol: child_symbol,
            args,
        } = source
            && *child_symbol == symbol
        {
            Term::op(
                symbol,
                args.iter()
                    .map(|arg| source_shape(symbol, arg, leaves))
                    .collect(),
            )
        } else {
            leaves.next().expect("associative source shape changed")
        }
    }

    match (source, normalized) {
        (
            Term::Op {
                symbol: source_symbol,
                args: direct_source_args,
            },
            Term::Op {
                symbol,
                args: direct_args,
            },
        ) if *source_symbol == symbol => {
            let mut flattened_source = Vec::new();
            let mut flattened = Vec::new();
            let blank_juxtaposition = m
                .syntax
                .get(&symbol)
                .is_some_and(|syntax| matches!(syntax.frags.as_slice(), [Frag::Hole, Frag::Hole]));
            let (source_args, args, restore_shape, left_fold_candidate) =
                if direct_source_args.len() == direct_args.len() {
                    (
                        direct_source_args.iter().collect::<Vec<_>>(),
                        direct_args,
                        false,
                        direct_source_args.len() > 2 && blank_juxtaposition,
                    )
                } else {
                    for arg in direct_source_args {
                        source_soup(symbol, arg, &mut flattened_source);
                    }
                    for arg in direct_args {
                        normalized_soup(symbol, arg, &mut flattened);
                    }
                    (flattened_source, flattened, true, blank_juxtaposition)
                };
            if source_args.len() != args.len() {
                return Term::op(symbol, args);
            }
            let left_fold = left_fold_candidate
                && source_args.len() > 2
                && source_args.iter().any(|arg| {
                    arg.top_symbol()
                        .and_then(|symbol| m.syntax.get(&symbol))
                        .is_some_and(|syntax| {
                            matches!(syntax.frags.first(), Some(Frag::Hole))
                                || matches!(syntax.frags.last(), Some(Frag::Hole))
                        })
                });
            let restore_shape = restore_shape && !left_fold;

            let mask: Vec<_> = source_args
                .iter()
                .map(|arg| matches!(arg, Term::Var(_)))
                .collect();
            let has_variables = mask.iter().any(|&is_variable| is_variable);
            let has_nonvariables = mask.iter().any(|&is_variable| !is_variable);
            let ordered = if has_variables && has_nonvariables {
                let (variables, nonvariables): (Vec<_>, Vec<_>) = args
                    .into_iter()
                    .partition(|arg| matches!(arg, Term::Var(_)));
                let mut variables = variables.into_iter();
                let mut nonvariables = nonvariables.into_iter();
                mask.into_iter()
                    .map(|is_variable| {
                        if is_variable {
                            variables.next().expect("variable partition length changed")
                        } else {
                            nonvariables
                                .next()
                                .expect("nonvariable partition length changed")
                        }
                    })
                    .collect()
            } else {
                args
            };
            let restored: Vec<_> = source_args
                .into_iter()
                .zip(ordered)
                .map(|(source, normalized)| restore_echo_variable_positions(m, source, normalized))
                .collect();
            if restore_shape {
                source_shape(symbol, source, &mut restored.into_iter())
            } else if left_fold {
                let mut restored = restored.into_iter();
                let mut term = restored.next().expect("associative term has no arguments");
                for arg in restored {
                    term = Term::op(symbol, vec![term, arg]);
                }
                term
            } else {
                Term::op(symbol, restored)
            }
        }
        (
            Term::Iter {
                symbol: source_symbol,
                count: source_count,
                arg: source_arg,
            },
            Term::Iter { symbol, count, arg },
        ) if *source_symbol == symbol && *source_count == count => Term::iter(
            symbol,
            count,
            restore_echo_variable_positions(m, source_arg, *arg),
        ),
        (_, normalized) => normalized,
    }
}

/// Why [`load_one_stmt`] registered nothing.
enum StatementLoadError {
    /// The statement's bubbles do not parse or build in the grammar used. This is grammar-relative, so an
    /// imported statement may retry under the flattened grammar.
    Parse(String),
    /// The statement parsed and built but is outside the executable statement boundary (a rewrite
    /// condition outside a rule, an unbound variable, a bare-variable left-hand side, or a conditional
    /// narrowing rule). This verdict is final for the statement's home grammar.
    Invalid(String),
}

impl From<String> for StatementLoadError {
    fn from(error: String) -> Self {
        Self::Parse(error)
    }
}

impl StatementLoadError {
    fn invalid(error: &str) -> Self {
        Self::Invalid(error.to_string())
    }

    fn message(&self) -> &str {
        match self {
            Self::Parse(error) | Self::Invalid(error) => error,
        }
    }
}

/// Parse + build + register one statement's bubbles into `m`, parsing against grammar `g`. `home` selects
/// the home-grammar path: the rhs is then parsed at the universal start (`g` is the statement's own
/// unambiguous home grammar, so the flattened-grammar kind-homogeneity trick is neither needed nor valid —
/// its `Nt::Comp(kind, …)` start would name a *flattened* kind absent from the home grammar). Registers
/// nothing before the last fallible parse, so a returned `Err` leaves `m` unchanged (safe to retry).
fn load_one_stmt(
    stmt: &Statement,
    m: &mut BuiltModule,
    g: &CompiledGrammar,
    home: bool,
    record_oo_diagnostic: bool,
    oo: &Option<tnk_core::engine::OoInfo>,
    i: &Interner,
) -> Result<bool, StatementLoadError> {
    // Parse + build the rhs: kind-homogeneous with the lhs against the flattened grammar (disambiguates a
    // bare overloaded constant), or universal in the home-grammar path.
    let build_rhs = |rhs: &[Token], lhs_t: &Term, m: &BuiltModule, vars: &mut VarIndex| {
        if home {
            parse_build(rhs, g, m, i, vars)
        } else {
            parse_build_rhs(rhs, lhs_t, g, m, i, vars)
        }
    };
    match stmt {
        Statement::Eq {
            lhs,
            rhs,
            cond,
            owise,
            variant,
            label,
            ..
        } => {
            // Build order: lhs → condition (assigns fresh `:=` vars + tracks bound) → rhs, all sharing
            // one variable index. Then add via the matching kernel facade.
            let mut vars = VarIndex::new();
            let mut lhs_t = parse_build(lhs, g, m, i, &mut vars)?;
            let mut bound: BTreeSet<u32> = (0..vars.count()).collect();
            let mut condition = match cond {
                Some(c) => parse_condition(c, g, m, i, &mut vars, &mut bound)?,
                None => Vec::new(),
            };
            let mut rhs_t = build_rhs(rhs, &lhs_t, m, &mut vars)?;
            let oo_source = (record_oo_diagnostic && oo.is_some()).then(|| {
                let source_count = vars.count();
                let names = oo_variable_names(m, &vars, source_count);
                (
                    render_oo_equation(m, i, &lhs_t, &rhs_t, &condition, &names, *owise, label),
                    source_count,
                )
            });
            let oo_completed = oo.as_ref().is_some_and(|info| {
                oo_complete::complete_statement(
                    info,
                    m,
                    &mut vars,
                    &mut lhs_t,
                    Some(&mut rhs_t),
                    &mut condition,
                )
            });
            if oo_completed && let Some((source, source_count)) = oo_source {
                let names = oo_variable_names(m, &vars, source_count);
                let transformed =
                    render_oo_equation(m, i, &lhs_t, &rhs_t, &condition, &names, *owise, label);
                push_oo_diagnostic(m, "equation", source, transformed);
            }
            let nr = vars.count();
            // Capture the source-form trace metadata before the Terms are moved into the kernel; the
            // kernel returns the dense equation id, which must index `eq_traces` (asserted).
            reject_rewrite_fragment(&condition, "equation").map_err(StatementLoadError::Invalid)?;
            if !statement_vars_bound(&lhs_t, &condition, Some(&rhs_t)) {
                return Err(StatementLoadError::invalid(
                    "unbound variable in equation right-hand side or condition",
                ));
            }
            // The kernel indexes executable equations by their lhs top symbol. A bare-variable lhs is
            // outside the current statement boundary, like the membership and rule cases below.
            if lhs_t.top_symbol().is_none() {
                return Err(StatementLoadError::invalid(
                    "equation left-hand side is a variable",
                ));
            }
            let trace = EqTrace {
                lhs: lhs_t.clone(),
                rhs: rhs_t.clone(),
                condition: condition.clone(),
                var_names: (0..nr).map(|k| vars.name(k).to_string()).collect(),
                owise: *owise,
                variant: *variant,
                label: label.clone(),
                nonexec: false, // engine-registered ⇒ executable
            };
            let id = if *variant {
                m.engine
                    .add_variant_equation(lhs_t, rhs_t, nr, condition, *owise)
            } else if *owise {
                m.engine.add_owise_equation(lhs_t, rhs_t, nr, condition)
            } else if condition.is_empty() {
                m.engine.add_equation(Equation {
                    lhs: lhs_t,
                    rhs: rhs_t,
                    nr_vars: nr,
                })
            } else {
                m.engine
                    .add_conditional_equation(lhs_t, rhs_t, nr, condition)
            };
            assert_eq!(
                id as usize,
                m.eq_traces.len(),
                "equation id is the dense eq_traces index"
            );
            m.eq_traces.push(trace);
            Ok(true)
        }
        Statement::Mb {
            lhs,
            sort,
            cond,
            label,
            ..
        } => {
            let mut vars = VarIndex::new();
            let mut lhs_t = parse_build(lhs, g, m, i, &mut vars)?;
            let mut bound: BTreeSet<u32> = (0..vars.count()).collect();
            let sort_id = resolve_sort(sort, m, i)?;
            let mut condition = match cond {
                Some(c) => parse_condition(c, g, m, i, &mut vars, &mut bound)?,
                None => Vec::new(),
            };
            let oo_source = (record_oo_diagnostic && oo.is_some()).then(|| {
                let source_count = vars.count();
                let names = oo_variable_names(m, &vars, source_count);
                (
                    render_oo_membership(m, i, &lhs_t, sort_id, &condition, &names, label),
                    source_count,
                )
            });
            let oo_completed = oo.as_ref().is_some_and(|info| {
                oo_complete::complete_statement(
                    info,
                    m,
                    &mut vars,
                    &mut lhs_t,
                    None,
                    &mut condition,
                )
            });
            if oo_completed && let Some((source, source_count)) = oo_source {
                let names = oo_variable_names(m, &vars, source_count);
                let transformed =
                    render_oo_membership(m, i, &lhs_t, sort_id, &condition, &names, label);
                push_oo_diagnostic(m, "membership axiom", source, transformed);
            }
            let nr = vars.count();
            reject_rewrite_fragment(&condition, "membership")
                .map_err(StatementLoadError::Invalid)?;
            if !statement_vars_bound(&lhs_t, &condition, None) {
                return Err(StatementLoadError::invalid(
                    "unbound variable in membership condition",
                ));
            }
            if lhs_t.top_symbol().is_none() {
                return Err(StatementLoadError::invalid(
                    "membership left-hand side is a variable",
                ));
            }
            let trace = MbTrace {
                lhs: lhs_t.clone(),
                sort: sort_id,
                condition: condition.clone(),
                var_names: (0..nr).map(|k| vars.name(k).to_string()).collect(),
                label: label.clone(),
                nonexec: false, // engine-registered ⇒ executable
            };
            let id = if condition.is_empty() {
                m.engine.add_membership(Membership {
                    lhs: lhs_t,
                    sort: sort_id,
                    nr_vars: nr,
                })
            } else {
                m.engine
                    .add_conditional_membership(lhs_t, sort_id, nr, condition)
            };
            assert_eq!(
                id as usize,
                m.mb_traces.len(),
                "membership id is the dense mb_traces index"
            );
            m.mb_traces.push(trace);
            Ok(true)
        }
        Statement::Rule {
            label,
            lhs,
            rhs,
            cond,
            nonexec,
            narrowing,
        } => {
            // Rules use the same lhs → condition → rhs build order and shared variable index as
            // equations, then register in the kernel's separate rule table.
            let mut vars = VarIndex::new();
            let mut lhs_t = parse_build(lhs, g, m, i, &mut vars)?;
            let mut bound: BTreeSet<u32> = (0..vars.count()).collect();
            let mut condition = match cond {
                Some(c) => parse_condition(c, g, m, i, &mut vars, &mut bound)?,
                None => Vec::new(),
            };
            let mut rhs_t = build_rhs(rhs, &lhs_t, m, &mut vars)?;
            let oo_source = (record_oo_diagnostic && oo.is_some()).then(|| {
                let source_count = vars.count();
                let names = oo_variable_names(m, &vars, source_count);
                (
                    render_oo_rule(m, i, &lhs_t, &rhs_t, &condition, &names, label, *narrowing),
                    source_count,
                )
            });
            let oo_completed = oo.as_ref().is_some_and(|info| {
                oo_complete::complete_statement(
                    info,
                    m,
                    &mut vars,
                    &mut lhs_t,
                    Some(&mut rhs_t),
                    &mut condition,
                )
            });
            if oo_completed && let Some((source, source_count)) = oo_source {
                let names = oo_variable_names(m, &vars, source_count);
                let transformed =
                    render_oo_rule(m, i, &lhs_t, &rhs_t, &condition, &names, label, *narrowing);
                push_oo_diagnostic(m, "rule", source, transformed);
            }
            let nr = vars.count();
            let variable_names: Vec<String> =
                (0..nr).map(|slot| vars.name(slot).to_string()).collect();
            let variable_specs = if *narrowing {
                (0..nr)
                    .map(|slot| {
                        let source = vars.name(slot);
                        let base = source.split_once(':').map_or(source, |(base, _)| base);
                        let code = i.get(base).map_or(slot, |symbol| symbol.index());
                        tnk_core::unify::problem::VarSpec {
                            sort: vars.sort(slot),
                            name: maude_variable_name_rank(base, code),
                        }
                    })
                    .collect()
            } else {
                Vec::new()
            };
            // A `[narrowing]` rule cannot carry a condition.
            if *narrowing && !condition.is_empty() {
                return Err(StatementLoadError::invalid(
                    "a narrowing rule cannot have a condition",
                ));
            }
            if !statement_vars_bound(&lhs_t, &condition, Some(&rhs_t)) && !*nonexec {
                return Err(StatementLoadError::invalid(
                    "unbound variable in rule right-hand side or condition",
                ));
            }
            if lhs_t.top_symbol().is_none() && !(*nonexec || *narrowing) {
                return Err(StatementLoadError::invalid(
                    "rule left-hand side is a variable",
                ));
            }
            m.engine.add_smt_rule(
                lhs_t.clone(),
                rhs_t.clone(),
                (0..nr).map(|slot| vars.sort(slot)).collect(),
                variable_names.clone(),
                condition.clone(),
            );
            if *narrowing {
                m.engine.add_narrowing_rule(
                    lhs_t.clone(),
                    rhs_t.clone(),
                    variable_specs,
                    variable_names.clone(),
                    condition.clone(),
                    label.clone(),
                    *nonexec,
                );
            }
            // A nonexec or bare-lhs narrowing rule exists only in the symbolic descriptor table.
            if *nonexec || lhs_t.top_symbol().is_none() {
                return Ok(false);
            }
            let (trace_lhs, trace_rhs) = (lhs_t.clone(), rhs_t.clone());
            let shared_label = label.as_deref().map(std::rc::Rc::<str>::from);
            let trace = RlTrace {
                lhs: trace_lhs,
                rhs: trace_rhs,
                condition: condition.clone(),
                var_names: variable_names,
                label: shared_label.clone(),
                nonexec: false, // engine-registered ⇒ executable
                narrowing: *narrowing,
            };
            let id = if condition.is_empty() {
                m.engine.add_labelled_rule(lhs_t, rhs_t, nr, shared_label)
            } else {
                m.engine
                    .add_labelled_conditional_rule(lhs_t, rhs_t, nr, condition, shared_label)
            };
            assert_eq!(
                id as usize,
                m.rl_traces.len(),
                "rule id is the dense rl_traces index"
            );
            m.rl_traces.push(trace);
            Ok(true)
        }
    }
}

fn push_oo_diagnostic(m: &mut BuiltModule, kind: &str, source: String, transformed: String) {
    m.oo_completion_diagnostics.push(format!(
        "Considering object completion on:\n  {source}\n\
         Transformed {kind}:\n  {transformed}"
    ));
}

fn oo_keyword(keyword: &str, label: &Option<String>) -> String {
    label.as_deref().map_or_else(
        || keyword.to_string(),
        |label| format!("{keyword} [{label}] :"),
    )
}

fn oo_variable_names(m: &BuiltModule, vars: &VarIndex, source_count: u32) -> Vec<String> {
    (0..vars.count())
        .map(|slot| {
            let raw = vars.name(slot);
            let base = raw.split_once(':').map_or(raw, |(base, _)| base);
            let sort = vars.sort(slot);
            let declared = m
                .vars
                .iter()
                .any(|(name, declared_sort)| name == base && *declared_sort == sort);
            if declared {
                base.to_string()
            } else if slot >= source_count {
                format!("{base}:{}", m.engine.sorts().name(sort))
            } else {
                raw.to_string()
            }
        })
        .collect()
}

fn print_oo_term(m: &BuiltModule, i: &Interner, term: &Term, names: &[String]) -> String {
    print_term(m, i, term, names, false)
}

#[allow(clippy::too_many_arguments)]
fn render_oo_equation(
    m: &BuiltModule,
    i: &Interner,
    lhs: &Term,
    rhs: &Term,
    condition: &[ConditionFragment],
    names: &[String],
    owise: bool,
    label: &Option<String>,
) -> String {
    let keyword = oo_keyword(if condition.is_empty() { "eq" } else { "ceq" }, label);
    let mut body = format!(
        "{keyword} {} = {}",
        print_oo_term(m, i, lhs, names),
        print_oo_term(m, i, rhs, names)
    );
    append_oo_condition(m, i, &mut body, condition, names);
    if owise {
        body.push_str(" [owise]");
    }
    body.push_str(" .");
    body
}

fn render_oo_membership(
    m: &BuiltModule,
    i: &Interner,
    lhs: &Term,
    sort: SortId,
    condition: &[ConditionFragment],
    names: &[String],
    label: &Option<String>,
) -> String {
    let keyword = oo_keyword(if condition.is_empty() { "mb" } else { "cmb" }, label);
    let mut body = format!(
        "{keyword} {} : {}",
        print_oo_term(m, i, lhs, names),
        m.engine.sorts().name(sort)
    );
    append_oo_condition(m, i, &mut body, condition, names);
    body.push_str(" .");
    body
}

#[allow(clippy::too_many_arguments)]
fn render_oo_rule(
    m: &BuiltModule,
    i: &Interner,
    lhs: &Term,
    rhs: &Term,
    condition: &[ConditionFragment],
    names: &[String],
    label: &Option<String>,
    narrowing: bool,
) -> String {
    let keyword = oo_keyword(if condition.is_empty() { "rl" } else { "crl" }, label);
    let mut body = format!(
        "{keyword} {} => {}",
        print_oo_term(m, i, lhs, names),
        print_oo_term(m, i, rhs, names)
    );
    append_oo_condition(m, i, &mut body, condition, names);
    if narrowing {
        body.push_str(" [narrowing]");
    }
    body.push_str(" .");
    body
}

fn append_oo_condition(
    m: &BuiltModule,
    i: &Interner,
    body: &mut String,
    condition: &[ConditionFragment],
    names: &[String],
) {
    if condition.is_empty() {
        return;
    }
    body.push_str(" if ");
    for (position, fragment) in condition.iter().enumerate() {
        if position != 0 {
            body.push_str(" /\\ ");
        }
        match fragment {
            ConditionFragment::Equality { lhs, rhs } => {
                body.push_str(&print_oo_term(m, i, lhs, names));
                body.push_str(" = ");
                body.push_str(&print_oo_term(m, i, rhs, names));
            }
            ConditionFragment::SortTest { term, sort } => {
                body.push_str(&print_oo_term(m, i, term, names));
                body.push_str(" : ");
                body.push_str(m.engine.sorts().name(*sort));
            }
            ConditionFragment::Matching {
                pattern, subject, ..
            } => {
                body.push_str(&print_oo_term(m, i, pattern, names));
                body.push_str(" := ");
                body.push_str(&print_oo_term(m, i, subject, names));
            }
            ConditionFragment::Rewrite { lhs, pattern, .. } => {
                body.push_str(&print_oo_term(m, i, lhs, names));
                body.push_str(" => ");
                body.push_str(&print_oo_term(m, i, pattern, names));
            }
        }
    }
}

/// One statement parsed into its trace form (the sum of the three engine-trace kinds). Produced by
/// [`parse_statement_trace`] for statements that carry no engine trace.
pub enum StmtTrace {
    Eq(EqTrace),
    Mb(MbTrace),
    Rl(RlTrace),
}

/// Parse a statement's raw bubbles into a [`StmtTrace`] against an already-built module's grammar and
/// signature without registering it. This exposes `[nonexec]` statements to reflective rendering even
/// though engine loading does not register them. When `oo` is the object-pattern completion context (the
/// statement satisfies `PreModule::completes_object_patterns`), the statement is completed first, as
/// engine loading completes executable statements and the rules of the narrowing and SMT tables. The left
/// side, condition, and right side share one variable index; the trace retains `nonexec`, `owise`, and
/// `label`.
pub fn parse_statement_trace(
    stmt: &Statement,
    m: &BuiltModule,
    g: &CompiledGrammar,
    i: &Interner,
    oo: Option<&tnk_core::engine::OoInfo>,
) -> Result<StmtTrace, String> {
    match stmt {
        Statement::Eq {
            lhs,
            rhs,
            cond,
            owise,
            variant,
            nonexec,
            label,
        } => {
            let mut vars = VarIndex::new();
            let mut lhs_t = parse_build(lhs, g, m, i, &mut vars)?;
            let mut bound: BTreeSet<u32> = (0..vars.count()).collect();
            let mut condition = match cond {
                Some(c) => parse_condition(c, g, m, i, &mut vars, &mut bound)?,
                None => Vec::new(),
            };
            let mut rhs_t = parse_build_rhs(rhs, &lhs_t, g, m, i, &mut vars)?;
            if let Some(info) = oo {
                oo_complete::complete_statement(
                    info,
                    m,
                    &mut vars,
                    &mut lhs_t,
                    Some(&mut rhs_t),
                    &mut condition,
                );
            }
            reject_rewrite_fragment(&condition, "equation")?;
            let nr = vars.count();
            Ok(StmtTrace::Eq(EqTrace {
                lhs: lhs_t,
                rhs: rhs_t,
                condition,
                var_names: (0..nr).map(|k| vars.name(k).to_string()).collect(),
                owise: *owise,
                variant: *variant,
                label: label.clone(),
                nonexec: *nonexec,
            }))
        }
        Statement::Mb {
            lhs,
            sort,
            cond,
            nonexec,
            label,
        } => {
            let mut vars = VarIndex::new();
            let mut lhs_t = parse_build(lhs, g, m, i, &mut vars)?;
            let mut bound: BTreeSet<u32> = (0..vars.count()).collect();
            let sort_id = resolve_sort(sort, m, i)?;
            let mut condition = match cond {
                Some(c) => parse_condition(c, g, m, i, &mut vars, &mut bound)?,
                None => Vec::new(),
            };
            if let Some(info) = oo {
                oo_complete::complete_statement(
                    info,
                    m,
                    &mut vars,
                    &mut lhs_t,
                    None,
                    &mut condition,
                );
            }
            reject_rewrite_fragment(&condition, "membership")?;
            let nr = vars.count();
            Ok(StmtTrace::Mb(MbTrace {
                lhs: lhs_t,
                sort: sort_id,
                condition,
                var_names: (0..nr).map(|k| vars.name(k).to_string()).collect(),
                label: label.clone(),
                nonexec: *nonexec,
            }))
        }
        Statement::Rule {
            label,
            lhs,
            rhs,
            cond,
            nonexec,
            narrowing,
        } => {
            let mut vars = VarIndex::new();
            let mut lhs_t = parse_build(lhs, g, m, i, &mut vars)?;
            let mut bound: BTreeSet<u32> = (0..vars.count()).collect();
            let mut condition = match cond {
                Some(c) => parse_condition(c, g, m, i, &mut vars, &mut bound)?,
                None => Vec::new(),
            };
            let mut rhs_t = parse_build_rhs(rhs, &lhs_t, g, m, i, &mut vars)?;
            if let Some(info) = oo {
                oo_complete::complete_statement(
                    info,
                    m,
                    &mut vars,
                    &mut lhs_t,
                    Some(&mut rhs_t),
                    &mut condition,
                );
            }
            // (a rule condition may carry a rewrite fragment `t => p`, so no reject here)
            let nr = vars.count();
            Ok(StmtTrace::Rl(RlTrace {
                lhs: lhs_t,
                rhs: rhs_t,
                condition,
                var_names: (0..nr).map(|k| vars.name(k).to_string()).collect(),
                label: label.as_deref().map(std::rc::Rc::<str>::from),
                nonexec: *nonexec,
                narrowing: *narrowing,
            }))
        }
    }
}

/// The connective of a condition fragment.
#[derive(Clone, Copy)]
enum Connective {
    /// `pattern := subject` (matching).
    Match,
    /// `lhs = rhs` (equality).
    Eq,
    /// `term : sort` (sort test).
    Sort,
    /// `lhs => pattern` (rewrite condition, legal only in rules).
    Rewrite,
}

/// Parse a condition bubble (the tokens after `if`) into kernel [`ConditionFragment`]s: split on `/\` at
/// paren-depth 0, then read each fragment with [`parse_condition_fragment`]. Shares the statement's
/// variable index; a `:=` fragment's *fresh* variables are the pattern variables not already bound (by
/// the lhs or an earlier fragment), which the matcher binds.
pub(crate) fn parse_condition(
    bubble: &[Token],
    g: &CompiledGrammar,
    m: &BuiltModule,
    i: &Interner,
    vars: &mut VarIndex,
    bound: &mut BTreeSet<u32>,
) -> Result<Vec<ConditionFragment>, String> {
    let mut frags = Vec::new();
    for ftoks in split_on_text(bubble, "/\\", i) {
        frags.push(parse_condition_fragment(ftoks, g, m, i, vars, bound)?);
    }
    Ok(frags)
}

/// Read one condition fragment. Its connective is a paren-depth-0 `:=`, `=>`, `=`, or `:` token, but an
/// operator name may contain the same text as a literal fragment (object syntax `< O : C | a : v >`, a
/// user `<_:_>`), so the connective is chosen by which split builds:
///
/// - With no such token, the fragment is a bare Boolean `b`, read as `b = true`.
/// - The first such token is tried first. When its split builds, it is the reading, so every fragment
///   that the first-token rule accepted keeps its meaning.
/// - Otherwise the candidate readings are the later connective tokens (a `:` only before a sort name)
///   and the whole fragment as a term of `true`'s kind, read as `b = true`. Exactly one of them must
///   build: with none, the first split's error stands, and several make the fragment ambiguous.
///
/// A parse that exceeds the effort limit decides nothing (`TNK-PARSE-003`), so its error ends the
/// search. On success, `vars` and `bound` record only the chosen reading's variables.
fn parse_condition_fragment(
    ftoks: &[Token],
    g: &CompiledGrammar,
    m: &BuiltModule,
    i: &Interner,
    vars: &mut VarIndex,
    bound: &mut BTreeSet<u32>,
) -> Result<ConditionFragment, String> {
    let candidates = connective_candidates(ftoks, i);
    let Some((&(left, conn, right), later)) = candidates.split_first() else {
        // A bare boolean fragment `b` abbreviates `b = true`. BOOL supplies the required true anchor.
        let lhs = parse_build(ftoks, g, m, i, vars)?;
        let true_sym = m
            .true_sym
            .ok_or("bare boolean condition, but no `true` is in scope (import BOOL)")?;
        return Ok(ConditionFragment::Equality {
            lhs,
            rhs: Term::constant(true_sym),
        });
    };
    let (vars_before, bound_before) = (vars.clone(), bound.clone());
    let first_error = match build_condition_fragment(left, conn, right, g, m, i, vars, bound) {
        Ok(fragment) => return Ok(fragment),
        Err(error) if is_parse_effort_error(&error) => return Err(error),
        Err(error) => error,
    };
    *vars = vars_before;
    *bound = bound_before;

    let mut readings = Vec::new();
    for &(left, conn, right) in later {
        if matches!(conn, Connective::Sort) && resolve_sort(right, m, i).is_err() {
            continue; // this `:` is not followed by a sort name, so it belongs to a term
        }
        let (mut fragment_vars, mut fragment_bound) = (vars.clone(), bound.clone());
        match build_condition_fragment(
            left,
            conn,
            right,
            g,
            m,
            i,
            &mut fragment_vars,
            &mut fragment_bound,
        ) {
            Ok(fragment) => readings.push((fragment, fragment_vars, fragment_bound)),
            Err(error) if is_parse_effort_error(&error) => return Err(error),
            Err(_) => {}
        }
    }
    if let Some(true_sym) = m.true_sym {
        let mut fragment_vars = vars.clone();
        match parse_build(ftoks, g, m, i, &mut fragment_vars) {
            Ok(lhs) if term_kind(&lhs, m) == Some(m.engine.symbol_kind(true_sym)) => {
                let fragment = ConditionFragment::Equality {
                    lhs,
                    rhs: Term::constant(true_sym),
                };
                readings.push((fragment, fragment_vars, bound.clone()));
            }
            Err(error) if is_parse_effort_error(&error) => return Err(error),
            _ => {}
        }
    }
    match readings.len() {
        0 => Err(first_error),
        1 => {
            let (fragment, fragment_vars, fragment_bound) =
                readings.pop().expect("one condition fragment reading");
            *vars = fragment_vars;
            *bound = fragment_bound;
            Ok(fragment)
        }
        _ => Err(format!(
            "ambiguous condition fragment: `{}`",
            ftoks
                .iter()
                .map(|t| i.resolve(t.sym))
                .collect::<Vec<_>>()
                .join(" ")
        )),
    }
}

/// Build one condition fragment from the split at a connective token.
#[allow(clippy::too_many_arguments)]
fn build_condition_fragment(
    left: &[Token],
    conn: Connective,
    right: &[Token],
    g: &CompiledGrammar,
    m: &BuiltModule,
    i: &Interner,
    vars: &mut VarIndex,
    bound: &mut BTreeSet<u32>,
) -> Result<ConditionFragment, String> {
    Ok(match conn {
        Connective::Match => {
            let pattern = parse_build(left, g, m, i, vars)?;
            let subject = parse_build(right, g, m, i, vars)?;
            let mut pat_vars = Vec::new();
            term_var_indices(&pattern, &mut pat_vars);
            let fresh: Vec<u32> = pat_vars
                .iter()
                .copied()
                .filter(|v| !bound.contains(v))
                .collect();
            bound.extend(pat_vars);
            ConditionFragment::Matching {
                pattern,
                subject,
                fresh_vars: fresh,
            }
        }
        Connective::Eq => ConditionFragment::Equality {
            lhs: parse_build(left, g, m, i, vars)?,
            rhs: parse_build(right, g, m, i, vars)?,
        },
        Connective::Rewrite => {
            // `lhs => pattern`: build the left term using existing bindings, then build the target
            // pattern, whose previously unbound variables become fresh binders for the search.
            let lhs = parse_build(left, g, m, i, vars)?;
            let pattern = parse_build(right, g, m, i, vars)?;
            let mut pat_vars = Vec::new();
            term_var_indices(&pattern, &mut pat_vars);
            let fresh: Vec<u32> = pat_vars
                .iter()
                .copied()
                .filter(|v| !bound.contains(v))
                .collect();
            bound.extend(pat_vars);
            ConditionFragment::Rewrite {
                lhs,
                pattern,
                fresh_vars: fresh,
            }
        }
        Connective::Sort => ConditionFragment::SortTest {
            term: parse_build(left, g, m, i, vars)?,
            sort: resolve_sort(right, m, i)?,
        },
    })
}

/// Split `toks` on the `sep`-text token at paren-depth 0 (e.g. `/\`). Always yields ≥ 1 part.
fn split_on_text<'a>(toks: &'a [Token], sep: &str, i: &Interner) -> Vec<&'a [Token]> {
    let mut parts = Vec::new();
    let (mut depth, mut start) = (0i32, 0usize);
    for (k, t) in toks.iter().enumerate() {
        match i.resolve(t.sym) {
            "(" => depth += 1,
            ")" => depth -= 1,
            s if depth == 0 && s == sep => {
                parts.push(&toks[start..k]);
                start = k + 1;
            }
            _ => {}
        }
    }
    parts.push(&toks[start..]);
    parts
}

/// Every split of a condition fragment at a paren-depth-0 connective token (`:=`, `=`, `:`, or `=>`), in
/// source order. A fragment with none is a bare boolean condition and is desugared to `b = true`.
fn connective_candidates<'a>(
    toks: &'a [Token],
    i: &Interner,
) -> Vec<(&'a [Token], Connective, &'a [Token])> {
    let mut candidates = Vec::new();
    let mut depth = 0i32;
    for (k, t) in toks.iter().enumerate() {
        let conn = match i.resolve(t.sym) {
            "(" => {
                depth += 1;
                None
            }
            ")" => {
                depth -= 1;
                None
            }
            ":=" if depth == 0 => Some(Connective::Match),
            // `=>` lexes as a single token, distinct from `=`, so the order of these arms is irrelevant.
            "=>" if depth == 0 => Some(Connective::Rewrite),
            "=" if depth == 0 => Some(Connective::Eq),
            ":" if depth == 0 => Some(Connective::Sort),
            _ => None,
        };
        if let Some(conn) = conn {
            candidates.push((&toks[..k], conn, &toks[k + 1..]));
        }
    }
    candidates
}

/// Whether a statement is `[nonexec]` (a proof obligation not applied during execution).
fn stmt_is_nonexec(s: &Statement) -> bool {
    match s {
        Statement::Eq { nonexec, .. }
        | Statement::Mb { nonexec, .. }
        | Statement::Rule { nonexec, .. } => *nonexec,
    }
}

/// Reject a rewrite (`=>`) fragment in a non-rule condition. Rewrite conditions are valid only in `crl`;
/// this guard returns a stable error before the kernel's defensive assertion. META down-installation of
/// reflected equations and memberships applies the same check.
pub fn reject_rewrite_fragment(condition: &[ConditionFragment], owner: &str) -> Result<(), String> {
    if condition
        .iter()
        .any(|f| matches!(f, ConditionFragment::Rewrite { .. }))
    {
        return Err(format!(
            "a rewrite condition (`=>`) is only allowed in a rule (`crl`), not an {owner}"
        ));
    }
    Ok(())
}

/// Check that every variable is bound before use. A right side and each evaluated condition side may
/// use left-side variables plus fresh binders from earlier `:=` or `=>` fragments. Violations make the
/// statement non-executable and retain a dropped-statement diagnostic. META down-installation of
/// reflected statements applies the same check.
pub fn statement_vars_bound(
    lhs: &Term,
    condition: &[ConditionFragment],
    rhs: Option<&Term>,
) -> bool {
    let mut bound = Vec::new();
    term_var_indices(lhs, &mut bound);
    let ok = |t: &Term, bound: &Vec<u32>| {
        let mut used = Vec::new();
        term_var_indices(t, &mut used);
        used.iter().all(|v| bound.contains(v))
    };
    for frag in condition {
        let frag_ok = match frag {
            ConditionFragment::Equality { lhs, rhs } => ok(lhs, &bound) && ok(rhs, &bound),
            ConditionFragment::SortTest { term, .. } => ok(term, &bound),
            ConditionFragment::Matching {
                subject,
                fresh_vars,
                ..
            } => {
                let r = ok(subject, &bound);
                bound.extend_from_slice(fresh_vars);
                r
            }
            ConditionFragment::Rewrite {
                lhs, fresh_vars, ..
            } => {
                let r = ok(lhs, &bound);
                bound.extend_from_slice(fresh_vars);
                r
            }
        };
        if !frag_ok {
            return false;
        }
    }
    rhs.is_none_or(|r| ok(r, &bound))
}

pub(crate) fn term_var_indices(t: &Term, out: &mut Vec<u32>) {
    match t {
        Term::Var(v) => {
            if !out.contains(&v.index) {
                out.push(v.index);
            }
        }
        Term::Na { .. } => {} // a literal introduces no variables
        Term::Op { args, .. } => {
            for a in args {
                term_var_indices(a, out);
            }
        }
        Term::Iter { arg, .. } => term_var_indices(arg, out),
    }
}

/// Parse a term token bubble to its (unambiguous) parse tree; rejects empty input, no-parse, and ambiguity.
fn parse_forest(tokens: &[Token], g: &CompiledGrammar, i: &Interner) -> Result<PTree, String> {
    let parsed = parse_forest_any(tokens, g, i)?;
    if parsed.ambiguous {
        let rendered = tokens
            .iter()
            .map(|t| i.resolve(t.sym))
            .collect::<Vec<_>>()
            .join(" ");
        return Err(format!("ambiguous parse: `{rendered}`"));
    }
    Ok(parsed.tree)
}

/// Parse a command term and choose the first chart/completion parse on ambiguity. Statement bubbles use
/// strict [`parse_forest`] and reject ambiguity.
fn parse_forest_pick(tokens: &[Token], g: &CompiledGrammar, i: &Interner) -> Result<PTree, String> {
    Ok(parse_forest_any(tokens, g, i)?.tree)
}

/// The leading text of every [`parse_effort_error`] message.
const PARSE_EFFORT_EXCEEDED: &str = "parse effort limit exceeded";

fn parse_effort_error(at: usize, tokens: &[Token], i: &Interner) -> String {
    let token = tokens.get(at).map(|token| token.text(i)).unwrap_or("<end>");
    format!("{PARSE_EFFORT_EXCEEDED} at token {at} (`{token}`)")
}

/// Whether a term parse/build error is effort exhaustion (`TNK-PARSE-003`) rather than a malformed term.
/// Every exhaustion error begins with [`parse_effort_error`]'s text, and no other error does.
fn is_parse_effort_error(error: &str) -> bool {
    error.starts_with(PARSE_EFFORT_EXCEEDED)
}

fn parse_forest_any(
    tokens: &[Token],
    g: &CompiledGrammar,
    i: &Interner,
) -> Result<forest::Parse, String> {
    let mut effort = ParseEffort::default();
    parse_forest_any_with_effort(tokens, g, i, &mut effort)
}

fn parse_forest_any_with_effort(
    tokens: &[Token],
    g: &CompiledGrammar,
    i: &Interner,
    effort: &mut ParseEffort,
) -> Result<forest::Parse, String> {
    if tokens.is_empty() {
        return Err("empty term".into());
    }
    let rendered = || {
        tokens
            .iter()
            .map(|t| i.resolve(t.sym))
            .collect::<Vec<_>>()
            .join(" ")
    };
    let chart = earley::parse(g, tokens, Nt::Term, i, effort)
        .map_err(|e| format!("{}: `{}`", parse_effort_error(e.at, tokens, i), rendered()))?;
    if !chart.recognized(g, Nt::Term) {
        let at = chart.furthest();
        let token = tokens.get(at).map(|token| token.text(i)).unwrap_or("<end>");
        return Err(format!(
            "no parse at token {at} (`{token}`): `{}`",
            rendered()
        ));
    }
    forest::extract(g, &chart, tokens.len(), Nt::Term, effort).map_err(|e| match e {
        forest::ExtractError::Effort(exceeded) => format!(
            "{}: `{}`",
            parse_effort_error(exceeded.at, tokens, i),
            rendered()
        ),
        forest::ExtractError::NoParse => format!("no parse: `{}`", rendered()),
    })
}

/// Object syntax permits an omitted third argument (`< O : C | >`), denoting the empty `AttributeSet`.
/// The mixfix grammar treats `<_:_|_>` as an ordinary three-hole operator, so this function materializes
/// the identity token before parsing. The common non-object path remains borrowed and allocates no token copy.
fn fill_empty_object_attributes<'a>(
    tokens: &'a [Token],
    m: &BuiltModule,
    i: &Interner,
) -> Cow<'a, [Token]> {
    let Some(none) = m
        .engine
        .oo_info()
        .and_then(|info| info.none_sym)
        .and_then(|symbol| i.get(m.engine.symbol(symbol).name()))
    else {
        return Cow::Borrowed(tokens);
    };
    if !tokens
        .windows(2)
        .any(|pair| pair[0].text(i) == "|" && pair[1].text(i) == ">")
    {
        return Cow::Borrowed(tokens);
    }

    let mut filled = Vec::with_capacity(tokens.len() + 1);
    for (index, token) in tokens.iter().copied().enumerate() {
        filled.push(token);
        if token.text(i) == "|"
            && tokens
                .get(index + 1)
                .is_some_and(|next| next.text(i) == ">")
        {
            filled.push(Token {
                sym: none,
                line: token.line,
                kind: TokKind::Ident,
            });
        }
    }
    Cow::Owned(filled)
}

/// One command term parsed once against its module grammar. The token bubble is borrowed on the common
/// path and owned only when omitted object attributes need their identity token materialized.
pub struct ParsedCommandTerm<'a> {
    tokens: Cow<'a, [Token]>,
    parsed: forest::Parse,
}

impl ParsedCommandTerm<'_> {
    pub fn tokens(&self) -> &[Token] {
        &self.tokens
    }
    pub(crate) fn tree(&self) -> &PTree {
        &self.parsed.tree
    }
    pub(crate) fn unambiguous_tree(&self, i: &Interner) -> Result<&PTree, String> {
        if self.parsed.ambiguous {
            let rendered = self
                .tokens
                .iter()
                .map(|token| token.text(i))
                .collect::<Vec<_>>()
                .join(" ");
            return Err(format!("ambiguous parse: `{rendered}`"));
        }
        Ok(&self.parsed.tree)
    }
}

pub fn parse_command_term<'a>(
    lm: &LoadedModule,
    i: &Interner,
    tokens: &'a [Token],
) -> Result<ParsedCommandTerm<'a>, String> {
    let tokens = fill_empty_object_attributes(tokens, &lm.built, i);
    let parsed = parse_forest_any(&tokens, &lm.grammar, i)?;
    Ok(ParsedCommandTerm { tokens, parsed })
}

/// Parse a term token bubble and build its kernel [`Term`] (the statement/pattern path).
pub(crate) fn parse_build(
    tokens: &[Token],
    g: &CompiledGrammar,
    m: &BuiltModule,
    i: &Interner,
    vars: &mut VarIndex,
) -> Result<Term, String> {
    let tokens = fill_empty_object_attributes(tokens, m, i);
    build_term(&parse_forest(&tokens, g, i)?, g, m, &tokens, i, vars)
}

/// The kind of a built term's top — its top symbol's range, or `None` for a bare variable (whose kind we
/// don't constrain against). Used to parse an equation's rhs in the *same* kind as its lhs.
fn term_kind(t: &Term, m: &BuiltModule) -> Option<KindId> {
    t.top_symbol().map(|s| m.engine.symbol_kind(s))
}

/// Parse and build an equation or rule right side in the left side's kind. This disambiguates a bare
/// overloaded constant such as `none`. If the kind-specific nonterminal yields no parse for a malformed
/// or cross-kind right side, retry from the universal start symbol so the underlying parse or build error
/// is reported.
fn parse_build_rhs(
    rhs: &[Token],
    lhs: &Term,
    g: &CompiledGrammar,
    m: &BuiltModule,
    i: &Interner,
    vars: &mut VarIndex,
) -> Result<Term, String> {
    let rhs = fill_empty_object_attributes(rhs, m, i);
    if let Some(k) = term_kind(lhs, m) {
        let start = Nt::Comp(k, NtType::Term);
        if let Ok(tree) = parse_forest_at(&rhs, g, i, start) {
            return build_term(&tree, g, m, &rhs, i, vars);
        }
    }
    parse_build(&rhs, g, m, i, vars)
}

/// Like [`parse_forest`] but starting at an arbitrary nonterminal (a per-kind term nonterminal), to parse
/// a bubble constrained to one kind.
fn parse_forest_at(
    tokens: &[Token],
    g: &CompiledGrammar,
    i: &Interner,
    start: Nt,
) -> Result<PTree, String> {
    if tokens.is_empty() {
        return Err("empty term".into());
    }
    let mut effort = ParseEffort::default();
    let chart = earley::parse(g, tokens, start, i, &mut effort)
        .map_err(|e| parse_effort_error(e.at, tokens, i))?;
    if !chart.recognized(g, start) {
        let at = chart.furthest();
        let token = tokens.get(at).map(|token| token.text(i)).unwrap_or("<end>");
        return Err(format!("no parse at token {at} (`{token}`)"));
    }
    let parsed =
        forest::extract(g, &chart, tokens.len(), start, &mut effort).map_err(|e| match e {
            forest::ExtractError::Effort(exceeded) => parse_effort_error(exceeded.at, tokens, i),
            forest::ExtractError::NoParse => "no parse".to_string(),
        })?;
    if parsed.ambiguous {
        return Err("ambiguous parse".into());
    }
    Ok(parsed.tree)
}

/// Resolve a sort token bubble to a [`SortId`]. A plain sort is one token; a **structured** sort
/// (`NeList{X}`) lexes as several tokens (`NeList`, `{`, `X`, `}`) which reassemble — no spaces — into the
/// canonical sort name the signature stored.
fn resolve_sort(tokens: &[Token], m: &BuiltModule, i: &Interner) -> Result<SortId, String> {
    let name: String = tokens.iter().map(|t| t.text(i)).collect();
    m.sorts
        .get(&name)
        .copied()
        .ok_or_else(|| format!("unknown sort `{name}`"))
}

/// Canonical command echo for `reduce in M : <term> .`: theory-normalized and pretty-printed from
/// the parsed command term. Special constants use canonical surface forms, redundant parentheses
/// drop, and AC arguments follow kernel order.
pub fn command_echo(
    lm: &mut LoadedModule,
    i: &Interner,
    term: &ParsedCommandTerm<'_>,
    color: bool,
) -> Result<String, String> {
    let dag = build_subject_dag(lm, term.tree(), term.tokens(), i)?;
    let mut echo = print_pretty(&lm.built, i, dag, color);
    // Nullary overloads share one runtime symbol and therefore cannot carry the parent's expected
    // declaration into pretty-printing. The variant metalevel APIs uniquely require their `empty`
    // argument at `GroundTermList`; restore that statically known domain in the command echo.
    let head = term
        .tokens()
        .first()
        .map(|token| token.text(i))
        .unwrap_or("");
    if matches!(
        head,
        "metaGetVariant"
            | "metaGetIrredundantVariant"
            | "metaVariantUnify"
            | "metaVariantDisjointUnify"
            | "metaVariantMatch"
    ) {
        echo = echo.replace("(empty).EmptyCommaList", "(empty).GroundTermList");
    }
    Ok(echo)
}

pub fn reduce_command(
    lm: &mut LoadedModule,
    i: &Interner,
    term: &ParsedCommandTerm<'_>,
) -> Result<(DagId, u64), String> {
    // Construction is uncounted; equations and memberships contribute during reduction. Build within a
    // deduplication window so repeated source subterms share one normalized DAG node. Close the window
    // before reduction, including on construction failure.
    lm.built.engine.reset_rewrites();
    lm.built.engine.begin_dedup();
    let dag = build_subject_dag(lm, term.tree(), term.tokens(), i);
    lm.built.engine.end_dedup();
    let dag = dag?;
    let result = lm
        .built
        .engine
        .try_reduce(dag)
        .map_err(|fault| fault.to_string())?;
    Ok((result, lm.built.engine.rewrites()))
}

/// Build a parsed command subject DAG, resetting the rewrite counter and building inside a dedup window
/// exactly like [`reduce_command`]. Shared by the `rewrite`/`frewrite` session builders and the REPL's
/// `reduce` (which then drives [`Engine::reduce_with`](tnk_core::engine::Engine::reduce_with) for
/// META-LEVEL descent).
pub fn build_command_dag(
    lm: &mut LoadedModule,
    i: &Interner,
    term: &ParsedCommandTerm<'_>,
) -> Result<DagId, String> {
    lm.built.engine.reset_rewrites();
    lm.built.engine.begin_dedup();
    let dag = build_subject_dag(lm, term.tree(), term.tokens(), i);
    lm.built.engine.end_dedup();
    dag
}

/// Parse a command-shaped term into the first one or two concrete parses required by `metaParse`. Each
/// tuple contains the source-order [`Term`] used for reflective encoding, its variable names, and the
/// canonical symbolic DAG used to compute the least sort.
pub fn build_logic_command_parses(
    lm: &mut LoadedModule,
    i: &Interner,
    tokens: &[Token],
) -> Result<Vec<(Term, VarIndex, DagId)>, String> {
    let parsed = parse_forest_any(tokens, &lm.grammar, i)?;
    let mut trees = vec![parsed.tree];
    if let Some(alternative) = parsed.alternative {
        trees.push(alternative);
    }
    let mut sources = Vec::with_capacity(trees.len());
    for tree in trees {
        let mut vars = VarIndex::new();
        let term = build_term(&tree, &lm.grammar, &lm.built, tokens, i, &mut vars)?;
        sources.push((tree, term, vars));
    }

    lm.built.engine.reset_rewrites();
    lm.built.engine.begin_dedup();
    let result = sources
        .into_iter()
        .map(|(tree, term, mut vars)| {
            let dag = build_logic_dag(
                &tree,
                &lm.grammar,
                &mut lm.built.engine,
                lm.built.nat_zero,
                lm.built.nat_succ,
                tokens,
                i,
                &mut vars,
            )?;
            Ok((term, vars, dag))
        })
        .collect();
    lm.built.engine.end_dedup();
    result
}

/// Parse a command-shaped term into a genuine symbolic DAG. Unlike [`build_command_dag`], variables stay
/// [`NodeRepr::Var`](tnk_core::dag::NodeRepr::Var) leaves rather than being lowered to inert constants.
/// META-LEVEL's `metaParse` needs this distinction because its result reifies variables as `Qid` terms.
pub fn build_logic_command_dag(
    lm: &mut LoadedModule,
    i: &Interner,
    term: &ParsedCommandTerm<'_>,
) -> Result<DagId, String> {
    lm.built.engine.reset_rewrites();
    lm.built.engine.begin_dedup();
    let mut vars = VarIndex::new();
    let dag = build_logic_dag(
        term.tree(),
        &lm.grammar,
        &mut lm.built.engine,
        lm.built.nat_zero,
        lm.built.nat_succ,
        term.tokens(),
        i,
        &mut vars,
    );
    lm.built.engine.end_dedup();
    dag
}

/// Build a command subject, using the fast ground-DAG path when possible. For an open term, realize each
/// distinct variable as an inert nullary constant of its declared sort and source print name. Repeated
/// occurrences share one constant.
fn build_subject_dag(
    lm: &mut LoadedModule,
    tree: &PTree,
    term: &[Token],
    i: &Interner,
) -> Result<DagId, String> {
    if !tree_has_var(tree, &lm.grammar) {
        return build_dag(
            tree,
            &lm.grammar,
            &mut lm.built.engine,
            lm.built.nat_zero,
            lm.built.nat_succ,
            term,
            i,
        );
    }
    let mut vars = VarIndex::new();
    let t = build_term(tree, &lm.grammar, &lm.built, term, i, &mut vars)?;
    let bindings: Vec<DagId> = (0..vars.count())
        .map(|idx| {
            let sym = lm
                .built
                .engine
                .add_op(vars.name(idx).to_string(), vec![], vars.sort(idx));
            // Mark the atom as a variable for stability and groundness analysis. Same-sort canonical
            // order uses the interned source-name rank rather than symbol creation order.
            let rank = i.get(vars.name(idx)).map(|s| s.index()).unwrap_or(u32::MAX);
            lm.built
                .engine
                .set_symbol_class(sym, tnk_core::symbol::SymbolClass::Variable { rank });
            lm.built.engine.make_const(sym)
        })
        .collect();
    Ok(lm.built.engine.instantiate_bindings(&t, &bindings))
}

/// Whether a parse tree contains a variable (a [`Action::MakeVariable`] production) — the ground/open
/// dispatch for [`build_subject_dag`].
fn tree_has_var(tree: &PTree, g: &CompiledGrammar) -> bool {
    matches!(g.prods[tree.prod as usize].action, Action::MakeVariable(_))
        || tree.nt_children.iter().any(|c| tree_has_var(c, g))
}

/// Furthest token consumed by a valid partial command parse. `metaParse` reports this index through
/// `noParse(n)`.
pub fn command_parse_furthest(lm: &LoadedModule, i: &Interner, term: &[Token]) -> usize {
    let mut effort = ParseEffort::default();
    match earley::parse(&lm.grammar, term, Nt::Term, i, &mut effort) {
        Ok(chart) => chart.furthest(),
        Err(exceeded) => exceeded.at,
    }
}

/// Begin a rule-fair `rewrite` session over `term`. The caller drives the returned [`Rewriting`] and
/// stores it for `continue`.
pub fn rewrite_command(
    lm: &mut LoadedModule,
    i: &Interner,
    term: &ParsedCommandTerm<'_>,
) -> Result<Rewriting, String> {
    let dag = build_command_dag(lm, i, term)?;
    Ok(lm.built.engine.rewrite(dag))
}

/// Begin a position-fair `frewrite` session over `term`, with `gas` rule applications per position
/// per pass.
pub fn frewrite_command(
    lm: &mut LoadedModule,
    i: &Interner,
    term: &ParsedCommandTerm<'_>,
    gas: u64,
) -> Result<Rewriting, String> {
    let dag = build_command_dag(lm, i, term)?;
    Ok(lm.built.engine.frewrite(dag, gas))
}

/// Begin an object-message-fair `erewrite` session over `term`; `gas` controls the non-configuration
/// position-fair fallback.
pub fn erewrite_command(
    lm: &mut LoadedModule,
    i: &Interner,
    term: &ParsedCommandTerm<'_>,
    gas: u64,
) -> Result<Rewriting, String> {
    let dag = build_command_dag(lm, i, term)?;
    Ok(lm.built.engine.erewrite(dag, gas))
}

/// Begin a `search`: build the subject DAG, goal pattern, goal-variable table, and optional `such that`
/// condition, then open a [`Search`] for `arrow` up to `max_depth`. Returns the session and variables
/// needed to render bindings.
#[allow(clippy::too_many_arguments)]
pub fn search_command(
    lm: &mut LoadedModule,
    i: &Interner,
    subject: &ParsedCommandTerm<'_>,
    arrow: SearchArrow,
    pattern: &ParsedCommandTerm<'_>,
    such_that: Option<&[Token]>,
    max_depth: Option<u64>,
) -> Result<(Search, VarIndex), String> {
    // Goal pattern + such-that condition share one variable index.
    let mut vars = VarIndex::new();
    let pat = build_term(
        pattern.unambiguous_tree(i)?,
        &lm.grammar,
        &lm.built,
        pattern.tokens(),
        i,
        &mut vars,
    )?;
    let mut bound: BTreeSet<u32> = (0..vars.count()).collect();
    let cond = match such_that {
        Some(c) => parse_condition(c, &lm.grammar, &lm.built, i, &mut vars, &mut bound)?,
        None => Vec::new(),
    };
    let nr = vars.count();
    // Subject as a ground DAG (reset the counter so the search's rewrites start clean).
    lm.built.engine.reset_rewrites();
    lm.built.engine.begin_dedup();
    let subj = build_dag(
        subject.tree(),
        &lm.grammar,
        &mut lm.built.engine,
        lm.built.nat_zero,
        lm.built.nat_succ,
        subject.tokens(),
        i,
    );
    lm.built.engine.end_dedup();
    let subj = subj?;
    let arrow = match arrow {
        SearchArrow::One => Arrow::One,
        SearchArrow::Plus => Arrow::Plus,
        SearchArrow::Star => Arrow::Star,
        SearchArrow::Bang => Arrow::Bang,
    };
    let search = lm
        .built
        .engine
        .try_search(subj, pat, nr, cond, arrow, max_depth.map(|d| d as u32))
        .map_err(|fault| fault.to_string())?;
    Ok((search, vars))
}

pub struct SmtSearchCommand {
    pub search: SmtSearch,
    pub goal_variables: VarIndex,
    pub target_variable_count: u32,
}

/// Build an object-level symbolic rewrite search modulo SMT. The initial state and accumulated
/// constraint use genuine variable DAGs; the goal remains a static matcher pattern.
#[allow(clippy::too_many_arguments)]
pub fn smt_search_command(
    lm: &mut LoadedModule,
    i: &mut Interner,
    subject: &ParsedCommandTerm<'_>,
    arrow: SearchArrow,
    pattern: &ParsedCommandTerm<'_>,
    such_that: Option<&[Token]>,
    max_depth: Option<u64>,
) -> Result<SmtSearchCommand, String> {
    if matches!(arrow, SearchArrow::Bang) {
        return Err("=>! mode is not supported for searching modulo SMT".to_string());
    }

    let subject_tree = subject.tree();
    let pattern_tree = pattern.tree();

    let mut subject_variables = VarIndex::new();
    let mut goal_variables = VarIndex::new();
    let goal = build_term(
        pattern_tree,
        &lm.grammar,
        &lm.built,
        pattern.tokens(),
        i,
        &mut goal_variables,
    )?;
    let target_variable_count = goal_variables.count();
    let mut bound: BTreeSet<u32> = (0..target_variable_count).collect();
    let condition = match such_that {
        Some(tokens) => parse_condition(
            tokens,
            &lm.grammar,
            &lm.built,
            i,
            &mut goal_variables,
            &mut bound,
        )?,
        None => Vec::new(),
    };

    if !lm.smt_rewrite_valid || !lm.built.engine.valid_smt_goal(&goal) {
        return Err("module or goal does not satisfy SMT rewriting restrictions".to_string());
    }

    lm.built.engine.reset_rewrites();
    lm.built.engine.begin_dedup();
    let subject_dag = build_logic_dag(
        subject_tree,
        &lm.grammar,
        &mut lm.built.engine,
        lm.built.nat_zero,
        lm.built.nat_succ,
        subject.tokens(),
        i,
        &mut subject_variables,
    );
    lm.built.engine.end_dedup();
    let subject_dag = subject_dag?;

    let mut variable_names: Vec<String> = (0..subject_variables.count())
        .map(|slot| {
            command_variable_display_name(
                &lm.grammar,
                i,
                subject_variables.name(slot),
                subject_variables.sort(slot),
            )
        })
        .collect();
    let subject_variable_count = subject_variables.count();
    let mut goal_variable_dags = Vec::with_capacity(goal_variables.count() as usize);
    for slot in 0..goal_variables.count() {
        let source = goal_variables.name(slot);
        let base = source.split_once(':').map_or(source, |(base, _)| base);
        let code = i.intern(base).index();
        let global_slot = subject_variable_count + slot;
        goal_variable_dags.push(lm.built.engine.make_var(
            goal_variables.sort(slot),
            code,
            global_slot,
        ));
        variable_names.push(command_variable_display_name(
            &lm.grammar,
            i,
            source,
            goal_variables.sort(slot),
        ));
    }

    let initial_constraint = lm
        .built
        .engine
        .make_smt_constraint(&condition, &goal_variable_dags)?;
    let goal_smt_variables = (0..target_variable_count)
        .filter(|&slot| {
            lm.built
                .engine
                .smt_type(goal_variables.sort(slot))
                .is_some()
        })
        .map(|slot| (slot, goal_variable_dags[slot as usize]))
        .collect();
    let arrow = match arrow {
        SearchArrow::One => Arrow::One,
        SearchArrow::Plus => Arrow::Plus,
        SearchArrow::Star => Arrow::Star,
        SearchArrow::Bang => unreachable!("rejected above"),
    };
    let search = lm.built.engine.smt_search(
        subject_dag,
        initial_constraint,
        goal,
        target_variable_count,
        goal_smt_variables,
        arrow,
        max_depth.map(|depth| depth as u32),
        variable_names,
    );
    Ok(SmtSearchCommand {
        search,
        goal_variables,
        target_variable_count,
    })
}

pub struct NarrowCommand {
    pub search: tnk_core::narrow::NarrowSearch,
    pub variables: VarIndex,
    pub initial_variable_count: usize,
    /// Per-root source variables for a disjunction; `None` for the ordinary shared subject/goal scope.
    pub initial_variables: Option<Vec<VarIndex>>,
    pub initial_echoes: Vec<String>,
    pub subject_echo: String,
    pub goal_echo: String,
}

#[allow(clippy::too_many_arguments)]
pub fn narrow_command(
    lm: &mut LoadedModule,
    i: &mut Interner,
    subject: &[Token],
    arrow: SearchArrow,
    goal: &[Token],
    max_depth: Option<u64>,
    fold: bool,
    vfold: bool,
    path: bool,
    filter: bool,
    delay: bool,
) -> Result<NarrowCommand, String> {
    use tnk_core::fresh::VariableFamily;
    use tnk_core::narrow::{NarrowFold, NarrowGoal, NarrowOptions, NarrowSearchType};
    use tnk_core::unify::problem::VarSpec;

    let initial_parts = split_on_text(subject, "\\/", i);
    if initial_parts.len() > 1 {
        return narrow_disjunction_command(
            lm,
            i,
            &initial_parts,
            arrow,
            goal,
            max_depth,
            fold,
            vfold,
            path,
            filter,
            delay,
        );
    }

    let subject_tree = parse_forest_pick(subject, &lm.grammar, i)?;
    let goal_tree = parse_forest_pick(goal, &lm.grammar, i)?;
    let mut variables = VarIndex::new();
    let _ = build_term(
        &subject_tree,
        &lm.grammar,
        &lm.built,
        subject,
        i,
        &mut variables,
    )?;
    let initial_variable_count = variables.count() as usize;
    let goal_term = build_term(&goal_tree, &lm.grammar, &lm.built, goal, i, &mut variables)?;
    let goal_variable_names: Vec<_> = (0..variables.count())
        .map(|slot| {
            command_variable_display_name(
                &lm.grammar,
                i,
                variables.name(slot),
                variables.sort(slot),
            )
        })
        .collect();
    for slot in 0..variables.count() {
        let base = variables
            .name(slot)
            .split_once(':')
            .map_or(variables.name(slot), |(base, _)| base);
        i.intern(base);
    }
    let mut specs: Vec<_> = (0..variables.count())
        .map(|slot| {
            let source = variables.name(slot);
            let base = source.split_once(':').map_or(source, |(base, _)| base);
            let code = i.intern(base).index();
            VarSpec {
                sort: variables.sort(slot),
                name: maude_variable_name_rank(base, code),
            }
        })
        .collect();

    lm.built.engine.reset_rewrites();
    lm.built.engine.begin_dedup();
    let subject_dag = build_logic_dag(
        &subject_tree,
        &lm.grammar,
        &mut lm.built.engine,
        lm.built.nat_zero,
        lm.built.nat_succ,
        subject,
        i,
        &mut variables,
    );
    let goal_dag = build_logic_dag(
        &goal_tree,
        &lm.grammar,
        &mut lm.built.engine,
        lm.built.nat_zero,
        lm.built.nat_succ,
        goal,
        i,
        &mut variables,
    );
    lm.built.engine.end_dedup();
    let mut subject_dag = subject_dag?;
    let mut goal_dag = goal_dag?;
    // Command variable slots follow canonical DAG traversal rather than token order. AC and ACU
    // canonicalization can therefore reorder substitution keys.
    let mut variable_order = tnk_core::variant::variables_in_dag(&lm.built.engine, subject_dag);
    for slot in tnk_core::variant::variables_in_dag(&lm.built.engine, goal_dag) {
        if !variable_order.contains(&slot) {
            variable_order.push(slot);
        }
    }
    if variable_order.len() != specs.len() {
        return Err("narrowing variable table does not match the command terms".into());
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
                lm.built
                    .engine
                    .make_var(spec.sort, spec.name, new_slot[old]),
            )
        })
        .collect();
    subject_dag = tnk_core::unify::instantiate(&mut lm.built.engine, &remapping, subject_dag)
        .unwrap_or(subject_dag);
    goal_dag = tnk_core::unify::instantiate(&mut lm.built.engine, &remapping, goal_dag)
        .unwrap_or(goal_dag);
    specs = variable_order.iter().map(|&old| specs[old]).collect();
    variables.reorder(&variable_order);
    let echo_variables: Vec<_> = (0..variables.count())
        .map(|slot| {
            command_variable_display_name(
                &lm.grammar,
                i,
                variables.name(slot),
                variables.sort(slot),
            )
        })
        .collect();
    let subject_echo =
        print_pretty_with_variables(&lm.built, i, subject_dag, &echo_variables, false);
    let goal_echo = print_term(&lm.built, i, &goal_term, &goal_variable_names, false);

    let equations = executable_variant_equations(&mut lm.built, i);
    let rules = lm.built.engine.narrowing_rules().to_vec();
    let search_type = match arrow {
        SearchArrow::One => NarrowSearchType::One,
        SearchArrow::Plus => NarrowSearchType::AtLeastOne,
        SearchArrow::Star => NarrowSearchType::Any,
        SearchArrow::Bang => NarrowSearchType::NormalForm,
    };
    let options = NarrowOptions {
        search_type,
        max_depth: max_depth.map(|depth| depth as usize),
        filter,
        delay,
        fold: if vfold {
            NarrowFold::Variant
        } else if fold {
            NarrowFold::Match
        } else {
            NarrowFold::None
        },
        keep_history: false,
        keep_paths: path,
        respect_frozen: true,
    };
    let mut names = InternerNames(i);
    let mut env = tnk_core::unify::UnifyEnv {
        e: &mut lm.built.engine,
        names: &mut names,
    };
    let mut search = tnk_core::narrow::NarrowSearch::new(
        &mut env,
        subject_dag,
        specs[..initial_variable_count].to_vec(),
        &rules,
        equations,
        "0",
        options,
    )?;
    let goal = NarrowGoal::new(env.e, goal_dag, specs, initial_variable_count);
    search.set_goal(goal);
    let _ = VariableFamily::Unify;
    Ok(NarrowCommand {
        search,
        variables,
        initial_variable_count,
        initial_variables: None,
        initial_echoes: vec![subject_echo.clone()],
        subject_echo,
        goal_echo,
    })
}

#[allow(clippy::too_many_arguments)]
fn narrow_disjunction_command(
    lm: &mut LoadedModule,
    i: &mut Interner,
    initial_parts: &[&[Token]],
    arrow: SearchArrow,
    goal: &[Token],
    max_depth: Option<u64>,
    fold: bool,
    vfold: bool,
    path: bool,
    filter: bool,
    delay: bool,
) -> Result<NarrowCommand, String> {
    use tnk_core::narrow::{NarrowFold, NarrowGoal, NarrowOptions, NarrowSearchType};
    use tnk_core::unify::problem::VarSpec;

    let mut initials = Vec::with_capacity(initial_parts.len());
    let mut initial_variables = Vec::with_capacity(initial_parts.len());
    let mut initial_echoes = Vec::with_capacity(initial_parts.len());
    let mut seen_initial_variables: Vec<(String, tnk_core::sort::SortId, usize)> = Vec::new();

    lm.built.engine.reset_rewrites();
    for (root, &tokens) in initial_parts.iter().enumerate() {
        if tokens.is_empty() {
            return Err("empty initial state in narrowing disjunction".into());
        }
        let tree = parse_forest_pick(tokens, &lm.grammar, i)?;
        let mut variables = VarIndex::new();
        let source_term = build_term(&tree, &lm.grammar, &lm.built, tokens, i, &mut variables)?;
        for slot in 0..variables.count() {
            let source = variables.name(slot);
            let base = source.split_once(':').map_or(source, |(base, _)| base);
            if let Some((_, _, prior)) = seen_initial_variables
                .iter()
                .find(|(name, sort, _)| name == base && *sort == variables.sort(slot))
            {
                return Err(format!(
                    "variable {source} appears in both initial state {} and initial state {root}",
                    prior
                ));
            }
            seen_initial_variables.push((base.to_string(), variables.sort(slot), root));
            i.intern(base);
        }
        let specs: Vec<VarSpec> = (0..variables.count())
            .map(|slot| {
                let source = variables.name(slot);
                let base = source.split_once(':').map_or(source, |(base, _)| base);
                VarSpec {
                    sort: variables.sort(slot),
                    name: maude_variable_name_rank(base, i.intern(base).index()),
                }
            })
            .collect();
        let echo_variables: Vec<_> = (0..variables.count())
            .map(|slot| {
                command_variable_display_name(
                    &lm.grammar,
                    i,
                    variables.name(slot),
                    variables.sort(slot),
                )
            })
            .collect();
        let echo_term = normalize_trace_term(&mut lm.built, i, &variables, &source_term)
            .map_err(|fault| fault.to_string())?;
        let echo_term = restore_echo_variable_positions(&lm.built, &source_term, echo_term);
        let initial_echo = print_term(&lm.built, i, &echo_term, &echo_variables, false);
        lm.built.engine.begin_dedup();
        let dag = build_logic_dag(
            &tree,
            &lm.grammar,
            &mut lm.built.engine,
            lm.built.nat_zero,
            lm.built.nat_succ,
            tokens,
            i,
            &mut variables,
        );
        lm.built.engine.end_dedup();
        let (dag, specs) =
            canonicalize_narrow_command_dag(&mut lm.built.engine, dag?, specs, &mut variables)?;
        initial_echoes.push(initial_echo);
        initial_variables.push(variables);
        initials.push((dag, specs));
    }

    let goal_tree = parse_forest_pick(goal, &lm.grammar, i)?;
    let mut variables = VarIndex::new();
    let goal_term = build_term(&goal_tree, &lm.grammar, &lm.built, goal, i, &mut variables)?;
    let goal_variable_names: Vec<_> = (0..variables.count())
        .map(|slot| {
            command_variable_display_name(
                &lm.grammar,
                i,
                variables.name(slot),
                variables.sort(slot),
            )
        })
        .collect();
    for slot in 0..variables.count() {
        let source = variables.name(slot);
        let base = source.split_once(':').map_or(source, |(base, _)| base);
        if let Some((_, _, root)) = seen_initial_variables
            .iter()
            .find(|(name, sort, _)| name == base && *sort == variables.sort(slot))
        {
            return Err(format!(
                "sharing variable {source} between initial state {root} and the goal is not allowed"
            ));
        }
        i.intern(base);
    }
    let goal_specs: Vec<VarSpec> = (0..variables.count())
        .map(|slot| {
            let source = variables.name(slot);
            let base = source.split_once(':').map_or(source, |(base, _)| base);
            VarSpec {
                sort: variables.sort(slot),
                name: maude_variable_name_rank(base, i.intern(base).index()),
            }
        })
        .collect();
    lm.built.engine.begin_dedup();
    let goal_dag = build_logic_dag(
        &goal_tree,
        &lm.grammar,
        &mut lm.built.engine,
        lm.built.nat_zero,
        lm.built.nat_succ,
        goal,
        i,
        &mut variables,
    );
    lm.built.engine.end_dedup();
    let (goal_dag, goal_specs) = canonicalize_narrow_command_dag(
        &mut lm.built.engine,
        goal_dag?,
        goal_specs,
        &mut variables,
    )?;
    let goal_echo = print_term(&lm.built, i, &goal_term, &goal_variable_names, false);

    let equations = executable_variant_equations(&mut lm.built, i);
    let rules = lm.built.engine.narrowing_rules().to_vec();
    let search_type = match arrow {
        SearchArrow::One => NarrowSearchType::One,
        SearchArrow::Plus => NarrowSearchType::AtLeastOne,
        SearchArrow::Star => NarrowSearchType::Any,
        SearchArrow::Bang => NarrowSearchType::NormalForm,
    };
    let options = NarrowOptions {
        search_type,
        max_depth: max_depth.map(|depth| depth as usize),
        filter,
        delay,
        fold: if vfold {
            NarrowFold::Variant
        } else if fold {
            NarrowFold::Match
        } else {
            NarrowFold::None
        },
        keep_history: false,
        keep_paths: path,
        respect_frozen: true,
    };
    let mut names = InternerNames(i);
    let mut env = tnk_core::unify::UnifyEnv {
        e: &mut lm.built.engine,
        names: &mut names,
    };
    let mut search = tnk_core::narrow::NarrowSearch::new_many(
        &mut env, initials, &rules, equations, "0", options,
    )?;
    search.set_goal(NarrowGoal::new(env.e, goal_dag, goal_specs, 0));
    let subject_echo = initial_echoes.join(" \\/ ");
    Ok(NarrowCommand {
        search,
        variables,
        initial_variable_count: 0,
        initial_variables: Some(initial_variables),
        initial_echoes,
        subject_echo,
        goal_echo,
    })
}

fn canonicalize_narrow_command_dag(
    engine: &mut tnk_core::engine::Engine,
    dag: DagId,
    specs: Vec<tnk_core::unify::problem::VarSpec>,
    variables: &mut VarIndex,
) -> Result<(DagId, Vec<tnk_core::unify::problem::VarSpec>), String> {
    let ranked_names: Vec<_> = specs
        .iter()
        .enumerate()
        .map(|(slot, spec)| Some(engine.make_var(spec.sort, spec.name, slot as u32)))
        .collect();
    let dag = tnk_core::unify::instantiate(engine, &ranked_names, dag).unwrap_or(dag);
    let dag = engine
        .try_normalize_for_unify(dag)
        .map_err(|fault| fault.to_string())?;
    let variable_order = tnk_core::variant::variables_in_dag(engine, dag);
    if variable_order.len() != specs.len() {
        return Err("narrowing variable table does not match the command term".into());
    }
    let mut new_slot = vec![0u32; specs.len()];
    for (new, &old) in variable_order.iter().enumerate() {
        new_slot[old] = new as u32;
    }
    let remapping: Vec<_> = specs
        .iter()
        .enumerate()
        .map(|(old, spec)| Some(engine.make_var(spec.sort, spec.name, new_slot[old])))
        .collect();
    let dag = tnk_core::unify::instantiate(engine, &remapping, dag).unwrap_or(dag);
    let specs = variable_order.iter().map(|&old| specs[old]).collect();
    variables.reorder(&variable_order);
    Ok((dag, specs))
}

/// The matched-portion id (for `xmatch`) and binding ids of one match solution, captured while the
/// kernel [`tnk_core::engine::Solutions`] stream is live; rendered to text only after it drops (the
/// stream holds `&mut Engine`, the pretty-printer needs `&BuiltModule`).
struct RawSolution {
    /// One `DagId` per pattern variable, indexed `0..nr_vars`.
    bindings: Vec<DagId>,
    /// The matched portion (`xmatch` only): `None` prints no `Matched portion` line (plain `match`, or an
    /// `xmatch` whose subject carried no extension info); `Some(Whole)` prints `(whole)`; `Some(Portion)`
    /// prints the built sub-portion.
    portion: Option<MatchedPortion>,
}

/// Parse, build, and enumerate a `match`/`xmatch` command. Returns one rendered block per solution in
/// the kernel matcher's enumeration order; [`format_matchers`] adds the `Matcher N` framing. `xmatch`
/// blocks may begin with `Matched portion = …`; both forms then list `Var --> value` bindings.
///
/// The pattern is a kernel [`Term`]; the subject is built as a ground DAG and normalized. `xmatch`
/// permits a sub-part match with residue, while `match` requires the whole subject.
pub fn match_command(
    lm: &mut LoadedModule,
    i: &Interner,
    pattern: &[Token],
    subject: &[Token],
    xmatch: bool,
) -> Result<Vec<String>, String> {
    let mut vars = VarIndex::new();
    let pat = parse_build(pattern, &lm.grammar, &lm.built, i, &mut vars)?;
    let nr = vars.count();

    let subj_tree = parse_forest_pick(subject, &lm.grammar, i)?;
    // Preserve source-level DAG sharing before reduction.
    lm.built.engine.begin_dedup();
    let subj = build_dag(
        &subj_tree,
        &lm.grammar,
        &mut lm.built.engine,
        lm.built.nat_zero,
        lm.built.nat_succ,
        subject,
        i,
    );
    lm.built.engine.end_dedup();
    let subj = subj?;
    let subj = lm
        .built
        .engine
        .try_reduce(subj)
        .map_err(|fault| fault.to_string())?;

    // Enumerate while the stream borrows the engine, capturing only `DagId`s; render afterwards.
    let mut raws: Vec<RawSolution> = Vec::new();
    {
        let mut sols = lm.built.engine.match_solutions(pat, nr, subj, xmatch);
        while sols.advance() {
            let bindings = (0..nr)
                .map(|k| {
                    sols.binding(k)
                        .expect("the matcher binds every pattern variable")
                })
                .collect();
            let portion = if xmatch {
                sols.matched_portion_display()
            } else {
                None
            };
            raws.push(RawSolution { bindings, portion });
        }
    }

    Ok(raws
        .iter()
        .map(|r| render_solution(&lm.built, i, r, &vars))
        .collect())
}

/// Render the optional matched-portion line and substitution. Bindings follow first occurrence in the
/// pattern; a ground pattern prints `empty substitution`.
fn render_solution(m: &BuiltModule, i: &Interner, sol: &RawSolution, vars: &VarIndex) -> String {
    let mut lines: Vec<String> = Vec::new();
    match sol.portion {
        Some(MatchedPortion::Whole) => lines.push("Matched portion = (whole)".to_string()),
        Some(MatchedPortion::Portion(p)) => {
            lines.push(format!(
                "Matched portion = {}",
                print_pretty(m, i, p, false)
            ));
        }
        None => {}
    }
    if sol.bindings.is_empty() {
        lines.push("empty substitution".to_string());
    } else {
        for (k, &b) in sol.bindings.iter().enumerate() {
            lines.push(format!(
                "{} --> {}",
                vars.name(k as u32),
                print_pretty(m, i, b, false)
            ));
        }
    }
    lines.join("\n")
}

/// Wrap rendered `match`/`xmatch` solution blocks: `No match.` when empty, otherwise `Matcher N`
/// sections separated by blank lines.
pub fn format_matchers(blocks: &[String]) -> String {
    if blocks.is_empty() {
        return "No match.".to_string();
    }
    blocks
        .iter()
        .enumerate()
        .map(|(n, b)| format!("Matcher {}\n{}", n + 1, b))
        .collect::<Vec<_>>()
        .join("\n\n")
}

/// A [`NameCodes`](tnk_core::unify::NameCodes) source backed by the session interner. Fresh and user
/// variable names share one code space, which supplies canonical variable ordering.
pub struct InternerNames<'a>(pub &'a mut Interner);
impl tnk_core::unify::NameCodes for InternerNames<'_> {
    fn code(&mut self, name: &str) -> u32 {
        self.0.intern(name).index()
    }
}

/// Reserved relative ranks for conventional standing variable names. Other names retain session
/// interner order after the reserved range.
pub fn maude_variable_name_rank(name: &str, fallback: u32) -> u32 {
    const STANDING: &[&str] = &[
        "E", "A", "B", "C", "I", "J", "N", "M", "K", "Z", "Q", "R", "X", "Y", "L", "S", "P", "D",
        "V", "U", "H", "T", "O", "F", "G", "W",
    ];
    STANDING
        .iter()
        .position(|&candidate| candidate == name)
        .map_or(0x100u32.saturating_add(fallback), |rank| rank as u32)
}
/// Resolve `X:Sort` to the declared variable `X` when both name and sort match, omitting the on-the-fly
/// sort suffix from command echoes and substitution keys.
pub fn command_variable_display_name(
    grammar: &CompiledGrammar,
    i: &Interner,
    source: &str,
    sort: SortId,
) -> String {
    let Some((base, _)) = source.split_once(':') else {
        return source.to_string();
    };
    let declared = grammar.prods.iter().any(|prod| {
        matches!(prod.action, Action::MakeVariable(s) if s == sort)
            && matches!(
                prod.rhs.as_slice(),
                [GSym::T(Terminal::Tok(sym))] if i.resolve(*sym) == base
            )
    });
    if declared {
        base.to_string()
    } else {
        source.to_string()
    }
}

/// The built pieces of a `unify` command: the pretty-printed echo body (`T1 =? T2 /\ …`, without
/// the `unify in M :` frame or trailing ` .`), input variable print names in slot order, and the resumable
/// [`UnifyProblem`](tnk_core::unify::problem::UnifyProblem).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UnifyReadiness {
    Ready,
    UnsafeVariableName,
    UnsupportedTheory,
}

pub struct UnifyCommand {
    pub echo: String,
    pub var_names: Vec<String>,
    /// Whether enumeration can start. Unsafe fresh-family names and unsupported theories are
    /// distinguished from a supported problem that has no unifier.
    pub readiness: UnifyReadiness,
    pub problem: tnk_core::unify::problem::UnifyProblem,
    pub(crate) source_var_names: Vec<String>,
    pub(crate) equations: Vec<(DagId, DagId)>,
    pub(crate) specs: Vec<tnk_core::unify::problem::VarSpec>,
    pub(crate) vars: VarIndex,
}

fn build_unify_echo_term(
    tree: &PTree,
    lm: &LoadedModule,
    tokens: &[Token],
    i: &Interner,
    vars: &mut VarIndex,
) -> Result<Term, String> {
    build_term(tree, &lm.grammar, &lm.built, tokens, i, vars)
}

/// Build a `unify` command: parse each pair with temporary source-order slots, normalize every side
/// by its theory, then use the resulting variable order for the resumable problem and displayed keys.
pub fn unify_command(
    lm: &mut LoadedModule,
    i: &mut Interner,
    body: &[Token],
) -> Result<UnifyCommand, String> {
    use tnk_core::fresh::VariableFamily;
    use tnk_core::unify::problem::{UnifyProblem, VarSpec};

    let conjs = split_on_text(body, "/\\", i);
    let sides: Vec<_> = conjs.iter().map(|c| split_on_text(c, "=?", i)).collect();
    if sides.iter().any(|s| s.len() != 2) {
        return Err("unify: each conjunct must be `T1 =? T2`".to_string());
    }

    let mut vars = VarIndex::new();
    let mut equations = Vec::with_capacity(sides.len());
    let mut echo_pairs = Vec::with_capacity(sides.len());
    for side in &sides {
        let lhs_tree = parse_forest_pick(side[0], &lm.grammar, i)?;
        // Establish source-order variable slots before the DAG constructor canonicalizes commutative args.
        let lhs_echo = build_unify_echo_term(&lhs_tree, lm, side[0], i, &mut vars)?;
        // Intern each on-the-fly `X:Sort` base before the DAG builder records its name id.
        for idx in 0..vars.count() {
            let name = vars.name(idx);
            let base = name.split_once(':').map_or(name, |(base, _)| base);
            i.intern(base);
        }
        let lhs = build_logic_dag(
            &lhs_tree,
            &lm.grammar,
            &mut lm.built.engine,
            lm.built.nat_zero,
            lm.built.nat_succ,
            side[0],
            i,
            &mut vars,
        )?;
        let rhs_tree = parse_forest_pick(side[1], &lm.grammar, i)?;
        let rhs_echo = build_unify_echo_term(&rhs_tree, lm, side[1], i, &mut vars)?;
        for idx in 0..vars.count() {
            let name = vars.name(idx);
            let base = name.split_once(':').map_or(name, |(base, _)| base);
            i.intern(base);
        }
        let rhs = build_logic_dag(
            &rhs_tree,
            &lm.grammar,
            &mut lm.built.engine,
            lm.built.nat_zero,
            lm.built.nat_succ,
            side[1],
            i,
            &mut vars,
        )?;
        echo_pairs.push((lhs_echo, rhs_echo));
        equations.push((lhs, rhs));
    }

    let source_var_names: Vec<String> = (0..vars.count())
        .map(|idx| command_variable_display_name(&lm.grammar, i, vars.name(idx), vars.sort(idx)))
        .collect();
    let echo = echo_pairs
        .iter()
        .map(|(lhs, rhs)| {
            format!(
                "{} =? {}",
                print_term(&lm.built, i, lhs, &source_var_names, false),
                print_term(&lm.built, i, rhs, &source_var_names, false)
            )
        })
        .collect::<Vec<_>>()
        .join(" /\\ ");
    let specs: Vec<VarSpec> = (0..vars.count())
        .map(|idx| {
            let source_name = vars.name(idx);
            let base = source_name
                .split_once(':')
                .map_or(source_name, |(base, _)| base);
            let code = i.intern(base).index();
            VarSpec {
                sort: vars.sort(idx),
                name: maude_variable_name_rank(base, code),
            }
        })
        .collect();

    let namegen = tnk_core::fresh::FreshVariableGenerator::new();
    let names_ok = source_var_names.iter().all(|name| {
        let bare = name.split(':').next().unwrap_or(name);
        !namegen.variable_name_conflict(bare, None)
    });
    let source_equations = equations.clone();
    let source_specs = specs.clone();
    let mut names = InternerNames(i);
    let mut env = tnk_core::unify::UnifyEnv {
        e: &mut lm.built.engine,
        names: &mut names,
    };
    let problem = UnifyProblem::try_new(&mut env, equations, specs, VariableFamily::Unify, "0")
        .map_err(|fault| fault.to_string())?;
    let readiness = if !names_ok {
        UnifyReadiness::UnsafeVariableName
    } else if !problem.problem_okay() {
        UnifyReadiness::UnsupportedTheory
    } else {
        UnifyReadiness::Ready
    };
    let var_names = problem
        .original_variable_order()
        .iter()
        .map(|&old| source_var_names[old].clone())
        .collect();
    Ok(UnifyCommand {
        echo,
        var_names,
        readiness,
        problem,
        source_var_names,
        equations: source_equations,
        specs: source_specs,
        vars,
    })
}

/// Render one unifier's substitution as `name --> value` lines, or `empty substitution`.
pub fn render_unifier(
    m: &BuiltModule,
    i: &Interner,
    var_names: &[String],
    values: &[DagId],
) -> String {
    if values.is_empty() {
        return "empty substitution".to_string();
    }
    values
        .iter()
        .enumerate()
        .map(|(k, &v)| format!("{} --> {}", var_names[k], print_pretty(m, i, v, false)))
        .collect::<Vec<_>>()
        .join("\n")
}

/// Parsed state for a resumable `get variants` command.
pub struct VariantCommand {
    pub echo: String,
    pub var_names: Vec<String>,
    pub names_ok: bool,
    pub search: VariantSearch,
}

/// Parsed state for a plain or filtered variant-unification command.
pub struct VariantUnifyCommand {
    pub echo: String,
    pub var_names: Vec<String>,
    pub names_ok: bool,
    pub pair_count: usize,
    pub search: VariantSearch,
}

/// Parsed state for variant matching: an irredundant pattern-variant search plus the grounded
/// subject matched against each surviving variant.
pub struct VariantMatchCommand {
    pub echo: String,
    pub var_names: Vec<String>,
    pub names_ok: bool,
    pub search: VariantSearch,
    pub subject: DagId,
    pub restorations: Vec<(DagId, DagId)>,
    pub fresh_base: String,
}

fn collect_term_variable_sorts(term: &Term, sorts: &mut Vec<Option<SortId>>) {
    match term {
        Term::Var(v) => {
            let slot = v.index as usize;
            if sorts.len() <= slot {
                sorts.resize(slot + 1, None);
            }
            sorts[slot] = Some(v.sort);
        }
        Term::Op { args, .. } => {
            for arg in args {
                collect_term_variable_sorts(arg, sorts);
            }
        }
        Term::Iter { arg, .. } => collect_term_variable_sorts(arg, sorts),
        Term::Na { .. } => {}
    }
}

pub fn executable_variant_equations(m: &mut BuiltModule, i: &mut Interner) -> Vec<VariantEquation> {
    use tnk_core::unify::problem::VarSpec;

    let traces = &m.eq_traces;
    let engine = &mut m.engine;
    traces
        .iter()
        .enumerate()
        .filter(|(_, trace)| trace.variant && !trace.nonexec)
        .map(|(id, trace)| {
            let mut sorts = Vec::new();
            collect_term_variable_sorts(&trace.lhs, &mut sorts);
            collect_term_variable_sorts(&trace.rhs, &mut sorts);
            let variables: Vec<_> = sorts
                .into_iter()
                .enumerate()
                .map(|(slot, sort)| {
                    let source = trace.var_names.get(slot).map(String::as_str).unwrap_or("X");
                    let base = source.split_once(':').map_or(source, |(base, _)| base);
                    let code = i.intern(base).index();
                    VarSpec {
                        sort: sort.expect("each statement variable occurs in its lhs or rhs"),
                        name: maude_variable_name_rank(base, code),
                    }
                })
                .collect();
            compile_variant_equation(engine, id as u32, &trace.lhs, &trace.rhs, variables)
        })
        .collect()
}

/// Build a variant target, irreducibility blockers, and executable `[variant]` equations. Target slots
/// are reordered only after theory canonicalization.
pub fn variant_command(
    lm: &mut LoadedModule,
    i: &mut Interner,
    term: &[Token],
    irreducible: Option<&[Token]>,
    irredundant: bool,
) -> Result<VariantCommand, String> {
    use tnk_core::fresh::{FreshVariableGenerator, VariableFamily};
    use tnk_core::unify::problem::VarSpec;

    let mut vars = VarIndex::new();
    let tree = parse_forest_pick(term, &lm.grammar, i)?;
    let _source_term = build_term(&tree, &lm.grammar, &lm.built, term, i, &mut vars)?;
    for slot in 0..vars.count() {
        let source = vars.name(slot);
        let base = source.split_once(':').map_or(source, |(base, _)| base);
        i.intern(base);
    }
    let target = build_logic_dag(
        &tree,
        &lm.grammar,
        &mut lm.built.engine,
        lm.built.nat_zero,
        lm.built.nat_succ,
        term,
        i,
        &mut vars,
    )?;
    let echo_term = tnk_core::variant::term_from_dag_slots(&lm.built.engine, target);
    let target_variables = vars.count();

    let mut blocker_terms = Vec::new();
    let mut blockers = Vec::new();
    if let Some(body) = irreducible {
        for part in split_on_text(body, ",", i) {
            let tree = parse_forest_pick(part, &lm.grammar, i)?;
            let source_term = build_term(&tree, &lm.grammar, &lm.built, part, i, &mut vars)?;
            for slot in 0..vars.count() {
                let source = vars.name(slot);
                let base = source.split_once(':').map_or(source, |(base, _)| base);
                i.intern(base);
            }
            let blocker = build_logic_dag(
                &tree,
                &lm.grammar,
                &mut lm.built.engine,
                lm.built.nat_zero,
                lm.built.nat_succ,
                part,
                i,
                &mut vars,
            )?;
            blocker_terms.push(source_term);
            blockers.push(blocker);
        }
    }

    let source_var_names: Vec<String> = (0..vars.count())
        .map(|slot| command_variable_display_name(&lm.grammar, i, vars.name(slot), vars.sort(slot)))
        .collect();
    let mut echo = print_term(&lm.built, i, &echo_term, &source_var_names, false);
    if !blocker_terms.is_empty() {
        let blockers = blocker_terms
            .iter()
            .map(|term| print_term(&lm.built, i, term, &source_var_names, false))
            .collect::<Vec<_>>()
            .join(", ");
        echo.push_str(" such that ");
        echo.push_str(&blockers);
        echo.push_str(" irreducible");
    }
    let specs: Vec<VarSpec> = (0..target_variables)
        .map(|slot| {
            let source = vars.name(slot);
            let base = source.split_once(':').map_or(source, |(base, _)| base);
            let code = i.intern(base).index();
            VarSpec {
                sort: vars.sort(slot),
                name: maude_variable_name_rank(base, code),
            }
        })
        .collect();
    let namegen = FreshVariableGenerator::new();
    let names_ok = source_var_names.iter().all(|name| {
        let bare = name.split(':').next().unwrap_or(name);
        !namegen.variable_name_conflict(bare, None)
    });
    let equations = executable_variant_equations(&mut lm.built, i);
    lm.built.engine.reset_rewrites();
    let mut names = InternerNames(i);
    let mut env = tnk_core::unify::UnifyEnv {
        e: &mut lm.built.engine,
        names: &mut names,
    };
    let mode = if irredundant {
        VariantMode::Irredundant
    } else {
        VariantMode::Incremental
    };
    let search = VariantSearch::new(
        &mut env,
        target,
        specs,
        blockers,
        equations,
        mode,
        None::<VariableFamily>,
        "0",
    )?;
    let var_names = search
        .original_variable_order()
        .iter()
        .map(|&old| source_var_names[old].clone())
        .collect();
    Ok(VariantCommand {
        echo,
        var_names,
        names_ok,
        search,
    })
}

pub fn variant_unify_command(
    lm: &mut LoadedModule,
    i: &mut Interner,
    body: &[Token],
    irreducible: Option<&[Token]>,
    _filtered: bool,
) -> Result<VariantUnifyCommand, String> {
    use tnk_core::fresh::VariableFamily;

    let UnifyCommand {
        mut echo,
        readiness,
        problem,
        source_var_names,
        equations,
        specs,
        mut vars,
        ..
    } = unify_command(lm, i, body)?;
    let names_ok = readiness != UnifyReadiness::UnsafeVariableName;
    drop(problem);
    let pair_count = equations.len();
    if pair_count == 0 {
        return Err("variant unify: expected at least one unification pair".to_string());
    }

    let mut blockers = Vec::new();
    let mut blocker_echoes = Vec::new();
    if let Some(tokens) = irreducible {
        for part in split_on_text(tokens, ",", i) {
            let tree = parse_forest_pick(part, &lm.grammar, i)?;
            let echo_term = build_term(&tree, &lm.grammar, &lm.built, part, i, &mut vars)?;
            for slot in 0..vars.count() {
                let source = vars.name(slot);
                let base = source.split_once(':').map_or(source, |(base, _)| base);
                i.intern(base);
            }
            let dag = build_logic_dag(
                &tree,
                &lm.grammar,
                &mut lm.built.engine,
                lm.built.nat_zero,
                lm.built.nat_succ,
                part,
                i,
                &mut vars,
            )?;
            blocker_echoes.push(print_term(
                &lm.built,
                i,
                &echo_term,
                &source_var_names,
                false,
            ));
            blockers.push(dag);
        }
    }
    if !blocker_echoes.is_empty() {
        echo.push_str(" such that ");
        echo.push_str(&blocker_echoes.join(", "));
        echo.push_str(" irreducible");
    }

    let target = if pair_count == 1 {
        let (lhs, rhs) = equations[0];
        let domains = [lhs, rhs]
            .map(|dag| {
                let sort = lm.built.engine.sort_of(dag);
                let kind = lm.built.engine.sorts().kind_of(sort);
                lm.built.engine.sorts().error_sort(kind)
            })
            .to_vec();
        let result_sort = domains[0];
        let pair_symbol = lm
            .built
            .engine
            .add_op("$variant-unification-pair", domains, result_sort);
        lm.built.engine.make_free(pair_symbol, vec![lhs, rhs])
    } else {
        let lhs: Vec<_> = equations.iter().map(|&(lhs, _)| lhs).collect();
        let rhs: Vec<_> = equations.iter().map(|&(_, rhs)| rhs).collect();
        let tuple_sort = {
            let kind = lm
                .built
                .engine
                .sorts()
                .kind_of(lm.built.engine.sort_of(lhs[0]));
            lm.built.engine.sorts().error_sort(kind)
        };
        let lhs_domains = lhs
            .iter()
            .map(|&dag| {
                let kind = lm
                    .built
                    .engine
                    .sorts()
                    .kind_of(lm.built.engine.sort_of(dag));
                lm.built.engine.sorts().error_sort(kind)
            })
            .collect();
        let rhs_domains = rhs
            .iter()
            .map(|&dag| {
                let kind = lm
                    .built
                    .engine
                    .sorts()
                    .kind_of(lm.built.engine.sort_of(dag));
                lm.built.engine.sorts().error_sort(kind)
            })
            .collect();
        let lhs_symbol =
            lm.built
                .engine
                .add_op("$variant-unification-lhs", lhs_domains, tuple_sort);
        let rhs_symbol =
            lm.built
                .engine
                .add_op("$variant-unification-rhs", rhs_domains, tuple_sort);
        let lhs = lm.built.engine.make_free(lhs_symbol, lhs);
        let rhs = lm.built.engine.make_free(rhs_symbol, rhs);
        let pair_symbol = lm.built.engine.add_op(
            "$variant-unification-pair",
            vec![tuple_sort, tuple_sort],
            tuple_sort,
        );
        lm.built.engine.make_free(pair_symbol, vec![lhs, rhs])
    };
    let target = lm
        .built
        .engine
        .try_normalize_for_unify(target)
        .map_err(|fault| fault.to_string())?;
    let equations = executable_variant_equations(&mut lm.built, i);
    lm.built.engine.reset_rewrites();
    let mut names = InternerNames(i);
    let mut env = tnk_core::unify::UnifyEnv {
        e: &mut lm.built.engine,
        names: &mut names,
    };
    let mode = VariantMode::Incremental;
    let mut search = VariantSearch::new(
        &mut env,
        target,
        specs,
        blockers,
        equations,
        mode,
        None::<VariableFamily>,
        "0",
    )?;
    search.enable_unification(env.e, pair_count);
    let var_names = search
        .original_variable_order()
        .iter()
        .map(|&old| source_var_names[old].clone())
        .collect();
    Ok(VariantUnifyCommand {
        echo,
        var_names,
        names_ok,
        pair_count,
        search,
    })
}

pub fn variant_match_command(
    lm: &mut LoadedModule,
    i: &mut Interner,
    pattern: &[Token],
    subject: &[Token],
    irreducible: Option<&[Token]>,
) -> Result<VariantMatchCommand, String> {
    use tnk_core::fresh::{FreshVariableGenerator, VariableFamily};
    use tnk_core::unify::problem::VarSpec;

    let mut pattern_vars = VarIndex::new();
    let pattern_tree = parse_forest_pick(pattern, &lm.grammar, i)?;
    let pattern_term = build_term(
        &pattern_tree,
        &lm.grammar,
        &lm.built,
        pattern,
        i,
        &mut pattern_vars,
    )?;
    for slot in 0..pattern_vars.count() {
        let source = pattern_vars.name(slot);
        i.intern(source.split_once(':').map_or(source, |(base, _)| base));
    }
    let pattern_dag = build_logic_dag(
        &pattern_tree,
        &lm.grammar,
        &mut lm.built.engine,
        lm.built.nat_zero,
        lm.built.nat_succ,
        pattern,
        i,
        &mut pattern_vars,
    )?;
    let target_variables = pattern_vars.count();
    let source_var_names: Vec<_> = (0..target_variables)
        .map(|slot| {
            command_variable_display_name(
                &lm.grammar,
                i,
                pattern_vars.name(slot),
                pattern_vars.sort(slot),
            )
        })
        .collect();

    let mut subject_vars = VarIndex::new();
    let subject_tree = parse_forest_pick(subject, &lm.grammar, i)?;
    let subject_term = build_term(
        &subject_tree,
        &lm.grammar,
        &lm.built,
        subject,
        i,
        &mut subject_vars,
    )?;
    for slot in 0..subject_vars.count() {
        let source = subject_vars.name(slot);
        i.intern(source.split_once(':').map_or(source, |(base, _)| base));
    }
    let subject_dag = build_logic_dag(
        &subject_tree,
        &lm.grammar,
        &mut lm.built.engine,
        lm.built.nat_zero,
        lm.built.nat_succ,
        subject,
        i,
        &mut subject_vars,
    )?;
    let subject_var_names: Vec<_> = (0..subject_vars.count())
        .map(|slot| {
            command_variable_display_name(
                &lm.grammar,
                i,
                subject_vars.name(slot),
                subject_vars.sort(slot),
            )
        })
        .collect();
    let fresh_base = subject_var_names
        .iter()
        .filter_map(|name| {
            name.split(':')
                .next()
                .and_then(|bare| bare.strip_prefix('#'))
                .and_then(|digits| digits.parse::<u64>().ok())
        })
        .max()
        .unwrap_or(0)
        .to_string();
    let (subject_dag, mut restorations) =
        tnk_core::variant::ground_subject_variables(&mut lm.built.engine, subject_dag);
    for (index, (_, variable)) in restorations.iter_mut().enumerate() {
        let sort = lm.built.engine.sort_of(*variable);
        let display = subject_var_names
            .get(index)
            .map(String::as_str)
            .unwrap_or("X");
        *variable = lm
            .built
            .engine
            .make_var(sort, i.intern(display).index(), index as u32);
    }

    let mut blockers = Vec::new();
    let mut blocker_echoes = Vec::new();
    if let Some(tokens) = irreducible {
        for part in split_on_text(tokens, ",", i) {
            let tree = parse_forest_pick(part, &lm.grammar, i)?;
            let term = build_term(&tree, &lm.grammar, &lm.built, part, i, &mut pattern_vars)?;
            let dag = build_logic_dag(
                &tree,
                &lm.grammar,
                &mut lm.built.engine,
                lm.built.nat_zero,
                lm.built.nat_succ,
                part,
                i,
                &mut pattern_vars,
            )?;
            blocker_echoes.push(print_term(&lm.built, i, &term, &source_var_names, false));
            blockers.push(dag);
        }
    }

    let mut echo = format!(
        "{} <=? {}",
        print_term(&lm.built, i, &pattern_term, &source_var_names, false),
        print_term(&lm.built, i, &subject_term, &subject_var_names, false)
    );
    if !blocker_echoes.is_empty() {
        echo.push_str(" such that ");
        echo.push_str(&blocker_echoes.join(", "));
        echo.push_str(" irreducible");
    }
    let specs: Vec<VarSpec> = (0..target_variables)
        .map(|slot| {
            let source = pattern_vars.name(slot);
            let base = source.split_once(':').map_or(source, |(base, _)| base);
            VarSpec {
                sort: pattern_vars.sort(slot),
                name: maude_variable_name_rank(base, i.intern(base).index()),
            }
        })
        .collect();
    let namegen = FreshVariableGenerator::new();
    let names_ok = source_var_names.iter().all(|name| {
        let bare = name.split(':').next().unwrap_or(name);
        !namegen.variable_name_conflict(bare, None)
    });
    let equations = executable_variant_equations(&mut lm.built, i);
    lm.built.engine.reset_rewrites();
    let mut names = InternerNames(i);
    let mut env = tnk_core::unify::UnifyEnv {
        e: &mut lm.built.engine,
        names: &mut names,
    };
    let search = VariantSearch::new(
        &mut env,
        pattern_dag,
        specs,
        blockers,
        equations,
        VariantMode::Irredundant,
        None::<VariableFamily>,
        &fresh_base,
    )?;
    let var_names = search
        .original_variable_order()
        .iter()
        .map(|&old| source_var_names[old].clone())
        .collect();
    Ok(VariantMatchCommand {
        echo,
        var_names,
        names_ok,
        search,
        subject: subject_dag,
        restorations,
        fresh_base,
    })
}
#[cfg(test)]
mod tests {
    use super::*;

    /// One expected command result for the fixture-result harness.
    enum Expect {
        /// A reduce expectation: result sort, equivalent surface term, and rewrite count.
        Reduce {
            sort: &'static str,
            term: &'static str,
            rewrites: u64,
        },
        /// A `match`/`xmatch`: the expected solution blocks (each the `Var --> value` lines, or for
        /// `xmatch` the `Matched portion = …` line + substitution), rendered by [`render_solution`].
        /// Compared as a set because solution enumeration order is not part of this harness contract.
        Match(&'static [&'static str]),
    }

    const fn e(sort: &'static str, term: &'static str, rewrites: u64) -> Expect {
        Expect::Reduce {
            sort,
            term,
            rewrites,
        }
    }

    const fn mat(blocks: &'static [&'static str]) -> Expect {
        Expect::Match(blocks)
    }

    /// A command's tokens, owned so the loop can `&mut`-borrow `loaded.modules` while iterating.
    enum Cmd {
        Reduce(Vec<Token>),
        Match {
            pattern: Vec<Token>,
            subject: Vec<Token>,
            xmatch: bool,
        },
    }

    /// Load `src` and check each reduce result's sort, count, and value or each match result's complete
    /// rendered solution set.
    fn check_results(src: &str, expected: &[Expect]) {
        let mut loaded = load_source(src).expect("load source");
        let cmds: Vec<(usize, Cmd)> = loaded
            .commands
            .iter()
            .map(|(m, c)| {
                let cmd = match c {
                    Command::Reduce { term, .. } => Cmd::Reduce(term.clone()),
                    Command::Match {
                        pattern,
                        subject,
                        xmatch,
                        ..
                    } => Cmd::Match {
                        pattern: pattern.clone(),
                        subject: subject.clone(),
                        xmatch: *xmatch,
                    },
                    _ => panic!("the fixture-result harness covers only reduce and match commands"),
                };
                (*m, cmd)
            })
            .collect();
        assert_eq!(cmds.len(), expected.len(), "command count");

        for (idx, ((m, cmd), exp)) in cmds.iter().zip(expected).enumerate() {
            match (cmd, exp) {
                (
                    Cmd::Reduce(term),
                    Expect::Reduce {
                        sort,
                        term: eterm,
                        rewrites,
                    },
                ) => {
                    let parsed = parse_command_term(&loaded.modules[*m], &loaded.interner, term)
                        .unwrap_or_else(|err| panic!("command {idx}: {err}"));
                    let (got, rw) =
                        reduce_command(&mut loaded.modules[*m], &loaded.interner, &parsed)
                            .unwrap_or_else(|err| panic!("command {idx}: {err}"));
                    {
                        let eng = &loaded.modules[*m].built.engine;
                        assert_eq!(
                            eng.sorts().name(eng.sort_of(got)),
                            *sort,
                            "command {idx} sort"
                        );
                    }
                    assert_eq!(rw, *rewrites, "command {idx} rewrite count");

                    let exp_toks = tokenize(eterm, &mut loaded.interner);
                    let expected_parsed =
                        parse_command_term(&loaded.modules[*m], &loaded.interner, &exp_toks)
                            .unwrap_or_else(|err| {
                                panic!("command {idx} expected `{eterm}`: {err}")
                            });
                    let (want, _) =
                        reduce_command(&mut loaded.modules[*m], &loaded.interner, &expected_parsed)
                            .unwrap_or_else(|err| {
                                panic!("command {idx} expected `{eterm}`: {err}")
                            });
                    let eng = &loaded.modules[*m].built.engine;
                    assert!(
                        eng.deep_equal(got, want),
                        "command {idx} value: expected `{eterm}`"
                    );
                }
                (
                    Cmd::Match {
                        pattern,
                        subject,
                        xmatch,
                    },
                    Expect::Match(blocks),
                ) => {
                    let mut got = match_command(
                        &mut loaded.modules[*m],
                        &loaded.interner,
                        pattern,
                        subject,
                        *xmatch,
                    )
                    .unwrap_or_else(|err| panic!("command {idx}: {err}"));
                    got.sort();
                    let mut want: Vec<String> = blocks.iter().map(|s| (*s).to_string()).collect();
                    want.sort();
                    assert_eq!(got, want, "command {idx} match solution set");
                }
                _ => panic!("command {idx}: command kind does not match its expectation"),
            }
        }
    }

    macro_rules! fixture_file {
        ($name:expr) => {
            include_str!(concat!(
                env!("CARGO_MANIFEST_DIR"),
                "/../../conformance/",
                $name
            ))
        };
    }

    #[test]
    fn iter_commands_produce_expected_results() {
        check_results(
            fixture_file!("iter.maude"),
            &[
                e("Zero", "0", 0),
                e("NzNat", "s 0", 0),
                e("NzNat", "s 0", 2),
                e("NzNat", "s 0", 2), // ITER-VAR
                e("NzNat", "s 0", 1),
            ],
        );
    }

    #[test]
    fn compact_prefix_iteration_command_stays_one_iter_node() {
        let mut loaded = load_source(
            "fmod PREFIX-ITER is
               sort Nat .
               op 0 : -> Nat [ctor] .
               op s : Nat -> Nat [ctor iter] .
             endfm",
        )
        .expect("load prefix iter module");
        let term = tokenize("s^1000000(0)", &mut loaded.interner);
        let lm = &mut loaded.modules[0];

        let parsed = parse_command_term(lm, &loaded.interner, &term).expect("parse command");
        assert_eq!(
            command_echo(lm, &loaded.interner, &parsed, false).expect("command echo"),
            "s^1000000(0)"
        );
        let (result, rewrites) =
            reduce_command(lm, &loaded.interner, &parsed).expect("reduce compact prefix iteration");
        assert_eq!(rewrites, 0);
        assert_eq!(
            lm.built
                .engine
                .sorts()
                .name(lm.built.engine.sort_of(result)),
            "Nat"
        );
        assert_eq!(
            crate::pretty::print_raw(&lm.built, &loaded.interner, result),
            "s^1000000(0)",
            "round-trip printer must not expand the million-count iter node"
        );
        match lm.built.engine.node(result).repr() {
            tnk_core::dag::NodeRepr::Iter { count, arg } => {
                assert_eq!(count, "1000000");
                assert!(matches!(
                    lm.built.engine.node(arg).repr(),
                    tnk_core::dag::NodeRepr::App
                ));
            }
            other => panic!("expected one compact iter node, got {other:?}"),
        }
    }

    #[test]
    fn prefix_and_mixfix_iter_notation_follow_overloaded_ditto_syntax() {
        let mut loaded = load_source(
            "fmod ITER-SYNTAX is
               sorts Small Big .
               subsort Small < Big .
               op a : -> Small [ctor] .
               op g : Big -> Big [ctor iter] .
               op g : Small -> Small [ditto] .
               op s_ : Big -> Big [ctor iter] .
               op s_ : Small -> Small [ditto] .
             endfm",
        )
        .expect("load overloaded iter module");

        for (input, echo) in [
            ("g^1(a)", "g(a)"),
            ("g^2(a)", "g^2(a)"),
            ("s_^1(a)", "s a"),
            ("s_^3(a)", "s_^3(a)"),
        ] {
            let term = tokenize(input, &mut loaded.interner);
            let lm = &mut loaded.modules[0];
            let parsed = parse_command_term(lm, &loaded.interner, &term).expect("parse command");
            assert_eq!(
                command_echo(lm, &loaded.interner, &parsed, false).expect("iter command echo"),
                echo,
                "expected print for `{input}`"
            );
            let (result, rewrites) =
                reduce_command(lm, &loaded.interner, &parsed).expect("reduce overloaded iter");
            assert_eq!(rewrites, 0);
            assert_eq!(
                lm.built
                    .engine
                    .sorts()
                    .name(lm.built.engine.sort_of(result)),
                "Small",
                "ditto declaration selects the Small sort for `{input}`"
            );
        }
    }

    #[test]
    fn u03_million_iter_identities_load_and_commands_five_six_match() {
        let mut loaded =
            load_source(fixture_file!("subsystems/U03-unification3.maude")).expect("load U03");
        let targets: Vec<_> = loaded
            .commands
            .iter()
            .skip(4)
            .take(2)
            .map(|(module, command)| {
                let Command::Unify { body, .. } = command else {
                    panic!("U03 commands 5/6 must be unify commands")
                };
                (*module, body.clone())
            })
            .collect();
        assert_eq!(targets.len(), 2);

        let expected = [
            vec!["X:Small --> #1:Small\nZ:Small --> #1:Small\nY:Big --> g^999999(a)"],
            vec![
                "X:Small --> #1:Small\nZ:Small --> #1:Small\nY:Big --> g^999999(a)",
                "X:Small --> f(#1:Small, g(#2:Small))\nZ:Small --> #1:Small\nY:Big --> #2:Small",
            ],
        ];

        for ((module, body), want) in targets.into_iter().zip(expected) {
            let mut command =
                unify_command(&mut loaded.modules[module], &mut loaded.interner, &body)
                    .expect("build U03 unify");
            assert_eq!(command.echo, "X:Small =? f(g(Y:Big), Z:Small)");
            assert_eq!(command.readiness, UnifyReadiness::Ready);

            let mut solutions = Vec::new();
            {
                let mut names = InternerNames(&mut loaded.interner);
                let mut env = tnk_core::unify::UnifyEnv {
                    e: &mut loaded.modules[module].built.engine,
                    names: &mut names,
                };
                while let Some(binding) = command.problem.find_next(&mut env) {
                    solutions.push(binding);
                }
            }
            let got: Vec<_> = solutions
                .iter()
                .map(|binding| {
                    render_unifier(
                        &loaded.modules[module].built,
                        &loaded.interner,
                        &command.var_names,
                        binding,
                    )
                })
                .collect();
            assert_eq!(got, want);
        }
    }

    #[test]
    fn iter_comm_normalization_uses_standing_variable_name_order() {
        let mut loaded = load_source(fixture_file!("subsystems/U-ch13-07-iter-comm.maude"))
            .expect("load iter-comm fixture");
        let commands: Vec<_> = loaded
            .commands
            .iter()
            .map(|(module, command)| {
                let Command::Unify { body, .. } = command else {
                    panic!("iter-comm fixture contains only unify commands")
                };
                (*module, body.clone())
            })
            .collect();
        let expected = [
            vec!["X:OddNat", "Y:Int"],
            vec!["X:OddNat", "W:Int", "Z:Int", "Y:Int"],
            vec!["X:OddNat", "W:Int", "Z:Int", "Y:Int"],
        ];

        for ((module, body), expected_names) in commands.into_iter().zip(expected) {
            let command = unify_command(&mut loaded.modules[module], &mut loaded.interner, &body)
                .expect("build iter-comm unify");
            assert_eq!(command.var_names, expected_names);
        }
    }

    #[test]
    fn bool_commands_produce_expected_results() {
        check_results(
            fixture_file!("bool.maude"),
            &[
                e("Truth", "tt", 1),
                e("Truth", "ff", 1),
                e("Truth", "tt", 1),
                e("Zero", "0", 1),
                e("NzNat", "s s 0", 2),
                e("Zero", "0", 1),
            ],
        );
    }

    #[test]
    fn nat_commands_produce_expected_results() {
        check_results(
            fixture_file!("nat.maude"),
            &[
                e("NzNat", "5", 1),
                e("NzNat", "4", 1),
                e("NzNat", "5", 1),
                e("NzNat", "12", 1),
                e("NzNat", "4", 1),
                e("NzNat", "3", 1),
                e("NzNat", "1", 1),
                e("NzNat", "1024", 1),
                e("NzNat", "6", 1),
                e("Truth", "tt", 1),
                e("Truth", "ff", 1),
                e("Truth", "tt", 1),
                e("NzNat", "x + 5", 1),
            ],
        );
    }

    #[test]
    fn int_commands_produce_expected_results() {
        check_results(
            fixture_file!("int.maude"),
            &[
                e("NzInt", "- 3", 0),
                e("NzNat", "3", 1),
                e("Zero", "0", 1),
                e("NzInt", "- 3", 1),
                e("NzInt", "- 5", 1),
                e("NzInt", "- 3", 1),
                e("NzNat", "3", 1),
                e("NzInt", "- 6", 1),
                e("NzNat", "6", 1),
                e("NzInt", "- 3", 1),
                e("NzInt", "- 1", 1),
                e("Truth", "tt", 1),
                e("Truth", "ff", 1),
            ],
        );
    }

    #[test]
    fn peano_commands_produce_expected_results() {
        check_results(
            fixture_file!("peano.maude"),
            &[
                e("Nat", "s s s s 0", 3),
                e("Nat", "s s s s s s s s s s s s 0", 21),
            ],
        );
    }

    #[test]
    fn strategy_commands_produce_expected_results() {
        check_results(
            fixture_file!("strat.maude"),
            &[
                e("Nat", "s s z", 1),
                e("Nat", "z", 1),
                e("Nat", "z", 1),
                e("Nat", "s s z", 2),
                e("S", "b", 1),                    // (0 1 0): first top succeeds
                e("S", "b", 2),                    // first top misses; argument then final top
                e("S", "b", 1),                    // first top skips a reducible argument
                e("S", "b", 2),                    // intermediate top excludes owise
                e("S", "b", 2),                    // (1 0 2 0): intermediate top skips arg 2
                e("S", "b", 3),                    // both staged arguments, then final top
                e("S", "b", 2),                    // missing final zero is appended
                e("S", "b", 2),                    // a strategy with no zero gets a final one
                e("S", "b", 2),                    // duplicate arguments/adjacent zeroes normalize
                e("S", "pair(a, a)", 2), // shared post-top redexes are copied per occurrence
                e("S", "pair(box(a), box(a))", 2), // eager descendants are copied too
                e("S", "a m a m b", 2),  // semi-eager AC reduces every physical argument
                e("S", "a ; b ; a", 3),  // semi-eager AU preserves per-occurrence accounting
            ],
        );
    }

    /// AC matching recurses into compound alien subterms and uses deterministic greedy binding order.
    #[test]
    fn ac_alien_matching_produces_expected_results() {
        check_results(
            fixture_file!("correctness-ac-alien.maude"),
            &[
                e("Nat", "s s s z", 2),
                e("Nat", "s s s s s z", 3),
                e("Nat", "s s s z", 3),
                e("Nat", "s s s z", 4),
                e("Nat", "s s s s s s s z", 4),
                e("Nat", "s s s s s s z", 8),        // 2 * 3
                e("Nat", "s s s s s s s s s z", 13), // 3 * 3
            ],
        );
    }

    /// AU matching recurses into alien subterms and rechecks nonlinear variables against the same run,
    /// using leftmost maximal-collector order.
    #[test]
    fn au_alien_matching_produces_expected_results() {
        check_results(
            fixture_file!("correctness-au-alien.maude"),
            &[
                e("E", "a b c", 2),     // (s s a) b c — peel two successors off the head
                e("E", "a b c", 1),     // a (s b) c   — interior successor untouched
                e("E", "a b c", 2),     // (s a)(s b) c
                e("E", "a", 1),         // a a         — non-linear collapse
                e("E", "a", 2),         // a a a
                e("E", "s (a b) c", 1), // (s a)(s b) c — two aliens, leading pair + residue c
            ],
        );
    }

    /// Free skeletons recursively match theory-rooted children, including AU and AC arguments.
    #[test]
    fn free_alien_matching_produces_expected_results() {
        check_results(
            fixture_file!("correctness-free-alien.maude"),
            &[
                e("E", "b c", 1),      // f(a b c) — AU alien under free f
                e("E", "f(b c)", 0),   // f(b c)   — no match (head is not a)
                e("E", "b ; c", 1),    // g(a ; b ; c) — AC alien under free g
                e("E", "g(b ; c)", 0), // g(b ; c)
                e("E", "c a", 1),      // h(a c, b a) — two aliens, one per argument
            ],
        );
    }

    /// Theory-rooted children compose uniformly beneath iterator and CUI operators.
    #[test]
    fn cross_theory_matching_produces_expected_results() {
        check_results(
            fixture_file!("correctness-cross-theory.maude"),
            &[
                e("Foo", "s (a + b)", 1), // membership lhs `s (a + X)` matches modulo AC under iter
                e("E", "b", 1),           // equation reduces s(a+a) before membership
                e("E", "s (b + b)", 0),   // no leading a
                e("E", "b ; b", 1),       // AC term as a CUI argument
                e("E", "(b + b) ; a", 0), // no leading a in either pairing
            ],
        );
    }

    /// Membership axioms use the same theory-aware lhs automata as equations. These cases cover AC,
    /// AU, and iterator matching; identity-collapse membership has a separate rewrite-count divergence.
    #[test]
    fn theory_memberships_produce_expected_results() {
        check_results(
            fixture_file!("correctness-membership-theory.maude"),
            &[
                // AC-MB
                e("Sym", "a + a", 1),
                e("E", "a + b", 0),
                e("Pair", "s a + b", 1), // alien membership lhs `s M + N` matches modulo AC
                e("Pair", "s a + s a", 1), // both apply; the tie-break picks Pair
                // AU-MB
                e("Lst", "a b c", 1),
                e("E", "b c", 0),
                e("Spec", "s a b c", 1), // alien head `(s M) L` matches modulo AU
                // S-MB
                e("Zero", "0", 0),
                e("NzNat", "s s 0", 0), // too few successors
                e("Big", "s s s 0", 1), // iter/S membership lhs `s s s X`
                e("Big", "s s s s 0", 1),
            ],
        );
    }

    /// Collapsing ACU, two-sided AU, and CUI memberships are offered outside their syntactic root.
    /// Covers recursive survivors, conditions, ordering, identity re-entry, and downstream sort effects.
    #[test]
    fn collapsing_memberships_produce_expected_results() {
        let source = fixture_file!("audit/B3c-membership-collapse.maude")
            .lines()
            .filter(|line| !line.starts_with("set trace"))
            .collect::<Vec<_>>()
            .join("\n");
        check_results(
            &source,
            &[
                e("Special", "a", 1),             // ACU identity collapse
                e("Special", "a", 1),             // AU two-sided identity collapse
                e("Special", "a", 1),             // CUI identity collapse
                e("Special", "a * b", 2),         // child collapse + rooted membership
                e("Special", "a", 1),             // CUI idempotent collapse
                e("Special", "s a", 1),           // collapse to iter survivor
                e("Special", "s a", 1),           // conditional collapse to iter
                e("Special", "a", 1),             // recursive CUI-over-AU survivor
                e("Special", "a", 1),             // recursive CUI-over-CUI survivor
                e("Special", "a", 1),             // all-variable ordinary subject
                e("Special", "z", 1),             // all-variable identity subject
                e("E", "a", 0),                   // conservative noncollapse control
                e("Special", "a * b", 1),         // rooted ground membership still applies
                e("Low", "a", 1),                 // direct+collapse streams: smallest first
                e("E", "b", 2),                   // true sort enables sorted equation
                e("Special", "s a", 1),           // iter contains CUI collapse
                e("Special", "b * s (a + a)", 1), // CUI contains iter + nonlinear AC
                e("Special", "a", 1),             // trace module's reduction
            ],
        );
    }

    /// Strategy-controlled arguments still receive true-sort and membership refinement at the top step.
    /// Discarded branches retain their rewrite accounting.
    #[test]
    fn strategy_memberships_produce_expected_results() {
        check_results(
            fixture_file!("correctness-strat-mb.maude"),
            &[
                e("WrS", "wrap(mk(e))", 1), // skipped arg refined → overloaded range WrS
                e("Sml", "mkA", 4), // both branches refined before selection; discarded one counts
            ],
        );
    }

    #[test]
    fn acu_overloads_produce_expected_results() {
        check_results(
            fixture_file!("acu-overload.maude"),
            &[
                e("NzNat", "z + nz", 0),
                e("NzNat", "z + nz", 0),
                e("Nat", "z + z", 0),
                e("NzNat", "nz + nz", 0),
                e("NzNat", "z + z + nz", 0),
                e("NzNat", "g(z, nz)", 0),
                e("NzNat", "g(z, nz)", 0),
                e("Nat", "g(z, z)", 0),
            ],
        );
    }

    #[test]
    fn acu_reduction_produces_expected_results() {
        check_results(
            fixture_file!("acu-reduce.maude"),
            &[
                e("N", "s 0 + s 0 + s 0", 1),
                e("E", "a + b", 1),
                e("E", "0 ; s 0", 2),
                e("E", "a", 3),
            ],
        );
    }

    #[test]
    fn membership_commands_produce_expected_results() {
        check_results(
            fixture_file!("membership.maude"),
            &[
                e("SymPair", "< z, z >", 1),
                e("Pair", "< z, s z >", 0),
                e("SymPair", "< s z, s z >", 1),
                e("Nat", "z", 2),
                e("Nat", "f(< z, s z >)", 0),
                e("A", "a", 0),
                e("B", "g(a)", 1),
                e("C", "g(g(a))", 2),
            ],
        );
    }

    /// Memberships on reducible operators apply only at normal form. An equation can therefore remove a
    /// redex before its membership or divergent membership condition is considered.
    #[test]
    fn reducible_memberships_produce_expected_results() {
        check_results(
            fixture_file!("correctness-mb-reducible.maude"),
            &[
                e("Big", "big", 1), // MB-REDUCIBLE: eq g(a)=big fires; mb g(X):Small never reached
                e("S", "g(b)", 2),  // MB-REWRITE-CHAIN: g(a)→g(b) [1] then g(b)'s mb [2]
                e("Big", "big", 1), // CMB-DIVERGENT: halts at big; the looping cmb condition is unreached
            ],
        );
    }

    /// Repeated reducible subterms normalize once through subject/RHS DAG sharing, including under AU,
    /// CUI, and ACU theories.
    #[test]
    fn shared_subterms_produce_expected_results() {
        check_results(
            fixture_file!("correctness-sharing.maude"),
            &[
                e("P", "< b, b >", 1), // FREE subject dup: two g(a) -> one node, reduced once
                e("P", "< c, c >", 2), // deep shared chain g(g(a))->g(b)->c, once
                e("P", "< b, b >", 2), // rhs dup: f(a) [1] + shared g(a) in rhs [2]
                e("P", "< b, b >", 2), // triple subject dup: g(a) once [1] + h [2]
                e("P", "< mkA, mkA >", 1), // mb on a shared constant: fires once
                e("L", "b b", 1),      // AU: two equal elements share, reduced once
                e("L", "b b b", 1),    // AU: three equal elements
                e("E", "b & b", 1),    // CUI: two equal elements share
                e("E", "b + b", 1),    // ACU: already merges to multiplicity 2
            ],
        );
    }

    #[test]
    fn overloaded_commands_produce_expected_results() {
        // Command 8 has a kind-level result named after the maximal sort. Non-preregularity warnings are
        // not surfaced; values and sorts remain checked.
        check_results(
            fixture_file!("overload.maude"),
            &[
                e("Zero", "0", 0),
                e("NzNat", "s 0", 0),
                e("NzNat", "s 0 + s 0", 0),
                e("Nat", "0 + s 0", 0),
                e("Nat", "0 + 0", 0),
                e("NzNat", "s s 0", 2),
                e("Zero", "0", 1),
                e("[Nat]", "0 + 0", 0),
                e("NzNat", "s 0 + s 0", 0),
                e("A", "f(c)", 0),
            ],
        );
    }

    /// Check each result's printed form for fixtures whose literal values are most directly compared as
    /// text and do not introduce ACU ordering or spacing choices.
    fn check_rendered_results(src: &str, expected: &[Expect]) {
        let mut loaded = load_source(src).expect("load source");
        let cmds: Vec<(usize, Vec<Token>)> = loaded
            .commands
            .iter()
            .map(|(m, c)| match c {
                Command::Reduce { term, .. } => (*m, term.clone()),
                _ => panic!("conform_render handles only reduce"),
            })
            .collect();
        assert_eq!(cmds.len(), expected.len(), "command count");
        for (idx, ((m, term), exp)) in cmds.iter().zip(expected).enumerate() {
            let Expect::Reduce {
                sort: esort,
                term: eterm,
                rewrites,
            } = exp
            else {
                panic!("conform_render handles only reduce expectations");
            };
            let parsed = parse_command_term(&loaded.modules[*m], &loaded.interner, term)
                .unwrap_or_else(|err| panic!("command {idx}: {err}"));
            let (got, rw) = reduce_command(&mut loaded.modules[*m], &loaded.interner, &parsed)
                .unwrap_or_else(|err| panic!("command {idx}: {err}"));
            let built = &loaded.modules[*m].built;
            let sort = built
                .engine
                .sorts()
                .name(built.engine.sort_of(got))
                .to_string();
            assert_eq!(sort, *esort, "command {idx} sort");
            assert_eq!(rw, *rewrites, "command {idx} rewrites");
            let printed = crate::pretty::print_pretty(built, &loaded.interner, got, false);
            assert_eq!(printed, *eterm, "command {idx} printed value");
        }
    }

    #[test]
    fn float_commands_render_expected_results() {
        check_rendered_results(
            fixture_file!("float.maude"),
            &[
                e("Flt", "4.0", 1),
                e("Flt", "3.5", 1),
                e("Flt", "6.0", 1),
                e("Flt", "3.5", 1),
                e("Flt", "-1.5", 1),
                e("Flt", "3.0", 2),
                e("Flt", "2.0", 1),
                e("Truth", "tt", 1),
                e("Truth", "ff", 1),
            ],
        );
    }

    /// Pin normalized scientific notation, 17-significant-digit rounding, and a long fixed-point
    /// mantissa.
    #[test]
    fn float_formatter_renders_expected_forms() {
        check_rendered_results(
            fixture_file!("correctness-float-print.maude"),
            &[
                e("Flt", "3.3333333333333331e-1", 1),
                e("Flt", "1.0e+4", 1),
                e("Flt", "2.5e-1", 0),
                e("Flt", "1.0000000000000001e-1", 0),
                e("Flt", "1.0e+3", 0),
                e("Flt", "1.0e-3", 0),
                e("Flt", "1.0e+1", 0),
                e("Flt", "5.0e-1", 0),
                e("Flt", "1.0e+16", 0),
                e("Flt", "1.23456789e+5", 0),
                e("Flt", "1.0", 0),
                e("Flt", "1.4142135623730951", 1),
            ],
        );
    }

    /// A `-` glued to digits (`-7`) is one `SMALL_NEG` token and uses the `-_` minus operator's
    /// `MAKE_INTEGER` production, so `-7 quo 2`, `3 + -7`, and `5 - -7` parse and reduce. With no
    /// separating operator token, `5 -7` remains invalid.
    #[test]
    fn glued_minus_parses_and_reduces() {
        check_rendered_results(
            fixture_file!("correctness-glued-minus.maude"),
            &[
                e("NzInt", "-3", 0),
                e("NzInt", "-7", 0),
                e("NzInt", "-3", 1),
                e("NzInt", "-4", 1),
                e("NzInt", "-1", 1),
                e("NzNat", "12", 1),
                e("NzNat", "6", 1),
                e("Truth", "tt", 1),
            ],
        );
    }

    /// Equation and membership application follows declaration order. The first matching equation
    /// fires regardless of specificity; comparable membership targets apply smallest-sort-first
    /// without double-counting, and a conditional fallback takes the first condition that succeeds.
    #[test]
    fn equation_and_membership_order_is_observable() {
        check_rendered_results(
            fixture_file!("correctness-eq-mb-order.maude"),
            &[
                e("S", "b", 1),
                e("S", "c", 1),
                e("S", "c", 1),
                e("S", "b", 1),
                e("A", "x", 1),
                e("S", "b", 1),
                e("S", "c", 1),
            ],
        );
    }

    #[test]
    fn string_commands_render_expected_results() {
        check_rendered_results(
            fixture_file!("string.maude"),
            &[
                e("Str", "\"abcd\"", 1),
                e("NzNat", "5", 1),
                e("Zero", "0", 1),
                e("Str", "\"ell\"", 1),
                e("Truth", "tt", 1),
                e("Truth", "ff", 1),
                e("Truth", "tt", 1),
                e("Truth", "ff", 1),
                e("Truth", "tt", 1),
                e("Truth", "ff", 1),
            ],
        );
    }

    /// A rational special constant prints compactly as `num/den`. A zero numerator is the ordinary
    /// `Zero` constant rather than a positive numeral, so `0 / 5` retains mixfix spacing.
    #[test]
    fn rational_commands_render_expected_results() {
        check_rendered_results(
            fixture_file!("rat.maude"),
            &[
                e("NzNat", "2", 1),
                e("NzRat", "3/4", 1),
                e("NzRat", "3/2", 1),
                e("NzRat", "-3/2", 1),
                e("NzNat", "5", 1),
                e("NzRat", "3/4", 0),
                e("Rat", "0 / 5", 0),
            ],
        );
    }

    #[test]
    fn conditional_equations_produce_expected_results() {
        check_results(
            fixture_file!("conditional.maude"),
            &[
                e("Nat", "s s z", 3),
                e("Nat", "s s z", 5),
                e("Nat", "z", 2),
                e("NzNat", "s z", 1),
                e("Nat", "nz?(z)", 0),
            ],
        );
    }

    #[test]
    fn owise_equations_produce_expected_results() {
        check_results(
            fixture_file!("owise.maude"),
            &[
                e("Truth", "tt", 1),
                e("Truth", "ff", 1),
                e("Truth", "ff", 1),
                e("Nat", "z", 2),
                e("Nat", "z", 3),
                e("Nat", "s z", 3),
            ],
        );
    }

    #[test]
    fn match_conditions_produce_expected_results() {
        check_results(
            fixture_file!("match-cond.maude"),
            &[
                e("Nat", "s z", 1),
                e("Nat", "z", 1),
                e("Nat", "pred(z)", 0),
                e("Nat", "s z", 2),
                e("Nat", "s s z", 2),
            ],
        );
    }

    #[test]
    fn conditional_memberships_produce_expected_results() {
        check_results(
            fixture_file!("cmb.maude"),
            &[
                e("GoodPair", "< z, s z >", 2),
                e("Pair", "< s z, z >", 1),
                e("GoodPair", "< z, z >", 2),
                e("GoodPair", "< s z, s z >", 3),
            ],
        );
    }

    /// End-to-end `match`/`xmatch` through the public kernel solution stream, including ACU identity
    /// and extension matches. Compare solution sets because enumeration order is not an API contract.
    #[test]
    fn acu_matching_produces_expected_solutions() {
        check_results(
            fixture_file!("acu-match.maude"),
            &[
                // match X + Y <=? a + b + c  — six splits into two non-empty parts.
                mat(&[
                    "X --> a\nY --> b + c",
                    "X --> b\nY --> a + c",
                    "X --> c\nY --> a + b",
                    "X --> a + b\nY --> c",
                    "X --> a + c\nY --> b",
                    "X --> b + c\nY --> a",
                ]),
                // match X # Y <=? a # b  — four, including a variable binding the identity `e`.
                mat(&[
                    "X --> e\nY --> a # b",
                    "X --> a\nY --> b",
                    "X --> b\nY --> a",
                    "X --> a # b\nY --> e",
                ]),
                // xmatch a + b <=? a + b + c  — one extension match, residue c, empty substitution.
                mat(&["Matched portion = a + b\nempty substitution"]),
            ],
        );
    }

    /// Empty results use `No match.`; numbered blocks are separated by blank lines.
    #[test]
    fn format_matchers_layout() {
        assert_eq!(format_matchers(&[]), "No match.");
        assert_eq!(
            format_matchers(&[
                "X --> a\nY --> b".to_string(),
                "X --> b\nY --> a".to_string()
            ]),
            "Matcher 1\nX --> a\nY --> b\n\nMatcher 2\nX --> b\nY --> a"
        );
    }

    /// CUI matching enumerates both commutative pairings and preserves identity/idempotence collapse.
    #[test]
    fn cui_commands_produce_expected_results() {
        check_results(
            fixture_file!("cui.maude"),
            &[
                // match f(X, Y) <=? f(a, b)  — the two pairings.
                mat(&["X --> a\nY --> b", "X --> b\nY --> a"]),
                e("E", "c", 1), // red f(b, a)  — matching modulo comm
                e("E", "a", 0), // red g(a, a)  — idempotence collapses at construction
                e("E", "a", 0), // red h(a, e)  — identity collapses at construction
            ],
        );
    }

    /// General ground identities normalize identically in ACU, AU, CUI, and one-sided AU theories.
    #[test]
    fn compound_identities_normalize_across_theories() {
        check_results(
            "fmod ID-THEORIES is
               sort S .
               ops a b : -> S [ctor] .
               op g : S -> S [ctor] .
               op _*_ : S S -> S [assoc comm id: g(a)] .
               op cat : S S -> S [assoc id: g(a)] .
               op pair : S S -> S [comm id: g(a)] .
               op lefty : S S -> S [assoc left id: g(a)] .
               op righty : S S -> S [assoc right id: g(a)] .
             endfm
             red g(a) * b .
             red cat(g(a), b) .
             red pair(g(a), b) .
             red lefty(g(a), b) .
             red lefty(b, g(a)) .
             red righty(b, g(a)) .
             red righty(g(a), b) .",
            &[
                e("S", "b", 0),
                e("S", "b", 0),
                e("S", "b", 0),
                e("S", "b", 0),
                e("S", "lefty(b, g(a))", 0),
                e("S", "b", 0),
                e("S", "righty(g(a), b)", 0),
            ],
        );
    }

    /// Juxtaposition syntax uses right-associating gather to disambiguate adjacent nonterminals. AU
    /// matching then enumerates ordered prefix/suffix splits, including identity splits.
    #[test]
    fn au_commands_produce_expected_results() {
        check_results(
            fixture_file!("au.maude"),
            &[
                // match X Y <=? a b c  — four ordered splits, including nil via the identity.
                mat(&[
                    "X --> nil\nY --> a b c",
                    "X --> a\nY --> b c",
                    "X --> a b\nY --> c",
                    "X --> a b c\nY --> nil",
                ]),
                e("E", "d a d", 1), // red d b c d  — `b c` rewrites to `a` in place (extension both ends)
                e("E", "b", 1),     // red a c c    — lone var absorbs the tail (`a X = b`)
            ],
        );
    }

    /// Declared command variables keep their base names while the solver reorders their slots by
    /// canonical DAG traversal. The colon-token ids occur in source order here, deliberately opposite
    /// the declared base-name order.
    #[test]
    fn unify_normalization_uses_declared_variable_base_names() {
        let src = r#"
fmod BASE-NAME-ORDER is
  sort S .
  op f : S S -> S [assoc comm] .
  vars Z X Y : S .
endfm
unify f(X:S, X:S, Y:S, Y:S, Z:S) =? f(X:S, Y:S, Z:S) .
"#;
        let mut loaded = load_source(src).expect("load source");
        let (module, command) = loaded.commands.pop().expect("unify command");
        let body = match command {
            Command::Unify { body, .. } => body,
            _ => panic!("expected unify command"),
        };
        let command = unify_command(&mut loaded.modules[module], &mut loaded.interner, &body)
            .expect("build unify");
        assert_eq!(command.var_names, ["Z", "X", "Y"]);
    }

    #[test]
    fn retains_nonexec_and_bare_lhs_narrowing_rules() {
        let loaded = load_source(
            r#"
mod NARROW-METADATA is
  sort S .
  op s : S -> S .
  vars X Y : S .
  rl [step] : s(X) => X [narrowing] .
  rl [extra] : X => Y [nonexec narrowing] .
  crl [bad] : s(X) => X if X = X [narrowing] .
endm
"#,
        )
        .expect("load narrowing metadata");
        let module = &loaded.modules[0].built;
        let rules = module.engine.narrowing_rules();
        assert_eq!(rules.len(), 2);
        assert_eq!(rules[0].label.as_deref(), Some("step"));
        assert!(!rules[0].nonexec);
        assert_eq!(rules[1].label.as_deref(), Some("extra"));
        assert!(rules[1].nonexec);
        assert!(matches!(rules[1].lhs, Term::Var(_)));
        assert_eq!(rules[1].variable_names, ["X", "Y"]);
        assert_eq!(module.rl_traces.len(), 1);
        assert!(module.rl_traces[0].narrowing);
    }

    /// The lexer interns an on-the-fly variable such as `Zqx:S` as one token, never its base name `Zqx`.
    /// Normalizing the narrowing display trace of a rule that uses one interns the base name rather than
    /// assuming the lexer did.
    #[test]
    fn narrowing_rule_with_on_the_fly_variable_loads() {
        let loaded = load_source(
            r#"
mod NARROW-ON-THE-FLY is
  sort S .
  op f : S -> S .
  rl [n] : f(Zqx:S) => Zqx:S [narrowing] .
endm
"#,
        )
        .expect("load on-the-fly narrowing rule");
        let module = &loaded.modules[0].built;
        let rules = module.engine.narrowing_rules();
        assert_eq!(rules.len(), 1);
        assert_eq!(rules[0].label.as_deref(), Some("n"));
        assert_eq!(module.rl_traces.len(), 1);
        assert!(module.rl_traces[0].narrowing);
        assert_eq!(module.rl_traces[0].var_names, ["Zqx:S"]);
        assert!(loaded.interner.get("Zqx").is_some());
    }

    /// The kernel indexes executable statements by their lhs top symbol. An executable equation whose lhs
    /// is a bare variable (plain, conditional, `owise`, or `variant`) is dropped with a statement warning,
    /// like the membership and rule cases, before any registration. `[nonexec]` equations never reach the
    /// engine, so they stay silent, and later statements keep dense ids and apply.
    #[test]
    fn bare_variable_equation_lhs_is_dropped_before_registration() {
        let src = "fmod BARE-EQ is\n\
                     sort S .\n\
                     ops a b c : -> S .\n\
                     op f : S -> S .\n\
                     var X : S .\n\
                     eq X = c .\n\
                     ceq X = c if X = a .\n\
                     eq X = b [owise] .\n\
                     eq X:S = a [variant] .\n\
                     eq X = b [nonexec] .\n\
                     ceq X = b if X = c [nonexec] .\n\
                     eq f(a) = b .\n\
                   endfm\n\
                   red f(a) .\n\
                   red c .\n";
        let loaded = load_source(src).expect("load bare-variable equations");
        let module = &loaded.modules[0];
        let dropped: Vec<_> = module
            .diagnostics
            .iter()
            .map(|diagnostic| {
                (
                    diagnostic.module.as_deref(),
                    diagnostic.line,
                    diagnostic.message.as_str(),
                )
            })
            .collect();
        let message = "dropped equation: equation left-hand side is a variable";
        assert_eq!(
            dropped,
            [6, 7, 8, 9].map(|line| (Some("BARE-EQ"), Some(line), message))
        );
        assert_eq!(module.built.eq_traces.len(), 1, "only `eq f(a) = b` loads");
        check_rendered_results(src, &[e("S", "b", 1), e("S", "c", 0)]);
    }

    /// The `message` of each of a module's diagnostics.
    fn diagnostic_messages(module: &LoadedModule) -> Vec<&str> {
        module
            .diagnostics
            .iter()
            .map(|diagnostic| diagnostic.message.as_str())
            .collect()
    }

    /// An operator name may contain connective text (`<_:_>` and `[_:_]` here, like object syntax), so
    /// the first connective token of a condition fragment is not necessarily its connective. Every
    /// fragment form builds over such terms, and so does a Boolean term containing one.
    #[test]
    fn condition_fragment_terms_may_contain_connective_text() {
        let loaded = load_source(
            r#"
mod COND-COLON is
  sorts S S2 T Bool .
  subsort S2 < S .
  op true : -> Bool [ctor special (id-hook SystemTrue)] .
  op <_:_> : S T -> S .
  op [_:_] : S T -> S .
  op _~_ : S S -> Bool .
  ops a b c d e : -> S .
  op t : -> T .
  ops f g h k n p : S -> S .
  crl [eq] : a => b if < a : t > = < a : t > .
  ceq f(X:S) = b if < X:S : t > = < a : t > .
  ceq g(X:S) = Y:S if < Y:S : t > := < X:S : t > .
  crl [rw] : c => d if < c : t > => < Z:S : t > .
  ceq h(X:S) = b if < X:S : t > : S .
  ceq k(X:S) = b if [X:S : t] = [a : t] .
  ceq n(X:S) = b if < X:S : t > ~ < a : t > .
  cmb p(X:S) : S2 if < X:S : t > = < e : t > .
endm
"#,
        )
        .expect("load connective-text conditions");
        let module = &loaded.modules[0];
        let messages = diagnostic_messages(module);
        assert!(messages.is_empty(), "no statement is dropped: {messages:?}");
        let built = &module.built;
        let only = |condition: &[ConditionFragment]| match condition {
            [fragment] => fragment.clone(),
            other => panic!("expected one condition fragment, got {other:?}"),
        };
        assert!(matches!(
            only(&built.rl_traces[0].condition),
            ConditionFragment::Equality { .. }
        ));
        assert!(matches!(
            only(&built.eq_traces[0].condition),
            ConditionFragment::Equality { .. }
        ));
        match only(&built.eq_traces[1].condition) {
            ConditionFragment::Matching { fresh_vars, .. } => assert_eq!(fresh_vars, [1]),
            other => panic!("expected a matching fragment, got {other:?}"),
        }
        assert_eq!(built.eq_traces[1].var_names, ["X:S", "Y:S"]);
        match only(&built.rl_traces[1].condition) {
            ConditionFragment::Rewrite { fresh_vars, .. } => assert_eq!(fresh_vars, [0]),
            other => panic!("expected a rewrite fragment, got {other:?}"),
        }
        assert!(matches!(
            only(&built.eq_traces[2].condition),
            ConditionFragment::SortTest { .. }
        ));
        assert!(matches!(
            only(&built.eq_traces[3].condition),
            ConditionFragment::Equality { .. }
        ));
        let truth = Term::constant(built.true_sym.expect("true is declared"));
        match only(&built.eq_traces[4].condition) {
            ConditionFragment::Equality { rhs, .. } => assert_eq!(rhs, truth),
            other => panic!("expected a bare Boolean fragment, got {other:?}"),
        }
        assert!(matches!(
            only(&built.mb_traces[0].condition),
            ConditionFragment::Equality { .. }
        ));
    }

    /// The first connective token's split is the reading whenever it builds, even when another reading
    /// also builds. Otherwise a later reading is accepted only when it is the unique one; with none, the
    /// first split's error is reported as before.
    #[test]
    fn condition_connective_keeps_the_first_split_and_requires_a_unique_alternative() {
        let loaded = load_source(
            r#"
fmod COND-POLICY is
  sorts S T Bool .
  op true : -> Bool [ctor special (id-hook SystemTrue)] .
  op <_:_> : S T -> S .
  op _=_ : S S -> Bool .
  ops a b : -> S .
  op t : -> T .
  ops f g h k : S -> S .
  ceq f(X:S) = b if X:S = a .
  ceq g(X:S) = b if < X:S : t > = < a : t > .
  ceq h(X:S) = b if < X:S : t > .
  ceq k(X:S) = b if < X:S : t > : Nope .
endfm
"#,
        )
        .expect("load connective policy");
        let module = &loaded.modules[0];
        assert_eq!(
            diagnostic_messages(module),
            [
                "dropped equation: ambiguous condition fragment: `< X:S : t > = < a : t >`",
                "dropped equation: no parse at token 2 (`<end>`): `< X:S`",
                "dropped equation: no parse at token 2 (`<end>`): `< X:S`",
            ]
        );
        // `X:S = a` is the `=` split, not the Boolean term `_=_(X:S, a)` read as `... = true`.
        match module.built.eq_traces.as_slice() {
            [trace] => assert!(
                matches!(
                    trace.condition.as_slice(),
                    [ConditionFragment::Equality {
                        lhs: Term::Var(_),
                        ..
                    }]
                ),
                "{:?}",
                trace.condition
            ),
            other => panic!("expected only `f`'s equation, got {other:?}"),
        }
    }

    /// Exceeding the parse effort limit decides no reading (`TNK-PARSE-003`): when a later connective
    /// split's side exhausts it, the fragment reports that exhaustion rather than the first split's
    /// malformed-term error or another reading.
    #[test]
    fn condition_connective_search_stops_at_parse_effort_exhaustion() {
        let mut source = String::from(
            "fmod COND-EFFORT is\n sorts S T .\n op <_:_> : S T -> S .\n op a : -> S .\n \
             op t : -> T .\n op f : S -> S .\n",
        );
        for index in 0..500 {
            source.push_str(&format!(" op _o{index}_ : S S -> S [assoc] .\n"));
        }
        source.push_str(" ceq f(X:S) = a if < X:S : t > = a");
        for _ in 1..640 {
            source.push_str(" o0 a");
        }
        source.push_str(" o0 bogus .\nendfm\n");
        let loaded = load_source(&source).expect("load effort module");
        match diagnostic_messages(&loaded.modules[0]).as_slice() {
            [message] => assert!(
                message.starts_with("dropped equation: parse effort limit exceeded at token "),
                "{message}"
            ),
            other => panic!("expected one dropped equation, got {other:?}"),
        }
    }

    /// Load, run, and raw-print every listed frontend fixture. Keeping the fixture list explicit prevents
    /// newly added cases from silently falling outside this breadth check.
    #[test]
    fn all_frontend_fixtures_load_run_and_round_trip() {
        use crate::pretty::print_raw;
        // (name, source, round_trip). `fib` is the throughput fixture — its result is a 17711-deep
        // successor chain, so we run+count it but skip the (correct, but O(n)-token) round-trip reparse;
        // `peano` round-trips the same Peano-Fibonacci theory at a small numeral.
        let modules: &[(&str, &str, bool)] = &[
            ("acu-match", fixture_file!("acu-match.maude"), true),
            ("acu-overload", fixture_file!("acu-overload.maude"), true),
            ("acu-reduce", fixture_file!("acu-reduce.maude"), true),
            ("au", fixture_file!("au.maude"), true),
            ("bool", fixture_file!("bool.maude"), true),
            ("cmb", fixture_file!("cmb.maude"), true),
            ("conditional", fixture_file!("conditional.maude"), true),
            ("cui", fixture_file!("cui.maude"), true),
            ("fib", fixture_file!("fib.maude"), false),
            ("float", fixture_file!("float.maude"), true),
            ("int", fixture_file!("int.maude"), true),
            ("iter", fixture_file!("iter.maude"), true),
            ("match-cond", fixture_file!("match-cond.maude"), true),
            ("membership", fixture_file!("membership.maude"), true),
            ("nat", fixture_file!("nat.maude"), true),
            ("overload", fixture_file!("overload.maude"), true),
            ("owise", fixture_file!("owise.maude"), true),
            ("peano", fixture_file!("peano.maude"), true),
            ("rat", fixture_file!("rat.maude"), true),
            ("strat", fixture_file!("strat.maude"), true),
            ("string", fixture_file!("string.maude"), true),
        ];
        for &(name, src, round_trip) in modules {
            let mut loaded = load_source(src).unwrap_or_else(|e| panic!("{name}: load: {e}"));
            let cmds: Vec<(usize, Cmd)> = loaded
                .commands
                .iter()
                .map(|(m, c)| {
                    let cmd = match c {
                        Command::Reduce { term, .. } => Cmd::Reduce(term.clone()),
                        Command::Match {
                            pattern,
                            subject,
                            xmatch,
                            ..
                        } => Cmd::Match {
                            pattern: pattern.clone(),
                            subject: subject.clone(),
                            xmatch: *xmatch,
                        },
                        _ => panic!("this conformance harness covers only reduce/match"),
                    };
                    (*m, cmd)
                })
                .collect();
            assert!(!cmds.is_empty(), "{name}: no commands parsed");
            for (idx, (m, cmd)) in cmds.iter().enumerate() {
                match cmd {
                    Cmd::Reduce(term) => {
                        let parsed =
                            parse_command_term(&loaded.modules[*m], &loaded.interner, term)
                                .unwrap_or_else(|e| panic!("{name} cmd {idx}: parse: {e}"));
                        let (result, _) =
                            reduce_command(&mut loaded.modules[*m], &loaded.interner, &parsed)
                                .unwrap_or_else(|e| panic!("{name} cmd {idx}: reduce: {e}"));
                        if round_trip {
                            let printed =
                                print_raw(&loaded.modules[*m].built, &loaded.interner, result);
                            let toks = tokenize(&printed, &mut loaded.interner);
                            let reparsed_term =
                                parse_command_term(&loaded.modules[*m], &loaded.interner, &toks)
                                    .unwrap_or_else(|e| {
                                        panic!("{name} cmd {idx} reparse `{printed}`: {e}")
                                    });
                            let (reparsed, _) = reduce_command(
                                &mut loaded.modules[*m],
                                &loaded.interner,
                                &reparsed_term,
                            )
                            .unwrap_or_else(|e| {
                                panic!("{name} cmd {idx} reparse `{printed}`: {e}")
                            });
                            let eng = &loaded.modules[*m].built.engine;
                            assert!(
                                eng.deep_equal(result, reparsed),
                                "{name} cmd {idx}: `{printed}` did not round-trip"
                            );
                        }
                    }
                    Cmd::Match {
                        pattern,
                        subject,
                        xmatch,
                    } => {
                        match_command(
                            &mut loaded.modules[*m],
                            &loaded.interner,
                            pattern,
                            subject,
                            *xmatch,
                        )
                        .unwrap_or_else(|e| panic!("{name} cmd {idx}: match: {e}"));
                    }
                }
            }
        }
    }

    #[test]
    fn parse_effort_limit_is_deterministic() {
        let mut loaded = load_source(
            "fmod EFFORT-LIMIT is
               sort S .
               op a : -> S [ctor] .
               op _+_ : S S -> S [assoc comm] .
             endfm",
        )
        .expect("load effort grammar");
        let text = std::iter::repeat_n("a", 200)
            .collect::<Vec<_>>()
            .join(" + ");
        let tokens = tokenize(&text, &mut loaded.interner);
        let mut first_error = None;
        for _ in 0..2 {
            let mut effort = ParseEffort::new(1_000);
            let error = parse_forest_any_with_effort(
                &tokens,
                &loaded.modules[0].grammar,
                &loaded.interner,
                &mut effort,
            )
            .expect_err("small explicit budget must reject");
            assert_eq!(effort.used(), 1_000);
            assert!(
                error.starts_with("parse effort limit exceeded at token "),
                "{error}"
            );
            if let Some(first) = &first_error {
                assert_eq!(&error, first);
            } else {
                first_error = Some(error);
            }
        }
    }

    #[test]
    fn forest_extraction_shares_recognizer_budget() {
        let mut loaded = load_source(
            "fmod FOREST-EFFORT is
               sort S .
               op a : -> S [ctor] .
               op _+_ : S S -> S [assoc comm] .
             endfm",
        )
        .expect("load forest effort grammar");
        let text = std::iter::repeat_n("a", 20).collect::<Vec<_>>().join(" + ");
        let tokens = tokenize(&text, &mut loaded.interner);
        let grammar = &loaded.modules[0].grammar;

        let mut recognition = ParseEffort::new(u64::MAX);
        earley::parse(
            grammar,
            &tokens,
            Nt::Term,
            &loaded.interner,
            &mut recognition,
        )
        .expect("recognize term");
        let recognition_cost = recognition.used();

        let mut shared = ParseEffort::new(recognition_cost);
        let error = parse_forest_any_with_effort(&tokens, grammar, &loaded.interner, &mut shared)
            .expect_err("forest must not receive a fresh budget");
        assert_eq!(shared.used(), recognition_cost);
        assert!(
            error.starts_with(&format!(
                "parse effort limit exceeded at token {} (`<end>`)",
                tokens.len()
            )),
            "{error}"
        );
    }

    /// Opt-in parser scaling benchmark above the interactive effort limit.
    #[test]
    #[ignore = "opt-in large-grammar parser benchmark"]
    fn large_grammar_valid_and_invalid_parse_benchmark() {
        let mut source = String::from("fmod EFFORT is\n sort S .\n op a : -> S [ctor] .\n");
        for index in 0..1000 {
            source.push_str(&format!(" op _o{index}_ : S S -> S [assoc] .\n"));
        }
        source.push_str("endfm\n");
        let mut loaded = load_source(&source).expect("load generated grammar");
        let mut text = String::from("a");
        for _ in 1..1280 {
            text.push_str(" o0 a");
        }

        let valid = tokenize(&text, &mut loaded.interner);
        let mut valid_effort = ParseEffort::new(u64::MAX);
        parse_forest_any_with_effort(
            &valid,
            &loaded.modules[0].grammar,
            &loaded.interner,
            &mut valid_effort,
        )
        .expect("valid benchmark term");
        assert!(valid_effort.used() > crate::cfparser::DEFAULT_PARSE_EFFORT_LIMIT);

        let invalid = tokenize(&format!("{text} o0 bogus"), &mut loaded.interner);
        let mut invalid_effort = ParseEffort::new(u64::MAX);
        let error = parse_forest_any_with_effort(
            &invalid,
            &loaded.modules[0].grammar,
            &loaded.interner,
            &mut invalid_effort,
        )
        .expect_err("invalid benchmark term");
        assert!(
            error.starts_with("no parse at token 2560 (`bogus`)"),
            "{error}"
        );
        assert!(invalid_effort.used() > crate::cfparser::DEFAULT_PARSE_EFFORT_LIMIT);
    }

    #[test]
    fn two_thousand_atom_flat_command_fits_parse_budget() {
        let mut loaded = load_source(
            "fmod D3 is
               sort S .
               op 1 : -> S [ctor] .
               op _+_ : S S -> S [assoc comm] .
             endfm",
        )
        .expect("load D3 grammar");
        let text = std::iter::repeat_n("1", 2000)
            .collect::<Vec<_>>()
            .join(" + ");
        let tokens = tokenize(&text, &mut loaded.interner);
        parse_command_term(&loaded.modules[0], &loaded.interner, &tokens)
            .expect("retained 2,000-atom command must remain below the parser budget");
    }
    #[test]
    fn unify_readiness_distinguishes_screening_failures() {
        fn readiness(source: &str) -> UnifyReadiness {
            let mut loaded = load_source(source).expect("load unification screening module");
            let (module, command) = loaded.commands.pop().expect("one unify command");
            let Command::Unify { body, .. } = command else {
                panic!("expected a unify command");
            };
            unify_command(&mut loaded.modules[module], &mut loaded.interner, &body)
                .expect("build unify command")
                .readiness
        }

        assert_eq!(
            readiness(
                "fmod UNSAFE-NAME is
                   sort S .
                   op a : -> S [ctor] .
                 endfm
                 unify #1:S =? a .",
            ),
            UnifyReadiness::UnsafeVariableName
        );
        assert_eq!(
            readiness(
                "fmod UNSUPPORTED-THEORY is
                   sort S .
                   op a : -> S [ctor] .
                   op f : S S -> S [comm idem] .
                 endfm
                 unify f(X:S, a) =? f(a, a) .",
            ),
            UnifyReadiness::UnsupportedTheory
        );
    }
}
