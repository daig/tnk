//! Reusable, host-owned TNK evaluation state.
//!
//! [`Session`] owns the persistent interner, module database, built modules, current module, and
//! resumable command state. [`Session::eval`] evaluates one submission. [`Session::builder`] can
//! install an immutable [`HostFunctionCatalog`] before module construction so source operators may
//! invoke strict host-provided Rust reducers. The `tnk-repl` crate buffers multiline input through
//! [`Session::input_complete`] and applies terminal wrapping to returned text. Evaluation is
//! synchronous; an executing reduction, search, or reducer callback has no cooperative cancellation token.

mod interpreter;
mod trace;

use interpreter::{InterpreterRegistry, LocalInterpreterManager};
use std::collections::{HashMap, HashSet};
use tnk_core::dag::DagId;
use tnk_core::host::{HostFunctionCatalog, ReducerFault};
use tnk_core::rewrite::{ExternalRun, RewriteStep, Rewriting};
use tnk_core::search::Search;
use tnk_core::smt::{ConfiguredSmtEngine, SmtEngine, SmtResult};
use tnk_frontend::build_term::VarIndex;
use tnk_frontend::lex::{Interner, TokKind, Token, tokenize};
use tnk_frontend::load::{
    InternerNames, LoadedModule, ParsedCommandTerm, UnifyReadiness, build_command_dag,
    build_logic_command_dag, command_echo, command_variable_display_name, erewrite_command,
    format_matchers, frewrite_command, match_command, maude_variable_name_rank, narrow_command,
    parse_command_term, render_unifier, rewrite_command, search_command, smt_search_command,
    unify_command, variant_command, variant_match_command, variant_unify_command,
};
use tnk_frontend::pretty::{print_pretty, print_pretty_with_variables};
use tnk_frontend::sig::build_sig::canonical_name;
use tnk_frontend::surface::ast::{
    Command, Diagnostic, DiagnosticSeverity, ModuleExpr, NarrowDisplay, OpMap, PreModule,
    SearchArrow, TopItem, ViewDecl,
};
use tnk_frontend::surface::parser::Parser;
use tnk_modules::db::ModuleDb;
use tnk_modules::load::{flatten_and_build_with_host_functions, module_dep_names, view_dep_names};
use tnk_modules::meta::{MetaDescent, MetaState};
use tnk_modules::view::{ViewDb, validate_view_with_host_functions};
use trace::{TraceFlags, render_trace};

/// The result of evaluating one input submission: the text to print, and whether to exit the loop.
#[derive(Debug, Default)]
pub struct Eval {
    pub output: String,
    pub exit: bool,
}

/// The interactive shell's state. One persistent [`Interner`] backs all submissions so module names,
/// operators, and command terms intern consistently.
pub struct Session {
    host_functions: HostFunctionCatalog,
    /// Optional safe-point GC cadence used only for non-resumable ordinary `reduce` commands.
    reduce_gc_interval: Option<u64>,
    /// First nested child-interpreter reducer fault, transferred to the owning semantic driver.
    reducer_fault: Option<ReducerFault>,
    interner: Interner,
    /// Parsed `PreModule`s (the input to flattening — an importer re-flattens its closure from here).
    db: ModuleDb,
    /// Flattened + built modules, keyed by name.
    modules: HashMap<String, LoadedModule>,
    /// Validated view definitions, keyed by name.
    views: ViewDb,
    /// Reflection search state retained across commands, including variant-unification cursors.
    meta_state: MetaState,
    /// Direct dependencies for each module and view. Redefinition triggers rebuilding every transitive
    /// dependent so cached flattened modules cannot retain a replaced definition.
    deps: HashMap<String, HashSet<String>>,
    /// The names of the built [`modules`](Self::modules), each once, in entry order (for `show modules`).
    /// A redefinition keeps its position; a module that was dropped and entered again is appended.
    order: Vec<String>,
    /// View names in entry order (for `show views`).
    view_order: Vec<String>,
    /// Module selected for unqualified commands.
    current: Option<String>,
    /// Per-call rendering choice supplied by the host; the Session does not choose terminal policy.
    render_color: bool,
    /// The full `trace` flags (`set trace [<option>] on|off`); `master` off by default.
    trace: TraceFlags,
    /// The last resumable session (`rewrite`/`frewrite` or `search`) and the module name it ran in, for
    /// `continue` (and `show path`/`show search graph`). A new execution command normally replaces or
    /// clears it; a strategy rejected before execution retains the saved continuation. Resumable
    /// operations always run with in-reduction GC disabled.
    last: Option<(String, Continuation)>,
    /// Pending scripted/piped input for `erewrite`'s `getLine`, moved into the selected engine when an
    /// `erewrite` command starts.
    stdin: String,
    /// `set include BOOL on|off`: inject `including BOOL .` into subsequently entered modules. Defaults off
    /// so early prelude modules can establish BOOL before enabling it.
    include_bool: bool,
    /// Canonicalized paths already `load`ed — `sload` (skip-load) consults this and loads only once.
    loaded_files: std::collections::HashSet<std::path::PathBuf>,
    show_breakdown: bool,
    /// `set verbose on|off`: show narrowing fold decisions and terminal state counts.
    verbose: bool,
    /// Local synchronous child interpreters. Each child is a complete independent Session and may own
    /// nested children of its own; IDs are scoped to this parent Session.
    interpreters: InterpreterRegistry,
    /// Unequal identity-collapse notices already emitted; each operator reports at most once.
    reported_identity_collapses: HashSet<(String, tnk_core::symbol::SymbolId, bool)>,
    /// Source diagnostics already shown in this Session. Imported, renamed, instantiated, or
    /// dependent rebuilds may rediscover the same source declaration; they must not create warning storms.
    reported_source_diagnostics: HashSet<Diagnostic>,
}

/// A resumable session stored for `continue` / `show`.
// A session owns at most one continuation; keeping the common rewrite state inline avoids an allocation
// on every rewrite command.
#[allow(clippy::large_enum_variant)]
enum Continuation {
    /// A `rewrite`/`frewrite` session.
    Rewrite(Rewriting),
    /// A `search` session (the state graph + the goal's variable index for rendering). Boxed: the search
    /// state graph is much larger than a `Rewriting`, so this keeps the enum (and the `last` slot) small.
    Search(Box<SearchSession>),
    /// An SMT rewrite-sequence search with accumulated constraints.
    SmtSearch(Box<SmtSearchSession>),
    /// A folding-variant enumeration, including its external numbering and output mode.
    Variants(Box<VariantSession>),
    /// A plain/filtered variant-unification enumeration.
    VariantUnifiers(Box<VariantUnifySession>),
    Narrow(Box<NarrowSession>),
}

/// A `search` session plus what the REPL needs to render and resume it.
struct SearchSession {
    search: Search,
    /// The goal pattern's variables (for the `X:Sort --> value` solution lines).
    vars: VarIndex,
}

struct SmtSearchSession {
    search: tnk_core::smt_search::SmtSearch,
    goal_variables: VarIndex,
    target_variable_count: u32,
    shown_total: u32,
}

/// A `get variants` session plus the source names needed for substitution rendering.
struct VariantSession {
    search: tnk_core::variant::VariantSearch,
    var_names: Vec<String>,
    irredundant: bool,
    reported_total: bool,
}

struct VariantUnifySession {
    search: tnk_core::variant::VariantSearch,
    var_names: Vec<String>,
    upfront: bool,
    matching: bool,
    subject: Option<DagId>,
    restorations: Vec<(DagId, DagId)>,
    fresh_base: String,
    prepared: bool,
    exhausted: bool,
    reported_total: bool,
    next_number: u64,
    stream: tnk_core::variant::FilteredVariantUnifierStream,
}

struct NarrowSession {
    search: tnk_core::narrow::NarrowSearch,
    variables: VarIndex,
    initial_variable_count: usize,
    initial_variables: Option<Vec<VarIndex>>,
    initial_echoes: Vec<String>,
    next_number: u64,
    path: bool,
}

#[derive(Default)]
pub struct SessionBuilder {
    host_functions: HostFunctionCatalog,
    reduce_gc_interval: Option<u64>,
}

impl SessionBuilder {
    /// Configure the immutable host-function capability catalog inherited by every module and child
    /// interpreter built by this Session.
    pub fn host_functions(mut self, host_functions: HostFunctionCatalog) -> Self {
        self.host_functions = host_functions;
        self
    }

    /// Set the safe-point collection cadence for ordinary, non-resumable `reduce` commands.
    ///
    /// The interval is installed on the selected module Engine immediately before reduction and removed
    /// before rendering the result. It does not enable GC for rewrite/search continuations or nested
    /// META object Engines. `Some(1)` is useful for stress-testing callback rooting.
    pub fn reduce_gc_interval(mut self, interval: Option<u64>) -> Self {
        self.reduce_gc_interval = interval;
        self
    }

    pub fn build(self) -> Session {
        Session::with_configuration(self.host_functions, self.reduce_gc_interval)
    }
}

impl Default for Session {
    fn default() -> Self {
        Self::new()
    }
}

impl Session {
    /// Start a Session builder. By default its host-function catalog is empty.
    pub fn builder() -> SessionBuilder {
        SessionBuilder::default()
    }

    pub fn new() -> Self {
        Self::builder().build()
    }

    fn with_configuration(
        host_functions: HostFunctionCatalog,
        reduce_gc_interval: Option<u64>,
    ) -> Self {
        Self {
            host_functions,
            reduce_gc_interval,
            reducer_fault: None,
            interner: Interner::new(),
            db: ModuleDb::new(),
            modules: HashMap::new(),
            views: ViewDb::new(),
            meta_state: MetaState::default(),
            deps: HashMap::new(),
            order: Vec::new(),
            view_order: Vec::new(),
            current: None,
            render_color: false,
            trace: TraceFlags::default(),
            last: None,
            stdin: String::new(),
            include_bool: false,
            loaded_files: std::collections::HashSet::new(),
            show_breakdown: false,
            verbose: false,
            interpreters: InterpreterRegistry::default(),
            reported_identity_collapses: HashSet::new(),
            reported_source_diagnostics: HashSet::new(),
        }
    }

    /// Replace the scripted/piped input stream consumed by `erewrite` `getLine` requests.
    pub fn set_stdin(&mut self, input: impl Into<String>) {
        self.stdin = input.into();
    }

    /// The current module's name, if any (for the prompt / introspection).
    pub fn current(&self) -> Option<&str> {
        self.current.as_deref()
    }

    /// Evaluate one complete input submission. `color` is host policy supplied per call; output is
    /// otherwise terminal-neutral and deliberately unwrapped.
    pub fn eval(&mut self, input: &str, color: bool) -> Eval {
        self.render_color = color;
        self.eval_dispatch(input)
    }

    /// The dispatch behind [`eval`](Self::eval): produces the unwrapped output text. A submission may
    /// hold several statements — a loaded `.maude` file freely mixes module definitions, commands, and
    /// `set`/`show`/`select`/`quit` meta-commands — so it is split into complete statements (the same
    /// boundary [`input_complete`](Self::input_complete) uses, so a multi-line module stays one chunk)
    /// and each is dispatched in turn. This is why a file's mid-stream `set trace on .` is handled rather
    /// than mis-parsed as a term.
    fn eval_dispatch(&mut self, input: &str) -> Eval {
        let mut output = String::new();
        let mut buffer = String::new();
        for line in input.lines() {
            buffer.push_str(line);
            buffer.push('\n');
            if self.input_complete(&buffer) {
                let ev = self.dispatch_one(&buffer);
                buffer.clear();
                append_block(&mut output, &ev.output);
                if ev.exit {
                    return Eval {
                        output: output.trim_end().to_string(),
                        exit: true,
                    };
                }
            }
        }
        // A trailing statement with no terminator (e.g. a partial interactive line) — dispatch it
        // best-effort so its parse error surfaces rather than being silently dropped.
        if !buffer.trim().is_empty() {
            let ev = self.dispatch_one(&buffer);
            append_block(&mut output, &ev.output);
        }
        Eval {
            output: output.trim_end().to_string(),
            exit: false,
        }
    }

    /// Dispatch ONE complete statement: a `set`/`show`/`select`/`quit` meta-command (by its first word),
    /// or a module definition / command parsed via [`Parser::parse_top_item`].
    fn dispatch_one(&mut self, input: &str) -> Eval {
        if input.trim().is_empty() {
            return Eval::default();
        }
        // Tokenize once so the meta-command dispatch keys on the first *token* (comments already stripped
        // by the lexer) rather than the first raw word: a `***`/`---` comment on the line before
        // `select`/`show`/`set` no longer desyncs it.
        // The meta handlers re-space the tokens (`join_tokens`), which keeps structured names (`LIST{Nat}`)
        // intact and drops the comment prefix.
        let toks = tokenize(input, &mut self.interner);
        let Some(first) = toks.first().map(|t| self.interner.resolve(t.sym)) else {
            return Eval::default(); // comment-only / blank submission
        };
        match first {
            "quit" | "q" | "exit" => {
                return Eval {
                    output: "Bye.".into(),
                    exit: true,
                };
            }
            "load" | "sload" => {
                // Load paths occupy the rest of the keyword's physical line; an optional final command
                // dot is not part of the path (Appendix D). Search by leading keyword because comments
                // may precede the command in this chunk.
                let path = input
                    .lines()
                    .map(str::trim)
                    .find(|l| l.split_whitespace().next() == Some(first))
                    .and_then(|l| l.split_once(char::is_whitespace))
                    .map(|(_, rest)| load_path_operand(rest))
                    .unwrap_or("");
                return self.meta_load(first == "sload", path);
            }
            "select" => return self.meta_select(&join_tokens(&toks, &self.interner)),
            "show" => return self.meta_show(&join_tokens(&toks, &self.interner)),
            "set" => return self.meta_set(&join_tokens(&toks, &self.interner)),
            "do" if toks.get(1).map(|token| self.interner.resolve(token.sym)) == Some("clear")
                && toks.get(2).map(|token| self.interner.resolve(token.sym)) == Some("memo") =>
            {
                return Eval {
                    output: unsupported_memo_control_warning().to_string(),
                    exit: false,
                };
            }
            _ => {}
        }

        // Otherwise: module definitions and reduce/match/rewrite/search commands. Collect the parsed
        // items first so the `Parser`'s shared borrow of the interner is released before we mutate it.
        let mut output = String::new();
        let items = {
            let mut p = Parser::new(&toks, &self.interner);
            let mut items = Vec::new();
            loop {
                match p.parse_top_item() {
                    Ok(Some(it)) => items.push(it),
                    Ok(None) => break,
                    Err(e) => {
                        let line = p.error_line();
                        let context = p.error_context();
                        output.push_str("parse error:");
                        if let Some((kind, name)) = context {
                            output.push_str(&format!(" {kind} `{name}`,"));
                        }
                        if let Some(line) = line {
                            output.push_str(&format!(" line {line}:"));
                        }
                        output.push_str(&format!(" {e}\n"));
                        break;
                    }
                }
            }
            items
        };
        // Reject multiple commands on one physical line. Each line in a loaded file is dispatched
        // separately; a module or view followed by one command remains valid.
        if items
            .iter()
            .enumerate()
            .any(|(k, it)| matches!(it, TopItem::Command(_)) && k + 1 < items.len())
        {
            // Reject the entire statement group before dispatch so no partial command results are emitted.
            output.push_str("error: more than one command on a line.\n");
            return Eval {
                output: output.trim_end().to_string(),
                exit: false,
            };
        }
        for item in items {
            match item {
                TopItem::Module(pm) => self.enter_module(pm, &mut output),
                TopItem::View(v) => self.enter_view(v, &mut output),
                TopItem::Command(c) => self.run_command(c, &mut output),
            }
        }
        let output = if output.ends_with("\n\n") {
            output
        } else {
            output.trim_end().to_string()
        };
        Eval {
            output,
            exit: false,
        }
    }

    /// Define or replace a module, rebuild its closure, and select it. Success is silent.
    fn enter_module(&mut self, mut pm: PreModule, out: &mut String) {
        let name = pm.name.clone();
        // Implicit BOOL: `set include BOOL on` injects
        // `including BOOL .`. An explicit BOOL import dedups in flatten's visited set.
        if self.include_bool && name != "BOOL" && self.db.get("BOOL").is_some() {
            pm.imports.insert(
                0,
                tnk_frontend::surface::ast::Import {
                    mode: tnk_frontend::surface::ast::ImportMode::Including,
                    expr: ModuleExpr::Named("BOOL".into()),
                },
            );
        }

        let dependencies = module_dep_names(&pm);
        let imports = pm.imports.clone();
        let mut diagnostics = unsupported_memo_diagnostics(&pm, &self.interner);

        // Build against a candidate database. A failed replacement must not mutate the source DB or
        // invalidate the last successful build, current selection, continuations, or metalevel DAGs.
        let mut candidate_db = self.db.clone();
        candidate_db.insert(pm);
        tnk_modules::prelude::ensure_builtins(&imports, &mut candidate_db, &mut self.interner);
        let built = {
            let mods = &self.modules;
            let home_mod = |module: &str| mods.get(module);
            flatten_and_build_with_host_functions(
                &name,
                &candidate_db,
                &self.views,
                &home_mod,
                &mut self.interner,
                &self.host_functions,
            )
        };

        match built {
            Ok(mut lm) => {
                diagnostics.append(&mut lm.diagnostics);
                sort_diagnostics(&mut diagnostics, &name);
                self.reported_source_diagnostics
                    .retain(|diagnostic| diagnostic.module.as_deref() != Some(name.as_str()));
                append_diagnostics(out, &diagnostics, &mut self.reported_source_diagnostics);
                if self.verbose && !lm.built.oo_completion_diagnostics.is_empty() {
                    out.push_str(&lm.built.oo_completion_diagnostics.join("\n\n"));
                    out.push_str("\n\n");
                }

                self.last = None;
                self.meta_state.clear();
                self.db = candidate_db;
                self.deps.insert(name.clone(), dependencies);
                if !self.modules.contains_key(&name) {
                    self.order.push(name.clone());
                }
                self.reported_identity_collapses
                    .retain(|(module, _, _)| module != &name);
                self.modules.insert(name.clone(), lm);
                self.current = Some(name.clone());
                self.rebuild_dependents(&name, out);
            }
            Err(e) => {
                out.push_str(&format!("error: module `{name}`"));
                if let Some(line) = candidate_db
                    .get(&name)
                    .and_then(|module| module.source_line)
                {
                    out.push_str(&format!(", line {line}"));
                }
                out.push_str(&format!(": {e}\n"));
            }
        }
    }

    /// Install a META-INTERPRETER module with both decoded source and compiled form. Reconstructing its
    /// statements through surface bubbles can lose overload resolution and make later reflection incomplete.
    fn enter_meta_module(&mut self, pm: PreModule, lm: LoadedModule, out: &mut String) {
        let name = pm.name.clone();
        self.last = None;
        self.meta_state.clear();
        self.deps.insert(name.clone(), module_dep_names(&pm));
        self.db.insert(pm);
        if self.verbose && !lm.built.oo_completion_diagnostics.is_empty() {
            out.push_str(&lm.built.oo_completion_diagnostics.join("\n\n"));
            out.push_str("\n\n");
        }
        if !self.modules.contains_key(&name) {
            self.order.push(name.clone());
        }
        self.reported_identity_collapses
            .retain(|(module, _, _)| module != &name);
        self.modules.insert(name.clone(), lm);
        self.current = Some(name.clone());
        self.rebuild_dependents(&name, out);
    }

    /// Validate and store a view. Success is silent; validation errors are emitted. A view can later serve
    /// as an instantiation argument and is available to `show view`.
    fn enter_view(&mut self, v: ViewDecl, out: &mut String) {
        match validate_view_with_host_functions(
            &v,
            &self.db,
            &self.views,
            &mut self.interner,
            &self.host_functions,
        ) {
            Ok(()) => {
                let name = v.name.clone();
                // Record the view's direct dependencies (its from/to modules + parameter theories) and
                // store it.
                self.deps.insert(name.clone(), view_dep_names(&v));
                if !self.views.contains(&v.name) {
                    self.view_order.push(v.name.clone());
                }
                self.views.insert(v);
                self.meta_state.clear(); // view semantics participate in reflected module construction
                // A redefined view makes cached builds of modules that instantiate with it stale
                // (`M{V}` was flattened using the replaced view), so re-flatten its transitive dependents.
                self.rebuild_dependents(&name, out);
            }
            Err(e) => {
                out.push_str(&format!("error: view `{}`", v.name));
                if let Some(line) = v.source_line {
                    out.push_str(&format!(", line {line}"));
                }
                out.push_str(&format!(": {e}\n"));
            }
        }
    }

    /// Re-flatten and rebuild every currently-built module that transitively depends on `changed` (a
    /// module or view name that was just (re)defined). Flattening reads the module database and view store
    /// directly — never the cached [`modules`](Self::modules) map — so each dependent is rebuilt
    /// independently (rebuild order is irrelevant) and picks up the new definition. A dependent's own
    /// source is unchanged, so its recorded direct dependencies stay valid and need no refresh. If any
    /// module is rebuilt, the saved rewrite/search continuation is dropped (its engine is replaced).
    fn rebuild_dependents(&mut self, changed: &str, out: &mut String) {
        // Reverse-reachability over the direct-dependency graph: every name that reaches `changed`.
        let mut dependents: HashSet<String> = HashSet::new();
        let mut frontier = vec![changed.to_string()];
        while let Some(cur) = frontier.pop() {
            for (name, ds) in &self.deps {
                if ds.contains(&cur) && dependents.insert(name.clone()) {
                    frontier.push(name.clone());
                }
            }
        }
        // Rebuild only the ones that are actually built modules (views aren't built; a dependent that
        // failed to build earlier isn't cached). The changed name itself was already (re)built by the
        // caller, so exclude it.
        let mut invalidated = false;
        for name in dependents {
            if name == changed || !self.modules.contains_key(&name) {
                continue;
            }
            let built = {
                let mods = &self.modules;
                let home_mod = |n: &str| mods.get(n);
                flatten_and_build_with_host_functions(
                    &name,
                    &self.db,
                    &self.views,
                    &home_mod,
                    &mut self.interner,
                    &self.host_functions,
                )
            };
            match built {
                Ok(lm) => {
                    self.reported_identity_collapses
                        .retain(|(module, _, _)| module != &name);
                    self.modules.insert(name, lm);
                    invalidated = true;
                }
                Err(e) => {
                    out.push_str(&format!("error in module `{name}`: {e}\n"));
                    // The dropped dependent leaves `show modules` too; entering it again re-lists it.
                    self.modules.remove(&name);
                    self.order.retain(|module| module != &name);
                    self.reported_identity_collapses
                        .retain(|(module, _, _)| module != &name);
                    if self.current.as_deref() == Some(&name) {
                        self.current = None;
                    }
                    invalidated = true;
                }
            }
        }
        if invalidated {
            self.last = None;
        }
    }

    /// Run a `reduce`/`match` command against the current module.
    fn run_command(&mut self, c: Command, out: &mut String) {
        // Zero is invalid in bracketed execution bounds and gas fields; reject before module resolution.
        // The bare `continue 0` cursor uses a separate grammar and remains valid.
        let zero_bound = match &c {
            Command::Rewrite { bound, .. } => *bound == Some(0),
            Command::Frewrite { bound, gas, .. } | Command::ERewrite { bound, gas, .. } => {
                *bound == Some(0) || *gas == Some(0)
            }
            Command::Search {
                max_solutions,
                max_depth,
                ..
            }
            | Command::SmtSearch {
                max_solutions,
                max_depth,
                ..
            } => *max_solutions == Some(0) || *max_depth == Some(0),
            Command::GetVariants { bound, .. }
            | Command::VariantUnify { bound, .. }
            | Command::VariantMatch { bound, .. } => *bound == Some(0),
            Command::Narrow {
                max_solutions,
                max_depth,
                ..
            } => *max_solutions == Some(0) || *max_depth == Some(0),
            _ => false,
        };
        if zero_bound {
            // A rejected command emits no echo or result.
            out.push_str("parse error: a `[0]` bound is not allowed.\n");
            return;
        }
        // `in <MODULE> :` overrides the selected module for this command only.
        let m_override = match &c {
            Command::Reduce { module, .. }
            | Command::Check { module, .. }
            | Command::Match { module, .. }
            | Command::Rewrite { module, .. }
            | Command::Frewrite { module, .. }
            | Command::ERewrite { module, .. }
            | Command::Search { module, .. }
            | Command::SmtSearch { module, .. }
            | Command::Unify { module, .. }
            | Command::GetVariants { module, .. }
            | Command::VariantUnify { module, .. }
            | Command::VariantMatch { module, .. }
            | Command::Narrow { module, .. }
            | Command::Srewrite { module, .. } => module.clone(),
            Command::ShowNarrowing { .. } | Command::Continue { .. } => None,
        };
        let Some(cur) = m_override.or_else(|| self.current.clone()) else {
            out.push_str("error: no current module — enter a module first.\n");
            return;
        };
        if !self.modules.contains_key(&cur) {
            out.push_str(&format!("error: module `{cur}` does not exist.\n"));
            return;
        }
        match c {
            Command::Reduce { term, .. } => {
                self.last = None; // a non-continue command invalidates the saved rewrite continuation
                let reduce_gc_interval = self.reduce_gc_interval;
                let lm = self.modules.get_mut(&cur).expect("current module is built");
                let Some(parsed) =
                    parse_command_or_report(lm, &self.interner, &term, out)
                else {
                    return;
                };
                // Echo the normalized, pretty-printed term. The parsed tree is shared by echo and execution;
                // raw token joining is only a fallback when echo DAG construction fails, after which
                // execution reports the build error.
                let echo = command_echo(lm, &self.interner, &parsed, self.render_color)
                    .unwrap_or_else(|_| join_tokens(&term, &self.interner));
                lm.built.engine.set_trace(self.trace.master);
                lm.built.engine.set_record_whole(self.trace.master && self.trace.whole);
                lm.built.engine.set_gc_interval(reduce_gc_interval);
                // Build the subject, then reduce driving META-LEVEL descent: a `metaReduce(…)` redex is
                // handed to `MetaDescent`, which down-translates its meta-module argument into a real
                // object module (resolving imports from the db) and reduces in it. The descent borrows the
                // interner mutably, so it is dropped before the (immutable-interner) pretty-print.
                let reduced = build_command_dag(lm, &self.interner, &parsed).and_then(|dag| {
                    let mut descent = MetaDescent::new(
                        &mut self.interner,
                        &self.db,
                        &self.views,
                        &mut self.meta_state,
                    )
                    .with_host_functions(self.host_functions.clone());
                    let result = lm
                        .built
                        .engine
                        .try_reduce_with(dag, &mut descent)
                        .map_err(|fault| fault.to_string())?;
                    let rewrites = lm.built.engine.rewrites();
                    let model_stats = lm.built.engine.take_model_check_stats();
                    let sat_stats = lm.built.engine.take_sat_solve_stats();
                    Ok((result, rewrites, model_stats, sat_stats))
                });
                lm.built.engine.set_gc_interval(None);
                match reduced {
                    Ok((dag, rw, model_stats, sat_stats)) => {
                        let mut identity_diagnostics = String::new();
                        if self.verbose {
                            append_verbose_identity_collapse_diagnostics(
                                lm,
                                &cur,
                                &mut self.reported_identity_collapses,
                                &mut identity_diagnostics,
                            );
                        }
                        let mut verbose_stats = String::new();
                        if self.verbose {
                            for stats in model_stats {
                                verbose_stats.push_str(&format!(
                                    "ModelChecker: Property automaton has {} state{}.\n\
                                     ModelCheckerSymbol: Examined {} system state{}.\n",
                                    stats.property_automaton_states,
                                    if stats.property_automaton_states == 1 { "" } else { "s" },
                                    stats.examined_system_states,
                                    if stats.examined_system_states == 1 { "" } else { "s" },
                                ));
                            }
                            for stats in sat_stats {
                                verbose_stats.push_str(&format!(
                                    "SatSolverSymbol: Generalized Buchi automaton has {} state{} and {} fairness set{}.\n",
                                    stats.generalized_buchi_states,
                                    if stats.generalized_buchi_states == 1 { "" } else { "s" },
                                    stats.fairness_sets,
                                    if stats.fairness_sets == 1 { "" } else { "s" },
                                ));
                            }
                        }
                        let events = lm.built.engine.take_trace();
                        let trace = render_trace(&lm.built, &self.interner, &events, self.trace, self.render_color);
                        let eng = &lm.built.engine;
                        let sort = eng.sorts().name(eng.sort_of(dag)).to_string();
                        let value = print_pretty(&lm.built, &self.interner, dag, self.render_color);
                        let breakdown = rewrite_breakdown(lm, self.show_breakdown);
                        out.push_str(&format!(
                            "{identity_diagnostics}reduce in {cur} : {echo} .\n{trace}{verbose_stats}\
                             rewrites: {rw}{breakdown}\nresult {sort}: {value}\n"
                        ));
                    }
                    Err(e) => out.push_str(&format!("error: {e}\n")),
                }
            }
            Command::Check { term, .. } => {
                self.last = None;
                let lm = self.modules.get_mut(&cur).expect("current module is built");
                let Some(parsed) =
                    parse_command_or_report(lm, &self.interner, &term, out)
                else {
                    return;
                };
                let echo = command_echo(lm, &self.interner, &parsed, self.render_color)
                    .unwrap_or_else(|_| join_tokens(&term, &self.interner));
                match build_logic_command_dag(lm, &self.interner, &parsed) {
                    Ok(dag) => {
                        let mut solver = ConfiguredSmtEngine::default();
                        let result = solver.check_dag(&lm.built.engine, dag);
                        out.push_str(&format!("check in {cur} : {echo} .\n"));
                        match result {
                            SmtResult::Sat => {
                                out.push_str("Result from sat solver is: sat\n");
                            }
                            SmtResult::Unsat => {
                                out.push_str("Result from sat solver is: unsat\n");
                            }
                            SmtResult::Unknown => {
                                out.push_str("Result from sat solver is: undecided\n");
                            }
                            SmtResult::BadDag => {}
                        }
                    }
                    Err(e) => out.push_str(&format!("error: {e}\n")),
                }
            }
            Command::Match { pattern, subject, xmatch, .. } => {
                self.last = None;
                let (pe, se) =
                    (join_tokens(&pattern, &self.interner), join_tokens(&subject, &self.interner));
                let kw = if xmatch { "xmatch" } else { "match" };
                let lm = self.modules.get_mut(&cur).expect("current module is built");
                lm.built.engine.set_trace(false); // the match's subject-reduce is not traced (yet)
                lm.built.engine.set_record_whole(false);
                match match_command(lm, &self.interner, &pattern, &subject, xmatch) {
                    Ok(blocks) => out.push_str(&format!(
                        "{kw} in {cur} : {pe} <=? {se} .\n\n{}\n",
                        format_matchers(&blocks)
                    )),
                    Err(e) => out.push_str(&format!("error: {e}\n")),
                }
            }
            Command::Rewrite { bound, term, .. } => {
                self.last = None;
                let lm = self.modules.get_mut(&cur).expect("current module is built");
                lm.built.engine.reset_counter(); // a fresh `rewrite` restarts the `counter` built-in
                let Some(parsed) =
                    parse_command_or_report(lm, &self.interner, &term, out)
                else {
                    return;
                };
                let echo = command_echo(lm, &self.interner, &parsed, self.render_color)
                    .unwrap_or_else(|_| join_tokens(&term, &self.interner));
                lm.built.engine.set_trace(self.trace.master);
                lm.built.engine.set_record_whole(self.trace.master && self.trace.whole);
                let bound_str = bound.map(|n| format!(" [{n}]")).unwrap_or_default();
                match rewrite_command(lm, &self.interner, &parsed) {
                    Ok(mut rw) => match render_rewriting(
                        lm,
                        &self.interner,
                        self.trace,
                        self.render_color,
                        self.show_breakdown,
                        &mut rw,
                        bound,
                    ) {
                        Ok(body) => {
                            out.push_str(&format!(
                                "rewrite{bound_str} in {cur} : {echo} .\n{body}"
                            ));
                            // `lm`'s borrow ends above; save the session so `continue` can resume it.
                            self.last = Some((cur.clone(), Continuation::Rewrite(rw)));
                        }
                        Err(fault) => out.push_str(&format!("error: {fault}\n")),
                    },
                    Err(e) => out.push_str(&format!("error: {e}\n")),
                }
            }
            Command::Frewrite { bound, gas, term, .. } => {
                self.last = None;
                let lm = self.modules.get_mut(&cur).expect("current module is built");
                lm.built.engine.reset_counter(); // a fresh `frewrite` restarts the `counter` built-in
                let Some(parsed) =
                    parse_command_or_report(lm, &self.interner, &term, out)
                else {
                    return;
                };
                let echo = command_echo(lm, &self.interner, &parsed, self.render_color)
                    .unwrap_or_else(|_| join_tokens(&term, &self.interner));
                lm.built.engine.set_trace(self.trace.master);
                lm.built.engine.set_record_whole(self.trace.master && self.trace.whole);
                // Preserve the written bound form in the echo; omitted gas defaults to one application per
                // position per pass.
                let bound_str = match (bound, gas) {
                    (Some(n), Some(g)) => format!(" [{n}, {g}]"),
                    (Some(n), None) => format!(" [{n}]"),
                    (None, Some(g)) => format!(" [, {g}]"),
                    _ => String::new(),
                };
                match frewrite_command(lm, &self.interner, &parsed, gas.unwrap_or(1)) {
                    Ok(mut rw) => match render_rewriting(
                        lm,
                        &self.interner,
                        self.trace,
                        self.render_color,
                        self.show_breakdown,
                        &mut rw,
                        bound,
                    ) {
                        Ok(body) => {
                            out.push_str(&format!(
                                "frewrite{bound_str} in {cur} : {echo} .\n{body}"
                            ));
                            self.last = Some((cur.clone(), Continuation::Rewrite(rw)));
                        }
                        Err(fault) => out.push_str(&format!("error: {fault}\n")),
                    },
                    Err(e) => out.push_str(&format!("error: {e}\n")),
                }
            }
            Command::ERewrite { bound, gas, term, .. } => {
                let Session {
                    host_functions,
                    interner,
                    db,
                    modules,
                    views,
                    meta_state,
                    interpreters,
                    last,
                    stdin,
                    trace,
                    render_color,
                    show_breakdown,
                    ..
                } = self;
                *last = None;
                let lm = modules.get_mut(&cur).expect("current module is built");
                let Some(parsed) = parse_command_or_report(lm, interner, &term, out) else {
                    return;
                };
                let external_input = std::mem::take(stdin);
                lm.built.engine.reset_counter();
                lm.built.engine.reset_external();
                // Interpreter objects are capabilities of one top-level `erewrite` command. Starting a new
                // command discards the existing configuration and restarts child IDs at zero.
                *interpreters = InterpreterRegistry::default();
                lm.built.engine.set_external_input(external_input);
                let echo = command_echo(lm, interner, &parsed, *render_color)
                    .unwrap_or_else(|_| join_tokens(&term, interner));
                lm.built.engine.set_trace(trace.master);
                lm.built.engine.set_record_whole(trace.master && trace.whole);
                let bound_str = match (bound, gas) {
                    (Some(n), Some(g)) => format!(" [{n}, {g}]"),
                    (Some(n), None) => format!(" [{n}]"),
                    _ => String::new(),
                };
                match erewrite_command(lm, interner, &parsed, gas.unwrap_or(1)) {
                    Ok(mut rw) => match drive_external_rewriting(
                        &mut rw,
                        lm,
                        host_functions,
                        interner,
                        db,
                        views,
                        meta_state,
                        interpreters,
                        bound,
                    ) {
                        Ok(step) => {
                            let body = render_rewrite_step(
                                lm,
                                interner,
                                *trace,
                                *render_color,
                                *show_breakdown,
                                step,
                            );
                            let ext = lm.built.engine.take_external_out();
                            out.push_str(&format!(
                                "erewrite{bound_str} in {cur} : {echo} .\n{ext}{body}"
                            ));
                            *last = Some((cur.clone(), Continuation::Rewrite(rw)));
                        }
                        Err(fault) => out.push_str(&format!("error: {fault}\n")),
                    },
                    Err(e) => out.push_str(&format!("error: {e}\n")),
                }
                *stdin = lm.built.engine.take_external_input();
            }
            Command::Search { max_solutions, max_depth, subject, arrow, pattern, such_that, .. } => {
                self.last = None;
                let lm = self.modules.get_mut(&cur).expect("current module is built");
                lm.built.engine.set_trace(false); // ordinary search tracing is unsupported
                lm.built.engine.set_record_whole(false);
                let Some(subject_parsed) =
                    parse_command_or_report(lm, &self.interner, &subject, out)
                else {
                    return;
                };
                let Some(pattern_parsed) =
                    parse_command_or_report(lm, &self.interner, &pattern, out)
                else {
                    return;
                };
                let header = search_header(
                    lm,
                    &self.interner,
                    &subject_parsed,
                    arrow,
                    &pattern_parsed,
                    such_that.as_deref(),
                    self.render_color,
                );
                let bound_str = match (max_solutions, max_depth) {
                    (None, None) => String::new(),
                    (Some(n), None) => format!(" [{n}]"),
                    (Some(n), Some(m)) => format!(" [{n}, {m}]"),
                    (None, Some(m)) => format!(" [, {m}]"),
                };
                match search_command(
                    lm,
                    &self.interner,
                    &subject_parsed,
                    arrow,
                    &pattern_parsed,
                    such_that.as_deref(),
                    max_depth,
                ) {
                    Ok((search, vars)) => {
                        let mut session = SearchSession { search, vars };
                        match render_search(
                            &mut session,
                            lm,
                            &self.interner,
                            self.render_color,
                            max_solutions,
                            self.show_breakdown,
                        ) {
                            Ok(body) => {
                                out.push_str(&format!(
                                    "search{bound_str} in {cur} : {header} .\n{body}"
                                ));
                                self.last =
                                    Some((cur.clone(), Continuation::Search(Box::new(session))));
                            }
                            Err(fault) => out.push_str(&format!("error: {fault}\n")),
                        }
                    }
                    Err(e) => out.push_str(&format!("error: {e}\n")),
                }
            }
            Command::SmtSearch {
                max_solutions,
                max_depth,
                subject,
                arrow,
                pattern,
                such_that,
                ..
            } => {
                self.last = None;
                let lm = self.modules.get_mut(&cur).expect("current module is built");
                lm.built.engine.set_trace(false);
                lm.built.engine.set_record_whole(false);
                let Some(subject_parsed) =
                    parse_command_or_report(lm, &self.interner, &subject, out)
                else {
                    return;
                };
                let Some(pattern_parsed) =
                    parse_command_or_report(lm, &self.interner, &pattern, out)
                else {
                    return;
                };
                let header = search_header(
                    lm,
                    &self.interner,
                    &subject_parsed,
                    arrow,
                    &pattern_parsed,
                    such_that.as_deref(),
                    self.render_color,
                );
                let bound_str = match (max_solutions, max_depth) {
                    (None, None) => String::new(),
                    (Some(n), None) => format!(" [{n}]"),
                    (Some(n), Some(m)) => format!(" [{n}, {m}]"),
                    (None, Some(m)) => format!(" [, {m}]"),
                };
                // A request rejected during construction (`=>!`, the SMT-rewriting restrictions, or a
                // `such that` condition) gets no echo, search, or continuation, as for `search`.
                match smt_search_command(
                    lm,
                    &mut self.interner,
                    &subject_parsed,
                    arrow,
                    &pattern_parsed,
                    such_that.as_deref(),
                    max_depth,
                ) {
                    Ok(command) => {
                        let mut session = SmtSearchSession {
                            search: command.search,
                            goal_variables: command.goal_variables,
                            target_variable_count: command.target_variable_count,
                            shown_total: 0,
                        };
                        let body = render_smt_search(
                            &mut session,
                            lm,
                            &self.interner,
                            self.render_color,
                            max_solutions,
                        );
                        out.push_str(&format!(
                            "smt-search{bound_str} in {cur} : {header} .\n{body}"
                        ));
                        self.last =
                            Some((cur.clone(), Continuation::SmtSearch(Box::new(session))));
                    }
                    Err(e) => out.push_str(&format!("error: {e}\n")),
                }
            }
            Command::Srewrite { depth_first, term, mut strategy, .. } => {
                let lm = self.modules.get_mut(&cur).expect("current module is built");
                tnk_frontend::strategy::discard_inapplicable_top(&mut strategy, lm);
                let Some(parsed) =
                    parse_command_or_report(lm, &self.interner, &term, out)
                else {
                    return;
                };
                let kw = if depth_first { "dsrewrite" } else { "srewrite" };
                let echo = command_echo(lm, &self.interner, &parsed, self.render_color)
                    .unwrap_or_else(|_| join_tokens(&term, &self.interner));
                let strat_str = tnk_frontend::strategy::print_strategy(&strategy, &self.interner);
                match tnk_frontend::strategy::srewrite_command(
                    lm, &self.interner, &parsed, &strategy, depth_first,
                ) {
                    Ok((sols, total)) => {
                        self.last = None;
                        let mut body = String::new();
                        if sols.is_empty() {
                            body.push_str(&format!("\nNo solution.\nrewrites: {total}\n"));
                        } else {
                            let eng = &lm.built.engine;
                            for (k, s) in sols.iter().enumerate() {
                                let sort = eng.sorts().name(eng.sort_of(s.term)).to_string();
                                let value = print_pretty(&lm.built, &self.interner, s.term, self.render_color);
                                body.push_str(&format!(
                                    "\nSolution {}\nrewrites: {}\nresult {sort}: {value}\n",
                                    k + 1,
                                    s.rewrites
                                ));
                            }
                            body.push_str(&format!("\nNo more solutions.\nrewrites: {total}\n"));
                        }
                        out.push_str(&format!("{kw} in {cur} : {echo} using {strat_str} .\n{body}"));
                    }
                    Err(tnk_frontend::strategy::StrategicRewriteError::Reducer(fault)) => {
                        self.last = None;
                        out.push_str(&format!("error: {fault}\n"));
                    }
                    Err(error) => out.push_str(&format!("error: {error}\n")),
                }
            }
            Command::Unify { bound, irredundant, body, .. } => {
                self.last = None;
                let limit = bound.unwrap_or(u64::MAX);
                let irr = if irredundant { "irredundant " } else { "" };
                let bnd = bound.map(|n| format!("[{n}] ")).unwrap_or_default();
                // The interner and the module engine are disjoint fields — borrow both.
                let (interner, modules) = (&mut self.interner, &mut self.modules);
                let lm = modules.get_mut(&cur).expect("current module is built");
                match unify_command(lm, interner, &body) {
                    Err(e) => out.push_str(&format!("error: {e}\n")),
                    Ok(mut uc) => {
                        if uc.readiness != UnifyReadiness::Ready {
                            out.push_str(&format!(
                                "{irr}unify {bnd}in {cur} : {} .\n",
                                uc.echo
                            ));
                            return;
                        }

                        // Collect unifiers while the engine is borrowed, then render after releasing
                        // the mutable interner borrow.
                        let enumeration = {
                            let mut names = InternerNames(interner);
                            let mut env = tnk_core::unify::UnifyEnv {
                                e: &mut lm.built.engine,
                                names: &mut names,
                            };
                            (|| -> Result<Vec<Vec<DagId>>, ReducerFault> {
                                let mut unifiers = Vec::new();
                                while (unifiers.len() as u64) < limit {
                                    match uc.problem.try_find_next(&mut env)? {
                                        Some(binding) => unifiers.push(binding),
                                        None => break,
                                    }
                                }
                                Ok(unifiers)
                            })()
                        };
                        let mut unifiers = match enumeration {
                            Ok(unifiers) => unifiers,
                            Err(fault) => {
                                out.push_str(&format!("error: {fault}\n"));
                                return;
                            }
                        };
                        if irredundant {
                            match tnk_core::unify::filter::try_irredundant(
                                &mut lm.built.engine,
                                unifiers,
                            ) {
                                Ok(filtered) => unifiers = filtered,
                                Err(fault) => {
                                    out.push_str(&format!("error: {fault}\n"));
                                    return;
                                }
                            }
                        }

                        out.push_str(&format!("{irr}unify {bnd}in {cur} : {} .\n", uc.echo));
                        if unifiers.is_empty() {
                            out.push_str("No unifier.\n");
                        } else {
                            for (n, unifier) in unifiers.iter().enumerate() {
                                out.push_str(&format!(
                                    "\nUnifier {}\n{}\n",
                                    n + 1,
                                    render_unifier(&lm.built, interner, &uc.var_names, unifier)
                                ));
                            }
                        }
                    }
                }
            }
            Command::GetVariants { bound, irredundant, term, blockers, .. } => {
                self.last = None;
                let irr = if irredundant { "irredundant " } else { "" };
                let bnd = bound.map(|n| format!(" [{n}]")).unwrap_or_default();
                let (interner, modules) = (&mut self.interner, &mut self.modules);
                let lm = modules.get_mut(&cur).expect("current module is built");
                let blocker_terms = (!blockers.is_empty()).then_some(blockers.as_slice());
                match variant_command(lm, interner, &term, blocker_terms, irredundant) {
                    Err(e) => out.push_str(&format!("error: {e}\n")),
                    Ok(vc) => {
                        if vc.names_ok {
                            let mut session = VariantSession {
                                search: vc.search,
                                var_names: vc.var_names,
                                irredundant,
                                reported_total: false,
                            };
                            match render_variants(
                                &mut session,
                                lm,
                                interner,
                                self.render_color,
                                bound,
                            ) {
                                Ok(body) => {
                                    out.push_str(&format!(
                                        "get {irr}variants{bnd} in {cur} : {} .\n{body}",
                                        vc.echo
                                    ));
                                    self.last = Some((
                                        cur.clone(),
                                        Continuation::Variants(Box::new(session)),
                                    ));
                                }
                                Err(fault) => out.push_str(&format!("error: {fault}\n")),
                            }
                        } else {
                            out.push_str(&format!(
                                "get {irr}variants{bnd} in {cur} : {} .\n",
                                vc.echo
                            ));
                        }
                    }
                }
            }
            Command::VariantUnify { bound, filtered, body, blockers, .. } => {
                self.last = None;
                let prefix = if filtered { "filtered " } else { "" };
                let bnd = bound.map(|n| format!(" [{n}]")).unwrap_or_default();
                let (interner, modules) = (&mut self.interner, &mut self.modules);
                let lm = modules.get_mut(&cur).expect("current module is built");
                let blocker_terms = (!blockers.is_empty()).then_some(blockers.as_slice());
                match variant_unify_command(lm, interner, &body, blocker_terms, filtered) {
                    Err(e) => out.push_str(&format!("error: {e}\n")),
                    Ok(vc) => {
                        if vc.names_ok {
                            let mut session = VariantUnifySession {
                                search: vc.search,
                                var_names: vc.var_names,
                                stream: tnk_core::variant::FilteredVariantUnifierStream::new(filtered),
                                upfront: filtered,
                                matching: false,
                                subject: None,
                                restorations: Vec::new(),
                                fresh_base: "0".to_string(),
                                prepared: false,
                                exhausted: false,
                                reported_total: false,
                                next_number: 0,
                            };
                            match render_variant_unifiers(
                                &mut session,
                                lm,
                                interner,
                                bound,
                                self.show_breakdown,
                            ) {
                                Ok(body) => {
                                    out.push_str(&format!(
                                        "{prefix}variant unify{bnd} in {cur} : {} .\n{body}",
                                        vc.echo
                                    ));
                                    self.last = Some((
                                        cur.clone(),
                                        Continuation::VariantUnifiers(Box::new(session)),
                                    ));
                                }
                                Err(fault) => out.push_str(&format!("error: {fault}\n")),
                            }
                        } else {
                            out.push_str(&format!(
                                "{prefix}variant unify{bnd} in {cur} : {} .\n",
                                vc.echo
                            ));
                        }
                    }
                }
            }
            Command::VariantMatch { bound, pattern, subject, blockers, .. } => {
                self.last = None;
                let bnd = bound.map(|n| format!(" [{n}]")).unwrap_or_default();
                let (interner, modules) = (&mut self.interner, &mut self.modules);
                let lm = modules.get_mut(&cur).expect("current module is built");
                let blocker_terms = (!blockers.is_empty()).then_some(blockers.as_slice());
                match variant_match_command(lm, interner, &pattern, &subject, blocker_terms) {
                    Err(e) => out.push_str(&format!("error: {e}\n")),
                    Ok(vc) => {
                        if vc.names_ok {
                            let mut session = VariantUnifySession {
                                search: vc.search,
                                var_names: vc.var_names,
                                stream: tnk_core::variant::FilteredVariantUnifierStream::new(false),
                                upfront: true,
                                matching: true,
                                subject: Some(vc.subject),
                                restorations: vc.restorations,
                                fresh_base: vc.fresh_base,
                                prepared: false,
                                exhausted: false,
                                reported_total: false,
                                next_number: 0,
                            };
                            match render_variant_unifiers(
                                &mut session,
                                lm,
                                interner,
                                bound,
                                self.show_breakdown,
                            ) {
                                Ok(body) => {
                                    out.push_str(&format!(
                                        "variant match{bnd} in {cur} : {} .\n{body}",
                                        vc.echo
                                    ));
                                    self.last = Some((
                                        cur.clone(),
                                        Continuation::VariantUnifiers(Box::new(session)),
                                    ));
                                }
                                Err(fault) => out.push_str(&format!("error: {fault}\n")),
                            }
                        } else {
                            out.push_str(&format!(
                                "variant match{bnd} in {cur} : {} .\n",
                                vc.echo
                            ));
                        }
                    }
                }
            }
            Command::Narrow {
                max_solutions,
                max_depth,
                subject,
                arrow,
                goal,
                condition,
                fold,
                vfold,
                path,
                filter,
                delay,
                fvu,
                ..
            } => {
                self.last = None;
                if condition.is_some() {
                    out.push_str("error: conditions are not currently supported for narrowing.\n");
                    return;
                }
                let bound_str = match (max_solutions, max_depth) {
                    (None, None) => String::new(),
                    (Some(n), None) => format!(" [{n}]"),
                    (Some(n), Some(m)) => format!(" [{n}, {m}]"),
                    (None, Some(m)) => format!(" [, {m}]"),
                };
                let prefix = if fvu {
                    String::new()
                } else {
                    let mut options = Vec::new();
                    if fold {
                        options.push("fold");
                    }
                    if vfold {
                        options.push("vfold");
                    }
                    if path {
                        options.push("path");
                    }
                    if options.is_empty() {
                        String::new()
                    } else {
                        format!("{{{}}} ", options.join(", "))
                    }
                };
                let keyword = if fvu { "fvu-narrow" } else { "vu-narrow" };
                let mut stream_options = Vec::new();
                if delay {
                    stream_options.push("delay");
                }
                if filter {
                    stream_options.push("filter");
                }
                let stream_options = if stream_options.is_empty() {
                    String::new()
                } else {
                    format!(" {{{}}}", stream_options.join(", "))
                };
                let arrow_echo = match arrow {
                    SearchArrow::One => "=>1",
                    SearchArrow::Plus => "=>+",
                    SearchArrow::Star => "=>*",
                    SearchArrow::Bang => "=>!",
                };
                let verbose = self.verbose;
                let (interner, modules, reported_identity_collapses) = (
                    &mut self.interner,
                    &mut self.modules,
                    &mut self.reported_identity_collapses,
                );
                let lm = modules.get_mut(&cur).expect("current module is built");
                match narrow_command(
                    lm,
                    interner,
                    &subject,
                    arrow,
                    &goal,
                    max_depth,
                    fold,
                    vfold,
                    path,
                    filter,
                    delay,
                ) {
                    Err(error) => out.push_str(&format!("error: {error}\n")),
                    Ok(command) => {
                        if verbose {
                            append_verbose_identity_collapse_diagnostics(
                                lm,
                                &cur,
                                reported_identity_collapses,
                                out,
                            );
                        }
                        let mut session = NarrowSession {
                            search: command.search,
                            variables: command.variables,
                            initial_variable_count: command.initial_variable_count,
                            initial_variables: command.initial_variables,
                            initial_echoes: command.initial_echoes,
                            next_number: 0,
                            path,
                        };
                        match render_narrowing(
                            &mut session,
                            lm,
                            interner,
                            self.render_color,
                            self.show_breakdown,
                            verbose,
                            path,
                            max_solutions,
                        ) {
                            Ok(body) => {
                                out.push_str(&format!(
                                    "{prefix}{keyword}{stream_options}{bound_str} in {cur} : {} \
                                     {arrow_echo} {} .\n{body}",
                                    command.subject_echo, command.goal_echo
                                ));
                                self.last =
                                    Some((cur.clone(), Continuation::Narrow(Box::new(session))));
                            }
                            Err(fault) => out.push_str(&format!("error: {fault}\n")),
                        }
                    }
                }
            }
            Command::ShowNarrowing { display, state } => {
                let Some((module, Continuation::Narrow(session))) = &mut self.last else {
                    out.push_str("error: no narrowing state graph is available.\n");
                    return;
                };
                if *module != cur {
                    out.push_str("error: the narrowing state graph belongs to another module.\n");
                    return;
                }
                let lm = self.modules.get_mut(&cur).expect("current module is built");
                let body = render_narrowing_display(
                    session,
                    lm,
                    &self.interner,
                    self.render_color,
                    display,
                    state.map(|number| number as usize),
                );
                out.push_str(&body);
                out.push('\n');
            }
            Command::Continue { bound } => match self.last.take() {
                Some((m, Continuation::Rewrite(mut rw))) if m == cur => {
                    let lm = self.modules.get_mut(&cur).expect("current module is built");
                    lm.built.engine.set_trace(self.trace.master);
                    lm.built.engine.set_record_whole(self.trace.master && self.trace.whole);
                    // `continue` reports only rewrites performed after resuming, so start with a fresh counter.
                    lm.built.engine.reset_rewrites();
                    match render_rewriting(
                        lm,
                        &self.interner,
                        self.trace,
                        self.render_color,
                        self.show_breakdown,
                        &mut rw,
                        bound,
                    ) {
                        Ok(body) => {
                            out.push_str(&body);
                            self.last = Some((m, Continuation::Rewrite(rw)));
                        }
                        Err(fault) => out.push_str(&format!("error: {fault}\n")),
                    }
                }
                Some((m, Continuation::Search(mut session))) if m == cur => {
                    let lm = self.modules.get_mut(&cur).expect("current module is built");
                    // Search continuation statistics count only work performed after resuming, so reset
                    // before newly generated states snapshot their rewrite count.
                    lm.built.engine.reset_rewrites();
                    match render_search(
                        &mut session,
                        lm,
                        &self.interner,
                        self.render_color,
                        bound,
                        self.show_breakdown,
                    ) {
                        Ok(body) => {
                            out.push_str(&body);
                            self.last = Some((m, Continuation::Search(session)));
                        }
                        Err(fault) => out.push_str(&format!("error: {fault}\n")),
                    }
                }
                Some((m, Continuation::SmtSearch(mut session))) if m == cur => {
                    let lm = self.modules.get_mut(&cur).expect("current module is built");
                    lm.built.engine.reset_rewrites();
                    let body = render_smt_search(
                        &mut session,
                        lm,
                        &self.interner,
                        self.render_color,
                        bound,
                    );
                    out.push_str(&body);
                    self.last = Some((m, Continuation::SmtSearch(session)));
                }
                Some((m, Continuation::Variants(mut session))) if m == cur => {
                    let lm = self.modules.get_mut(&cur).expect("current module is built");
                    lm.built.engine.reset_rewrites();
                    match render_variants(
                        &mut session,
                        lm,
                        &mut self.interner,
                        self.render_color,
                        bound,
                    ) {
                        Ok(body) => {
                            out.push_str(&body);
                            self.last = Some((m, Continuation::Variants(session)));
                        }
                        Err(fault) => out.push_str(&format!("error: {fault}\n")),
                    }
                }
                Some((m, Continuation::VariantUnifiers(mut session))) if m == cur => {
                    let lm = self.modules.get_mut(&cur).expect("current module is built");
                    lm.built.engine.reset_rewrites();
                    match render_variant_unifiers(
                        &mut session,
                        lm,
                        &mut self.interner,
                        bound,
                        self.show_breakdown,
                    ) {
                        Ok(body) => {
                            out.push_str(&body);
                            self.last = Some((m, Continuation::VariantUnifiers(session)));
                        }
                        Err(fault) => out.push_str(&format!("error: {fault}\n")),
                    }
                }
                Some((m, Continuation::Narrow(mut session))) if m == cur => {
                    let lm = self.modules.get_mut(&cur).expect("current module is built");
                    lm.built.engine.reset_rewrites();
                    let show_state_number = session.path;
                    match render_narrowing(
                        &mut session,
                        lm,
                        &mut self.interner,
                        self.render_color,
                        self.show_breakdown,
                        self.verbose,
                        show_state_number,
                        bound,
                    ) {
                        Ok(body) => {
                            out.push_str(&body);
                            self.last = Some((m, Continuation::Narrow(session)));
                        }
                        Err(fault) => out.push_str(&format!("error: {fault}\n")),
                    }
                }
                _ => out.push_str(
                    "error: no previous rewriting, search, or variant enumeration to continue in this \
                     module.\n",
                ),
            },
        }
    }

    /// `select <NAME> .` — make `NAME` the current module.
    fn meta_select(&mut self, line: &str) -> Eval {
        let name = line
            .split_whitespace()
            .nth(1)
            .map(|s| s.trim_end_matches('.'))
            .unwrap_or("");
        let out = if name.is_empty() {
            "error: select: expected a module name.".to_string()
        } else if self.modules.contains_key(name) {
            if self.current.as_deref() != Some(name) {
                self.meta_state.clear();
            }
            self.current = Some(name.to_string());
            self.last = None; // switching modules invalidates the saved rewrite continuation
            String::new()
        } else {
            format!("error: select: no module `{name}` — enter it first.")
        };
        Eval {
            output: out,
            exit: false,
        }
    }

    /// `show modules` (the entered names) or `show module [NAME]` (a module's sorts + ops).
    fn meta_show(&mut self, line: &str) -> Eval {
        let words: Vec<&str> = line
            .split_whitespace()
            .map(|s| s.trim_end_matches('.'))
            .filter(|s| !s.is_empty())
            .collect();
        let out = match words.get(1).copied() {
            Some("modules") => {
                let list = if self.order.is_empty() {
                    "(none)".into()
                } else {
                    self.order.join(" ")
                };
                format!("modules: {list}")
            }
            Some("module") => {
                let requested = words.get(2).copied();
                match requested
                    .or(self.current.as_deref())
                    .and_then(|n| self.modules.get(n).map(|lm| (n, lm)))
                {
                    Some((n, lm)) => render_module(n, lm),
                    None => match requested {
                        Some(n) => format!("error: show module: no such module `{n}`."),
                        None => "error: show module: no current module.".into(),
                    },
                }
            }
            Some("views") => {
                let list = if self.view_order.is_empty() {
                    "(none)".into()
                } else {
                    self.view_order.join(" ")
                };
                format!("views: {list}")
            }
            Some("view") => match words.get(2).and_then(|n| self.views.get(n)) {
                Some(v) => render_view(v, &self.interner),
                None => "error: show view: no such view (usage: `show view NAME .`).".into(),
            },
            // `show path [states] N .` — regular-search or narrowing history.
            Some("path") => {
                let path_states = words.get(2).copied() == Some("states");
                let number_slot = if path_states { 3 } else { 2 };
                let n: Option<usize> = words.get(number_slot).and_then(|s| s.parse().ok());
                match (n, self.current.as_deref()) {
                    (Some(n), Some(cur)) => match &self.last {
                        Some((m, Continuation::Search(session))) if m == cur && !path_states => {
                            let lm = self.modules.get(cur).expect("current module is built");
                            render_path(&session.search, lm, &self.interner, n, self.render_color)
                        }
                        Some((m, Continuation::Narrow(session))) if m == cur => {
                            let lm = self.modules.get(cur).expect("current module is built");
                            render_narrowing_display(
                                session,
                                lm,
                                &self.interner,
                                self.render_color,
                                if path_states {
                                    NarrowDisplay::PathStates
                                } else {
                                    NarrowDisplay::Path
                                },
                                Some(n),
                            )
                        }
                        // `path states` renders only narrowing histories; do not report the current
                        // ordinary search as missing.
                        Some((m, Continuation::Search(_))) if m == cur => {
                            "error: show path states: not available for an ordinary search; use \
                             `show path N .`."
                                .into()
                        }
                        _ => "error: show path: no current search (run `search` first).".into(),
                    },
                    (None, _) => "error: show path: expected a state number.".into(),
                    _ => "error: show path: no current module.".into(),
                }
            }
            Some("frontier") if words.get(2).copied() == Some("states") => {
                match self.current.as_deref() {
                    Some(cur) => match &self.last {
                        Some((m, Continuation::Narrow(session))) if m == cur => {
                            let lm = self.modules.get(cur).expect("current module is built");
                            render_narrowing_display(
                                session,
                                lm,
                                &self.interner,
                                self.render_color,
                                NarrowDisplay::Frontier,
                                None,
                            )
                        }
                        _ => "error: show frontier states: no narrowing state graph is available."
                            .into(),
                    },
                    None => "error: show frontier states: no current module.".into(),
                }
            }
            Some("most")
                if words.get(2).copied() == Some("general")
                    && words.get(3).copied() == Some("states") =>
            {
                match self.current.as_deref() {
                    Some(cur) => match &self.last {
                        Some((m, Continuation::Narrow(session))) if m == cur => {
                            let lm = self.modules.get(cur).expect("current module is built");
                            render_narrowing_display(
                                session,
                                lm,
                                &self.interner,
                                self.render_color,
                                NarrowDisplay::MostGeneral,
                                None,
                            )
                        }
                        _ => "error: show most general states: no narrowing state graph is \
                              available."
                            .into(),
                    },
                    None => "error: show most general states: no current module.".into(),
                }
            }
            // `show search graph .` — the whole reachable-state graph of the last search.
            Some("search")
                if words.get(3).copied() == Some("graph")
                    || words.get(2).copied() == Some("graph") =>
            {
                match self.current.as_deref() {
                    Some(cur) => match &self.last {
                        Some((m, Continuation::Search(session))) if m == cur => {
                            let lm = self.modules.get(cur).expect("current module is built");
                            render_graph(&session.search, lm, &self.interner, self.render_color)
                        }
                        _ => "error: show search graph: no current search.".into(),
                    },
                    None => "error: show search graph: no current module.".into(),
                }
            }
            _ => {
                let forms = "`show modules .`, `show module [NAME] .`, `show views .`, \
                             `show view NAME .`, `show path [states] N .`, `show search graph .`, \
                             `show frontier states .`, or `show most general states .`";
                // Name only the form's first word; the dispatched chunk can hold later source text.
                match words.get(1) {
                    Some(form) => format!("error: show: unknown form `{form}`; try {forms}."),
                    None => format!("error: show: expected a form; try {forms}."),
                }
            }
        };
        Eval {
            output: out,
            exit: false,
        }
    }

    /// Dispatch supported `set` controls: trace flags, include BOOL, timing diagnostics, breakdown, and
    /// verbose mode. Memoization controls report their explicit unsupported warning.
    fn meta_set(&mut self, line: &str) -> Eval {
        let words: Vec<&str> = line
            .split_whitespace()
            .map(|word| word.trim_end_matches('.'))
            .filter(|word| !word.is_empty())
            .collect();
        let out = match words.get(1).copied() {
            // A rejected trace request changes no flag and reports a command diagnostic.
            Some("trace") => match self.trace.apply(&words[2..]) {
                Ok(()) => String::new(),
                Err(error) => format!("error: {error}"),
            },
            Some("memo") => unsupported_memo_control_warning().to_string(),
            Some("clear") if words.get(2).copied() == Some("memo") => {
                unsupported_memo_control_warning().to_string()
            }
            // `set include BOOL on|off`: toggle the implicit-BOOL auto-import. Other
            // `set include <MOD>` names remain silent no-ops (nothing else is auto-imported).
            Some("include") if words.get(2).copied() == Some("BOOL") => {
                match words.get(3).copied() {
                    Some("on") => self.include_bool = true,
                    Some("off") => self.include_bool = false,
                    _ => {}
                }
                String::new()
            }
            // Timing measurement is not implemented. `off` is silent; `on` reports the unavailable
            // capability and leaves timing output disabled.
            Some("show") if words.get(2).copied() == Some("timing") => {
                match words.get(3).copied() {
                    Some("on") => unsupported_timing_control_warning().to_string(),
                    _ => String::new(),
                }
            }
            Some("show") if words.get(2).copied() == Some("breakdown") => {
                match words.get(3).copied() {
                    Some("on") => self.show_breakdown = true,
                    Some("off") => self.show_breakdown = false,
                    _ => {}
                }
                String::new()
            }
            Some("verbose") => {
                match words.get(2).copied() {
                    Some("on") => self.verbose = true,
                    Some("off") => self.verbose = false,
                    _ => {}
                }
                String::new()
            }
            // Unknown directives remain inert. Recognized commands with unavailable semantics are handled
            // explicitly above instead of disappearing silently.
            _ => String::new(),
        };
        Eval {
            output: out,
            exit: false,
        }
    }

    /// `load <file>` / `sload <file>`: read the file and evaluate its contents in place
    /// (modules + commands), resolving relative to the CWD then `$MAUDE_LIB` (colon-separated),
    /// with and without an appended `.maude`. `sload` skips a file that was already loaded.
    fn meta_load(&mut self, sload: bool, path: &str) -> Eval {
        if path.is_empty() {
            return Eval {
                output: "error: load needs a file name".into(),
                exit: false,
            };
        }
        let mut candidates: Vec<std::path::PathBuf> = Vec::new();
        for base in [path.to_string(), format!("{path}.maude")] {
            candidates.push(std::path::PathBuf::from(&base));
            if let Ok(lib) = std::env::var("MAUDE_LIB") {
                for dir in lib.split(':').filter(|d| !d.is_empty()) {
                    candidates.push(std::path::Path::new(dir).join(&base));
                }
            }
        }
        let Some(found) = candidates.iter().find(|p| p.is_file()) else {
            return Eval {
                output: format!("error: cannot open file `{path}`"),
                exit: false,
            };
        };
        let canonical = std::fs::canonicalize(found).unwrap_or_else(|_| found.clone());
        if sload && self.loaded_files.contains(&canonical) {
            return Eval::default(); // already loaded: sload is a silent skip
        }
        let src = match std::fs::read_to_string(found) {
            Ok(s) => s,
            Err(e) => {
                return Eval {
                    output: format!("error: cannot read `{path}`: {e}"),
                    exit: false,
                };
            }
        };
        self.loaded_files.insert(canonical);
        self.eval_dispatch(&src)
    }

    /// Whether `input` forms a complete submission — the multi-line buffer boundary for the binary.
    /// Complete iff it is a bare `quit`/`q`/`exit`, or its last token closes a module (`endfm`/…) or is a
    /// terminator `.` at module-depth 0 (so a half-typed module body keeps buffering).
    pub fn input_complete(&mut self, input: &str) -> bool {
        let trimmed = input.trim();
        if trimmed.is_empty() {
            return false;
        }
        if matches!(trimmed, "quit" | "q" | "exit") {
            return true;
        }
        // `load`/`sload` are line-terminated (a final `.` is optional): a submission whose first
        // TOKEN is the keyword (leading comments stripped by the lexer) is complete at its line end —
        // both drivers append whole lines, so the buffer already ends at one.
        {
            let toks = tokenize(input, &mut self.interner);
            if let Some(t) = toks.first()
                && matches!(self.interner.resolve(t.sym), "load" | "sload")
            {
                return true;
            }
        }
        let toks = tokenize(input, &mut self.interner);
        let Some(last) = toks.last().copied() else {
            return false;
        };
        // Track module nesting, but only count a module keyword (`fmod`/`endfm`/…) when it is a real
        // delimiter: at bracket depth 0 and in statement-leading position. The meta-level's
        // module-constructor operators put `fmod`/`is`/`sorts`/`endfm` *inside* a term
        // (`getName(fmod Q is … endfm) = Q`), where they are operator-name fragments, not delimiters —
        // counting those would close the module early and submit it without its `endfm`.
        let is_close = |s: &str| {
            matches!(
                s,
                "endfm"
                    | "endm"
                    | "endfth"
                    | "endth"
                    | "endv"
                    | "endsm"
                    | "endsth"
                    | "endom"
                    | "endoth"
            )
        };
        // A command keyword *claims* the statement it leads (`red …`, `search …`): a module-open keyword
        // inside a command's term (`red fmod … endfm .`, `reduce metaReduce(…)`) is then an operator-name
        // fragment, not a real module. Junk tokens do NOT claim the statement, so a module preceded by
        // top-level junk (`junkalpha … fmod MC …`) is still recognized — the buffer
        // must not complete mid-module at the module's first inner `.`.
        let is_command = |s: &str| {
            matches!(
                s,
                "reduce"
                    | "red"
                    | "rewrite"
                    | "rew"
                    | "frewrite"
                    | "frew"
                    | "erewrite"
                    | "erew"
                    | "search"
                    | "smt-search"
                    | "match"
                    | "xmatch"
                    | "continue"
                    | "cont"
                    | "srewrite"
                    | "srew"
                    | "dsrewrite"
                    | "dsrew"
                    | "unify"
                    | "irredundant"
                    | "irred"
            )
        };
        let is_open = |s: &str| {
            matches!(
                s,
                "fmod" | "mod" | "fth" | "th" | "smod" | "sth" | "omod" | "oth" | "view"
            )
        };
        let mut open = false;
        let mut saw_open = false;
        let mut reflected_module_depth = 0u32;
        let mut depth = 0i32;
        let mut leading = true; // start, just after a depth-0 `.`, or just after a module delimiter
        let mut claimed = false; // the current statement is a command (its body is a term, not a module)
        for t in &toks {
            let txt = self.interner.resolve(t.sym);
            // A command keyword at statement-leading position claims the statement (its module keywords are
            // term fragments). Outside a module, a module-open keyword still ignores leading junk. Inside a
            // module, an unparenthesized reflected constructor (`= fmod ... endfm`) gets its own depth so its
            // closing keyword cannot be mistaken for the enclosing source module's close.
            if depth == 0 && leading && is_command(txt) {
                claimed = true;
            }
            let mut real_close = false;
            if depth == 0 && !claimed && is_open(txt) {
                if open {
                    reflected_module_depth += 1;
                } else {
                    open = true;
                    saw_open = true;
                }
            } else if depth == 0 && is_close(txt) {
                if reflected_module_depth > 0 {
                    reflected_module_depth -= 1;
                } else if open {
                    open = false;
                    real_close = true;
                }
            }
            match txt {
                "(" | "[" | "{" => depth += 1,
                ")" | "]" | "}" => depth -= 1,
                _ => {}
            }
            let boundary =
                (t.kind == TokKind::Dot && depth == 0 && reflected_module_depth == 0) || real_close;
            leading = boundary;
            if boundary {
                claimed = false; // a new statement begins after a depth-0 `.` / real module close
            }
        }
        let last_txt = self.interner.resolve(last.sym);
        let module_closed =
            is_close(last_txt) && saw_open && !open && reflected_module_depth == 0 && depth == 0;
        module_closed || (last.kind == TokKind::Dot && depth == 0 && !open)
    }
}

fn unsupported_memo_control_warning() -> &'static str {
    "warning: memoization controls are recognized but not implemented; this command has no effect."
}

fn unsupported_timing_control_warning() -> &'static str {
    "warning: timing measurements are unavailable; timing output remains disabled."
}

fn unsupported_memo_diagnostics(pm: &PreModule, interner: &Interner) -> Vec<Diagnostic> {
    pm.ops
        .iter()
        .filter(|op| op.attrs.memo)
        .map(|op| {
            let name = canonical_name(&op.name, interner);
            Diagnostic::warning(
                pm.name.clone(),
                op.name.first().map(|token| token.line),
                format!("operator `{name}`"),
                format!(
                    "`[memo]` on operator `{name}` is recognized but not implemented; \
                     evaluation continues without memoization"
                ),
            )
        })
        .collect()
}

fn sort_diagnostics(diagnostics: &mut Vec<Diagnostic>, root: &str) {
    let mut module_order = HashMap::<String, usize>::new();
    module_order.insert(root.to_string(), 0);
    for diagnostic in diagnostics.iter() {
        let next = module_order.len();
        if let Some(module) = diagnostic.module.as_ref() {
            module_order.entry(module.clone()).or_insert(next);
        }
    }
    diagnostics.sort_by_key(|diagnostic| {
        (
            diagnostic
                .module
                .as_ref()
                .and_then(|module| module_order.get(module))
                .copied()
                .unwrap_or(usize::MAX),
            diagnostic.line.unwrap_or(u32::MAX),
        )
    });
    let mut seen = HashSet::new();
    diagnostics.retain(|diagnostic| seen.insert(diagnostic.clone()));
}

fn append_diagnostics(
    out: &mut String,
    diagnostics: &[Diagnostic],
    reported: &mut HashSet<Diagnostic>,
) {
    for diagnostic in diagnostics {
        if !reported.insert(diagnostic.clone()) {
            continue;
        }
        let severity = match diagnostic.severity {
            DiagnosticSeverity::Warning => "warning",
            DiagnosticSeverity::Error => "error",
        };
        out.push_str(severity);
        out.push(':');
        if let Some(module) = diagnostic.module.as_ref() {
            out.push_str(&format!(" module `{module}`"));
        }
        if let Some(line) = diagnostic.line {
            out.push_str(&format!(", line {line}"));
        }
        out.push_str(&format!(": {}\n", diagnostic.message));
    }
}

/// Binary-symbol sort checks run lazily when a symbolic command first needs them. Under `set verbose on`,
/// an identity whose collapse lowers the result sort reports once, immediately before that command's echo.
fn append_verbose_identity_collapse_diagnostics(
    lm: &LoadedModule,
    module: &str,
    reported: &mut HashSet<(String, tnk_core::symbol::SymbolId, bool)>,
    out: &mut String,
) {
    let mut symbols: Vec<_> = lm.built.syntax.keys().copied().collect();
    symbols.sort_unstable();
    symbols.dedup();
    for symbol in symbols {
        for (left, collapse) in [
            (
                true,
                tnk_core::unify::unequal_left_identity_collapse(&lm.built.engine, symbol),
            ),
            (
                false,
                tnk_core::unify::unequal_right_identity_collapse(&lm.built.engine, symbol),
            ),
        ] {
            let Some((result, collapsed)) = collapse else {
                continue;
            };
            if !reported.insert((module.to_string(), symbol, left)) {
                continue;
            }
            let name = lm.built.engine.symbol(symbol).name().replace(',', "`,");
            out.push_str(&format!(
                "op {} {}-identity collapse from {} to {} is unequal.\n",
                name,
                if left { "left" } else { "right" },
                lm.built.engine.sorts().name(result),
                lm.built.engine.sorts().name(collapsed),
            ));
        }
    }
}

/// Append a non-empty per-statement output block to the accumulated submission output, separating
/// consecutive blocks by a single newline.
fn append_block(out: &mut String, block: &str) {
    if !block.is_empty() {
        if !out.is_empty() && !out.ends_with('\n') {
            out.push('\n');
        }
        out.push_str(block);
    }
}

/// The path operand of `load`/`sload` (Appendix D): the rest of the keyword's line with surrounding
/// whitespace trimmed and one optional final command dot removed. A final `.` is the command dot only
/// when it is the whole operand or follows whitespace; a `.` glued to the path is part of the path.
fn load_path_operand(rest: &str) -> &str {
    let rest = rest.trim();
    match rest.strip_suffix('.') {
        Some(head) if head.is_empty() || head.ends_with(char::is_whitespace) => head.trim_end(),
        _ => rest,
    }
}

/// Join command tokens with canonical mixfix spacing: no space before commas or brackets, none after an
/// opening bracket, and one elsewhere. This preserves the input term rather than reparsing it, including
/// redundant parentheses.
fn join_tokens(toks: &[Token], i: &Interner) -> String {
    let mut out = String::new();
    let mut no_space = true; // suppress the leading space, and the space after an opening bracket
    for t in toks {
        let text = i.resolve(t.sym);
        let open = matches!(text, "(" | "[" | "{");
        let close = matches!(text, ")" | "]" | "}");
        if !(no_space || open || close || text == ",") {
            out.push(' ');
        }
        out.push_str(text);
        no_space = open;
    }
    out
}

fn parse_command_or_report<'a>(
    lm: &LoadedModule,
    i: &Interner,
    tokens: &'a [Token],
    out: &mut String,
) -> Option<ParsedCommandTerm<'a>> {
    match parse_command_term(lm, i, tokens) {
        Ok(parsed) => Some(parsed),
        Err(error) => {
            out.push_str(&format!("error: {error}\n"));
            None
        }
    }
}

/// Drive a `rewrite`/`continue` session and render trace, rewrite count, and result. A bounded
/// `frewrite` stop may report `result (sort not calculated)` because the term is not canonical.
fn render_rewriting(
    lm: &mut LoadedModule,
    i: &Interner,
    flags: TraceFlags,
    color: bool,
    show_breakdown: bool,
    rw: &mut Rewriting,
    bound: Option<u64>,
) -> Result<String, ReducerFault> {
    let step = rw.try_run(&mut lm.built.engine, bound)?;
    Ok(render_rewrite_step(
        lm,
        i,
        flags,
        color,
        show_breakdown,
        step,
    ))
}

#[allow(clippy::too_many_arguments)]
fn drive_external_rewriting(
    rw: &mut Rewriting,
    lm: &mut LoadedModule,
    host_functions: &HostFunctionCatalog,
    interner: &mut Interner,
    db: &ModuleDb,
    views: &ViewDb,
    meta_state: &mut MetaState,
    interpreters: &mut InterpreterRegistry,
    bound: Option<u64>,
) -> Result<RewriteStep, ReducerFault> {
    let mut outcome = {
        let mut descent = MetaDescent::new(interner, db, views, meta_state)
            .with_host_functions(host_functions.clone());
        rw.try_run_with_external(&mut lm.built.engine, bound, &mut descent)?
    };
    loop {
        match outcome {
            ExternalRun::Complete(step) => return Ok(step),
            ExternalRun::Suspended { token, request } => {
                let response = {
                    let mut manager = LocalInterpreterManager::new(
                        interpreters,
                        interner,
                        db,
                        views,
                        host_functions,
                    );
                    let mut action = manager.handle(request);
                    if let Some(fault) = action.fault.take() {
                        return Err(fault);
                    }
                    if let Some(unregister) = action.unregister.take() {
                        lm.built.engine.unregister_external_target(unregister);
                    }
                    if let Some((id, target)) = action.register.take() {
                        match lm.built.engine.register_external_target(&target) {
                            Some(target_token) if manager.commit_registration(id, target_token) => {
                            }
                            Some(target_token) => {
                                lm.built.engine.unregister_external_target(target_token);
                                manager.rollback_create(id);
                                action.response = None;
                            }
                            None => {
                                manager.rollback_create(id);
                                action.response = None;
                            }
                        }
                    }
                    action.response
                };
                outcome = {
                    let mut descent = MetaDescent::new(interner, db, views, meta_state)
                        .with_host_functions(host_functions.clone());
                    rw.try_resume_external(&mut lm.built.engine, token, response, &mut descent)?
                        .expect("the scheduler resumes the token it was just given")
                };
            }
        }
    }
}

fn render_rewrite_step(
    lm: &mut LoadedModule,
    i: &Interner,
    flags: TraceFlags,
    color: bool,
    show_breakdown: bool,
    step: RewriteStep,
) -> String {
    let events = lm.built.engine.take_trace();
    let trace = render_trace(&lm.built, i, &events, flags, color);
    let eng = &lm.built.engine;
    let rw_count = eng.rewrites();
    let breakdown = rewrite_breakdown(lm, show_breakdown);
    let value = print_pretty(&lm.built, i, step.term, color);
    let result_line = if step.sort_known {
        let sort = eng.sorts().name(eng.sort_of(step.term)).to_string();
        format!("result {sort}: {value}")
    } else {
        format!("result (sort not calculated): {value}")
    };
    format!("{trace}rewrites: {rw_count}{breakdown}\n{result_line}\n")
}

/// The `search` command's echoed query: `{subject} {arrow} {pattern}[ such that {cond}]`.
fn search_header(
    lm: &mut LoadedModule,
    i: &Interner,
    subject: &ParsedCommandTerm<'_>,
    arrow: SearchArrow,
    pattern: &ParsedCommandTerm<'_>,
    such_that: Option<&[Token]>,
    color: bool,
) -> String {
    let subj =
        command_echo(lm, i, subject, color).unwrap_or_else(|_| join_tokens(subject.tokens(), i));
    let arrow_str = match arrow {
        SearchArrow::One => "=>1",
        SearchArrow::Plus => "=>+",
        SearchArrow::Star => "=>*",
        SearchArrow::Bang => "=>!",
    };
    let pattern =
        command_echo(lm, i, pattern, color).unwrap_or_else(|_| join_tokens(pattern.tokens(), i));
    let mut h = format!("{subj} {arrow_str} {pattern}");
    if let Some(c) = such_that {
        h.push_str(&format!(" such that {}", join_tokens(c, i)));
    }
    h
}

/// Pull up to `limit` more solutions from a search session, rendering each `Solution N (state K)` block;
/// on exhaustion append `No more solutions.` + the final stats. Shared by `search` and `continue`.
fn render_search(
    session: &mut SearchSession,
    lm: &mut LoadedModule,
    i: &Interner,
    color: bool,
    limit: Option<u64>,
    show_breakdown: bool,
) -> Result<String, ReducerFault> {
    let mut out = String::new();
    let mut shown = 0u64;
    loop {
        if limit == Some(shown) {
            return Ok(out); // hit the per-invocation solution bound — continuable, no "No more solutions"
        }
        match session.search.try_next_solution(&mut lm.built.engine)? {
            Some(sol) => {
                shown += 1;
                let bindings = render_search_bindings(lm, i, &session.vars, &sol.bindings, color);
                let breakdown = rewrite_breakdown(lm, show_breakdown);
                out.push_str(&format!(
                    "\nSolution {} (state {})\nstates: {}  rewrites: {}{breakdown}\n{bindings}\n",
                    sol.number, sol.state, sol.states, sol.rewrites
                ));
            }
            None => {
                let states = session.search.states();
                let rewrites = lm.built.engine.rewrites();
                let breakdown = rewrite_breakdown(lm, show_breakdown);
                out.push_str(&format!(
                    "\nNo more solutions.\nstates: {states}  rewrites: {rewrites}{breakdown}\n"
                ));
                return Ok(out);
            }
        }
    }
}

/// Pull object-level SMT-search results. SMT-sorted goal variables are represented by equalities in
/// the final `where` constraint; only non-SMT goal variables appear as substitution lines.
fn render_smt_search(
    session: &mut SmtSearchSession,
    lm: &mut LoadedModule,
    i: &Interner,
    color: bool,
    limit: Option<u64>,
) -> String {
    let mut out = String::new();
    let mut shown = 0u64;
    loop {
        if limit == Some(shown) {
            return out;
        }
        let Some(solution) = session.search.next_solution(&mut lm.built.engine) else {
            let message = if session.shown_total == 0 {
                "No solution."
            } else {
                "No more solutions."
            };
            out.push_str(&format!(
                "\n{message}\n{}\n",
                rewrite_count_line(lm.built.engine.rewrites())
            ));
            return out;
        };
        shown += 1;
        session.shown_total += 1;
        let names = session.search.variable_names();
        let state = session
            .search
            .state_term(solution.state)
            .expect("SMT solution references a live state");
        let state = print_pretty_with_variables(&lm.built, i, state, names, color);
        let constraint =
            print_pretty_with_variables(&lm.built, i, solution.constraint, names, color);
        out.push_str(&format!(
            "\nSolution {}\n{}\nstate: {state}\n",
            solution.number,
            rewrite_count_line(solution.rewrites)
        ));
        let mut rendered_binding = false;
        for slot in 0..session.target_variable_count {
            if lm
                .built
                .engine
                .smt_type(session.goal_variables.sort(slot))
                .is_some()
            {
                continue;
            }
            rendered_binding = true;
            let value = print_pretty_with_variables(
                &lm.built,
                i,
                solution.bindings[slot as usize],
                names,
                color,
            );
            out.push_str(&format!(
                "{} --> {value}\n",
                session.goal_variables.name(slot)
            ));
        }
        if !rendered_binding {
            out.push_str("empty substitution\n");
        }
        out.push_str(&format!("where {constraint}\n"));
    }
}

/// Pull up to `limit` variants from one resumable folding search. Incremental mode reports the rewrite
/// snapshot for each layer; irredundant mode computes the survivor set first and reports one total.
fn render_variants(
    session: &mut VariantSession,
    lm: &mut LoadedModule,
    i: &mut Interner,
    color: bool,
    limit: Option<u64>,
) -> Result<String, ReducerFault> {
    let mut out = String::new();
    let mut shown = 0u64;
    loop {
        if limit == Some(shown) {
            return Ok(out);
        }
        let next = {
            let mut names = InternerNames(i);
            let mut env = tnk_core::unify::UnifyEnv {
                e: &mut lm.built.engine,
                names: &mut names,
            };
            session.search.try_find_next(&mut env)?
        };
        if session.irredundant && !session.reported_total {
            let rewrites = lm.built.engine.rewrites();
            out.push_str(&format!("rewrites: {rewrites}\n"));
            session.reported_total = true;
        }
        match next {
            Some(variant) => {
                shown += 1;
                let eng = &lm.built.engine;
                let sort = eng.sorts().name(eng.sort_of(variant.term));
                let value = print_pretty(&lm.built, i, variant.term, color);
                out.push_str(&format!("\nVariant {}\n", variant.index + 1));
                if !session.irredundant {
                    out.push_str(&format!("rewrites: {}\n", variant.rewrites));
                }
                out.push_str(&format!("{sort}: {value}\n"));
                for (slot, &binding) in variant.substitution.iter().enumerate() {
                    let value = print_pretty(&lm.built, i, binding, color);
                    out.push_str(&format!("{} --> {value}\n", session.var_names[slot]));
                }
            }
            None => {
                out.push_str("\nNo more variants.\n");
                if !session.irredundant {
                    let rewrites = lm.built.engine.rewrites();
                    out.push_str(&format!("rewrites: {rewrites}\n"));
                }
                return Ok(out);
            }
        }
    }
}

impl VariantUnifySession {
    fn advance(&mut self, lm: &mut LoadedModule, i: &mut Interner) -> Result<(), ReducerFault> {
        if self.exhausted {
            return Ok(());
        }
        let mut names = InternerNames(i);
        let mut env = tnk_core::unify::UnifyEnv {
            e: &mut lm.built.engine,
            names: &mut names,
        };
        if self.matching {
            let subject = self.subject.expect("variant matching subject");
            loop {
                let Some(variant) = self.search.try_find_next(&mut env)? else {
                    self.exhausted = true;
                    return Ok(());
                };
                let matches = tnk_core::variant::try_variant_match_bindings(
                    &mut env,
                    &variant,
                    subject,
                    &self.fresh_base,
                )?;
                if matches.is_empty() {
                    continue;
                }
                let rewrites = env.e.rewrites();
                for bindings in matches {
                    let equations = self.search.variant_equations();
                    self.stream.try_insert(
                        &mut env,
                        bindings,
                        variant.family,
                        rewrites,
                        &equations,
                    )?;
                }
                return Ok(());
            }
        }
        let Some(variant) = self.search.try_find_next(&mut env)? else {
            self.exhausted = true;
            return Ok(());
        };
        debug_assert!(variant.unifier);
        let rewrites = env.e.rewrites();
        let equations = self.search.variant_equations();
        self.stream.try_insert(
            &mut env,
            variant.substitution,
            variant.family,
            rewrites,
            &equations,
        )?;
        Ok(())
    }

    fn prepare_filtered(
        &mut self,
        lm: &mut LoadedModule,
        i: &mut Interner,
    ) -> Result<(), ReducerFault> {
        if self.prepared {
            return Ok(());
        }
        while !self.exhausted {
            self.advance(lm, i)?;
        }
        self.stream.finish();
        self.prepared = true;
        Ok(())
    }
}

fn render_variant_unifiers(
    session: &mut VariantUnifySession,
    lm: &mut LoadedModule,
    i: &mut Interner,
    limit: Option<u64>,
    show_breakdown: bool,
) -> Result<String, ReducerFault> {
    let mut out = String::new();
    if session.upfront {
        session.prepare_filtered(lm, i)?;
        if !session.reported_total {
            out.push_str(&format!("rewrites: {}\n", lm.built.engine.rewrites()));
            if show_breakdown {
                let breakdown = rewrite_breakdown(lm, true);
                out.push_str(breakdown.trim_start_matches('\n'));
                out.push('\n');
            }
            session.reported_total = true;
        }
    }
    let mut shown = 0;
    loop {
        if limit == Some(shown) {
            return Ok(out);
        }
        let index = loop {
            if let Some(index) = session.stream.pop_pending() {
                break Some(index);
            }
            if session.exhausted {
                break None;
            }
            session.advance(lm, i)?;
        };
        let Some(index) = index else {
            let noun = if session.matching {
                "matchers"
            } else {
                "unifiers"
            };
            let message = if session.next_number == 0 {
                format!("No {noun}.")
            } else {
                format!("No more {noun}.")
            };
            out.push_str(&format!("\n{message}\n"));
            if !session.upfront {
                out.push_str(&format!("rewrites: {}\n", lm.built.engine.rewrites()));
                if show_breakdown {
                    let breakdown = rewrite_breakdown(lm, true);
                    out.push_str(breakdown.trim_start_matches('\n'));
                    out.push('\n');
                }
            }
            return Ok(out);
        };
        shown += 1;
        session.next_number += 1;
        let result_rewrites = session.stream.rewrites(index);
        let label = if session.matching {
            "Matcher"
        } else {
            "Unifier"
        };
        out.push_str(&format!("\n{label} {}\n", session.next_number));
        if !session.upfront {
            out.push_str(&format!("rewrites: {result_rewrites}\n"));
            if show_breakdown {
                let breakdown = format_rewrite_breakdown(result_rewrites, 0, 0, result_rewrites, 0);
                out.push_str(breakdown.trim_start_matches('\n'));
                out.push('\n');
            }
        }
        let bindings = if session.matching {
            session
                .stream
                .bindings(index)
                .iter()
                .map(|&dag| {
                    tnk_core::variant::restore_subject_variables(
                        &mut lm.built.engine,
                        dag,
                        &session.restorations,
                    )
                })
                .collect::<Vec<_>>()
        } else {
            session.stream.bindings(index).to_vec()
        };
        out.push_str(&render_unifier(&lm.built, i, &session.var_names, &bindings));
        out.push('\n');
    }
}

fn rewrite_count_line(rewrites: u64) -> String {
    format!("rewrites: {rewrites}")
}

fn render_narrow_accumulated(
    session: &NarrowSession,
    lm: &LoadedModule,
    i: &Interner,
    state: usize,
    color: bool,
) -> String {
    let (_, substitution, _, _) = session.search.state(state);
    let (variables, count) = if let Some(initials) = &session.initial_variables {
        let variables = &initials[session.search.root_index(state)];
        (variables, variables.count() as usize)
    } else {
        (&session.variables, session.initial_variable_count)
    };
    (0..count)
        .map(|slot| {
            let value = print_pretty(&lm.built, i, substitution[slot], color);
            let name = command_variable_display_name(
                &lm.grammar,
                i,
                variables.name(slot as u32),
                variables.sort(slot as u32),
            );
            format!("{name} --> {value}")
        })
        .collect::<Vec<_>>()
        .join("\n")
}

fn render_narrow_variant_unifier(
    lm: &LoadedModule,
    i: &Interner,
    variables: &[tnk_core::unify::problem::VarSpec],
    bindings: &[DagId],
    color: bool,
    source_variables: Option<(&VarIndex, usize)>,
) -> String {
    variables
        .iter()
        .zip(bindings)
        .map(|(variable, &binding)| {
            let source_name = source_variables.and_then(|(variables, first_goal)| {
                (first_goal..variables.count() as usize).find_map(|slot| {
                    let source = variables.name(slot as u32);
                    let base = source.split_once(':').map_or(source, |(name, _)| name);
                    let code = i.get(base)?.index();
                    (variable.name == maude_variable_name_rank(base, code)
                        && variable.sort == variables.sort(slot as u32))
                    .then(|| {
                        command_variable_display_name(
                            &lm.grammar,
                            i,
                            source,
                            variables.sort(slot as u32),
                        )
                    })
                })
            });
            let name = source_name.unwrap_or_else(|| {
                let base = i.resolve(tnk_frontend::lex::Sym::from_raw(variable.name));
                if matches!(base.as_bytes().first(), Some(b'#' | b'%' | b'@')) {
                    format!("{base}:{}", lm.built.engine.sorts().name(variable.sort))
                } else {
                    base.to_string()
                }
            });
            let value = print_pretty(&lm.built, i, binding, color);
            format!("{name} --> {value}")
        })
        .collect::<Vec<_>>()
        .join("\n")
}

fn rewrite_breakdown(lm: &LoadedModule, enabled: bool) -> String {
    if !enabled {
        return String::new();
    }
    let total = lm.built.engine.rewrites();
    let (membership, rule, variant, narrowing) = lm.built.engine.rewrite_breakdown();
    format_rewrite_breakdown(total, membership, rule, variant, narrowing)
}

fn format_rewrite_breakdown(
    total: u64,
    membership: u64,
    rule: u64,
    variant: u64,
    narrowing: u64,
) -> String {
    let equational = total.saturating_sub(membership + rule + variant + narrowing);
    format!(
        "\nmb applications: {membership}  equational rewrites: {equational}  \
         rule rewrites: {rule}  variant narrowing steps: {variant}  narrowing steps: {narrowing}"
    )
}

fn render_narrow_folding_events(
    session: &mut NarrowSession,
    lm: &LoadedModule,
    i: &Interner,
    color: bool,
) -> String {
    let mut out = String::new();
    for event in session.search.take_folding_events() {
        match event {
            tnk_core::narrow::FoldingEvent::Subsumed { state, by, .. } => {
                let candidate = print_pretty(&lm.built, i, session.search.state(state).0, color);
                let retained = print_pretty(&lm.built, i, session.search.state(by).0, color);
                out.push_str(&format!("New state {candidate} subsumed by {retained}\n"));
            }
            tnk_core::narrow::FoldingEvent::Evicted { state, by } => {
                let candidate = print_pretty(&lm.built, i, session.search.state(by).0, color);
                let victim = print_pretty(&lm.built, i, session.search.state(state).0, color);
                out.push_str(&format!(
                    "New state {candidate} subsumed older state {victim}\n"
                ));
            }
        }
    }
    out
}

#[allow(clippy::too_many_arguments)]
fn render_narrowing(
    session: &mut NarrowSession,
    lm: &mut LoadedModule,
    i: &mut Interner,
    color: bool,
    show_breakdown: bool,
    verbose: bool,
    show_state_number: bool,
    limit: Option<u64>,
) -> Result<String, ReducerFault> {
    let mut out = String::new();
    let mut shown = 0;
    loop {
        if limit == Some(shown) {
            return Ok(out);
        }
        let solution = {
            let mut names = InternerNames(i);
            let mut env = tnk_core::unify::UnifyEnv {
                e: &mut lm.built.engine,
                names: &mut names,
            };
            session.search.try_find_next(&mut env)?
        };
        if verbose {
            out.push_str(&render_narrow_folding_events(session, lm, i, color));
        }
        let Some(solution) = solution else {
            if verbose {
                out.push_str(&format!(
                    "Total number of states seen = {}\n\
                     Of which {} were considered for further narrowing.\n",
                    session.search.state_count(),
                    session.search.states_expanded(),
                ));
            }
            let message = if session.next_number == 0 {
                "No solution."
            } else {
                "No more solutions."
            };
            out.push_str(&format!(
                "\n{message}\n{}{}\n",
                rewrite_count_line(lm.built.engine.rewrites()),
                rewrite_breakdown(lm, show_breakdown),
            ));
            return Ok(out);
        };
        shown += 1;
        session.next_number += 1;
        let (term, _, _, _) = session.search.state(solution.state);
        let state = print_pretty(&lm.built, i, term, color);
        let state_number = if show_state_number {
            format!(" (state {})", solution.state)
        } else {
            String::new()
        };
        let initial_state = session
            .initial_variables
            .as_ref()
            .map_or_else(String::new, |_| {
                format!(
                    "\ninitial state: {}",
                    session.initial_echoes[session.search.root_index(solution.state)]
                )
            });
        let accumulated = render_narrow_accumulated(session, lm, i, solution.state, color);
        let accumulated_newline = if accumulated.is_empty() { "" } else { "\n" };
        let unifier = render_narrow_variant_unifier(
            lm,
            i,
            &solution.variables,
            &solution.bindings,
            color,
            Some((&session.variables, session.initial_variable_count)),
        );
        let unifier_newline = if unifier.is_empty() { "" } else { "\n" };
        out.push_str(&format!(
            "\nSolution {}{state_number}\n{}{}\nstate: {state}{initial_state}\n\
             accumulated substitution:\n{accumulated}{accumulated_newline}variant unifier:\n{unifier}{unifier_newline}",
            session.next_number,
            rewrite_count_line(lm.built.engine.rewrites()),
            rewrite_breakdown(lm, show_breakdown),
        ));
    }
}

fn render_narrow_state(
    session: &NarrowSession,
    lm: &LoadedModule,
    i: &Interner,
    state: usize,
    color: bool,
) -> String {
    let (term, _, _, _) = session.search.state(state);
    let sort = lm.built.engine.sorts().name(lm.built.engine.sort_of(term));
    let value = print_pretty(&lm.built, i, term, color);
    let accumulated = render_narrow_accumulated(session, lm, i, state, color);
    format!("state {state}, {sort}: {value}\naccumulated substitution:\n{accumulated}")
}

fn render_narrowing_display(
    session: &NarrowSession,
    lm: &LoadedModule,
    i: &Interner,
    color: bool,
    display: NarrowDisplay,
    requested: Option<usize>,
) -> String {
    match display {
        NarrowDisplay::MostGeneral | NarrowDisplay::Frontier => {
            let states: Vec<_> = if matches!(display, NarrowDisplay::MostGeneral) {
                session.search.alive_states().collect()
            } else {
                session.search.frontier_states().collect()
            };
            if states.is_empty() {
                return if matches!(display, NarrowDisplay::Frontier) {
                    "*** frontier is empty ***".to_string()
                } else {
                    "*** there are no most general states ***".to_string()
                };
            }
            states
                .iter()
                .map(|&state| {
                    let (term, _, _, _) = session.search.state(state);
                    print_pretty(&lm.built, i, term, color)
                })
                .collect::<Vec<_>>()
                .join(" \\/\n")
        }
        NarrowDisplay::Path | NarrowDisplay::PathStates => {
            let state = requested.expect("show path carries a state");
            let path = session.search.path_indices(state);
            if path.is_empty() {
                return format!("error: show path: no state {state}.");
            }
            let mut out = String::new();
            for (position, &index) in path.iter().enumerate() {
                if position > 0 {
                    let step = session.search.step(index).expect("non-root path state");
                    let rule = &lm.built.engine.narrowing_rules()[step.rule_index];
                    if matches!(display, NarrowDisplay::PathStates) {
                        out.push_str(&format!(
                            "--- {} --->\n",
                            rule.label.as_deref().unwrap_or("unlabeled")
                        ));
                    } else {
                        out.push_str(&format!(
                            "===[ {} ]===>\nvariant unifier:\n",
                            trace::rule_body(&lm.built, i, step.rule_id, color)
                        ));
                        for (name, &binding) in
                            rule.variable_names.iter().zip(&step.source_substitution)
                        {
                            let value = print_pretty(&lm.built, i, binding, color);
                            out.push_str(&format!("{name} --> {value}\n"));
                        }
                        let parent = session.search.parent(index).expect("path child has parent");
                        let variables = session.search.state_variables(parent);
                        let rendered = render_narrow_variant_unifier(
                            lm,
                            i,
                            variables,
                            &step.state_unifier,
                            color,
                            None,
                        );
                        if !rendered.is_empty() {
                            out.push_str(&rendered);
                            out.push('\n');
                        }
                    }
                }
                out.push_str(&render_narrow_state(session, lm, i, index, color));
                if position + 1 != path.len() {
                    out.push('\n');
                }
            }
            out
        }
    }
}

/// Render search bindings as `Var --> value` lines. Declared variables use their written names;
/// on-the-fly `X:Sort` variables retain the sort suffix as part of the name.
fn render_search_bindings(
    lm: &LoadedModule,
    i: &Interner,
    vars: &VarIndex,
    bindings: &[DagId],
    color: bool,
) -> String {
    if vars.count() == 0 {
        return "empty substitution".to_string();
    }
    (0..vars.count())
        .map(|k| {
            let value = print_pretty(&lm.built, i, bindings[k as usize], color);
            format!("{} --> {value}", vars.name(k))
        })
        .collect::<Vec<_>>()
        .join("\n")
}

/// Render `show path N`: the transition sequence from state 0 to state `n` — `state K, Sort: value`
/// lines separated by `===[ rule ]===>` arcs. A state the graph lacks yields an `error:` diagnostic line.
fn render_path(search: &Search, lm: &LoadedModule, i: &Interner, n: usize, color: bool) -> String {
    let steps = search.path(n);
    if steps.is_empty() {
        return format!("error: show path: no state {n}.");
    }
    let mut out = String::new();
    for (idx, step) in steps.iter().enumerate() {
        if idx > 0 {
            let rb = step
                .via
                .map(|r| trace::rule_body(&lm.built, i, r, color))
                .unwrap_or_default();
            out.push_str(&format!("===[ {rb} ]===>\n"));
        }
        let sort = lm
            .built
            .engine
            .sorts()
            .name(lm.built.engine.sort_of(step.term));
        let value = print_pretty(&lm.built, i, step.term, color);
        out.push_str(&format!("state {}, {sort}: {value}\n", step.state));
    }
    out.trim_end().to_string()
}

/// Render `show search graph`: every state and its forward arcs (`arc N ===> state T (rule)`).
fn render_graph(search: &Search, lm: &LoadedModule, i: &Interner, color: bool) -> String {
    let graph = search.graph();
    let mut out = String::new();
    for (idx, (sidx, term, arcs)) in graph.iter().enumerate() {
        if idx > 0 {
            out.push('\n');
        }
        let sort = lm.built.engine.sorts().name(lm.built.engine.sort_of(*term));
        let value = print_pretty(&lm.built, i, *term, color);
        out.push_str(&format!("state {sidx}, {sort}: {value}\n"));
        // Group all rules with the same successor on one arc, listing each rule in its own
        // parenthesized body.
        for (arc_n, (target, rules)) in arcs.iter().enumerate() {
            let bodies: String = rules
                .iter()
                .map(|rid| format!(" ({})", trace::rule_body(&lm.built, i, *rid, color)))
                .collect();
            out.push_str(&format!("arc {arc_n} ===> state {target}{bodies}\n"));
        }
    }
    out.trim_end().to_string()
}

/// Render `show view` with sort maps before operator maps and two-space indentation.
fn render_view(v: &ViewDecl, i: &Interner) -> String {
    let mut s = format!(
        "view {} from {} to {} is\n",
        v.name,
        module_expr_str(&v.from),
        module_expr_str(&v.to)
    );
    for (a, b) in &v.sort_maps {
        s.push_str(&format!("  sort {a} to {b} .\n"));
    }
    for m in &v.op_maps {
        match m {
            OpMap::Op {
                from,
                to,
                dom_range,
            } => {
                let signature = dom_range
                    .as_ref()
                    .map_or_else(String::new, |(domain, range)| {
                        format!(" : {} -> {range}", domain.join(" "))
                    });
                s.push_str(&format!(
                    "  op {}{} to {} .\n",
                    join_tokens(from, i),
                    signature,
                    join_tokens(to, i)
                ));
            }
            OpMap::Term {
                from,
                to,
                dom_range,
            } => {
                let signature = dom_range
                    .as_ref()
                    .map_or_else(String::new, |(domain, range)| {
                        format!(" : {} -> {range}", domain.join(" "))
                    });
                s.push_str(&format!(
                    "  op {}{} to term {} .\n",
                    join_tokens(from, i),
                    signature,
                    join_tokens(to, i)
                ));
            }
        }
    }
    s.push_str("endv");
    s
}

/// Render a module expression as text for `show view`'s from/to. These are normally named modules.
fn module_expr_str(e: &ModuleExpr) -> String {
    match e {
        ModuleExpr::Named(n) => n.clone(),
        ModuleExpr::Sum(a, b) => format!("{} + {}", module_expr_str(a), module_expr_str(b)),
        ModuleExpr::Rename(inner, _) => format!("{} * (…)", module_expr_str(inner)),
        ModuleExpr::Instantiation(base, args) => {
            let parts: Vec<String> = args.iter().map(module_expr_str).collect();
            format!("{}{{{}}}", module_expr_str(base), parts.join(", "))
        }
    }
}

/// Render a compact module summary containing its name, sorted sort names, and sorted operator
/// name/arities. Statements are intentionally omitted.
fn render_module(name: &str, lm: &LoadedModule) -> String {
    let b = &lm.built;
    let mut sorts: Vec<&str> = b.sorts.keys().map(String::as_str).collect();
    sorts.sort_unstable();
    let mut ops: Vec<String> = b.ops.keys().map(|(n, a)| format!("{n}/{a}")).collect();
    ops.sort_unstable();
    format!(
        "fmod {name}\n  sorts: {}\n  ops: {}",
        sorts.join(" "),
        ops.join(" ")
    )
}
