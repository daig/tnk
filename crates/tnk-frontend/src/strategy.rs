//! Strategy-language execution over parsed [`StratExpr`] values.
//!
//! Resolution parses term bubbles with their compiled grammar, binds rule labels, and leaves named calls as
//! lazy `RStrat::Call` frames. At execution, a call matches compatible definitions in declaration order,
//! specializes each matching body with argument bindings, and schedules its bodies one at a time.
//!
//! Each `Process` carries a term, pending strategy stack, and task id. Decomposing a frame only schedules
//! successors; an `AppState` instead fires at most one rule match per process step. A process whose pending
//! stack is empty emits a solution to its task. `srewrite` appends successors for FIFO round-robin search;
//! `dsrewrite` prepends them, preserving local successor order for depth-first search.
//!
//! Branching, `one`, and normalization run sub-searches as child tasks in the same queue. A task's `slaves`
//! count includes its live processes and child tasks; reaching zero triggers exhaustion behavior such as a
//! branch failure arm or normal-form emission. Shared scheduling determines both solution order and the
//! cumulative rewrite count recorded when each solution is emitted.
//!
//! `matchrew` and `amatchrew` run each selected by-variable strategy to exhaustion before rebuilding the
//! Cartesian product of their results. These eager sub-searches share the cumulative rewrite counter, so
//! unequal branch depths affect later emitted counts. Resolution rejects `xmatchrew` and calls that have only
//! conditional `csd` definitions.

use crate::build_term::{VarIndex, build_term};
use crate::cfparser::compile::CompiledGrammar;
use crate::lex::{Interner, Token};
use crate::load::{
    LoadedModule, ParsedCommandTerm, parse_build, parse_condition, term_var_indices,
};
use crate::surface::ast::{StratExpr, StratSugar, TestKind};
use std::collections::{BTreeSet, HashSet, VecDeque};
use std::rc::Rc;
use tnk_core::dag::{DagId, NodeRepr};
use tnk_core::engine::Engine;
use tnk_core::host::ReducerFault;
use tnk_core::sort::KindId;
use tnk_core::term::{ConditionFragment, Term};
use tnk_core::variant::term_from_dag_slots;

/// A reduced strategy result and the cumulative rewrite count when it was emitted.
pub struct StratSolution {
    pub term: DagId,
    pub rewrites: u64,
}

#[derive(Debug)]
pub enum StrategicRewriteError {
    Invalid(String),
    Reducer(ReducerFault),
}

impl std::fmt::Display for StrategicRewriteError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Invalid(message) => formatter.write_str(message),
            Self::Reducer(fault) => fault.fmt(formatter),
        }
    }
}

impl std::error::Error for StrategicRewriteError {}

impl From<String> for StrategicRewriteError {
    fn from(message: String) -> Self {
        Self::Invalid(message)
    }
}

impl From<&str> for StrategicRewriteError {
    fn from(message: &str) -> Self {
        Self::Invalid(message.to_owned())
    }
}

impl From<ReducerFault> for StrategicRewriteError {
    fn from(fault: ReducerFault) -> Self {
        Self::Reducer(fault)
    }
}

/// A rule selected for strategy application, including its condition and variable-slot names.
#[derive(Clone)]
struct RRule {
    lhs: Term,
    rhs: Term,
    condition: Vec<ConditionFragment>,
    nr_vars: u32,
    var_names: Vec<String>,
}

/// A resolved strategy — recursive children are [`Rc`]'d so the pending stack can share them cheaply and the
/// cycle-pruning seen-set can key on their (stable) pointer identity.
enum RStrat {
    Idle,
    Fail,
    Apply {
        rules: Vec<RRule>,
        top: bool,
        subst: Vec<(String, Term)>,
        substrats: Vec<Rc<RStrat>>,
    },
    One(Rc<RStrat>),
    Seq(Rc<RStrat>, Rc<RStrat>),
    Union(Rc<RStrat>, Rc<RStrat>),
    Star(Rc<RStrat>),
    Plus(Rc<RStrat>),
    Normalize(Rc<RStrat>),
    Branch {
        test: Rc<RStrat>,
        success: Rc<RStrat>,
        failure: Rc<RStrat>,
    },
    Test {
        anywhere: bool,
        extension: bool,
        pattern: Term,
        nr_vars: u32,
        cond: Vec<ConditionFragment>,
    },
    MatchRew {
        anywhere: bool,
        pattern: Term,
        nr_vars: u32,
        cond: Vec<ConditionFragment>,
        by: Vec<(u32, Rc<RStrat>)>,
    },
    Call {
        name: String,
        args: Vec<Term>,
    },
    /// Enumerates specialized named-call bodies one at a time. Each body runs as a child task while the
    /// generator remains in the parent task, allowing fair interleaving.
    CallGenerator {
        bodies: Rc<Vec<Rc<RStrat>>>,
        next: usize,
    },
}

#[derive(Clone, PartialEq, Eq)]
struct ProfileKey {
    name: String,
    args: Vec<KindId>,
    subject: KindId,
}

struct DeclProfile {
    key: ProfileKey,
    origins: HashSet<String>,
}

struct RDef {
    key: ProfileKey,
    patterns: Vec<Term>,
    nr_vars: u32,
    body: Rc<RStrat>,
}

#[derive(Default)]
struct StrategyProgram {
    profiles: Vec<DeclProfile>,
    defs: Vec<RDef>,
}

/// The evaluation context: the engine, the compiled strategy-definition program, the cumulative
/// rewrite count, and the first strict-reducer fault raised by an internal equational normalization.
struct Cx<'a> {
    eng: &'a mut Engine,
    program: &'a StrategyProgram,
    count: u64,
    reducer_fault: Option<ReducerFault>,
}

/// A pending continuation: an immutable stack of resolved strategy frames (top = the next to decompose).
type Pending = Option<Rc<Frame>>;
struct Frame {
    strat: Rc<RStrat>,
    rest: Pending,
}

fn push(p: &Pending, s: Rc<RStrat>) -> Pending {
    Some(Rc::new(Frame {
        strat: s,
        rest: p.clone(),
    }))
}

/// Push `ss` so that `ss[0]` ends on top (decomposed first).
fn push_all(mut p: Pending, ss: &[Rc<RStrat>]) -> Pending {
    for s in ss.iter().rev() {
        p = push(&p, s.clone());
    }
    p
}

/// A structural key for a pending stack. Resolved nodes use their stable pointer identity; runtime call
/// generators use the persistent body-vector identity plus cursor because their short-lived node allocation
/// can otherwise reuse an address retained by the seen-set.
fn pending_key(p: &Pending) -> Vec<usize> {
    let mut key = Vec::new();
    let mut current = p.clone();
    while let Some(frame) = current {
        if let RStrat::CallGenerator { bodies, next } = &*frame.strat {
            key.push(0);
            key.push(Rc::as_ptr(bodies) as usize);
            key.push(*next);
        } else {
            key.push(Rc::as_ptr(&frame.strat) as *const () as usize);
        }
        current = frame.rest.clone();
    }
    key
}

/// A scheduled process: a term + its pending strategy stack + the task it belongs to, or — when `app` is set
/// — a resumable rule application yielding one rewrite per step.
struct Process {
    dag: DagId,
    pending: Pending,
    app: Option<AppState>,
    task: usize,
}

/// A resumable rule application: the remaining matches to fire (one per step) + the continuation per result.
struct AppState {
    rest: Pending,
    matches: VecDeque<OneMatch>,
}

struct OneMatch {
    path: Vec<usize>,
    result: DagId,
}

/// A sub-search whose solutions feed a continuation. `slaves` counts live processes and child tasks;
/// reaching zero exhausts the task and runs its completion action.
struct TaskState {
    parent: usize,
    slaves: i32,
    alive: bool,
    kind: TaskKind,
}

enum TaskKind {
    /// The top-level task — its solutions are the command's results.
    Root,
    /// A named-call body task. Each solution resumes the call's outer continuation in the parent task;
    /// exhaustion has no fallback action.
    Call { rest: Pending },
    /// `E ? success : failure` on `dag`: the first `E` solution schedules `success` and commits; exhaustion
    /// without a solution schedules `failure` on the original `dag`.
    Branch {
        dag: DagId,
        success: Rc<RStrat>,
        failure: Rc<RStrat>,
        rest: Pending,
        had_success: bool,
    },
    /// `one(E)` (continuation `rest`): forward the **first** `E`-solution, then discard the rest.
    One { rest: Pending, taken: bool },
    /// `E !` on `dag`: each `E` solution starts another normalization round; a round with no solution emits
    /// `dag` as a normal form.
    Normalize {
        dag: DagId,
        normalize: Rc<RStrat>,
        rest: Pending,
        had_success: bool,
    },
}

/// Run a fair or depth-first strategic rewrite and return per-solution cumulative rewrite counts.
pub fn srewrite_command(
    lm: &mut LoadedModule,
    i: &Interner,
    term: &ParsedCommandTerm<'_>,
    strat: &StratExpr,
    depth_first: bool,
) -> Result<(Vec<StratSolution>, u64), StrategicRewriteError> {
    let mut vars = VarIndex::new();
    let subj_term = build_term(
        term.unambiguous_tree(i)?,
        &lm.grammar,
        &lm.built,
        term.tokens(),
        i,
        &mut vars,
    )?;
    if vars.count() != 0 {
        return Err("srewrite subject must be a ground term".into());
    }
    let subj = lm.built.engine.instantiate_bindings(&subj_term, &[]);
    srewrite_dag(lm, i, subj, strat, depth_first)
}

/// Run a strategy over an already-built ground subject, bypassing subject parsing and construction.
pub fn srewrite_dag(
    lm: &mut LoadedModule,
    i: &Interner,
    subj: DagId,
    strat: &StratExpr,
    depth_first: bool,
) -> Result<(Vec<StratSolution>, u64), StrategicRewriteError> {
    let program = compile_strategy_program(lm, i);
    let rstrat = resolve(strat, lm, i)?;
    let mut cx = Cx {
        eng: &mut lm.built.engine,
        program: &program,
        count: 0,
        reducer_fault: None,
    };
    cx.eng.reset_rewrites();
    let subj = cx.eng.try_reduce(subj)?;
    cx.count = cx.eng.rewrites();
    let sols = run_search(&mut cx, subj, rstrat, !depth_first);
    if let Some(fault) = cx.reducer_fault.take() {
        return Err(StrategicRewriteError::Reducer(fault));
    }
    let total = cx.count;
    let out = dedup(
        cx.eng,
        sols.into_iter()
            .map(|(term, rewrites)| StratSolution { term, rewrites })
            .collect(),
    );
    Ok((out, total))
}

/// Format a strategy expression for command echoing.
pub fn print_strategy(e: &StratExpr, i: &Interner) -> String {
    /// Surface-syntax precedence, tightest first: atoms and keyword forms, postfix iteration, sequence,
    /// union, then branch. Parenthesize children that exceed their allowed precedence and right children
    /// of left-associative sequence or union nodes.
    fn prec(e: &StratExpr) -> u8 {
        match e {
            StratExpr::Star(_) | StratExpr::Plus(_) | StratExpr::Normalize(_) => 1,
            StratExpr::Seq(..) => 2,
            StratExpr::Union(..) => 3,
            StratExpr::Branch { .. } => 4,
            _ => 0,
        }
    }
    fn child(e: &StratExpr, i: &Interner, max: u8, group_equal: bool) -> String {
        let s = print_strategy(e, i);
        let p = prec(e);
        if p > max || (group_equal && p == max) {
            format!("({s})")
        } else {
            s
        }
    }
    fn iteration(a: &StratExpr, i: &Interner, op: &str) -> String {
        if prec(a) <= 1 {
            format!("{} {op}", print_strategy(a, i))
        } else {
            format!("({}){op}", print_strategy(a, i))
        }
    }
    // Punctuation-aware token spacing: no space after an opener or before a closer/comma.
    fn join(toks: &[Token], i: &Interner) -> String {
        let mut out = String::new();
        for t in toks {
            let s = i.resolve(t.sym);
            let no_space = out.is_empty()
                || out.ends_with(['(', '[', '{'])
                || matches!(s, ")" | "]" | "}" | ",")
                // Applications glue `f(`, while operator contexts retain spaces such as `a + (b + c)`.
                || (s == "(" && out.chars().last().is_some_and(|c| c.is_alphanumeric()));
            if !no_space {
                out.push(' ');
            }
            out.push_str(s);
        }
        out
    }
    match e {
        StratExpr::Idle => "idle".into(),
        StratExpr::Fail => "fail".into(),
        StratExpr::All => "all".into(),
        StratExpr::Apply {
            label,
            subst,
            substrats,
        } => {
            let mut s = label.clone();
            if !subst.is_empty() {
                let sigma = subst
                    .iter()
                    .map(|(v, t)| format!("{} <- {}", join(v, i), join(t, i)))
                    .collect::<Vec<_>>()
                    .join(", ");
                s.push_str(&format!("[{sigma}]"));
            }
            if !substrats.is_empty() {
                let ss = substrats
                    .iter()
                    .map(|e| print_strategy(e, i))
                    .collect::<Vec<_>>()
                    .join(", ");
                s.push_str(&format!("{{{ss}}}"));
            }
            s
        }
        StratExpr::Top(a) => format!("top({})", print_strategy(a, i)),
        StratExpr::One(a) => format!("one({})", print_strategy(a, i)),
        StratExpr::Seq(a, b) => {
            format!("{} ; {}", child(a, i, 2, false), child(b, i, 2, true))
        }
        StratExpr::Union(a, b) => {
            format!("{} | {}", child(a, i, 3, false), child(b, i, 3, true))
        }
        StratExpr::Star(a) => iteration(a, i, "*"),
        StratExpr::Plus(a) => iteration(a, i, "+"),
        StratExpr::Normalize(a) => iteration(a, i, "!"),
        StratExpr::Branch {
            test,
            success,
            failure,
        } => {
            format!(
                "{} ? {} : {}",
                child(test, i, 3, false),
                child(success, i, 4, false),
                child(failure, i, 4, false)
            )
        }
        StratExpr::Test {
            kind,
            pattern,
            cond,
        } => {
            let k = match kind {
                TestKind::Match => "match",
                TestKind::XMatch => "xmatch",
                TestKind::AMatch => "amatch",
            };
            let mut s = format!("{k} {}", join(pattern, i));
            if let Some(c) = cond {
                s.push_str(&format!(" such that {}", join(c, i)));
            }
            s
        }
        StratExpr::MatchRew {
            kind,
            pattern,
            cond,
            subs,
        } => {
            let kw = match kind {
                TestKind::Match => "matchrew",
                TestKind::XMatch => "xmatchrew",
                TestKind::AMatch => "amatchrew",
            };
            let by = subs
                .iter()
                .map(|(v, st)| {
                    // A by-clause strategy binds tighter than its comma; sequence, union, and branch
                    // children therefore need parentheses.
                    let s = print_strategy(st, i);
                    let s = if prec(st) >= 2 { format!("({s})") } else { s };
                    format!("{} using {}", join(v, i), s)
                })
                .collect::<Vec<_>>()
                .join(", ");
            let st = cond
                .as_ref()
                .map(|c| format!(" such that {}", join(c, i)))
                .unwrap_or_default();
            format!("{kw} {}{st} by {by}", join(pattern, i))
        }
        StratExpr::Sugar { kind, args } => {
            let kw = match kind {
                StratSugar::Try => "try",
                StratSugar::NotS => "not",
                StratSugar::TestS => "test",
                StratSugar::OrElse => "or-else",
            };
            let a = args
                .iter()
                .map(|e| print_strategy(e, i))
                .collect::<Vec<_>>()
                .join(", ");
            format!("{kw}({a})")
        }
        StratExpr::Call { name, args } => {
            if args.is_empty() {
                name.clone()
            } else {
                let a = args
                    .iter()
                    .map(|t| join(t, i))
                    .collect::<Vec<_>>()
                    .join(", ");
                format!("{name}({a})")
            }
        }
    }
}

/// Remove `top` unless it directly wraps `all` or a rule label. A named call does not inherit `top` when
/// its body later applies a rule.
pub fn discard_inapplicable_top(e: &mut StratExpr, lm: &LoadedModule) {
    match e {
        StratExpr::Top(inner) => {
            discard_inapplicable_top(inner, lm);
            let direct_application = match &**inner {
                StratExpr::All => true,
                StratExpr::Apply { label, .. } => !rules_labelled(lm, label).is_empty(),
                _ => false,
            };
            if !direct_application {
                *e = std::mem::replace(&mut **inner, StratExpr::Idle);
            }
        }
        StratExpr::Apply { substrats, .. } => {
            for child in substrats {
                discard_inapplicable_top(child, lm);
            }
        }
        StratExpr::One(child)
        | StratExpr::Star(child)
        | StratExpr::Plus(child)
        | StratExpr::Normalize(child) => discard_inapplicable_top(child, lm),
        StratExpr::Seq(left, right) | StratExpr::Union(left, right) => {
            discard_inapplicable_top(left, lm);
            discard_inapplicable_top(right, lm);
        }
        StratExpr::Branch {
            test,
            success,
            failure,
        } => {
            discard_inapplicable_top(test, lm);
            discard_inapplicable_top(success, lm);
            discard_inapplicable_top(failure, lm);
        }
        StratExpr::MatchRew { subs, .. } => {
            for (_, child) in subs {
                discard_inapplicable_top(child, lm);
            }
        }
        StratExpr::Sugar { args, .. } => {
            for child in args {
                discard_inapplicable_top(child, lm);
            }
        }
        StratExpr::Idle
        | StratExpr::Fail
        | StratExpr::All
        | StratExpr::Test { .. }
        | StratExpr::Call { .. } => {}
    }
}

/// Resolve supported surface forms into shared [`RStrat`] nodes. Named calls stay lazy; resolution rejects
/// `xmatchrew` and calls supported only by conditional definitions.
fn resolve(e: &StratExpr, lm: &LoadedModule, i: &Interner) -> Result<Rc<RStrat>, String> {
    resolve_in(e, lm, &lm.grammar, i, &VarIndex::new())
}

/// Resolve term bubbles with `grammar`, treating the variables in `seed` as already bound. Resolved terms
/// and selected rules belong to `lm.built`.
fn resolve_in(
    e: &StratExpr,
    lm: &LoadedModule,
    grammar: &CompiledGrammar,
    i: &Interner,
    seed: &VarIndex,
) -> Result<Rc<RStrat>, String> {
    let r = match e {
        StratExpr::Idle => RStrat::Idle,
        StratExpr::Fail => RStrat::Fail,
        StratExpr::All => RStrat::Apply {
            rules: all_rules(lm),
            top: false,
            subst: Vec::new(),
            substrats: Vec::new(),
        },
        StratExpr::Apply {
            label,
            subst,
            substrats,
        } => {
            let rules = rules_labelled(lm, label);
            if !rules.is_empty() {
                let app_subst = resolve_subst(subst, lm, grammar, i, seed)?;
                let subs = substrats
                    .iter()
                    .map(|child| resolve_in(child, lm, grammar, i, seed))
                    .collect::<Result<Vec<_>, _>>()?;
                RStrat::Apply {
                    rules,
                    top: false,
                    subst: app_subst,
                    substrats: subs,
                }
            } else if subst.is_empty() && substrats.is_empty() {
                return resolve_call(label, &[], lm, grammar, i, seed);
            } else {
                return Err(format!(
                    "`{label}` is not a rule label (application `[…]{{…}}` needs a rule)"
                ));
            }
        }
        StratExpr::Top(inner) => {
            let resolved = resolve_in(inner, lm, grammar, i, seed)?;
            // `top` applies only to a direct rule application, not to a named call whose body later
            // resolves to one.
            let direct_application = match &**inner {
                StratExpr::All => true,
                StratExpr::Apply { label, .. } => !rules_labelled(lm, label).is_empty(),
                _ => false,
            };
            if !direct_application {
                return Ok(resolved);
            }
            match &*resolved {
                RStrat::Apply {
                    rules,
                    subst,
                    substrats,
                    ..
                } => RStrat::Apply {
                    rules: rules.clone(),
                    top: true,
                    subst: subst.clone(),
                    substrats: substrats.clone(),
                },
                _ => unreachable!("a direct application must resolve to RStrat::Apply"),
            }
        }
        StratExpr::One(inner) => RStrat::One(resolve_in(inner, lm, grammar, i, seed)?),
        StratExpr::Seq(left, right) => RStrat::Seq(
            resolve_in(left, lm, grammar, i, seed)?,
            resolve_in(right, lm, grammar, i, seed)?,
        ),
        StratExpr::Union(left, right) => RStrat::Union(
            resolve_in(left, lm, grammar, i, seed)?,
            resolve_in(right, lm, grammar, i, seed)?,
        ),
        StratExpr::Star(child) => RStrat::Star(resolve_in(child, lm, grammar, i, seed)?),
        StratExpr::Plus(child) => RStrat::Plus(resolve_in(child, lm, grammar, i, seed)?),
        StratExpr::Normalize(child) => RStrat::Normalize(resolve_in(child, lm, grammar, i, seed)?),
        // Lower surface sugar to branch combinators; printing retains the original form.
        StratExpr::Sugar { kind, args } => {
            let branch =
                |test: &StratExpr, success: StratExpr, failure: StratExpr| StratExpr::Branch {
                    test: Box::new(test.clone()),
                    success: Box::new(success),
                    failure: Box::new(failure),
                };
            let desugared = match kind {
                StratSugar::Try | StratSugar::TestS => {
                    branch(&args[0], StratExpr::Idle, StratExpr::Fail)
                }
                StratSugar::NotS => branch(&args[0], StratExpr::Fail, StratExpr::Idle),
                StratSugar::OrElse => branch(&args[0], StratExpr::Idle, args[1].clone()),
            };
            return resolve_in(&desugared, lm, grammar, i, seed);
        }
        StratExpr::Branch {
            test,
            success,
            failure,
        } => RStrat::Branch {
            test: resolve_in(test, lm, grammar, i, seed)?,
            success: resolve_in(success, lm, grammar, i, seed)?,
            failure: resolve_in(failure, lm, grammar, i, seed)?,
        },
        StratExpr::Test {
            kind,
            pattern,
            cond,
        } => {
            let (anywhere, extension) = match kind {
                TestKind::Match => (false, false),
                TestKind::AMatch => (true, false),
                TestKind::XMatch => (false, true),
            };
            let mut vars = seed.clone();
            let pattern = parse_build(pattern, grammar, &lm.built, i, &mut vars)?;
            let cond = resolve_test_cond(
                cond.as_deref(),
                &pattern,
                &mut vars,
                lm,
                grammar,
                i,
                seed.count(),
                "test",
            )?;
            RStrat::Test {
                anywhere,
                extension,
                pattern,
                nr_vars: vars.count(),
                cond,
            }
        }
        StratExpr::MatchRew {
            kind,
            pattern,
            cond,
            subs,
        } => {
            let anywhere = match kind {
                TestKind::Match => false,
                TestKind::AMatch => true,
                TestKind::XMatch => {
                    return Err("xmatchrew is recognized but not implemented".to_string());
                }
            };
            let mut vars = seed.clone();
            let pattern = parse_build(pattern, grammar, &lm.built, i, &mut vars)?;
            let cond = resolve_test_cond(
                cond.as_deref(),
                &pattern,
                &mut vars,
                lm,
                grammar,
                i,
                seed.count(),
                "matchrew `such that`",
            )?;
            let mut by = Vec::new();
            for (variable, child) in subs {
                let name = token_text(variable, i);
                let index = matchrew_variable_slot(variable, &name, &vars, lm, grammar, i)
                    .ok_or_else(|| {
                        format!("matchrew variable `{name}` does not occur in the pattern")
                    })?;
                by.push((index, resolve_in(child, lm, grammar, i, seed)?));
            }
            RStrat::MatchRew {
                anywhere,
                pattern,
                nr_vars: vars.count(),
                cond,
                by,
            }
        }
        StratExpr::Call { name, args } => {
            return resolve_call(name, args, lm, grammar, i, seed);
        }
    };
    Ok(Rc::new(r))
}

/// The slot of the pattern variable that a matchrew `by` variable names. A variable is identified by its
/// base name and sort, so a spelling other than the slot's first-seen one (`X:S` for a pattern written
/// with the declared `X : S`, or the reverse) is parsed and resolved through the same [`VarIndex`].
fn matchrew_variable_slot(
    variable: &[Token],
    name: &str,
    vars: &VarIndex,
    lm: &LoadedModule,
    grammar: &CompiledGrammar,
    i: &Interner,
) -> Option<u32> {
    if let Some(slot) = (0..vars.count()).find(|&slot| vars.name(slot) == name) {
        return Some(slot);
    }
    let mut probe = vars.clone();
    match parse_build(variable, grammar, &lm.built, i, &mut probe) {
        Ok(Term::Var(var)) if var.index < vars.count() => Some(var.index),
        _ => None,
    }
}

/// Resolve an optional test or matchrew condition, rejecting rewrite (`=>`) fragments.
#[allow(clippy::too_many_arguments)]
fn resolve_test_cond(
    cond: Option<&[Token]>,
    pattern: &Term,
    vars: &mut VarIndex,
    lm: &LoadedModule,
    grammar: &CompiledGrammar,
    i: &Interner,
    bound_prefix: u32,
    owner: &str,
) -> Result<Vec<ConditionFragment>, String> {
    let Some(cond) = cond else {
        return Ok(Vec::new());
    };
    let mut bound: BTreeSet<u32> = (0..bound_prefix).collect();
    let mut pattern_vars = Vec::new();
    term_var_indices(pattern, &mut pattern_vars);
    bound.extend(pattern_vars);
    let fragments = parse_condition(cond, grammar, &lm.built, i, vars, &mut bound)?;
    if fragments
        .iter()
        .any(|fragment| matches!(fragment, ConditionFragment::Rewrite { .. }))
    {
        return Err(format!(
            "a rewrite condition (`=>`) is not allowed in a {owner}"
        ));
    }
    Ok(fragments)
}

/// Resolve a rule application's initial substitution. Values may use variables from the enclosing strategy
/// definition but cannot introduce variables.
fn resolve_subst(
    subst: &[(Vec<Token>, Vec<Token>)],
    lm: &LoadedModule,
    grammar: &CompiledGrammar,
    i: &Interner,
    seed: &VarIndex,
) -> Result<Vec<(String, Term)>, String> {
    let mut out = Vec::new();
    for (variable, value) in subst {
        let name = token_text(variable, i);
        let mut vars = seed.clone();
        let term = parse_build(value, grammar, &lm.built, i, &mut vars)?;
        if vars.count() != seed.count() {
            return Err(
                "an application substitution value contains an unbound strategy variable"
                    .to_string(),
            );
        }
        out.push((name, term));
    }
    Ok(out)
}

/// Resolve a named call's arguments while deferring definition matching until execution. A declared strategy
/// without an executable matching definition resolves successfully and yields no solutions.
fn resolve_call(
    name: &str,
    args: &[Vec<Token>],
    lm: &LoadedModule,
    grammar: &CompiledGrammar,
    i: &Interner,
    seed: &VarIndex,
) -> Result<Rc<RStrat>, String> {
    let declared = lm
        .built
        .strat_decls
        .iter()
        .any(|decl| decl.name == name && decl.domain.len() == args.len());
    if !declared {
        return Err(format!(
            "`{name}` is neither a rule label nor a strategy of this module"
        ));
    }
    let has_unconditional = lm
        .built
        .strat_defs
        .iter()
        .any(|def| def.name == name && def.params.len() == args.len() && def.cond.is_none());
    let has_conditional = lm
        .built
        .strat_defs
        .iter()
        .any(|def| def.name == name && def.params.len() == args.len() && def.cond.is_some());
    if has_conditional && !has_unconditional {
        return Err(
            "conditional strategy definitions (`csd`) are recognized but not implemented"
                .to_string(),
        );
    }
    let unconditional_defs: Vec<_> = lm
        .built
        .strat_defs
        .iter()
        .filter(|def| def.name == name && def.params.len() == args.len() && def.cond.is_none())
        .collect();
    if !unconditional_defs.is_empty()
        && unconditional_defs
            .iter()
            .all(|def| contains_xmatchrew(&def.body))
    {
        return Err("xmatchrew is recognized but not implemented".to_string());
    }
    let mut vars = seed.clone();
    let mut resolved_args = Vec::with_capacity(args.len());
    for arg in args {
        resolved_args.push(parse_build(arg, grammar, &lm.built, i, &mut vars)?);
    }
    if vars.count() != seed.count() {
        return Err(format!(
            "strategy call `{name}` contains an unbound argument variable"
        ));
    }
    Ok(Rc::new(RStrat::Call {
        name: name.to_string(),
        args: resolved_args,
    }))
}

fn contains_xmatchrew(strategy: &StratExpr) -> bool {
    match strategy {
        StratExpr::MatchRew {
            kind: TestKind::XMatch,
            ..
        } => true,
        StratExpr::Apply { substrats, .. } => substrats.iter().any(contains_xmatchrew),
        StratExpr::Top(child)
        | StratExpr::One(child)
        | StratExpr::Star(child)
        | StratExpr::Plus(child)
        | StratExpr::Normalize(child) => contains_xmatchrew(child),
        StratExpr::Seq(left, right) | StratExpr::Union(left, right) => {
            contains_xmatchrew(left) || contains_xmatchrew(right)
        }
        StratExpr::Branch {
            test,
            success,
            failure,
        } => contains_xmatchrew(test) || contains_xmatchrew(success) || contains_xmatchrew(failure),
        StratExpr::MatchRew { subs, .. } => subs.iter().any(|(_, child)| contains_xmatchrew(child)),
        StratExpr::Sugar { args, .. } => args.iter().any(contains_xmatchrew),
        StratExpr::Idle
        | StratExpr::Fail
        | StratExpr::All
        | StratExpr::Test { .. }
        | StratExpr::Call { .. } => false,
    }
}

/// Compile kind-based call profiles and executable unconditional definitions in declaration order.
fn compile_strategy_program(lm: &LoadedModule, i: &Interner) -> StrategyProgram {
    let mut program = StrategyProgram::default();
    let mut seen_declarations = HashSet::new();
    for decl in &lm.built.strat_decls {
        if let (Some(origin), Some(source_index)) = (&decl.origin, decl.source_index)
            && !seen_declarations.insert((origin.clone(), source_index))
        {
            continue;
        }
        let Some(args) = decl
            .domain
            .iter()
            .map(|sort| strategy_sort_kind(lm, sort))
            .collect::<Option<Vec<_>>>()
        else {
            continue;
        };
        let Some(subject) = strategy_sort_kind(lm, &decl.subject) else {
            continue;
        };
        let key = ProfileKey {
            name: decl.name.clone(),
            args,
            subject,
        };
        let origin = decl
            .origin
            .clone()
            .unwrap_or_else(|| format!("{}#local", lm.built.name));
        if let Some(profile) = program
            .profiles
            .iter_mut()
            .find(|profile| profile.key == key)
        {
            profile.origins.insert(origin);
        } else {
            program.profiles.push(DeclProfile {
                key,
                origins: HashSet::from([origin]),
            });
        }
    }

    let mut seen_definitions = HashSet::new();
    for def in &lm.built.strat_defs {
        if def.cond.is_some() {
            continue;
        }
        if let (Some(origin), Some(source_index)) = (&def.origin, def.source_index)
            && !seen_definitions.insert((origin.clone(), source_index))
        {
            continue;
        }
        let Some(grammar) = definition_grammar(lm, def.home.as_deref()) else {
            // A definition is executable only with its associated grammar; never parse its token bubbles
            // with another grammar.
            continue;
        };
        let mut vars = VarIndex::new();
        let mut patterns = Vec::with_capacity(def.params.len());
        let mut arg_kinds = Vec::with_capacity(def.params.len());
        let mut valid = true;
        for param in &def.params {
            match parse_build(param, grammar, &lm.built, i, &mut vars) {
                Ok(pattern) => {
                    arg_kinds.push(term_kind(&pattern, lm));
                    patterns.push(pattern);
                }
                Err(_) => {
                    valid = false;
                    break;
                }
            }
        }
        if !valid {
            continue;
        }
        let matching_profiles: Vec<ProfileKey> = program
            .profiles
            .iter()
            .filter(|profile| {
                profile.origins.len() == 1
                    && profile.key.name == def.name
                    && profile.key.args == arg_kinds
            })
            .map(|profile| profile.key.clone())
            .collect();
        if matching_profiles.is_empty() {
            continue;
        }
        let Ok(body) = resolve_in(&def.body, lm, grammar, i, &vars) else {
            continue;
        };
        let nr_vars = vars.count();
        for key in matching_profiles {
            program.defs.push(RDef {
                key,
                patterns: patterns.clone(),
                nr_vars,
                body: body.clone(),
            });
        }
    }
    program
}

fn strategy_sort_kind(lm: &LoadedModule, name: &str) -> Option<KindId> {
    lm.built
        .sorts
        .get(name)
        .map(|&sort| lm.built.engine.sorts().kind_of(sort))
}

fn term_kind(term: &Term, lm: &LoadedModule) -> KindId {
    match term {
        Term::Var(variable) => lm.built.engine.sorts().kind_of(variable.sort),
        _ => lm.built.engine.symbol_kind(
            term.top_symbol()
                .expect("non-variable term has a top symbol"),
        ),
    }
}

fn definition_grammar<'a>(lm: &'a LoadedModule, home: Option<&str>) -> Option<&'a CompiledGrammar> {
    match home {
        None => Some(&lm.grammar),
        Some(home) if home == lm.built.name => Some(&lm.grammar),
        Some(home) => lm.strategy_grammars.get(home),
    }
}

/// The concatenated text of a token bubble (a variable `X:S` is one token).
fn token_text(toks: &[Token], i: &Interner) -> String {
    toks.iter().map(|t| i.resolve(t.sym)).collect()
}

/// All rules of the module, as [`RRule`]s (conditional rules included).
fn all_rules(lm: &LoadedModule) -> Vec<RRule> {
    lm.built.rl_traces.iter().map(rrule).collect()
}

/// The rules labelled `label`.
fn rules_labelled(lm: &LoadedModule, label: &str) -> Vec<RRule> {
    lm.built
        .rl_traces
        .iter()
        .filter(|t| t.label.as_deref() == Some(label))
        .map(rrule)
        .collect()
}

fn rrule(t: &crate::sig::syntax::RlTrace) -> RRule {
    RRule {
        lhs: t.lhs.clone(),
        rhs: t.rhs.clone(),
        condition: t.condition.clone(),
        nr_vars: t.var_names.len() as u32,
        var_names: t.var_names.clone(),
    }
}

fn reduce_or_capture(cx: &mut Cx<'_>, dag: DagId) -> DagId {
    if cx.reducer_fault.is_some() {
        return dag;
    }
    match cx.eng.try_reduce(dag) {
        Ok(reduced) => reduced,
        Err(fault) => {
            cx.reducer_fault = Some(fault);
            dag
        }
    }
}

/// Execute a search to exhaustion and return solutions in emission order with their cumulative counts.
fn run_search(cx: &mut Cx, dag: DagId, strat: Rc<RStrat>, fifo: bool) -> Vec<(DagId, u64)> {
    let mut s = Search {
        q: VecDeque::new(),
        tasks: vec![TaskState {
            parent: 0,
            slaves: 0,
            alive: true,
            kind: TaskKind::Root,
        }],
        seen: Vec::new(),
        fifo,
        out: Vec::new(),
    };
    s.schedule(vec![Process {
        dag,
        pending: push(&None, strat),
        app: None,
        task: 0,
    }]);
    while cx.reducer_fault.is_none() {
        let Some(process) = s.q.pop_front() else {
            break;
        };
        s.run_one(cx, process);
    }
    s.out
}

/// Runnable processes and the task tree that routes sub-search results and detects exhaustion.
struct Search {
    q: VecDeque<Process>,
    tasks: Vec<TaskState>,
    /// Prunes repeated `(term, pending-key, task)` states, including repeated solution states. Task identity
    /// keeps independent sub-searches separate.
    seen: Vec<(DagId, Vec<usize>, usize)>,
    fifo: bool,
    out: Vec<(DagId, u64)>,
}

impl Search {
    /// Add successors as live slaves of their tasks. FIFO mode appends them for round-robin execution;
    /// depth-first mode prepends them while preserving their local order.
    fn schedule(&mut self, succ: Vec<Process>) {
        for s in &succ {
            self.tasks[s.task].slaves += 1;
        }
        if self.fifo {
            for s in succ {
                self.q.push_back(s);
            }
        } else {
            for s in succ.into_iter().rev() {
                self.q.push_front(s);
            }
        }
    }

    /// Register a child task, which counts as one live slave of `parent`.
    fn new_task(&mut self, parent: usize, kind: TaskKind) -> usize {
        self.tasks[parent].slaves += 1;
        self.tasks.push(TaskState {
            parent,
            slaves: 0,
            alive: true,
            kind,
        });
        self.tasks.len() - 1
    }

    /// Remove one live slave. Losing the last slave exhausts the task and may cascade into its parent.
    fn dec_slave(&mut self, task: usize) {
        self.tasks[task].slaves -= 1;
        if self.tasks[task].slaves == 0 && self.tasks[task].alive {
            self.exhaust(task);
        }
    }

    /// Run a task's exhaustion action, then detach the task from its parent.
    fn exhaust(&mut self, task: usize) {
        let parent = self.tasks[task].parent;
        let succ = match &mut self.tasks[task].kind {
            TaskKind::Root | TaskKind::One { .. } | TaskKind::Call { .. } => Vec::new(),
            TaskKind::Branch {
                dag,
                failure,
                rest,
                had_success,
                ..
            } => {
                if *had_success {
                    Vec::new()
                } else {
                    vec![Process {
                        dag: *dag,
                        pending: push(rest, failure.clone()),
                        app: None,
                        task: parent,
                    }]
                }
            }
            TaskKind::Normalize {
                dag,
                rest,
                had_success,
                ..
            } => {
                if *had_success {
                    Vec::new()
                } else {
                    vec![Process {
                        dag: *dag,
                        pending: rest.clone(),
                        app: None,
                        task: parent,
                    }]
                }
            }
        };
        self.tasks[task].alive = false;
        self.schedule(succ);
        if task != parent {
            self.dec_slave(parent);
        }
    }

    /// Route a completed process through its task's continuation.
    fn emit(&mut self, task: usize, dag: DagId, count: u64) {
        let parent = self.tasks[task].parent;
        let succ = match &mut self.tasks[task].kind {
            TaskKind::Root => {
                self.out.push((dag, count));
                return;
            }
            TaskKind::Call { rest } => vec![Process {
                dag,
                pending: rest.clone(),
                app: None,
                task: parent,
            }],
            TaskKind::Branch {
                success,
                rest,
                had_success,
                ..
            } => {
                if *had_success {
                    Vec::new()
                } else {
                    *had_success = true;
                    vec![Process {
                        dag,
                        pending: push(rest, success.clone()),
                        app: None,
                        task: parent,
                    }]
                }
            }
            TaskKind::One { rest, taken } => {
                if *taken {
                    Vec::new()
                } else {
                    *taken = true;
                    vec![Process {
                        dag,
                        pending: rest.clone(),
                        app: None,
                        task: parent,
                    }]
                }
            }
            TaskKind::Normalize {
                normalize,
                rest,
                had_success,
                ..
            } => {
                *had_success = true;
                vec![Process {
                    dag,
                    pending: push(rest, normalize.clone()),
                    app: None,
                    task: parent,
                }]
            }
        };
        let commit = matches!(
            self.tasks[task].kind,
            TaskKind::One { .. } | TaskKind::Branch { .. }
        );
        self.schedule(succ);
        // `one` and conditional branching discard their remaining sub-search after the first solution.
        if commit {
            self.kill(task);
        }
    }

    /// Mark a task dead and detach it; any queued processes are discarded when dequeued.
    fn kill(&mut self, task: usize) {
        if !self.tasks[task].alive {
            return;
        }
        self.tasks[task].alive = false;
        let parent = self.tasks[task].parent;
        if task != parent {
            self.dec_slave(parent);
        }
    }

    /// Run one process step.
    fn run_one(&mut self, cx: &mut Cx, mut p: Process) {
        let t = p.task;
        if !self.tasks[t].alive {
            // A committed `one` or branch can leave already-queued processes behind.
            self.dec_slave(t);
            return;
        }
        // A resumable application fires one match and reschedules itself for the remaining matches.
        if let Some(mut app) = p.app.take() {
            if let Some(m) = app.matches.pop_front() {
                let whole = replace_at(cx.eng, p.dag, &m.path, m.result);
                cx.eng.reset_rewrites();
                let whole = reduce_or_capture(cx, whole);
                cx.count += 1 + cx.eng.rewrites();
                let result = Process {
                    dag: whole,
                    pending: app.rest.clone(),
                    app: None,
                    task: t,
                };
                let again = Process {
                    dag: p.dag,
                    pending: None,
                    app: Some(app),
                    task: t,
                };
                self.schedule(vec![result, again]);
            }
            self.dec_slave(t);
            return;
        }
        // Repeated decomposition states within one task cannot produce new continuations.
        let key = pending_key(&p.pending);
        if self
            .seen
            .iter()
            .any(|(d, k, tt)| *tt == t && *k == key && cx.eng.deep_equal(*d, p.dag))
        {
            self.dec_slave(t);
            return;
        }
        self.seen.push((p.dag, key, t));
        let Some(frame) = p.pending.clone() else {
            self.emit(t, p.dag, cx.count);
            self.dec_slave(t);
            return;
        };
        let succ = self.decompose(cx, p.dag, &frame.strat, &frame.rest, t);
        self.schedule(succ);
        self.dec_slave(t);
    }

    /// Turn the next frame into successor processes. Branch, `one`, and normalization instead create child
    /// tasks so their sub-search completion can control the outer continuation.
    fn decompose(
        &mut self,
        cx: &mut Cx,
        dag: DagId,
        strat: &Rc<RStrat>,
        rest: &Pending,
        t: usize,
    ) -> Vec<Process> {
        match &**strat {
            RStrat::Idle => vec![Process {
                dag,
                pending: rest.clone(),
                app: None,
                task: t,
            }],
            RStrat::Fail => Vec::new(),
            RStrat::Test {
                anywhere,
                extension,
                pattern,
                nr_vars,
                cond,
            } => {
                if test_holds(cx, pattern, *nr_vars, dag, *anywhere, *extension, cond) {
                    vec![Process {
                        dag,
                        pending: rest.clone(),
                        app: None,
                        task: t,
                    }]
                } else {
                    Vec::new()
                }
            }
            RStrat::Seq(..) => {
                let mut frames = Vec::new();
                flatten_seq(strat, &mut frames);
                vec![Process {
                    dag,
                    pending: push_all(rest.clone(), &frames),
                    app: None,
                    task: t,
                }]
            }
            RStrat::Union(..) => {
                let mut alts = Vec::new();
                flatten_union(strat, &mut alts);
                alts.into_iter()
                    .map(|s| Process {
                        dag,
                        pending: push(rest, s),
                        app: None,
                        task: t,
                    })
                    .collect()
            }
            RStrat::Apply {
                rules,
                top,
                subst,
                substrats,
            } => {
                if substrats.is_empty() && rules.iter().all(|r| r.condition.is_empty()) {
                    let matches = precompute_matches(cx, dag, *top, rules, subst);
                    vec![Process {
                        dag,
                        pending: None,
                        app: Some(AppState {
                            rest: rest.clone(),
                            matches,
                        }),
                        task: t,
                    }]
                } else {
                    apply_eager(cx, dag, *top, rules, subst, substrats, self.fifo)
                        .into_iter()
                        .map(|r| Process {
                            dag: r,
                            pending: rest.clone(),
                            app: None,
                            task: t,
                        })
                        .collect()
                }
            }
            RStrat::Star(child) => {
                let zero = Process {
                    dag,
                    pending: rest.clone(),
                    app: None,
                    task: t,
                };
                let more = Process {
                    dag,
                    pending: push(&push(rest, strat.clone()), child.clone()),
                    app: None,
                    task: t,
                };
                vec![zero, more]
            }
            RStrat::Plus(child) => {
                let star = Rc::new(RStrat::Star(child.clone()));
                vec![Process {
                    dag,
                    pending: push(&push(rest, star), child.clone()),
                    app: None,
                    task: t,
                }]
            }
            RStrat::Branch {
                test,
                success,
                failure,
            } => {
                let nt = self.new_task(
                    t,
                    TaskKind::Branch {
                        dag,
                        success: success.clone(),
                        failure: failure.clone(),
                        rest: rest.clone(),
                        had_success: false,
                    },
                );
                vec![Process {
                    dag,
                    pending: push(&None, test.clone()),
                    app: None,
                    task: nt,
                }]
            }
            RStrat::One(child) => {
                let nt = self.new_task(
                    t,
                    TaskKind::One {
                        rest: rest.clone(),
                        taken: false,
                    },
                );
                vec![Process {
                    dag,
                    pending: push(&None, child.clone()),
                    app: None,
                    task: nt,
                }]
            }
            RStrat::Normalize(child) => {
                let nt = self.new_task(
                    t,
                    TaskKind::Normalize {
                        dag,
                        normalize: strat.clone(),
                        rest: rest.clone(),
                        had_success: false,
                    },
                );
                vec![Process {
                    dag,
                    pending: push(&None, child.clone()),
                    app: None,
                    task: nt,
                }]
            }
            RStrat::MatchRew {
                anywhere,
                pattern,
                nr_vars,
                cond,
                by,
            } => matchrew_solutions(cx, dag, *anywhere, pattern, *nr_vars, cond, by, self.fifo)
                .into_iter()
                .map(|r| Process {
                    dag: r,
                    pending: rest.clone(),
                    app: None,
                    task: t,
                })
                .collect(),
            RStrat::Call { name, args } => {
                let bodies = Rc::new(call_bodies(cx, dag, name, args));
                if bodies.is_empty() {
                    Vec::new()
                } else {
                    vec![Process {
                        dag,
                        pending: push(rest, Rc::new(RStrat::CallGenerator { bodies, next: 0 })),
                        app: None,
                        task: t,
                    }]
                }
            }
            RStrat::CallGenerator { bodies, next } => {
                if *next >= bodies.len() {
                    Vec::new()
                } else {
                    let call_task = self.new_task(t, TaskKind::Call { rest: rest.clone() });
                    let body = Process {
                        dag,
                        pending: push(&None, bodies[*next].clone()),
                        app: None,
                        task: call_task,
                    };
                    let again = Process {
                        dag,
                        pending: push(
                            rest,
                            Rc::new(RStrat::CallGenerator {
                                bodies: bodies.clone(),
                                next: next + 1,
                            }),
                        ),
                        app: None,
                        task: t,
                    };
                    vec![body, again]
                }
            }
        }
    }
}

/// Return specialized bodies for definitions whose name, argument kinds, subject kind, and patterns match.
/// Definitions and matcher solutions retain their enumeration order.
fn call_bodies(cx: &mut Cx, dag: DagId, name: &str, args: &[Term]) -> Vec<Rc<RStrat>> {
    let subject_kind = cx.eng.sorts().kind_of(cx.eng.node(dag).sort());
    let arg_kinds: Vec<KindId> = args
        .iter()
        .map(|arg| match arg {
            Term::Var(variable) => cx.eng.sorts().kind_of(variable.sort),
            _ => cx
                .eng
                .symbol_kind(arg.top_symbol().expect("non-variable call argument")),
        })
        .collect();
    let mut arg_dags = Vec::with_capacity(args.len());
    for arg in args {
        let mut vars = Vec::new();
        term_var_indices(arg, &mut vars);
        if !vars.is_empty() {
            return Vec::new();
        }
        arg_dags.push(inst_reduce(cx, arg, &[]));
    }

    let mut bodies = Vec::new();
    for def in &cx.program.defs {
        if def.key.name != name || def.key.args != arg_kinds || def.key.subject != subject_kind {
            continue;
        }
        let mut substitutions = vec![vec![None; def.nr_vars as usize]];
        for (pattern, &arg) in def.patterns.iter().zip(&arg_dags) {
            let mut next = Vec::new();
            for substitution in substitutions {
                next.extend(match_extend(cx.eng, pattern, &substitution, arg, false));
            }
            substitutions = next;
            if substitutions.is_empty() {
                break;
            }
        }
        for substitution in substitutions {
            let terms: Vec<Option<Term>> = substitution
                .into_iter()
                .map(|binding| binding.map(|value| term_from_dag_slots(cx.eng, value)))
                .collect();
            bodies.push(specialize_strategy(&def.body, &terms));
        }
    }
    bodies
}

/// Substitute bound definition variables throughout a resolved body, leaving unbound slots unchanged.
fn specialize_strategy(strategy: &Rc<RStrat>, bindings: &[Option<Term>]) -> Rc<RStrat> {
    let resolved = match &**strategy {
        RStrat::Idle => RStrat::Idle,
        RStrat::Fail => RStrat::Fail,
        RStrat::Apply {
            rules,
            top,
            subst,
            substrats,
        } => RStrat::Apply {
            rules: rules.clone(),
            top: *top,
            subst: subst
                .iter()
                .map(|(name, term)| (name.clone(), specialize_term(term, bindings)))
                .collect(),
            substrats: substrats
                .iter()
                .map(|child| specialize_strategy(child, bindings))
                .collect(),
        },
        RStrat::One(child) => RStrat::One(specialize_strategy(child, bindings)),
        RStrat::Seq(left, right) => RStrat::Seq(
            specialize_strategy(left, bindings),
            specialize_strategy(right, bindings),
        ),
        RStrat::Union(left, right) => RStrat::Union(
            specialize_strategy(left, bindings),
            specialize_strategy(right, bindings),
        ),
        RStrat::Star(child) => RStrat::Star(specialize_strategy(child, bindings)),
        RStrat::Plus(child) => RStrat::Plus(specialize_strategy(child, bindings)),
        RStrat::Normalize(child) => RStrat::Normalize(specialize_strategy(child, bindings)),
        RStrat::Branch {
            test,
            success,
            failure,
        } => RStrat::Branch {
            test: specialize_strategy(test, bindings),
            success: specialize_strategy(success, bindings),
            failure: specialize_strategy(failure, bindings),
        },
        RStrat::Test {
            anywhere,
            extension,
            pattern,
            nr_vars,
            cond,
        } => RStrat::Test {
            anywhere: *anywhere,
            extension: *extension,
            pattern: specialize_term(pattern, bindings),
            nr_vars: *nr_vars,
            cond: cond
                .iter()
                .map(|fragment| specialize_condition(fragment, bindings))
                .collect(),
        },
        RStrat::MatchRew {
            anywhere,
            pattern,
            nr_vars,
            cond,
            by,
        } => RStrat::MatchRew {
            anywhere: *anywhere,
            pattern: specialize_term(pattern, bindings),
            nr_vars: *nr_vars,
            cond: cond
                .iter()
                .map(|fragment| specialize_condition(fragment, bindings))
                .collect(),
            by: by
                .iter()
                .map(|(variable, child)| (*variable, specialize_strategy(child, bindings)))
                .collect(),
        },
        RStrat::Call { name, args } => RStrat::Call {
            name: name.clone(),
            args: args
                .iter()
                .map(|arg| specialize_term(arg, bindings))
                .collect(),
        },
        RStrat::CallGenerator { bodies, next } => RStrat::CallGenerator {
            bodies: Rc::new(
                bodies
                    .iter()
                    .map(|body| specialize_strategy(body, bindings))
                    .collect(),
            ),
            next: *next,
        },
    };
    Rc::new(resolved)
}

fn specialize_condition(
    fragment: &ConditionFragment,
    bindings: &[Option<Term>],
) -> ConditionFragment {
    match fragment {
        ConditionFragment::Equality { lhs, rhs } => ConditionFragment::Equality {
            lhs: specialize_term(lhs, bindings),
            rhs: specialize_term(rhs, bindings),
        },
        ConditionFragment::SortTest { term, sort } => ConditionFragment::SortTest {
            term: specialize_term(term, bindings),
            sort: *sort,
        },
        ConditionFragment::Matching {
            pattern,
            subject,
            fresh_vars,
        } => ConditionFragment::Matching {
            pattern: specialize_term(pattern, bindings),
            subject: specialize_term(subject, bindings),
            fresh_vars: fresh_vars
                .iter()
                .copied()
                .filter(|&slot| bindings.get(slot as usize).is_none_or(Option::is_none))
                .collect(),
        },
        ConditionFragment::Rewrite {
            lhs,
            pattern,
            fresh_vars,
        } => ConditionFragment::Rewrite {
            lhs: specialize_term(lhs, bindings),
            pattern: specialize_term(pattern, bindings),
            fresh_vars: fresh_vars
                .iter()
                .copied()
                .filter(|&slot| bindings.get(slot as usize).is_none_or(Option::is_none))
                .collect(),
        },
    }
}

fn specialize_term(term: &Term, bindings: &[Option<Term>]) -> Term {
    match term {
        Term::Var(variable) => bindings
            .get(variable.index as usize)
            .and_then(Option::as_ref)
            .cloned()
            .unwrap_or_else(|| term.clone()),
        Term::Op { symbol, args } => Term::Op {
            symbol: *symbol,
            args: args
                .iter()
                .map(|arg| specialize_term(arg, bindings))
                .collect(),
        },
        Term::Iter { symbol, count, arg } => Term::Iter {
            symbol: *symbol,
            count: count.clone(),
            arg: Box::new(specialize_term(arg, bindings)),
        },
        Term::Na { .. } => term.clone(),
    }
}

/// Flatten a left-nested `_;_` spine into its element strategies.
fn flatten_seq(s: &Rc<RStrat>, out: &mut Vec<Rc<RStrat>>) {
    if let RStrat::Seq(a, b) = &**s {
        flatten_seq(a, out);
        flatten_seq(b, out);
    } else {
        out.push(s.clone());
    }
}

/// Flatten a `_|_` spine into alternatives while retaining decomposition order.
fn flatten_union(s: &Rc<RStrat>, out: &mut Vec<Rc<RStrat>>) {
    if let RStrat::Union(a, b) = &**s {
        flatten_union(a, out);
        flatten_union(b, out);
    } else {
        out.push(s.clone());
    }
}

/// Collect rule matches in position, rule, and matcher order. `top` restricts matching to the root, and the
/// application substitution is enforced while matching. The executor fires one collected match per step.
fn precompute_matches(
    cx: &mut Cx,
    dag: DagId,
    top: bool,
    rules: &[RRule],
    subst: &[(String, Term)],
) -> VecDeque<OneMatch> {
    let positions = if top {
        vec![Vec::new()]
    } else {
        all_positions(cx.eng, dag)
    };
    let mut out = VecDeque::new();
    for path in &positions {
        let sub = subterm_at(cx.eng, dag, path);
        for r in rules {
            let Some(initial) = initial_bindings(cx, r, subst) else {
                continue;
            };
            let mut matching = cx.eng.rewrite_match_solutions_with_bindings(
                r.lhs.clone(),
                r.nr_vars,
                sub,
                &initial,
            );
            while matching.advance() {
                let result = matching.rewrite_result(&r.rhs);
                out.push_back(OneMatch {
                    path: path.clone(),
                    result,
                });
            }
        }
    }
    out
}

/// Build initial rule-variable bindings from the application substitution. Supplying them to the matcher
/// preserves any theory-extension residue associated with each solution.
fn initial_bindings(
    cx: &mut Cx,
    r: &RRule,
    subst: &[(String, Term)],
) -> Option<Vec<Option<DagId>>> {
    let mut initial = vec![None; r.nr_vars as usize];
    for (name, term) in subst {
        let slot = r.var_names.iter().position(|candidate| candidate == name)?;
        let dag = inst(cx, term, &[]);
        initial[slot] = Some(reduce_or_capture(cx, dag));
    }
    Some(initial)
}

/// Apply rules eagerly when conditions or rewrite-condition substrategies require nested searches.
fn apply_eager(
    cx: &mut Cx,
    dag: DagId,
    top: bool,
    rules: &[RRule],
    subst: &[(String, Term)],
    substrats: &[Rc<RStrat>],
    fifo: bool,
) -> Vec<DagId> {
    let positions = if top {
        vec![Vec::new()]
    } else {
        all_positions(cx.eng, dag)
    };
    let mut out = Vec::new();
    for path in &positions {
        let sub = subterm_at(cx.eng, dag, path);
        for r in rules {
            let Some(initial) = initial_bindings(cx, r, subst) else {
                continue;
            };
            let mut matching = cx.eng.rewrite_match_solutions_with_bindings(
                r.lhs.clone(),
                r.nr_vars,
                sub,
                &initial,
            );
            let mut candidates = Vec::new();
            while matching.advance() {
                let bindings = (0..r.nr_vars).map(|slot| matching.binding(slot)).collect();
                let context = matching.rewrite_context();
                candidates.push((bindings, context));
            }
            for (bindings, context) in candidates {
                for bindings in solve_frags(cx, &r.condition, 0, bindings, substrats, 0, fifo) {
                    let bindings: Vec<DagId> = bindings
                        .into_iter()
                        .map(|binding| {
                            binding.expect("successful rule condition left an RHS variable unbound")
                        })
                        .collect();
                    let result = cx
                        .eng
                        .instantiate_rewrite_result(&r.rhs, &bindings, &context);
                    let whole = replace_at(cx.eng, dag, path, result);
                    cx.eng.reset_rewrites();
                    let whole = reduce_or_capture(cx, whole);
                    cx.count += 1 + cx.eng.rewrites();
                    out.push(whole);
                }
            }
        }
    }
    out
}

/// Solve `frags[i..]` in order and return every completed binding vector.
fn solve_frags(
    cx: &mut Cx,
    frags: &[ConditionFragment],
    i: usize,
    bindings: Vec<Option<DagId>>,
    substrats: &[Rc<RStrat>],
    sub_idx: usize,
    fifo: bool,
) -> Vec<Vec<Option<DagId>>> {
    let Some(frag) = frags.get(i) else {
        return vec![bindings];
    };
    match frag {
        ConditionFragment::Equality { lhs, rhs } => {
            let l = inst_reduce(cx, lhs, &bindings);
            let r = inst_reduce(cx, rhs, &bindings);
            if cx.eng.deep_equal(l, r) {
                solve_frags(cx, frags, i + 1, bindings, substrats, sub_idx, fifo)
            } else {
                Vec::new()
            }
        }
        ConditionFragment::SortTest { term, sort } => {
            let tt = inst_reduce(cx, term, &bindings);
            let ls = cx.eng.sort_of(tt);
            if cx.eng.sorts().same_kind(ls, *sort) && cx.eng.sorts().leq(ls, *sort) {
                solve_frags(cx, frags, i + 1, bindings, substrats, sub_idx, fifo)
            } else {
                Vec::new()
            }
        }
        ConditionFragment::Matching {
            pattern, subject, ..
        } => {
            let subj = inst_reduce(cx, subject, &bindings);
            let mut out = Vec::new();
            for nb in match_extend(cx.eng, pattern, &bindings, subj, false) {
                out.extend(solve_frags(cx, frags, i + 1, nb, substrats, sub_idx, fifo));
            }
            out
        }
        ConditionFragment::Rewrite { lhs, pattern, .. } => {
            if sub_idx >= substrats.len() {
                return Vec::new();
            }
            let start = inst_reduce(cx, lhs, &bindings);
            let states = run_search(cx, start, substrats[sub_idx].clone(), fifo);
            let mut out = Vec::new();
            for (s, _) in states {
                for nb in match_extend(cx.eng, pattern, &bindings, s, false) {
                    out.extend(solve_frags(
                        cx,
                        frags,
                        i + 1,
                        nb,
                        substrats,
                        sub_idx + 1,
                        fifo,
                    ));
                }
            }
            out
        }
    }
}

/// For each selected `matchrew` or `amatchrew` match satisfying `cond`, run every by-variable strategy to
/// exhaustion and rebuild the Cartesian product of their results. The first by-variable varies fastest.
#[allow(clippy::too_many_arguments)]
fn matchrew_solutions(
    cx: &mut Cx,
    dag: DagId,
    anywhere: bool,
    pattern: &Term,
    nr_vars: u32,
    cond: &[ConditionFragment],
    by: &[(u32, Rc<RStrat>)],
    fifo: bool,
) -> Vec<DagId> {
    let positions = if anywhere {
        all_positions(cx.eng, dag)
    } else {
        vec![Vec::new()]
    };
    let mut out = Vec::new();
    for path in &positions {
        let sub = subterm_at(cx.eng, dag, path);
        let base = vec![None; nr_vars as usize];
        for b in match_extend(cx.eng, pattern, &base, sub, false) {
            for fb in solve_frags(cx, cond, 0, b, &[], 0, fifo) {
                let mut per: Vec<Vec<DagId>> = Vec::new();
                for (vi, st) in by {
                    let subterm =
                        fb[*vi as usize].expect("matchrew by-variable bound by the match");
                    per.push(
                        run_search(cx, subterm, st.clone(), fifo)
                            .into_iter()
                            .map(|(d, _)| d)
                            .collect(),
                    );
                }
                let counts: Vec<usize> = per.iter().map(|s| s.len()).collect();
                let total: usize = counts.iter().product();
                for n in 0..total {
                    let mut rem = n;
                    let mut bnd = fb.clone();
                    for (k, (vi, _)) in by.iter().enumerate() {
                        let choice = rem % counts[k];
                        rem /= counts[k];
                        bnd[*vi as usize] = Some(per[k][choice]);
                    }
                    let new_sub = inst(cx, pattern, &bnd);
                    let whole = replace_at(cx.eng, dag, path, new_sub);
                    cx.eng.reset_rewrites();
                    let whole = reduce_or_capture(cx, whole);
                    cx.count += cx.eng.rewrites();
                    out.push(whole);
                }
            }
        }
    }
    out
}

/// Whether `pattern` matches `dag` (top / extension / anywhere) with `cond` holding under the match.
#[allow(clippy::too_many_arguments)]
fn test_holds(
    cx: &mut Cx,
    pattern: &Term,
    nr_vars: u32,
    dag: DagId,
    anywhere: bool,
    extension: bool,
    cond: &[ConditionFragment],
) -> bool {
    let positions = if anywhere {
        all_positions(cx.eng, dag)
    } else {
        vec![Vec::new()]
    };
    for path in positions {
        let sub = subterm_at(cx.eng, dag, &path);
        let base = vec![None; nr_vars as usize];
        for b in match_extend(cx.eng, pattern, &base, sub, extension) {
            if cond.is_empty() || !solve_frags(cx, cond, 0, b, &[], 0, false).is_empty() {
                return true;
            }
        }
    }
    false
}

/// Match `pattern` against `subject`, extending `base`: unbound pattern variables bound, bound ones checked
/// for consistency. `extension` enables AC/AU/S sub-part matching.
fn match_extend(
    eng: &mut Engine,
    pattern: &Term,
    base: &[Option<DagId>],
    subject: DagId,
    extension: bool,
) -> Vec<Vec<Option<DagId>>> {
    let mut pvars = Vec::new();
    term_var_indices(pattern, &mut pvars);
    let rpat = renumber_term(pattern, &pvars);
    let m = pvars.len() as u32;
    let mut raw: Vec<Vec<DagId>> = Vec::new();
    {
        let mut sols = eng.match_solutions(rpat, m, subject, extension);
        while sols.advance() {
            let mut row = Vec::with_capacity(m as usize);
            let mut ok = true;
            for j in 0..m {
                match sols.binding(j) {
                    Some(d) => row.push(d),
                    None => {
                        ok = false;
                        break;
                    }
                }
            }
            if ok {
                raw.push(row);
            }
        }
    }
    let mut out = Vec::new();
    for row in raw {
        let mut nb = base.to_vec();
        let mut ok = true;
        for (k, &v) in pvars.iter().enumerate() {
            let val = row[k];
            let idx = v as usize;
            match nb[idx] {
                Some(existing) => {
                    if !eng.deep_equal(existing, val) {
                        ok = false;
                        break;
                    }
                }
                None => nb[idx] = Some(val),
            }
        }
        if ok {
            out.push(nb);
        }
    }
    out
}

/// Rebuild `t` with its variables renumbered to their position in `pvars` (a compact space).
fn renumber_term(t: &Term, pvars: &[u32]) -> Term {
    match t {
        Term::Var(v) => {
            let j = pvars
                .iter()
                .position(|&x| x == v.index)
                .expect("variable collected by term_var_indices");
            Term::var(j as u32, v.sort)
        }
        Term::Na { symbol, value } => Term::Na {
            symbol: *symbol,
            value: value.clone(),
        },
        Term::Iter { symbol, count, arg } => {
            Term::iter(*symbol, count.clone(), renumber_term(arg, pvars))
        }
        Term::Op { symbol, args } => Term::Op {
            symbol: *symbol,
            args: args.iter().map(|a| renumber_term(a, pvars)).collect(),
        },
    }
}

/// Build a DAG instance of `term` under `bindings` (a partial binding vector). Unbound slots are filled with
/// an arbitrary bound value (never read).
fn inst(cx: &mut Cx, term: &Term, bindings: &[Option<DagId>]) -> DagId {
    match bindings.iter().flatten().copied().next() {
        None => cx.eng.instantiate_bindings(term, &[]),
        Some(placeholder) => {
            let full: Vec<DagId> = bindings.iter().map(|b| b.unwrap_or(placeholder)).collect();
            cx.eng.instantiate_bindings(term, &full)
        }
    }
}

/// Instantiate `term` under `bindings` and reduce it, counting the reductions toward the running total.
fn inst_reduce(cx: &mut Cx, term: &Term, bindings: &[Option<DagId>]) -> DagId {
    let d = inst(cx, term, bindings);
    cx.eng.reset_rewrites();
    let r = reduce_or_capture(cx, d);
    cx.count += cx.eng.rewrites();
    r
}

/// All subterm positions of `dag` (child-index paths), pre-order (outermost first).
fn all_positions(eng: &Engine, dag: DagId) -> Vec<Vec<usize>> {
    fn go(eng: &Engine, node: DagId, path: &mut Vec<usize>, out: &mut Vec<Vec<usize>>) {
        out.push(path.clone());
        let kids: Vec<DagId> = eng.node(node).children().collect();
        for (k, c) in kids.into_iter().enumerate() {
            path.push(k);
            go(eng, c, path, out);
            path.pop();
        }
    }
    let mut out = Vec::new();
    go(eng, dag, &mut Vec::new(), &mut out);
    out
}

/// The subterm of `root` at child-index `path`.
fn subterm_at(eng: &Engine, root: DagId, path: &[usize]) -> DagId {
    let mut node = root;
    for &k in path {
        node = eng.node(node).children().nth(k).expect("valid position");
    }
    node
}

/// `root` with the subterm at `path` replaced by `new` (rebuilding the spine, theory-aware). An `iter`
/// ancestor `f^n(...)` keeps its count `n`; `make_node` would build a single application of `f`.
fn replace_at(eng: &mut Engine, root: DagId, path: &[usize], new: DagId) -> DagId {
    let Some((&head, rest)) = path.split_first() else {
        return new;
    };
    let sym = eng.node(root).symbol();
    let mut kids: Vec<DagId> = eng.node(root).children().collect();
    kids[head] = replace_at(eng, kids[head], rest, new);
    let iter_count = match eng.node(root).repr() {
        NodeRepr::Iter { count, .. } => Some(count),
        _ => None,
    };
    match iter_count {
        Some(count) => eng
            .make_iter_decimal(sym, &count, kids[0])
            .expect("an iteration count is a decimal numeral"),
        None => eng.make_node(sym, kids),
    }
}

/// Deduplicate solutions by `deep_equal`, keeping the first occurrence + its count.
fn dedup(eng: &Engine, sols: Vec<StratSolution>) -> Vec<StratSolution> {
    let mut out: Vec<StratSolution> = Vec::new();
    for s in sols {
        if !out.iter().any(|k| eng.deep_equal(k.term, s.term)) {
            out.push(s);
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lex::tokenize;
    use crate::load::build_loaded_module;
    use crate::surface::parser::Parser;

    fn loaded_strategy_module(source: &str) -> (LoadedModule, Interner) {
        let mut interner = Interner::new();
        let tokens = tokenize(source, &mut interner);
        let mut source = Parser::new(&tokens, &interner)
            .parse_source()
            .expect("parse strategy module");
        assert_eq!(source.modules.len(), 1);
        let module = source.modules.remove(0);
        let loaded = build_loaded_module(&module, &mut interner).expect("build strategy module");
        (loaded, interner)
    }

    #[test]
    fn declaration_profiles_use_kinds_not_exact_sorts() {
        let (loaded, interner) = loaded_strategy_module(
            "smod STRAT-PROFILES is
               sorts K A B T .
               subsorts A B < K .
               ops a : -> A .
               op b : -> B .
               op t : -> T .
               strat same : A @ A .
               strat same : B @ B .
               strat same : T @ T .
               strat zero : @ A .
               strat zero : @ B .
             endsm",
        );
        let program = compile_strategy_program(&loaded, &interner);
        let same = program
            .profiles
            .iter()
            .filter(|profile| profile.key.name == "same")
            .collect::<Vec<_>>();
        assert_eq!(
            same.len(),
            2,
            "A/B declarations coalesce by their shared argument and subject kinds; T stays distinct"
        );
        assert_eq!(
            program
                .profiles
                .iter()
                .filter(|profile| profile.key.name == "zero")
                .count(),
            1,
            "zero-argument declarations ignore the exact A/B subject sort within one kind"
        );
    }

    #[test]
    fn definitions_keep_order_and_share_lhs_variable_slots() {
        let (loaded, interner) = loaded_strategy_module(
            "smod STRAT-DEFINITIONS is
               sort S .
               ops a b : -> S .
               var X : S .
               strat choose : S @ S .
               strat pair : S S @ S .
               sd choose(a) := idle .
               sd choose(b) := fail .
               sd pair(X, X) := match X .
             endsm",
        );
        let program = compile_strategy_program(&loaded, &interner);
        let choose = program
            .defs
            .iter()
            .filter(|definition| definition.key.name == "choose")
            .collect::<Vec<_>>();
        assert_eq!(choose.len(), 2);
        let pattern_name = |definition: &RDef| match &definition.patterns[0] {
            Term::Op { symbol, args } if args.is_empty() => {
                loaded.built.engine.symbol(*symbol).name()
            }
            pattern => panic!("expected constant definition pattern, got {pattern:?}"),
        };
        assert_eq!(
            choose
                .iter()
                .map(|definition| pattern_name(definition))
                .collect::<Vec<_>>(),
            ["a", "b"],
            "definition declaration order is retained"
        );

        let pair = program
            .defs
            .iter()
            .find(|definition| definition.key.name == "pair")
            .expect("pair definition");
        assert_eq!(pair.nr_vars, 1);
        let [Term::Var(left), Term::Var(right)] = pair.patterns.as_slice() else {
            panic!("expected two variable patterns");
        };
        assert_eq!(
            left.index, right.index,
            "both lhs occurrences bind the same strategy variable slot"
        );
        let RStrat::Test {
            pattern: Term::Var(body),
            ..
        } = &*pair.body
        else {
            panic!("expected match test body");
        };
        assert_eq!(
            body.index, left.index,
            "the lhs binding is shared with the resolved definition body"
        );
    }
}
