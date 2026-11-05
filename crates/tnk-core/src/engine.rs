//! The [`Engine`] — the instantiable owner of all runtime state (no globals,
//! so several engines can coexist, e.g. for meta-interpreters).
//!
//! Internally it is split into an immutable-during-reduction `Signature`
//! (sorts, symbols, compiled equations) and a mutable `Runtime` (the GC'd DAG arena, roots, and
//! rewrite statistics): matching and instantiation hold a *shared* borrow of the signature while
//! mutating the runtime, so a rewrite instantiates an equation's right-hand side straight out of
//! the still-borrowed equation table — no defensive clone. [`Engine`] is a thin facade that
//! re-exposes the same public API over the two halves.
//!
//! It computes each node's least sort at construction and runs garbage collection
//! (non-moving mark-sweep) over the DAG from an explicit root set.

use crate::arena::Arena;
use crate::dag::{DagId, DagNode, NaValue, NodeTerm};
use crate::descent::{DescentOps, MetaCtx, NullDescent};
use crate::external::{ExternalRewriteBreakdown, ExternalTargetToken, MetaEnvelope};
use crate::host::{
    HookSort, HostBindingError, HostBindingId, HostFunctionCatalog, HostFunctionId,
    HostFunctionKey, ReducerFault, ResolvedHostBinding, ResolvedHostHooks, StrictOutcome, built_id,
    invoke_strict,
};
use crate::num::Nat;
use crate::rewrite::Rewriting;
use crate::root::{RootGuard, Roots};
use crate::search::{Arrow, RawSuccessor, RawSuccessors, Search};
use crate::smt::{SmtInfo, SmtNumber, SmtOp, SmtType};
use crate::smt_search::SmtSearch;
use crate::sort::{KindId, SortId, Sorts};
use crate::symbol::{
    Axioms, EvalStep, EvalStrategy, Identity, IdentityId, IdentitySide, OoFlags, OpDeclaration,
    SpecialOp, StdStream, Symbol, SymbolClass, SymbolId, Theory,
};
use crate::term::{ConditionFragment, Equation, Membership, Subst, Term};
use crate::theory::{LhsAutomaton, RewriteMatchContext, Subproblem};
use std::cell::Cell;
use std::cmp::Ordering;
use std::collections::{HashMap, HashSet, VecDeque};

/// Conservative static register pressure for constructing `term` into a substitution slot.
///
/// Temporary RHS pressure is estimated from tree lifetimes: non-variable children are built
/// largest-first, stay live until their parent is built, and allow the parent to reuse one child slot.
/// Ignoring reusable LHS terms makes this a conservative upper bound.
fn term_construction_slots(term: &Term) -> usize {
    let children: Vec<&Term> = match term {
        Term::Var(_) => return 0,
        Term::Na { .. } => return 1,
        Term::Iter { arg, .. } => vec![arg],
        Term::Op { args, .. } => args.iter().collect(),
    };
    let mut pressures: Vec<usize> = children
        .into_iter()
        .map(term_construction_slots)
        .filter(|&p| p != 0)
        .collect();
    pressures.sort_unstable_by(|a, b| b.cmp(a));
    let mut peak = 0;
    for (live, pressure) in pressures.into_iter().enumerate() {
        peak = peak.max(live + pressure);
    }
    peak.max(1)
}

/// Construction pressure of one condition fragment. Both sides of an equality must coexist;
/// matching/rewrite patterns are match automata rather than constructed terms.
fn fragment_construction_slots(fragment: &ConditionFragment) -> usize {
    match fragment {
        ConditionFragment::Equality { lhs, rhs } => {
            let lhs = term_construction_slots(lhs);
            let rhs = term_construction_slots(rhs);
            lhs.max((lhs != 0) as usize + rhs)
        }
        ConditionFragment::SortTest { term, .. } => term_construction_slots(term),
        ConditionFragment::Matching { subject, .. } => term_construction_slots(subject),
        ConditionFragment::Rewrite { lhs, .. } => term_construction_slots(lhs),
    }
}

fn term_variable_indices(term: &Term) -> HashSet<u32> {
    let mut variables = HashSet::new();
    let mut work = vec![term];
    while let Some(term) = work.pop() {
        match term {
            Term::Var(variable) => {
                variables.insert(variable.index);
            }
            Term::Op { args, .. } => work.extend(args),
            Term::Iter { arg, .. } => work.push(arg),
            Term::Na { .. } => {}
        }
    }
    variables
}

fn term_is_linear(term: &Term) -> bool {
    let mut variables = HashSet::new();
    let mut work = vec![term];
    while let Some(term) = work.pop() {
        match term {
            Term::Var(variable) => {
                if !variables.insert(variable.index) {
                    return false;
                }
            }
            Term::Op { args, .. } => work.extend(args),
            Term::Iter { arg, .. } => work.push(arg),
            Term::Na { .. } => {}
        }
    }
    true
}

fn term_contains_smt(sig: &Signature, term: &Term) -> bool {
    let mut work = vec![term];
    while let Some(term) = work.pop() {
        match term {
            Term::Var(_) => {}
            Term::Op { symbol, args } => {
                let symbol = sig.symbol(*symbol);
                if matches!(symbol.special(), Some(SpecialOp::Smt { .. }))
                    || symbol.class() == SymbolClass::SmtNumber
                {
                    return true;
                }
                work.extend(args);
            }
            Term::Iter { symbol, arg, .. } => {
                if matches!(sig.symbol(*symbol).special(), Some(SpecialOp::Smt { .. })) {
                    return true;
                }
                work.push(arg);
            }
            Term::Na { symbol, .. } => {
                if sig.symbol(*symbol).class() == SymbolClass::SmtNumber {
                    return true;
                }
            }
        }
    }
    false
}

/// Variables mentioned by a statement condition. ACU's specialized sole nonlinear-variable
/// automaton is invalid for one of these variables because a failed condition must be able to
/// backtrack through the general matcher stream.
fn condition_variable_indices(condition: &[ConditionFragment]) -> HashSet<u32> {
    let mut variables = HashSet::new();
    let mut add = |term: &Term| variables.extend(term_variable_indices(term));
    for fragment in condition {
        match fragment {
            ConditionFragment::Equality { lhs, rhs } => {
                add(lhs);
                add(rhs);
            }
            ConditionFragment::SortTest { term, .. } => add(term),
            ConditionFragment::Matching {
                pattern, subject, ..
            } => {
                add(pattern);
                add(subject);
            }
            ConditionFragment::Rewrite { lhs, pattern, .. } => {
                add(lhs);
                add(pattern);
            }
        }
    }
    variables
}

/// Structural equation-pattern matching for static terms. Pattern variables are wildcards, with
/// repeated occurrences required to denote the same subject subtree.
fn term_matches_pattern(pattern: &Term, subject: &Term) -> bool {
    fn matches(pattern: &Term, subject: &Term, bindings: &mut HashMap<u32, Term>) -> bool {
        match (pattern, subject) {
            (Term::Var(variable), subject) => match bindings.get(&variable.index) {
                Some(bound) => bound == subject,
                None => {
                    bindings.insert(variable.index, subject.clone());
                    true
                }
            },
            (
                Term::Op {
                    symbol: pattern_symbol,
                    args: pattern_args,
                },
                Term::Op {
                    symbol: subject_symbol,
                    args: subject_args,
                },
            ) => {
                pattern_symbol == subject_symbol
                    && pattern_args.len() == subject_args.len()
                    && pattern_args
                        .iter()
                        .zip(subject_args)
                        .all(|(pattern, subject)| matches(pattern, subject, bindings))
            }
            (
                Term::Iter {
                    symbol: pattern_symbol,
                    count: pattern_count,
                    arg: pattern_arg,
                },
                Term::Iter {
                    symbol: subject_symbol,
                    count: subject_count,
                    arg: subject_arg,
                },
            ) => {
                pattern_symbol == subject_symbol
                    && pattern_count == subject_count
                    && matches(pattern_arg, subject_arg, bindings)
            }
            (Term::Na { .. }, Term::Na { .. }) => pattern == subject,
            _ => false,
        }
    }

    matches(pattern, subject, &mut HashMap::new())
}

/// An equation as stored in the engine: its left-hand side compiled to a theory [`LhsAutomaton`],
/// with the right-hand side and variable count kept for instantiation.
/// The public [`Equation`] (lhs as a [`Term`]) is compiled into this by [`Engine::add_equation`].
#[derive(Clone)]
struct CompiledEquation {
    /// Dense per-module id (assigned by [`Signature::push_equation`]); the frontend keeps this
    /// equation's source `Term`s + variable names at `eq_traces[id]` for the trace renderer.
    id: u32,
    lhs: LhsAutomaton,
    rhs: Term,
    nr_vars: u32,
    /// Every condition fragment must hold; failure resumes the next matcher solution.
    condition: Vec<CompiledFragment>,
    /// Fallback equation, considered only after ordinary equations for the symbol fail.
    owise: bool,
    /// Whether rhs construction needs structural deduplication for a repeated compound subterm.
    rhs_shares: bool,
    /// Non-ground compound RHS subterms that also occur below the LHS root. Reusing their already
    /// reduced matched DAGs preserves structure-sensitive rewrite counts.
    lhs_reuse: Vec<Term>,
}

/// Compiled membership matcher, target sort, variable layout, and optional condition.
struct SortConstraint {
    /// Dense per-module id (assigned by [`Signature::push_membership`]); the frontend keeps this
    /// membership's source `Term` + variable names at `mb_traces[id]` for the trace renderer.
    id: u32,
    lhs: LhsAutomaton,
    sort: SortId,
    nr_vars: u32,
    /// Evaluated under the membership substitution before the sort is lowered.
    condition: Vec<CompiledFragment>,
}

/// Observable sort-constraint order: descending component-local target-sort index, then declaration id.
/// Both direct-symbol and collapsing-kind indexes use this comparator so their runtime merge is allocation-free.
fn membership_order(
    constraints: &[SortConstraint],
    sorts: &Sorts,
    left: u32,
    right: u32,
) -> Ordering {
    let left_constraint = &constraints[left as usize];
    let right_constraint = &constraints[right as usize];
    sorts
        .component_index(right_constraint.sort)
        .cmp(&sorts.component_index(left_constraint.sort))
        .then_with(|| left.cmp(&right))
}

/// A rule `rl lhs => rhs` compiled for the engine: structurally a [`CompiledEquation`] without `[owise]`.
/// Rules live in their own [`Signature::rules`] table and are applied only by rewriting and search,
/// never by [`reduce`](Engine::reduce). The frontend retains source terms, variable names, and labels
/// for tracing and `show path`.
/// The `erewrite` role of a rule. A configuration rule with exactly one object and one message sharing
/// the same name uses the message-keyed fast path; all other configuration rules use `LeftOver`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum OoRuleKind {
    NotConfig,
    ObjectMessage(SymbolId),
    LeftOver,
}

/// Which `erewrite` rule class [`Runtime::apply_first_rule_filtered`] considers.
#[derive(Debug, Clone, Copy)]
enum RuleFilter {
    /// Fast-path object-message rules (any message symbol).
    ObjectMessage,
    /// Generic `leftOver` rules.
    LeftOver,
}

struct CompiledRule {
    id: u32,
    /// Source rule label shared with the frontend's trace metadata; `None` for an unlabeled rule.
    label: Option<std::rc::Rc<str>>,
    lhs: LhsAutomaton,
    rhs: Term,
    nr_vars: u32,
    /// The `erewrite` scheduler role, classified from the (uncompiled) lhs at registration.
    oo: OoRuleKind,
    /// Condition fragments (empty for an unconditional `rl`); a `crl` may additionally carry a rewrite
    /// fragment `t => p`, which is not legal in equations or memberships.
    condition: Vec<CompiledFragment>,
    /// Whether rhs construction needs structural deduplication.
    rhs_shares: bool,
}

/// A source-ordered rule compiled for rewriting modulo SMT. Unlike [`CompiledRule`], this table also
/// retains `[nonexec]` rules: SMT search supplies fresh values for variables not bound by the lhs and
/// treats equality conditions as solver constraints rather than reducing them.
struct CompiledSmtRule {
    variable_sorts: Vec<SortId>,
    lhs: LhsAutomaton,
    rhs: Term,
    nr_vars: u32,
    condition: Vec<ConditionFragment>,
    variable_names: Vec<String>,
}

/// One satisfiability-unchecked symbolic transition. The SMT search state machine owns solver
/// push/pop and accepts only transitions whose `local_constraint` is satisfiable with the parent.
pub(crate) struct RawSmtSuccessor {
    pub term: DagId,
    pub local_constraint: Option<DagId>,
    pub avoid_variable_number: Nat,
    pub fresh_names: Vec<(u32, String)>,
}

/// One structural goal match before its SMT-variable equalities are checked against the state
/// constraint.
pub(crate) struct RawSmtGoalMatch {
    pub bindings: Vec<DagId>,
    pub match_constraint: Option<DagId>,
}

/// A condition fragment compiled for evaluation: like the public [`ConditionFragment`] but with the
/// matching fragment's pattern compiled to an [`LhsAutomaton`]. Built by
/// [`Signature::compile_condition`]. The `fresh_vars` of a matching fragment are unbound before each
/// match attempt so backtracking re-binds cleanly.
#[derive(Clone)]
pub(crate) enum CompiledFragment {
    Equality {
        lhs: Term,
        rhs: Term,
    },
    SortTest {
        term: Term,
        sort: SortId,
    },
    Matching {
        pattern: LhsAutomaton,
        subject: Term,
        fresh_vars: Vec<u32>,
    },
    /// `lhs => pattern` — a rewrite condition, legal only in rules: search `lhs`'s reachable states and
    /// match `pattern` against each one.
    Rewrite {
        lhs: Term,
        pattern: LhsAutomaton,
        fresh_vars: Vec<u32>,
    },
}

/// Which statement a condition belongs to — gates the `=>` (rewrite) fragment, which is legal **only** in
/// a rule (`crl`) condition, never in an equation/membership (`ceq`/`cmb`).
#[derive(Clone, Copy, PartialEq, Eq)]
pub(crate) enum CondOwner {
    EqOrMb,
    Rule,
}

/// Whether [`Runtime::drive_match`]'s `accept` callback stops at the first rewrite (equational reduction
/// and direct rewriting) or enumerates every solution (search successor collection).
enum Flow {
    Stop,
    /// Keep enumerating every solution. Equational reduction and direct rewriting use [`Flow::Stop`].
    Continue,
}

/// Identifies the statement [`Runtime::drive_match`] is driving, for trace events and condition
/// root set. `kind` selects the trace metadata (equation vs rule) and the [`RewriteKind`]; `frames`/`redex`
/// are threaded into [`condition_holds`](Runtime::condition_holds) for GC rooting of a conditional
/// statement's re-entrant condition reduction (moot for unconditional statements / GC-off REPL).
struct StmtCtx<'a> {
    kind: StmtKind,
    stmt_id: u32,
    frames: &'a [ReduceFrame],
    redex: DagId,
}

/// One position in the top-down rewrite stack: node, parent index, and flattened parent argument.
/// These fields reconstruct the root path after a rewrite.
struct RedexPos {
    node: DagId,
    parent: usize,
    arg_index: usize,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum EvalAction {
    Argument(usize),
    Top { final_step: bool },
}

/// One pending node-normalization on the iterative [`Engine::reduce`] work-stack.
///
/// A frame represents one recursive `reduce`/`reduce_args` activation without using the call stack.
/// Its cursor executes the operator's normalized argument/top instruction stream. Reduced children
/// replace their positions in `args`, while a successful Top instruction reuses the frame slot.
///
/// **Safe-point GC contract.** Frames contain most in-flight DAG handles, but a completed child remains
/// in `child_result` until the next loop iteration. Collection is therefore restricted to the loop head,
/// where `walk(stack) ∪ child_result` is complete. Matcher and constructor locals are not discoverable
/// from the frame stack and must not cross a collection point unrooted.
struct ReduceFrame {
    /// The node first assigned to this frame. It remains stable across top rewrites so normal-form
    /// forwarding can update every shared reference to the original redex.
    start: DagId,
    /// The node this frame started from; returned unchanged when no child changed (preserves the
    /// shared DAG id rather than rebuilding an identical node).
    original: DagId,
    symbol: SymbolId,
    /// The original children of `original`, copied out so the spine can be walked across the `&mut
    /// self` reductions that may grow (and thus reallocate) the arena. The change test is `args != orig`.
    orig: Vec<DagId>,
    /// Current arguments: `orig` with each strategy-reduced position replaced by its normal form;
    /// positions the strategy leaves unreduced keep their `orig` value (lazy). The node is rebuilt from
    /// this.
    args: Vec<DagId>,
    /// Instructions completed so far; [`Signature::strat_action`] synthesizes the standard and
    /// permutative strategies or indexes the symbol's normalized sequence.
    cursor: usize,
    /// Whether the first top instruction has been reached, where every argument's true sort is computed.
    seen_top: bool,
}

/// One symbolic alien that may need a protected abstraction slot while matching a statement LHS.
struct LayoutAlien {
    parent: SymbolId,
    term: Term,
}

/// An equation-derived collapse shape. `target = None` means the pattern can collapse to any term;
/// otherwise it can collapse to a term rooted by that symbol.
struct CollapsePattern {
    pattern: Term,
    target: Option<SymbolId>,
}

/// Static ingredients needed to revise a statement's substitution lower bound when later equations
/// reveal additional collapse shapes.
struct SubstitutionLayoutEstimate {
    /// Real variables plus colored RHS/condition construction slots.
    base: usize,
    abstraction_candidates: Vec<LayoutAlien>,
}

/// The immutable-during-reduction half of the engine: the sort poset, the symbol table, and the
/// compiled equation set. Matching, instantiation, and reduction take this by shared reference, so
/// the [`Runtime`] can mutate the DAG arena while the equation table stays borrowed.
pub(crate) struct Signature {
    sorts: Sorts,
    symbols: Arena<Symbol>,
    /// Ground identity terms referenced by symbols. Unlike DAG nodes these are signature-lifetime data;
    /// the runtime materializes each as one normalized, rooted DAG.
    identities: Arena<Identity>,
    /// Unconditional equations (LHS compiled to a theory automaton), indexed by lhs top symbol.
    equations: HashMap<SymbolId, Vec<CompiledEquation>>,
    /// Every compiled membership axiom exactly once, in declaration/id order. The direct and collapsing
    /// indexes below contain ids into this arena, avoiding matcher/condition copies for broadly offered
    /// collapse constraints. Empty in modules without memberships, preserving the hot-path gate.
    memberships: Vec<SortConstraint>,
    /// Noncollapsing memberships, indexed only by their syntactic lhs top symbol.
    membership_index: HashMap<SymbolId, Vec<u32>>,
    /// ACU/two-sided-AU/CUI memberships that can collapse at the top, offered to every subject in the
    /// target sort's kind. The compiled matcher rejects impossible conservative candidates.
    collapsing_memberships: HashMap<KindId, Vec<u32>>,
    /// Rules (`rl`/`crl`), indexed by lhs top symbol. Applied only by rewriting and search, never by
    /// [`reduce`](Engine::reduce), so adding one does not change equational normal forms or `eq_epoch`.
    rules: HashMap<SymbolId, Vec<CompiledRule>>,
    /// Source-form rules used only by `smt-search`, indexed by lhs top symbol. This deliberately
    /// includes `[nonexec]` rules, which are proof obligations for ordinary rewriting but executable
    /// symbolic transitions modulo SMT.
    smt_rules: HashMap<SymbolId, Vec<CompiledSmtRule>>,
    /// Whether every retained SMT rule satisfies the static SMT-rewriting LHS restrictions.
    smt_rules_valid: bool,
    /// Source-form `[narrowing]` rules in flattened module order. This includes nonexec rules that are
    /// deliberately absent from `rules`; symbolic unification needs their lhs/rhs and variable layout.
    narrowing_rules: Vec<crate::narrow::NarrowingRule>,
    /// Bumped whenever the equation set changes; stamped into nodes when they are proved canonical,
    /// so `add_equation` invalidates stale "reduced" results. `0` is the "never
    /// reduced" sentinel stored on nodes, so this starts at `1`.
    eq_epoch: u32,
    /// Next dense equation id (the count of equations added). Assigned to each [`CompiledEquation`] so
    /// the frontend can key its trace metadata by it; per-module (each `Engine` starts at 0).
    next_eq_id: u32,
    /// Next dense membership-axiom id (the count of memberships added). Assigned to each
    /// [`SortConstraint`] so the frontend can key trace metadata by it.
    next_mb_id: u32,
    /// Next dense rule id (the count of rules added). Assigned to each [`CompiledRule`]; the frontend
    /// keys its `rl_traces` metadata by it.
    next_rule_id: u32,
    /// Quoted-identifier classification sorts (META-TERM's `<Qids>` ops). When set, a `Qid` constant's
    /// least sort is text-dependent (`'X:S` → `Variable`, `'c.S` → `Constant`, `'[K]` → `Kind`, plain `'S`
    /// → `Sort`); empty elsewhere, where every `Qid` is just a `Qid`.
    qid_class: QidClass,
    /// SMT sort/operator bindings assembled from `SMT_Symbol`/`SMT_NumberSymbol` hooks.
    smt_info: SmtInfo,
    /// Per-sort variable symbols created lazily in demand order. Creation order participates in
    /// `dag_compare` through symbol identity.
    var_symbols: HashMap<SortId, SymbolId>,
    /// The `zeroTerm` attached to each `iter` successor (`SuccSymbol`).
    succ_zeros: HashMap<SymbolId, SymbolId>,
    /// Module-wide lower bound for substitution arrays: statement variables plus temporary
    /// construction and protected-variable slots.
    minimum_substitution_size: usize,
    /// Equation-derived symbolic collapse shapes used to approximate protected LHS abstraction
    /// variables. Retained so imported/replayed statement metadata remains module-global.
    collapse_patterns: Vec<CollapsePattern>,
    substitution_layout_estimates: Vec<SubstitutionLayoutEstimate>,
    /// Immutable reducer implementations shared by every binding in this signature.
    host_functions: HostFunctionCatalog,
    /// Signature-local hook and declaration bindings referenced by `SpecialOp::HostFunction`.
    host_bindings: Vec<ResolvedHostBinding>,
    /// One-way lifecycle guard: semantic execution prevents later host attachment or replacement.
    host_bindings_sealed: Cell<bool>,
}

/// Sorts used to classify quoted-identifier constants; see [`Signature::qid_class`].
#[derive(Debug, Default, Clone, Copy)]
pub(crate) struct QidClass {
    base: Option<SortId>,
    sort: Option<SortId>,
    kind: Option<SortId>,
    constant: Option<SortId>,
    variable: Option<SortId>,
}

#[derive(Clone, Copy)]
enum QidAux {
    Sort,
    StructuredSort,
    Variable,
    Constant,
    Kind,
}

/// Scan canonical quoted-identifier sort-name syntax. Returns the byte index of the terminator and
/// whether the name contains a structured-sort parameter list.
fn skip_qid_sort_name(text: &[u8], start: usize) -> Option<(usize, bool)> {
    let mut parameterized = false;
    let mut depth = 0_u32;
    let mut seen_name = false;
    let mut i = start;
    loop {
        let Some(&byte) = text.get(i) else {
            return (seen_name && depth == 0).then_some((i, parameterized));
        };
        match byte {
            b'`' => {
                let escaped = *text.get(i + 1)?;
                match escaped {
                    b']' => {
                        return (seen_name && depth == 0).then_some((i, parameterized));
                    }
                    b'{' if seen_name => {
                        parameterized = true;
                        depth += 1;
                        seen_name = false;
                    }
                    b',' if seen_name => {
                        if depth == 0 {
                            return Some((i, parameterized));
                        }
                        seen_name = false;
                    }
                    b'}' if seen_name && depth > 0 => {
                        depth -= 1;
                    }
                    b'[' | b'{' | b',' | b'}' => return None,
                    _ => seen_name = true,
                }
                i += 2;
            }
            b'.' | b':' if depth == 0 => return None,
            _ => {
                seen_name = true;
                i += 1;
            }
        }
    }
}

/// Add canonical backtick escapes to compact quoted-identifier text before auxiliary classification.
fn canonical_qid_token_name(text: &str) -> std::borrow::Cow<'_, str> {
    let punct = |c: char| matches!(c, '(' | ')' | '[' | ']' | '{' | '}' | ',');
    let mut previous_backtick = false;
    let needs_escape = text.chars().any(|c| {
        let needed = punct(c) && !previous_backtick;
        previous_backtick = c == '`';
        needed
    });
    if !needs_escape {
        return std::borrow::Cow::Borrowed(text);
    }

    let mut out = String::with_capacity(text.len() + 4);
    previous_backtick = false;
    for c in text.chars() {
        if punct(c) && !previous_backtick {
            out.push('`');
        }
        out.push(c);
        previous_backtick = c == '`';
    }
    std::borrow::Cow::Owned(out)
}

/// Classify a quoted identifier's unquoted text using canonical token-name rules.
fn qid_aux_property(text: &str) -> Option<QidAux> {
    let text = canonical_qid_token_name(text);
    let bytes = text.as_bytes();

    if bytes.starts_with(b"`[") {
        // Parse one or more sort names separated by backtick-comma and closed by backtick-right-bracket.
        let mut start = 1;
        loop {
            let (end, _) = skip_qid_sort_name(bytes, start)?;
            match (bytes.get(end), bytes.get(end + 1)) {
                (Some(b'`'), Some(b']')) if end + 2 == bytes.len() => {
                    return Some(QidAux::Kind);
                }
                (Some(b'`'), Some(b',')) => start = end + 2,
                _ => break,
            }
        }
    } else if let Some((end, parameterized)) = skip_qid_sort_name(bytes, 0)
        && end == bytes.len()
    {
        return Some(if parameterized {
            QidAux::StructuredSort
        } else {
            QidAux::Sort
        });
    }

    // Constant and variable suffixes are recognized only when the suffix itself is a sort or kind.
    // Separators inside a structured-sort `{...}` parameter list do not count.
    let mut depth = 0_i32;
    for i in (1..bytes.len()).rev() {
        match bytes[i] {
            b'}' => depth += 1,
            b'{' => depth -= 1,
            b'.' | b':' if depth == 0 => {
                let suffix = text.get(i + 1..)?;
                if matches!(
                    qid_aux_property(suffix),
                    Some(QidAux::Sort | QidAux::StructuredSort | QidAux::Kind)
                ) {
                    return Some(if bytes[i] == b'.' {
                        QidAux::Constant
                    } else {
                        QidAux::Variable
                    });
                }
                break;
            }
            _ => {}
        }
    }
    None
}

/// One recorded reduction event, enabled through [`Engine::set_trace`]. Each event carries its
/// condition-nesting `depth`: zero at the command's top level and one higher inside each condition
/// fragment. Disabling condition tracing renders only depth-zero events. Node IDs retained by an event
/// (redex, result, bindings, subject, and whole term) participate in the reduction's GC root set.
///
/// The `id` values identify equations and membership axioms within one compiled module. The frontend
/// retains the corresponding source terms and variable names for rendering.
#[derive(Debug, Clone)]
pub enum TraceEvent {
    /// A term rewrite: an equation (`eq_id = Some`) or a built-in (`special`) reduction (`eq_id =
    /// None`). `bindings[i]` is the matched value of the equation's variable `i` (`None` = unbound; empty
    /// for a built-in). `whole_before`/`whole_after` are the whole root term before/after this rewrite —
    /// `Some` only when whole-tracing is on (`set trace whole`); reconstructed from the reduce frame stack.
    Rewrite {
        kind: RewriteKind,
        eq_id: Option<u32>,
        depth: u32,
        /// Stable configured identity for a strict host rewrite; absent for every other rewrite kind.
        host_key: Option<HostFunctionKey>,
        redex: DagId,
        result: DagId,
        bindings: Vec<Option<DagId>>,
        whole_before: Option<DagId>,
        whole_after: Option<DagId>,
    },
    /// A membership-axiom sort narrowing (not a term rewrite): `subject`'s least sort was lowered from
    /// `old_sort` to `new_sort` by membership `mb_id`. `bindings` is the membership match's substitution.
    /// (`whole` is reserved for `set trace whole`; currently `None` — memberships fire at node
    /// construction, where the reduce frame stack isn't available, so the whole term isn't reconstructed.)
    Membership {
        mb_id: u32,
        depth: u32,
        subject: DagId,
        old_sort: SortId,
        new_sort: SortId,
        bindings: Vec<Option<DagId>>,
        whole: Option<DagId>,
    },
    /// Begin trying a conditional equation/membership against one matcher solution (a *trial*).
    /// `bindings` is the substitution so far (the lhs match; fresh `:=` variables are still `None`).
    TrialStart {
        kind: StmtKind,
        stmt_id: u32,
        depth: u32,
        bindings: Vec<Option<DagId>>,
    },
    /// End a trial: `success` iff the whole condition held. `kind` and `depth` repeat the associated
    /// [`TrialStart`](TraceEvent::TrialStart) values so rendering and pairing use identical keys.
    TrialEnd {
        kind: StmtKind,
        depth: u32,
        success: bool,
    },
    /// Begin condition fragment `index`; `first_attempt = false` marks a backtracking re-solve.
    FragmentStart {
        kind: StmtKind,
        stmt_id: u32,
        index: u32,
        depth: u32,
        first_attempt: bool,
    },
    /// End solving a condition fragment. On `success`, `bindings` is the substitution after the fragment
    /// (it may have bound fresh `:=` variables).
    FragmentEnd {
        kind: StmtKind,
        stmt_id: u32,
        index: u32,
        depth: u32,
        success: bool,
        bindings: Vec<Option<DagId>>,
    },
}

impl TraceEvent {
    /// The condition-nesting depth this event was recorded at (0 = top level). The REPL renders an
    /// event iff `depth == 0` or `set trace condition` is on.
    pub fn depth(&self) -> u32 {
        match self {
            TraceEvent::Rewrite { depth, .. }
            | TraceEvent::Membership { depth, .. }
            | TraceEvent::TrialStart { depth, .. }
            | TraceEvent::TrialEnd { depth, .. }
            | TraceEvent::FragmentStart { depth, .. }
            | TraceEvent::FragmentEnd { depth, .. } => *depth,
        }
    }

    /// Every DAG node id this event references (for GC rooting under in-reduction GC).
    fn for_each_id(&self, mut f: impl FnMut(DagId)) {
        let binds = |bs: &[Option<DagId>], f: &mut dyn FnMut(DagId)| {
            bs.iter().flatten().for_each(|&d| f(d))
        };
        match self {
            TraceEvent::Rewrite {
                redex,
                result,
                bindings,
                whole_before,
                whole_after,
                ..
            } => {
                f(*redex);
                f(*result);
                binds(bindings, &mut f);
                whole_before
                    .iter()
                    .chain(whole_after.iter())
                    .for_each(|&d| f(d));
            }
            TraceEvent::Membership {
                subject,
                bindings,
                whole,
                ..
            } => {
                f(*subject);
                binds(bindings, &mut f);
                whole.iter().for_each(|&d| f(d));
            }
            TraceEvent::TrialStart { bindings, .. } | TraceEvent::FragmentEnd { bindings, .. } => {
                binds(bindings, &mut f)
            }
            TraceEvent::TrialEnd { .. } | TraceEvent::FragmentStart { .. } => {}
        }
    }
}

/// What kind of rule produced a [`Rewrite`](TraceEvent::Rewrite) event.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RewriteKind {
    /// A user equation.
    Equation,
    /// A built-in (`special`) operator's reduction.
    BuiltIn,
    /// A successfully applied strict Rust reducer.
    HostFunction,
    /// A user rule (`rl`/`crl`), applied by rewriting or search.
    Rule,
}

/// Which statement table a trial / fragment / membership event refers to — selects the frontend
/// metadata (`eq_traces` vs `mb_traces`) the REPL looks `stmt_id` up in, and the `eqs`/`mbs` trace flag.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum StmtKind {
    /// A (conditional) equation.
    Equation,
    /// A (conditional) membership axiom.
    Membership,
    /// A (conditional) rule (`rl`/`crl`) — selects the frontend `rl_traces` metadata and the `rls`
    /// trace flag.
    Rule,
}

/// One completed model-check operation's deterministic statistics. The kernel records typed data;
/// the REPL's verbose path owns presentation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ModelCheckStats {
    pub property_automaton_states: usize,
    pub examined_system_states: usize,
}

/// One completed LTL satisfiability operation's deterministic automaton statistics.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SatSolveStats {
    pub generalized_buchi_states: usize,
    pub fairness_sets: usize,
}

struct RootedDag {
    node: DagId,
    _root: RootGuard,
}

struct ERewriteObject {
    name: DagId,
    object: Option<DagId>,
    messages: Vec<DagId>,
    next_message: usize,
    incoming_drained: bool,
}

/// Resumable state for one object-message scheduler pass. Every stored DAG is reachable either from
/// `_roots` or from the parent rewriting session's current root.
pub(crate) struct ERewritePass {
    config_symbol: SymbolId,
    portal_seen: bool,
    objects: Vec<ERewriteObject>,
    next_object: usize,
    remainder: Vec<(DagId, u32)>,
    progress: bool,
    awaiting_external: bool,
    _roots: Vec<RootGuard>,
}

pub(crate) enum ERewritePassStep {
    Complete { term: DagId, progress: bool },
    External { target: DagId, message: DagId },
}

#[derive(Clone, Copy)]
pub(crate) struct SemanticCheckpoint {
    rewrite_count: u64,
    membership_count: u64,
    rule_rewrite_count: u64,
    variant_narrowing_count: u64,
    narrowing_count: u64,
    model_check_stats_len: usize,
    sat_solve_stats_len: usize,
    trace_len: Option<usize>,
}

/// The mutable half of the engine: the garbage-collected DAG arena, the GC root registry, and the
/// rewrite statistics. Operations that consult the signature (sorts/symbols/equations) take a
/// `&Signature`; everything else is pure arena work.
#[derive(Default)]
pub(crate) struct Runtime {
    dags: Arena<DagNode>,
    /// Name-token ranks of pseudo-variable constants realized for non-ground command subjects.
    /// Same-sort variables order by name code. Empty unless a non-ground subject was built, so the
    /// ground hot path pays one `is_empty` check.
    var_ranks: HashMap<SymbolId, u32>,
    /// Relative first-ascent ranks for quoted identifiers synthesized by META-level output. Each
    /// complete payload (for example `X:Foo`) is interned lazily; the source variable's bare token
    /// code gives the wrong order when fresh and rule variables share a reflected substitution.
    qid_ranks: HashMap<String, u32>,
    /// Relative creation ranks of per-sort variable symbols. Original command variables are parsed
    /// before their final theory-normalized slots are known, so the unification driver records the
    /// parser-equivalent first-demand order explicitly. Unranked mid-solve symbols use `SymbolId`.
    sort_var_ranks: HashMap<SymbolId, u32>,
    /// Kind/error metadata for per-sort variable symbols. Within one kind, real-sort variables
    /// precede the synthesized kind-error variable even if an earlier command created the error
    /// symbol first.
    sort_var_meta: HashMap<SymbolId, (KindId, bool)>,
    /// Per-identity cached normalized DAG. Values are engine-lifetime GC roots and are stamped
    /// reduced when handed to a collapse binding.
    identity_dags: HashMap<IdentityId, DagId>,
    /// Guards identity materialization against recursively identity-bearing terms.
    identity_building: HashSet<IdentityId>,
    /// Aggregate command count. The categories below are subcounts; equational rewrites are the remainder.
    pub(crate) rewrite_count: u64,
    membership_count: u64,
    rule_rewrite_count: u64,
    variant_narrowing_count: u64,
    narrowing_count: u64,
    /// Completed model-check statistics waiting for the command layer to consume them.
    model_check_stats: Vec<ModelCheckStats>,
    /// Completed satisfiability statistics waiting for the command layer to consume them.
    sat_solve_stats: Vec<SatSolveStats>,
    /// Next value of each `CounterSymbol` operator, keyed by symbol; an absent entry means 0. A
    /// rule-style counter redex yields its own operator's value and increments it, so distinct counter
    /// operators (two declared directly, or a renamed copy of `counter`) have independent sequences.
    /// Cleared at the start of each top-level rewriting command except `continue`; inert under
    /// equational `reduce`.
    ///
    /// Not part of [`SemanticCheckpoint`]: only the [`Rewriting`] drives fire counters
    /// ([`try_counter`](Self::try_counter) is reached from `rewrite_step` and `frewrite_pass` alone),
    /// and they snapshot and restore this map themselves on a reducer fault
    /// ([`Engine::counter_snapshot`]). Any other caller of `try_counter` must do the same.
    pub(crate) counter_values: HashMap<SymbolId, u64>,
    /// When `Some`, [`reduce`](Engine::reduce) records a structured [`TraceEvent`] stream here (opt-in
    /// via [`Engine::set_trace`]); `None` (the default) is zero-cost. Holds intermediate node ids, so it
    /// is rooted by [`safe_point_gc`](Self::safe_point_gc) — but it is meant for the REPL, which runs
    /// with in-reduction GC off.
    trace: Option<Vec<TraceEvent>>,
    /// Current condition-fragment nesting depth: 0 at top level, incremented around each condition
    /// fragment's re-entrant reduction (so events recorded inside a condition are tagged `depth >= 1`).
    /// Always maintained (a cheap `u32`), but only consulted when `trace` is `Some`.
    condition_depth: u32,
    /// Whether to reconstruct the whole root term at each rewrite (`set trace whole`). Off by default
    /// (the reconstruction allocates O(depth) nodes per rewrite, so it is gated). Only acts when tracing.
    record_whole: bool,
    /// Persistent GC roots held by live [`RootGuard`]s. `gc` always marks
    /// from here; the shared `Rc<RefCell<…>>` lets a guard outlive a `&mut self` call.
    roots: Roots,
    /// If `Some(n)`, [`reduce`](Engine::reduce) collects at its loop head once this many DAG nodes
    /// have been allocated since the last collection — letting one large reduction run in bounded
    /// memory. `None` (default) disables in-reduction GC (callers collect between reductions).
    gc_interval: Option<u64>,
    /// DAG nodes allocated since the last collection (drives `gc_interval`).
    allocs_since_gc: u64,
    /// Engine-global roots protecting an outer reduction across re-entrant condition reduction.
    /// Nested collection sees its own frames, so condition solving temporarily adds the outer frames,
    /// match bindings, and redex here. This remains empty when in-reduction GC is disabled.
    protected: Vec<DagId>,
    /// Construction-scoped structural deduplication. While present, allocation reuses an equal
    /// [`NodeTerm`]. Windows never span a GC safe point, so the memo cannot retain stale handles.
    dedup: Option<HashMap<NodeTerm, DagId>>,
    /// Captured `stdout` / `stderr` writes from `erewrite` stream managers, surfaced by the REPL and
    /// reset per `erewrite` command via [`reset_external`](Engine::reset_external).
    external_out: String,
    external_err: String,
    /// Buffered, rooted replies from external managers. The next `erewrite` pass delivers them into
    /// the soup; they remain live across suspended parent work.
    incoming: Vec<RootedDag>,
    /// Capability registry for host-owned external targets. The rooted target DAGs persist across
    /// commands until the host explicitly unregisters the corresponding opaque token.
    external_targets: HashMap<u64, RootedDag>,
    next_external_target: u64,
    /// Pending scripted `stdin` bytes for `getLine`. A call consumes through the next `\n` (inclusive),
    /// or the remainder when no newline exists; an empty buffer is EOF. The REPL preserves unread input
    /// across commands.
    pub(crate) external_in: String,
    /// Fault captured across an infallible theory-construction seam (notably lazy identity DAGs).
    /// The enclosing fallible semantic driver consumes it before reporting success.
    reducer_fault: Option<ReducerFault>,
}

#[derive(Default)]
pub struct Engine {
    sig: Signature,
    rt: Runtime,
}

impl Default for Signature {
    fn default() -> Self {
        Signature {
            sorts: Sorts::default(),
            symbols: Arena::default(),
            identities: Arena::default(),
            equations: HashMap::default(),
            memberships: Vec::default(),
            membership_index: HashMap::default(),
            collapsing_memberships: HashMap::default(),
            rules: HashMap::default(),
            smt_rules: HashMap::default(),
            smt_rules_valid: true,
            narrowing_rules: Vec::default(),
            eq_epoch: 1, // 0 is the "never reduced" sentinel stored on nodes
            next_eq_id: 0,
            next_mb_id: 0,
            next_rule_id: 0,
            qid_class: QidClass::default(),
            smt_info: SmtInfo::default(),
            var_symbols: HashMap::default(),
            succ_zeros: HashMap::default(),
            minimum_substitution_size: 1,
            collapse_patterns: Vec::default(),
            substitution_layout_estimates: Vec::default(),
            host_functions: HostFunctionCatalog::default(),
            host_bindings: Vec::default(),
            host_bindings_sealed: Cell::new(false),
        }
    }
}

/// Detect a repeated compound rhs subterm. Variables are excluded because repeated occurrences already
/// share their substitution binding. A false positive only enables an idempotent deduplication window.
fn term_has_repeated_subterm(t: &Term) -> bool {
    let mut seen: HashSet<&Term> = HashSet::new();
    let mut stack = vec![t];
    while let Some(cur) = stack.pop() {
        match cur {
            Term::Op { args, .. } => {
                if !seen.insert(cur) {
                    return true; // this compound subterm was already seen elsewhere — a real duplicate
                }
                stack.extend(args.iter());
            }
            Term::Iter { arg, .. } => {
                if !seen.insert(cur) {
                    return true;
                }
                stack.push(arg);
            }
            Term::Var(_) | Term::Na { .. } => {}
        }
    }
    false
}

/// Textually equal, non-ground compound terms available for left-to-right equation sharing. The LHS
/// root is excluded; variables already share through substitution.
fn lhs_rhs_shared_subterms(lhs: &Term, rhs: &Term) -> Vec<Term> {
    fn has_variable(term: &Term) -> bool {
        match term {
            Term::Var(_) => true,
            Term::Op { args, .. } => args.iter().any(has_variable),
            Term::Iter { arg, .. } => has_variable(arg),
            Term::Na { .. } => false,
        }
    }

    fn push_children<'a>(term: &'a Term, stack: &mut Vec<&'a Term>) {
        match term {
            Term::Op { args, .. } => stack.extend(args),
            Term::Iter { arg, .. } => stack.push(arg),
            Term::Var(_) | Term::Na { .. } => {}
        }
    }

    let mut available: HashSet<&Term> = HashSet::new();
    let mut stack = Vec::new();
    push_children(lhs, &mut stack);
    while let Some(term) = stack.pop() {
        if matches!(term, Term::Op { .. } | Term::Iter { .. }) && has_variable(term) {
            available.insert(term);
        }
        push_children(term, &mut stack);
    }

    let mut shared = Vec::new();
    stack.push(rhs);
    while let Some(term) = stack.pop() {
        if available.contains(term) && !shared.iter().any(|prior| prior == term) {
            shared.push(term.clone());
        }
        push_children(term, &mut stack);
    }
    shared
}

// ======================================================================================
// Signature: sorts, symbols, equations (immutable during a reduction)
// ======================================================================================

impl Signature {
    pub(crate) fn add_sort(&mut self, name: impl Into<String>) -> SortId {
        self.sorts.add_sort(name)
    }
    pub(crate) fn add_subsort(&mut self, sub: SortId, sup: SortId) {
        self.sorts.add_subsort(sub, sup);
    }
    pub(crate) fn close_sorts(&mut self) {
        self.sorts.close();
    }
    pub(crate) fn sorts(&self) -> &Sorts {
        &self.sorts
    }
    pub(crate) fn smt_info(&self) -> &SmtInfo {
        &self.smt_info
    }
    /// Iterate every symbol (id + data). Used by the order-sorted-unification `SortBdds` to size
    /// its domain-bit block to the widest operator in the module.
    pub(crate) fn symbols_iter(&self) -> impl Iterator<Item = (SymbolId, &Symbol)> + '_ {
        self.symbols.iter()
    }
    pub(crate) fn succ_zero(&self, succ: SymbolId) -> Option<SymbolId> {
        self.succ_zeros.get(&succ).copied()
    }

    fn note_substitution_layout(
        &mut self,
        lhs: &Term,
        nr_vars: u32,
        built_term: Option<&Term>,
        condition: &[ConditionFragment],
    ) {
        let construction = built_term.map_or(0, term_construction_slots).max(
            condition
                .iter()
                .map(fragment_construction_slots)
                .max()
                .unwrap_or(0),
        );
        let mut abstraction_candidates = Vec::new();
        self.collect_abstraction_candidates(lhs, &mut abstraction_candidates);
        self.substitution_layout_estimates
            .push(SubstitutionLayoutEstimate {
                base: nr_vars as usize + construction,
                abstraction_candidates,
            });
        self.recompute_minimum_substitution_size();
    }

    /// Recursively retain each immediate non-variable alien beneath a non-free theory node.
    /// [`recompute_minimum_substitution_size`](Self::recompute_minimum_substitution_size) decides
    /// whether each candidate needs protection from equation-derived collapse shapes.
    fn collect_abstraction_candidates(&self, term: &Term, out: &mut Vec<LayoutAlien>) {
        match term {
            Term::Op { symbol, args } => {
                if self.symbol(*symbol).theory() != Theory::Free {
                    for arg in args {
                        if !matches!(arg, Term::Var(_))
                            && arg.top_symbol().is_some_and(|alien| alien != *symbol)
                        {
                            out.push(LayoutAlien {
                                parent: *symbol,
                                term: arg.clone(),
                            });
                        }
                    }
                }
                for arg in args {
                    self.collect_abstraction_candidates(arg, out);
                }
            }
            Term::Iter { symbol, arg, .. } => {
                if !matches!(arg.as_ref(), Term::Var(_))
                    && arg.top_symbol().is_some_and(|alien| alien != *symbol)
                {
                    out.push(LayoutAlien {
                        parent: *symbol,
                        term: arg.as_ref().clone(),
                    });
                }
                self.collect_abstraction_candidates(arg, out);
            }
            Term::Var(_) | Term::Na { .. } => {}
        }
    }

    /// Record a collapse relation in the orientation used by symbolic alien matching. A bare-variable
    /// RHS means the original LHS can collapse to any root. Otherwise, when both sides contain the
    /// same variables, the RHS is a reversible equation pattern that can expose the LHS top symbol.
    fn note_collapse_pattern(&mut self, lhs: &Term, rhs: &Term) {
        let lhs_top = lhs
            .top_symbol()
            .expect("equation lhs must be an application");
        if matches!(rhs, Term::Var(_)) {
            self.collapse_patterns.push(CollapsePattern {
                pattern: lhs.clone(),
                target: None,
            });
        } else if term_variable_indices(lhs) == term_variable_indices(rhs) {
            self.collapse_patterns.push(CollapsePattern {
                pattern: rhs.clone(),
                target: Some(lhs_top),
            });
        }
    }

    fn recompute_minimum_substitution_size(&mut self) {
        let estimated = self
            .substitution_layout_estimates
            .iter()
            .map(|estimate| {
                let protected = estimate
                    .abstraction_candidates
                    .iter()
                    .filter(|alien| {
                        self.collapse_patterns.iter().any(|collapse| {
                            collapse.target.is_none_or(|target| target == alien.parent)
                                && term_matches_pattern(&collapse.pattern, &alien.term)
                        })
                    })
                    .count();
                estimate.base + protected
            })
            .max()
            .unwrap_or(1);
        self.minimum_substitution_size = estimated.max(1);
    }

    fn constant_identity(&mut self, symbol: SymbolId) -> IdentityId {
        let sort = self.symbols.get(symbol).decls()[0].range;
        self.identities.alloc(Identity {
            term: Some(Term::constant(symbol)),
            sort,
        })
    }

    fn reserve_identity(&mut self, sort: SortId) -> IdentityId {
        self.identities.alloc(Identity { term: None, sort })
    }

    pub(crate) fn identity_term(&self, id: IdentityId) -> &Term {
        self.identities
            .get(id)
            .term
            .as_ref()
            .expect("identity term not installed")
    }

    pub(crate) fn identity_sort(&self, id: IdentityId) -> SortId {
        self.identities.get(id).sort
    }

    pub(crate) fn identity_constant(&self, id: IdentityId) -> Option<SymbolId> {
        match self.identity_term(id) {
            Term::Op { symbol, args } if args.is_empty() => Some(*symbol),
            _ => None,
        }
    }

    fn term_sort(&self, term: &Term) -> SortId {
        match term {
            Term::Var(v) => v.sort,
            Term::Na { symbol, value } => self.compute_na_sort(*symbol, value),
            Term::Iter { symbol, count, arg } => {
                self.compute_s_sort(*symbol, self.term_sort(arg), count)
            }
            Term::Op { symbol, args } if args.is_empty() => {
                let declarations = self.symbol(*symbol).decls();
                declarations
                    .iter()
                    .find(|candidate| {
                        declarations
                            .iter()
                            .all(|other| self.sorts.leq(candidate.range, other.range))
                    })
                    .unwrap_or(&declarations[0])
                    .range
            }
            Term::Op { symbol, args } => {
                let arg_sorts: Vec<SortId> = args.iter().map(|arg| self.term_sort(arg)).collect();
                if matches!(self.symbol(*symbol).theory(), Theory::Acu | Theory::Au) {
                    // The parser and META down-translation flatten associative applications, so a
                    // binary declaration may legitimately own three or more `Term` children.
                    self.compute_sort_fold(*symbol, &arg_sorts)
                } else {
                    self.compute_sort(*symbol, &arg_sorts)
                }
            }
        }
    }

    pub(crate) fn add_op(
        &mut self,
        name: impl Into<String>,
        domain: Vec<SortId>,
        range: SortId,
    ) -> SymbolId {
        self.symbols.alloc(Symbol {
            name: name.into(),
            decls: vec![OpDeclaration {
                domain,
                range,
                ctor: false,
            }],
            axioms: Axioms::default(),
            inconsistent_constructor_axioms: false,
            identity: None,
            one_sided_id: None,
            strategy: None,
            strict_eager_source_strategy: true,
            frozen: None,
            special: None,
            oo: OoFlags::default(),
            class: SymbolClass::default(),
        })
    }

    /// Register a binary ACU operator, optionally with a two-sided identity. Applications are stored as
    /// flattened multisets and matched modulo associativity, commutativity, and identity.
    pub(crate) fn add_op_ac(
        &mut self,
        name: impl Into<String>,
        domain: Vec<SortId>,
        range: SortId,
        identity: Option<SymbolId>,
    ) -> SymbolId {
        assert_eq!(domain.len(), 2, "an `assoc comm` operator must be binary");
        let identity = identity.map(|s| self.constant_identity(s));
        let id = self.symbols.alloc(Symbol {
            name: name.into(),
            decls: vec![OpDeclaration {
                domain,
                range,
                ctor: false,
            }],
            axioms: Axioms {
                assoc: true,
                comm: true,
                idem: false,
                iter: false,
            },
            inconsistent_constructor_axioms: false,
            identity,
            one_sided_id: None,
            strategy: None,
            strict_eager_source_strategy: true,
            frozen: None,
            special: None,
            oo: OoFlags::default(),
            class: SymbolClass::default(),
        });
        self.commutative_sort_completion(id);
        id
    }

    /// Register an **AU** operator (`assoc`, not commutative, optionally with a two-sided `id:`). Must
    /// be binary; its arguments are stored as a flattened ordered sequence and matched modulo
    /// associativity (with extension).
    pub(crate) fn add_op_au(
        &mut self,
        name: impl Into<String>,
        domain: Vec<SortId>,
        range: SortId,
        identity: Option<SymbolId>,
    ) -> SymbolId {
        assert_eq!(domain.len(), 2, "an `assoc` operator must be binary");
        let identity = identity.map(|s| self.constant_identity(s));
        self.symbols.alloc(Symbol {
            name: name.into(),
            decls: vec![OpDeclaration {
                domain,
                range,
                ctor: false,
            }],
            axioms: Axioms {
                assoc: true,
                comm: false,
                idem: false,
                iter: false,
            },
            inconsistent_constructor_axioms: false,
            identity,
            one_sided_id: None,
            strategy: None,
            strict_eager_source_strategy: true,
            frozen: None,
            special: None,
            oo: OoFlags::default(),
            class: SymbolClass::default(),
        })
    }

    /// Register a **CUI** operator (`comm`, not associative, optionally `idem` and/or `id:`). Must be
    /// binary; its two arguments are stored in canonical order and matched modulo commutativity
    /// (idempotence and identity collapse `f(a,a)`/`f(a,e)` to a single element at construction).
    pub(crate) fn add_op_cui(
        &mut self,
        name: impl Into<String>,
        domain: Vec<SortId>,
        range: SortId,
        comm: bool,
        idem: bool,
        identity: Option<SymbolId>,
    ) -> SymbolId {
        assert_eq!(domain.len(), 2, "a CUI operator must be binary");
        let identity = identity.map(|s| self.constant_identity(s));
        let id = self.symbols.alloc(Symbol {
            name: name.into(),
            decls: vec![OpDeclaration {
                domain,
                range,
                ctor: false,
            }],
            axioms: Axioms {
                assoc: false,
                comm,
                idem,
                iter: false,
            },
            inconsistent_constructor_axioms: false,
            identity,
            one_sided_id: None,
            strategy: None,
            strict_eager_source_strategy: true,
            frozen: None,
            special: None,
            oo: OoFlags::default(),
            class: SymbolClass::default(),
        });
        self.commutative_sort_completion(id);
        id
    }

    /// Register a unary `iter` successor. Nodes store a compact iteration count and match modulo
    /// successor extension.
    pub(crate) fn add_op_iter(
        &mut self,
        name: impl Into<String>,
        domain: Vec<SortId>,
        range: SortId,
    ) -> SymbolId {
        assert_eq!(domain.len(), 1, "an `iter` operator must be unary");
        self.symbols.alloc(Symbol {
            name: name.into(),
            decls: vec![OpDeclaration {
                domain,
                range,
                ctor: false,
            }],
            axioms: Axioms {
                iter: true,
                ..Default::default()
            },
            inconsistent_constructor_axioms: false,
            identity: None,
            one_sided_id: None,
            strategy: None,
            strict_eager_source_strategy: true,
            frozen: None,
            special: None,
            oo: OoFlags::default(),
            class: SymbolClass::default(),
        })
    }
    /// Whether any unconditional or conditional equation is indexed at `s`, used by the
    /// decompose-equality stability test.
    pub(crate) fn has_equations(&self, s: SymbolId) -> bool {
        self.equations.get(&s).is_some_and(|v| !v.is_empty())
    }

    pub(crate) fn symbol(&self, id: SymbolId) -> &Symbol {
        self.symbols.get(id)
    }
    pub(crate) fn host_symbol(&self, id: SymbolId) -> Option<&Symbol> {
        self.symbols.try_get(id)
    }

    /// Resolve an operator by canonical name and arity for metalevel construction. Overloads sharing
    /// that pair are folded into one symbol; absent declarations return `None`.
    pub(crate) fn resolve_symbol(&self, name: &str, arity: usize) -> Option<SymbolId> {
        self.symbols
            .iter()
            .find(|(_, s)| s.arity() == arity && s.name() == name)
            .map(|(id, _)| id)
    }

    /// The kind of `id`'s first declaration's range.
    pub(crate) fn symbol_range_kind(&self, id: SymbolId) -> KindId {
        self.sorts.kind_of(self.symbols.get(id).decls[0].range)
    }

    /// Attach an additional declaration to an existing operator (ad-hoc / subsort overloading). All
    /// declarations must agree on arity. Least-sort resolution walks them in insertion order, so the
    /// first `add_op*` declaration wins an incomparable tie. Call this before building any node of
    /// `sym`, because construction caches sorts. The frontend uses this while building signatures;
    /// programmatic clients may call it directly.
    pub(crate) fn add_op_decl(&mut self, sym: SymbolId, domain: Vec<SortId>, range: SortId) {
        self.add_op_decl_with_ctor(sym, domain, range, false);
    }

    pub(crate) fn add_op_decl_with_ctor(
        &mut self,
        sym: SymbolId,
        domain: Vec<SortId>,
        range: SortId,
        ctor: bool,
    ) {
        assert!(
            !matches!(
                self.symbols.get(sym).special,
                Some(SpecialOp::HostFunction(_))
            ),
            "a strict host operator's overload profile is sealed at binding"
        );
        {
            let s = self.symbols.get_mut(sym);
            assert_eq!(
                s.decls[0].domain.len(),
                domain.len(),
                "overloaded declarations of `{}` must agree on arity",
                s.name()
            );
            s.decls.push(OpDeclaration {
                domain,
                range,
                ctor,
            });
        }
        // Keep a commutative operator's declaration set complete under argument swap (no-op for free
        // and AU operators, whose declarations stay positional).
        self.commutative_sort_completion(sym);
    }

    pub(crate) fn mark_inconsistent_constructor_axioms(&mut self, sym: SymbolId) {
        self.symbols.get_mut(sym).inconsistent_constructor_axioms = true;
    }

    /// Complete a commutative operator's declaration set: every asymmetric declaration
    /// `[a, b] -> r` also receives `[b, a] -> r` with the same range and constructor flag, unless
    /// that declaration already exists.
    ///
    /// [`compute_sort`](Self::compute_sort) checks declarations positionally while ACU and CUI nodes
    /// canonicalize their arguments. Completing both positions makes least-sort selection independent
    /// of canonical argument order. Without the swapped declaration, an overload such as
    /// `_+_ : NzNat Nat -> NzNat` could type `z + nz` as `Nat` instead of `NzNat`. Completion is
    /// idempotent and runs after each declaration is registered. AU and free operators are unchanged
    /// because their argument order is significant.
    fn commutative_sort_completion(&mut self, sym: SymbolId) {
        let s = self.symbols.get(sym);
        if !matches!(s.theory(), Theory::Acu | Theory::Cui) || !s.axioms.comm {
            return; // only genuinely commutative ops complete; AU / free / non-comm CUI
            // (id:/idem-only) stay positional
        }
        // Snapshot the current declarations so the shared borrow ends before the mutable push below
        // (the sort ids are `Copy`, so this clone is cheap and small).
        let decls: Vec<OpDeclaration> = s.decls.clone();
        let mut to_add: Vec<OpDeclaration> = Vec::new();
        for d in &decls {
            if d.domain.len() != 2 || d.domain[0] == d.domain[1] {
                continue; // a symmetric (or non-binary) declaration is its own swap
            }
            let swapped = vec![d.domain[1], d.domain[0]];
            let present = decls
                .iter()
                .chain(to_add.iter())
                .any(|e| e.domain == swapped && e.range == d.range && e.ctor == d.ctor);
            if !present {
                to_add.push(OpDeclaration {
                    domain: swapped,
                    range: d.range,
                    ctor: d.ctor,
                });
            }
        }
        self.symbols.get_mut(sym).decls.extend(to_add);
    }

    /// Mark every declaration of `sym` as a constructor (`[ctor]`). This does not change reduction;
    /// constructor-sensitive symbolic analyses consume the metadata.
    pub(crate) fn set_ctor(&mut self, sym: SymbolId) {
        for decl in &mut self.symbols.get_mut(sym).decls {
            decl.ctor = true;
        }
    }

    /// Install and normalize an operator evaluation strategy.
    ///
    /// Source positions are one-based and zero means top. Duplicate positions and adjacent zeroes are
    /// discarded, a missing final zero is appended, and an empty list selects the standard strategy.
    /// Associative symbols classify as eager, lazy, or semi-eager.
    pub(crate) fn set_strategy(&mut self, sym: SymbolId, raw: &[u32]) {
        assert!(
            !matches!(
                self.symbols.get(sym).special,
                Some(SpecialOp::HostFunction(_))
            ),
            "a strict host operator's strategy is sealed at binding"
        );
        let symbol = self.symbols.get(sym);
        let arity = symbol.arity();
        assert!(
            raw.iter().all(|&p| p as usize <= arity),
            "evaluation strategy {raw:?} for `{}` references an argument outside 0..={arity}",
            symbol.name()
        );
        let strict_eager_source_strategy = if raw.is_empty() {
            true
        } else {
            let arguments = if raw.last() == Some(&0) {
                &raw[..raw.len() - 1]
            } else {
                raw
            };
            arguments.len() == arity
                && arguments
                    .iter()
                    .enumerate()
                    .all(|(position, &step)| step as usize == position + 1)
        };

        let strategy = if raw.is_empty() {
            None
        } else if matches!(symbol.theory(), Theory::Acu | Theory::Au) {
            // Flattened associative applications cannot distinguish the two declared positions.
            // Arguments before the first top imply eager; after top imply semi-eager; none imply lazy.
            let mut seen_top = false;
            let mut classified = None;
            for &step in raw {
                if step == 0 {
                    seen_top = true;
                } else {
                    classified = Some(seen_top);
                    break;
                }
            }
            match classified {
                Some(false) => None,
                Some(true) => Some(EvalStrategy::PermutativeSemiEager),
                None => Some(EvalStrategy::Sequence(vec![EvalStep::Top])),
            }
        } else {
            let mut steps = Vec::with_capacity(raw.len() + 1);
            let mut evaluated = vec![false; arity];
            let mut last_was_top = false;
            for &step in raw {
                if step == 0 {
                    if !last_was_top {
                        steps.push(EvalStep::Top);
                        last_was_top = true;
                    }
                } else {
                    let position = (step - 1) as usize;
                    if !evaluated[position] {
                        steps.push(EvalStep::Argument(position as u32));
                        evaluated[position] = true;
                        last_was_top = false;
                    }
                }
            }
            if !last_was_top {
                steps.push(EvalStep::Top);
            }
            let standard = steps.len() == arity + 1
                && steps[..arity]
                    .iter()
                    .enumerate()
                    .all(|(position, step)| *step == EvalStep::Argument(position as u32))
                && steps[arity] == EvalStep::Top;
            (!standard).then_some(EvalStrategy::Sequence(steps))
        };
        let symbol = self.symbols.get_mut(sym);
        symbol.strategy = strategy;
        symbol.strict_eager_source_strategy = strict_eager_source_strategy;
    }

    /// Mark the frozen arguments of `sym` (`frozen` / `frozen (…)`). `raw` contains the 1-based source
    /// positions — empty for bare `[frozen]` (all arguments) — and is stored 0-based.
    ///
    /// Invalid positions and bare `frozen` on a constant leave the symbol unchanged and return false;
    /// the frontend owns diagnostics.
    #[must_use]
    pub(crate) fn set_frozen(&mut self, sym: SymbolId, raw: &[u32]) -> bool {
        let arity = self.symbols.get(sym).arity();
        if (arity == 0 && raw.is_empty())
            || raw
                .iter()
                .any(|&position| position == 0 || position as usize > arity)
        {
            return false;
        }
        self.symbols.get_mut(sym).frozen = Some(raw.iter().map(|&position| position - 1).collect());
        true
    }

    /// Set the object-system role flags (`config`/`obj`/`msg`/`portal`) on `sym`. Ordinary rewrite modes
    /// treat them as metadata; the `erewrite` object-message scheduler consumes them.
    pub(crate) fn set_oo_flags(&mut self, sym: SymbolId, oo: OoFlags) {
        self.symbols.get_mut(sym).oo = oo;
    }
    fn validate_host_function(
        &self,
        sym: SymbolId,
        key: &str,
        hooks: &ResolvedHostHooks,
    ) -> Result<(HostFunctionId, usize), HostBindingError> {
        if self.host_bindings_sealed.get() {
            return Err(HostBindingError::SignatureSealed);
        }
        let key = HostFunctionKey::parse(key)
            .map_err(|error| HostBindingError::InvalidKey(error.to_string()))?;
        let function = self
            .host_functions
            .resolve(&key)
            .ok_or_else(|| HostBindingError::MissingCapability(key.clone()))?;

        if let Some(special) = self.symbols.get(sym).special() {
            return match special {
                SpecialOp::HostFunction(_) => Err(HostBindingError::DuplicateBinding),
                _ => Err(HostBindingError::InvalidOperator(format!(
                    "operator `{}` already has a non-host special attachment",
                    self.symbols.get(sym).name()
                ))),
            };
        }

        let descriptor = self.host_functions.descriptor(function);
        let symbol = self.symbols.get(sym);
        if symbol.theory() != Theory::Free {
            return Err(HostBindingError::InvalidOperator(format!(
                "strict host operator `{}` must use the free root theory",
                symbol.name()
            )));
        }
        if !symbol.strict_eager_source_strategy {
            return Err(HostBindingError::InvalidOperator(format!(
                "strict host operator `{}` must use the standard eager strategy without repeated \
                 or incremental steps",
                symbol.name()
            )));
        }
        if symbol.has_inconsistent_constructor_axioms() {
            return Err(HostBindingError::IncompatibleDeclarations(format!(
                "strict host operator `{}` has inconsistent structural declarations",
                symbol.name()
            )));
        }
        if symbol.arity() != descriptor.arity() {
            return Err(HostBindingError::InvalidOperator(format!(
                "strict host operator `{}` has arity {}, but `{key}` requires {}",
                symbol.name(),
                symbol.arity(),
                descriptor.arity()
            )));
        }

        let declarations = symbol.decls();
        let result_kind = self.sorts.kind_of(declarations[0].range);
        if declarations
            .iter()
            .any(|declaration| self.sorts.kind_of(declaration.range) != result_kind)
        {
            return Err(HostBindingError::IncompatibleDeclarations(format!(
                "strict host operator `{}` has declarations in different result kinds",
                symbol.name()
            )));
        }
        for (index, left) in declarations.iter().enumerate() {
            for right in &declarations[index + 1..] {
                let domains_overlap =
                    left.domain
                        .iter()
                        .zip(&right.domain)
                        .all(|(&left_sort, &right_sort)| {
                            if !self.sorts.same_kind(left_sort, right_sort) {
                                return false;
                            }
                            self.sorts
                                .kind(self.sorts.kind_of(left_sort))
                                .members
                                .iter()
                                .copied()
                                .any(|actual| {
                                    self.sorts.leq(actual, left_sort)
                                        && self.sorts.leq(actual, right_sort)
                                })
                        });
                if domains_overlap
                    && !self.sorts.leq(left.range, right.range)
                    && !self.sorts.leq(right.range, left.range)
                {
                    return Err(HostBindingError::IncompatibleDeclarations(format!(
                        "strict host operator `{}` has overlapping declarations with incomparable \
                         result sorts `{}` and `{}`",
                        symbol.name(),
                        self.sorts.name(left.range),
                        self.sorts.name(right.range)
                    )));
                }
            }
        }

        let required_ops: HashSet<&str> = descriptor
            .required_op_hooks()
            .iter()
            .map(|requirement| requirement.purpose())
            .collect();
        let required_terms: HashSet<&str> = descriptor
            .required_term_hooks()
            .iter()
            .map(|requirement| requirement.purpose())
            .collect();
        for purpose in hooks.op_purposes() {
            if !required_ops.contains(purpose) {
                return Err(HostBindingError::UnexpectedHook(purpose.to_string()));
            }
        }
        for purpose in hooks.term_purposes() {
            if !required_terms.contains(purpose) {
                return Err(HostBindingError::UnexpectedHook(purpose.to_string()));
            }
        }

        let contract_sort = |declaration: &OpDeclaration, sort: HookSort| match sort {
            HookSort::Argument(position) => declaration.domain[position],
            HookSort::Result => declaration.range,
        };
        for requirement in descriptor.required_op_hooks() {
            let hook_id = hooks
                .get_op(requirement.purpose())
                .ok_or_else(|| HostBindingError::MissingHook(requirement.purpose().to_string()))?;
            let hook = self.host_symbol(hook_id).ok_or_else(|| {
                HostBindingError::InvalidHook(format!(
                    "op-hook `{}` does not belong to this signature",
                    requirement.purpose()
                ))
            })?;
            if hook.arity() != requirement.domain().len() {
                return Err(HostBindingError::InvalidHook(format!(
                    "op-hook `{}` requires arity {}, found {}",
                    requirement.purpose(),
                    requirement.domain().len(),
                    hook.arity()
                )));
            }
            for declaration in symbol.decls() {
                let compatible = hook.decls().iter().any(|hook_declaration| {
                    requirement
                        .domain()
                        .iter()
                        .copied()
                        .zip(&hook_declaration.domain)
                        .all(|(expected, &actual)| {
                            self.sorts
                                .same_kind(contract_sort(declaration, expected), actual)
                        })
                        && requirement.range_constraints().all(|expected| {
                            self.sorts.same_kind(
                                contract_sort(declaration, expected),
                                hook_declaration.range,
                            )
                        })
                });
                if !compatible {
                    return Err(HostBindingError::InvalidHook(format!(
                        "op-hook `{}` has no profile compatible with `{}`",
                        requirement.purpose(),
                        symbol.name()
                    )));
                }
            }
        }
        for requirement in descriptor.required_term_hooks() {
            let hook_id = hooks
                .get_term(requirement.purpose())
                .ok_or_else(|| HostBindingError::MissingHook(requirement.purpose().to_string()))?;
            let hook = self.host_symbol(hook_id).ok_or_else(|| {
                HostBindingError::InvalidHook(format!(
                    "term-hook `{}` does not belong to this signature",
                    requirement.purpose()
                ))
            })?;
            if hook.arity() != 0 {
                return Err(HostBindingError::InvalidHook(format!(
                    "term-hook `{}` must resolve to a ground constant",
                    requirement.purpose()
                )));
            }
            for declaration in symbol.decls() {
                let expected = contract_sort(declaration, requirement.sort());
                if !hook
                    .decls()
                    .iter()
                    .any(|hook_declaration| self.sorts.same_kind(expected, hook_declaration.range))
                {
                    return Err(HostBindingError::InvalidHook(format!(
                        "term-hook `{}` has no sort compatible with `{}`",
                        requirement.purpose(),
                        symbol.name()
                    )));
                }
            }
        }

        Ok((function, descriptor.arity()))
    }

    fn bind_host_function(
        &mut self,
        sym: SymbolId,
        key: &str,
        hooks: ResolvedHostHooks,
    ) -> Result<HostBindingId, HostBindingError> {
        let (function, arity) = self.validate_host_function(sym, key, &hooks)?;
        let binding = HostBindingId::from_index(self.host_bindings.len());
        self.host_bindings.push(ResolvedHostBinding {
            function,
            hooks,
            arity,
        });
        // Host attachment changes normal forms just like a new equation. Invalidate every existing
        // reduced stamp before exposing the binding.
        self.eq_epoch += 1;
        self.symbols.get_mut(sym).special = Some(SpecialOp::HostFunction(binding));
        Ok(binding)
    }

    pub(crate) fn host_binding(&self, binding: HostBindingId) -> &ResolvedHostBinding {
        &self.host_bindings[binding.index()]
    }

    pub(crate) fn host_function_key(&self, binding: HostBindingId) -> &HostFunctionKey {
        self.host_functions
            .key(self.host_bindings[binding.index()].function)
    }

    pub(crate) fn mark_host_execution(&self) {
        self.host_bindings_sealed.set(true);
    }
    /// Every public symbolic operation is semantic execution, even before a first attachment exists.
    /// Module construction uses separate crate-private preparation seams.
    pub(crate) fn mark_symbolic_execution(&self) {
        self.mark_host_execution();
    }
    pub(crate) fn host_reducer(&self, binding: HostBindingId) -> &dyn crate::host::StrictReducer {
        self.host_functions
            .reducer(self.host_bindings[binding.index()].function)
    }

    /// Set a built-in reduction rule (`special (id-hook …)`) on `sym`. Hook references arrive already
    /// resolved to [`SymbolId`]s. Attaching [`SpecialOp::Branch`] also installs its intrinsic lazy
    /// evaluation strategy and synthetic branch-sort declarations.
    pub(crate) fn set_special(&mut self, sym: SymbolId, op: SpecialOp) {
        assert!(
            !matches!(
                self.symbols.get(sym).special,
                Some(SpecialOp::HostFunction(_))
            ),
            "a strict host binding cannot be replaced"
        );
        if let SpecialOp::Branch { .. } = op {
            // Branch attachment is idempotent because flattened imports can revisit the same symbol.
            // A user strategy is still invalid on the first attachment.
            if matches!(
                self.symbols.get(sym).special,
                Some(SpecialOp::Branch { .. })
            ) {
                return;
            }
            assert!(
                self.symbols.get(sym).strategy.is_none(),
                "`{}` is a Branch operator; its laziness is installed by the seam — it must not also \
                 carry a user strat",
                self.symbols.get(sym).name()
            );
            // A branch operator's result sort follows its branch arguments. Add one synthetic
            // condition-sort × branch-sortⁿ → branch-sort declaration per proper branch sort.
            let (arity, condition_sort, branch_sorts) = {
                let symbol = self.symbols.get(sym);
                let base = &symbol.decls()[0];
                let arity = base.domain.len();
                assert!(
                    arity >= 2,
                    "a Branch operator needs a condition and a branch"
                );
                let branch_kind = self.sorts.kind_of(base.domain[1]);
                debug_assert!(
                    base.domain[1..]
                        .iter()
                        .all(|&sort| self.sorts.kind_of(sort) == branch_kind),
                    "all Branch arguments must belong to one kind"
                );
                (
                    arity,
                    base.domain[0],
                    self.sorts.kind(branch_kind).index_order[1..].to_vec(),
                )
            };
            for branch_sort in branch_sorts {
                let mut domain = Vec::with_capacity(arity);
                domain.push(condition_sort);
                domain.resize(arity, branch_sort);
                self.add_op_decl_with_ctor(sym, domain, branch_sort, false);
            }
            let mut strategy = Vec::with_capacity(arity + 2);
            strategy.extend([1, 0]); // condition, then branch selection
            strategy.extend(2..=arity as u32); // remaining branches, only after failed selection
            strategy.push(0); // user equations over the normalized, still-stuck conditional
            self.set_strategy(sym, &strategy);
        }
        self.symbols.get_mut(sym).special = Some(op);
    }

    /// The next normalized instruction for an application frame. The standard strategy is synthesized
    /// without allocating: every physical argument left-to-right, then one final top attempt. A
    /// permutative semi-eager strategy similarly expands over every physical argument of the flattened
    /// A/AC node.
    fn strat_action(&self, symbol: SymbolId, cursor: usize, arity: usize) -> Option<EvalAction> {
        match &self.symbols.get(symbol).strategy {
            None => {
                if cursor < arity {
                    Some(EvalAction::Argument(cursor))
                } else if cursor == arity {
                    Some(EvalAction::Top { final_step: true })
                } else {
                    None
                }
            }
            Some(EvalStrategy::Sequence(steps)) => {
                let step = *steps.get(cursor)?;
                Some(match step {
                    EvalStep::Argument(position) => EvalAction::Argument(position as usize),
                    EvalStep::Top => EvalAction::Top {
                        final_step: cursor + 1 == steps.len(),
                    },
                })
            }
            Some(EvalStrategy::PermutativeSemiEager) => {
                if cursor == 0 {
                    Some(EvalAction::Top { final_step: false })
                } else if cursor <= arity {
                    Some(EvalAction::Argument(cursor - 1))
                } else if cursor == arity + 1 {
                    Some(EvalAction::Top { final_step: true })
                } else {
                    None
                }
            }
        }
    }

    /// Least sort of `symbol(args…)` under multi-declaration overloading. A declaration applies iff
    /// every `arg_sorts[i] <= decl.domain[i]`. A later range replaces the current choice only when it
    /// is below every earlier applicable range, so incomparable ties select the earliest declaration.
    /// If no declaration applies, the result is the error sort of the range kind.
    pub(crate) fn compute_sort(&self, symbol: SymbolId, arg_sorts: &[SortId]) -> SortId {
        let decls = self.symbols.get(symbol).decls();
        assert_eq!(
            arg_sorts.len(),
            decls[0].domain.len(),
            "arity mismatch building `{}`",
            self.symbols.get(symbol).name()
        );
        let applicable = |decl: &OpDeclaration| {
            arg_sorts
                .iter()
                .zip(&decl.domain)
                .all(|(&arg, &domain)| self.sorts.leq(arg, domain))
        };
        if let [only] = decls {
            return if applicable(only) {
                only.range
            } else {
                self.sorts.error_sort(self.sorts.kind_of(only.range))
            };
        }
        debug_assert!(
            decls
                .iter()
                .all(|decl| self.sorts.kind_of(decl.range) == self.sorts.kind_of(decls[0].range)),
            "operator declaration group invariant violated for `{}`: range kinds differ; cross-kind \
             range overloads must use distinct symbols",
            self.symbols.get(symbol).name()
        );
        let mut least = None;
        for (index, decl) in decls.iter().enumerate() {
            if applicable(decl)
                && decls[..index]
                    .iter()
                    .filter(|prior| applicable(prior))
                    .all(|prior| self.sorts.leq(decl.range, prior.range))
            {
                least = Some(decl.range);
            }
        }
        least.unwrap_or_else(|| self.sorts.error_sort(self.sorts.kind_of(decls[0].range)))
    }

    /// Value-dependent least sort of a built-in nonalgebraic constant. One-character strings and
    /// finite floats select the narrow declaration; quoted identifiers use token classification and
    /// otherwise fall back to the base `Qid` sort.
    pub(crate) fn compute_na_sort(&self, symbol: SymbolId, value: &NaValue) -> SortId {
        let decls = self.symbols.get(symbol).decls();
        let (mut min, mut max) = (decls[0].range, decls[0].range);
        for d in &decls[1..] {
            if self.sorts.leq(d.range, min) {
                min = d.range;
            }
            if self.sorts.leq(max, d.range) {
                max = d.range;
            }
        }
        if let NaValue::Qid(q) = value {
            // Unclassified quoted identifiers use the base `Qid` rather than an arbitrary
            // incomparable classification subsort.
            return self.classify_qid(q).or(self.qid_class.base).unwrap_or(max);
        }
        let special = match value {
            NaValue::Str(s) => s.len() == 1,
            NaValue::Float(bits) => f64::from_bits(*bits).is_finite(),
            NaValue::SmtNum(_) => true,
            NaValue::Qid(_) => unreachable!(),
        };
        if special { min } else { max }
    }

    /// Classify quoted-identifier text; return `None` for ordinary names or absent class sorts.
    fn classify_qid(&self, text: &str) -> Option<SortId> {
        let qc = &self.qid_class;
        match qid_aux_property(text)? {
            QidAux::Sort | QidAux::StructuredSort => qc.sort,
            QidAux::Kind => qc.kind,
            QidAux::Constant => qc.constant,
            QidAux::Variable => qc.variable,
        }
    }

    /// Record the base sort or one classification sort from a `QuotedIdentifierSymbol` id-hook.
    /// META-TERM's empty hook data identifies base `Qid`; nonempty codes identify its
    /// Sort/Kind/Constant/Variable subsorts.
    pub(crate) fn set_qid_class(&mut self, code: Option<&str>, sort: SortId) {
        match code {
            None => self.qid_class.base = Some(sort),
            Some("sortQid") => self.qid_class.sort = Some(sort),
            Some("kindQid") => self.qid_class.kind = Some(sort),
            Some("constantQid") => self.qid_class.constant = Some(sort),
            Some("variableQid") => self.qid_class.variable = Some(sort),
            Some(_) => {}
        }
    }

    /// Fold a binary theory operator left-to-right over canonical element sorts. This handles
    /// subsort overloads without representation-specific sort logic.
    pub(crate) fn compute_sort_fold(&self, symbol: SymbolId, elem_sorts: &[SortId]) -> SortId {
        let mut acc = elem_sorts[0];
        for &e in &elem_sorts[1..] {
            acc = self.compute_sort(symbol, &[acc, e]);
        }
        acc
    }

    /// Whether a variable of `sort` may take `op`'s identity.
    pub(crate) fn acu_take_identity(&self, op: SymbolId, sort: SortId) -> bool {
        self.symbol(op)
            .identity()
            .is_some_and(|id| self.sorts.leq(self.identity_sort(id), sort))
    }

    /// Maximum number of associative operands a term of each sort can contain. Element sorts have
    /// bound one; collector sorts are unbounded. These bounds distinguish stripper and collector rows
    /// in ACU distribution. Variable-headed membership constraints are outside this analysis.
    pub(crate) fn acu_sort_bounds(&self, op: SymbolId) -> std::collections::HashMap<SortId, i32> {
        use crate::diophantine::UNBOUNDED;
        let range = self.symbols.get(op).decls()[0].range;
        let kind = self.sorts.kind_of(range);
        let members: Vec<SortId> = self.sorts.kind(kind).members.clone();
        let error = self.sorts.error_sort(kind);
        let mut bounds: std::collections::HashMap<SortId, i32> =
            members.iter().map(|&s| (s, UNBOUNDED)).collect();
        // Sorts greater than or equal to `s` within the component.
        let ge = |s: SortId| -> Vec<SortId> {
            members
                .iter()
                .copied()
                .filter(|&m| self.sorts.leq(s, m))
                .collect()
        };
        let mut largest_bound = 1;
        let mut i = 1;
        while i <= largest_bound {
            let mut too_big: std::collections::HashSet<SortId> = std::collections::HashSet::new();
            for &j in &members {
                let j_bound = bounds[&j];
                for &k in &members {
                    let k_bound = bounds[&k];
                    if j_bound == UNBOUNDED || k_bound == UNBOUNDED || j_bound + k_bound > i {
                        let result = self.compute_sort(op, &[j, k]);
                        if result != error && !too_big.contains(&result) {
                            for s in ge(result) {
                                too_big.insert(s);
                            }
                        }
                    }
                }
            }
            for &j in &members {
                if !too_big.contains(&j) && bounds[&j] == UNBOUNDED {
                    bounds.insert(j, i);
                    largest_bound = 2 * i;
                }
            }
            i += 1;
        }
        bounds
    }

    /// Whether every pair of operand sorts below `sort` combines below `sort`, permitting a repeated
    /// variable to collect multiple associative operands safely.
    pub(crate) fn acu_nonlinear_sort_safe(&self, op: SymbolId, sort: SortId) -> bool {
        let kind = self.sorts.kind_of(sort);
        self.sorts
            .kind(kind)
            .index_order
            .iter()
            .copied()
            .all(|left| {
                !self.sorts.leq(left, sort)
                    || self
                        .sorts
                        .kind(kind)
                        .index_order
                        .iter()
                        .copied()
                        .all(|right| {
                            !self.sorts.leq(right, sort)
                                || self.sorts.leq(self.compute_sort(op, &[left, right]), sort)
                        })
            })
    }

    /// Least sort of `s^count(arg)`. Iterating a unary sort function over a finite kind eventually
    /// follows a lead and cycle; counts beyond the lead index modulo the cycle.
    pub(crate) fn compute_s_sort(&self, symbol: SymbolId, arg_sort: SortId, count: &Nat) -> SortId {
        let (seq, lead) = self.s_sort_path(symbol, arg_sort);
        let path_len = seq.len();
        // An S node always has count >= 1. The first `path_len` successors index the path directly.
        if let Some(c) = count.to_usize()
            && c <= path_len
        {
            return seq[c - 1];
        }
        // Past the lead, index modulo the cycle.
        let cycle = path_len - lead;
        let steps = count
            .checked_sub(&Nat::from_u64((lead + 1) as u64))
            .expect("count > path_len >= lead+1");
        seq[lead + steps.rem_usize(cycle)]
    }

    /// The successor sort path from `arg_sort`: `seq[k]` = least sort of `s^(k+1)(arg)`, iterating the
    /// unary [`compute_sort`](Self::compute_sort) until a sort repeats; returns `(seq, lead)` where
    /// `lead` is the index at which the cycle begins. Pigeonhole-terminating (finite kind).
    fn s_sort_path(&self, symbol: SymbolId, arg_sort: SortId) -> (Vec<SortId>, usize) {
        let mut seq: Vec<SortId> = Vec::new();
        let mut cur = arg_sort;
        loop {
            cur = self.compute_sort(symbol, &[cur]);
            if let Some(p) = seq.iter().position(|&s| s == cur) {
                return (seq, p);
            }
            seq.push(cur);
        }
    }

    /// Register an unconditional equation, compiling its lhs to a theory `LhsAutomaton` once, and
    /// advance the equation epoch (see [`Engine::add_equation`]).
    pub(crate) fn add_equation(&mut self, eq: Equation) -> u32 {
        self.push_equation(eq.lhs, eq.rhs, eq.nr_vars, Vec::new(), false)
    }

    /// Register a conditional equation. All equality and sort-test fragments must hold; failure
    /// backtracks to the next matcher solution.
    pub(crate) fn add_conditional_equation(
        &mut self,
        lhs: Term,
        rhs: Term,
        nr_vars: u32,
        condition: Vec<ConditionFragment>,
    ) -> u32 {
        self.push_equation(lhs, rhs, nr_vars, condition, false)
    }

    /// Register an optional conditional `[owise]` equation, tried only after every ordinary equation
    /// for the symbol fails.
    pub(crate) fn add_owise_equation(
        &mut self,
        lhs: Term,
        rhs: Term,
        nr_vars: u32,
        condition: Vec<ConditionFragment>,
    ) -> u32 {
        self.push_equation(lhs, rhs, nr_vars, condition, true)
    }

    /// Register an executable equation carrying the `[variant]` attribute.
    pub(crate) fn add_variant_equation(
        &mut self,
        lhs: Term,
        rhs: Term,
        nr_vars: u32,
        condition: Vec<ConditionFragment>,
        owise: bool,
    ) -> u32 {
        self.push_equation(lhs, rhs, nr_vars, condition, owise)
    }

    /// Compile and register an equation, returning its dense per-module **id** (the index the frontend
    /// keys its trace metadata by).
    fn push_equation(
        &mut self,
        lhs: Term,
        rhs: Term,
        nr_vars: u32,
        condition: Vec<ConditionFragment>,
        owise: bool,
    ) -> u32 {
        let top = lhs
            .top_symbol()
            .expect("equation lhs must be an application");
        assert!(
            !matches!(
                self.symbols.get(top).special,
                Some(SpecialOp::HostFunction(_))
            ),
            "equations cannot be added after a strict host binding is installed"
        );
        self.note_collapse_pattern(&lhs, &rhs);
        self.note_substitution_layout(&lhs, nr_vars, Some(&rhs), &condition);
        let condition_variables = condition_variable_indices(&condition);
        let id = self.next_eq_id;
        self.next_eq_id += 1;
        let rhs_shares = term_has_repeated_subterm(&rhs);
        let lhs_reuse = lhs_rhs_shared_subterms(&lhs, &rhs);
        // Index collapsing equations under every possible surviving top symbol. Identity and
        // idempotence can erase the declared root, so a bare collapse target must still try the equation.
        let extra_targets = self.collapse_targets(&lhs, top);
        let compiled = CompiledEquation {
            id,
            lhs: LhsAutomaton::compile_avoiding_nonlinear_vars(lhs, self, &condition_variables),
            rhs,
            nr_vars,
            condition: self.compile_condition(condition, CondOwner::EqOrMb),
            owise,
            rhs_shares,
            lhs_reuse,
        };
        for t in extra_targets {
            self.equations.entry(t).or_default().push(compiled.clone());
        }
        self.equations.entry(top).or_default().push(compiled);
        // Adding an equation can invalidate every cached normal form; advance the epoch.
        self.eq_epoch += 1;
        id
    }

    /// Additional symbol indices for an equation whose LHS can collapse below its root. Identity-only
    /// variable patterns include the identity; a multiplicity-one variable can leave any top symbol;
    /// one non-variable argument can leave that argument's top. Idempotent CUI patterns can collapse
    /// only to a shape matched by both operands.
    fn collapse_targets(&self, lhs: &Term, top: SymbolId) -> Vec<SymbolId> {
        let sym = self.symbols.get(top);
        let has_id = sym.identity.is_some();
        let idem = sym.axioms.idem;
        if !(has_id || idem) || sym.axioms.iter {
            return Vec::new();
        }
        let args = match lhs {
            Term::Op { args, .. } => args,
            _ => return Vec::new(),
        };
        let mut targets: Vec<SymbolId> = Vec::new();
        let push = |t: SymbolId, targets: &mut Vec<SymbolId>| {
            if t != top && !targets.contains(&t) {
                targets.push(t);
            }
        };
        if has_id {
            let identity = sym.identity.expect("has_id");
            let identity_top = self.identity_term(identity).top_symbol();
            let nonvars: Vec<&Term> = args.iter().filter(|a| !matches!(a, Term::Var(_))).collect();
            match nonvars.len() {
                0 => {
                    // A variable occurring once may be the lone survivor of any shape. If every
                    // variable repeats, only the all-identity collapse remains.
                    let mut single_occurrence = false;
                    for a in args {
                        if let Term::Var(v) = a
                            && args
                                .iter()
                                .filter(|b| matches!(b, Term::Var(w) if w.index == v.index))
                                .count()
                                == 1
                        {
                            single_occurrence = true;
                        }
                    }
                    if single_occurrence {
                        for (s, _) in self.symbols.iter() {
                            push(s, &mut targets);
                        }
                    } else {
                        if let Some(id_top) = identity_top {
                            push(id_top, &mut targets);
                        }
                    }
                }
                1 => {
                    if let Some(t) = nonvars[0].top_symbol() {
                        push(t, &mut targets);
                    }
                }
                _ => {}
            }
        }
        if idem && args.len() == 2 {
            // Idem collapse `f(P, P')` vs a single subject: both operands must match it. A variable
            // operand matches anything → the other operand's top bounds the shape; two variables →
            // any symbol.
            match (&args[0], &args[1]) {
                (Term::Var(_), Term::Var(_)) => {
                    for (s, _) in self.symbols.iter() {
                        push(s, &mut targets);
                    }
                }
                (Term::Var(_), other) | (other, Term::Var(_)) => {
                    if let Some(t) = other.top_symbol() {
                        push(t, &mut targets);
                    }
                }
                (a, _) => {
                    if let Some(t) = a.top_symbol() {
                        push(t, &mut targets);
                    }
                }
            }
        }
        targets
    }

    /// Compile a condition (public [`ConditionFragment`]s) for evaluation: equality / sort-test fragments
    /// are stored as-is; a matching (`:=`) or rewrite (`=>`) fragment's pattern is compiled to an
    /// [`LhsAutomaton`] through the same matcher seam and rule-only guard as an equation lhs. `owner` gates
    /// the **rewrite** (`=>`) fragment, which is legal only in a rule condition — the frontend rejects it in
    /// an `ceq`/`cmb`; this is the defensive kernel backstop.
    fn compile_condition(
        &self,
        condition: Vec<ConditionFragment>,
        owner: CondOwner,
    ) -> Vec<CompiledFragment> {
        condition
            .into_iter()
            .map(|frag| match frag {
                ConditionFragment::Equality { lhs, rhs } => CompiledFragment::Equality { lhs, rhs },
                ConditionFragment::SortTest { term, sort } => {
                    CompiledFragment::SortTest { term, sort }
                }
                ConditionFragment::Matching {
                    pattern,
                    subject,
                    fresh_vars,
                } => CompiledFragment::Matching {
                    pattern: LhsAutomaton::compile(pattern, self),
                    subject,
                    fresh_vars,
                },
                ConditionFragment::Rewrite {
                    lhs,
                    pattern,
                    fresh_vars,
                } => {
                    assert!(
                        owner == CondOwner::Rule,
                        "a rewrite (`=>`) condition fragment is legal only in a rule (`crl`)"
                    );
                    CompiledFragment::Rewrite {
                        lhs,
                        pattern: LhsAutomaton::compile(pattern, self),
                        fresh_vars,
                    }
                }
            })
            .collect()
    }

    /// Register an unconditional rule `rl lhs => rhs`. Compiles the lhs through the theory matcher seam
    /// and stores it in the rule table, which equational [`reduce`](Engine::reduce) never consults.
    pub(crate) fn add_rule(&mut self, lhs: Term, rhs: Term, nr_vars: u32) -> u32 {
        self.push_rule(lhs, rhs, nr_vars, Vec::new(), None)
    }

    pub(crate) fn add_labelled_rule(
        &mut self,
        lhs: Term,
        rhs: Term,
        nr_vars: u32,
        label: Option<std::rc::Rc<str>>,
    ) -> u32 {
        self.push_rule(lhs, rhs, nr_vars, Vec::new(), label)
    }

    /// Register a conditional rule `crl lhs => rhs if condition`. It accepts the same condition fragments
    /// as `ceq`, plus rule-only rewrite fragments `t => p`. Fragment failure backtracks into the next
    /// matcher solution.
    pub(crate) fn add_conditional_rule(
        &mut self,
        lhs: Term,
        rhs: Term,
        nr_vars: u32,
        condition: Vec<ConditionFragment>,
    ) -> u32 {
        self.push_rule(lhs, rhs, nr_vars, condition, None)
    }

    pub(crate) fn add_labelled_conditional_rule(
        &mut self,
        lhs: Term,
        rhs: Term,
        nr_vars: u32,
        condition: Vec<ConditionFragment>,
        label: Option<std::rc::Rc<str>>,
    ) -> u32 {
        self.push_rule(lhs, rhs, nr_vars, condition, label)
    }

    /// Compile and register a rule with a dense module-local id. Rules do not advance `eq_epoch`
    /// because they cannot alter equational normal forms.
    fn push_rule(
        &mut self,
        lhs: Term,
        rhs: Term,
        nr_vars: u32,
        condition: Vec<ConditionFragment>,
        label: Option<std::rc::Rc<str>>,
    ) -> u32 {
        self.note_substitution_layout(&lhs, nr_vars, Some(&rhs), &condition);
        let top = lhs.top_symbol().expect("rule lhs must be an application");
        let id = self.next_rule_id;
        self.next_rule_id += 1;
        let rhs_shares = term_has_repeated_subterm(&rhs);
        let condition_variables = condition_variable_indices(&condition);
        let oo = self.classify_oo_rule(&lhs);
        let compiled = CompiledRule {
            id,
            label,
            lhs: LhsAutomaton::compile_avoiding_nonlinear_vars(lhs, self, &condition_variables),
            rhs,
            nr_vars,
            oo,
            condition: self.compile_condition(condition, CondOwner::Rule),
            rhs_shares,
        };
        self.rules.entry(top).or_default().push(compiled);
        id
    }

    pub(crate) fn rule_label(&self, id: u32) -> Option<&std::rc::Rc<str>> {
        self.rules
            .values()
            .flatten()
            .find(|rule| rule.id == id)
            .and_then(|rule| rule.label.as_ref())
    }

    /// Retain one source rule for root rewriting modulo SMT. This table is independent of the ordinary
    /// executable-rule table, so `[nonexec]` rules participate without changing `rewrite`/`search`.
    fn add_smt_rule(
        &mut self,
        lhs: Term,
        rhs: Term,
        variable_sorts: Vec<SortId>,
        variable_names: Vec<String>,
        condition: Vec<ConditionFragment>,
    ) {
        self.smt_rules_valid &= term_is_linear(&lhs) && !term_contains_smt(self, &lhs);
        let Some(top) = lhs.top_symbol() else {
            return;
        };
        let condition_variables = condition_variable_indices(&condition);
        let lhs = LhsAutomaton::compile_avoiding_nonlinear_vars(lhs, self, &condition_variables);
        self.smt_rules
            .entry(top)
            .or_default()
            .push(CompiledSmtRule {
                lhs,
                rhs,
                nr_vars: variable_sorts.len() as u32,
                condition,
                variable_sorts,
                variable_names,
            });
    }

    /// Classify a configuration rule for `erewrite`. The object-message fast path requires exactly
    /// one stable object and one stable message sharing their first, name-bearing argument.
    fn classify_oo_rule(&self, lhs: &Term) -> OoRuleKind {
        let Term::Op { symbol, args } = lhs else {
            return OoRuleKind::NotConfig;
        };
        if !self.symbol(*symbol).oo.config {
            return OoRuleKind::NotConfig;
        }
        if args.len() != 2 {
            return OoRuleKind::LeftOver;
        }
        let (mut object, mut message, mut name): (bool, Option<SymbolId>, Option<&Term>) =
            (false, None, None);
        for arg in args {
            // Must be stable — an application whose first argument is the name (a top variable disqualifies).
            let Term::Op {
                symbol: asym,
                args: aargs,
            } = arg
            else {
                return OoRuleKind::LeftOver;
            };
            let Some(arg0) = aargs.first() else {
                return OoRuleKind::LeftOver;
            };
            let oo = self.symbol(*asym).oo;
            if oo.object {
                if object {
                    return OoRuleKind::LeftOver;
                }
                object = true;
            } else if oo.message {
                if message.is_some() {
                    return OoRuleKind::LeftOver;
                }
                message = Some(*asym);
            } else {
                return OoRuleKind::LeftOver;
            }
            match name {
                None => name = Some(arg0),
                Some(n) if n != arg0 => return OoRuleKind::LeftOver,
                Some(_) => {}
            }
        }
        match (object, message) {
            (true, Some(msg)) => OoRuleKind::ObjectMessage(msg),
            _ => OoRuleKind::LeftOver,
        }
    }

    /// Register an unconditional membership axiom `mb lhs : sort`, compile its lhs, and add it to the
    /// direct-symbol or collapse-kind index. Memberships refine sorts lazily at a node's reduction
    /// normal-form point and do not change the equation epoch.
    pub(crate) fn add_membership(&mut self, mb: Membership) -> u32 {
        self.push_membership(mb.lhs, mb.sort, mb.nr_vars, Vec::new())
    }

    /// Register a conditional membership, lowering the sort only when its condition holds.
    pub(crate) fn add_conditional_membership(
        &mut self,
        lhs: Term,
        sort: SortId,
        nr_vars: u32,
        condition: Vec<ConditionFragment>,
    ) -> u32 {
        self.push_membership(lhs, sort, nr_vars, condition)
    }

    /// Compile and register a membership axiom, returning its dense per-module **id**. (The membership
    /// table is re-sorted smallest-target-first for application, but `id` stays declaration order — the
    /// frontend keys `mb_traces` by it.)
    fn push_membership(
        &mut self,
        lhs: Term,
        sort: SortId,
        nr_vars: u32,
        condition: Vec<ConditionFragment>,
    ) -> u32 {
        self.note_substitution_layout(&lhs, nr_vars, None, &condition);
        let top = lhs
            .top_symbol()
            .expect("membership lhs must be an application");
        // Index top-collapsing memberships across the result kind; individual matchers reject
        // impossible candidates without cloning the compiled constraint.
        let collapse_kind = {
            let symbol = self.symbols.get(top);
            match symbol.theory() {
                Theory::Acu | Theory::Au
                    if symbol.left_identity().is_some() || symbol.right_identity().is_some() =>
                {
                    Some(self.sorts.kind_of(sort))
                }
                Theory::Cui if symbol.identity().is_some() || symbol.axioms.idem => {
                    Some(self.sorts.kind_of(sort))
                }
                _ => None,
            }
        };
        let id = self.next_mb_id;
        self.next_mb_id += 1;
        debug_assert_eq!(id as usize, self.memberships.len());
        let condition_variables = condition_variable_indices(&condition);
        self.memberships.push(SortConstraint {
            id,
            lhs: LhsAutomaton::compile_avoiding_nonlinear_vars(lhs, self, &condition_variables),
            sort,
            nr_vars,
            condition: self.compile_condition(condition, CondOwner::EqOrMb),
        });

        let constraints = &self.memberships;
        let sorts = &self.sorts;
        let ids = match collapse_kind {
            Some(kind) => self.collapsing_memberships.entry(kind).or_default(),
            None => self.membership_index.entry(top).or_default(),
        };
        ids.push(id);
        ids.sort_by(|&left, &right| membership_order(constraints, sorts, left, right));
        id
    }

    /// The current equation-set epoch (stamped into nodes proved canonical; see [`DagNode`]).
    pub(crate) fn eq_epoch(&self) -> u32 {
        self.eq_epoch
    }

    fn invalidate_normal_forms(&mut self) {
        self.eq_epoch += 1;
    }
}

// ======================================================================================
// Runtime: the DAG arena, GC, and the reduction subsystem (mutates; borrows the Signature)
// ======================================================================================

impl Runtime {
    // ---- DAG construction ----

    /// Allocate a node with its structural base sort and account for safe-point GC. Membership
    /// refinement occurs only when reduction reaches a normal form.
    fn alloc_node(&mut self, sort: SortId, term: NodeTerm) -> DagId {
        // Reuse an equal node while a construction deduplication window is open. A hit allocates
        // nothing and therefore does not advance the GC allocation counter.
        if self.dedup.is_some() {
            if let Some(&existing) = self.dedup.as_ref().unwrap().get(&term) {
                return existing;
            }
            let key = term.clone();
            let id = self.alloc_raw(sort, term);
            self.dedup.as_mut().unwrap().insert(key, id);
            return id;
        }
        self.alloc_raw(sort, term)
    }

    /// The raw allocation funnel: account the node against the safe-point-GC interval and allocate it
    /// fresh. Split out of [`alloc_node`](Self::alloc_node) so a dedup *hit* (which allocates nothing)
    /// bypasses the counter bump entirely.
    fn alloc_raw(&mut self, sort: SortId, term: NodeTerm) -> DagId {
        if self.gc_interval.is_some() {
            self.allocs_since_gc += 1;
        }
        self.dags.alloc(DagNode {
            sort,
            reduced_epoch: 0,
            nf: None,
            term,
        })
    }

    /// Open a construction-only structural-deduplication window. It must not span a GC safe point and
    /// must be balanced by [`end_dedup`](Self::end_dedup).
    fn begin_dedup(&mut self) {
        self.dedup = Some(HashMap::new());
    }

    /// Close the dedup window opened by [`begin_dedup`](Self::begin_dedup), dropping the memo.
    fn end_dedup(&mut self) {
        self.dedup = None;
    }

    /// Lower a node's cached least sort through applicable direct and top-collapsing memberships.
    /// Candidates merge by target-sort order and match whole; every successful lowering counts once.
    /// Memberships run only at a node's reduction normal form. `whole` carries trace reconstruction.
    fn constrain_to_smaller_sort(
        &mut self,
        sig: &Signature,
        id: DagId,
        whole: Option<DagId>,
        frames: &[ReduceFrame],
    ) {
        // Lazy associative flattening lets each intermediate parse node reach its own normal-form
        // membership point, preserving source-order accounting.
        self.constrain_node_whole(sig, id, whole, frames);
    }

    /// Repeatedly apply the first whole-matching membership whose target is strictly below the current
    /// sort, then restart from the smallest target until a fixpoint. Each lowering counts once.
    fn constrain_node_whole(
        &mut self,
        sig: &Signature,
        id: DagId,
        whole: Option<DagId>,
        frames: &[ReduceFrame],
    ) {
        let node = self.node(id);
        let symbol = node.symbol();
        let kind = sig.sorts.kind_of(node.sort);
        let direct = sig
            .membership_index
            .get(&symbol)
            .map_or(&[][..], Vec::as_slice);
        let collapsing = sig
            .collapsing_memberships
            .get(&kind)
            .map_or(&[][..], Vec::as_slice);
        if direct.is_empty() && collapsing.is_empty() {
            return;
        }
        let original_sort = self.node(id).sort;
        let checkpoint = self.semantic_checkpoint();

        loop {
            let current = self.node(id).sort;
            let mut lowered = false;
            let (mut direct_cursor, mut collapse_cursor) = (0, 0);
            while direct_cursor < direct.len() || collapse_cursor < collapsing.len() {
                let constraint_id = match (
                    direct.get(direct_cursor).copied(),
                    collapsing.get(collapse_cursor).copied(),
                ) {
                    (Some(left), Some(right))
                        if membership_order(&sig.memberships, &sig.sorts, left, right)
                            != Ordering::Greater =>
                    {
                        direct_cursor += 1;
                        left
                    }
                    (Some(_), Some(right)) => {
                        collapse_cursor += 1;
                        right
                    }
                    (Some(left), None) => {
                        direct_cursor += 1;
                        left
                    }
                    (None, Some(right)) => {
                        collapse_cursor += 1;
                        right
                    }
                    (None, None) => unreachable!("candidate cursors are exhausted"),
                };
                let sc = &sig.memberships[constraint_id as usize];
                // Only a membership whose target is *strictly below* the current sort can refine it.
                if sc.sort == current || !sig.sorts().leq(sc.sort, current) {
                    continue;
                }
                let applies = self.membership_applies(sig, sc, id, frames);
                if self.reducer_fault.is_some() {
                    self.dags.get_mut(id).sort = original_sort;
                    self.restore_semantic_checkpoint(checkpoint);
                    return;
                }
                if let Some(bindings) = applies {
                    // Record before mutation so the event captures the current sort as `old_sort`.
                    if self.tracing() {
                        let depth = self.condition_depth;
                        self.record(TraceEvent::Membership {
                            mb_id: sc.id,
                            depth,
                            subject: id,
                            old_sort: current,
                            new_sort: sc.sort,
                            bindings,
                            whole,
                        });
                    }
                    self.dags.get_mut(id).sort = sc.sort;
                    self.rewrite_count += 1; // membership application
                    self.membership_count += 1;
                    lowered = true;
                    break; // restart the merged order with the new, smaller sort
                }
            }
            if !lowered {
                break;
            }
        }
    }

    /// Whether a compiled membership lhs matches `id` and, for a `cmb`, its condition holds. Free and
    /// theory patterns dispatch through the same automaton seam; a condition failure backtracks into the
    /// next match solution, and all condition reductions contribute to the rewrite total.
    /// On success returns the membership match's substitution snapshot (for the trace), or an empty
    /// `Vec` when not tracing (no allocation); `None` on no-match. A conditional membership (`cmb`) emits
    /// a *trial* per matcher solution, backtracking on condition failure.
    fn membership_applies(
        &mut self,
        sig: &Signature,
        sc: &SortConstraint,
        id: DagId,
        frames: &[ReduceFrame],
    ) -> Option<Vec<Option<DagId>>> {
        let mut subst = Subst::new();
        subst.reset(sc.nr_vars);
        let mut sp = sc.lhs.match_(self, sig, id, &mut subst, false, false)?;
        while sp.next(self, sig, &mut subst) {
            if self.reducer_fault.is_some() {
                return None;
            }
            if sc.condition.is_empty() {
                return Some(if self.tracing() {
                    Self::snapshot_subst(&subst)
                } else {
                    Vec::new()
                });
            }
            let depth = self.condition_depth;
            if self.tracing() {
                let bindings = Self::snapshot_subst(&subst);
                self.record(TraceEvent::TrialStart {
                    kind: StmtKind::Membership,
                    stmt_id: sc.id,
                    depth,
                    bindings,
                });
            }
            let holds = match self.condition_holds(
                sig,
                &sc.condition,
                &mut subst,
                StmtKind::Membership,
                sc.id,
                frames,
                id,
            ) {
                Ok(holds) => holds,
                Err(fault) => {
                    self.reducer_fault = Some(fault);
                    return None;
                }
            };
            if self.tracing() {
                self.record(TraceEvent::TrialEnd {
                    kind: StmtKind::Membership,
                    depth,
                    success: holds,
                });
            }
            if holds {
                return Some(if self.tracing() {
                    Self::snapshot_subst(&subst)
                } else {
                    Vec::new()
                });
            }
        }
        None
    }

    /// Build a free-theory node `symbol(args...)`, computing and caching its least sort.
    pub(crate) fn make_free(
        &mut self,
        sig: &Signature,
        symbol: SymbolId,
        args: Vec<DagId>,
    ) -> DagId {
        // Preserve the public guard message while keeping arity validation in `compute_sort`.
        assert_eq!(
            sig.symbol(symbol).theory(),
            Theory::Free,
            "`{}` is an ACU operator — build it with make_acu/make_ac, not make_free",
            sig.symbol(symbol).name()
        );
        let sort = self.free_sort(sig, symbol, &args);
        self.alloc_node(sort, NodeTerm::Free { symbol, args })
    }

    /// Rebuild a node after substitution while preserving its exact theory representation.
    ///
    /// Substitution skips top normalization, so a same-symbol AC/AU binding can remain a shared nested
    /// child until reduction. This transient representation preserves narrowing rewrite counts.
    pub(crate) fn make_preserving_representation(
        &mut self,
        sig: &Signature,
        term: NodeTerm,
    ) -> DagId {
        let sort = match &term {
            NodeTerm::Free { symbol, args } => self.free_sort(sig, *symbol, args),
            NodeTerm::Acu { symbol, args } => {
                let elem_sorts: Vec<SortId> = args
                    .iter()
                    .flat_map(|&(arg, multiplicity)| {
                        std::iter::repeat_n(self.dags.get(arg).sort, multiplicity as usize)
                    })
                    .collect();
                sig.compute_sort_fold(*symbol, &elem_sorts)
            }
            NodeTerm::Au { symbol, args } | NodeTerm::Cui { symbol, args } => {
                let elem_sorts: Vec<SortId> =
                    args.iter().map(|&arg| self.dags.get(arg).sort).collect();
                sig.compute_sort_fold(*symbol, &elem_sorts)
            }
            NodeTerm::S { symbol, count, arg } => {
                sig.compute_s_sort(*symbol, self.dags.get(*arg).sort, count)
            }
            NodeTerm::Na { symbol, value } => sig.compute_na_sort(*symbol, value),
            NodeTerm::Var { symbol, .. } => sig.symbol(*symbol).decls[0].range,
        };
        self.alloc_node(sort, term)
    }

    /// Least sort of a free node `symbol(args…)`. A single declaration is handled inline without
    /// allocating; overloaded operators use [`Signature::compute_sort`] with a collected sort slice.
    fn free_sort(&self, sig: &Signature, symbol: SymbolId, args: &[DagId]) -> SortId {
        let decls = sig.symbol(symbol).decls();
        if let [only] = decls {
            assert_eq!(
                args.len(),
                only.domain.len(),
                "arity mismatch building `{}`",
                sig.symbol(symbol).name()
            );
            let well_sorted = only
                .domain
                .iter()
                .zip(args)
                .all(|(&dom, &arg)| sig.sorts().leq(self.dags.get(arg).sort, dom));
            return if well_sorted {
                only.range
            } else {
                sig.sorts().error_sort(sig.sorts().kind_of(only.range))
            };
        }
        let arg_sorts: Vec<SortId> = args.iter().map(|&a| self.dags.get(a).sort).collect();
        sig.compute_sort(symbol, &arg_sorts)
    }

    /// Recompute an existing node's structural base sort from its current children without applying
    /// memberships. This propagates child sort refinements even when the parent node itself was reused.
    fn compute_base_sort(&self, sig: &Signature, id: DagId) -> SortId {
        match &self.node(id).term {
            NodeTerm::Free { symbol, args } => self.free_sort(sig, *symbol, args),
            NodeTerm::Acu { symbol, args } => {
                let elem_sorts: Vec<SortId> = args
                    .iter()
                    .flat_map(|&(e, m)| std::iter::repeat_n(self.dags.get(e).sort, m as usize))
                    .collect();
                sig.compute_sort_fold(*symbol, &elem_sorts)
            }
            NodeTerm::Au { symbol, args } => {
                let arg_sorts: Vec<SortId> = args.iter().map(|&e| self.dags.get(e).sort).collect();
                sig.compute_sort_fold(*symbol, &arg_sorts)
            }
            NodeTerm::Cui { symbol, args } => sig.compute_sort(
                *symbol,
                &[self.dags.get(args[0]).sort, self.dags.get(args[1]).sort],
            ),
            NodeTerm::S { symbol, count, arg } => {
                sig.compute_s_sort(*symbol, self.dags.get(*arg).sort, count)
            }
            // A constant leaf's sort never changes; a variable's sort is authoritative as built
            // (declared sort, or the kind for a mid-solve fresh variable).
            NodeTerm::Na { .. } | NodeTerm::Var { .. } => self.node(id).sort,
        }
    }

    /// Make a fresh reducible occurrence of `id` for an argument evaluated after a strategy `0`.
    ///
    /// Copies the unreduced root and only its eager argument positions. The fresh occurrence prevents
    /// two physical subject positions sharing one hash-consed redex from normalizing only once.
    /// `copies` preserves sharing within one occurrence and is reset for each strategy argument.
    fn copy_reducible(&mut self, sig: &Signature, id: DagId) -> DagId {
        self.copy_eager_upto_reduced(sig, id, &mut HashMap::new())
    }

    fn copy_eager_upto_reduced(
        &mut self,
        sig: &Signature,
        id: DagId,
        copies: &mut HashMap<DagId, DagId>,
    ) -> DagId {
        let node = self.node(id);
        if node.reduced_epoch == sig.eq_epoch() {
            return node.nf.unwrap_or(id);
        }
        if let Some(&copy) = copies.get(&id) {
            return copy;
        }

        let mut term = node.term.clone();
        match &mut term {
            NodeTerm::Free { symbol, args } | NodeTerm::Cui { symbol, args } => {
                let strategy = &sig.symbol(*symbol).strategy;
                for (position, arg) in args.iter_mut().enumerate() {
                    let eager = match strategy {
                        None => true,
                        Some(EvalStrategy::Sequence(steps)) => steps
                            .iter()
                            .take_while(|step| **step != EvalStep::Top)
                            .any(|step| *step == EvalStep::Argument(position as u32)),
                        Some(EvalStrategy::PermutativeSemiEager) => false,
                    };
                    if eager {
                        *arg = self.copy_eager_upto_reduced(sig, *arg, copies);
                    }
                }
            }
            NodeTerm::Acu { symbol, args } => {
                if sig.symbol(*symbol).strategy.is_none() {
                    for (arg, _) in args {
                        *arg = self.copy_eager_upto_reduced(sig, *arg, copies);
                    }
                }
            }
            NodeTerm::Au { symbol, args } => {
                if sig.symbol(*symbol).strategy.is_none() {
                    for arg in args {
                        *arg = self.copy_eager_upto_reduced(sig, *arg, copies);
                    }
                }
            }
            NodeTerm::S { symbol, arg, .. } => {
                let eager = match &sig.symbol(*symbol).strategy {
                    None => true,
                    Some(EvalStrategy::Sequence(steps)) => steps
                        .iter()
                        .take_while(|step| **step != EvalStep::Top)
                        .any(|step| *step == EvalStep::Argument(0)),
                    Some(EvalStrategy::PermutativeSemiEager) => false,
                };
                if eager {
                    *arg = self.copy_eager_upto_reduced(sig, *arg, copies);
                }
            }
            NodeTerm::Na { .. } | NodeTerm::Var { .. } => {}
        }
        let copy = self.make_preserving_representation(sig, term);
        copies.insert(id, copy);
        copy
    }

    /// Compute true sorts recursively without applying equations. Evaluation strategies may skip
    /// arguments during reduction, so this path still refines their children, recomputes each base sort,
    /// and applies memberships. `seen` prevents duplicate work for shared subterms within one strategy
    /// frame; already-reduced nodes already carry their true sort.
    fn compute_true_sort(
        &mut self,
        sig: &Signature,
        id: DagId,
        seen: &mut HashSet<DagId>,
        frames: &[ReduceFrame],
    ) {
        if self.node(id).reduced_epoch == sig.eq_epoch() || !seen.insert(id) {
            return; // already at its true sort, or already refined in this pass
        }
        let children: Vec<DagId> = self.node(id).children().collect();
        for c in children {
            self.compute_true_sort(sig, c, seen, frames);
        }
        let base = self.compute_base_sort(sig, id);
        self.dags.get_mut(id).sort = base;
        // No reduce frame here (this is off the main stack), so no `Whole:` reconstruction — `None`. `frames`
        // is the enclosing reduce's stack: a root set for a `cmb` condition that re-enters `reduce`.
        self.constrain_to_smaller_sort(sig, id, None, frames);
    }

    /// Convenience for a constant (an arity-0 symbol).
    pub(crate) fn make_const(&mut self, sig: &Signature, symbol: SymbolId) -> DagId {
        self.make_free(sig, symbol, Vec::new())
    }

    /// Build an overloaded constant using a specific declaration range. Ordinary construction infers
    /// the least declaration from children; a nullary symbol has no children to disambiguate overloads.
    pub(crate) fn make_const_at_sort(
        &mut self,
        sig: &Signature,
        symbol: SymbolId,
        sort: SortId,
    ) -> DagId {
        debug_assert!(
            sig.symbol(symbol)
                .decls()
                .iter()
                .any(|decl| { decl.domain.is_empty() && decl.range == sort })
        );
        self.alloc_node(
            sort,
            NodeTerm::Free {
                symbol,
                args: Vec::new(),
            },
        )
    }

    /// Materialize a signature-owned identity term once as a normalized, engine-lifetime DAG.
    ///
    /// The raw instance is entered in the permanent cache before reduction: safe-point GC may run
    /// during that reduction, and collapse normalization may consult an identity while reducing one.
    /// A cached identity is reduced again only after the equation epoch changes; this preserves the
    /// canonical node on ordinary fetches without blessing a stale normal form after module extension.
    pub(crate) fn identity_dag(&mut self, sig: &Signature, identity: IdentityId) -> DagId {
        let d = match self.identity_dags.get(&identity) {
            Some(&d) => {
                // Reduction of an identity can match an identity-bearing equation, whose matcher
                // asks for this same identity to build an empty variable run. Handing that cached
                // DAG to the collapse binding must stamp it reduced: if the equation rewrites the
                // identity to itself, the enclosing reducer then counts the one application and
                // stops instead of applying it forever. Clear an older epoch's forwarding target
                // before blessing the value for the current one.
                if self.identity_building.contains(&identity) {
                    let n = self.dags.get_mut(d);
                    n.nf = None;
                    n.reduced_epoch = sig.eq_epoch();
                    return d;
                }
                d
            }
            None => {
                assert!(
                    self.identity_building.insert(identity),
                    "recursive identity-term materialization"
                );
                let term = sig.identity_term(identity);
                let d = self.instantiate(sig, term, &Subst::new());
                self.identity_dags.insert(identity, d);
                self.identity_building.remove(&identity);
                d
            }
        };
        assert!(
            self.identity_building.insert(identity),
            "recursive identity normalization was not intercepted by the cache"
        );
        // Identity canonicalization is module/runtime maintenance, not a user rewrite command:
        // preserve observable rewrite statistics and discard any internal trace events. Keeping
        // the existing trace buffer installed during reduction still roots its DAGs across GC.
        let rewrite_count = self.rewrite_count;
        let membership_count = self.membership_count;
        let rule_rewrite_count = self.rule_rewrite_count;
        let variant_narrowing_count = self.variant_narrowing_count;
        let narrowing_count = self.narrowing_count;
        let trace_len = self.trace.as_ref().map(Vec::len);
        let normalized = match self.reduce(sig, d, &mut NullDescent) {
            Ok(normalized) => normalized,
            Err(fault) => {
                self.reducer_fault = Some(fault);
                d
            }
        };
        self.rewrite_count = rewrite_count;
        self.membership_count = membership_count;
        self.rule_rewrite_count = rule_rewrite_count;
        self.variant_narrowing_count = variant_narrowing_count;
        self.narrowing_count = narrowing_count;
        if let (Some(trace), Some(len)) = (&mut self.trace, trace_len) {
            trace.truncate(len);
        }
        self.identity_building.remove(&identity);
        self.identity_dags.insert(identity, normalized);
        normalized
    }

    pub(crate) fn is_identity(&self, sig: &Signature, identity: IdentityId, dag: DagId) -> bool {
        if let Some(&id_dag) = self.identity_dags.get(&identity) {
            return id_dag == dag || self.deep_equal(id_dag, dag);
        }
        sig.identity_constant(identity)
            .is_some_and(|id_sym| self.is_constant(dag, id_sym))
    }

    /// Build a canonical **ACU** node from `(element, multiplicity)` pairs. Flatten same-symbol nodes,
    /// discard identities, merge equal elements, sort structurally, then collapse an empty multiset to
    /// the identity or a singleton to its element. Every surviving node is therefore in ACU normal form.
    pub(crate) fn make_acu(
        &mut self,
        sig: &Signature,
        symbol: SymbolId,
        raw_args: Vec<(DagId, u32)>,
    ) -> DagId {
        self.make_acu_normalized(sig, symbol, raw_args, false)
    }

    /// Canonicalize a fresh non-eager ACU application before its first top attempt, including nested
    /// same-symbol nodes and equal unreduced entries.
    fn make_acu_at_top(
        &mut self,
        sig: &Signature,
        symbol: SymbolId,
        raw_args: Vec<DagId>,
    ) -> DagId {
        self.make_acu_normalized(
            sig,
            symbol,
            raw_args.into_iter().map(|arg| (arg, 1)).collect(),
            true,
        )
    }

    fn make_acu_normalized(
        &mut self,
        sig: &Signature,
        symbol: SymbolId,
        raw_args: Vec<(DagId, u32)>,
        normalize_unreduced: bool,
    ) -> DagId {
        debug_assert_eq!(
            sig.symbol(symbol).theory(),
            Theory::Acu,
            "make_acu on a non-ACU symbol"
        );
        let identity = sig.symbol(symbol).identity();
        let epoch = sig.eq_epoch();

        // Ordinary construction defers unreduced nested applications to retain bottom-up rewrite
        // accounting. An explicit strategy Top boundary flattens them immediately.
        let mut pending = raw_args;
        let mut flat: Vec<(DagId, u32)> = Vec::with_capacity(pending.len());
        while let Some((arg, mult)) = pending.pop() {
            if mult == 0 {
                continue;
            }
            if identity.is_some_and(|id| self.is_identity(sig, id, arg)) {
                continue;
            }
            match &self.dags.get(arg).term {
                NodeTerm::Acu {
                    symbol: inner,
                    args,
                } if *inner == symbol
                    && (normalize_unreduced || self.dags.get(arg).reduced_epoch == epoch) =>
                {
                    for &(element, inner_mult) in args {
                        pending.push((element, inner_mult * mult));
                    }
                }
                _ => flat.push((arg, mult)),
            }
        }

        // Ordinary construction merges equal entries only after reduction; explicit top
        // normalization merges them immediately.
        flat.sort_by(|&(x, _), &(y, _)| self.dag_compare(x, y));
        let mut args: Vec<(DagId, u32)> = Vec::with_capacity(flat.len());
        for (element, mult) in flat {
            match args.last_mut() {
                Some(last)
                    if last.0 == element
                        || (self.dag_compare(last.0, element) == Ordering::Equal
                            && (normalize_unreduced
                                || (self.dags.get(last.0).reduced_epoch == epoch
                                    && self.dags.get(element).reduced_epoch == epoch))) =>
                {
                    last.1 += mult;
                }
                _ => args.push((element, mult)),
            }
        }

        let total: u64 = args.iter().map(|&(_, mult)| u64::from(mult)).sum();
        match total {
            0 => {
                let identity =
                    identity.expect("an empty ACU multiset requires an identity element");
                self.identity_dag(sig, identity)
            }
            1 => args[0].0,
            _ => {
                let elem_sorts: Vec<SortId> = args
                    .iter()
                    .flat_map(|&(element, mult)| {
                        std::iter::repeat_n(self.dags.get(element).sort, mult as usize)
                    })
                    .collect();
                let sort = sig.compute_sort_fold(symbol, &elem_sorts);
                self.alloc_node(sort, NodeTerm::Acu { symbol, args })
            }
        }
    }

    /// Rebuild an ACU node after changing only variable indices, preserving argument order,
    /// multiplicities, and duplicate entries. Symbolic DAG indexing must not sort, merge, or collapse:
    /// copied ground subterms may occupy distinct entries with independent reduction state.
    pub(crate) fn make_acu_preserving_order(
        &mut self,
        sig: &Signature,
        symbol: SymbolId,
        args: Vec<(DagId, u32)>,
    ) -> DagId {
        let elem_sorts: Vec<SortId> = args
            .iter()
            .flat_map(|&(e, m)| std::iter::repeat_n(self.dags.get(e).sort, m as usize))
            .collect();
        let sort = if elem_sorts.is_empty() {
            let identity = sig
                .symbol(symbol)
                .identity()
                .expect("an empty ACU multiset requires an identity element");
            sig.identity_sort(identity)
        } else {
            sig.compute_sort_fold(symbol, &elem_sorts)
        };
        self.alloc_node(sort, NodeTerm::Acu { symbol, args })
    }

    /// Put `dag` into eager **theory normal form** for symbolic operations: recursively flatten nested
    /// same-symbol ACU/AU nodes and merge equal ACU elements unconditionally. This differs from
    /// [`make_acu`](Self::make_acu), whose lazy splice preserves concrete rewrite accounting. Without
    /// this pass, a binary parse of `X + X + Y` would reach ACU solving as `{(X+X): 1, Y: 1}` rather
    /// than `{X: 2, Y: 1}`.
    ///
    /// A normal-form source may transfer its reduced stamp to an equivalent rebuilt node. Forwarding
    /// redexes and theory collapses may not.
    fn inherit_reduced_status(&mut self, sig: &Signature, source: DagId, rebuilt: DagId) {
        if source == rebuilt {
            return;
        }
        let source_is_normal = {
            let node = self.dags.get(source);
            node.reduced_epoch == sig.eq_epoch()
                && node.nf.is_none()
                && node.symbol() == self.dags.get(rebuilt).symbol()
        };
        if source_is_normal {
            let node = self.dags.get_mut(rebuilt);
            node.reduced_epoch = sig.eq_epoch();
            node.nf = None;
        }
    }

    pub(crate) fn normalize_for_unify(&mut self, sig: &Signature, dag: DagId) -> DagId {
        match self.dags.get(dag).term.clone() {
            NodeTerm::Var { .. } | NodeTerm::Na { .. } => dag,
            NodeTerm::Free { symbol, args } => {
                let nargs: Vec<DagId> = args
                    .iter()
                    .map(|&a| self.normalize_for_unify(sig, a))
                    .collect();
                if nargs == args {
                    dag
                } else {
                    self.make_free(sig, symbol, nargs)
                }
            }
            NodeTerm::Cui { symbol, args } => {
                let x = self.normalize_for_unify(sig, args[0]);
                let y = self.normalize_for_unify(sig, args[1]);
                self.make_cui_for_unify(sig, symbol, x, y)
            }
            NodeTerm::S { symbol, count, arg } => {
                let na = self.normalize_for_unify(sig, arg);
                self.make_s(sig, symbol, count, na)
            }
            NodeTerm::Acu { symbol, args } => {
                let mut flat: Vec<(DagId, u32)> = Vec::new();
                for (e, m) in args {
                    let ne = self.normalize_for_unify(sig, e);
                    match &self.dags.get(ne).term {
                        NodeTerm::Acu {
                            symbol: inner,
                            args: inner_args,
                        } if *inner == symbol => {
                            for &(ie, im) in inner_args {
                                flat.push((ie, im * m));
                            }
                        }
                        _ => flat.push((ne, m)),
                    }
                }
                self.build_acu_eager(sig, symbol, flat)
            }
            NodeTerm::Au { symbol, args } => {
                let mut flat: Vec<DagId> = Vec::new();
                for a in args {
                    let na = self.normalize_for_unify(sig, a);
                    match &self.dags.get(na).term {
                        NodeTerm::Au {
                            symbol: inner,
                            args: inner_args,
                        } if *inner == symbol => {
                            flat.extend(inner_args.iter().copied());
                        }
                        _ => flat.push(na),
                    }
                }
                self.make_au(sig, symbol, flat) // flat already spliced; make_au drops identities/collapses
            }
        }
    }

    /// The eager ACU canonicalizer used by [`normalize_for_unify`]: sort + **unconditionally** merge
    /// equal elements (summing multiplicities) + collapse, over an already-flattened element list.
    fn build_acu_eager(
        &mut self,
        sig: &Signature,
        symbol: SymbolId,
        flat: Vec<(DagId, u32)>,
    ) -> DagId {
        let identity = sig.symbol(symbol).identity();
        let mut flat: Vec<(DagId, u32)> = flat
            .into_iter()
            .filter(|&(arg, m)| {
                m != 0 && !identity.is_some_and(|id| self.is_identity(sig, id, arg))
            })
            .collect();
        flat.sort_by(|&(x, _), &(y, _)| self.dag_compare_for_unify(x, y));
        let mut args: Vec<(DagId, u32)> = Vec::with_capacity(flat.len());
        for (e, m) in flat {
            match args.last_mut() {
                Some(last)
                    if last.0 == e || self.dag_compare_for_unify(last.0, e) == Ordering::Equal =>
                {
                    last.1 += m
                }
                _ => args.push((e, m)),
            }
        }
        let total: u64 = args.iter().map(|&(_, m)| u64::from(m)).sum();
        match total {
            0 => {
                let identity =
                    identity.expect("an empty ACU multiset requires an identity element");
                self.identity_dag(sig, identity)
            }
            1 => args[0].0,
            _ => {
                let elem_sorts: Vec<SortId> = args
                    .iter()
                    .flat_map(|&(e, m)| std::iter::repeat_n(self.dags.get(e).sort, m as usize))
                    .collect();
                let sort = sig.compute_sort_fold(symbol, &elem_sorts);
                self.alloc_node(sort, NodeTerm::Acu { symbol, args })
            }
        }
    }

    /// Build a canonical **AU** node. Two-sided identities vanish anywhere; a one-sided identity
    /// vanishes only at its legal edge after associative flattening.
    pub(crate) fn make_au(
        &mut self,
        sig: &Signature,
        symbol: SymbolId,
        raw_args: Vec<DagId>,
    ) -> DagId {
        self.make_au_normalized(sig, symbol, raw_args, false)
    }

    fn make_au_at_top(&mut self, sig: &Signature, symbol: SymbolId, raw_args: Vec<DagId>) -> DagId {
        self.make_au_normalized(sig, symbol, raw_args, true)
    }

    fn make_au_normalized(
        &mut self,
        sig: &Signature,
        symbol: SymbolId,
        raw_args: Vec<DagId>,
        normalize_unreduced: bool,
    ) -> DagId {
        debug_assert_eq!(
            sig.symbol(symbol).theory(),
            Theory::Au,
            "make_au on a non-AU symbol"
        );
        let sym = sig.symbol(symbol);
        let identity = sym.identity();
        let left_identity = sym.left_identity();
        let right_identity = sym.right_identity();
        let epoch = sig.eq_epoch();

        // A stack in reverse source order preserves AU ordering while recursively flattening at an
        // explicit Top boundary. Ordinary construction still defers unreduced nested applications.
        let mut pending: Vec<DagId> = raw_args.into_iter().rev().collect();
        let mut args = Vec::with_capacity(pending.len());
        while let Some(arg) = pending.pop() {
            if identity.is_some_and(|id| self.is_identity(sig, id, arg)) {
                continue;
            }
            match &self.dags.get(arg).term {
                NodeTerm::Au {
                    symbol: inner,
                    args: inner_args,
                } if *inner == symbol
                    && (normalize_unreduced || self.dags.get(arg).reduced_epoch == epoch) =>
                {
                    for &element in inner_args.iter().rev() {
                        pending.push(element);
                    }
                }
                _ => args.push(arg),
            }
        }
        if identity.is_none() {
            while args
                .first()
                .is_some_and(|&arg| left_identity.is_some_and(|id| self.is_identity(sig, id, arg)))
            {
                args.remove(0);
            }
            while args
                .last()
                .is_some_and(|&arg| right_identity.is_some_and(|id| self.is_identity(sig, id, arg)))
            {
                args.pop();
            }
        }
        match args.len() {
            0 => {
                let id = identity
                    .or(left_identity)
                    .or(right_identity)
                    .expect("an empty AU sequence requires an identity");
                self.identity_dag(sig, id)
            }
            1 => args[0],
            _ => {
                let elem_sorts: Vec<SortId> = args.iter().map(|&e| self.dags.get(e).sort).collect();
                let sort = sig.compute_sort_fold(symbol, &elem_sorts);
                self.alloc_node(sort, NodeTerm::Au { symbol, args })
            }
        }
    }

    /// Build a canonical **CUI** node from two arguments. An identity argument yields the other
    /// argument; idempotence collapses `f(a, a)` to `a`; commutative arguments are sorted. These
    /// collapses are structural and do not increment the rewrite count.
    pub(crate) fn make_cui(
        &mut self,
        sig: &Signature,
        symbol: SymbolId,
        x: DagId,
        y: DagId,
    ) -> DagId {
        self.make_cui_ordered(sig, symbol, x, y, false)
    }

    /// Pre-index normalization compares variable arguments by name because substitution slots do not exist yet.
    fn make_cui_for_unify(
        &mut self,
        sig: &Signature,
        symbol: SymbolId,
        x: DagId,
        y: DagId,
    ) -> DagId {
        self.make_cui_ordered(sig, symbol, x, y, true)
    }

    fn make_cui_ordered(
        &mut self,
        sig: &Signature,
        symbol: SymbolId,
        mut x: DagId,
        mut y: DagId,
        variables_by_name: bool,
    ) -> DagId {
        debug_assert_eq!(
            sig.symbol(symbol).theory(),
            Theory::Cui,
            "make_cui on a non-CUI symbol"
        );
        let sym = sig.symbol(symbol);
        let idem = sym.axioms.idem;
        if sym
            .left_identity()
            .is_some_and(|id| self.is_identity(sig, id, x))
        {
            return y;
        }
        if sym
            .right_identity()
            .is_some_and(|id| self.is_identity(sig, id, y))
        {
            return x;
        }
        if idem && self.dag_compare_inner(x, y, variables_by_name) == Ordering::Equal {
            return x;
        }
        if sym.axioms.comm && self.dag_compare_inner(x, y, variables_by_name) == Ordering::Greater {
            std::mem::swap(&mut x, &mut y);
        }
        let sort = sig.compute_sort(symbol, &[self.dags.get(x).sort, self.dags.get(y).sort]);
        self.alloc_node(
            sort,
            NodeTerm::Cui {
                symbol,
                args: vec![x, y],
            },
        )
    }

    /// Build a canonical **S** (`iter`) node `s^count(arg)`: zero collapses to `arg`, nested
    /// same-symbol successors combine counts, and surviving nodes use the periodic least sort.
    pub(crate) fn make_s(
        &mut self,
        sig: &Signature,
        symbol: SymbolId,
        count: Nat,
        arg: DagId,
    ) -> DagId {
        debug_assert_eq!(
            sig.symbol(symbol).theory(),
            Theory::S,
            "make_s on a non-S symbol"
        );
        if count.is_zero() {
            return arg;
        }
        let (count, arg) = match &self.dags.get(arg).term {
            NodeTerm::S {
                symbol: inner,
                count: k,
                arg: inner_arg,
            } if *inner == symbol => (count.add(k), *inner_arg),
            _ => (count, arg),
        };
        let arg_sort = self.dags.get(arg).sort;
        let sort = sig.compute_s_sort(symbol, arg_sort, &count);
        self.alloc_node(sort, NodeTerm::S { symbol, count, arg })
    }

    /// Build an atomic **NA** constant node carrying a string, quoted identifier, or float. The sort
    /// is derived from the arity-zero symbol and value.
    pub(crate) fn make_na(&mut self, sig: &Signature, symbol: SymbolId, value: NaValue) -> DagId {
        // Normalize -0.0 to +0.0 so bit-level structural equality and ordering coincide with value
        // equality.
        let value = match value {
            NaValue::Float(bits) if f64::from_bits(bits) == 0.0 => NaValue::Float(0.0f64.to_bits()),
            v => v,
        };
        let sort = sig.compute_na_sort(symbol, &value);
        self.alloc_node(sort, NodeTerm::Na { symbol, value })
    }

    /// Build a variable leaf. `symbol` identifies its sort, `name` is the interned base-name token,
    /// and `index` is the owning problem's substitution slot.
    pub(crate) fn make_var(
        &mut self,
        sig: &Signature,
        symbol: SymbolId,
        name: u32,
        index: u32,
    ) -> DagId {
        let sort = sig.symbol(symbol).decls[0].range;
        self.alloc_node(
            sort,
            NodeTerm::Var {
                symbol,
                name,
                index,
            },
        )
    }

    /// Rebuild a node for `symbol` from `children` (the flattened child sequence), dispatching on the
    /// operator's theory: a free node directly, or a canonical ACU/AU/CUI/S node. Used by `reduce` when a
    /// child changed and by `instantiate`, so neither hard-codes the free constructor (which rejects
    /// theory symbols).
    pub(crate) fn rebuild(
        &mut self,
        sig: &Signature,
        symbol: SymbolId,
        children: Vec<DagId>,
    ) -> DagId {
        match sig.symbol(symbol).theory() {
            Theory::Free => self.make_free(sig, symbol, children),
            Theory::Acu => {
                self.make_acu(sig, symbol, children.into_iter().map(|d| (d, 1)).collect())
            }
            Theory::Au => self.make_au(sig, symbol, children),
            Theory::Cui => {
                debug_assert_eq!(children.len(), 2, "a CUI node is binary");
                self.make_cui(sig, symbol, children[0], children[1])
            }
            // A fresh iter application (an `Op` layer from `instantiate`, or a builder's application) is
            // one successor; `make_s` flattening folds nested layers into a single `s^k`. Rebuilding an
            // existing S node must keep its count instead: `reduce` re-seats it directly, and splicers
            // that put a rewritten child back into its parent use [`rebuild_like`](Self::rebuild_like).
            Theory::S => {
                debug_assert_eq!(children.len(), 1, "an S successor is unary");
                self.make_s(sig, symbol, Nat::one(), children[0])
            }
        }
    }

    /// Rebuild the existing node `original` over replacement `children`. Unlike [`rebuild`](Self::rebuild),
    /// which builds a fresh application, this keeps the node's non-child state: an S node `s^n(t)` keeps
    /// its count `n` and becomes `s^n(t')` (a same-symbol S child folds in). Every other node is rebuilt
    /// by `rebuild`. Rule-position splicers use this to rebuild the ancestors of a rewritten position.
    pub(crate) fn rebuild_like(
        &mut self,
        sig: &Signature,
        original: DagId,
        children: Vec<DagId>,
    ) -> DagId {
        let symbol = self.node(original).symbol();
        if let NodeTerm::S { count, .. } = &self.node(original).term {
            debug_assert_eq!(children.len(), 1, "an S node has one child");
            let count = count.clone();
            return self.make_s(sig, symbol, count, children[0]);
        }
        self.rebuild(sig, symbol, children)
    }

    /// Whether `arg` is the constant `id_sym()` (an arity-0 free node). Used to recognise identity
    /// arguments during ACU canonicalization.
    fn is_constant(&self, arg: DagId, id_sym: SymbolId) -> bool {
        matches!(
            &self.dags.get(arg).term,
            NodeTerm::Free { symbol, args } if *symbol == id_sym && args.is_empty()
        )
    }

    /// A node's top-symbol arity: two for ACU/AU/CUI, one for S, zero for NA constants and variables,
    /// otherwise the free symbol's declared arity. This is the primary [`dag_compare`] key.
    fn node_arity(n: &DagNode) -> usize {
        match &n.term {
            NodeTerm::Free { args, .. } => args.len(),
            NodeTerm::Acu { .. } | NodeTerm::Au { .. } | NodeTerm::Cui { .. } => 2,
            NodeTerm::S { .. } => 1,
            NodeTerm::Na { .. } | NodeTerm::Var { .. } => 0,
        }
    }

    pub(crate) fn register_qid_rank(&mut self, text: &str) {
        let next = self.qid_ranks.len() as u32;
        self.qid_ranks.entry(text.to_string()).or_insert(next);
    }

    /// Compare DAGs in the runtime's total structural order. Equality agrees with
    /// [`deep_equal`](Self::deep_equal), and nested canonical elements are compared recursively.
    pub(crate) fn dag_compare(&self, a: DagId, b: DagId) -> Ordering {
        self.dag_compare_inner(a, b, false)
    }

    /// Pre-index theory-normalization comparison, using variable names before slots are assigned.
    fn dag_compare_for_unify(&self, a: DagId, b: DagId) -> Ordering {
        self.dag_compare_inner(a, b, true)
    }

    fn dag_compare_inner(&self, a: DagId, b: DagId, variables_by_name: bool) -> Ordering {
        if a == b {
            return Ordering::Equal; // same node id — identical, prune
        }
        let (na, nb) = (self.dags.get(a), self.dags.get(b));
        // Canonical symbol order is arity first, then global creation index. Mixed-arity ACU terms
        // therefore group by arity before creation order.
        match Self::node_arity(na).cmp(&Self::node_arity(nb)) {
            Ordering::Equal => {}
            ord => return ord,
        }
        // Same-sort command-subject variables order by name-token rank rather than per-command symbol
        // creation order. Cross-sort variables retain the `SymbolId` fallback.
        if na.symbol() != nb.symbol()
            && !self.var_ranks.is_empty()
            && na.sort == nb.sort
            && let (Some(&ra), Some(&rb)) = (
                self.var_ranks.get(&na.symbol()),
                self.var_ranks.get(&nb.symbol()),
            )
        {
            return ra.cmp(&rb).then_with(|| na.symbol().cmp(&nb.symbol()));
        }
        // Variables of different sorts have different per-sort symbols. Prefer their recorded lazy
        // creation rank to the SymbolId fallback so cached searches retain traversal order.
        if na.symbol() != nb.symbol()
            && matches!(na.term, NodeTerm::Var { .. })
            && matches!(nb.term, NodeTerm::Var { .. })
            && let (Some(&ra), Some(&rb)) = (
                self.sort_var_ranks.get(&na.symbol()),
                self.sort_var_ranks.get(&nb.symbol()),
            )
        {
            return ra.cmp(&rb).then_with(|| na.symbol().cmp(&nb.symbol()));
        }
        match na.symbol().cmp(&nb.symbol()) {
            Ordering::Equal => {}
            ord => return ord,
        }
        // Equal top symbols ⇒ the same theory ⇒ the same `NodeTerm` arm.
        match (&na.term, &nb.term) {
            (NodeTerm::Free { args: xa, .. }, NodeTerm::Free { args: ya, .. }) => {
                for (&x, &y) in xa.iter().zip(ya.iter()) {
                    match self.dag_compare_inner(x, y, variables_by_name) {
                        Ordering::Equal => {}
                        ord => return ord,
                    }
                }
                Ordering::Equal // same symbol ⇒ same arity ⇒ all pairs compared
            }
            // ACU nodes compare argument count first, then each pair's multiplicity before its element.
            // This keeps same-symbol nodes of different sizes in a stable enclosing canonical order.
            (NodeTerm::Acu { args: xa, .. }, NodeTerm::Acu { args: ya, .. }) => {
                match xa.len().cmp(&ya.len()) {
                    Ordering::Equal => {}
                    ord => return ord,
                }
                for (&(xe, xm), &(ye, ym)) in xa.iter().zip(ya.iter()) {
                    match xm.cmp(&ym) {
                        Ordering::Equal => {}
                        ord => return ord,
                    }
                    match self.dag_compare_inner(xe, ye, variables_by_name) {
                        Ordering::Equal => {}
                        ord => return ord,
                    }
                }
                Ordering::Equal
            }
            // AU compares length and then elements. CUI always has two arguments, so its length
            // comparison is a no-op.
            (NodeTerm::Au { args: xa, .. }, NodeTerm::Au { args: ya, .. })
            | (NodeTerm::Cui { args: xa, .. }, NodeTerm::Cui { args: ya, .. }) => {
                match xa.len().cmp(&ya.len()) {
                    Ordering::Equal => {}
                    ord => return ord,
                }
                for (&x, &y) in xa.iter().zip(ya.iter()) {
                    match self.dag_compare_inner(x, y, variables_by_name) {
                        Ordering::Equal => {}
                        ord => return ord,
                    }
                }
                Ordering::Equal
            }
            // S compares its scalar count before its argument, matching structural equality and
            // ordering iterates such as `s^2(0)` and `s^3(0)` correctly inside ACU subjects.
            (
                NodeTerm::S {
                    count: xc, arg: xa, ..
                },
                NodeTerm::S {
                    count: yc, arg: ya, ..
                },
            ) => match xc.cmp(yc) {
                Ordering::Equal => self.dag_compare_inner(*xa, *ya, variables_by_name),
                ord => ord,
            },
            // NA constants compare scalar values. Strings use signed-byte order, so a high byte sorts
            // before an ASCII byte.
            (
                NodeTerm::Na {
                    value: NaValue::Str(xs),
                    ..
                },
                NodeTerm::Na {
                    value: NaValue::Str(ys),
                    ..
                },
            ) => crate::dag::rope_cmp(xs, ys),
            (
                NodeTerm::Na {
                    value: NaValue::Qid(xs),
                    ..
                },
                NodeTerm::Na {
                    value: NaValue::Qid(ys),
                    ..
                },
            ) => match (
                self.qid_ranks.get(xs.as_ref()),
                self.qid_ranks.get(ys.as_ref()),
            ) {
                (Some(xr), Some(yr)) => xr.cmp(yr).then_with(|| xs.cmp(ys)),
                _ => xs.cmp(ys),
            },
            (NodeTerm::Na { value: xv, .. }, NodeTerm::Na { value: yv, .. }) => xv.cmp(yv),
            // Variables compare by interned name during pre-index normalization and by established
            // slot order during ordinary DAG solving.
            (
                NodeTerm::Var {
                    name: xn,
                    index: xi,
                    ..
                },
                NodeTerm::Var {
                    name: yn,
                    index: yi,
                    ..
                },
            ) => {
                if variables_by_name {
                    xn.cmp(yn)
                } else {
                    xi.cmp(yi)
                }
            }
            _ => unreachable!("equal top symbols must share a NodeTerm arm"),
        }
    }

    pub(crate) fn node(&self, id: DagId) -> &DagNode {
        self.dags.get(id)
    }
    pub(crate) fn sort_of(&self, id: DagId) -> SortId {
        self.dags.get(id).sort
    }
    /// Number of live DAG nodes (post-GC this is the reachable set).
    pub(crate) fn live_nodes(&self) -> usize {
        self.dags.len()
    }
    /// Peak DAG-arena capacity (high-water mark of allocated slots; stays bounded when GC runs).
    pub(crate) fn node_capacity(&self) -> usize {
        self.dags.capacity()
    }

    // ---- garbage collection ----

    /// Stable identity of this runtime's DAG arena/root domain. Persistent descent caches use it to
    /// discard engine-local DAG keys before servicing a different loaded module.
    pub(crate) fn context_id(&self) -> usize {
        std::rc::Rc::as_ptr(&self.roots) as usize
    }

    /// Pin `id` as a GC root for as long as the returned [`RootGuard`] lives (see [`Engine::root`]).
    pub(crate) fn root(&self, id: DagId) -> RootGuard {
        RootGuard::new(&self.roots, id)
    }

    /// Keep callback-scoped DAG handles live across a re-entrant reduction's safe-point collection.
    /// The returned index must be restored when the callback ends; nested callbacks therefore stack.
    pub(crate) fn begin_strict_callback_scope(
        &mut self,
        redex: DagId,
        arguments: &[DagId],
    ) -> Option<usize> {
        self.gc_interval.map(|_| {
            let base = self.protected.len();
            self.protected.push(redex);
            self.protected.extend_from_slice(arguments);
            base
        })
    }

    /// Add a value constructed inside the active strict callback to its scoped GC root set.
    pub(crate) fn protect_strict_callback_value(&mut self, value: DagId) {
        if self.gc_interval.is_some() {
            self.protected.push(value);
        }
    }

    /// Release the roots installed by [`Self::begin_strict_callback_scope`].
    pub(crate) fn end_strict_callback_scope(&mut self, base: usize) {
        debug_assert!(base <= self.protected.len());
        self.protected.truncate(base);
    }

    /// Collect every DAG node not reachable from a live [`RootGuard`], an engine-lifetime identity
    /// cache entry, or from `extra_roots` (see [`Engine::gc`]); returns the number reclaimed.
    pub(crate) fn gc(&mut self, extra_roots: impl IntoIterator<Item = DagId>) -> usize {
        self.dags.clear_marks();
        self.mark_registered_roots();
        self.mark_identity_roots();
        for root in extra_roots {
            self.mark_reachable(root);
        }
        self.dags.sweep(|_| {})
    }

    /// Mark (transitively) every root currently pinned by a [`RootGuard`].
    fn mark_registered_roots(&mut self) {
        // Collect first so the registry borrow is released before the `&mut self` mark walk.
        let pinned: Vec<DagId> = self.roots.borrow().live_roots().collect();
        for r in pinned {
            self.mark_reachable(r);
        }
    }

    /// Mark the normalized identity DAG cache, whose entries are permanent runtime roots.
    fn mark_identity_roots(&mut self) {
        let identity_roots: Vec<DagId> = self.identity_dags.values().copied().collect();
        for d in identity_roots {
            self.mark_reachable(d);
        }
    }

    /// Enable (or disable) safe-point GC during [`reduce`](Engine::reduce) (see
    /// [`Engine::set_gc_interval`] for the rooting contract).
    pub(crate) fn set_gc_interval(&mut self, interval: Option<u64>) {
        self.gc_interval = interval;
    }

    /// Collect at a `reduce` safe point, rooting the in-flight working set: the registry, plus every
    /// frame's term (`original`, which transitively covers its unreduced `orig` children) and its
    /// current `args` (the strategy-reduced positions are fresh nodes not reachable from `original`),
    /// plus the `child_result` not yet delivered into a frame. This is the complete loop-head root set
    /// (see the [`ReduceFrame`] safe-point contract); collecting anywhere else would miss fresh nodes
    /// living only in native-stack locals.
    fn safe_point_gc(&mut self, frames: &[ReduceFrame], child_result: Option<DagId>) {
        self.dags.clear_marks();
        self.mark_registered_roots();
        // Cached identity DAGs are engine-lifetime roots: collapse matches bind variables to them
        // (and their reduced stamps are load-bearing), so they must survive every collection.
        self.mark_identity_roots();
        for frame in frames {
            self.mark_reachable(frame.original);
            // `start` is the frame's forwarding target. After a rewrite it may be reachable only from
            // this frame, so root it until completion stores its normal form.
            self.mark_reachable(frame.start);
            for &r in &frame.args {
                self.mark_reachable(r);
            }
        }
        if let Some(r) = child_result {
            self.mark_reachable(r);
        }
        // A trace holds intermediate node ids (redex/result/bindings/subject/whole, incl. of failed
        // condition trials) for later rendering — root them all so a traced reduction under in-reduction
        // GC keeps them alive. (Collected first to release the shared borrow before `mark_reachable`
        // takes `&mut self`; `None` on the common untraced path.)
        if let Some(trace) = &self.trace {
            let mut ids: Vec<DagId> = Vec::new();
            for ev in trace {
                ev.for_each_id(|d| ids.push(d));
            }
            for id in ids {
                self.mark_reachable(id);
            }
        }
        // The outer reduction's working set is protected across any re-entrant condition reduction we
        // are nested inside (`condition_holds` pushed it). Without this a nested condition-GC would sweep
        // the outer frames' siblings / match bindings / redex. (Cloned to release the borrow before
        // `mark_reachable` takes `&mut self`; empty — a no-op — unless we are inside a condition.)
        if !self.protected.is_empty() {
            let protected = self.protected.clone();
            for id in protected {
                self.mark_reachable(id);
            }
        }
        self.dags.sweep(|_| {});
    }

    /// Iterative (stack-based) transitive marker. Marks each node **on push** (using the
    /// "newly-marked" result of [`Arena::mark`]) so a node shared by *k* parents is pushed once,
    /// keeping the work stack O(nodes) rather than O(edges); it also terminates on shared/cyclic
    /// structure.
    fn mark_reachable(&mut self, root: DagId) {
        let mut stack = Vec::new();
        // Children are collected (via the `children()` visitor) into this reused scratch buffer, then
        // marked: enumerating borrows the node (hence the arena) immutably, while marking needs the
        // arena mutably, so the two phases can't overlap. `extend` from the iterator hits a slice
        // fast-path for the free rep; a non-slice arm still works, just without the memcpy.
        let mut kids: Vec<DagId> = Vec::new();
        if self.dags.mark(root) {
            stack.push(root);
        }
        while let Some(id) = stack.pop() {
            kids.clear();
            kids.extend(self.dags.get(id).children());
            // A forwarding normal form is not a structural child; mark it explicitly so it lives with
            // the node that references it.
            if let Some(nf) = self.dags.get(id).nf {
                kids.push(nf);
            }
            for &child in &kids {
                if self.dags.mark(child) {
                    stack.push(child);
                }
            }
        }
    }

    // ---- statistics ----
    fn semantic_checkpoint(&self) -> SemanticCheckpoint {
        SemanticCheckpoint {
            rewrite_count: self.rewrite_count,
            membership_count: self.membership_count,
            rule_rewrite_count: self.rule_rewrite_count,
            variant_narrowing_count: self.variant_narrowing_count,
            narrowing_count: self.narrowing_count,
            model_check_stats_len: self.model_check_stats.len(),
            sat_solve_stats_len: self.sat_solve_stats.len(),
            trace_len: self.trace.as_ref().map(Vec::len),
        }
    }

    fn restore_semantic_checkpoint(&mut self, checkpoint: SemanticCheckpoint) {
        self.rewrite_count = checkpoint.rewrite_count;
        self.membership_count = checkpoint.membership_count;
        self.rule_rewrite_count = checkpoint.rule_rewrite_count;
        self.variant_narrowing_count = checkpoint.variant_narrowing_count;
        self.narrowing_count = checkpoint.narrowing_count;
        self.model_check_stats
            .truncate(checkpoint.model_check_stats_len);
        self.sat_solve_stats
            .truncate(checkpoint.sat_solve_stats_len);
        if let (Some(trace), Some(len)) = (&mut self.trace, checkpoint.trace_len) {
            trace.truncate(len);
        }
    }

    /// Total equational rewrites applied so far.
    pub(crate) fn rewrites(&self) -> u64 {
        self.rewrite_count
    }
    pub(crate) fn reset_rewrites(&mut self) {
        self.rewrite_count = 0;
        self.membership_count = 0;
        self.rule_rewrite_count = 0;
        self.variant_narrowing_count = 0;
        self.narrowing_count = 0;
        self.model_check_stats.clear();
        self.sat_solve_stats.clear();
    }
    /// Add `n` to the rewrite counter (a META-LEVEL descent function folding the object-level
    /// reduction's rewrites into the current command's total).
    pub(crate) fn add_rewrites(&mut self, n: u64) {
        self.rewrite_count += n;
    }
    pub(crate) fn add_variant_narrowing_subcount(&mut self, n: u64) {
        self.variant_narrowing_count += n;
    }
    pub(crate) fn add_narrowing_subcount(&mut self, n: u64) {
        self.narrowing_count += n;
    }
    pub(crate) fn rewrite_breakdown(&self) -> (u64, u64, u64, u64) {
        (
            self.membership_count,
            self.rule_rewrite_count,
            self.variant_narrowing_count,
            self.narrowing_count,
        )
    }

    pub(crate) fn reduce_or_defer_fault(
        &mut self,
        sig: &Signature,
        root: DagId,
        descent: &mut dyn DescentOps,
    ) -> DagId {
        match self.reduce(sig, root, descent) {
            Ok(result) => result,
            Err(fault) => {
                self.reducer_fault = Some(fault);
                root
            }
        }
    }

    pub(crate) fn defer_reducer_fault(&mut self, fault: ReducerFault) {
        self.reducer_fault = Some(fault);
    }

    fn check_reducer_fault(&mut self) -> Result<(), ReducerFault> {
        match self.reducer_fault.take() {
            Some(fault) => Err(fault),
            None => Ok(()),
        }
    }

    pub(crate) fn record_model_check_stats(&mut self, stats: ModelCheckStats) {
        self.model_check_stats.push(stats);
    }

    pub(crate) fn record_sat_solve_stats(&mut self, stats: SatSolveStats) {
        self.sat_solve_stats.push(stats);
    }

    // ---- reduction ----

    /// The reduction core; see [`Engine::reduce`] for the contract and the iterative-vs-recursive
    /// rationale. Reads `sig.eq_epoch()`, builds nodes via `self.make_free(sig, ..)`, and rewrites
    /// the top via `self.try_rewrite_top(sig, ..)` — all while holding only a shared borrow of `sig`.
    pub(crate) fn reduce(
        &mut self,
        sig: &Signature,
        root: DagId,
        descent: &mut dyn DescentOps,
    ) -> Result<DagId, ReducerFault> {
        self.check_reducer_fault()?;
        sig.mark_host_execution();
        if self.node(root).reduced_epoch == sig.eq_epoch() {
            // Return the recorded out-of-place normal form; `None` means the node itself is canonical.
            return Ok(self.node(root).nf.unwrap_or(root));
        }

        let mut stack: Vec<ReduceFrame> = Vec::new();
        stack.push(self.new_reduce_frame(root));
        // Carries a just-completed child's normal form up to the parent frame waiting on it.
        let mut child_result: Option<DagId> = None;

        loop {
            self.check_reducer_fault()?;
            // Invariant: `stack` is non-empty throughout the body. It starts with the root frame and
            // the only `pop` (below) is immediately followed by a `return` when it empties, so the
            // loop never re-enters with an empty stack — the `expect`s below are therefore unreachable.

            // Safe-point GC: the loop head is the *only* point during a reduction where every
            // in-flight node is discoverable (the frame stack + `child_result`); collect here when
            // allocation pressure crosses the configured interval so a large reduction stays bounded.
            if let Some(interval) = self.gc_interval
                && self.allocs_since_gc >= interval
            {
                self.safe_point_gc(&stack, child_result);
                self.allocs_since_gc = 0;
            }

            // Deliver a completed child into the Argument instruction that pushed it.
            if let Some(result) = child_result.take() {
                let frame = stack
                    .last_mut()
                    .expect("child result with empty reduce stack");
                let action = sig
                    .strat_action(frame.symbol, frame.cursor, frame.orig.len())
                    .expect("delivering a child means a strategy instruction is in progress");
                let EvalAction::Argument(position) = action else {
                    unreachable!("only an Argument strategy instruction can push a child frame");
                };
                frame.args[position] = result;
                frame.cursor += 1;
            }

            let action = {
                let frame = stack.last().expect("empty reduce stack");
                sig.strat_action(frame.symbol, frame.cursor, frame.orig.len())
                    .expect("a normalized evaluation strategy always ends in Top")
            };

            // After a Top instruction, reduce a fresh per-occurrence copy. Otherwise two physical
            // slots sharing one hash-consed redex would normalize only once. Before the first Top,
            // already-reduced shared subterms retain normal-form forwarding.
            if let EvalAction::Argument(position) = action {
                let (mut child, after_top) = {
                    let frame = stack.last().expect("empty reduce stack");
                    (frame.args[position], frame.seen_top)
                };
                if after_top
                    && matches!(
                        sig.symbol(stack.last().unwrap().symbol).theory(),
                        Theory::Acu
                    )
                {
                    // ACU stores one entry per distinct element plus a multiplicity. The generic frame
                    // expands this for rebuilding, but each distinct entry is copied and reduced once.
                    let repeated_result = {
                        let frame = stack.last().unwrap();
                        let original = frame.orig[position];
                        frame.orig[..position]
                            .iter()
                            .position(|&earlier| earlier == original)
                            .map(|earlier| frame.args[earlier])
                    };
                    if let Some(result) = repeated_result {
                        child_result = Some(result);
                        continue;
                    }
                }
                if after_top {
                    child = self.copy_reducible(sig, child);
                    stack.last_mut().expect("empty reduce stack").args[position] = child;
                }
                if self.node(child).reduced_epoch == sig.eq_epoch() {
                    child_result = Some(self.node(child).nf.unwrap_or(child));
                } else {
                    stack.push(self.new_reduce_frame(child));
                }
                continue;
            }

            let EvalAction::Top { final_step } = action else {
                unreachable!("Argument handled above");
            };

            // At the first `0`, compute true sorts for every argument, including lazy arguments this
            // strategy never reduces. Standard strategies already reach those normal-form points and
            // retain the membership-free hot path.
            let (first_top, custom_strategy) = {
                let frame = stack.last_mut().expect("empty reduce stack");
                let first = !frame.seen_top;
                frame.seen_top = true;
                (first, sig.symbol(frame.symbol).strategy.is_some())
            };
            if first_top && custom_strategy && !sig.memberships.is_empty() {
                let args = stack.last().expect("empty reduce stack").args.clone();
                let mut seen = HashSet::new();
                for arg in args {
                    self.compute_true_sort(sig, arg, &mut seen, &stack);
                }
            }

            // Materialize the application as it exists at this Top instruction. An intermediate Top
            // must retain the frame's argument vector so a failed attempt can continue with later
            // instructions; at the final Top the vector can move into the rebuild.
            let (symbol, original, args, changed, normalize_associative_at_top) = {
                let frame = stack.last_mut().expect("empty reduce stack");
                let theory = sig.symbol(frame.symbol).theory();
                let normalize_at_top =
                    first_top && custom_strategy && matches!(theory, Theory::Acu | Theory::Au);
                let mut changed = frame.args != frame.orig || normalize_at_top;
                if !changed
                    && matches!(theory, Theory::Acu | Theory::Au)
                    && frame
                        .args
                        .iter()
                        .any(|&child| self.node(child).symbol() == frame.symbol)
                {
                    // Force the deferred associative splice/merge before attempting equations.
                    changed = true;
                }
                let args = if changed {
                    if final_step {
                        std::mem::take(&mut frame.args)
                    } else {
                        frame.args.clone()
                    }
                } else {
                    Vec::new()
                };
                (
                    frame.symbol,
                    frame.original,
                    args,
                    changed,
                    normalize_at_top,
                )
            };
            let rebuilt = if !changed {
                original
            } else if normalize_associative_at_top
                && matches!(sig.symbol(symbol).theory(), Theory::Acu)
            {
                self.make_acu_at_top(sig, symbol, args)
            } else if normalize_associative_at_top
                && matches!(sig.symbol(symbol).theory(), Theory::Au)
            {
                self.make_au_at_top(sig, symbol, args)
            } else if matches!(sig.symbol(symbol).theory(), Theory::S) {
                // An S node's `count` is non-child state `rebuild` cannot recover (it would re-wrap as
                // `s^1`); preserve the original count and re-seat it over the reduced argument.
                let count = match &self.node(original).term {
                    NodeTerm::S { count, .. } => count.clone(),
                    _ => unreachable!("a Theory::S node is NodeTerm::S"),
                };
                self.make_s(sig, symbol, count, args[0])
            } else {
                self.rebuild(sig, symbol, args)
            };

            // Intermediate Top instructions exclude `[owise]`; the final Top includes it. A successful
            // attempt abandons this strategy and starts the replacement term's strategy from step 0.
            if let Some(next) = self.try_rewrite_top(sig, rebuilt, &stack, descent, final_step)? {
                self.rewrite_count += 1;
                // A rewrite result already stamped reduced terminates this position after counting the
                // rewrite. Fresh RHS nodes lack the stamp, so a self-rewrite such as `eq a = a` loops.
                if self.node(next).reduced_epoch == sig.eq_epoch() {
                    let done = self.node(next).nf.unwrap_or(next);
                    if self.record_whole && self.tracing() {
                        let before = self.reconstruct_whole(sig, &stack, rebuilt);
                        let after = self.reconstruct_whole(sig, &stack, done);
                        self.patch_whole(before, after);
                    }
                    let start = stack.last().expect("empty reduce stack").start;
                    if start != done {
                        let node = self.dags.get_mut(start);
                        node.nf = Some(done);
                        node.reduced_epoch = sig.eq_epoch();
                    }
                    stack.pop();
                    if stack.is_empty() {
                        return Ok(done);
                    }
                    child_result = Some(done);
                    continue;
                }
                // Whole tracing reconstructs the root before and after this top rewrite by threading
                // the redex and result through ancestor frames. This allocation is gated off by default.
                if self.record_whole && self.tracing() {
                    let before = self.reconstruct_whole(sig, &stack, rebuilt);
                    let after = self.reconstruct_whole(sig, &stack, next);
                    self.patch_whole(before, after);
                }
                // Reuse this frame's slot for the rewritten term, but carry `start` over: this frame's
                // forwarding target is still the node it was originally pushed for.
                let start = stack.last().expect("empty reduce stack").start;
                let mut frame = self.new_reduce_frame(next);
                frame.start = start;
                *stack.last_mut().expect("empty reduce stack") = frame;
                continue;
            }

            if !final_step {
                // The provisional top attempt failed. Continue the same strategy over the canonical
                // partially-reduced application. A theory collapse changes the root symbol, in which
                // case the collapsed term starts its own strategy instead.
                let rebuilt_symbol = self.node(rebuilt).symbol();
                let start = stack.last().expect("empty reduce stack").start;
                if rebuilt_symbol != symbol {
                    let mut frame = self.new_reduce_frame(rebuilt);
                    frame.start = start;
                    *stack.last_mut().expect("empty reduce stack") = frame;
                } else {
                    let children: Vec<DagId> = self.node(rebuilt).children().collect();
                    let frame = stack.last_mut().expect("empty reduce stack");
                    frame.original = rebuilt;
                    frame.symbol = rebuilt_symbol;
                    frame.orig = children.clone();
                    frame.args = children;
                    frame.cursor += 1;
                }
                continue;
            }

            // The final Top failed: this is the normal-form point. Recompute the base sort before
            // applying memberships because in-place child refinements do not propagate automatically.
            if !sig.memberships.is_empty() {
                let base = self.compute_base_sort(sig, rebuilt);
                self.dags.get_mut(rebuilt).sort = base;
                let whole = (self.record_whole && self.tracing())
                    .then(|| self.reconstruct_whole(sig, &stack, rebuilt));
                self.constrain_to_smaller_sort(sig, rebuilt, whole, &stack);
                self.check_reducer_fault()?;
            }

            // Stamp the canonical result and forward the frame's original `start` node to it.
            let start = stack.last().expect("empty reduce stack").start;
            {
                let node = self.dags.get_mut(rebuilt);
                node.nf = None;
                node.reduced_epoch = sig.eq_epoch();
            }
            if start != rebuilt {
                let node = self.dags.get_mut(start);
                node.nf = Some(rebuilt);
                node.reduced_epoch = sig.eq_epoch();
            }
            stack.pop();
            if stack.is_empty() {
                return Ok(rebuilt);
            }
            child_result = Some(rebuilt);
        }
    }

    /// Build a [`ReduceFrame`] at the start of `id`'s children. `start` initially names `id` and remains
    /// stable across top-rewrite replacements so normalization can update the original node's cache.
    fn new_reduce_frame(&self, id: DagId) -> ReduceFrame {
        let node = self.node(id);
        let orig: Vec<DagId> = node.children().collect();
        ReduceFrame {
            start: id,
            original: id,
            symbol: node.symbol(),
            args: orig.clone(),
            orig,
            cursor: 0,
            seen_top: false,
        }
    }

    /// Reconstruct the in-progress root by threading `leaf` through ancestor reduce frames. Each
    /// ancestor is waiting on an Argument instruction; reduced siblings are in `args`, and unvisited
    /// siblings retain their originals. Allocates O(depth), so only whole tracing calls this path.
    fn reconstruct_whole(&mut self, sig: &Signature, stack: &[ReduceFrame], leaf: DagId) -> DagId {
        let mut node = leaf;
        for frame in stack[..stack.len() - 1].iter().rev() {
            let action = sig
                .strat_action(frame.symbol, frame.cursor, frame.orig.len())
                .expect("an ancestor reduce frame has an active strategy instruction");
            let EvalAction::Argument(pos) = action else {
                unreachable!("only an Argument instruction can have a descendant frame");
            };
            let mut args = frame.args.clone();
            args[pos] = node;
            // Preserve an S node's `count` (as the reduce loop does), else `rebuild` would re-wrap `s^1`.
            node = if matches!(sig.symbol(frame.symbol).theory(), Theory::S) {
                let count = match &self.node(frame.original).term {
                    NodeTerm::S { count, .. } => count.clone(),
                    _ => unreachable!("a Theory::S frame is over an S node"),
                };
                self.make_s(sig, frame.symbol, count, args[0])
            } else {
                self.rebuild(sig, frame.symbol, args)
            };
        }
        node
    }

    /// Attach reconstructed whole-before/after terms to the most-recently recorded `Rewrite` event (the
    /// top rewrite `try_equations`/`try_special` just recorded).
    fn patch_whole(&mut self, before: DagId, after: DagId) {
        if let Some(TraceEvent::Rewrite {
            whole_before,
            whole_after,
            ..
        }) = self.trace.as_mut().and_then(|b| b.last_mut())
        {
            *whole_before = Some(before);
            *whole_after = Some(after);
        }
    }

    /// Whether the [`TraceEvent`] stream is being recorded (opt-in via [`Engine::set_trace`]).
    fn tracing(&self) -> bool {
        self.trace.is_some()
    }

    /// Push a trace event when tracing is on (a cheap `None` check otherwise).
    fn record(&mut self, ev: TraceEvent) {
        if let Some(buf) = &mut self.trace {
            buf.push(ev);
        }
    }

    /// Snapshot all substitution bindings in variable-index order for a trace event.
    fn snapshot_subst(subst: &Subst) -> Vec<Option<DagId>> {
        (0..subst.len()).map(|i| subst.get(i)).collect()
    }

    fn try_host_function(
        &mut self,
        sig: &Signature,
        redex: DagId,
        binding: HostBindingId,
    ) -> Result<Option<DagId>, ReducerFault> {
        let symbol = self.node(redex).symbol();
        let resolved = sig.host_binding(binding);
        let key = sig.host_function_key(binding);
        let epoch = sig.eq_epoch();
        let mut arguments: Vec<DagId> = self.node(redex).children().collect();
        for (position, argument) in arguments.iter_mut().enumerate() {
            let node = self.node(*argument);
            if node.reduced_epoch != epoch {
                return Err(ReducerFault::new(format!(
                    "strict callback argument {position} is not normal at the active equation epoch"
                ))
                .for_key(key));
            }
            let normal = node.nf.unwrap_or(*argument);
            let target = self.node(normal);
            if target.reduced_epoch != epoch || target.nf.is_some() {
                return Err(ReducerFault::new(format!(
                    "strict callback argument {position} has stale normal-form forwarding"
                ))
                .for_key(key));
            }
            *argument = normal;
        }
        let argument_sorts: Vec<SortId> = arguments
            .iter()
            .map(|&argument| self.node(argument).sort)
            .collect();
        let result_range = sig.compute_sort(symbol, &argument_sorts);
        debug_assert_eq!(arguments.len(), resolved.arity);
        let reducer = sig.host_reducer(binding);
        let outcome = invoke_strict(
            self,
            sig,
            redex,
            arguments,
            argument_sorts,
            result_range,
            &resolved.hooks,
            reducer,
        )
        .map(|outcome| match outcome {
            StrictOutcome::Decline => None,
            StrictOutcome::Reduced(result) => Some(built_id(result)),
        });
        // Identity construction can defer a nested fault through an infallible theory seam. Consume it
        // even when the callback also failed, and preserve that earlier fault's original host key.
        self.check_reducer_fault()?;
        let Some(result) = outcome.map_err(|fault| fault.for_key(key))? else {
            return Ok(None);
        };
        let actual = self.node(result).sort;
        let actual_kind = sig.sorts.kind_of(actual);
        let range_kind = sig.sorts.kind_of(result_range);
        if actual_kind != range_kind {
            return Err(ReducerFault::new(format!(
                "returned sort `{}` is in a different kind from selected range `{}`",
                sig.sorts.name(actual),
                sig.sorts.name(result_range)
            ))
            .for_key(key));
        }
        if actual == sig.sorts.error_sort(actual_kind) {
            return Err(ReducerFault::new(format!(
                "returned the error sort for kind `{}`",
                sig.sorts.name(result_range)
            ))
            .for_key(key));
        }
        if !sig.sorts.leq(actual, result_range) {
            return Err(ReducerFault::new(format!(
                "returned sort `{}` is not below selected range `{}`",
                sig.sorts.name(actual),
                sig.sorts.name(result_range)
            ))
            .for_key(key));
        }
        Ok(Some(result))
    }

    fn try_rewrite_top(
        &mut self,
        sig: &Signature,
        id: DagId,
        frames: &[ReduceFrame],
        descent: &mut dyn DescentOps,
        final_step: bool,
    ) -> Result<Option<DagId>, ReducerFault> {
        let symbol = self.node(id).symbol();
        if let Some(op) = sig.symbol(symbol).special() {
            let (result, host_binding) = match op {
                SpecialOp::HostFunction(binding) => {
                    debug_assert!(
                        final_step,
                        "validated strict host bindings have one final Top instruction"
                    );
                    (self.try_host_function(sig, id, *binding)?, Some(*binding))
                }
                _ => (self.try_special(sig, id, op, descent)?, None),
            };
            self.check_reducer_fault()?;
            if let Some(result) = result {
                if self.tracing() {
                    let depth = self.condition_depth;
                    let host_key =
                        host_binding.map(|binding| sig.host_function_key(binding).clone());
                    self.record(TraceEvent::Rewrite {
                        kind: if host_binding.is_some() {
                            RewriteKind::HostFunction
                        } else {
                            RewriteKind::BuiltIn
                        },
                        eq_id: None,
                        host_key,
                        depth,
                        redex: id,
                        result,
                        bindings: Vec::new(),
                        whole_before: None,
                        whole_after: None,
                    });
                }
                return Ok(Some(result));
            }
            // A branch operator's first Top is selection-only. If no test matches, reduce every
            // remaining branch before trying user equations.
            if !final_step && matches!(op, SpecialOp::Branch { .. }) {
                return Ok(None);
            }
        }
        // ACU/AU/S/CUI rewriting matches *modulo* the axioms with extension: a pattern may match a
        // sub-multiset (ACU), a contiguous sub-sequence (AU), a successor prefix `s^k` of an `s^n`
        // subject (S), or — for a CUI op with identity — a single argument via pattern collapse,
        // leaving a residue to splice back. The free theory matches the whole node.
        let ext_allowed = matches!(
            sig.symbol(symbol).theory(),
            Theory::Acu | Theory::Au | Theory::S | Theory::Cui
        );
        let Some(eqs) = sig.equations.get(&symbol) else {
            return Ok(None);
        };
        // Intermediate `0` instructions try ordinary equations only; the final `0` adds `[owise]`
        // fallbacks. A branch operator's selection-only Top returned above before either class.
        if let Some(result) = self.try_equations(sig, id, eqs, ext_allowed, false, frames)? {
            return Ok(Some(result));
        }
        if final_step {
            self.try_equations(sig, id, eqs, ext_allowed, true, frames)
        } else {
            Ok(None)
        }
    }

    /// Try one equation class (`owise == false` for ordinary equations, `true` for fallbacks) against
    /// `id`, returning the first applicable rewrite. Each compiled matcher yields a solution stream;
    /// conditional failure backtracks to the next solution. The shared signature borrow keeps the rhs
    /// available for direct instantiation without cloning it.
    fn try_equations(
        &mut self,
        sig: &Signature,
        id: DagId,
        eqs: &[CompiledEquation],
        ext_allowed: bool,
        owise: bool,
        frames: &[ReduceFrame],
    ) -> Result<Option<DagId>, ReducerFault> {
        let mut subst = Subst::new();
        for eq in eqs {
            if eq.owise != owise {
                continue; // wrong phase
            }
            // First applicable solution wins (`Flow::Stop`): equational reduction takes the first
            // equation whose lhs matches and whose condition holds.
            let result = self.drive_match(
                sig,
                id,
                &eq.lhs,
                eq.nr_vars,
                &eq.condition,
                &eq.rhs,
                eq.rhs_shares,
                &eq.lhs_reuse,
                ext_allowed,
                &mut subst,
                StmtCtx {
                    kind: StmtKind::Equation,
                    stmt_id: eq.id,
                    frames,
                    redex: id,
                },
                &mut |_, _| Flow::Stop,
            )?;
            if result.is_some() {
                return Ok(result);
            }
        }
        Ok(None)
    }

    /// Drive one equation or rule as a matcher solution stream. Each candidate must satisfy the
    /// condition before rhs construction and theory-specific residue reconstruction. The callback
    /// selects first-applicable behavior or complete successor enumeration.
    #[allow(clippy::too_many_arguments)]
    fn drive_match(
        &mut self,
        sig: &Signature,
        subject: DagId,
        lhs: &LhsAutomaton,
        nr_vars: u32,
        condition: &[CompiledFragment],
        rhs: &Term,
        rhs_shares: bool,
        lhs_reuse: &[Term],
        ext_allowed: bool,
        subst: &mut Subst,
        ctx: StmtCtx<'_>,
        accept: &mut dyn FnMut(&mut Runtime, DagId) -> Flow,
    ) -> Result<Option<DagId>, ReducerFault> {
        subst.reset(nr_vars);
        let Some(mut sp) = lhs.match_(self, sig, subject, subst, ext_allowed, false) else {
            return Ok(None);
        };
        self.check_reducer_fault()?;
        let rewrite_kind = match ctx.kind {
            StmtKind::Equation => RewriteKind::Equation,
            StmtKind::Rule => RewriteKind::Rule,
            StmtKind::Membership => unreachable!("memberships are not driven through drive_match"),
        };
        while sp.next(self, sig, subst) {
            // Conditional statements: each matcher solution is a *trial* — evaluate the condition, and on
            // failure backtrack into the next solution. Unconditional statements short-circuit (no call)
            // — the free reduce hot path.
            if !condition.is_empty() {
                let depth = self.condition_depth;
                if self.tracing() {
                    let bindings = Self::snapshot_subst(subst);
                    self.record(TraceEvent::TrialStart {
                        kind: ctx.kind,
                        stmt_id: ctx.stmt_id,
                        depth,
                        bindings,
                    });
                }
                let holds = self.condition_holds(
                    sig,
                    condition,
                    subst,
                    ctx.kind,
                    ctx.stmt_id,
                    ctx.frames,
                    ctx.redex,
                )?;
                if self.tracing() {
                    self.record(TraceEvent::TrialEnd {
                        kind: ctx.kind,
                        depth,
                        success: holds,
                    });
                }
                if !holds {
                    continue;
                }
            }
            // Reuse structurally repeated RHS subterms. Distinct expressions that instantiate to equal
            // values remain distinct so physical-occurrence rewrite accounting stays intact.
            let reuse = self.find_reduced_instances(sig, subject, lhs_reuse, subst);
            let built = match (rhs_shares, reuse.is_empty()) {
                (true, true) => self.instantiate_cse(sig, rhs, subst),
                (false, true) => self.instantiate(sig, rhs, subst),
                (true, false) => self.instantiate_cse_reusing(sig, rhs, subst, &reuse),
                (false, false) => self.instantiate_reusing(sig, rhs, subst, &reuse),
            };
            let result = sp.build_result(self, sig, built);
            if self.tracing() {
                let depth = self.condition_depth;
                let bindings = Self::snapshot_subst(subst);
                self.record(TraceEvent::Rewrite {
                    kind: rewrite_kind,
                    eq_id: Some(ctx.stmt_id),
                    host_key: None,
                    depth,
                    redex: ctx.redex,
                    result,
                    bindings,
                    whole_before: None,
                    whole_after: None,
                });
            }
            match accept(self, result) {
                Flow::Stop => return Ok(Some(result)),
                Flow::Continue => {}
            }
        }
        self.check_reducer_fault()?;
        Ok(None)
    }

    fn smt_conjoin(
        &mut self,
        sig: &Signature,
        left: Option<DagId>,
        right: DagId,
    ) -> Result<Option<DagId>, ()> {
        let Some(left) = left else {
            return Ok(Some(right));
        };
        let conjunction = sig.smt_info.conjunction().ok_or(())?;
        Ok(Some(self.make_free(sig, conjunction, vec![left, right])))
    }

    /// Instantiate equality condition fragments into one SMT conjunction. `None` is the optimized
    /// representation of `true`; non-equality fragments or missing equality metadata reject the rule.
    fn smt_condition_constraint(
        &mut self,
        sig: &Signature,
        condition: &[ConditionFragment],
        subst: &Subst,
    ) -> Result<Option<DagId>, ()> {
        let true_symbol = sig.smt_info.true_symbol().ok_or(())?;
        let mut constraint = None;
        for fragment in condition {
            let ConditionFragment::Equality { lhs, rhs } = fragment else {
                return Err(());
            };
            let lhs = self.instantiate(sig, lhs, subst);
            let rhs = self.instantiate(sig, rhs, subst);
            if self.deep_equal(lhs, rhs) {
                continue;
            }
            let clause = if self.node(rhs).symbol() == true_symbol {
                lhs
            } else if self.node(lhs).symbol() == true_symbol {
                rhs
            } else {
                let lhs_kind = sig.sorts.kind_of(self.node(lhs).sort);
                let rhs_kind = sig.sorts.kind_of(self.node(rhs).sort);
                if lhs_kind != rhs_kind {
                    return Err(());
                }
                let equality = sig.smt_info.equality(lhs_kind).ok_or(())?;
                self.make_free(sig, equality, vec![lhs, rhs])
            };
            constraint = self.smt_conjoin(sig, constraint, clause)?;
        }
        Ok(constraint)
    }

    /// Enumerate every non-extension root rewrite modulo SMT in source rule/matcher order. Unbound rule
    /// variables are replaced by fresh `#n-source` variables; numbering starts above the parent state's
    /// `avoid_variable_number`, independently on each branch.
    fn smt_state_successors(
        &mut self,
        sig: &Signature,
        state: DagId,
        avoid_variable_number: &Nat,
        next_variable_slot: &mut u32,
    ) -> Vec<RawSmtSuccessor> {
        let symbol = self.node(state).symbol();
        let Some(rules) = sig.smt_rules.get(&symbol) else {
            return Vec::new();
        };
        let mut out = Vec::new();
        let mut subst = Subst::new();
        for rule in rules {
            subst.reset(rule.nr_vars);
            let Some(mut matching) = rule.lhs.match_(self, sig, state, &mut subst, false, false)
            else {
                continue;
            };
            while matching.next(self, sig, &mut subst) {
                let mut fresh_number = avoid_variable_number.clone();
                let mut fresh_slots = Vec::new();
                let mut fresh_names = Vec::new();
                for slot in 0..rule.nr_vars {
                    if subst.get(slot).is_some() {
                        continue;
                    }
                    fresh_number = fresh_number.add(&Nat::one());
                    let sort = rule.variable_sorts[slot as usize];
                    let variable_symbol = sig.var_symbols[&sort];
                    let dag_slot = *next_variable_slot;
                    *next_variable_slot = next_variable_slot
                        .checked_add(1)
                        .expect("SMT-search variable slot overflow");
                    let name_code = 0x8000_0000u32
                        .checked_add(dag_slot)
                        .expect("SMT-search variable name overflow");
                    let variable = self.make_var(sig, variable_symbol, name_code, dag_slot);
                    subst.bind(slot, variable);
                    fresh_slots.push(slot);
                    let source = rule.variable_names[slot as usize]
                        .split_once(':')
                        .map_or(rule.variable_names[slot as usize].as_str(), |(base, _)| {
                            base
                        });
                    fresh_names
                        .push((dag_slot, format!("#{}-{source}", fresh_number.to_decimal())));
                }

                if let Ok(local_constraint) =
                    self.smt_condition_constraint(sig, &rule.condition, &subst)
                {
                    let term = self.instantiate(sig, &rule.rhs, &subst);
                    out.push(RawSmtSuccessor {
                        term,
                        local_constraint,
                        avoid_variable_number: fresh_number,
                        fresh_names,
                    });
                }
                for slot in fresh_slots {
                    subst.unbind(slot);
                }
            }
        }
        out
    }

    fn smt_goal_matches(
        &mut self,
        sig: &Signature,
        goal: &LhsAutomaton,
        nr_vars: u32,
        smt_variables: &[(u32, DagId)],
        state: DagId,
    ) -> Vec<RawSmtGoalMatch> {
        let mut subst = Subst::new();
        subst.reset(nr_vars);
        let Some(mut matching) = goal.match_(self, sig, state, &mut subst, false, false) else {
            return Vec::new();
        };
        let mut out = Vec::new();
        while matching.next(self, sig, &mut subst) {
            let Some(bindings) = (0..nr_vars)
                .map(|slot| subst.get(slot))
                .collect::<Option<Vec<_>>>()
            else {
                continue;
            };
            let mut match_constraint = None;
            let mut valid = true;
            for &(slot, variable) in smt_variables {
                let value = bindings[slot as usize];
                let kind = sig.sorts.kind_of(self.node(variable).sort);
                let Some(equality) = sig.smt_info.equality(kind) else {
                    valid = false;
                    break;
                };
                let clause = self.make_free(sig, equality, vec![variable, value]);
                match self.smt_conjoin(sig, match_constraint, clause) {
                    Ok(next) => match_constraint = next,
                    Err(()) => {
                        valid = false;
                        break;
                    }
                }
            }
            if valid {
                out.push(RawSmtGoalMatch {
                    bindings,
                    match_constraint,
                });
            }
        }
        out
    }

    /// Apply the first rule at `node`, round-robin from the per-symbol cursor. The cursor advances past
    /// the rule that fires, and the rewrite contributes to the global count. Conditional rules use the
    /// same matching and condition evaluator as equations.
    fn apply_first_rule_at(
        &mut self,
        sig: &Signature,
        node: DagId,
        cursors: &mut HashMap<SymbolId, u32>,
    ) -> Result<Option<(u32, DagId)>, ReducerFault> {
        self.apply_first_rule_filtered(sig, node, cursors, None)
    }

    /// As [`apply_first_rule_at`](Self::apply_first_rule_at), optionally restricted to one `erewrite`
    /// class: object-message rules or generic leftovers. `None` considers every rule.
    fn apply_first_rule_filtered(
        &mut self,
        sig: &Signature,
        node: DagId,
        cursors: &mut HashMap<SymbolId, u32>,
        filter: Option<RuleFilter>,
    ) -> Result<Option<(u32, DagId)>, ReducerFault> {
        let symbol = self.node(node).symbol();
        let Some(rules) = sig.rules.get(&symbol) else {
            return Ok(None);
        };
        let n = rules.len();
        if n == 0 {
            return Ok(None);
        }
        // Rules of ACU/AU/S symbols match *modulo* the axioms with extension (a sub-multiset / contiguous
        // sub-sequence / successor prefix), exactly as equations do (try_rewrite_top).
        let ext_allowed = matches!(
            sig.symbol(symbol).theory(),
            Theory::Acu | Theory::Au | Theory::S
        );
        let start = (*cursors.get(&symbol).unwrap_or(&0) as usize) % n;
        let mut subst = Subst::new();
        for k in 0..n {
            let idx = (start + k) % n;
            let rule = &rules[idx];
            // Skip rules outside the requested `erewrite` class (object-message vs leftOver).
            match filter {
                Some(RuleFilter::ObjectMessage)
                    if !matches!(rule.oo, OoRuleKind::ObjectMessage(_)) =>
                {
                    continue;
                }
                Some(RuleFilter::LeftOver) if rule.oo != OoRuleKind::LeftOver => continue,
                _ => {}
            }
            // Rule application happens outside `reduce`, so there are no outer reduce frames to root for a
            // conditional rule's re-entrant condition reduction; the caller keeps the whole term rooted
            // (and the REPL runs with GC off), so an empty frame slice is correct here.
            let result = self.drive_match(
                sig,
                node,
                &rule.lhs,
                rule.nr_vars,
                &rule.condition,
                &rule.rhs,
                rule.rhs_shares,
                &[],
                ext_allowed,
                &mut subst,
                StmtCtx {
                    kind: StmtKind::Rule,
                    stmt_id: rule.id,
                    frames: &[],
                    redex: node,
                },
                &mut |_, _| Flow::Stop,
            )?;
            if let Some(result) = result {
                let rule_id = rule.id;
                self.rewrite_count += 1;
                self.rule_rewrite_count += 1;
                cursors.insert(symbol, ((idx + 1) % n) as u32);
                return Ok(Some((rule_id, result)));
            }
        }
        Ok(None)
    }

    /// Find the first rewritable position in top-down breadth-first order and apply one rule there.
    /// Returns the rebuilt root, or `None` when no rule applies anywhere. Positions and rules retain
    /// their stack/declaration order.
    fn rewrite_step(
        &mut self,
        sig: &Signature,
        root: DagId,
        cursors: &mut HashMap<SymbolId, u32>,
    ) -> Result<Option<DagId>, ReducerFault> {
        let mut stack = vec![RedexPos {
            node: root,
            parent: usize::MAX,
            arg_index: 0,
        }];
        let mut next_to_explore = 0usize;
        let mut i = 0usize;
        loop {
            if i == stack.len() {
                // No pending position at the current frontier — stack the next node's children, skipping
                // childless leaves, until the stack grows or every node has been explored.
                loop {
                    if next_to_explore == stack.len() {
                        return Ok(None); // every position explored; no rule applies (a normal form)
                    }
                    let parent_idx = next_to_explore;
                    let d = stack[parent_idx].node;
                    let before = stack.len();
                    let sym = self.node(d).symbol();
                    let children: Vec<DagId> = self.node(d).children().collect();
                    for (ai, c) in children.into_iter().enumerate() {
                        if sig.symbol(sym).is_frozen_arg(ai) {
                            continue; // frozen blocks rule application below (same check as frewrite;
                            // equational reduction is untouched)
                        }
                        stack.push(RedexPos {
                            node: c,
                            parent: parent_idx,
                            arg_index: ai,
                        });
                    }
                    next_to_explore += 1;
                    if stack.len() > before {
                        break; // grew the stack — new positions to try
                    }
                }
            }
            let node = stack[i].node;
            // A `counter` redex fires like a rule at this (top-down-first) position.
            if let Some(result) = self.try_counter(sig, node) {
                return Ok(Some(self.rebuild_path(sig, &stack, i, result)));
            }
            if let Some((_rule_id, result)) = self.apply_first_rule_at(sig, node, cursors)? {
                return Ok(Some(self.rebuild_path(sig, &stack, i, result)));
            }
            i += 1;
        }
    }

    /// The argument positions below `node` that a rule-position enumerator visits, as
    /// `(physical child index, child)` pairs in [`children`](DagNode::children) order. Physical
    /// indices for which `frozen` holds are omitted.
    ///
    /// Below an ACU node, the copies of a repeated element are one position: rewriting any copy yields
    /// the same multiset. Each entry is therefore addressed once, through its first non-frozen copy.
    /// An entry structurally equal to the previously yielded one is skipped as well; this covers equal
    /// elements that construction has not merged yet. Equal entries are normally adjacent in the
    /// canonical order. If an equal entry is not adjacent, it stays a redundant position, which can
    /// repeat a result but never loses one. The arguments of every other theory are separate
    /// positions, even when they are equal or one shared node. Callers splice a result back through
    /// the physical index.
    pub(crate) fn redex_arguments(
        &self,
        node: DagId,
        frozen: impl Fn(usize) -> bool,
    ) -> Vec<(usize, DagId)> {
        match &self.node(node).term {
            NodeTerm::Acu { args, .. } => {
                let mut arguments: Vec<(usize, DagId)> = Vec::with_capacity(args.len());
                let mut offset = 0usize;
                for &(element, multiplicity) in args {
                    let copies = offset..offset + multiplicity as usize;
                    offset = copies.end;
                    let Some(index) = copies.into_iter().find(|&index| !frozen(index)) else {
                        continue; // every copy is frozen
                    };
                    let repeated = arguments.last().is_some_and(|&(_, previous)| {
                        previous == element || self.deep_equal(previous, element)
                    });
                    if !repeated {
                        arguments.push((index, element));
                    }
                }
                arguments
            }
            _ => self
                .node(node)
                .children()
                .enumerate()
                .filter(|&(index, _)| !frozen(index))
                .collect(),
        }
    }

    /// Rebuild from a rewritten position to the root, replacing the path argument at each ancestor
    /// while preserving all other children by sharing. An iter ancestor keeps its count.
    fn rebuild_path(
        &mut self,
        sig: &Signature,
        stack: &[RedexPos],
        leaf_idx: usize,
        new_node: DagId,
    ) -> DagId {
        let mut node = new_node;
        let mut idx = leaf_idx;
        while stack[idx].parent != usize::MAX {
            let parent_idx = stack[idx].parent;
            let arg_index = stack[idx].arg_index;
            let parent_node = stack[parent_idx].node;
            let mut args: Vec<DagId> = self.node(parent_node).children().collect();
            args[arg_index] = node;
            node = self.rebuild_like(sig, parent_node, args);
            idx = parent_idx;
        }
        node
    }

    /// Materialize one state's raw rule results while deferring the equational work spent finding
    /// them. `StateGraph` replays each prefix when its result is consumed and the tail only when the
    /// caller proves exhaustion, without retaining matcher borrows across graph calls.
    pub(crate) fn state_successors_deferred(
        &mut self,
        sig: &Signature,
        root: DagId,
    ) -> Result<RawSuccessors, ReducerFault> {
        let checkpoint = self.semantic_checkpoint();
        let result = self.state_successors_deferred_inner(sig, root, checkpoint.rewrite_count);
        if result.is_err() {
            self.restore_semantic_checkpoint(checkpoint);
        }
        result
    }

    fn state_successors_deferred_inner(
        &mut self,
        sig: &Signature,
        root: DagId,
        count_start: u64,
    ) -> Result<RawSuccessors, ReducerFault> {
        self.check_reducer_fault()?;
        let mut last_count = count_start;
        let mut entries = Vec::new();

        // Enumerate all non-frozen positions (a flattened parent/arg-index list for the path rebuild).
        let mut positions = vec![RedexPos {
            node: root,
            parent: usize::MAX,
            arg_index: 0,
        }];
        let mut i = 0;
        while i < positions.len() {
            let node = positions[i].node;
            let symbol = self.node(node).symbol();
            let children: Vec<DagId> = self.node(node).children().collect();
            for (ai, c) in children.into_iter().enumerate() {
                if !sig.symbol(symbol).is_frozen_arg(ai) {
                    positions.push(RedexPos {
                        node: c,
                        parent: i,
                        arg_index: ai,
                    });
                }
            }
            i += 1;
        }

        // At each position, collect every (rule, result), splicing the result back to the root.
        for pos_idx in 0..positions.len() {
            let node = positions[pos_idx].node;
            let mut local: Vec<(u32, DagId, u64, RootGuard)> = Vec::new();
            self.all_successors_at(sig, node, &mut local)?;
            self.check_reducer_fault()?;
            for (rule_id, result, count_after_match, _result_root) in local {
                let spliced = self.rebuild_path(sig, &positions, pos_idx, result);
                self.check_reducer_fault()?;
                entries.push(RawSuccessor {
                    rule_id,
                    term: spliced,
                    enumeration_rewrites: count_after_match - last_count,
                    _root: self.root(spliced),
                });
                last_count = count_after_match;
            }
        }

        self.check_reducer_fault()?;
        let tail_rewrites = self.rewrite_count - last_count;
        self.rewrite_count = count_start;
        Ok(RawSuccessors {
            entries,
            tail_rewrites,
        })
    }

    pub(crate) fn reduce_graph_successor(
        &mut self,
        sig: &Signature,
        successor: DagId,
        descent: &mut dyn DescentOps,
    ) -> Result<DagId, ReducerFault> {
        self.rewrite_count += 1;
        self.rule_rewrite_count += 1;
        self.reduce(sig, successor, descent)
    }

    /// Every `(rule_id, result, enumeration_rewrite_count, root)` from applying any of `node`'s rules
    /// (every matcher solution) at `node` itself. The count snapshot lets the state graph defer
    /// condition reductions until it consumes that result; the root keeps earlier results alive while
    /// the matcher continues enumerating.
    fn all_successors_at(
        &mut self,
        sig: &Signature,
        node: DagId,
        out: &mut Vec<(u32, DagId, u64, RootGuard)>,
    ) -> Result<(), ReducerFault> {
        let symbol = self.node(node).symbol();
        let Some(rules) = sig.rules.get(&symbol) else {
            return Ok(());
        };
        let ext_allowed = matches!(
            sig.symbol(symbol).theory(),
            Theory::Acu | Theory::Au | Theory::S
        );
        let mut subst = Subst::new();
        for rule in rules {
            let rid = rule.id;
            self.drive_match(
                sig,
                node,
                &rule.lhs,
                rule.nr_vars,
                &rule.condition,
                &rule.rhs,
                rule.rhs_shares,
                &[],
                ext_allowed,
                &mut subst,
                StmtCtx {
                    kind: StmtKind::Rule,
                    stmt_id: rule.id,
                    frames: &[],
                    redex: node,
                },
                &mut |rt, result| {
                    // The rule itself is counted when the graph commits this result. Preserve the
                    // equation work spent finding it as an absolute snapshot for prefix differencing.
                    out.push((rid, result, rt.rewrite_count, rt.root(result)));
                    Flow::Continue
                },
            )?;
        }
        Ok(())
    }

    /// A structural hash of the DAG at `id`, **consistent with [`deep_equal`](Self::deep_equal)**: equal
    /// terms hash equal (the hash-cons contract for `search` states). Iterative post-order with a per-call
    /// memo (so shared subterms hash once and deep terms don't overflow). Mixes the symbol, the scalar
    /// payload `deep_equal` special-cases (S `count` / NA `value`, via [`DagNode::repr`]), and the child
    /// hashes in canonical order.
    pub(crate) fn dag_hash(&self, id: DagId) -> u64 {
        use crate::dag::NodeRepr;
        use std::collections::hash_map::DefaultHasher;
        use std::hash::{Hash, Hasher};
        let mut memo: HashMap<DagId, u64> = HashMap::new();
        let mut stack: Vec<(DagId, bool)> = vec![(id, false)];
        while let Some((nid, processed)) = stack.pop() {
            if memo.contains_key(&nid) {
                continue;
            }
            let node = self.node(nid);
            if !processed {
                stack.push((nid, true));
                for c in node.children() {
                    if !memo.contains_key(&c) {
                        stack.push((c, false));
                    }
                }
            } else {
                let mut h = DefaultHasher::new();
                node.symbol().hash(&mut h);
                match node.repr() {
                    NodeRepr::App => {}
                    NodeRepr::Iter { count, .. } => count.hash(&mut h),
                    NodeRepr::Str(s) => s.hash(&mut h),
                    NodeRepr::Qid(q) => q.hash(&mut h),
                    NodeRepr::Float(f) => f.to_bits().hash(&mut h),
                    NodeRepr::SmtNum(number) => number.hash(&mut h),
                    NodeRepr::Var { name } => name.hash(&mut h),
                }
                for c in node.children() {
                    memo[&c].hash(&mut h);
                }
                memo.insert(nid, h.finish());
            }
        }
        memo[&id]
    }

    /// Enumerate goal matches whose `such_that` condition holds. Each result contains bindings for goal
    /// variables `0..nr_vars` and the rewrite count after condition evaluation.
    fn eval_goal(
        &mut self,
        sig: &Signature,
        goal: &LhsAutomaton,
        nr_vars: u32,
        such_that: &[CompiledFragment],
        state: DagId,
    ) -> Result<Vec<(Vec<DagId>, u64)>, ReducerFault> {
        let mut solutions = Vec::new();
        let mut subst = Subst::new();
        subst.reset(nr_vars);
        let Some(mut sp) = goal.match_(self, sig, state, &mut subst, false, false) else {
            return Ok(solutions);
        };
        while sp.next(self, sig, &mut subst) {
            if self.condition_holds(sig, such_that, &mut subst, StmtKind::Rule, 0, &[], state)? {
                // Snapshot after the `such that` condition's equational reductions so the accepted
                // solution includes their rewrite count. An empty condition has no cost.
                let bindings = (0..nr_vars)
                    .map(|k| subst.get(k).expect("goal variable bound"))
                    .collect();
                solutions.push((bindings, self.rewrites()));
            }
        }
        Ok(solutions)
    }

    /// Evaluate every condition fragment under a matched substitution.
    ///
    /// Fragment evaluation may re-enter reduction. Before doing so, protect the outer frames,
    /// substitution bindings, and redex because a nested GC sees only its own reduction stack. Nested
    /// conditions stack and then remove their own protected roots.
    #[allow(clippy::too_many_arguments)]
    fn condition_holds(
        &mut self,
        sig: &Signature,
        condition: &[CompiledFragment],
        subst: &mut Subst,
        kind: StmtKind,
        stmt_id: u32,
        frames: &[ReduceFrame],
        redex: DagId,
    ) -> Result<bool, ReducerFault> {
        if condition.is_empty() {
            return Ok(true);
        }
        // Every rewrite-condition recursion cycle passes through here. Grow the stack on demand so an
        // unbounded recursive condition remains heap-growing and externally interruptible rather than
        // aborting the process on native call-stack overflow.
        stacker::maybe_grow(128 * 1024, 8 * 1024 * 1024, || {
            self.condition_holds_inner(sig, condition, subst, kind, stmt_id, frames, redex)
        })
    }

    #[allow(clippy::too_many_arguments)]
    fn condition_holds_inner(
        &mut self,
        sig: &Signature,
        condition: &[CompiledFragment],
        subst: &mut Subst,
        kind: StmtKind,
        stmt_id: u32,
        frames: &[ReduceFrame],
        redex: DagId,
    ) -> Result<bool, ReducerFault> {
        let restore = self.gc_interval.is_some().then(|| {
            let base = self.protected.len();
            for f in frames {
                self.protected.push(f.original);
                self.protected.push(f.start); // normal-form forwarding target
                self.protected.extend_from_slice(&f.args);
            }
            for i in 0..subst.len() {
                if let Some(b) = subst.get(i) {
                    self.protected.push(b);
                }
            }
            self.protected.push(redex);
            base
        });
        let holds = self.solve_condition(sig, condition, 0, subst, kind, stmt_id);
        if let Some(base) = restore {
            self.protected.truncate(base);
        }
        holds
    }
    fn reduce_condition_term(
        &mut self,
        sig: &Signature,
        term: DagId,
    ) -> Result<DagId, ReducerFault> {
        self.condition_depth += 1;
        let result = self.reduce(sig, term, &mut NullDescent);
        self.condition_depth -= 1;
        result
    }

    /// Record a condition fragment's end, including the resulting substitution on success.
    fn end_fragment(
        &mut self,
        kind: StmtKind,
        stmt_id: u32,
        index: usize,
        depth: u32,
        success: bool,
        subst: &Subst,
    ) {
        if self.tracing() {
            let bindings = if success {
                Self::snapshot_subst(subst)
            } else {
                Vec::new()
            };
            self.record(TraceEvent::FragmentEnd {
                kind,
                stmt_id,
                index: index as u32,
                depth,
                success,
                bindings,
            });
        }
    }

    /// Emit the trace-only revisit of a deterministic equality or sort-test fragment while
    /// backtracking. Recursive solving unwinds rather than evaluating that no-second-solution attempt,
    /// so this records the corresponding start and failure without changing search, counts, or bindings.
    fn trace_deterministic_backtrack(
        &mut self,
        kind: StmtKind,
        stmt_id: u32,
        i: usize,
        depth: u32,
    ) {
        self.record(TraceEvent::FragmentStart {
            kind,
            stmt_id,
            index: i as u32,
            depth,
            first_attempt: false,
        });
        self.record(TraceEvent::FragmentEnd {
            kind,
            stmt_id,
            index: i as u32,
            depth,
            success: false,
            bindings: Vec::new(),
        });
    }

    /// Satisfy `condition[i..]` under `subst` with backtracking. Equality fragments reduce and compare
    /// both sides; sort tests reduce and inspect the least sort; matching fragments reduce the subject
    /// and enumerate pattern solutions. Re-entrant reductions contribute to the command total.
    /// Matching fragments clear their fresh variables before each attempt; accepted bindings remain
    /// available to RHS construction.
    #[allow(clippy::too_many_arguments)]
    fn solve_condition(
        &mut self,
        sig: &Signature,
        condition: &[CompiledFragment],
        i: usize,
        subst: &mut Subst,
        kind: StmtKind,
        stmt_id: u32,
    ) -> Result<bool, ReducerFault> {
        let Some(frag) = condition.get(i) else {
            return Ok(true); // every fragment satisfied
        };
        let depth = self.condition_depth;
        // Record the first attempt. A matching fragment may emit another start event when backtracking
        // asks it for another solution.
        if self.tracing() {
            self.record(TraceEvent::FragmentStart {
                kind,
                stmt_id,
                index: i as u32,
                depth,
                first_attempt: true,
            });
        }
        // The fragment's own reduction is one condition-level deeper, so its rewrites are tagged
        // `depth + 1` (gated by `set trace condition`).
        match frag {
            CompiledFragment::Equality { lhs, rhs } => {
                // Reduce each side while pinning the reduced `l` across `r`'s reduction. Under
                // in-reduction GC, `l` is live only in this native local while `r` reduces.
                let l = self.instantiate(sig, lhs, subst);
                let l = self.reduce_condition_term(sig, l)?;
                let _root_l = self.root(l);
                let r = self.instantiate(sig, rhs, subst);
                let r = self.reduce_condition_term(sig, r)?;
                let holds = self.deep_equal(l, r);
                self.end_fragment(kind, stmt_id, i, depth, holds, subst);
                if !holds {
                    return Ok(false);
                }
                if self.solve_condition(sig, condition, i + 1, subst, kind, stmt_id)? {
                    return Ok(true);
                }
                // A later fragment failed; trace deterministic backtracking without changing search or counts.
                self.trace_deterministic_backtrack(kind, stmt_id, i, depth);
                Ok(false)
            }
            CompiledFragment::SortTest { term, sort } => {
                let term = self.instantiate(sig, term, subst);
                let term = self.reduce_condition_term(sig, term)?;
                let holds = sig.sorts().leq(self.node(term).sort, *sort);
                self.end_fragment(kind, stmt_id, i, depth, holds, subst);
                if !holds {
                    return Ok(false);
                }
                if self.solve_condition(sig, condition, i + 1, subst, kind, stmt_id)? {
                    return Ok(true);
                }
                self.trace_deterministic_backtrack(kind, stmt_id, i, depth);
                Ok(false)
            }
            CompiledFragment::Matching {
                pattern,
                subject,
                fresh_vars,
            } => {
                let subject = self.instantiate(sig, subject, subst);
                let subject = self.reduce_condition_term(sig, subject)?;
                // `subject` and its fresh-variable subterms stay rooted through recursive reductions.
                let _root_subject = self.root(subject);
                for &fresh in fresh_vars {
                    subst.unbind(fresh);
                }
                let satisfied = match pattern.match_(self, sig, subject, subst, false, false) {
                    Some(mut solutions) => {
                        let mut satisfied = false;
                        let mut first = true;
                        loop {
                            if !first && self.tracing() {
                                self.record(TraceEvent::FragmentStart {
                                    kind,
                                    stmt_id,
                                    index: i as u32,
                                    depth,
                                    first_attempt: false,
                                });
                            }
                            first = false;
                            let found = solutions.next(self, sig, subst);
                            self.end_fragment(kind, stmt_id, i, depth, found, subst);
                            if !found {
                                break;
                            }
                            if self.solve_condition(sig, condition, i + 1, subst, kind, stmt_id)? {
                                satisfied = true;
                                break;
                            }
                        }
                        satisfied
                    }
                    None => {
                        self.end_fragment(kind, stmt_id, i, depth, false, subst);
                        false
                    }
                };
                if !satisfied {
                    for &fresh in fresh_vars {
                        subst.unbind(fresh);
                    }
                }
                Ok(satisfied)
            }
            CompiledFragment::Rewrite {
                lhs,
                pattern,
                fresh_vars,
            } => {
                // Reduce the instantiated origin, then search its `=>*` states for a matching pattern.
                let start = self.instantiate(sig, lhs, subst);
                let start = self.reduce_condition_term(sig, start)?;
                self.solve_rewrite_condition(
                    sig, start, pattern, fresh_vars, subst, condition, i, kind, stmt_id, depth,
                )
            }
        }
    }

    /// Solve a rewrite condition with breadth-first `=>*` reachability, including the zero-step state.
    /// Pattern and remaining-condition failure backtrack to the next reachable state. Every rule step
    /// contributes to the rewrite count; infinite reachable spaces may not terminate.
    ///
    /// Every retained DAG follows the same ownership contract as `StateGraph`: `states` owns one
    /// [`RootGuard`] per discovered canonical state, and each raw successor keeps its guard until it has
    /// been reduced and either interned into `states` or discarded as a duplicate. Frontier entries are
    /// state indexes rather than independent DAG handles. Consequently a nested reduce may collect without
    /// reclaiming pending successors, the current state, or fresh bindings reachable from a matched state.
    #[allow(clippy::too_many_arguments)]
    fn solve_rewrite_condition(
        &mut self,
        sig: &Signature,
        start: DagId,
        pattern: &LhsAutomaton,
        fresh_vars: &[u32],
        subst: &mut Subst,
        condition: &[CompiledFragment],
        i: usize,
        kind: StmtKind,
        stmt_id: u32,
        depth: u32,
    ) -> Result<bool, ReducerFault> {
        let mut states = vec![RootedDag {
            node: start,
            _root: self.root(start),
        }];
        let mut frontier = VecDeque::from([0usize]);
        while let Some(state_index) = frontier.pop_front() {
            let state = states[state_index].node;
            for &fv in fresh_vars {
                subst.unbind(fv);
            }
            if let Some(mut sp) = pattern.match_(self, sig, state, subst, false, false) {
                while sp.next(self, sig, subst) {
                    self.end_fragment(kind, stmt_id, i, depth, true, subst);
                    if self.solve_condition(sig, condition, i + 1, subst, kind, stmt_id)? {
                        return Ok(true);
                    }
                }
            }

            // Generate eagerly exactly as `state_successors` does, including charging all matcher/
            // condition work before reducing the first result. Keep the raw guards, however: reducing
            // one successor may collect, so every other pending result must remain live.
            let batch = self.state_successors_deferred(sig, state)?;
            for successor in &batch.entries {
                self.rewrite_count += successor.enumeration_rewrites;
            }
            self.rewrite_count += batch.tail_rewrites;
            for successor in batch.entries {
                let RawSuccessor {
                    term: succ,
                    _root: pending_root,
                    ..
                } = successor;
                self.rewrite_count += 1;
                self.rule_rewrite_count += 1;
                let reduced = self.reduce_condition_term(sig, succ)?;
                if !states
                    .iter()
                    .any(|rooted| self.deep_equal(rooted.node, reduced))
                {
                    let next = states.len();
                    states.push(RootedDag {
                        node: reduced,
                        _root: self.root(reduced),
                    });
                    frontier.push_back(next);
                }
                // If `reduced` was new, `states` now owns it. If it was a duplicate, the matching
                // canonical state was already rooted and this transient result is no longer needed.
                drop(pending_root);
            }
        }
        self.end_fragment(kind, stmt_id, i, depth, false, subst);
        for &fv in fresh_vars {
            subst.unbind(fv);
        }
        Ok(false)
    }
}

// ======================================================================================
// Engine: the thin public facade over Signature + Runtime
// ======================================================================================

/// The symbols and sorts used by object-pattern completion. They are resolved structurally from the
/// object constructor `<_:_|_>`, so modules may use arbitrary sort names. [`Engine::oo_info`] returns
/// `None` when no object constructor is in scope.
#[derive(Debug, Clone)]
pub struct OoInfo {
    /// The object constructor `<_:_|_> : Oid Cid AttributeSet -> Object` (the `object` attribute).
    pub object_ctor: SymbolId,
    /// The AttributeSet multiset constructor `_,_` (the object constructor's `attributeSetSymbol` op-hook):
    /// the ACU operator ranging on the object constructor's 3rd argument sort.
    pub attr_set_sym: SymbolId,
    /// The AttributeSet sort — the object constructor's 3rd argument sort. A fresh completion variable
    /// `Atts` is created at this sort.
    pub attr_set_sort: SortId,
    /// The AttributeSet identity (`none`), if `_,_` was declared with one — the empty attribute set.
    pub none_sym: Option<SymbolId>,
    /// The class-identifier sort `Cid` — the object constructor's 2nd argument sort.
    pub cid_sort: SortId,
    /// The class sorts: the strict subsorts of [`cid_sort`](Self::cid_sort) (a class `C` is declared
    /// `subsort C < Cid`). A class *constant* (arity-0 ctor ranging on one of these) or a variable of one
    /// of these sorts is what makes an object pattern eligible for completion.
    pub class_sorts: Vec<SortId>,
}

impl Engine {
    /// Whether `sym` is **associative** (an ACU or AU operator).
    pub fn symbol_is_assoc(&self, sym: SymbolId) -> bool {
        matches!(self.sig.symbol(sym).theory(), Theory::Acu | Theory::Au)
    }

    /// Whether `sym` is commutative (ACU or commutative CUI).
    pub fn symbol_is_commutative(&self, sym: SymbolId) -> bool {
        self.sig.symbol(sym).is_commutative()
    }

    /// Resolve the object-pattern completion context from the current signature. Returns `None` when
    /// the object constructor or its `Oid Cid AttributeSet` structure is unavailable.
    pub fn oo_info(&self) -> Option<OoInfo> {
        // The object constructor: the first symbol carrying the `object` OO flag.
        let (object_ctor, osym) = self.sig.symbols.iter().find(|(_, s)| s.oo.object)?;
        let odecl = &osym.decls[0];
        if odecl.domain.len() != 3 {
            return None; // not the `<_:_|_> : Oid Cid AttributeSet -> Object` shape
        }
        let cid_sort = odecl.domain[1];
        let attr_set_sort = odecl.domain[2];
        // The AttributeSet constructor `_,_`: the ACU operator whose range is the AttributeSet sort.
        let (attr_set_sym, assym) = self
            .sig
            .symbols
            .iter()
            .find(|(_, s)| s.theory() == Theory::Acu && s.decls[0].range == attr_set_sort)?;
        let none_sym = assym
            .identity()
            .and_then(|identity| self.sig.identity_constant(identity));
        let class_sorts = self.sig.sorts.strict_subsorts(cid_sort);
        Some(OoInfo {
            object_ctor,
            attr_set_sym,
            attr_set_sort,
            none_sym,
            cid_sort,
            class_sorts,
        })
    }
}

impl Engine {
    pub fn new() -> Self {
        Self::default()
    }
    /// Create an empty engine whose signature may bind functions from `catalog` before execution.
    pub fn with_host_functions(catalog: HostFunctionCatalog) -> Self {
        let mut engine = Self::default();
        engine.sig.host_functions = catalog;
        engine
    }

    /// The immutable capability catalog configured for this engine.
    ///
    /// Select a different catalog by constructing a new [`Engine`]; the shared accessor cannot
    /// replace an existing engine's reducer implementations:
    ///
    /// ```compile_fail
    /// use tnk_core::engine::Engine;
    /// use tnk_core::host::HostFunctionCatalog;
    ///
    /// fn replace_catalog(engine: &mut Engine, replacement: HostFunctionCatalog) {
    ///     *engine.host_functions() = replacement;
    /// }
    /// ```
    pub fn host_functions(&self) -> &HostFunctionCatalog {
        &self.sig.host_functions
    }

    /// Validate a prospective strict reducer attachment without mutating the signature.
    pub fn validate_host_function_binding(
        &self,
        symbol: SymbolId,
        key: &str,
        hooks: &ResolvedHostHooks,
    ) -> Result<(), HostBindingError> {
        self.sig
            .validate_host_function(symbol, key, hooks)
            .map(|_| ())
    }

    /// Bind a signature operator to one configured strict reducer.
    ///
    /// Binding is validation-only and allowed before the first semantic operation. The resolved
    /// binding becomes immutable signature data and is copied neither per call nor per DAG node.
    pub fn bind_host_function(
        &mut self,
        symbol: SymbolId,
        key: &str,
        hooks: ResolvedHostHooks,
    ) -> Result<HostBindingId, HostBindingError> {
        self.sig.bind_host_function(symbol, key, hooks)
    }

    /// Module-wide lower bound for substitution layouts. Narrowing places state variables at or
    /// above this index so statement construction/protected slots remain reserved.
    pub fn minimum_substitution_size(&self) -> usize {
        self.sig.minimum_substitution_size
    }

    /// Shared access to the immutable signature half (sorts/symbols/equations). Used by the matcher
    /// seam's tests to drive [`LhsAutomaton`](crate::theory) directly over the two halves, and by
    /// the order-sorted-unification driver (which builds `SortBdds` and reads sorts/symbols).
    pub(crate) fn signature(&self) -> &Signature {
        &self.sig
    }
    /// Shared access to the mutable runtime half (DAG arena, GC, and statistics), available only in
    /// tests. [`signature`](Self::signature) exposes the immutable half.
    #[cfg(test)]
    pub(crate) fn runtime(&self) -> &Runtime {
        &self.rt
    }
    /// Both halves borrowed disjointly, to drive the matcher seam's `next` — which needs a `&mut
    /// Runtime` and a `&Signature` at once. Used by
    /// [`match_solutions`](Self::match_solutions) and its [`Solutions`] stream, and by the theory tests.
    pub(crate) fn parts_mut(&mut self) -> (&Signature, &mut Runtime) {
        (&self.sig, &mut self.rt)
    }
    /// Run one operation against the public, minimal META descent view of this engine.
    ///
    /// Kept crate-visible for engine-neutral external-message transport; neither the runtime nor
    /// signature can remain borrowed after the callback returns.
    pub(crate) fn with_meta_ctx<R>(&mut self, f: impl FnOnce(&mut MetaCtx) -> R) -> R {
        let mut ctx = MetaCtx {
            rt: &mut self.rt,
            sig: &self.sig,
        };
        f(&mut ctx)
    }

    // ---- sort signature ----

    pub fn add_sort(&mut self, name: impl Into<String>) -> SortId {
        self.sig.add_sort(name)
    }
    pub fn add_subsort(&mut self, sub: SortId, sup: SortId) {
        self.sig.add_subsort(sub, sup);
    }
    /// A declared subsort cycle, if any, as a witness path `[s0, ..., s0]` (see
    /// [`Sorts::subsort_cycle`]). [`close_sorts`](Self::close_sorts) requires an acyclic order;
    /// callers handling untrusted input check this first and reject the signature.
    pub fn subsort_cycle(&self) -> Option<Vec<SortId>> {
        self.sig.sorts().subsort_cycle()
    }
    /// Finish the sort poset (compute kinds + subsort closure). Call before building DAG nodes.
    /// Panics if the declared subsorts contain a cycle; check [`subsort_cycle`](Self::subsort_cycle)
    /// first when the declarations come from user input.
    pub fn close_sorts(&mut self) {
        self.sig.close_sorts();
    }
    pub fn sorts(&self) -> &Sorts {
        self.sig.sorts()
    }

    pub fn smt_info(&self) -> &SmtInfo {
        &self.sig.smt_info
    }

    pub fn smt_type(&self, sort: SortId) -> Option<SmtType> {
        self.sig.smt_info.sort_type(sort)
    }

    /// Number of distinct kinds whose values use unsigned decimal integer syntax.
    ///
    /// Algebraic successor naturals and SMT integer constants are competing numeral families. An
    /// unknown-range numeral needs a qualifier when more than one such kind exists; the frontend also
    /// accounts for colliding user constants.
    pub fn integer_literal_kind_count(&self) -> usize {
        let mut kinds = HashSet::new();
        for &symbol in self.sig.succ_zeros.keys() {
            for decl in self.sig.symbol(symbol).decls() {
                kinds.insert(self.sig.sorts.kind_of(decl.range));
            }
        }
        for index in 0..self.sig.sorts.num_sorts() {
            let sort = SortId::from_raw(index as u32);
            if self.sig.smt_info.sort_type(sort) == Some(SmtType::Integer) {
                kinds.insert(self.sig.sorts.kind_of(sort));
            }
        }
        kinds.len()
    }
    pub fn smt_operator(&self, symbol: SymbolId) -> Option<SmtOp> {
        match self.sig.symbol(symbol).special() {
            Some(SpecialOp::Smt { op }) => Some(*op),
            _ => None,
        }
    }
    /// Kernel-side validity gate for SMT rewriting. The frontend separately distinguishes collapse
    /// axioms on ordinary operators from polymorphic instances.
    pub fn valid_for_smt_rewriting(&self) -> bool {
        self.sig.smt_info.conjunction().is_some()
            && !self.sig.smt_rules.is_empty()
            && self.sig.smt_rules_valid
            && self.sig.equations.is_empty()
            && self.sig.memberships.is_empty()
    }

    pub fn valid_smt_goal(&self, goal: &Term) -> bool {
        term_is_linear(goal) && !term_contains_smt(&self.sig, goal)
    }

    /// Register an `SMT_NumberSymbol` constructor and the SMT type of its range sort.
    pub fn register_smt_number(&mut self, symbol: SymbolId, sort: SortId, kind: SmtType) {
        let component = self.sig.sorts.kind_of(sort);
        self.sig.smt_info.set_sort_type(sort, kind);
        self.sig.smt_info.set_number_symbol(component, symbol);
        self.set_symbol_class(symbol, SymbolClass::SmtNumber);
    }

    /// Populate the non-behavioral `SMT_Info` bindings contributed by an `SMT_Symbol`. All overload
    /// declarations participate, so equality is available in each operand kind.
    pub fn register_smt_operator(&mut self, symbol: SymbolId, op: SmtOp) {
        let decls = self.symbol_declarations(symbol);
        match op {
            SmtOp::True | SmtOp::False => {
                for (_, range) in decls {
                    self.sig.smt_info.set_sort_type(range, SmtType::Boolean);
                }
                if op == SmtOp::True {
                    self.sig.smt_info.set_true_symbol(symbol);
                }
            }
            SmtOp::And => self.sig.smt_info.set_conjunction(symbol),
            SmtOp::Equals => {
                for (domain, _) in decls {
                    if let Some(&sort) = domain.first() {
                        let kind = self.sig.sorts.kind_of(sort);
                        self.sig.smt_info.set_equality(kind, symbol);
                    }
                }
            }
            _ => {}
        }
    }

    // ---- symbols ----

    pub fn add_op(
        &mut self,
        name: impl Into<String>,
        domain: Vec<SortId>,
        range: SortId,
    ) -> SymbolId {
        self.sig.add_op(name, domain, range)
    }

    /// Attach an additional declaration to an existing operator (ad-hoc / subsort overloading); the
    /// least sort of an application is resolved across all declarations. They must agree on arity and
    /// are tried in insertion order, so the first `add_op*` declaration wins an incomparable tie. Add
    /// every declaration before building a node of `sym`, because construction caches sorts.
    pub fn add_op_decl(&mut self, sym: SymbolId, domain: Vec<SortId>, range: SortId) {
        self.sig.add_op_decl(sym, domain, range);
    }

    /// Frontend declaration path: preserve this overload's own constructor bit instead of applying
    /// `[ctor]` retroactively to every declaration folded into the symbol.
    pub fn add_op_decl_with_ctor(
        &mut self,
        sym: SymbolId,
        domain: Vec<SortId>,
        range: SortId,
        ctor: bool,
    ) {
        self.sig.add_op_decl_with_ctor(sym, domain, range, ctor);
    }

    /// Record that folded overload declarations disagree on their structural constructor axioms.
    pub fn mark_inconsistent_constructor_axioms(&mut self, sym: SymbolId) {
        self.sig.mark_inconsistent_constructor_axioms(sym);
    }

    /// Mark an operator as a constructor (`[ctor]`); reduction-inert metadata used by symbolic analyses.
    pub fn set_ctor(&mut self, sym: SymbolId) {
        self.sig.set_ctor(sym);
    }

    /// Whether every declaration of `sym` is a constructor (`[ctor]`).
    pub fn is_constructor(&self, sym: SymbolId) -> bool {
        self.sig.symbol(sym).is_constructor()
    }

    /// Install an operator evaluation strategy: positive entries are 1-based argument positions and
    /// `0` is a top-rewrite attempt. An empty slice selects the standard eager strategy.
    pub fn set_strategy(&mut self, sym: SymbolId, raw: &[u32]) {
        self.sig.set_strategy(sym, raw);
    }

    /// Mark 1-based frozen argument positions on `sym`; an empty slice freezes every argument.
    /// Rule rewriting and search skip frozen arguments, while equational reduction still visits them.
    ///
    /// Returns `false` and leaves the symbol unchanged when the attribute references an invalid
    /// position. This makes declaration input recoverable without weakening the signature invariant.
    #[must_use]
    pub fn set_frozen(&mut self, sym: SymbolId, raw: &[u32]) -> bool {
        self.sig.set_frozen(sym, raw)
    }

    pub(crate) fn is_frozen_arg(&self, sym: SymbolId, arg: usize) -> bool {
        self.sig.symbol(sym).is_frozen_arg(arg)
    }

    /// Record the object-system role of `sym` (`config`/`obj`/`msg`/`portal`). Ordinary rewrite modes
    /// treat the configuration as an ACU soup; the flags drive `erewrite`'s object/message partition.
    pub fn set_oo_flags(
        &mut self,
        sym: SymbolId,
        config: bool,
        object: bool,
        message: bool,
        portal: bool,
    ) {
        self.sig.set_oo_flags(
            sym,
            OoFlags {
                config,
                object,
                message,
                portal,
            },
        );
    }

    /// Classify `sym` for decompose-equality stability analysis. Module construction marks built-in
    /// marker classes, and command evaluation marks pseudo-variable constants for non-ground subjects.
    pub fn set_symbol_class(&mut self, sym: SymbolId, class: SymbolClass) {
        if let SymbolClass::Variable { rank } = class {
            self.rt.var_ranks.insert(sym, rank);
        }
        self.sig.symbols.get_mut(sym).class = class;
    }

    /// Reserve a two-sided identity slot before the ground term is parsed. This supports mutually
    /// referring operator declarations without degrading identity terms to name lookups.
    pub fn reserve_identity(&mut self, sym: SymbolId, sort: SortId) {
        assert!(
            !matches!(
                self.sig.symbol(sym).special(),
                Some(SpecialOp::HostFunction(_))
            ),
            "a strict host operator's theory is sealed at binding"
        );
        let identity = self.sig.reserve_identity(sort);
        self.sig.symbols.get_mut(sym).identity = Some(identity);
    }

    /// Reserve a one-sided identity slot before its ground term is parsed.
    pub fn reserve_one_sided_identity(&mut self, sym: SymbolId, side: IdentitySide, sort: SortId) {
        assert!(
            !matches!(
                self.sig.symbol(sym).special(),
                Some(SpecialOp::HostFunction(_))
            ),
            "a strict host operator's theory is sealed at binding"
        );
        let identity = self.sig.reserve_identity(sort);
        self.sig.symbols.get_mut(sym).one_sided_id = Some((side, identity));
    }

    /// Install the parsed ground term into a previously reserved identity slot.
    pub fn set_identity_term(&mut self, sym: SymbolId, term: Term) {
        assert!(
            !matches!(
                self.sig.symbol(sym).special(),
                Some(SpecialOp::HostFunction(_))
            ),
            "a strict host operator's identity is sealed at binding"
        );
        let identity = self
            .sig
            .symbol(sym)
            .identity()
            .expect("identity slot not reserved");
        assert!(term.is_ground(), "identity term must be ground");
        let sort = self.sig.term_sort(&term);
        *self.sig.identities.get_mut(identity) = Identity {
            term: Some(term),
            sort,
        };
    }

    /// Install the parsed ground term into a previously reserved one-sided identity slot.
    pub fn set_one_sided_identity_term(&mut self, sym: SymbolId, term: Term) {
        assert!(
            !matches!(
                self.sig.symbol(sym).special(),
                Some(SpecialOp::HostFunction(_))
            ),
            "a strict host operator's identity is sealed at binding"
        );
        let identity = self
            .sig
            .symbol(sym)
            .one_sided_id
            .expect("one-sided identity slot not reserved")
            .1;
        assert!(term.is_ground(), "identity term must be ground");
        let sort = self.sig.term_sort(&term);
        *self.sig.identities.get_mut(identity) = Identity {
            term: Some(term),
            sort,
        };
    }

    /// Materialize every installed identity as a normalized permanent DAG after module construction.
    ///
    /// This compatibility wrapper panics on a strict-reducer fault. Runtime and frontend boundaries
    /// should use [`Self::try_prepare_identities`].
    pub fn prepare_identities(&mut self) {
        self.try_prepare_identities()
            .unwrap_or_else(|fault| panic!("{fault}"));
    }

    /// Fallible identity materialization for module-build boundaries.
    pub fn try_prepare_identities(&mut self) -> Result<(), ReducerFault> {
        let identities: HashSet<IdentityId> = self
            .sig
            .symbols_iter()
            .flat_map(|(_, sym)| {
                sym.identity
                    .into_iter()
                    .chain(sym.one_sided_id.map(|(_, identity)| identity))
            })
            .collect();
        self.try_symbolic_operation(|rt, sig| {
            for identity in identities {
                rt.identity_dag(sig, identity);
                if rt.reducer_fault.is_some() {
                    break;
                }
            }
        })
    }
    /// Retain a `SuccSymbol`'s `zeroTerm`. A raw term-hook lookup is name/arity-only; select the
    /// same-name zero declaration whose range belongs to the successor's domain kind.
    pub fn register_succ_zero(&mut self, succ: SymbolId, proposed: SymbolId) -> SymbolId {
        let domain = self.sig.symbol(succ).decls()[0].domain[0];
        let name = self.sig.symbol(proposed).name().to_string();
        let zero = self
            .sig
            .symbols_iter()
            .find_map(|(id, symbol)| {
                (symbol.name() == name
                    && symbol.decls().iter().any(|decl| {
                        decl.domain.is_empty() && self.sig.sorts.leq(decl.range, domain)
                    }))
                .then_some(id)
            })
            .unwrap_or(proposed);
        self.sig.succ_zeros.insert(succ, zero);
        zero
    }

    /// Lazily create and cache one internal variable symbol per sort. Demand order is observable in
    /// structural ordering, so command parsing, fresh-kind generation, and extraction share a permanent
    /// module-level rank. Symbols use their sort names but never enter frontend name tables.
    ///
    /// Command normalization records first demand for each sort, appends new ranks, and restores the
    /// supplied slice to module-lifetime order. An already-canonical command DAG therefore cannot
    /// change the permanent ranks used by later commands.
    fn rank_term_variable_sorts(&mut self, terms: &[&Term]) {
        fn collect(term: &Term, sorts: &mut Vec<SortId>) {
            match term {
                Term::Var(v) => {
                    if !sorts.contains(&v.sort) {
                        sorts.push(v.sort);
                    }
                }
                Term::Op { args, .. } => {
                    for arg in args {
                        collect(arg, sorts);
                    }
                }
                Term::Iter { arg, .. } => collect(arg, sorts),
                Term::Na { .. } => {}
            }
        }

        let mut sorts = Vec::new();
        for term in terms {
            collect(term, &mut sorts);
        }
        self.rank_variable_sorts(&mut sorts);
    }

    pub(crate) fn rank_variable_sorts(&mut self, sorts: &mut [SortId]) {
        let mut next = self
            .rt
            .sort_var_ranks
            .values()
            .copied()
            .max()
            .map_or(0, |r| r + 1);
        for &sort in sorts.iter() {
            let sym = self.variable_symbol(sort);
            if let std::collections::hash_map::Entry::Vacant(entry) =
                self.rt.sort_var_ranks.entry(sym)
            {
                entry.insert(next);
                next += 1;
            }
        }
        sorts.sort_by_key(|sort| {
            let sym = self.sig.var_symbols[sort];
            self.rt.sort_var_ranks[&sym]
        });
    }
    pub fn variable_symbol(&mut self, sort: SortId) -> SymbolId {
        let kind = self.sig.sorts().kind_of(sort);
        let is_error = self.sig.sorts().sort(sort).is_error;
        if let Some(&sym) = self.sig.var_symbols.get(&sort) {
            self.rt.sort_var_meta.entry(sym).or_insert((kind, is_error));
            return sym;
        }
        let name = self.sig.sorts().name(sort).to_string();
        let sym = self.sig.add_op(name, vec![], sort);
        self.sig.symbols.get_mut(sym).class = SymbolClass::SortVariable;
        self.sig.var_symbols.insert(sort, sym);
        self.rt.sort_var_meta.insert(sym, (kind, is_error));
        sym
    }

    /// Build a variable leaf of `sort`. `name` is its interned base-name token and `index` is the owning
    /// symbolic problem's substitution slot. The per-sort symbol is created on first use.
    pub fn make_var(&mut self, sort: SortId, name: u32, index: u32) -> DagId {
        let sym = self.variable_symbol(sort);
        self.rt.make_var(&self.sig, sym, name, index)
    }

    /// Fallible form of [`normalize_pattern_for_reflection`](Self::normalize_pattern_for_reflection).
    /// Returns a strict-reducer fault raised while an identity is materialized by theory
    /// normalization.
    pub fn try_normalize_pattern_for_reflection(
        &mut self,
        term: &Term,
        variable_names: &[u32],
    ) -> Result<DagId, ReducerFault> {
        self.sig.mark_symbolic_execution();
        self.rt.check_reducer_fault()?;
        let checkpoint = self.semantic_checkpoint();
        let mut variable_sorts = Vec::<Option<SortId>>::new();
        let mut variable_sort_order = Vec::new();
        let mut work = vec![term];
        while let Some(term) = work.pop() {
            match term {
                Term::Var(var) => {
                    let slot = var.index as usize;
                    if variable_sorts.len() <= slot {
                        variable_sorts.resize(slot + 1, None);
                    }
                    variable_sorts[slot] = Some(var.sort);
                    if !variable_sort_order.contains(&var.sort) {
                        variable_sort_order.push(var.sort);
                    }
                }
                Term::Op { args, .. } => work.extend(args),
                Term::Iter { arg, .. } => work.push(arg),
                Term::Na { .. } => {}
            }
        }
        self.rank_variable_sorts(&mut variable_sort_order);

        let mut subst = Subst::new();
        subst.reset(variable_sorts.len() as u32);
        for (slot, sort) in variable_sorts.into_iter().enumerate() {
            if let Some(sort) = sort {
                let name = variable_names.get(slot).copied().unwrap_or(slot as u32);
                let variable = self.make_var(sort, name, slot as u32);
                subst.bind(slot as u32, variable);
            }
        }
        let dag = self.rt.instantiate(&self.sig, term, &subst);
        if let Err(fault) = self.rt.check_reducer_fault() {
            self.restore_semantic_checkpoint(checkpoint);
            return Err(fault);
        }
        let normalized = self.rt.normalize_for_unify(&self.sig, dag);
        if let Err(fault) = self.rt.check_reducer_fault() {
            self.restore_semantic_checkpoint(checkpoint);
            return Err(fault);
        }
        Ok(normalized)
    }

    /// Instantiate and eagerly theory-normalize a static statement pattern for reflection.
    ///
    /// # Panics
    ///
    /// Panics if strict host reduction fails while normalizing an attached identity. Call
    /// [`try_normalize_pattern_for_reflection`](Self::try_normalize_pattern_for_reflection) at
    /// fallible semantic boundaries.
    pub fn normalize_pattern_for_reflection(
        &mut self,
        term: &Term,
        variable_names: &[u32],
    ) -> DagId {
        self.try_normalize_pattern_for_reflection(term, variable_names)
            .unwrap_or_else(|fault| panic!("pattern theory normalization failed: {fault}"))
    }

    /// Run one symbolic operation as an atomic semantic boundary. Public symbolic work seals host
    /// attachment before dispatch, including when no attachment exists yet.
    fn try_symbolic_operation<T>(
        &mut self,
        operation: impl FnOnce(&mut Runtime, &Signature) -> T,
    ) -> Result<T, ReducerFault> {
        self.sig.mark_symbolic_execution();
        self.try_build_symbolic_operation(operation)
    }

    /// Staged module construction may canonicalize statement patterns before committing validated host
    /// attachments. This is the only unsealed symbolic funnel and remains private to the kernel.
    fn try_build_symbolic_operation<T>(
        &mut self,
        operation: impl FnOnce(&mut Runtime, &Signature) -> T,
    ) -> Result<T, ReducerFault> {
        self.rt.check_reducer_fault()?;
        let checkpoint = self.semantic_checkpoint();
        let value = operation(&mut self.rt, &self.sig);
        if let Err(fault) = self.rt.check_reducer_fault() {
            self.restore_semantic_checkpoint(checkpoint);
            return Err(fault);
        }
        Ok(value)
    }

    /// Fallible symbolic theory normalization.
    pub fn try_normalize_for_unify(&mut self, dag: DagId) -> Result<DagId, ReducerFault> {
        self.try_symbolic_operation(|rt, sig| rt.normalize_for_unify(sig, dag))
    }
    /// Internal symbolic normalization for callbacks that cannot return a [`ReducerFault`]. Retain
    /// the fault for the enclosing fallible driver and leave the input representation in place.
    pub(crate) fn normalize_for_unify_or_defer_fault(&mut self, dag: DagId) -> DagId {
        match self.try_normalize_for_unify(dag) {
            Ok(normalized) => normalized,
            Err(fault) => {
                self.defer_reducer_fault(fault);
                dag
            }
        }
    }
    /// Module-build counterpart to [`Self::normalize_for_unify_or_defer_fault`]. It intentionally does
    /// not seal the signature because all equations are still being installed before host attachment.
    pub(crate) fn normalize_for_unify_for_build_or_defer_fault(&mut self, dag: DagId) -> DagId {
        match self.try_build_symbolic_operation(|rt, sig| rt.normalize_for_unify(sig, dag)) {
            Ok(normalized) => normalized,
            Err(fault) => {
                self.defer_reducer_fault(fault);
                dag
            }
        }
    }

    /// Eagerly theory-normalize `dag` (flatten/merge ACU/AU) for the symbolic engine.
    ///
    /// # Panics
    ///
    /// Panics if strict host reduction fails while normalizing an attached identity. Fallible
    /// semantic entry points must use [`try_normalize_for_unify`](Self::try_normalize_for_unify).
    pub fn normalize_for_unify(&mut self, dag: DagId) -> DagId {
        self.try_normalize_for_unify(dag)
            .unwrap_or_else(|fault| panic!("symbolic theory normalization failed: {fault}"))
    }

    /// Carry the current-epoch self-normal stamp across a semantics-preserving alpha rebuild.
    pub(crate) fn inherit_reduced_status(&mut self, source: DagId, rebuilt: DagId) {
        self.rt.inherit_reduced_status(&self.sig, source, rebuilt);
    }

    /// Rebuild a symbolic DAG with each original slot replaced by `new_slots[old_slot]`. This runs
    /// after theory normalization, so commutative canonical order—not parser encounter order—defines
    /// visible substitution slots. The iterative postorder walk preserves sharing and compact S counts.
    pub(crate) fn remap_variable_slots(&mut self, root: DagId, new_slots: &[u32]) -> DagId {
        self.remap_variable_slots_inner(root, new_slots, false)
    }

    /// Remap variable slots without normalizing any enclosing theory node.
    ///
    /// Final narrowing goals may contain shared, transiently noncanonical AC/AU children. Canonical
    /// builders would destroy that sharing before reduction.
    pub(crate) fn remap_variable_slots_preserving_representation(
        &mut self,
        root: DagId,
        new_slots: &[u32],
    ) -> DagId {
        self.remap_variable_slots_inner(root, new_slots, true)
    }

    fn remap_variable_slots_inner(
        &mut self,
        root: DagId,
        new_slots: &[u32],
        preserve_representation: bool,
    ) -> DagId {
        if new_slots.is_empty() {
            return root;
        }

        #[derive(Clone)]
        enum Shape {
            Free(SymbolId, Vec<DagId>),
            Acu(SymbolId, Vec<(DagId, u32)>),
            Au(SymbolId, Vec<DagId>),
            Cui(SymbolId, DagId, DagId),
            S(SymbolId, Nat, DagId),
            Na,
            Var(SymbolId, u32, u32),
        }

        let mut rebuilt: HashMap<DagId, DagId> = HashMap::new();
        let mut work = vec![(root, false)];
        while let Some((id, expanded)) = work.pop() {
            if rebuilt.contains_key(&id) {
                continue;
            }
            let shape = match &self.rt.dags.get(id).term {
                NodeTerm::Free { symbol, args } => Shape::Free(*symbol, args.clone()),
                NodeTerm::Acu { symbol, args } => Shape::Acu(*symbol, args.clone()),
                NodeTerm::Au { symbol, args } => Shape::Au(*symbol, args.clone()),
                NodeTerm::Cui { symbol, args } => Shape::Cui(*symbol, args[0], args[1]),
                NodeTerm::S { symbol, count, arg } => Shape::S(*symbol, count.clone(), *arg),
                NodeTerm::Na { .. } => Shape::Na,
                NodeTerm::Var {
                    symbol,
                    name,
                    index,
                } => Shape::Var(*symbol, *name, *index),
            };
            if !expanded {
                work.push((id, true));
                match &shape {
                    Shape::Free(_, args) | Shape::Au(_, args) => {
                        work.extend(args.iter().rev().map(|&child| (child, false)));
                    }
                    Shape::Acu(_, args) => {
                        work.extend(args.iter().rev().map(|&(child, _)| (child, false)));
                    }
                    Shape::Cui(_, x, y) => {
                        work.push((*y, false));
                        work.push((*x, false));
                    }
                    Shape::S(_, _, arg) => work.push((*arg, false)),
                    Shape::Na | Shape::Var(_, _, _) => {}
                }
                continue;
            }
            let map_child = |child: DagId| {
                *rebuilt
                    .get(&child)
                    .expect("postorder child must be rebuilt")
            };
            let new = match shape {
                Shape::Free(symbol, args) => {
                    let args = args.into_iter().map(map_child).collect();
                    if preserve_representation {
                        self.rt.make_preserving_representation(
                            &self.sig,
                            NodeTerm::Free { symbol, args },
                        )
                    } else {
                        self.rt.make_free(&self.sig, symbol, args)
                    }
                }
                Shape::Acu(symbol, args) => {
                    let args = args
                        .into_iter()
                        .map(|(child, mult)| (map_child(child), mult))
                        .collect();
                    if preserve_representation {
                        self.rt.make_preserving_representation(
                            &self.sig,
                            NodeTerm::Acu { symbol, args },
                        )
                    } else {
                        self.rt.make_acu(&self.sig, symbol, args)
                    }
                }
                Shape::Au(symbol, args) => {
                    let args = args.into_iter().map(map_child).collect();
                    if preserve_representation {
                        self.rt.make_preserving_representation(
                            &self.sig,
                            NodeTerm::Au { symbol, args },
                        )
                    } else {
                        self.rt.make_au(&self.sig, symbol, args)
                    }
                }
                Shape::Cui(symbol, x, y) => {
                    let x = map_child(x);
                    let y = map_child(y);
                    if preserve_representation {
                        self.rt.make_preserving_representation(
                            &self.sig,
                            NodeTerm::Cui {
                                symbol,
                                args: vec![x, y],
                            },
                        )
                    } else {
                        self.rt.make_cui(&self.sig, symbol, x, y)
                    }
                }
                Shape::S(symbol, count, arg) => {
                    let arg = map_child(arg);
                    if preserve_representation {
                        self.rt.make_preserving_representation(
                            &self.sig,
                            NodeTerm::S { symbol, count, arg },
                        )
                    } else {
                        self.rt.make_s(&self.sig, symbol, count, arg)
                    }
                }
                Shape::Na => id,
                Shape::Var(symbol, name, old_slot) => {
                    self.rt
                        .make_var(&self.sig, symbol, name, new_slots[old_slot as usize])
                }
            };
            self.rt.inherit_reduced_status(&self.sig, id, new);
            rebuilt.insert(id, new);
        }
        rebuilt[&root]
    }

    /// A fresh, distinct ground constant of `sort`. The irredundant filter
    /// ([`crate::unify::filter`]) freezes a candidate unifier's variables into these, so that "is
    /// unifier `u` an instance of unifier `r`?" reduces to the satisfiability of `r =? freeze(u)` —
    /// matching expressed as unification with the subject side frozen. The name is uniquified by the
    /// live symbol count so repeated calls never alias; it enters no frontend name table (cannot
    /// collide with a user operator) and never reaches any printed output.
    pub fn fresh_constant(&mut self, sort: SortId) -> DagId {
        let name = format!("%frozen-{}", self.sig.symbols_iter().count());
        let sym = self.sig.add_op(name, vec![], sort);
        self.make_const(sym)
    }

    /// Attach a built-in reduction rule to `sym`, before user equations. Hook references must already
    /// be resolved. Branch hooks install their intrinsic strategy and synthetic sort declarations.
    pub fn set_special(&mut self, sym: SymbolId, op: SpecialOp) {
        assert!(
            !matches!(&op, SpecialOp::HostFunction(_)),
            "host functions must be installed through Engine::bind_host_function"
        );
        self.sig.set_special(sym, op);
    }

    /// Register an **ACU** operator (`assoc comm`, optionally with a two-sided `id:`). Must be binary;
    /// `identity` is the constant symbol declared as `id: <const>`, or `None`. The operator's
    /// arguments are stored flattened as a canonical multiset and matched/rewritten modulo AC(+U).
    pub fn add_op_ac(
        &mut self,
        name: impl Into<String>,
        domain: Vec<SortId>,
        range: SortId,
        identity: Option<SymbolId>,
    ) -> SymbolId {
        self.sig.add_op_ac(name, domain, range, identity)
    }

    /// Register an **AU** operator (`assoc`, not commutative, optionally with a two-sided `id:`). Must
    /// be binary; arguments are stored as a flattened ordered sequence and matched modulo associativity.
    pub fn add_op_au(
        &mut self,
        name: impl Into<String>,
        domain: Vec<SortId>,
        range: SortId,
        identity: Option<SymbolId>,
    ) -> SymbolId {
        self.sig.add_op_au(name, domain, range, identity)
    }

    /// Register a binary **CUI** operator with any non-associative subset of `comm`, `id:`, and `idem`.
    /// Commutative arguments are canonicalized; identities and equal idempotent arguments collapse.
    pub fn add_op_cui(
        &mut self,
        name: impl Into<String>,
        domain: Vec<SortId>,
        range: SortId,
        comm: bool,
        idem: bool,
        identity: Option<SymbolId>,
    ) -> SymbolId {
        self.sig
            .add_op_cui(name, domain, range, comm, idem, identity)
    }

    /// Register a unary **S** (`iter`) operator whose nodes store `s^count(arg)` compactly.
    pub fn add_op_iter(
        &mut self,
        name: impl Into<String>,
        domain: Vec<SortId>,
        range: SortId,
    ) -> SymbolId {
        self.sig.add_op_iter(name, domain, range)
    }
    pub fn symbol(&self, id: SymbolId) -> &Symbol {
        self.sig.symbol(id)
    }

    /// Resolve a source operator among same-name symbols using the argument sorts. META terms carry the
    /// operator name but not its overload id, so their down-translation needs the same applicability test
    /// as ordinary parsing. A reflected associative application is flat: three or more arguments still
    /// select a binary ACU/AU declaration, using its binary sort fold to disambiguate ad-hoc overloads.
    pub fn resolve_operator_for_sorts(
        &self,
        name: &str,
        argument_sorts: &[SortId],
    ) -> Option<SymbolId> {
        let exact = self.sig.symbols_iter().find_map(|(id, symbol)| {
            (symbol.name() == name
                && symbol.arity() == argument_sorts.len()
                && symbol.decls().iter().any(|decl| {
                    argument_sorts
                        .iter()
                        .zip(&decl.domain)
                        .all(|(&actual, &declared)| self.sig.sorts.leq(actual, declared))
                }))
            .then_some(id)
        });
        if exact.is_some() || argument_sorts.len() < 3 {
            return exact;
        }
        self.sig.symbols_iter().find_map(|(id, symbol)| {
            if symbol.name() != name
                || symbol.arity() != 2
                || !matches!(symbol.theory(), Theory::Acu | Theory::Au)
            {
                return None;
            }
            let result = self.sig.compute_sort_fold(id, argument_sorts);
            let range_kind = self.sig.sorts.kind_of(symbol.decls()[0].range);
            (result != self.sig.sorts.error_sort(range_kind)).then_some(id)
        })
    }

    /// Resolve a META application by connected-component profile when no sort-level declaration applies.
    /// Reflected rule sides may contain special operations whose result remains an error sort until
    /// inner reduction refines it. Name-and-arity selection alone is unsafe across unrelated kinds.
    pub fn resolve_operator_for_kinds(
        &self,
        name: &str,
        argument_sorts: &[SortId],
    ) -> Option<SymbolId> {
        let same_kind =
            |actual: SortId, declared: SortId| self.sig.sorts.same_kind(actual, declared);
        let exact = self.sig.symbols_iter().find_map(|(id, symbol)| {
            (symbol.name() == name
                && symbol.arity() == argument_sorts.len()
                && symbol.decls().iter().any(|decl| {
                    argument_sorts
                        .iter()
                        .zip(&decl.domain)
                        .all(|(&actual, &declared)| same_kind(actual, declared))
                }))
            .then_some(id)
        });
        if exact.is_some() || argument_sorts.len() < 3 {
            return exact;
        }
        self.sig.symbols_iter().find_map(|(id, symbol)| {
            if symbol.name() != name
                || symbol.arity() != 2
                || !matches!(symbol.theory(), Theory::Acu | Theory::Au)
            {
                return None;
            }
            symbol
                .decls()
                .iter()
                .any(|decl| {
                    same_kind(argument_sorts[0], decl.domain[0])
                        && argument_sorts[1..]
                            .iter()
                            .all(|&actual| same_kind(actual, decl.domain[1]))
                        && same_kind(decl.range, decl.domain[0])
                })
                .then_some(id)
        })
    }

    /// Resolve an operator hook by its complete connected-component profile. Unlike ordinary META-term
    /// descent, a hook signature supplies its result type as well as its argument types; including that
    /// result kind is essential for overloaded constants such as `none`.
    pub fn resolve_operator_for_kind_profile(
        &self,
        name: &str,
        argument_sorts: &[SortId],
        range_sort: SortId,
    ) -> Option<SymbolId> {
        let range_kind = self.sig.sorts.kind_of(range_sort);
        self.sig.symbols_iter().find_map(|(id, symbol)| {
            (symbol.name() == name
                && symbol.arity() == argument_sorts.len()
                && symbol.decls().iter().any(|decl| {
                    self.sig.sorts.kind_of(decl.range) == range_kind
                        && argument_sorts
                            .iter()
                            .zip(&decl.domain)
                            .all(|(&actual, &declared)| self.sig.sorts.same_kind(actual, declared))
                }))
            .then_some(id)
        })
    }

    /// Resolve a META constant in the connected component named by its annotation. The suffix selects
    /// a component rather than imposing an upper sort bound.
    pub fn resolve_constant_at_sort(&self, name: &str, sort: SortId) -> Option<SymbolId> {
        let kind = self.sig.sorts.kind_of(sort);
        self.sig.symbols_iter().find_map(|(id, symbol)| {
            (symbol.name() == name
                && symbol.decls().iter().any(|decl| {
                    decl.domain.is_empty() && self.sig.sorts.kind_of(decl.range) == kind
                }))
            .then_some(id)
        })
    }

    pub fn term_sort(&self, term: &Term) -> SortId {
        self.sig.term_sort(term)
    }

    /// The `(domain, range)` of each of `sym`'s operator declarations (one per ad-hoc/subsort overload).
    /// The META-LEVEL `maximalAritySet` descent reads these to find an operator's maximal argument sorts.
    pub fn symbol_declarations(&self, id: SymbolId) -> Vec<(Vec<SortId>, SortId)> {
        self.sig
            .symbol(id)
            .decls()
            .iter()
            .map(|d| (d.domain.clone(), d.range))
            .collect()
    }

    /// Fallible materialization of the normalized identity attached to `id`, including one-sided
    /// identities.
    pub fn try_symbol_identity_dag(&mut self, id: SymbolId) -> Result<Option<DagId>, ReducerFault> {
        self.sig.mark_symbolic_execution();
        self.rt.check_reducer_fault()?;
        let identity = {
            let symbol = self.sig.symbol(id);
            symbol
                .identity()
                .or_else(|| symbol.left_identity())
                .or_else(|| symbol.right_identity())
        };
        let Some(identity) = identity else {
            return Ok(None);
        };
        self.try_symbolic_operation(|rt, sig| Some(rt.identity_dag(sig, identity)))
    }

    /// Materialize the normalized identity attached to `id`, including one-sided identities.
    ///
    /// # Panics
    ///
    /// Panics if strict host reduction of the identity fails. Fallible semantic entry points must
    /// use [`try_symbol_identity_dag`](Self::try_symbol_identity_dag).
    pub fn symbol_identity_dag(&mut self, id: SymbolId) -> Option<DagId> {
        self.try_symbol_identity_dag(id)
            .unwrap_or_else(|fault| panic!("identity materialization failed: {fault}"))
    }

    /// The kind (connected component) of `sym`'s result — its first declaration's range kind. Used by the
    /// frontend to parse an equation's rhs in the same kind as its lhs (overloads that span kinds fall
    /// back to unconstrained parsing).
    pub fn symbol_kind(&self, id: SymbolId) -> KindId {
        self.sig.symbol_range_kind(id)
    }

    /// Record the base sort (`code == None`) or a classification sort for a
    /// `QuotedIdentifierSymbol` declaration.
    pub fn set_qid_class(&mut self, code: Option<&str>, sort: SortId) {
        self.sig.set_qid_class(code, sort);
    }

    // ---- DAG construction ----

    /// Fallible theory-aware node construction. Returns a strict-reducer fault if construction has to
    /// normalize an attached identity.
    pub fn try_make_node(
        &mut self,
        symbol: SymbolId,
        children: Vec<DagId>,
    ) -> Result<DagId, ReducerFault> {
        self.try_symbolic_operation(|rt, sig| rt.rebuild(sig, symbol, children))
    }

    /// Build a theory-aware node from `children`.
    ///
    /// # Panics
    ///
    /// Panics if strict host reduction fails while materializing an attached identity. Fallible
    /// semantic entry points must use [`try_make_node`](Self::try_make_node).
    pub fn make_node(&mut self, symbol: SymbolId, children: Vec<DagId>) -> DagId {
        self.try_make_node(symbol, children)
            .unwrap_or_else(|fault| panic!("theory-aware node construction failed: {fault}"))
    }

    /// Build a free-theory node `symbol(args...)`, computing and caching its least sort.
    pub fn make_free(&mut self, symbol: SymbolId, args: Vec<DagId>) -> DagId {
        self.rt.make_free(&self.sig, symbol, args)
    }
    /// Convenience for a constant (an arity-0 symbol).
    pub fn make_const(&mut self, symbol: SymbolId) -> DagId {
        self.rt.make_const(&self.sig, symbol)
    }

    pub(crate) fn make_identity(&mut self, identity: IdentityId) -> DagId {
        self.rt.identity_dag(&self.sig, identity)
    }

    pub(crate) fn is_identity(&self, identity: IdentityId, dag: DagId) -> bool {
        self.rt.is_identity(&self.sig, identity, dag)
    }

    /// Fallible canonical ACU construction.
    pub fn try_make_acu(
        &mut self,
        symbol: SymbolId,
        args: Vec<(DagId, u32)>,
    ) -> Result<DagId, ReducerFault> {
        self.try_symbolic_operation(|rt, sig| rt.make_acu(sig, symbol, args))
    }

    /// Build a canonical ACU node.
    ///
    /// # Panics
    ///
    /// Panics if strict host reduction fails while materializing an attached identity. Fallible
    /// semantic entry points must use [`try_make_acu`](Self::try_make_acu).
    pub fn make_acu(&mut self, symbol: SymbolId, args: Vec<(DagId, u32)>) -> DagId {
        self.try_make_acu(symbol, args)
            .unwrap_or_else(|fault| panic!("ACU construction failed: {fault}"))
    }

    pub(crate) fn make_acu_preserving_order(
        &mut self,
        symbol: SymbolId,
        args: Vec<(DagId, u32)>,
    ) -> DagId {
        self.rt.make_acu_preserving_order(&self.sig, symbol, args)
    }
    /// Fallible convenience form of [`try_make_acu`](Self::try_make_acu) for elements with
    /// multiplicity one.
    pub fn try_make_ac(
        &mut self,
        symbol: SymbolId,
        elements: Vec<DagId>,
    ) -> Result<DagId, ReducerFault> {
        self.try_make_acu(
            symbol,
            elements.into_iter().map(|element| (element, 1)).collect(),
        )
    }

    /// Convenience for [`make_acu`](Self::make_acu) from a flat list of elements.
    ///
    /// # Panics
    ///
    /// Panics under the same conditions as [`make_acu`](Self::make_acu).
    pub fn make_ac(&mut self, symbol: SymbolId, elements: Vec<DagId>) -> DagId {
        self.try_make_ac(symbol, elements)
            .unwrap_or_else(|fault| panic!("ACU construction failed: {fault}"))
    }

    /// Fallible canonical AU construction.
    pub fn try_make_au(
        &mut self,
        symbol: SymbolId,
        elements: Vec<DagId>,
    ) -> Result<DagId, ReducerFault> {
        self.try_symbolic_operation(|rt, sig| rt.make_au(sig, symbol, elements))
    }

    /// Build a canonical AU node.
    ///
    /// # Panics
    ///
    /// Panics if strict host reduction fails while materializing an attached identity. Fallible
    /// semantic entry points must use [`try_make_au`](Self::try_make_au).
    pub fn make_au(&mut self, symbol: SymbolId, elements: Vec<DagId>) -> DagId {
        self.try_make_au(symbol, elements)
            .unwrap_or_else(|fault| panic!("AU construction failed: {fault}"))
    }

    /// Build a canonical **CUI** node for a `comm [idem] [id:]` operator from its two arguments (see
    /// `Runtime::make_cui`): commutatively ordered, with `f(a,a)`/`f(a,e)` collapsed.
    pub fn make_cui(&mut self, symbol: SymbolId, x: DagId, y: DagId) -> DagId {
        self.rt.make_cui(&self.sig, symbol, x, y)
    }

    /// Build a canonical **S** (`iter`) node `s^count(arg)` for an `iter` operator (see
    /// `Runtime::make_s`): `count == 0` collapses to `arg`, nested same-symbol successors flatten.
    /// `symbol` must be an `iter` operator (declared via [`add_op_iter`](Self::add_op_iter)).
    pub fn make_iter(&mut self, symbol: SymbolId, count: u64, arg: DagId) -> DagId {
        self.rt.make_s(&self.sig, symbol, Nat::from_u64(count), arg)
    }

    /// As [`make_iter`](Self::make_iter) with an arbitrary-precision decimal count — the frontend's
    /// bignum numeral / `s_^k` literal bridge (`1267650600228229401496703205376` builds directly;
    /// the kernel count is a bignum [`Nat`] natively). `None` if `count` is not a decimal numeral.
    pub fn make_iter_decimal(
        &mut self,
        symbol: SymbolId,
        count: &str,
        arg: DagId,
    ) -> Option<DagId> {
        let n = crate::num::Int::from_string_base(10, count)?;
        if n.is_negative() {
            return None;
        }
        Some(self.rt.make_s(&self.sig, symbol, n.magnitude(), arg))
    }

    /// Build a raw-byte string literal as an atomic node.
    pub fn make_string(&mut self, symbol: SymbolId, value: &[u8]) -> DagId {
        self.rt
            .make_na(&self.sig, symbol, NaValue::Str(value.into()))
    }
    /// Build a quoted identifier as an atomic node.
    pub fn make_qid(&mut self, symbol: SymbolId, value: &str) -> DagId {
        self.rt
            .make_na(&self.sig, symbol, NaValue::Qid(value.into()))
    }
    /// Build a float as an atomic node.
    pub fn make_float(&mut self, symbol: SymbolId, value: f64) -> DagId {
        self.rt
            .make_na(&self.sig, symbol, NaValue::Float(value.to_bits()))
    }
    /// Build an exact SMT integer/rational NA node (`SMT_NumberSymbol`).
    pub fn make_smt_number(&mut self, symbol: SymbolId, value: SmtNumber) -> DagId {
        self.rt
            .make_na(&self.sig, symbol, NaValue::SmtNum(std::rc::Rc::new(value)))
    }

    pub fn node(&self, id: DagId) -> &DagNode {
        self.rt.node(id)
    }
    pub fn sort_of(&self, id: DagId) -> SortId {
        self.rt.sort_of(id)
    }
    /// The canonical total order on DAG nodes (`DagNode::compare`) used by theory normalization.
    pub(crate) fn dag_compare(&self, a: DagId, b: DagId) -> Ordering {
        self.rt.dag_compare(a, b)
    }
    /// Number of live DAG nodes (post-GC this is the reachable set).
    pub fn live_nodes(&self) -> usize {
        self.rt.live_nodes()
    }
    /// Peak DAG-arena capacity (high-water mark of allocated slots; stays bounded when GC runs).
    pub fn node_capacity(&self) -> usize {
        self.rt.node_capacity()
    }

    // ---- garbage collection ----

    /// Pin `id` as a GC root for as long as the returned [`RootGuard`] lives.
    /// The guard registers the root on construction and releases it on `Drop`; it holds a shared
    /// handle to the registry rather than borrowing the engine, so the caller can keep it alive
    /// across `&mut self` calls like [`reduce`](Self::reduce).
    ///
    /// Bind the guard to a named local (`let _g = engine.root(id);`). `let _ = engine.root(id)` drops
    /// it immediately, releasing the root on the same line — and `#[must_use]` does *not* flag the
    /// discarding `let _` form. `id` is not validated here; a stale or cross-engine handle surfaces at
    /// the next collection, not at this call.
    pub fn root(&self, id: DagId) -> RootGuard {
        self.rt.root(id)
    }

    /// Collect every DAG node not reachable from a live [`RootGuard`], a cached identity DAG, or from
    /// `extra_roots`; returns the number reclaimed. Roots pinned by guards and permanent identity cache
    /// entries are *always* included, so callers normally pass `[]`; `extra_roots` is the advanced entry
    /// point for roots not (yet) held by a guard — e.g. the `examples/peano` benchmark, which roots a
    /// term inline.
    pub fn gc(&mut self, extra_roots: impl IntoIterator<Item = DagId>) -> usize {
        self.rt.gc(extra_roots)
    }

    /// Enable (or disable) safe-point GC during [`reduce`](Self::reduce). `Some(interval)` collects
    /// at the reduce loop head once `interval` DAG nodes have been allocated since the last
    /// collection; `None` (default) disables it, so callers collect between reductions instead.
    ///
    /// **Rooting contract.** Once this is enabled, a collection can run *during* `reduce`. Any `DagId`
    /// you keep across a later allocation or `reduce` call — including the result of an *earlier*
    /// `reduce` — must be pinned with [`root`](Self::root), or that collection may reclaim it (it is
    /// not reachable from the in-progress reduction's working set). Using an unrooted, reclaimed
    /// handle panics in debug (the generational check) and is a silent wrong answer in release.
    pub fn set_gc_interval(&mut self, interval: Option<u64>) {
        self.rt.set_gc_interval(interval);
    }

    // ---- equations + reduction ----

    /// Register an unconditional equation and invalidate canonical-form caches by advancing the equation
    /// epoch.
    pub fn add_equation(&mut self, eq: Equation) -> u32 {
        self.rank_term_variable_sorts(&[&eq.lhs, &eq.rhs]);
        self.sig.add_equation(eq)
    }

    /// Register a conditional equation. All fragments must hold; failure resumes the next matcher
    /// solution.
    pub fn add_conditional_equation(
        &mut self,
        lhs: Term,
        rhs: Term,
        nr_vars: u32,
        condition: Vec<ConditionFragment>,
    ) -> u32 {
        self.rank_term_variable_sorts(&[&lhs, &rhs]);
        self.sig
            .add_conditional_equation(lhs, rhs, nr_vars, condition)
    }

    /// Register an optional conditional fallback equation, considered only after ordinary equations fail.
    pub fn add_owise_equation(
        &mut self,
        lhs: Term,
        rhs: Term,
        nr_vars: u32,
        condition: Vec<ConditionFragment>,
    ) -> u32 {
        self.rank_term_variable_sorts(&[&lhs, &rhs]);
        self.sig.add_owise_equation(lhs, rhs, nr_vars, condition)
    }

    /// Register an executable equation carrying the `[variant]` attribute.
    pub fn add_variant_equation(
        &mut self,
        lhs: Term,
        rhs: Term,
        nr_vars: u32,
        condition: Vec<ConditionFragment>,
        owise: bool,
    ) -> u32 {
        self.rank_term_variable_sorts(&[&lhs, &rhs]);
        self.sig
            .add_variant_equation(lhs, rhs, nr_vars, condition, owise)
    }

    /// Whether `pattern` has at least one equation-style match against `subject`, optionally with a
    /// theory extension. Unlike [`match_solutions`](Self::match_solutions), this keeps the matcher in
    /// rewrite mode (`command = false`), which is the contract used by variant-equation reducibility.
    pub(crate) fn has_equation_match(
        &mut self,
        pattern: &Term,
        nr_vars: u32,
        subject: DagId,
        extension: bool,
    ) -> bool {
        let automaton = LhsAutomaton::compile(pattern.clone(), &self.sig);
        let mut subst = Subst::new();
        subst.reset(nr_vars);
        let Some(mut subproblem) =
            automaton.match_(&self.rt, &self.sig, subject, &mut subst, extension, false)
        else {
            return false;
        };
        subproblem.next(&mut self.rt, &self.sig, &mut subst)
    }

    /// Whether retained patterns match candidate DAGs under one shared substitution. Variant folding
    /// uses matching rather than unification so AU matching remains complete.
    pub(crate) fn shared_match_exists(
        &mut self,
        patterns: Vec<Term>,
        subjects: &[DagId],
        nr_vars: u32,
    ) -> bool {
        fn exists(
            index: usize,
            pairs: &[(Term, DagId)],
            rt: &mut Runtime,
            sig: &Signature,
            subst: &mut Subst,
        ) -> bool {
            if index == pairs.len() {
                return true;
            }
            let (pattern, subject) = &pairs[index];
            let automaton = LhsAutomaton::compile(pattern.clone(), sig);
            let checkpoint = subst.clone();
            if let Some(mut subproblem) = automaton.match_(rt, sig, *subject, subst, false, false) {
                while subproblem.next(rt, sig, subst) {
                    if exists(index + 1, pairs, rt, sig, subst) {
                        return true;
                    }
                }
            }
            *subst = checkpoint;
            false
        }
        if patterns.len() != subjects.len() {
            return false;
        }
        let pairs: Vec<_> = patterns.into_iter().zip(subjects.iter().copied()).collect();
        let mut subst = Subst::new();
        subst.reset(nr_vars);
        exists(0, &pairs, &mut self.rt, &self.sig, &mut subst)
    }

    /// Register an unconditional membership axiom. Its compiled matcher is indexed for direct and
    /// top-collapsing candidates; sort refinement occurs lazily at reduction normal form.
    pub fn add_membership(&mut self, mb: Membership) -> u32 {
        self.rank_term_variable_sorts(&[&mb.lhs]);
        self.sig.add_membership(mb)
    }

    /// Register a conditional membership. An empty condition is equivalent to a plain membership.
    pub fn add_conditional_membership(
        &mut self,
        lhs: Term,
        sort: SortId,
        nr_vars: u32,
        condition: Vec<ConditionFragment>,
    ) -> u32 {
        self.rank_term_variable_sorts(&[&lhs]);
        self.sig
            .add_conditional_membership(lhs, sort, nr_vars, condition)
    }

    /// Register an unconditional rule, returning its dense per-module id. Rules are applied only by
    /// rewriting and search, never by [`reduce`](Self::reduce).
    pub fn add_rule(&mut self, lhs: Term, rhs: Term, nr_vars: u32) -> u32 {
        self.rank_term_variable_sorts(&[&lhs, &rhs]);
        self.sig.add_rule(lhs, rhs, nr_vars)
    }

    /// Register an executable rule while sharing its source label with frontend trace metadata.
    pub fn add_labelled_rule(
        &mut self,
        lhs: Term,
        rhs: Term,
        nr_vars: u32,
        label: Option<std::rc::Rc<str>>,
    ) -> u32 {
        self.rank_term_variable_sorts(&[&lhs, &rhs]);
        self.sig.add_labelled_rule(lhs, rhs, nr_vars, label)
    }

    /// Register a conditional rule. It accepts the equation condition fragments plus rewrite fragments
    /// of the form `term => pattern`.
    pub fn add_conditional_rule(
        &mut self,
        lhs: Term,
        rhs: Term,
        nr_vars: u32,
        condition: Vec<ConditionFragment>,
    ) -> u32 {
        self.rank_term_variable_sorts(&[&lhs, &rhs]);
        self.sig.add_conditional_rule(lhs, rhs, nr_vars, condition)
    }

    /// Register a labelled conditional rule.
    pub fn add_labelled_conditional_rule(
        &mut self,
        lhs: Term,
        rhs: Term,
        nr_vars: u32,
        condition: Vec<ConditionFragment>,
        label: Option<std::rc::Rc<str>>,
    ) -> u32 {
        self.rank_term_variable_sorts(&[&lhs, &rhs]);
        self.sig
            .add_labelled_conditional_rule(lhs, rhs, nr_vars, condition, label)
    }

    /// Retain a rule for `smt-search`, including `[nonexec]` rules. Equality conditions become solver
    /// constraints; this registration does not make the rule executable by ordinary rewriting.
    pub fn add_smt_rule(
        &mut self,
        lhs: Term,
        rhs: Term,
        variable_sorts: Vec<SortId>,
        variable_names: Vec<String>,
        condition: Vec<ConditionFragment>,
    ) {
        if self.sig.smt_info.conjunction().is_none() {
            return;
        }
        self.rank_term_variable_sorts(&[&lhs, &rhs]);
        for &sort in &variable_sorts {
            self.variable_symbol(sort);
        }
        self.sig
            .add_smt_rule(lhs, rhs, variable_sorts, variable_names, condition);
    }

    /// Retain an unconditional `[narrowing]` rule for symbolic search. Registration is independent of
    /// ordinary rule compilation, so `[nonexec narrowing]` and bare-variable lhs rules remain usable.
    #[allow(clippy::too_many_arguments)]
    pub fn add_narrowing_rule(
        &mut self,
        lhs: Term,
        rhs: Term,
        variables: Vec<crate::unify::problem::VarSpec>,
        variable_names: Vec<String>,
        condition: Vec<ConditionFragment>,
        label: Option<String>,
        nonexec: bool,
    ) -> u32 {
        self.rank_term_variable_sorts(&[&lhs, &rhs]);
        let id = self.sig.narrowing_rules.len() as u32;
        let rule = crate::narrow::compile_narrowing_rule(
            self,
            id,
            lhs,
            rhs,
            variables,
            variable_names,
            condition,
            label,
            nonexec,
        );
        self.sig.narrowing_rules.push(rule);
        id
    }

    pub fn narrowing_rules(&self) -> &[crate::narrow::NarrowingRule] {
        &self.sig.narrowing_rules
    }

    /// Reorder executable rules by dense id without changing ids or trace metadata. Reflection calls
    /// this after an AC-canonical RuleSet has erased source declaration order.
    pub fn reorder_rules(&mut self, ordered_ids: &[u32]) {
        let mut ranks = vec![usize::MAX; self.sig.next_rule_id as usize];
        for (rank, &id) in ordered_ids.iter().enumerate() {
            if let Some(slot) = ranks.get_mut(id as usize) {
                *slot = rank;
            }
        }
        for rules in self.sig.rules.values_mut() {
            rules.sort_by_key(|rule| ranks.get(rule.id as usize).copied().unwrap_or(usize::MAX));
        }
    }

    /// Begin a rule-fair rewrite session: reduce to canonical form, then apply the
    /// first rule at the top-down-first redex. Returns a resumable [`Rewriting`] — drive it with
    /// [`Rewriting::run`] (bound or unbounded) and resume with `continue`. The session keeps its current
    /// term GC-rooted, so it can be stored between REPL commands.
    pub fn rewrite(&mut self, initial: DagId) -> Rewriting {
        self.sig.mark_host_execution();
        let root = self.root(initial);
        Rewriting::new_rule_fair(root, initial)
    }

    /// One rule-fair step (used by [`Rewriting::run`]): apply the first rule at the top-down-first redex
    /// of `current`, returning the rebuilt root, or `None` at a normal form. `cursors` carries the
    /// per-symbol round-robin rule cursor across steps.
    pub(crate) fn rewrite_step(
        &mut self,
        current: DagId,
        cursors: &mut HashMap<SymbolId, u32>,
    ) -> Result<Option<DagId>, ReducerFault> {
        self.rt.rewrite_step(&self.sig, current, cursors)
    }

    /// Apply the first rule at `node` using the per-symbol round-robin cursor. Position-fair rewriting
    /// and search use this entry directly instead of the top-down [`rewrite_step`](Self::rewrite_step).
    pub(crate) fn rewrite_at(
        &mut self,
        node: DagId,
        cursors: &mut HashMap<SymbolId, u32>,
    ) -> Result<Option<DagId>, ReducerFault> {
        self.rt
            .apply_first_rule_at(&self.sig, node, cursors)
            .map(|result| result.map(|(_, rewritten)| rewritten))
    }

    /// Apply the first applicable rule in one `erewrite` class—object-message or generic leftover—at
    /// `node`.
    fn rewrite_at_filtered(
        &mut self,
        node: DagId,
        cursors: &mut HashMap<SymbolId, u32>,
        filter: RuleFilter,
    ) -> Result<Option<DagId>, ReducerFault> {
        self.rt
            .apply_first_rule_filtered(&self.sig, node, cursors, Some(filter))
            .map(|result| result.map(|(_, rewritten)| rewritten))
    }

    /// Whether the config operator `sym` has a generic `LeftOver` rule, enabling the scheduler's
    /// non-object-message rewrite path.
    fn has_leftover_rules(&self, sym: SymbolId) -> bool {
        self.sig
            .rules
            .get(&sym)
            .is_some_and(|rs| rs.iter().any(|r| r.oo == OoRuleKind::LeftOver))
    }

    /// Begin a search from `initial`, panicking if equational normalization invokes a failing reducer.
    /// Use [`try_search`](Self::try_search) to preserve reducer failures.
    pub fn search(
        &mut self,
        initial: DagId,
        goal: Term,
        nr_vars: u32,
        such_that: Vec<ConditionFragment>,
        arrow: Arrow,
        max_depth: Option<u32>,
    ) -> Search {
        self.try_search(initial, goal, nr_vars, such_that, arrow, max_depth)
            .unwrap_or_else(|fault| panic!("{fault}"))
    }

    /// Fallible form of [`search`](Self::search).
    pub fn try_search(
        &mut self,
        initial: DagId,
        goal: Term,
        nr_vars: u32,
        such_that: Vec<ConditionFragment>,
        arrow: Arrow,
        max_depth: Option<u32>,
    ) -> Result<Search, ReducerFault> {
        self.sig.mark_host_execution();
        let goal = LhsAutomaton::compile(goal, &self.sig);
        // A `such that` condition may contain a rewrite (`=>`) fragment (a nested search), so it compiles
        // with the rule owner.
        let such_that = self.sig.compile_condition(such_that, CondOwner::Rule);
        // State 0 is the reduced initial term; its reduction's rewrites count toward the search total
        // (they stay in the engine counter, read live for state 0's snapshot).
        let reduced = self.try_reduce(initial)?;
        let root = self.root(reduced);
        Ok(Search::new(
            root, reduced, goal, nr_vars, such_that, arrow, max_depth,
        ))
    }

    /// Turn `smt-search`'s `such that` equality fragments into the initial accumulated constraint.
    /// The supplied DAGs are the symbolic values of the condition's variable slots.
    pub fn make_smt_constraint(
        &mut self,
        condition: &[ConditionFragment],
        variables: &[DagId],
    ) -> Result<DagId, String> {
        let mut subst = Subst::new();
        subst.reset(variables.len() as u32);
        for (slot, &variable) in variables.iter().enumerate() {
            subst.bind(slot as u32, variable);
        }
        let constraint = self
            .rt
            .smt_condition_constraint(&self.sig, condition, &subst)
            .map_err(|()| "unsupported SMT-search condition".to_string())?;
        match constraint {
            Some(constraint) => Ok(constraint),
            None => {
                let true_symbol = self
                    .sig
                    .smt_info
                    .true_symbol()
                    .ok_or_else(|| "module has no SMT true operator".to_string())?;
                Ok(self.rt.make_free(&self.sig, true_symbol, Vec::new()))
            }
        }
    }

    /// Begin a breadth-first symbolic rewrite search modulo SMT. States and constraints are not reduced;
    /// the module restriction gate guarantees there are no equations or memberships.
    #[allow(clippy::too_many_arguments)]
    pub fn smt_search(
        &mut self,
        initial: DagId,
        initial_constraint: DagId,
        goal: Term,
        goal_nr_vars: u32,
        goal_smt_variables: Vec<(u32, DagId)>,
        arrow: Arrow,
        max_depth: Option<u32>,
        variable_names: Vec<String>,
    ) -> SmtSearch {
        self.sig.mark_host_execution();
        self.smt_search_from_fresh_base(
            initial,
            initial_constraint,
            goal,
            goal_nr_vars,
            goal_smt_variables,
            arrow,
            max_depth,
            variable_names,
            Nat::zero(),
        )
    }

    /// Begin an SMT search whose fresh rule variables start strictly above an arbitrary-precision
    /// decimal base. Object-level commands use zero through [`Self::smt_search`].
    #[allow(clippy::too_many_arguments)]
    pub fn smt_search_with_fresh_base(
        &mut self,
        initial: DagId,
        initial_constraint: DagId,
        goal: Term,
        goal_nr_vars: u32,
        goal_smt_variables: Vec<(u32, DagId)>,
        arrow: Arrow,
        max_depth: Option<u32>,
        variable_names: Vec<String>,
        fresh_base_decimal: &str,
    ) -> Option<SmtSearch> {
        self.sig.mark_host_execution();
        let fresh_base = Nat::from_decimal(fresh_base_decimal)?;
        Some(self.smt_search_from_fresh_base(
            initial,
            initial_constraint,
            goal,
            goal_nr_vars,
            goal_smt_variables,
            arrow,
            max_depth,
            variable_names,
            fresh_base,
        ))
    }

    #[allow(clippy::too_many_arguments)]
    fn smt_search_from_fresh_base(
        &mut self,
        initial: DagId,
        initial_constraint: DagId,
        goal: Term,
        goal_nr_vars: u32,
        goal_smt_variables: Vec<(u32, DagId)>,
        arrow: Arrow,
        max_depth: Option<u32>,
        variable_names: Vec<String>,
        fresh_base: Nat,
    ) -> SmtSearch {
        let goal = LhsAutomaton::compile(goal, &self.sig);
        SmtSearch::new(
            self,
            initial,
            initial_constraint,
            goal,
            goal_nr_vars,
            goal_smt_variables,
            arrow,
            max_depth,
            variable_names,
            fresh_base,
        )
    }

    pub(crate) fn smt_state_successors(
        &mut self,
        state: DagId,
        avoid_variable_number: &Nat,
        next_variable_slot: &mut u32,
    ) -> Vec<RawSmtSuccessor> {
        self.rt
            .smt_state_successors(&self.sig, state, avoid_variable_number, next_variable_slot)
    }

    pub(crate) fn smt_goal_matches(
        &mut self,
        goal: &LhsAutomaton,
        nr_vars: u32,
        smt_variables: &[(u32, DagId)],
        state: DagId,
    ) -> Vec<RawSmtGoalMatch> {
        self.rt
            .smt_goal_matches(&self.sig, goal, nr_vars, smt_variables, state)
    }

    /// Whether `constraint` is the signature's literal SMT `true` constant, the accumulated constraint
    /// of a state that no non-trivial `such that` formula or rule condition has constrained.
    pub(crate) fn is_smt_true(&self, constraint: DagId) -> bool {
        self.sig
            .smt_info
            .true_symbol()
            .is_some_and(|true_symbol| self.rt.node(constraint).symbol() == true_symbol)
    }

    pub(crate) fn smt_conjoin_constraints(
        &mut self,
        accumulated: DagId,
        local: Option<DagId>,
    ) -> DagId {
        let Some(local) = local else {
            return accumulated;
        };
        if self.is_smt_true(accumulated) {
            return local;
        }
        self.rt
            .smt_conjoin(&self.sig, Some(accumulated), local)
            .expect("SMT conjunction metadata checked by the module gate")
            .expect("conjoining two constraints is non-empty")
    }

    pub(crate) fn smt_conjoin_goal_constraints(
        &mut self,
        accumulated: DagId,
        matched: Option<DagId>,
    ) -> DagId {
        let Some(matched) = matched else {
            return accumulated;
        };
        self.rt
            .smt_conjoin(&self.sig, Some(accumulated), matched)
            .expect("SMT conjunction metadata checked by the module gate")
            .expect("conjoining two constraints is non-empty")
    }

    pub(crate) fn count_smt_rewrite(&mut self) {
        self.rt.rewrite_count += 1;
    }

    /// Structural hash of the DAG at `id`, consistent with [`deep_equal`](Self::deep_equal) — the `search`
    /// state-graph hash-cons key.
    pub(crate) fn dag_hash(&self, id: DagId) -> u64 {
        self.rt.dag_hash(id)
    }

    /// Every raw rule result one step from `root`, with equation-enumeration work deferred until the
    /// graph consumes the corresponding result.
    pub(crate) fn state_successors(&mut self, root: DagId) -> Result<RawSuccessors, ReducerFault> {
        self.rt.state_successors_deferred(&self.sig, root)
    }

    pub(crate) fn replay_graph_rewrites(&mut self, rewrites: u64) {
        self.rt.add_rewrites(rewrites);
    }

    /// Count one rule application and reduce its successor to canonical state form. Interleaving the
    /// increment with reduction preserves each discovered state's rewrite-count snapshot.
    pub(crate) fn reduce_successor(&mut self, succ: DagId) -> Result<DagId, ReducerFault> {
        self.rt
            .reduce_graph_successor(&self.sig, succ, &mut NullDescent)
    }

    /// Match the compiled `goal` (filtered by `such_that`) against `state`, returning `(bindings,
    /// rewrites-at-acceptance)` per solution — the `search` goal test. The rewrite count is snapshotted
    /// after each solution's `such that` condition evaluation, so the per-solution `rewrites:` count bills
    /// the condition's reductions.
    pub(crate) fn eval_goal(
        &mut self,
        goal: &LhsAutomaton,
        nr_vars: u32,
        such_that: &[CompiledFragment],
        state: DagId,
    ) -> Result<Vec<(Vec<DagId>, u64)>, ReducerFault> {
        self.rt
            .eval_goal(&self.sig, goal, nr_vars, such_that, state)
    }

    /// Begin a position-fair `frewrite` session over `initial`, allowing `gas` rule applications per
    /// position per traversal pass. Returns a resumable [`Rewriting`] driven by [`Rewriting::run`].
    pub fn frewrite(&mut self, initial: DagId, gas: u64) -> Rewriting {
        self.sig.mark_host_execution();
        let root = self.root(initial);
        Rewriting::new_position_fair(root, initial, gas)
    }

    /// Run one position-fair traversal pass in post-order, left to right. Each non-frozen position gets
    /// up to `gas` rule applications, with equational reduction between applications. `remaining` bounds
    /// rewrites across the run; `progress` records whether another pass is needed.
    ///
    /// The deterministic traversal order may affect the intermediate result of a bounded `frewrite`.
    pub(crate) fn frewrite_pass(
        &mut self,
        node: DagId,
        gas: u64,
        remaining: &mut Option<u64>,
        progress: &mut bool,
        cursors: &mut HashMap<SymbolId, u32>,
    ) -> Result<DagId, ReducerFault> {
        if *remaining == Some(0) {
            return Ok(node); // bound exhausted — leave the rest of the term as it stands
        }
        // 1. Recurse into the non-frozen children first (post-order), rebuilding the node if any changed.
        let symbol = self.node(node).symbol();
        let children: Vec<DagId> = self.node(node).children().collect();
        let mut new_children = Vec::with_capacity(children.len());
        let mut changed = false;
        for (pos, &c) in children.iter().enumerate() {
            if *remaining == Some(0) || self.symbol(symbol).is_frozen_arg(pos) {
                new_children.push(c); // frozen (rules blocked) or budget spent — keep as-is
            } else {
                let nc = self.frewrite_pass(c, gas, remaining, progress, cursors)?;
                changed |= nc != c;
                new_children.push(nc);
            }
        }
        let mut node = if changed {
            self.rt.rebuild_like(&self.sig, node, new_children)
        } else {
            node
        };
        // 2. A rewritten child may enable an equation here. Reduce the rebuilt parent before trying
        //    rules; frozen positions block rules, not equational reduction.
        if changed {
            node = self.try_reduce(node)?;
        }
        // 3. Apply up to `gas` rules at this node, reducing between applications. Counter redexes use
        //    the same budget and advance the counter.
        let mut g = gas;
        while g > 0 && *remaining != Some(0) {
            let fired = match self.rt.try_counter(&self.sig, node) {
                Some(result) => Some(result),
                None => self.rewrite_at(node, cursors)?,
            };
            match fired {
                Some(r) => {
                    *progress = true;
                    node = self.try_reduce(r)?;
                    g -= 1;
                    if let Some(rem) = remaining {
                        *rem -= 1;
                    }
                }
                None => break,
            }
        }
        Ok(node)
    }

    /// Begin object-message-fair rewriting of a configuration. `gas` controls deliveries per pass.
    pub fn erewrite(&mut self, initial: DagId, gas: u64) -> crate::rewrite::Rewriting {
        self.sig.mark_host_execution();
        let root = self.root(initial);
        crate::rewrite::Rewriting::new_object_message_fair(root, initial, gas)
    }

    /// Whether `id` is a `config`-tagged ACU node, which selects the object-message scheduler.
    pub(crate) fn is_config_node(&self, id: DagId) -> bool {
        let node = self.node(id);
        let symbol = self.symbol(node.symbol());

        matches!(node.term, NodeTerm::Acu { .. }) && symbol.oo.config
    }

    /// Partition a configuration and root all state needed to resume its delivery pass.
    pub(crate) fn begin_erewrite_pass(&mut self, config: DagId) -> ERewritePass {
        let config_symbol = self.node(config).symbol();
        let args: Vec<(DagId, u32)> = match &self.node(config).term {
            NodeTerm::Acu { args, .. } => args.clone(),
            _ => Vec::new(),
        };
        let mut objects: Vec<ERewriteObject> = Vec::new();
        let mut remainder = Vec::new();
        let mut portal_seen = false;
        for (element, multiplicity) in args {
            let symbol = self.node(element).symbol();
            let flags = self.symbol(symbol).oo;
            portal_seen |= flags.portal;
            if flags.object {
                let name = self
                    .node(element)
                    .children()
                    .next()
                    .expect("object constructor has a name argument");
                match objects
                    .iter_mut()
                    .find(|entry| self.rt.dag_compare(entry.name, name) == Ordering::Equal)
                {
                    Some(entry) if entry.object.is_none() => entry.object = Some(element),
                    Some(_) => remainder.push((element, multiplicity)),
                    None => objects.push(ERewriteObject {
                        name,
                        object: Some(element),
                        messages: Vec::new(),
                        next_message: 0,
                        incoming_drained: false,
                    }),
                }
                for _ in 1..multiplicity {
                    remainder.push((element, 1));
                }
            } else if flags.message {
                let target = self
                    .node(element)
                    .children()
                    .next()
                    .expect("message has a target argument");
                match objects
                    .iter_mut()
                    .find(|entry| self.rt.dag_compare(entry.name, target) == Ordering::Equal)
                {
                    Some(entry) => {
                        for _ in 0..multiplicity {
                            entry.messages.push(element);
                        }
                    }
                    None => objects.push(ERewriteObject {
                        name: target,
                        object: None,
                        messages: vec![element; multiplicity as usize],
                        next_message: 0,
                        incoming_drained: false,
                    }),
                }
            } else {
                remainder.push((element, multiplicity));
            }
        }
        objects.sort_by(|left, right| self.rt.dag_compare(left.name, right.name));
        ERewritePass {
            config_symbol,
            portal_seen,
            objects,
            next_object: 0,
            remainder,
            progress: false,
            awaiting_external: false,
            _roots: vec![self.root(config)],
        }
    }

    /// Advance a delivery pass until it completes or reaches one registered host target. A suspended
    /// message remains at the current cursor; [`resolve_erewrite_external`](Self::resolve_erewrite_external)
    /// consumes or restores it before the next advance.
    pub(crate) fn advance_erewrite_pass(
        &mut self,
        pass: &mut ERewritePass,
        cursors: &mut HashMap<SymbolId, u32>,
        offer_external: bool,
        descent: &mut dyn DescentOps,
    ) -> Result<ERewritePassStep, ReducerFault> {
        assert!(
            !pass.awaiting_external,
            "external request must be resolved before resuming"
        );
        while pass.next_object < pass.objects.len() {
            let object_index = pass.next_object;
            let name = pass.objects[object_index].name;
            if pass.portal_seen && !pass.objects[object_index].incoming_drained {
                let pending = std::mem::take(&mut self.rt.incoming);
                let mut rest = Vec::new();
                for incoming in pending {
                    let addressed_here = self
                        .node(incoming.node)
                        .children()
                        .next()
                        .is_some_and(|target| self.rt.dag_compare(target, name) == Ordering::Equal);
                    if addressed_here {
                        pass.objects[object_index].messages.push(incoming.node);
                        pass._roots.push(incoming._root);
                    } else {
                        rest.push(incoming);
                    }
                }
                self.rt.incoming = rest;
                pass.objects[object_index].incoming_drained = true;
            }

            while pass.objects[object_index].next_message
                < pass.objects[object_index].messages.len()
            {
                let message_index = pass.objects[object_index].next_message;
                let message = pass.objects[object_index].messages[message_index];
                if let Some(object) = pass.objects[object_index].object {
                    let pair = self.make_acu(pass.config_symbol, vec![(object, 1), (message, 1)]);
                    match self.rewrite_at_filtered(pair, cursors, RuleFilter::ObjectMessage)? {
                        Some(result) => {
                            let result = self.try_reduce_with(result, descent)?;
                            pass._roots.push(self.root(result));
                            let (object, others) = self.retrieve_object(result, name);
                            pass.objects[object_index].object = object;
                            pass.remainder
                                .extend(others.into_iter().map(|element| (element, 1)));
                            pass.progress = true;
                        }
                        None => pass.remainder.push((message, 1)),
                    }
                    pass.objects[object_index].next_message += 1;
                    continue;
                }

                if pass.portal_seen && self.handle_stream_message(name, message) {
                    pass.progress = true;
                    pass.objects[object_index].next_message += 1;
                    continue;
                }
                if pass.portal_seen && offer_external && self.is_registered_external_target(name) {
                    let message = self.reduce_external_message_payload(message, descent)?;
                    pass.objects[object_index].messages[message_index] = message;
                    pass._roots.push(self.root(message));
                    pass.awaiting_external = true;
                    return Ok(ERewritePassStep::External {
                        target: name,
                        message,
                    });
                }
                pass.remainder.push((message, 1));
                pass.objects[object_index].next_message += 1;
            }

            if let Some(object) = pass.objects[object_index].object {
                pass.remainder.push((object, 1));
            }
            pass.next_object += 1;
        }

        let remainder = self.make_acu(pass.config_symbol, std::mem::take(&mut pass.remainder));
        pass._roots.push(self.root(remainder));
        if self.has_leftover_rules(pass.config_symbol) {
            let reduced = self.try_reduce(remainder)?;
            pass._roots.push(self.root(reduced));
            if let Some(result) =
                self.rewrite_at_filtered(reduced, cursors, RuleFilter::LeftOver)?
            {
                pass.progress = true;
                pass._roots.push(self.root(result));
                return Ok(ERewritePassStep::Complete {
                    term: result,
                    progress: true,
                });
            }
            return Ok(ERewritePassStep::Complete {
                term: reduced,
                progress: pass.progress,
            });
        }
        Ok(ERewritePassStep::Complete {
            term: remainder,
            progress: pass.progress,
        })
    }

    /// Evaluate a manager request's payload while preserving its target and requester. Configuration
    /// arguments are otherwise frozen; the external-manager boundary evaluates these values before dispatch.
    fn reduce_external_message_payload(
        &mut self,
        message: DagId,
        descent: &mut dyn DescentOps,
    ) -> Result<DagId, ReducerFault> {
        let symbol = self.node(message).symbol();
        let mut args: Vec<_> = self.node(message).children().collect();
        let mut payload_roots = Vec::with_capacity(args.len().saturating_sub(2));
        for argument in args.iter_mut().skip(2) {
            let reduced = self.try_reduce_with(*argument, descent)?;
            let meta = match self.symbol(self.node(reduced).symbol()).special() {
                Some(SpecialOp::Meta { op, hooks }) => Some((*op, hooks.clone())),
                _ => None,
            };
            *argument = if let Some((op, hooks)) = meta {
                match self.with_meta_ctx(|ctx| descent.descend(ctx, op, &hooks, reduced))? {
                    Some(result) => {
                        self.rt.add_rewrites(1);
                        result
                    }
                    None => reduced,
                }
            } else {
                reduced
            };
            payload_roots.push(self.root(*argument));
        }

        let message = self.make_node(symbol, args);
        drop(payload_roots);
        Ok(message)
    }

    /// Resolve the message at a suspended pass cursor. Accepted requests are consumed; rejected requests
    /// return to the configuration unchanged.
    pub(crate) fn resolve_erewrite_external(&mut self, pass: &mut ERewritePass, accepted: bool) {
        assert!(pass.awaiting_external, "no external request is pending");
        let entry = &mut pass.objects[pass.next_object];
        let message = entry.messages[entry.next_message];
        if accepted {
            pass.progress = true;
        } else {
            pass.remainder.push((message, 1));
        }
        entry.next_message += 1;
        pass.awaiting_external = false;
    }

    /// Extract the object named `name` from a delivery result. Return that object and every other
    /// configuration element; if the rule consumed the object, return `None` and all elements as others.
    fn retrieve_object(&self, r: DagId, name: DagId) -> (Option<DagId>, Vec<DagId>) {
        let elems: Vec<(DagId, u32)> = match &self.node(r).term {
            NodeTerm::Acu { args, .. } if self.symbol(self.node(r).symbol()).oo.config => {
                args.clone()
            }
            _ => vec![(r, 1)],
        };
        let mut obj = None;
        let mut others = Vec::new();
        for (e, m) in elems {
            let is_named_object = obj.is_none()
                && self.symbol(self.node(e).symbol()).oo.object
                && self
                    .node(e)
                    .children()
                    .next()
                    .is_some_and(|a| self.rt.dag_compare(a, name) == Ordering::Equal);
            if is_named_object {
                obj = Some(e);
                for _ in 1..m {
                    others.push(e); // duplicate of the named object (defensive; mult is normally 1)
                }
            } else {
                for _ in 0..m {
                    others.push(e);
                }
            }
        }
        (obj, others)
    }

    /// Total equational rewrites applied so far.
    pub fn rewrites(&self) -> u64 {
        self.rt.rewrites()
    }
    pub fn reset_rewrites(&mut self) {
        self.rt.reset_rewrites();
    }

    /// Count one symbolic variant-narrowing step in the command's aggregate rewrite total.
    pub(crate) fn count_variant_narrowing_step(&mut self) {
        self.rt.add_rewrites(1);
        self.rt.variant_narrowing_count += 1;
    }

    pub(crate) fn count_narrowing_step(&mut self) {
        self.rt.add_rewrites(1);
        self.rt.narrowing_count += 1;
    }

    /// `(membership, rule, variant-narrowing, narrowing)` subcounts of [`Self::rewrites`].
    pub fn rewrite_breakdown(&self) -> (u64, u64, u64, u64) {
        (
            self.rt.membership_count,
            self.rt.rule_rewrite_count,
            self.rt.variant_narrowing_count,
            self.rt.narrowing_count,
        )
    }

    /// Snapshot command-visible rewrite accounting around an isolated subcontext. Narrowing `vfold`
    /// retains its subsumption searches for reuse without transferring their counts to the parent.
    pub(crate) fn rewrite_checkpoint(&self) -> (u64, u64, u64, u64, u64) {
        (
            self.rt.rewrite_count,
            self.rt.membership_count,
            self.rt.rule_rewrite_count,
            self.rt.variant_narrowing_count,
            self.rt.narrowing_count,
        )
    }

    pub(crate) fn restore_rewrite_checkpoint(&mut self, checkpoint: (u64, u64, u64, u64, u64)) {
        self.rt.rewrite_count = checkpoint.0;
        self.rt.membership_count = checkpoint.1;
        self.rt.rule_rewrite_count = checkpoint.2;
        self.rt.variant_narrowing_count = checkpoint.3;
        self.rt.narrowing_count = checkpoint.4;
    }

    pub(crate) fn semantic_checkpoint(&self) -> SemanticCheckpoint {
        self.rt.semantic_checkpoint()
    }

    pub(crate) fn restore_semantic_checkpoint(&mut self, checkpoint: SemanticCheckpoint) {
        self.rt.restore_semantic_checkpoint(checkpoint);
        self.sig.invalidate_normal_forms();
    }

    /// Reset every `counter` built-in operator to zero at the start of a top-level `rewrite`,
    /// `frewrite`, or `erewrite`. Each counter operator keeps its own sequence; `continue`
    /// deliberately preserves them.
    pub fn reset_counter(&mut self) {
        self.rt.reset_counter();
    }

    /// Snapshot every `counter` operator's next value, for fault rollback by the owning
    /// [`Rewriting`] drive (counters are not part of [`SemanticCheckpoint`]).
    pub(crate) fn counter_snapshot(&self) -> HashMap<SymbolId, u64> {
        self.rt.counter_values.clone()
    }

    /// Restore a [`counter_snapshot`](Self::counter_snapshot).
    pub(crate) fn restore_counters(&mut self, snapshot: HashMap<SymbolId, u64>) {
        self.rt.counter_values = snapshot;
    }

    /// Clear captured external stream output and the reply mailbox before a new `erewrite` command.
    pub fn reset_external(&mut self) {
        self.rt.external_out.clear();
        self.rt.external_err.clear();
        self.rt.incoming.clear();
    }
    /// Register one host-owned external target in this engine. The target is rebuilt from an owned
    /// envelope and rooted until [`unregister_external_target`](Self::unregister_external_target).
    pub fn register_external_target(
        &mut self,
        target: &MetaEnvelope,
    ) -> Option<ExternalTargetToken> {
        let (roots, mut guards) = self.with_meta_ctx(|ctx| target.build_roots(ctx))?;
        if roots.len() != 1 || guards.len() != 1 {
            return None;
        }
        let node = roots[0];
        let root = guards.pop().expect("one target root");
        let token = self.rt.next_external_target;
        self.rt.next_external_target = self
            .rt
            .next_external_target
            .checked_add(1)
            .expect("external target token space exhausted");
        self.rt
            .external_targets
            .insert(token, RootedDag { node, _root: root });
        Some(ExternalTargetToken(token))
    }

    /// Remove a previously registered host target. Stale tokens are harmless and return `false`.
    pub fn unregister_external_target(&mut self, token: ExternalTargetToken) -> bool {
        self.rt.external_targets.remove(&token.0).is_some()
    }

    fn is_registered_external_target(&self, target: DagId) -> bool {
        matches!(
            self.symbol(self.node(target).symbol()).special(),
            Some(SpecialOp::InterpreterManager)
        ) || self
            .rt
            .external_targets
            .values()
            .any(|registered| self.rt.dag_compare(registered.node, target) == Ordering::Equal)
    }

    fn queue_incoming(&mut self, node: DagId) {
        let root = self.root(node);
        self.rt.incoming.push(RootedDag { node, _root: root });
    }

    /// Transfer one accepted child result into the parent engine. Reply materialization and rewrite-count
    /// transfer happen together; a malformed envelope changes neither.
    pub(crate) fn accept_external_response(
        &mut self,
        reply: Option<&MetaEnvelope>,
        rewrites: u64,
        breakdown: ExternalRewriteBreakdown,
    ) -> bool {
        if let Some(reply) = reply {
            let Some((roots, mut guards)) = self.with_meta_ctx(|ctx| reply.build_roots(ctx)) else {
                return false;
            };
            if roots.len() != 1 || guards.len() != 1 {
                return false;
            }
            let node = roots[0];
            let root = guards.pop().expect("one reply root");
            self.rt.incoming.push(RootedDag { node, _root: root });
        }
        self.rt.add_rewrites(rewrites);
        self.rt.membership_count += breakdown.membership_applications;
        self.rt.rule_rewrite_count += breakdown.rule_rewrites;
        self.rt.variant_narrowing_count += breakdown.variant_narrowing_steps;
        self.rt.narrowing_count += breakdown.narrowing_steps;
        true
    }

    /// Take captured `stdout` writes from the last `erewrite` run before rendering its result lines.
    pub fn take_external_out(&mut self) -> String {
        std::mem::take(&mut self.rt.external_out)
    }
    /// Take the captured `stderr` writes from the last `erewrite` run.
    pub fn take_external_err(&mut self) -> String {
        std::mem::take(&mut self.rt.external_err)
    }

    /// Set the pending scripted `stdin` input consumed by `getLine`.
    pub fn set_external_input(&mut self, input: String) {
        self.rt.external_in = input;
    }
    /// Take back the unread `stdin` input (the REPL threads it across `erewrite` commands).
    pub fn take_external_input(&mut self) -> String {
        std::mem::take(&mut self.rt.external_in)
    }

    /// Handle a standard-stream manager request. Output writes emit text and queue `wrote(me, self)`;
    /// `getLine` consumes scripted input and queues `gotLine(me, self, line)`. Returns whether a request
    /// was recognized and consumed.
    fn handle_stream_message(&mut self, name: DagId, msg: DagId) -> bool {
        let Some(SpecialOp::StreamManager {
            stream,
            string_sym,
            write_msg,
            wrote_msg,
            get_line_msg,
            got_line_msg,
        }) = self.symbol(self.node(name).symbol()).special.clone()
        else {
            return false;
        };
        let msg_sym = self.node(msg).symbol();
        let args: Vec<DagId> = self.node(msg).children().collect();
        // `write(self, me, str)` → emit `str`, reply `wrote(me, self)` (stdout/stderr).
        if Some(msg_sym) == write_msg && matches!(stream, StdStream::Stdout | StdStream::Stderr) {
            if args.len() != 3 {
                return false;
            }
            let (me, target, payload) = (args[1], args[0], args[2]);
            let Some(text) = self.rt.as_str(payload) else {
                return false;
            };
            // The buffers are `String`; strings are bytes — decode lossily at this I/O boundary (the
            // pinned STD-STREAM traffic is ASCII, so this is exact for it).
            let text = String::from_utf8_lossy(&text);
            match stream {
                StdStream::Stdout => self.rt.external_out.push_str(&text),
                StdStream::Stderr => self.rt.external_err.push_str(&text),
                StdStream::Stdin => unreachable!(),
            }
            if let Some(wrote) = wrote_msg {
                let reply = self.make_free(wrote, vec![me, target]); // wrote(me, self) — swap arg0/arg1
                self.queue_incoming(reply);
            }
            return true;
        }
        // `getLine(self, me, prompt)` (stdin) → write `prompt` to stdout, consume one line from the
        // scripted input buffer, and reply `gotLine(me, self, line)`.
        if Some(msg_sym) == get_line_msg && stream == StdStream::Stdin {
            if args.len() != 3 {
                return false;
            }
            let (me, target, prompt) = (args[1], args[0], args[2]);
            if let Some(p) = self.rt.as_str(prompt) {
                self.rt.external_out.push_str(&String::from_utf8_lossy(&p)); // the prompt goes to stdout
            }
            let line = self.rt.read_line();
            if let (Some(got), Some(str_sym)) = (got_line_msg, string_sym) {
                let line_dag = self.rt.make_na(
                    &self.sig,
                    str_sym,
                    crate::dag::NaValue::Str(line.into_bytes().into()),
                );
                let reply = self.make_free(got, vec![me, target, line_dag]); // gotLine(me, self, line)
                self.queue_incoming(reply);
            }
            return true;
        }
        false
    }

    /// Enable or disable reduction tracing. When on, [`reduce`](Self::reduce) records a structured
    /// [`TraceEvent`] stream; collect it with [`take_trace`](Self::take_trace). Disabling drops any
    /// buffered events. Intended for the REPL (which runs with in-reduction GC off).
    pub fn set_trace(&mut self, on: bool) {
        self.rt.trace = on.then(Vec::new);
        self.rt.condition_depth = 0;
    }

    /// Enable whole-root reconstruction for each trace rewrite. This allocates per rewrite, is disabled
    /// by default, and only acts while tracing.
    pub fn set_record_whole(&mut self, on: bool) {
        self.rt.record_whole = on;
    }

    /// Whether tracing is currently enabled.
    pub fn is_tracing(&self) -> bool {
        self.rt.trace.is_some()
    }

    /// Take the recorded trace events, clearing the buffer (tracing stays enabled). Empty when off.
    pub fn take_trace(&mut self) -> Vec<TraceEvent> {
        self.rt
            .trace
            .as_mut()
            .map(std::mem::take)
            .unwrap_or_default()
    }

    /// Take model-check statistics recorded since the previous call.
    pub fn take_model_check_stats(&mut self) -> Vec<ModelCheckStats> {
        std::mem::take(&mut self.rt.model_check_stats)
    }

    /// Take LTL satisfiability statistics recorded since the previous call.
    pub fn take_sat_solve_stats(&mut self) -> Vec<SatSolveStats> {
        std::mem::take(&mut self.rt.sat_solve_stats)
    }

    /// Open a construction-only structural-deduplication window. Equal nodes built through the standard
    /// construction funnel share one DAG identity. The window must not contain reduction or collection
    /// and must be closed with [`end_dedup`](Self::end_dedup).
    pub fn begin_dedup(&mut self) {
        self.rt.begin_dedup();
    }

    /// Close the dedup window opened by [`begin_dedup`](Self::begin_dedup).
    pub fn end_dedup(&mut self) {
        self.rt.end_dedup();
    }

    /// Reduce `root` to canonical form by innermost equational simplification. Canonical nodes and shared
    /// forwarding targets are reused. An explicit frame stack avoids subject-depth recursion while
    /// preserving left-to-right child order, top rewriting, and rewrite counts.
    ///
    /// Panics when a configured reducer reports a contract fault. Embeddings should use
    /// [`try_reduce`](Self::try_reduce) to handle that fault.
    #[must_use]
    pub fn reduce(&mut self, root: DagId) -> DagId {
        self.try_reduce(root)
            .unwrap_or_else(|fault| panic!("{fault}"))
    }

    /// Fallible form of [`reduce`](Self::reduce).
    pub fn try_reduce(&mut self, root: DagId) -> Result<DagId, ReducerFault> {
        self.sig.mark_host_execution();
        let checkpoint = self.semantic_checkpoint();
        let result = self.rt.reduce(&self.sig, root, &mut NullDescent);
        if result.is_err() {
            self.restore_semantic_checkpoint(checkpoint);
        }
        result
    }

    /// Like [`reduce`](Self::reduce) but driving META-LEVEL descent through `descent`: a `metaReduce`/…
    /// redex encountered during reduction is handed to the handler (which builds the object module and
    /// runs the operation). Panics on reducer faults; embeddings should use
    /// [`try_reduce_with`](Self::try_reduce_with).
    #[must_use]
    pub fn reduce_with(&mut self, root: DagId, descent: &mut dyn DescentOps) -> DagId {
        self.try_reduce_with(root, descent)
            .unwrap_or_else(|fault| panic!("{fault}"))
    }

    /// Fallible form of [`reduce_with`](Self::reduce_with).
    pub fn try_reduce_with(
        &mut self,
        root: DagId,
        descent: &mut dyn DescentOps,
    ) -> Result<DagId, ReducerFault> {
        self.sig.mark_host_execution();
        let checkpoint = self.semantic_checkpoint();
        let result = self.rt.reduce(&self.sig, root, descent);
        if result.is_err() {
            self.restore_semantic_checkpoint(checkpoint);
        }
        result
    }

    /// Internal symbolic-driver reduction. The first reducer fault is retained until the enclosing
    /// fallible driver boundary retrieves it.
    pub(crate) fn reduce_or_defer_fault(&mut self, root: DagId) -> DagId {
        self.sig.mark_host_execution();
        self.rt
            .reduce_or_defer_fault(&self.sig, root, &mut NullDescent)
    }

    /// Retrieve a reducer fault deferred by an internal symbolic driver.
    pub(crate) fn check_deferred_reducer_fault(&mut self) -> Result<(), ReducerFault> {
        self.rt.check_reducer_fault()
    }
    /// Seal host attachment before a semantic operation implemented outside this module.
    pub(crate) fn begin_symbolic_execution(&self) {
        self.sig.mark_symbolic_execution();
    }

    pub(crate) fn defer_reducer_fault(&mut self, fault: ReducerFault) {
        self.rt.defer_reducer_fault(fault);
    }

    /// Try to match pattern `pat` against `subject`, filling `subst` (which must already be
    /// [`Subst::reset`] to the pattern's variable count). Returns `true` on success; on failure
    /// `subst` may hold partial bindings, so callers reset before each attempt.
    #[must_use]
    pub fn match_pattern(&self, pat: &Term, subject: DagId, subst: &mut Subst) -> bool {
        self.rt.match_pattern(&self.sig, pat, subject, subst)
    }

    /// Structural equality of two DAG nodes.
    #[must_use]
    pub fn deep_equal(&self, a: DagId, b: DagId) -> bool {
        self.rt.deep_equal(a, b)
    }

    /// The argument positions below `node` that a rule-position enumerator visits, as
    /// `(physical child index, child)` pairs in [`DagNode::children`] order, omitting physical indices
    /// for which `frozen` holds. The copies of a repeated element of an associative-commutative node
    /// are one position, addressed through the first non-frozen copy. The arguments of every other
    /// theory are separate positions, even when they are equal.
    #[must_use]
    pub fn redex_arguments(
        &self,
        node: DagId,
        frozen: impl Fn(usize) -> bool,
    ) -> Vec<(usize, DagId)> {
        self.rt.redex_arguments(node, frozen)
    }

    /// Build a DAG instance of `term` under `subst` (the rhs of a matched equation).
    pub fn instantiate(&mut self, term: &Term, subst: &Subst) -> DagId {
        self.rt.instantiate(&self.sig, term, subst)
    }

    /// Build a DAG instance of `term` under explicit `bindings` (variable index → value) — a match
    /// solution's bindings captured from a [`Solutions`] stream. The META-LEVEL `metaApply`/`metaXapply`
    /// descent uses it to build a named rule's rhs from the bindings of matching its lhs.
    pub fn instantiate_bindings(&mut self, term: &Term, bindings: &[DagId]) -> DagId {
        let mut subst = Subst::new();
        subst.reset(bindings.len() as u32);
        for (i, &b) in bindings.iter().enumerate() {
            subst.bind(i as u32, b);
        }
        self.instantiate(term, &subst)
    }
    /// Instantiate a rule RHS under explicit bindings and splice it through a detached match residue.
    /// Callers can release the solution stream, extend its bindings while solving conditions, and then
    /// reconstruct the result from the captured context.
    pub fn instantiate_rewrite_result(
        &mut self,
        rhs: &Term,
        bindings: &[DagId],
        context: &RewriteMatchContext,
    ) -> DagId {
        let built = self.instantiate_bindings(rhs, bindings);
        let (signature, runtime) = self.parts_mut();
        context.build_result(runtime, signature, built)
    }

    /// Begin enumerating every match of `pattern` against `subject`. `extension` permits a subterm match
    /// with a residual context; otherwise the whole subject must match. The returned [`Solutions`]
    /// exposes bindings, matched portions, and reconstruction contexts for `match` and `xmatch`.
    pub fn match_solutions(
        &mut self,
        pattern: Term,
        nr_vars: u32,
        subject: DagId,
        extension: bool,
    ) -> Solutions<'_> {
        self.match_solutions_with_bindings(pattern, nr_vars, subject, extension, &[])
    }
    /// Begin enumerating matches while preserving caller-supplied bindings for selected pattern
    /// variables. `initial[k] == Some(d)` constrains variable slot `k` to `d`; missing trailing slots
    /// and `None` entries remain unbound. This is the matcher contract used by META-LEVEL's partial
    /// substitutions for `metaApply` and `metaXapply`.
    pub fn match_solutions_with_bindings(
        &mut self,
        pattern: Term,
        nr_vars: u32,
        subject: DagId,
        extension: bool,
        initial: &[Option<DagId>],
    ) -> Solutions<'_> {
        self.match_solution_stream(pattern, nr_vars, subject, extension, initial, true)
    }

    /// Enumerate matches in rule-rewrite mode, including the subject theory's rewrite extension.
    /// Unlike the interactive `xmatch` stream this uses the matcher order and extension floors consumed
    /// by `apply_first_rule_at`; strategy-controlled rule application uses the same contract.
    pub fn rewrite_match_solutions_with_bindings(
        &mut self,
        pattern: Term,
        nr_vars: u32,
        subject: DagId,
        initial: &[Option<DagId>],
    ) -> Solutions<'_> {
        let extension = matches!(
            self.sig.symbol(self.node(subject).symbol()).theory(),
            Theory::Acu | Theory::Au | Theory::S
        );
        self.match_solution_stream(pattern, nr_vars, subject, extension, initial, false)
    }

    fn match_solution_stream(
        &mut self,
        pattern: Term,
        nr_vars: u32,
        subject: DagId,
        extension: bool,
        initial: &[Option<DagId>],
        command: bool,
    ) -> Solutions<'_> {
        // Compile and run the first (deterministic) match phase. The returned `Subproblem` owns its
        // state (no borrow of the automaton or the engine), so the throwaway `automaton` can drop here.
        let automaton = LhsAutomaton::compile(pattern.clone(), &self.sig);
        let mut subst = Subst::new();
        subst.reset(nr_vars);
        for (slot, binding) in initial.iter().copied().enumerate().take(nr_vars as usize) {
            if let Some(binding) = binding {
                subst.bind(slot as u32, binding);
            }
        }
        let subproblem = {
            let (sig, rt) = self.parts_mut();
            automaton.match_(rt, sig, subject, &mut subst, extension, command)
        };
        Solutions {
            engine: self,
            pattern,
            subproblem,
            subst,
        }
    }
}

/// A resumable stream of the matches of `pattern <=? subject`, wrapping the matcher seam's
/// `Subproblem` so callers outside the kernel can enumerate solutions without touching the
/// crate-private matcher types. Created by [`Engine::match_solutions`].
///
/// Holds `&mut Engine` because advancing a multi-solution (ACU/AU) match allocates fresh
/// binding/residue nodes between solutions while widening variable sorts — the same reason the reduce driver
/// drives `Subproblem::next` with `&mut Runtime`.
pub struct Solutions<'e> {
    engine: &'e mut Engine,
    /// Kept to reconstruct the matched portion (the instantiated pattern) on demand.
    pattern: Term,
    /// `None` when the subject could not match at all (no first-phase solution); then `advance` is
    /// always `false`. `Some` holds the live enumerator.
    subproblem: Option<Subproblem>,
    subst: Subst,
}

impl Solutions<'_> {
    /// Advance to the next solution, binding its variables into the internal substitution; returns
    /// `false` once the solutions are exhausted (and stays `false` thereafter). Read the solution with
    /// [`binding`](Self::binding) / [`matched_portion`](Self::matched_portion) before the next call.
    /// (Named `advance` rather than `next` — it returns a `bool` and the bound solution is read through
    /// the accessors, not yielded, so it is not an [`Iterator`].)
    #[must_use]
    pub fn advance(&mut self) -> bool {
        let Some(sp) = self.subproblem.as_mut() else {
            return false;
        };
        let (sig, rt) = self.engine.parts_mut();
        sp.next(rt, sig, &mut self.subst)
    }

    /// The current solution's binding for variable `index` (`None` before the first successful
    /// [`advance`](Self::advance), or if the index is out of range).
    #[must_use]
    pub fn binding(&self, index: u32) -> Option<DagId> {
        self.subst.get(index)
    }
    /// Snapshot the current solution's theory residue so result construction can happen after this
    /// stream releases its mutable engine borrow (for example, after solving a rule condition).
    #[must_use]
    pub fn rewrite_context(&self) -> RewriteMatchContext {
        self.subproblem
            .as_ref()
            .expect("rewrite_context requires a live match")
            .rewrite_context()
    }

    /// The unmatched ordered prefix and suffix for the current AU extension match.
    /// Other theories either have order-free residue or no two-sided ordered context.
    #[must_use]
    pub fn ordered_context_parts(&self) -> Option<(&[DagId], &[DagId])> {
        self.subproblem.as_ref()?.ordered_context_parts()
    }

    /// The matched portion of the subject under the current solution — the pattern instantiated with
    /// the current bindings. For a whole (`match`) match this equals the subject; for an extension
    /// (`xmatch`) match it is the matched sub-part (the subject minus the residue). Builds a fresh
    /// node, so it takes `&mut self`; valid only after a successful [`advance`](Self::advance).
    pub fn matched_portion(&mut self) -> DagId {
        self.engine.instantiate(&self.pattern, &self.subst)
    }

    /// Instantiate `rhs` under the current match and splice it into the unmatched theory residue.
    /// Valid only after a successful [`advance`](Self::advance).
    pub fn rewrite_result(&mut self, rhs: &Term) -> DagId {
        let built = self.engine.instantiate(rhs, &self.subst);
        let subproblem = self
            .subproblem
            .as_ref()
            .expect("rewrite_result requires a live match");
        let (sig, runtime) = self.engine.parts_mut();
        subproblem.build_result(runtime, sig, built)
    }

    /// Matched-portion data for `xmatch` command display. `None` means no extension information and
    /// suppresses the display line; `Some(Whole)` prints `(whole)`; `Some(Portion(dag))` carries the
    /// matched sub-part. Valid only after a successful [`advance`](Self::advance).
    pub fn matched_portion_display(&mut self) -> Option<MatchedPortion> {
        match self.subproblem.as_ref()?.matched_status()? {
            true => Some(MatchedPortion::Whole),
            false => Some(MatchedPortion::Portion(
                self.engine.instantiate(&self.pattern, &self.subst),
            )),
        }
    }
}

/// The matched portion of an `xmatch` command solution (see [`Solutions::matched_portion_display`]):
/// either the whole subject (`(whole)`) or a genuine sub-portion carrying its built DAG.
pub enum MatchedPortion {
    /// The extension match covered the whole subject and renders as `(whole)`.
    Whole,
    /// A proper sub-portion of the subject; the caller renders this DAG.
    Portion(DagId),
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::host::{
        HostFunctionCatalog, ReducerFault, ResolvedHostHooks, StrictCall, StrictOutcome,
        StrictReduceCtx, StrictReducer, StrictReducerDescriptor,
    };
    use crate::term::{ConditionFragment, Equation, Membership, Term};
    use std::panic::{AssertUnwindSafe, catch_unwind};
    use std::sync::Arc;
    use std::sync::atomic::{AtomicUsize, Ordering as AtomicOrdering};

    /// `f(a, g(a))` over a single sort `Nat`, with `a` shared (a true DAG). Returns engine + root.
    fn fixture() -> (Engine, DagId, SortId) {
        let mut e = Engine::new();
        let nat = e.add_sort("Nat");
        e.close_sorts();
        let a = e.add_op("a", vec![], nat);
        let g = e.add_op("g", vec![nat], nat);
        let f = e.add_op("f", vec![nat, nat], nat);
        let a1 = e.make_const(a);
        let ga = e.make_free(g, vec![a1]);
        let root = e.make_free(f, vec![a1, ga]);
        (e, root, nat)
    }

    /// Decode a DAG into a sorted multiset of leaf-constant names (`b + c` → `["b","c"]`), so a public
    /// `match_solutions` binding can be compared by value.
    fn leaf_names(e: &Engine, id: DagId) -> Vec<String> {
        let node = e.node(id);
        let kids: Vec<DagId> = node.children().collect();
        if kids.is_empty() {
            vec![e.symbol(node.symbol()).name().to_string()]
        } else {
            let mut out: Vec<String> = kids.into_iter().flat_map(|c| leaf_names(e, c)).collect();
            out.sort();
            out
        }
    }

    /// Invalid declaration positions are user input, not kernel invariants. Recovery ignores the
    /// complete attribute atomically and preserves any frozen metadata already installed on a symbol.
    #[test]
    fn invalid_frozen_positions_are_recoverable_and_atomic() {
        let mut e = Engine::new();
        let s = e.add_sort("S");
        e.close_sorts();
        let constant = e.add_op("c", vec![], s);
        let fresh = e.add_op("fresh", vec![s, s], s);
        let configured = e.add_op("configured", vec![s, s], s);

        assert!(!e.set_frozen(constant, &[]));
        assert!(!e.set_frozen(fresh, &[1, 3]));
        assert!(!e.is_frozen_arg(fresh, 0));
        assert!(!e.is_frozen_arg(fresh, 1));

        assert!(e.set_frozen(configured, &[2]));
        assert!(!e.set_frozen(configured, &[1, 3]));
        assert!(!e.is_frozen_arg(configured, 0));
        assert!(e.is_frozen_arg(configured, 1));
    }

    /// Rule-position enumeration addresses a repeated ACU element once, through its first non-frozen
    /// physical copy, including equal entries that construction has not merged. Equal arguments of
    /// every other theory stay separate positions, even when they are one shared node.
    #[test]
    fn redex_arguments_address_each_acu_element_once() {
        let mut e = Engine::new();
        let s = e.add_sort("S");
        e.close_sorts();
        let d = e.add_op("d", vec![], s);
        let x = e.add_op("x", vec![], s);
        let k = e.add_op("k", vec![s], s);
        let pair = e.add_op("pair", vec![s, s], s);
        let soup = e.add_op_ac("soup", vec![s, s], s, None);
        let seq = e.add_op_au("seq", vec![s, s], s, None);
        let swap = e.add_op_cui("swap", vec![s, s], s, true, false, None);

        // A merged multiset: the three copies of `d` are physical children 0..3 and `x` is child 3.
        let dd = e.make_const(d);
        let xx = e.make_const(x);
        let merged = e.make_acu(soup, vec![(dd, 3), (xx, 1)]);
        assert_eq!(
            e.node(merged).children().collect::<Vec<_>>(),
            vec![dd, dd, dd, xx]
        );
        assert_eq!(e.redex_arguments(merged, |_| false), vec![(0, dd), (3, xx)]);
        // A frozen copy defers the element to its next copy; with every index frozen nothing remains.
        assert_eq!(
            e.redex_arguments(merged, |index| index == 0),
            vec![(1, dd), (3, xx)]
        );
        assert_eq!(e.redex_arguments(merged, |_| true), vec![]);

        // Separately built equal elements are distinct unreduced entries, but still one position.
        let copies: Vec<DagId> = (0..3)
            .map(|_| {
                let inner = e.make_const(d);
                e.make_free(k, vec![inner])
            })
            .collect();
        let unmerged = e.make_ac(soup, copies.clone());
        let entries: Vec<DagId> = e.node(unmerged).children().collect();
        assert_eq!(entries.len(), 3);
        assert!(entries.iter().all(|entry| copies.contains(entry)));
        assert_ne!(entries[0], entries[1]);
        assert_eq!(
            e.redex_arguments(unmerged, |_| false),
            vec![(0, entries[0])]
        );

        // One shared node under a free, associative, or commutative operator is two positions.
        let shared = e.make_free(k, vec![dd]);
        let free = e.make_free(pair, vec![shared, shared]);
        let assoc = e.make_au(seq, vec![shared, shared]);
        let comm = e.make_cui(swap, shared, shared);
        for node in [free, assoc, comm] {
            assert_eq!(
                e.redex_arguments(node, |_| false),
                vec![(0, shared), (1, shared)]
            );
        }
    }

    /// Genuine variable leaves (`make_var` / `variable_symbol`): per-sort symbol caching in demand
    /// order and name-code identity (`deep_equal` ignores the slot index). Ordinary symbolic DAGs
    /// keep their established slot order; the pre-index unification normalizer uses name-code order.
    #[test]
    fn var_leaves_identity_and_order() {
        let mut e = Engine::new();
        let nat = e.add_sort("Nat");
        let nznat = e.add_sort("NzNat");
        e.add_subsort(nznat, nat);
        e.close_sorts();
        let plus = e.add_op_ac("+", vec![nat, nat], nat, None);

        // Per-sort variable symbols cache and record creation order.
        let vs_nat = e.variable_symbol(nat);
        let vs_nz = e.variable_symbol(nznat);
        assert_eq!(e.variable_symbol(nat), vs_nat, "same sort → cached symbol");
        assert_ne!(vs_nat, vs_nz);

        // Identity uses the variable's name code, not its substitution slot.
        let x0 = e.make_var(nat, 7, 0);
        let x1 = e.make_var(nat, 7, 1);
        let y = e.make_var(nat, 8, 2);
        assert!(
            e.deep_equal(x0, x1),
            "same name+sort, different slot: equal"
        );
        assert!(!e.deep_equal(x0, y), "different name codes differ");
        assert_eq!(
            e.sort_of(x0),
            nat,
            "a variable's sort is its symbol's range"
        );

        // Order inside an ordinary ACU DAG: same-sort variables by slot; a variable (arity 0)
        // precedes an application (arity 2) regardless of creation order.
        let z = e.make_var(nznat, 9, 3); // NzNat's variable symbol created after Nat's
        let app = e.make_ac(plus, vec![x0, y]);
        let soup = e.make_ac(plus, vec![app, z, y, x0]);
        let order: Vec<DagId> = e.node(soup).children().collect();
        assert_eq!(
            order,
            vec![x0, y, z, app],
            "name-code order, then creation order, then arity"
        );
    }

    /// Pre-index unification normalization prevents temporary source slots from determining the
    /// canonical order of same-sort variables.
    #[test]
    fn unify_normalization_orders_variables_by_name_before_reindex() {
        let mut e = Engine::new();
        let s = e.add_sort("S");
        e.close_sorts();
        let plus = e.add_op_ac("+", vec![s, s], s, None);

        let later_name = e.make_var(s, 20, 0);
        let earlier_name = e.make_var(s, 10, 1);
        let parsed = e.make_ac(plus, vec![later_name, earlier_name]);
        assert_eq!(
            e.node(parsed).children().collect::<Vec<_>>(),
            vec![later_name, earlier_name],
            "ordinary DAG construction follows the established slot order"
        );

        let normalized = e.normalize_for_unify(parsed);
        assert_eq!(
            e.node(normalized).children().collect::<Vec<_>>(),
            vec![earlier_name, later_name],
            "pre-index term normalization follows the variable name ids"
        );
    }

    #[derive(Clone)]
    struct NormalizeIdentityFault;

    impl StrictReducer for NormalizeIdentityFault {
        fn reduce<'ctx>(
            &self,
            _ctx: &mut StrictReduceCtx<'ctx>,
            _call: StrictCall<'ctx>,
        ) -> Result<StrictOutcome<'ctx>, ReducerFault> {
            Err(ReducerFault::new("raw symbolic identity fault"))
        }
    }

    fn faulting_raw_acu() -> (Engine, DagId) {
        let catalog = HostFunctionCatalog::builder()
            .register(
                "identity.normalize",
                NormalizeIdentityFault,
                StrictReducerDescriptor::builder(0).build(),
            )
            .expect("register normalization fault reducer")
            .build();
        let mut engine = Engine::with_host_functions(catalog);
        let sort = engine.add_sort("S");
        engine.close_sorts();
        let identity = engine.add_op("badIdentity", vec![], sort);
        engine
            .bind_host_function(identity, "identity.normalize", ResolvedHostHooks::default())
            .expect("bind normalization fault reducer");
        let plus = engine.add_op_ac("plus", vec![sort, sort], sort, Some(identity));
        let raw = engine.make_acu_preserving_order(plus, Vec::new());
        engine.set_trace(true);
        engine.reset_rewrites();
        (engine, raw)
    }

    #[test]
    fn symbolic_normalization_preserves_identity_fault_and_infallible_wrapper_panics() {
        let (mut fallible, raw) = faulting_raw_acu();
        let fault = fallible
            .try_normalize_for_unify(raw)
            .expect_err("raw empty ACU must materialize its identity");
        assert_eq!(
            fault.key().expect("fault key").as_str(),
            "identity.normalize"
        );
        assert_eq!(fault.message(), "raw symbolic identity fault");
        assert_eq!(fallible.rewrites(), 0);
        assert_eq!(fallible.rewrite_breakdown(), (0, 0, 0, 0));
        assert!(fallible.take_trace().is_empty());

        let repeated = fallible
            .try_normalize_for_unify(raw)
            .expect_err("failed normalization must remain retry-safe");
        assert_eq!(
            repeated.key().expect("repeated fault key").as_str(),
            "identity.normalize"
        );
        assert_eq!(repeated.message(), "raw symbolic identity fault");
        assert_eq!(fallible.rewrites(), 0);
        assert_eq!(fallible.rewrite_breakdown(), (0, 0, 0, 0));
        assert!(fallible.take_trace().is_empty());

        let (mut infallible, raw) = faulting_raw_acu();
        let panic = catch_unwind(AssertUnwindSafe(|| infallible.normalize_for_unify(raw)))
            .expect_err("documented infallible normalization must panic");
        let message = panic
            .downcast_ref::<String>()
            .map(String::as_str)
            .or_else(|| panic.downcast_ref::<&str>().copied())
            .unwrap_or("non-string panic");
        assert!(message.contains("identity.normalize"), "{message}");
    }

    /// The public matcher facade enumerates all six ACU bindings for `X + Y <=? a + b + c`; the test
    /// compares them as a set because enumeration order is not part of this API's contract. Extension
    /// matching also reports the matched `a + b` portion.
    #[test]
    fn match_solutions_enumerates_acu() {
        let mut e = Engine::new();
        let s = e.add_sort("E");
        e.close_sorts();
        let a = e.add_op("a", vec![], s);
        let b = e.add_op("b", vec![], s);
        let c = e.add_op("c", vec![], s);
        let plus = e.add_op_ac("+", vec![s, s], s, None);
        let (a0, b0, c0) = (e.make_const(a), e.make_const(b), e.make_const(c));
        let subject = e.make_ac(plus, vec![a0, b0, c0]);

        // `match X + Y <=? a + b + c` — whole match (no extension), six solutions. Collect the binding
        // ids while the stream is live, then decode after it drops (the caller pattern the frontend uses).
        let pat = Term::op(plus, vec![Term::var(0, s), Term::var(1, s)]);
        let mut ids: Vec<(DagId, DagId)> = Vec::new();
        {
            let mut sols = e.match_solutions(pat, 2, subject, false);
            while sols.advance() {
                ids.push((sols.binding(0).unwrap(), sols.binding(1).unwrap()));
            }
        }
        let mut got: Vec<(Vec<String>, Vec<String>)> = ids
            .iter()
            .map(|&(x, y)| (leaf_names(&e, x), leaf_names(&e, y)))
            .collect();
        got.sort();
        let mut want = vec![
            (vec!["a".into()], vec!["b".into(), "c".into()]),
            (vec!["b".into()], vec!["a".into(), "c".into()]),
            (vec!["c".into()], vec!["a".into(), "b".into()]),
            (vec!["a".into(), "b".into()], vec!["c".into()]),
            (vec!["a".into(), "c".into()], vec!["b".into()]),
            (vec!["b".into(), "c".into()], vec!["a".into()]),
        ];
        want.sort();
        assert_eq!(got, want, "six ACU matchers, as a set");

        // `xmatch a + b <=? a + b + c` — one extension match, matched portion `a + b`, empty subst.
        let ground = Term::op(plus, vec![Term::constant(a), Term::constant(b)]);
        let portion = {
            let mut sols = e.match_solutions(ground, 0, subject, true);
            assert!(sols.advance(), "one extension solution");
            let p = sols.matched_portion();
            // The display view reports a partial portion (not `(whole)`) for `a + b <=? a + b + c`.
            assert!(matches!(
                sols.matched_portion_display(),
                Some(MatchedPortion::Portion(_))
            ));
            assert!(!sols.advance(), "exactly one");
            p
        };
        assert_eq!(
            leaf_names(&e, portion),
            vec!["a".to_string(), "b".to_string()]
        );
    }

    /// Three constants threaded by rules `a => b => c => d`. `rewrite` drives them to the normal form
    /// `d` in 3 rule applications, while `reduce` (which consults only the equation table) leaves `a`
    /// untouched — the structural guarantee that equations do not perform rule rewriting.
    fn chain_engine() -> (Engine, SymbolId, SymbolId, SymbolId, SymbolId) {
        let mut e = Engine::new();
        let s = e.add_sort("S");
        e.close_sorts();
        let a = e.add_op("a", vec![], s);
        let b = e.add_op("b", vec![], s);
        let c = e.add_op("c", vec![], s);
        let d = e.add_op("d", vec![], s);
        e.add_rule(Term::constant(a), Term::constant(b), 0);
        e.add_rule(Term::constant(b), Term::constant(c), 0);
        e.add_rule(Term::constant(c), Term::constant(d), 0);
        (e, a, b, c, d)
    }

    #[test]
    fn rewrite_applies_rules_and_reduce_does_not() {
        let (mut e, a, _b, _c, _d) = chain_engine();

        // reduce never applies a rule: `a` is its own equational normal form.
        let a0 = e.make_const(a);
        let red = e.reduce(a0);
        assert_eq!(
            e.symbol(e.node(red).symbol()).name(),
            "a",
            "reduce must not apply rules"
        );

        // rewrite drives the rules to the normal form `d` in 3 steps.
        e.reset_rewrites();
        let a1 = e.make_const(a);
        let mut rw = e.rewrite(a1);
        let step = rw.run(&mut e, None);
        assert!(step.done, "reached a normal form");
        assert_eq!(e.symbol(e.node(step.term).symbol()).name(), "d");
        assert_eq!(e.rewrites(), 3, "three rule applications");
    }

    #[test]
    fn rewrite_bound_then_continue() {
        let (mut e, a, _b, _c, _d) = chain_engine();
        let a0 = e.make_const(a);
        let mut rw = e.rewrite(a0);

        e.reset_rewrites();
        let s1 = rw.run(&mut e, Some(1));
        assert!(!s1.done, "stopped at the bound, not a normal form");
        assert_eq!(e.symbol(e.node(s1.term).symbol()).name(), "b");
        assert_eq!(e.rewrites(), 1, "exactly one rule application under [1]");

        // `continue` (unbounded) runs to the normal form, the round-robin cursor having persisted.
        let s2 = rw.run(&mut e, None);
        assert!(s2.done);
        assert_eq!(e.symbol(e.node(s2.term).symbol()).name(), "d");
    }

    #[test]
    fn gc_keeps_reachable_shared_structure() {
        let (mut e, root, _nat) = fixture();
        assert_eq!(e.live_nodes(), 3);
        assert_eq!(e.gc([root]), 0);
        assert_eq!(e.live_nodes(), 3);
    }

    #[test]
    fn gc_collects_unreachable() {
        let (mut e, root, nat) = fixture();
        let h = e.add_op("h", vec![], nat);
        let _garbage = e.make_const(h);
        assert_eq!(e.live_nodes(), 4);
        assert_eq!(e.gc([root]), 1);
        assert_eq!(e.live_nodes(), 3);
    }

    #[test]
    fn gc_with_no_roots_collects_all() {
        let (mut e, _root, _nat) = fixture();
        assert_eq!(e.gc(Vec::new()), 3);
        assert_eq!(e.live_nodes(), 0);
    }

    #[test]
    fn computes_node_sorts_through_subsorts() {
        let mut e = Engine::new();
        let zero = e.add_sort("Zero");
        let nznat = e.add_sort("NzNat");
        let nat = e.add_sort("Nat");
        e.add_subsort(zero, nat);
        e.add_subsort(nznat, nat);
        e.close_sorts();
        let z = e.add_op("0", vec![], zero);
        let s = e.add_op("s", vec![nat], nznat);
        let plus = e.add_op("+", vec![nat, nat], nat);

        let n0 = e.make_const(z); // 0 : Zero
        let n1 = e.make_free(s, vec![n0]); // s(0): Zero <= Nat  =>  NzNat
        let sum = e.make_free(plus, vec![n0, n1]); // Zero,NzNat <= Nat  =>  Nat

        assert_eq!(e.sort_of(n0), zero);
        assert_eq!(e.sort_of(n1), nznat);
        assert_eq!(e.sort_of(sum), nat);
    }

    /// Resolve least sorts across every declaration of an overloaded operator.
    #[test]
    fn overloaded_operator_least_sort() {
        let mut e = Engine::new();
        let zero = e.add_sort("Zero");
        let nznat = e.add_sort("NzNat");
        let nat = e.add_sort("Nat");
        e.add_subsort(zero, nat);
        e.add_subsort(nznat, nat);
        e.close_sorts();
        let z = e.add_op("0", vec![], zero);
        let s = e.add_op("s", vec![nat], nznat);
        let plus = e.add_op("+", vec![nat, nat], nat); // decl 0: Nat Nat -> Nat
        e.add_op_decl(plus, vec![nznat, nznat], nznat); // decl 1: NzNat NzNat -> NzNat

        let n0 = e.make_const(z); // 0 : Zero
        let s0 = e.make_free(s, vec![n0]); // s 0 : NzNat
        assert_eq!(e.sort_of(n0), zero, "0 : Zero");
        assert_eq!(e.sort_of(s0), nznat, "s 0 : NzNat");
        // s0 / n0 are reused as shared children below (a genuine DAG share).
        let s0_plus_s0 = e.make_free(plus, vec![s0, s0]);
        assert_eq!(
            e.sort_of(s0_plus_s0),
            nznat,
            "s 0 + s 0 : NzNat (both args NzNat)"
        );
        let zero_plus_s0 = e.make_free(plus, vec![n0, s0]);
        assert_eq!(
            e.sort_of(zero_plus_s0),
            nat,
            "0 + s 0 : Nat (Zero is not <= NzNat)"
        );
        let zero_plus_zero = e.make_free(plus, vec![n0, n0]);
        assert_eq!(e.sort_of(zero_plus_zero), nat, "0 + 0 : Nat");
    }

    /// Overloading and equations make the result's least sort and rewrite count co-vary.
    #[test]
    fn overloaded_operator_reduce_and_resort() {
        let mut e = Engine::new();
        let zero = e.add_sort("Zero");
        let nznat = e.add_sort("NzNat");
        let nat = e.add_sort("Nat");
        e.add_subsort(zero, nat);
        e.add_subsort(nznat, nat);
        e.close_sorts();
        let z = e.add_op("0", vec![], zero);
        let s = e.add_op("s", vec![nat], nznat);
        let plus = e.add_op("+", vec![nat, nat], nat);
        e.add_op_decl(plus, vec![nznat, nznat], nznat);
        e.add_equation(Equation {
            lhs: Term::op(plus, vec![Term::var(0, nat), Term::constant(z)]),
            rhs: Term::var(0, nat),
            nr_vars: 1,
        });
        e.add_equation(Equation {
            lhs: Term::op(
                plus,
                vec![Term::var(0, nat), Term::op(s, vec![Term::var(1, nat)])],
            ),
            rhs: Term::op(
                s,
                vec![Term::op(plus, vec![Term::var(0, nat), Term::var(1, nat)])],
            ),
            nr_vars: 2,
        });

        let z0 = e.make_const(z);
        let s0a = e.make_free(s, vec![z0]);
        let s0b = e.make_free(s, vec![z0]);
        let sum = e.make_free(plus, vec![s0a, s0b]); // s 0 + s 0
        let r = e.reduce(sum);
        assert_eq!(e.rewrites(), 2, "s 0 + s 0 = s s 0 in 2 rewrites");
        assert_eq!(e.sort_of(r), nznat, "result s s 0 : NzNat");
        assert_eq!(e.node(r).symbol(), s, "result is an s_ application");

        e.reset_rewrites();
        let (z1, z2) = (e.make_const(z), e.make_const(z));
        let zz = e.make_free(plus, vec![z1, z2]); // 0 + 0
        assert_eq!(e.sort_of(zz), nat, "0 + 0 : Nat before reduction");
        let r2 = e.reduce(zz);
        assert_eq!(e.rewrites(), 1, "0 + 0 = 0 in 1 rewrite");
        assert_eq!(e.sort_of(r2), zero, "result 0 : Zero (re-sorted down)");
    }

    /// With no applicable declaration, an overloaded application has the kind's error sort and does not rewrite.
    #[test]
    fn overloaded_operator_no_applicable_decl_is_error_sort() {
        let mut e = Engine::new();
        let zero = e.add_sort("Zero");
        let nznat = e.add_sort("NzNat");
        let nat = e.add_sort("Nat");
        e.add_subsort(zero, nat);
        e.add_subsort(nznat, nat);
        e.close_sorts();
        let z = e.add_op("0", vec![], zero);
        let s = e.add_op("s", vec![nat], nznat);
        let plus = e.add_op("+", vec![nznat, nznat], nznat); // ONLY NzNat NzNat -> NzNat

        let (z1, z2) = (e.make_const(z), e.make_const(z));
        let zz = e.make_free(plus, vec![z1, z2]); // 0 + 0 : no decl applies
        assert!(
            e.sorts().sort(e.sort_of(zz)).is_error,
            "0 + 0 lands in the error sort"
        );

        let z0 = e.make_const(z);
        let s0a = e.make_free(s, vec![z0]);
        let s0b = e.make_free(s, vec![z0]);
        let ss = e.make_free(plus, vec![s0a, s0b]); // s 0 + s 0 : NzNat
        assert_eq!(
            e.sort_of(ss),
            nznat,
            "s 0 + s 0 : NzNat (the one declaration applies)"
        );
    }

    /// Reflected rule sides are allowed to be well formed only at the kind level while an inner special
    /// operation is waiting to reduce. The fallback must select the `Configuration` overload of `__`,
    /// never an unrelated same-name `AttrSet` overload.
    #[test]
    fn kind_profile_resolution_disambiguates_error_sort_arguments() {
        let mut e = Engine::new();
        let attr = e.add_sort("Attr");
        let attr_set = e.add_sort("AttrSet");
        let object = e.add_sort("Object");
        let message = e.add_sort("Msg");
        let configuration = e.add_sort("Configuration");
        e.add_subsort(attr, attr_set);
        e.add_subsort(object, configuration);
        e.add_subsort(message, configuration);
        e.close_sorts();

        let attr_join = e.add_op("__", vec![attr_set, attr_set], attr_set);
        let config_join = e.add_op("__", vec![configuration, configuration], configuration);
        let config_error = e.sorts().error_sort(e.sorts().kind_of(configuration));
        let arguments = [object, config_error];

        assert_eq!(e.resolve_operator_for_sorts("__", &arguments), None);
        assert_eq!(
            e.resolve_operator_for_kinds("__", &arguments),
            Some(config_join)
        );
        assert_ne!(config_join, attr_join);
    }

    /// A non-preregular operator with incomparable result sorts resolves to its earliest declaration.
    /// Diagnostic emission is outside this kernel API.
    #[test]
    fn non_preregular_overload_breaks_toward_earliest_declaration() {
        let mut e = Engine::new();
        let a = e.add_sort("A");
        let b = e.add_sort("B");
        let top = e.add_sort("Top");
        e.add_subsort(a, top);
        e.add_subsort(b, top);
        e.close_sorts();
        let c = e.add_op("c", vec![], a);
        let f = e.add_op("f", vec![a], a); // decl 0: A -> A
        e.add_op_decl(f, vec![a], b); // decl 1: A -> B (incomparable range)

        let c0 = e.make_const(c);
        let fc = e.make_free(f, vec![c0]);
        assert_eq!(
            e.sort_of(fc),
            a,
            "f(c) : A — the earliest of the two incomparable declarations"
        );
    }

    /// An asymmetric commutative overload must have an argument-order-independent least sort. Sort
    /// completion adds the swapped declaration so canonical argument order cannot select a broader range.
    #[test]
    fn acu_asymmetric_overload_least_sort_is_commutative() {
        let mut e = Engine::new();
        let zero = e.add_sort("Zero");
        let nznat = e.add_sort("NzNat");
        let nat = e.add_sort("Nat");
        e.add_subsort(zero, nat);
        e.add_subsort(nznat, nat);
        e.close_sorts();
        let z = e.add_op("z", vec![], zero);
        let nz = e.add_op("nz", vec![], nznat);
        let plus = e.add_op_ac("+", vec![nznat, nat], nznat, None); // decl0: NzNat Nat -> NzNat
        e.add_op_decl(plus, vec![nat, nat], nat); // decl1: Nat Nat -> Nat

        let sum = |e: &mut Engine, a: SymbolId, b: SymbolId| {
            let (x, y) = (e.make_const(a), e.make_const(b));
            let s = e.make_ac(plus, vec![x, y]);
            e.sorts().name(e.sort_of(s)).to_string()
        };
        assert_eq!(
            sum(&mut e, z, nz),
            "NzNat",
            "z + nz : NzNat (order-independent)"
        );
        assert_eq!(sum(&mut e, nz, z), "NzNat", "nz + z : NzNat");
        assert_eq!(sum(&mut e, z, z), "Nat", "z + z : Nat");
        assert_eq!(sum(&mut e, nz, nz), "NzNat", "nz + nz : NzNat");
        // Ternary: the left-to-right multiset fold stays order-independent.
        let tern = {
            let (x, y, w) = (e.make_const(z), e.make_const(nz), e.make_const(z));
            e.make_ac(plus, vec![x, y, w])
        };
        assert_eq!(
            e.sorts().name(e.sort_of(tern)),
            "NzNat",
            "z + z + nz : NzNat"
        );
    }

    /// The same overload-order independence applies to commutative non-associative operators.
    #[test]
    fn cui_asymmetric_overload_least_sort_is_commutative() {
        let mut e = Engine::new();
        let zero = e.add_sort("Zero");
        let nznat = e.add_sort("NzNat");
        let nat = e.add_sort("Nat");
        e.add_subsort(zero, nat);
        e.add_subsort(nznat, nat);
        e.close_sorts();
        let z = e.add_op("z", vec![], zero);
        let nz = e.add_op("nz", vec![], nznat);
        let g = e.add_op_cui("g", vec![nznat, nat], nznat, true, false, None); // NzNat Nat -> NzNat
        e.add_op_decl(g, vec![nat, nat], nat); // Nat Nat -> Nat

        let gg = |e: &mut Engine, a: SymbolId, b: SymbolId| {
            let (x, y) = (e.make_const(a), e.make_const(b));
            let s = e.make_cui(g, x, y);
            e.sorts().name(e.sort_of(s)).to_string()
        };
        assert_eq!(
            gg(&mut e, z, nz),
            "NzNat",
            "g(z, nz) : NzNat (order-independent)"
        );
        assert_eq!(gg(&mut e, nz, z), "NzNat", "g(nz, z) : NzNat");
        assert_eq!(gg(&mut e, z, z), "Nat", "g(z, z) : Nat");
    }

    /// A non-linear membership lowers a pair's least sort and counts as a rewrite. The refined sort then
    /// determines which equations apply.
    #[test]
    fn membership_lowers_sort_and_counts_as_rewrite() {
        let mut e = Engine::new();
        let nat = e.add_sort("Nat");
        let pair = e.add_sort("Pair");
        let sympair = e.add_sort("SymPair");
        e.add_subsort(sympair, pair);
        e.close_sorts();
        let z = e.add_op("z", vec![], nat);
        let s = e.add_op("s", vec![nat], nat);
        let pairop = e.add_op("<_,_>", vec![nat, nat], pair);
        let f = e.add_op("f", vec![pair], nat);
        e.add_membership(Membership {
            lhs: Term::op(pairop, vec![Term::var(0, nat), Term::var(0, nat)]), // < N, N > (non-linear)
            sort: sympair,
            nr_vars: 1,
        });
        e.add_equation(Equation {
            lhs: Term::op(f, vec![Term::var(0, sympair)]), // f(P), P : SymPair
            rhs: Term::constant(z),
            nr_vars: 1,
        });

        // < z, z > : SymPair — one membership application. Construction gives the *base* sort
        // (Pair); the membership refines it to SymPair lazily, at the reduce normal-form point.
        e.reset_rewrites();
        let (z0, z1) = (e.make_const(z), e.make_const(z));
        let zz = e.make_free(pairop, vec![z0, z1]);
        assert_eq!(
            e.sort_of(zz),
            pair,
            "base sort Pair at construction (membership applies lazily)"
        );
        let r = e.reduce(zz);
        assert_eq!(e.rewrites(), 1, "one membership application");
        assert_eq!(e.sort_of(r), sympair, "< z, z > : SymPair after reduce");

        // < z, s z > : Pair — components differ, no membership applies.
        e.reset_rewrites();
        let zc = e.make_const(z);
        let sz = {
            let z2 = e.make_const(z);
            e.make_free(s, vec![z2])
        };
        let zsz = e.make_free(pairop, vec![zc, sz]);
        assert_eq!(e.sort_of(zsz), pair, "< z, s z > : Pair");
        let _ = e.reduce(zsz);
        assert_eq!(e.rewrites(), 0, "no membership applies");

        // f(< z, z >) : Nat — membership (1) + equation (1) = 2 rewrites.
        e.reset_rewrites();
        let (z3, z4) = (e.make_const(z), e.make_const(z));
        let zz2 = e.make_free(pairop, vec![z3, z4]); // membership fires here
        let fzz = e.make_free(f, vec![zz2]);
        let r2 = e.reduce(fzz); // equation fires here
        assert_eq!(e.rewrites(), 2, "membership + equation");
        assert_eq!(e.node(r2).symbol(), z, "f(< z, z >) = z");

        // f(< z, s z >) : Nat — arg is only Pair, so f(P : SymPair) does not match.
        e.reset_rewrites();
        let zc2 = e.make_const(z);
        let sz2 = {
            let z5 = e.make_const(z);
            e.make_free(s, vec![z5])
        };
        let zsz2 = e.make_free(pairop, vec![zc2, sz2]);
        let fzsz = e.make_free(f, vec![zsz2]);
        let r3 = e.reduce(fzsz);
        assert_eq!(e.rewrites(), 0, "no membership, no equation");
        assert_eq!(
            e.node(r3).symbol(),
            f,
            "f(< z, s z >) is its own normal form"
        );
    }

    /// An AC membership fires through extension on a sub-multiset, not only on the whole node. Refining a
    /// transient prefix affects the rewrite count but can disappear when the parent is flattened again.
    #[test]
    fn ac_membership_fires_through_extension() {
        let mut e = Engine::new();
        let et = e.add_sort("E");
        let special = e.add_sort("Special");
        e.add_subsort(special, et);
        e.close_sorts();
        let a = e.add_op("a", vec![], et);
        let bar = e.add_op_ac("|", vec![et, et], et, None);
        e.add_membership(Membership {
            lhs: Term::op(bar, vec![Term::constant(a), Term::constant(a)]), // a | a
            sort: special,
            nr_vars: 0,
        });

        // red a | a — one application, whole match; result lowers to Special.
        e.reset_rewrites();
        let (a0, a1) = (e.make_const(a), e.make_const(a));
        let aa = e.make_ac(bar, vec![a0, a1]);
        let r = e.reduce(aa);
        assert_eq!(e.rewrites(), 1, "a | a: one membership application (whole)");
        assert_eq!(e.sort_of(r), special, "a | a : Special");

        // red a | a | a — one application, through extension: the subject is built right-nested
        // `a | (a | a)` as the parser builds it (the lazy splice keeps the unreduced inner node
        // nested), so the inner `a | a` reaches its own normal-form point and fires the mb there.
        e.reset_rewrites();
        let (b0, b1, b2) = (e.make_const(a), e.make_const(a), e.make_const(a));
        let inner = e.make_ac(bar, vec![b1, b2]);
        let aaa = e.make_ac(bar, vec![b0, inner]);
        let r3 = e.reduce(aaa);
        assert_eq!(
            e.rewrites(),
            1,
            "a | a | a: one membership application (extension), not 0"
        );
        assert_eq!(
            e.sort_of(r3),
            et,
            "a | a | a : E (whole match fails; prefix refinement discarded)"
        );
    }

    /// Conditional AC memberships also fire through extension; condition reductions remain included in
    /// the rewrite count.
    #[test]
    fn ac_conditional_membership_fires_through_extension() {
        let mut e = Engine::new();
        let et = e.add_sort("E");
        let special = e.add_sort("Special");
        e.add_subsort(special, et);
        e.close_sorts();
        let a = e.add_op("a", vec![], et);
        let h = e.add_op("h", vec![et], et);
        let bar = e.add_op_ac("|", vec![et, et], et, None);
        e.add_equation(Equation {
            lhs: Term::op(h, vec![Term::constant(a)]), // h(a) = a
            rhs: Term::constant(a),
            nr_vars: 0,
        });
        e.add_conditional_membership(
            Term::op(bar, vec![Term::constant(a), Term::constant(a)]), // a | a
            special,
            0,
            vec![ConditionFragment::Equality {
                lhs: Term::constant(a),
                rhs: Term::constant(a),
            }],
        );

        // red a | a | h(h(a)) — 2 (h reductions) + 1 (cmb on the inner node) = 3. Right-nested
        // `a | (a | h(h(a)))`, the parse shape: the inner node reduces to `a | a` and its
        // normal-form point fires the cmb before the parent splices it flat.
        e.reset_rewrites();
        let (a0, a1) = (e.make_const(a), e.make_const(a));
        let hha = {
            let ac = e.make_const(a);
            let ha = e.make_free(h, vec![ac]);
            e.make_free(h, vec![ha])
        };
        let inner = e.make_ac(bar, vec![a1, hha]);
        let subject = e.make_ac(bar, vec![a0, inner]);
        let r = e.reduce(subject);
        assert_eq!(e.rewrites(), 3, "2 h-reductions + 1 cmb-through-extension");
        assert_eq!(e.sort_of(r), et, "a | a | a : E");
        let three = {
            let (c0, c1, c2) = (e.make_const(a), e.make_const(a), e.make_const(a));
            e.make_ac(bar, vec![c0, c1, c2])
        };
        assert!(e.deep_equal(r, three), "result is a | a | a");
    }

    /// Extension folding builds transient prefix nodes and evaluates membership conditions off the main
    /// reduction stack. Forced collection verifies that the subject and its children stay rooted.
    #[test]
    fn ac_conditional_membership_extension_survives_gc() {
        let mut e = Engine::new();
        let et = e.add_sort("E");
        let special = e.add_sort("Special");
        e.add_subsort(special, et);
        e.close_sorts();
        let a = e.add_op("a", vec![], et);
        let h = e.add_op("h", vec![et], et);
        let bar = e.add_op_ac("|", vec![et, et], et, None);
        e.add_equation(Equation {
            lhs: Term::op(h, vec![Term::constant(a)]),
            rhs: Term::constant(a),
            nr_vars: 0,
        });
        e.add_conditional_membership(
            Term::op(bar, vec![Term::constant(a), Term::constant(a)]),
            special,
            0,
            vec![ConditionFragment::Equality {
                lhs: Term::constant(a),
                rhs: Term::constant(a),
            }],
        );
        e.set_gc_interval(Some(1)); // collect at every allocation — stress nested-reduction rooting
        e.reset_rewrites();
        let (a0, a1, a2, a3) = (
            e.make_const(a),
            e.make_const(a),
            e.make_const(a),
            e.make_const(a),
        );
        // a | (a | (a | (a | h(h(a))))) — the right-nested parse shape; the innermost node's cmb
        // condition re-enters reduce under per-allocation GC.
        let hha = {
            let ac = e.make_const(a);
            let ha = e.make_free(h, vec![ac]);
            e.make_free(h, vec![ha])
        };
        let l1 = e.make_ac(bar, vec![a3, hha]);
        let l2 = e.make_ac(bar, vec![a2, l1]);
        let l3 = e.make_ac(bar, vec![a1, l2]);
        let subject = e.make_ac(bar, vec![a0, l3]);
        let r = e.reduce(subject); // must not crash / read freed nodes
        assert_eq!(
            e.rewrites(),
            3,
            "2 h-reductions + 1 cmb (prefix a | a) under aggressive GC"
        );
        let five = {
            let cs: Vec<DagId> = (0..5).map(|_| e.make_const(a)).collect();
            e.make_ac(bar, cs)
        };
        assert!(e.deep_equal(r, five), "result is a | a | a | a | a");
    }

    /// Chained memberships lower sorts in smallest-target-first order.
    #[test]
    fn membership_chain_lowers_two_levels() {
        let mut e = Engine::new();
        let sa = e.add_sort("A");
        let sb = e.add_sort("B");
        let sc = e.add_sort("C");
        e.add_subsort(sc, sb);
        e.add_subsort(sb, sa);
        e.close_sorts();
        let a = e.add_op("a", vec![], sa);
        let g = e.add_op("g", vec![sa], sa);
        e.add_membership(Membership {
            lhs: Term::op(g, vec![Term::var(0, sa)]),
            sort: sb,
            nr_vars: 1,
        }); // g(X) : B
        e.add_membership(Membership {
            lhs: Term::op(g, vec![Term::op(g, vec![Term::var(0, sa)])]), // g(g(X)) : C
            sort: sc,
            nr_vars: 1,
        });

        e.reset_rewrites();
        let a0 = e.make_const(a);
        assert_eq!(e.sort_of(a0), sa, "a : A");
        let _ = e.reduce(a0);
        assert_eq!(e.rewrites(), 0);

        // Construction gives the base sort (A); the memberships refine it lazily at reduce.
        e.reset_rewrites();
        let a1 = e.make_const(a);
        let ga = e.make_free(g, vec![a1]);
        assert_eq!(e.sort_of(ga), sa, "g(a) base sort A at construction");
        let rga = e.reduce(ga);
        assert_eq!(e.rewrites(), 1, "one membership application g(X):B");
        assert_eq!(e.sort_of(rga), sb, "g(a) : B after reduce");

        e.reset_rewrites();
        let a2 = e.make_const(a);
        let ga2 = e.make_free(g, vec![a2]);
        let gga = e.make_free(g, vec![ga2]);
        assert_eq!(e.sort_of(gga), sa, "g(g(a)) base sort A at construction");
        let rgga = e.reduce(gga);
        assert_eq!(
            e.rewrites(),
            2,
            "inner g(a):B then outer g(g(a)):C — smallest-first, 2 not 3"
        );
        assert_eq!(e.sort_of(rgga), sc, "g(g(a)) : C after reduce");
    }

    /// Tracing (opt-in) records a [`TraceEvent::Rewrite`] per rewrite — kind, the equation `id`, its
    /// `depth` (0 at top level), the redex/result, and the matched substitution. `add(s(0), s(0))`
    /// reduces in two equation steps; `take_trace` drains them and leaves the buffer empty (tracing
    /// stays on).
    #[test]
    fn trace_records_rewrite_steps() {
        let mut e = Engine::new();
        let nat = e.add_sort("Nat");
        e.close_sorts();
        let z = e.add_op("0", vec![], nat);
        let s = e.add_op("s", vec![nat], nat);
        let add = e.add_op("add", vec![nat, nat], nat);
        let v = |i| Term::var(i, nat);
        let s_of = |t| Term::op(s, vec![t]);
        // eq add(0, Y) = Y .   eq add(s(X), Y) = s(add(X, Y)) .   (ids 0 and 1)
        let id_add0 = e.add_equation(Equation {
            lhs: Term::op(add, vec![Term::constant(z), v(0)]),
            rhs: v(0),
            nr_vars: 1,
        });
        let id_adds = e.add_equation(Equation {
            lhs: Term::op(add, vec![s_of(v(0)), v(1)]),
            rhs: s_of(Term::op(add, vec![v(0), v(1)])),
            nr_vars: 2,
        });
        assert_eq!((id_add0, id_adds), (0, 1), "dense per-module equation ids");

        let z0 = e.make_const(z);
        let one = e.make_free(s, vec![z0]);
        let subject = e.make_free(add, vec![one, one]); // add(s(0), s(0))

        assert!(!e.is_tracing());
        e.set_trace(true);
        let result = e.reduce(subject);
        let steps = e.take_trace();

        assert_eq!(steps.len(), 2, "two equation rewrites");
        // Step 0: add(s(X),Y) fires on the whole subject, binding X and Y (2 vars).
        match &steps[0] {
            TraceEvent::Rewrite {
                kind,
                eq_id,
                depth,
                redex,
                bindings,
                whole_before,
                ..
            } => {
                assert_eq!(*kind, RewriteKind::Equation);
                assert_eq!(*eq_id, Some(id_adds));
                assert_eq!(*depth, 0);
                assert_eq!(*redex, subject, "first redex is the whole subject");
                assert_eq!(bindings.len(), 2, "X, Y bound");
                assert!(bindings.iter().all(Option::is_some));
                assert!(whole_before.is_none(), "whole off by default");
            }
            ev => panic!("expected Rewrite, got {ev:?}"),
        }
        // Step 1: add(0,Y) fires on the inner redex, binding Y (1 var).
        match &steps[1] {
            TraceEvent::Rewrite {
                kind,
                eq_id,
                bindings,
                ..
            } => {
                assert_eq!(*kind, RewriteKind::Equation);
                assert_eq!(*eq_id, Some(id_add0));
                assert_eq!(bindings.len(), 1, "Y bound");
            }
            ev => panic!("expected Rewrite, got {ev:?}"),
        }
        let z1 = e.make_const(z);
        let s1 = e.make_free(s, vec![z1]);
        let two = e.make_free(s, vec![s1]);
        assert!(e.deep_equal(result, two), "add(s(0), s(0)) = s(s(0))");
        // take_trace drained the buffer; tracing is still on.
        assert!(e.take_trace().is_empty());
        assert!(e.is_tracing());
    }

    /// Whole-term tracing (`set trace whole`): each `Rewrite` event carries the reconstructed whole root
    /// term before/after. The second (inner) rewrite's whole is the *full* term `s(add(0, s 0))` → `s s
    /// 0`, not just the inner redex `add(0, s 0)` → `s 0`.
    #[test]
    fn trace_records_whole_terms() {
        let mut e = Engine::new();
        let nat = e.add_sort("Nat");
        e.close_sorts();
        let z = e.add_op("0", vec![], nat);
        let s = e.add_op("s", vec![nat], nat);
        let add = e.add_op("add", vec![nat, nat], nat);
        let v = |i| Term::var(i, nat);
        let s_of = |t| Term::op(s, vec![t]);
        e.add_equation(Equation {
            lhs: Term::op(add, vec![Term::constant(z), v(0)]),
            rhs: v(0),
            nr_vars: 1,
        });
        e.add_equation(Equation {
            lhs: Term::op(add, vec![s_of(v(0)), v(1)]),
            rhs: s_of(Term::op(add, vec![v(0), v(1)])),
            nr_vars: 2,
        });
        let z0 = e.make_const(z);
        let one = e.make_free(s, vec![z0]);
        let subject = e.make_free(add, vec![one, one]); // add(s(0), s(0))

        e.set_trace(true);
        e.set_record_whole(true);
        let result = e.reduce(subject);
        let steps = e.take_trace();
        assert_eq!(steps.len(), 2);

        // Build the expected whole terms to compare structurally.
        let mk = |e: &mut Engine, n: u32| {
            let mut t = e.make_const(z);
            for _ in 0..n {
                t = e.make_free(s, vec![t]);
            }
            t
        };
        let two = mk(&mut e, 2); // s s 0
        let one_again = mk(&mut e, 1); // s 0
        // Step 1 is the inner rewrite add(0, s 0) -> s 0; its WHOLE after is s s 0 (not s 0).
        match &steps[1] {
            TraceEvent::Rewrite {
                redex,
                result: res,
                whole_before,
                whole_after,
                ..
            } => {
                assert!(e.deep_equal(*res, one_again), "inner result is s 0");
                assert!(
                    e.deep_equal(whole_after.unwrap(), two),
                    "whole after is s s 0"
                );
                // whole_before is s (add(0, s 0)) — strictly larger than the redex add(0, s 0).
                assert!(
                    !e.deep_equal(whole_before.unwrap(), *redex),
                    "whole_before is the full term"
                );
            }
            ev => panic!("expected Rewrite, got {ev:?}"),
        }
        assert!(e.deep_equal(result, two));
    }

    /// In `ceq max(M,N)=M if M<=N=ff`, condition reduction contributes to the count. Failure of the
    /// first equation retries the condition for the second, so `max(2,1)` takes five rewrites.
    #[test]
    fn conditional_equation_with_equality_condition() {
        let mut e = Engine::new();
        let nat = e.add_sort("Nat");
        let truth = e.add_sort("Truth");
        e.close_sorts();
        let z = e.add_op("z", vec![], nat);
        let s = e.add_op("s", vec![nat], nat);
        let tt = e.add_op("tt", vec![], truth);
        let ff = e.add_op("ff", vec![], truth);
        let le = e.add_op("<=", vec![nat, nat], truth);
        let max = e.add_op("max", vec![nat, nat], nat);
        let v = |i| Term::var(i, nat);
        let s_of = |t| Term::op(s, vec![t]);
        // eq z <= N = tt . eq s M <= z = ff . eq s M <= s N = M <= N .
        e.add_equation(Equation {
            lhs: Term::op(le, vec![Term::constant(z), v(0)]),
            rhs: Term::constant(tt),
            nr_vars: 1,
        });
        e.add_equation(Equation {
            lhs: Term::op(le, vec![s_of(v(0)), Term::constant(z)]),
            rhs: Term::constant(ff),
            nr_vars: 1,
        });
        e.add_equation(Equation {
            lhs: Term::op(le, vec![s_of(v(0)), s_of(v(1))]),
            rhs: Term::op(le, vec![v(0), v(1)]),
            nr_vars: 2,
        });
        // ceq max(M, N) = N if M <= N = tt .   /   ceq max(M, N) = M if M <= N = ff .
        let le_mn = || Term::op(le, vec![v(0), v(1)]);
        e.add_conditional_equation(
            Term::op(max, vec![v(0), v(1)]),
            v(1),
            2,
            vec![ConditionFragment::Equality {
                lhs: le_mn(),
                rhs: Term::constant(tt),
            }],
        );
        e.add_conditional_equation(
            Term::op(max, vec![v(0), v(1)]),
            v(0),
            2,
            vec![ConditionFragment::Equality {
                lhs: le_mn(),
                rhs: Term::constant(ff),
            }],
        );

        // max(1, 2) = 2 in 3 rewrites: condition `1<=2` reduces to tt (2), then max→N (1).
        e.reset_rewrites();
        let (n1, n2) = (numeral(&mut e, z, s, 1), numeral(&mut e, z, s, 2));
        let m = e.make_free(max, vec![n1, n2]);
        let r = e.reduce(m);
        assert_eq!(e.rewrites(), 3, "max(1,2): condition reduce (2) + max (1)");
        assert_eq!(decode(&e, r, z, s), 2, "max(1,2) = 2");

        // max(2, 1) = 2 in 5 rewrites: first condition `2<=1`→ff fails tt (2), backtrack, second
        // condition re-reduces `2<=1`→ff (2), matches ff, then max→M (1).
        e.reset_rewrites();
        let (n2b, n1b) = (numeral(&mut e, z, s, 2), numeral(&mut e, z, s, 1));
        let m2 = e.make_free(max, vec![n2b, n1b]);
        let r2 = e.reduce(m2);
        assert_eq!(
            e.rewrites(),
            5,
            "max(2,1): cond fails (2) + cond re-reduced (2) + max (1)"
        );
        assert_eq!(
            decode(&e, r2, z, s),
            2,
            "max(2,1) = 2 (backtracked to the second equation)"
        );

        // max(0, 0) = 0 in 2 rewrites.
        e.reset_rewrites();
        let (z1, z2) = (numeral(&mut e, z, s, 0), numeral(&mut e, z, s, 0));
        let m3 = e.make_free(max, vec![z1, z2]);
        let r3 = e.reduce(m3);
        assert_eq!(e.rewrites(), 2, "max(0,0): condition reduce (1) + max (1)");
        assert_eq!(decode(&e, r3, z, s), 0, "max(0,0) = 0");
    }

    /// A conditional equation with a sort-test condition fires only for a compatible least sort.
    /// `ceq nz?(N) = s z if N : NzNat` fires only when the argument's least sort is `<= NzNat`.
    #[test]
    fn conditional_equation_with_sort_test_condition() {
        let mut e = Engine::new();
        let nat = e.add_sort("Nat");
        let nznat = e.add_sort("NzNat");
        e.add_subsort(nznat, nat);
        e.close_sorts();
        let z = e.add_op("z", vec![], nat);
        let s = e.add_op("s", vec![nat], nznat); // s_ : Nat -> NzNat
        let nzq = e.add_op("nz?", vec![nat], nat);
        e.add_conditional_equation(
            Term::op(nzq, vec![Term::var(0, nat)]),
            Term::op(s, vec![Term::constant(z)]), // = s z
            1,
            vec![ConditionFragment::SortTest {
                term: Term::var(0, nat),
                sort: nznat,
            }],
        );

        // nz?(s z) : the argument is NzNat → condition holds → s z, 1 rewrite.
        e.reset_rewrites();
        let s0 = {
            let z0 = e.make_const(z);
            e.make_free(s, vec![z0])
        };
        let q1 = e.make_free(nzq, vec![s0]);
        let r1 = e.reduce(q1);
        assert_eq!(e.rewrites(), 1, "condition N : NzNat holds for s z");
        assert_eq!(e.sort_of(r1), nznat, "result s z : NzNat");
        assert_eq!(e.node(r1).symbol(), s);

        // nz?(z) : z is only Nat → condition fails → no rewrite.
        e.reset_rewrites();
        let z1 = e.make_const(z);
        let q2 = e.make_free(nzq, vec![z1]);
        let r2 = e.reduce(q2);
        assert_eq!(e.rewrites(), 0, "condition N : NzNat fails for z");
        assert_eq!(e.node(r2).symbol(), nzq, "nz?(z) is its own normal form");
    }

    /// Re-entrant condition reduction remains correct under safe-point collection: the outer frame,
    /// bindings, redex, and equality result stay rooted.
    #[test]
    fn conditional_reduce_is_stable_under_safe_point_gc() {
        fn run(interval: Option<u64>) -> (SymbolId, u64) {
            let mut e = Engine::new();
            let nat = e.add_sort("Nat");
            let truth = e.add_sort("Truth");
            e.close_sorts();
            let z = e.add_op("z", vec![], nat);
            let s = e.add_op("s", vec![nat], nat);
            let tt = e.add_op("tt", vec![], truth);
            let g = e.add_op("g", vec![nat], truth);
            let f = e.add_op("f", vec![nat], nat);
            e.add_equation(Equation {
                lhs: Term::op(g, vec![Term::op(s, vec![Term::var(0, nat)])]), // g(s N) = g(N)
                rhs: Term::op(g, vec![Term::var(0, nat)]),
                nr_vars: 1,
            });
            e.add_equation(Equation {
                lhs: Term::op(g, vec![Term::constant(z)]), // g(z) = tt
                rhs: Term::constant(tt),
                nr_vars: 0,
            });
            e.add_conditional_equation(
                Term::op(f, vec![Term::var(0, nat)]), // ceq f(N) = z if g(N) = tt
                Term::constant(z),
                1,
                vec![ConditionFragment::Equality {
                    lhs: Term::op(g, vec![Term::var(0, nat)]),
                    rhs: Term::constant(tt),
                }],
            );
            e.set_gc_interval(interval);
            let n = numeral(&mut e, z, s, 20); // condition g(20) reduces in 21 rewrites
            let q = e.make_free(f, vec![n]);
            let r = e.reduce(q);
            (e.node(r).symbol(), e.rewrites())
        }
        let off = run(None);
        let on = run(Some(4)); // aggressive collection during the condition reduce
        assert_eq!(
            off.1, 22,
            "f(20) → z in 22 rewrites (21 condition + 1 equation)"
        );
        assert_eq!(
            on, off,
            "conditional reduce is identical with safe-point GC enabled"
        );
    }

    /// An `[owise]` equation fires only when no ordinary equation for the symbol applies.
    #[test]
    fn owise_equation_applies_when_no_normal_equation_matches() {
        let mut e = Engine::new();
        let nat = e.add_sort("Nat");
        let truth = e.add_sort("Truth");
        e.close_sorts();
        let z = e.add_op("z", vec![], nat);
        let s = e.add_op("s", vec![nat], nat);
        let tt = e.add_op("tt", vec![], truth);
        let ff = e.add_op("ff", vec![], truth);
        let iszero = e.add_op("iszero", vec![nat], truth);
        // eq iszero(z) = tt .   eq iszero(N) = ff [owise] .
        e.add_equation(Equation {
            lhs: Term::op(iszero, vec![Term::constant(z)]),
            rhs: Term::constant(tt),
            nr_vars: 0,
        });
        e.add_owise_equation(
            Term::op(iszero, vec![Term::var(0, nat)]),
            Term::constant(ff),
            1,
            Vec::new(),
        );

        // iszero(z): the specific non-owise equation matches.
        e.reset_rewrites();
        let z0 = e.make_const(z);
        let q0 = e.make_free(iszero, vec![z0]);
        let r0 = e.reduce(q0);
        assert_eq!(e.rewrites(), 1);
        assert_eq!(e.node(r0).symbol(), tt, "iszero(z) = tt");

        // iszero(s z): nothing else matches → owise applies.
        e.reset_rewrites();
        let s0 = {
            let z1 = e.make_const(z);
            e.make_free(s, vec![z1])
        };
        let q1 = e.make_free(iszero, vec![s0]);
        let r1 = e.reduce(q1);
        assert_eq!(e.rewrites(), 1);
        assert_eq!(e.node(r1).symbol(), ff, "iszero(s z) = ff via owise");
    }

    /// `[owise]` still applies when an ordinary conditional equation matches structurally but its
    /// condition fails.
    #[test]
    fn owise_applies_when_conditional_equation_condition_fails() {
        let mut e = Engine::new();
        let nat = e.add_sort("Nat");
        let truth = e.add_sort("Truth");
        e.close_sorts();
        let z = e.add_op("z", vec![], nat);
        let s = e.add_op("s", vec![nat], nat);
        let tt = e.add_op("tt", vec![], truth);
        let ff = e.add_op("ff", vec![], truth);
        let le = e.add_op("<=", vec![nat, nat], truth);
        let clamp = e.add_op("clamp", vec![nat], nat);
        let v = |i| Term::var(i, nat);
        let s_of = |t| Term::op(s, vec![t]);
        e.add_equation(Equation {
            lhs: Term::op(le, vec![Term::constant(z), v(0)]),
            rhs: Term::constant(tt),
            nr_vars: 1,
        });
        e.add_equation(Equation {
            lhs: Term::op(le, vec![s_of(v(0)), Term::constant(z)]),
            rhs: Term::constant(ff),
            nr_vars: 1,
        });
        e.add_equation(Equation {
            lhs: Term::op(le, vec![s_of(v(0)), s_of(v(1))]),
            rhs: Term::op(le, vec![v(0), v(1)]),
            nr_vars: 2,
        });
        // ceq clamp(N) = z if N <= s z = tt .   eq clamp(N) = s z [owise] .
        e.add_conditional_equation(
            Term::op(clamp, vec![v(0)]),
            Term::constant(z),
            1,
            vec![ConditionFragment::Equality {
                lhs: Term::op(le, vec![v(0), s_of(Term::constant(z))]),
                rhs: Term::constant(tt),
            }],
        );
        e.add_owise_equation(
            Term::op(clamp, vec![v(0)]),
            s_of(Term::constant(z)),
            1,
            Vec::new(),
        );

        for (input, expected, rewrites) in [(0u32, 0u32, 2u64), (1, 0, 3), (2, 1, 3)] {
            e.reset_rewrites();
            let n = numeral(&mut e, z, s, input);
            let c = e.make_free(clamp, vec![n]);
            let r = e.reduce(c);
            assert_eq!(e.rewrites(), rewrites, "clamp({input}) rewrite count");
            assert_eq!(decode(&e, r, z, s), expected, "clamp({input}) value");
        }
    }

    /// A conditional membership lowers a pair's sort only when its condition holds; condition reductions
    /// contribute to the rewrite count.
    #[test]
    fn conditional_membership_lowers_sort_when_condition_holds() {
        let mut e = Engine::new();
        let nat = e.add_sort("Nat");
        let pair = e.add_sort("Pair");
        let goodpair = e.add_sort("GoodPair");
        let truth = e.add_sort("Truth");
        e.add_subsort(goodpair, pair);
        e.close_sorts();
        let z = e.add_op("z", vec![], nat);
        let s = e.add_op("s", vec![nat], nat);
        let tt = e.add_op("tt", vec![], truth);
        let _ff = e.add_op("ff", vec![], truth);
        let le = e.add_op("<=", vec![nat, nat], truth);
        let pairop = e.add_op("<_,_>", vec![nat, nat], pair);
        let v = |i| Term::var(i, nat);
        let s_of = |t| Term::op(s, vec![t]);
        e.add_equation(Equation {
            lhs: Term::op(le, vec![Term::constant(z), v(0)]),
            rhs: Term::constant(tt),
            nr_vars: 1,
        });
        e.add_equation(Equation {
            lhs: Term::op(le, vec![s_of(v(0)), Term::constant(z)]),
            rhs: Term::constant(_ff),
            nr_vars: 1,
        });
        e.add_equation(Equation {
            lhs: Term::op(le, vec![s_of(v(0)), s_of(v(1))]),
            rhs: Term::op(le, vec![v(0), v(1)]),
            nr_vars: 2,
        });
        // cmb < M, N > : GoodPair if M <= N = tt .
        e.add_conditional_membership(
            Term::op(pairop, vec![v(0), v(1)]),
            goodpair,
            2,
            vec![ConditionFragment::Equality {
                lhs: Term::op(le, vec![v(0), v(1)]),
                rhs: Term::constant(tt),
            }],
        );

        // Build and reduce `< a, b >` before reading its least sort and rewrite count.
        let build = |e: &mut Engine, a: u32, b: u32| -> (SortId, u64) {
            e.reset_rewrites();
            let na = numeral(e, z, s, a);
            let nb = numeral(e, z, s, b);
            let p = e.make_free(pairop, vec![na, nb]);
            let p = e.reduce(p);
            (e.sort_of(p), e.rewrites())
        };
        assert_eq!(
            build(&mut e, 0, 1),
            (goodpair, 2),
            "< z, s z > : GoodPair, 2 rewrites"
        );
        assert_eq!(
            build(&mut e, 1, 0),
            (pair, 1),
            "< s z, z > : Pair (condition fails), 1 rewrite"
        );
        assert_eq!(
            build(&mut e, 0, 0),
            (goodpair, 2),
            "< z, z > : GoodPair, 2 rewrites"
        );
        assert_eq!(
            build(&mut e, 1, 1),
            (goodpair, 3),
            "< s z, s z > : GoodPair, 3 rewrites"
        );
    }

    /// A `:=` condition binds fresh variables by matching its pattern against the reduced subject; the
    /// match itself is not counted as a rewrite.
    #[test]
    fn matching_condition_binds_fresh_variable() {
        let mut e = Engine::new();
        let nat = e.add_sort("Nat");
        e.close_sorts();
        let z = e.add_op("z", vec![], nat);
        let s = e.add_op("s", vec![nat], nat);
        let pred = e.add_op("pred", vec![nat], nat);
        // ceq pred(N) = M if s M := N .   (N = var 0, M = var 1, introduced fresh by the `:=`)
        e.add_conditional_equation(
            Term::op(pred, vec![Term::var(0, nat)]),
            Term::var(1, nat),
            2,
            vec![ConditionFragment::Matching {
                pattern: Term::op(s, vec![Term::var(1, nat)]),
                subject: Term::var(0, nat),
                fresh_vars: vec![1],
            }],
        );

        for (input, expected) in [(2u32, 1u32), (1, 0)] {
            e.reset_rewrites();
            let n = numeral(&mut e, z, s, input);
            let q = e.make_free(pred, vec![n]);
            let r = e.reduce(q);
            assert_eq!(
                e.rewrites(),
                1,
                "pred({input}): one rewrite (the := match is not counted)"
            );
            assert_eq!(decode(&e, r, z, s), expected, "pred({input}) = {expected}");
        }

        // pred(z): `s M := z` has no match → condition fails → no rewrite.
        e.reset_rewrites();
        let n0 = numeral(&mut e, z, s, 0);
        let q0 = e.make_free(pred, vec![n0]);
        let r0 = e.reduce(q0);
        assert_eq!(e.rewrites(), 0, "pred(z): the matching condition fails");
        assert_eq!(e.node(r0).symbol(), pred, "pred(z) is its own normal form");
    }

    /// A `:=` condition reduces its subject before matching.
    #[test]
    fn matching_condition_reduces_subject_first() {
        let mut e = Engine::new();
        let nat = e.add_sort("Nat");
        e.close_sorts();
        let z = e.add_op("z", vec![], nat);
        let s = e.add_op("s", vec![nat], nat);
        let g = e.add_op("g", vec![nat], nat);
        let f = e.add_op("f", vec![nat], nat);
        e.add_equation(Equation {
            lhs: Term::op(g, vec![Term::var(0, nat)]), // g(N) = s s N
            rhs: Term::op(s, vec![Term::op(s, vec![Term::var(0, nat)])]),
            nr_vars: 1,
        });
        e.add_conditional_equation(
            Term::op(f, vec![Term::var(0, nat)]), // ceq f(N) = M if s M := g(N)
            Term::var(1, nat),
            2,
            vec![ConditionFragment::Matching {
                pattern: Term::op(s, vec![Term::var(1, nat)]),
                subject: Term::op(g, vec![Term::var(0, nat)]),
                fresh_vars: vec![1],
            }],
        );

        for (input, expected) in [(0u32, 1u32), (1, 2)] {
            e.reset_rewrites();
            let n = numeral(&mut e, z, s, input);
            let q = e.make_free(f, vec![n]);
            let r = e.reduce(q);
            assert_eq!(e.rewrites(), 2, "f({input}): g reduces (1) + f→M (1)");
            assert_eq!(decode(&e, r, z, s), expected, "f({input}) = {expected}");
        }
    }

    /// A `[ctor]` declaration is recorded but does not affect functional reduction.
    #[test]
    fn ctor_is_recorded_and_inert_for_reduction() {
        let mut e = Engine::new();
        let nat = e.add_sort("Nat");
        e.close_sorts();
        let z = e.add_op("z", vec![], nat);
        let s = e.add_op("s", vec![nat], nat);
        let plus = e.add_op("+", vec![nat, nat], nat);
        e.set_ctor(z);
        e.set_ctor(s);
        assert!(e.is_constructor(z), "z is a constructor");
        assert!(e.is_constructor(s), "s is a constructor");
        assert!(
            !e.is_constructor(plus),
            "+ is a defined function, not a constructor"
        );
        e.add_equation(Equation {
            lhs: Term::op(plus, vec![Term::var(0, nat), Term::constant(z)]),
            rhs: Term::var(0, nat),
            nr_vars: 1,
        });
        e.add_equation(Equation {
            lhs: Term::op(
                plus,
                vec![Term::var(0, nat), Term::op(s, vec![Term::var(1, nat)])],
            ),
            rhs: Term::op(
                s,
                vec![Term::op(plus, vec![Term::var(0, nat), Term::var(1, nat)])],
            ),
            nr_vars: 2,
        });
        let (a, b) = (numeral(&mut e, z, s, 1), numeral(&mut e, z, s, 2));
        let sum = e.make_free(plus, vec![a, b]);
        let r = e.reduce(sum);
        assert_eq!(e.rewrites(), 3, "[ctor] does not change the rewrite count");
        assert_eq!(decode(&e, r, z, s), 3, "s 0 + s s 0 = s s s 0");
    }

    /// With `strat (1 0)`, `if_then_else_fi` reduces the condition and then the selected top while
    /// leaving the unused branch unreduced. The chosen branch is reduced because it becomes the
    /// result.
    #[test]
    fn evaluation_strategy_is_lazy() {
        let mut e = Engine::new();
        let nat = e.add_sort("Nat");
        let truth = e.add_sort("Truth");
        e.close_sorts();
        let tt = e.add_op("tt", vec![], truth);
        let ff = e.add_op("ff", vec![], truth);
        let z = e.add_op("z", vec![], nat);
        let s = e.add_op("s", vec![nat], nat);
        let big = e.add_op("big", vec![], nat);
        let ite = e.add_op("if", vec![truth, nat, nat], nat);
        e.set_strategy(ite, &[1, 0]); // reduce arg 1 (the condition), then top; branches lazy
        let v = |i| Term::var(i, nat);
        e.add_equation(Equation {
            lhs: Term::constant(big), // eq big = s s z
            rhs: Term::op(s, vec![Term::op(s, vec![Term::constant(z)])]),
            nr_vars: 0,
        });
        e.add_equation(Equation {
            lhs: Term::op(ite, vec![Term::constant(tt), v(0), v(1)]), // if tt then X else Y = X
            rhs: v(0),
            nr_vars: 2,
        });
        e.add_equation(Equation {
            lhs: Term::op(ite, vec![Term::constant(ff), v(0), v(1)]), // if ff then X else Y = Y
            rhs: v(1),
            nr_vars: 2,
        });

        // big = s s z (sanity).
        e.reset_rewrites();
        let bnode = e.make_const(big);
        let rb = e.reduce(bnode);
        assert_eq!(e.rewrites(), 1);
        assert_eq!(decode(&e, rb, z, s), 2, "big = s s z");

        // Each case: build if(cond, then, else) and reduce. (cond_is_tt, then_big, expected, rewrites)
        let cases = [
            (true, false, 0u32, 1u64), // if tt then z   else big -> z      (else not reduced)
            (false, true, 0, 1),       // if ff then big else z   -> z      (then not reduced)
            (true, true, 2, 2),        // if tt then big else z   -> s s z  (chosen big IS reduced)
        ];
        for (cond_tt, then_big, expected, rewrites) in cases {
            e.reset_rewrites();
            let cond = if cond_tt {
                e.make_const(tt)
            } else {
                e.make_const(ff)
            };
            let then_arg = if then_big {
                e.make_const(big)
            } else {
                e.make_const(z)
            };
            let else_arg = if then_big {
                e.make_const(z)
            } else {
                e.make_const(big)
            };
            let q = e.make_free(ite, vec![cond, then_arg, else_arg]);
            let r = e.reduce(q);
            assert_eq!(
                e.rewrites(),
                rewrites,
                "rewrite count for case {cond_tt}/{then_big}"
            );
            assert_eq!(
                decode(&e, r, z, s),
                expected,
                "result for case {cond_tt}/{then_big}"
            );
        }
    }

    #[test]
    #[should_panic]
    fn arity_mismatch_panics() {
        let mut e = Engine::new();
        let nat = e.add_sort("Nat");
        e.close_sorts();
        let f = e.add_op("f", vec![nat, nat], nat);
        let _ = e.make_free(f, Vec::new());
    }

    /// An `assoc comm` operator classifies as the ACU theory and carries its axioms +
    /// identity; a plain operator stays Free. (The free hot path must be untouched by AC ops.)
    #[test]
    fn ac_operator_is_classified_acu() {
        use crate::symbol::Theory;
        let mut e = Engine::new();
        let nat = e.add_sort("Nat");
        e.close_sorts();
        let empty = e.add_op("empty", vec![], nat);
        let union = e.add_op_ac("union", vec![nat, nat], nat, Some(empty));
        let plus = e.add_op("+", vec![nat, nat], nat); // a free op, for contrast

        let u = e.symbol(union);
        assert_eq!(u.theory(), Theory::Acu);
        assert_eq!(e.sig.identity_constant(u.identity().unwrap()), Some(empty));
        assert_eq!(e.symbol(plus).theory(), Theory::Free, "a plain op is free");
        assert_eq!(e.symbol(empty).theory(), Theory::Free, "a constant is free");
    }

    #[test]
    #[should_panic(expected = "must be binary")]
    fn ac_operator_must_be_binary() {
        let mut e = Engine::new();
        let nat = e.add_sort("Nat");
        e.close_sorts();
        let _ = e.add_op_ac("bad", vec![nat, nat, nat], nat, None);
    }

    /// Engine with constants `a`,`b`,`c` and an `assoc comm` `+` (no identity) over sort `S`.
    fn ac_ctx() -> (Engine, SortId, SymbolId, SymbolId, SymbolId, SymbolId) {
        let mut e = Engine::new();
        let s = e.add_sort("S");
        e.close_sorts();
        let a = e.add_op("a", vec![], s);
        let b = e.add_op("b", vec![], s);
        let c = e.add_op("c", vec![], s);
        let plus = e.add_op_ac("+", vec![s, s], s, None);
        (e, s, a, b, c, plus)
    }

    /// ACU construction is canonical modulo commutativity and associativity — `a+b == b+a`,
    /// and `(a+b)+c == a+(b+c) == a+b+c` (flattened to a 3-element multiset).
    #[test]
    fn acu_canonical_modulo_ac() {
        let (mut e, _s, a, b, c, plus) = ac_ctx();
        let ab = {
            let (x, y) = (e.make_const(a), e.make_const(b));
            e.make_ac(plus, vec![x, y])
        };
        let ba = {
            let (x, y) = (e.make_const(b), e.make_const(a));
            e.make_ac(plus, vec![x, y])
        };
        assert!(e.deep_equal(ab, ba), "a+b == b+a");
        assert_eq!(
            e.runtime().dag_compare(ab, ba),
            std::cmp::Ordering::Equal,
            "and the total order agrees"
        );

        let abc_left = {
            // (a+b)+c — the left arg is itself an ACU node, must flatten
            let (x, y) = (e.make_const(a), e.make_const(b));
            let ab = e.make_ac(plus, vec![x, y]);
            let z = e.make_const(c);
            e.make_ac(plus, vec![ab, z])
        };
        let abc_right = {
            let (y, z) = (e.make_const(b), e.make_const(c));
            let bc = e.make_ac(plus, vec![y, z]);
            let x = e.make_const(a);
            e.make_ac(plus, vec![x, bc])
        };
        let abc_flat = {
            let (x, y, z) = (e.make_const(a), e.make_const(b), e.make_const(c));
            e.make_ac(plus, vec![x, y, z])
        };
        // Nested same-symbol arguments splice lazily: unreduced nodes remain nested at construction,
        // then become canonically equal at the zero-rewrite normal-form point.
        let abc_left = e.reduce(abc_left);
        let abc_right = e.reduce(abc_right);
        let abc_flat = e.reduce(abc_flat);
        assert!(e.deep_equal(abc_left, abc_right), "(a+b)+c == a+(b+c)");
        assert!(e.deep_equal(abc_left, abc_flat), "(a+b)+c == a+b+c");
        assert_eq!(
            e.node(abc_flat).children().count(),
            3,
            "flattened to 3 children"
        );
    }

    /// Identity (`id:`) elements vanish and the multiset collapses — `a+e == a`, `e+e == e`,
    /// `a+e+b == a+b`.
    #[test]
    fn acu_identity_collapses() {
        let mut e = Engine::new();
        let s = e.add_sort("S");
        e.close_sorts();
        let a = e.add_op("a", vec![], s);
        let b = e.add_op("b", vec![], s);
        let unit = e.add_op("e", vec![], s);
        let plus = e.add_op_ac("+", vec![s, s], s, Some(unit));

        let a_plus_e = {
            let (x, u) = (e.make_const(a), e.make_const(unit));
            e.make_ac(plus, vec![x, u])
        };
        assert_eq!(e.node(a_plus_e).symbol(), a, "a + e collapses to a");

        let e_plus_e = {
            let (u1, u2) = (e.make_const(unit), e.make_const(unit));
            e.make_ac(plus, vec![u1, u2])
        };
        assert_eq!(e.node(e_plus_e).symbol(), unit, "e + e collapses to e");

        let aeb = {
            let (x, u, y) = (e.make_const(a), e.make_const(unit), e.make_const(b));
            e.make_ac(plus, vec![x, u, y])
        };
        assert_eq!(
            e.node(aeb).children().count(),
            2,
            "a + e + b == a + b (2 children)"
        );
    }

    /// Equal elements merge into a multiplicity (`a+a` keeps two children via one `(a,2)` pair),
    /// and a lone element never gets wrapped (`make_ac` of one element is that element).
    #[test]
    fn acu_merges_multiplicity_and_never_wraps_singleton() {
        let (mut e, _s, a, _b, _c, plus) = ac_ctx();
        let aa = {
            let (x, y) = (e.make_const(a), e.make_const(a)); // distinct ids, structurally equal
            e.make_ac(plus, vec![x, y])
        };
        assert_eq!(
            e.node(aa).children().count(),
            2,
            "a + a has two children (multiplicity 2)"
        );
        assert_eq!(e.node(aa).symbol(), plus, "a + a is an ACU node");

        let lone = e.make_const(a);
        let wrapped = e.make_ac(plus, vec![lone]);
        assert_eq!(wrapped, lone, "make_ac of a single element collapses to it");
    }

    /// GC traces an ACU DAG through the visitor (reachable kept, rest reclaimed) and `deep_equal`
    /// is modulo-AC across *distinct* element ids.
    #[test]
    fn acu_gc_and_modulo_equality() {
        let (mut e, _s, a, b, _c, plus) = ac_ctx();
        let ab = {
            let (x, y) = (e.make_const(a), e.make_const(b));
            e.make_ac(plus, vec![x, y])
        }; // ab + a0 + b0 = 3 nodes
        let _garbage = {
            let (x, y) = (e.make_const(b), e.make_const(a));
            e.make_ac(plus, vec![x, y]) // structurally equal to ab but distinct ids
        };
        assert!(e.deep_equal(ab, _garbage), "b+a == a+b across distinct ids");
        assert_eq!(
            e.gc([ab]),
            3,
            "the unreachable b+a subgraph (3 nodes) is reclaimed"
        );
        assert_eq!(e.node(ab).children().count(), 2, "ab survives intact");
    }

    #[test]
    #[should_panic(expected = "make_acu")]
    fn make_free_on_ac_operator_panics() {
        let (mut e, _s, a, _b, _c, plus) = ac_ctx();
        let a0 = e.make_const(a);
        let _ = e.make_free(plus, vec![a0, a0]); // building an ACU op as a free node is a bug
    }

    fn s_of_zero(e: &mut Engine, zero: SymbolId, s: SymbolId) -> DagId {
        let z = e.make_const(zero);
        e.make_free(s, vec![z])
    }

    /// Under `[assoc comm]`, `eq X + 0 = X` rewrites `s 0 + 0 + s 0 + s 0` once to
    /// `s 0 + s 0 + s 0`: `X` absorbs the remainder and the matched ground `0` is removed.
    #[test]
    fn ac_reduce_ground_consumed_with_extension() {
        let mut e = Engine::new();
        let nat = e.add_sort("Nat");
        e.close_sorts();
        let zero = e.add_op("0", vec![], nat);
        let s = e.add_op("s", vec![nat], nat);
        let plus = e.add_op_ac("+", vec![nat, nat], nat, None);
        e.add_equation(Equation {
            lhs: Term::op(plus, vec![Term::var(0, nat), Term::constant(zero)]),
            rhs: Term::var(0, nat),
            nr_vars: 1,
        });
        let (s0a, s0b, s0c) = (
            s_of_zero(&mut e, zero, s),
            s_of_zero(&mut e, zero, s),
            s_of_zero(&mut e, zero, s),
        );
        let z = e.make_const(zero);
        let subject = e.make_ac(plus, vec![s0a, z, s0b, s0c]); // s0 + 0 + s0 + s0
        let r = e.reduce(subject);
        assert_eq!(e.rewrites(), 1, "one rewrite removes the 0");
        let kids: Vec<_> = e.node(r).children().collect();
        assert_eq!(kids.len(), 3, "result is s0 + s0 + s0");
        assert!(
            kids.iter().all(|&k| e.node(k).symbol() == s),
            "all three are successors"
        );
    }

    /// AC reduce lock: ground AC pattern needing a residue splice — `eq a + a = a` on `a + a + b`
    /// → `a + b` in **1** rewrite (the matched `{a,a}` is replaced by `a`, residue `b` spliced).
    #[test]
    fn ac_reduce_ground_pattern_residue_splice() {
        let (mut e, _s, a, b, _c, plus) = ac_ctx();
        e.add_equation(Equation {
            lhs: Term::op(plus, vec![Term::constant(a), Term::constant(a)]),
            rhs: Term::constant(a),
            nr_vars: 0,
        });
        let (a0, a1, b0) = (e.make_const(a), e.make_const(a), e.make_const(b));
        let subject = e.make_ac(plus, vec![a0, a1, b0]); // a + a + b
        let r = e.reduce(subject);
        assert_eq!(e.rewrites(), 1, "a + a = a fires once");
        let mut kids: Vec<_> = e.node(r).children().map(|k| e.node(k).symbol()).collect();
        kids.sort_by_key(|s| format!("{s:?}"));
        assert_eq!(kids, vec![a, b], "result is a + b");
    }

    /// Non-linear AC matching with identity: `eq N ; N = N` reduces `0 ; s0 ; 0 ; s0` to `0 ; s0`
    /// in two rewrites. This requires minimal-first solutions and skipping the empty no-op binding.
    #[test]
    fn ac_reduce_set_idempotency_two_rewrites() {
        let mut e = Engine::new();
        let nat = e.add_sort("Nat");
        e.close_sorts();
        let zero = e.add_op("0", vec![], nat);
        let s = e.add_op("s", vec![nat], nat);
        let empty = e.add_op("empty", vec![], nat);
        let set = e.add_op_ac(";", vec![nat, nat], nat, Some(empty));
        e.add_equation(Equation {
            lhs: Term::op(set, vec![Term::var(0, nat), Term::var(0, nat)]), // N ; N
            rhs: Term::var(0, nat),
            nr_vars: 1,
        });
        // Build inside the construction-dedup window, as every real command subject is:
        // the repeated `0`/`s 0` subterms become ONE shared node each, so the ACU multiset merges
        // by node identity exactly as the frontend-built subject would.
        e.begin_dedup();
        let (z0, z1) = (e.make_const(zero), e.make_const(zero));
        let (s0a, s0b) = (s_of_zero(&mut e, zero, s), s_of_zero(&mut e, zero, s));
        let subject = e.make_ac(set, vec![z0, s0a, z1, s0b]); // 0 ; s0 ; 0 ; s0
        e.end_dedup();
        let r = e.reduce(subject);
        assert_eq!(e.rewrites(), 2, "two duplicate-removal rewrites");
        assert_eq!(e.node(r).children().count(), 2, "result is 0 ; s0");
    }

    /// For a direct flattened AC node, the specialized non-linear matcher binds the maximal quotient:
    /// `eq X + X = X` reduces `a+a+a+a` to `a` in two rewrites. A binary source construction takes
    /// three because its nested nodes reduce bottom-up.
    #[test]
    fn ac_reduce_flat_nonlinear_idempotency_two_rewrites() {
        let (mut e, s, a, _b, _c, plus) = ac_ctx();
        e.add_equation(Equation {
            lhs: Term::op(plus, vec![Term::var(0, s), Term::var(0, s)]), // X + X
            rhs: Term::var(0, s),
            nr_vars: 1,
        });
        // Merge equal leaves into one canonical flat multiset entry with multiplicity four.
        e.begin_dedup();
        let (a0, a1, a2, a3) = (
            e.make_const(a),
            e.make_const(a),
            e.make_const(a),
            e.make_const(a),
        );
        let subject = e.make_ac(plus, vec![a0, a1, a2, a3]); // a + a + a + a
        e.end_dedup();
        let r = e.reduce(subject);
        assert_eq!(
            e.rewrites(),
            2,
            "the specialized matcher takes the maximal quotient of a flat AC node"
        );
        assert_eq!(e.node(r).symbol(), a, "result collapses to the constant a");
    }

    /// For `eq a + X = b` on `a + c + c`, the collector binding assigns all of `c + c` to `X`, so
    /// the result is `b` in one rewrite rather than `b + c` from a minimal binding.
    #[test]
    fn ac_reduce_lone_variable_absorbs() {
        let (mut e, s, a, b, c, plus) = ac_ctx();
        e.add_equation(Equation {
            lhs: Term::op(plus, vec![Term::constant(a), Term::var(0, s)]), // a + X
            rhs: Term::constant(b),
            nr_vars: 1,
        });
        let (a0, c0, c1) = (e.make_const(a), e.make_const(c), e.make_const(c));
        let subject = e.make_ac(plus, vec![a0, c0, c1]); // a + c + c
        let r = e.reduce(subject);
        assert_eq!(e.rewrites(), 1, "a + X = b fires once");
        assert_eq!(
            e.node(r).symbol(),
            b,
            "result is b (X absorbed c + c), not b + c"
        );
    }

    /// A free skeleton can recursively match a structured AC child modulo its theory.
    #[test]
    fn free_pattern_over_theory_subterm_matches() {
        let (mut e, s, a, b, _c, plus) = ac_ctx();
        let c = e.add_op("cc", vec![], s);
        let f = e.add_op("f", vec![s], s); // free, unary
        // eq f(a + b) = cc   — `a + b` is an AC subterm under the free `f`.
        e.add_equation(Equation {
            lhs: Term::op(
                f,
                vec![Term::op(plus, vec![Term::constant(a), Term::constant(b)])],
            ),
            rhs: Term::constant(c),
            nr_vars: 0,
        });
        let (a0, b0) = (e.make_const(a), e.make_const(b));
        let ba = e.make_ac(plus, vec![b0, a0]); // b + a  → canonical a + b
        let subject = e.make_free(f, vec![ba]); // f(b + a)
        let r = e.reduce(subject);
        assert_eq!(e.rewrites(), 1, "f(a + b) = cc fires once");
        assert_eq!(e.node(r).symbol(), c, "result is cc");
    }

    /// A variable beneath a free symbol can bind an entire theory term.
    #[test]
    fn free_pattern_with_variable_over_theory_subject_is_allowed() {
        let (mut e, s, a, b, _c, plus) = ac_ctx();
        let g = e.add_op("g", vec![s], s);
        let f = e.add_op("f", vec![s], s);
        e.add_equation(Equation {
            lhs: Term::op(f, vec![Term::var(0, s)]), // f(X)
            rhs: Term::op(g, vec![Term::var(0, s)]), // g(X)
            nr_vars: 1,
        });
        let (a0, b0) = (e.make_const(a), e.make_const(b));
        let ab = e.make_ac(plus, vec![a0, b0]); // a + b
        let subject = e.make_free(f, vec![ab]); // f(a + b)
        let r = e.reduce(subject);
        assert_eq!(e.rewrites(), 1, "f(X) = g(X) fires once on f(a + b)");
        assert_eq!(e.node(r).symbol(), g, "result is g(a + b)");
    }

    /// A theory-rooted child under another theory operator is compiled as an alien automaton and matched
    /// recursively modulo its own theory.
    #[test]
    fn theory_subterm_under_theory_operator_matches() {
        let mut e = Engine::new();
        let s = e.add_sort("S");
        e.close_sorts();
        let a = e.add_op("a", vec![], s);
        let b = e.add_op("b", vec![], s);
        let c = e.add_op("c", vec![], s);
        let d = e.add_op("d", vec![], s);
        let plus = e.add_op_ac("+", vec![s, s], s, None);
        let semi = e.add_op_ac(";", vec![s, s], s, None);
        let ab = Term::op(plus, vec![Term::constant(a), Term::constant(b)]);
        e.add_equation(Equation {
            lhs: Term::op(semi, vec![ab, Term::constant(c)]),
            rhs: Term::constant(d),
            nr_vars: 0,
        });
        // Build `(b + a) ; c` (the `+` canonicalizes to `a + b`); the alien `a + b` matches it.
        let (a0, b0, c0) = (e.make_const(a), e.make_const(b), e.make_const(c));
        let ba = e.make_ac(plus, vec![b0, a0]);
        let subject = e.make_ac(semi, vec![ba, c0]);
        let r = e.reduce(subject);
        assert_eq!(e.rewrites(), 1, "(a + b) ; c = d fires once");
        assert_eq!(e.node(r).symbol(), d, "result is d");
    }

    /// Engine with constants `a`,`b`,`c`,`d` and an `assoc` (not comm) `__` over sort `E`.
    fn au_ctx() -> (
        Engine,
        SortId,
        SymbolId,
        SymbolId,
        SymbolId,
        SymbolId,
        SymbolId,
    ) {
        let mut e = Engine::new();
        let s = e.add_sort("E");
        e.close_sorts();
        let a = e.add_op("a", vec![], s);
        let b = e.add_op("b", vec![], s);
        let c = e.add_op("c", vec![], s);
        let d = e.add_op("d", vec![], s);
        let cat = e.add_op_au("__", vec![s, s], s, None);
        (e, s, a, b, c, d, cat)
    }

    /// Under `[assoc]`, `eq b c = a` rewrites `d b c d` once to `d a d`; extension matching
    /// preserves and restores both the prefix and suffix.
    #[test]
    fn au_reduce_ground_pattern_extension_both_ends() {
        let (mut e, _s, a, b, c, d, cat) = au_ctx();
        e.add_equation(Equation {
            lhs: Term::op(cat, vec![Term::constant(b), Term::constant(c)]), // b c
            rhs: Term::constant(a),
            nr_vars: 0,
        });
        let (d0, b0, c0, d1) = (
            e.make_const(d),
            e.make_const(b),
            e.make_const(c),
            e.make_const(d),
        );
        let subject = e.make_au(cat, vec![d0, b0, c0, d1]); // d b c d
        let r = e.reduce(subject);
        assert_eq!(e.rewrites(), 1, "b c = a fires once");
        let kids: Vec<_> = e.node(r).children().map(|k| e.node(k).symbol()).collect();
        assert_eq!(kids, vec![d, a, d], "result is the ordered sequence d a d");
    }

    /// For `eq a X = b` on `a c c`, the collector binding assigns the ordered tail `c c` to `X`, so
    /// the result is `b` in one rewrite.
    #[test]
    fn au_reduce_lone_variable_absorbs() {
        let (mut e, s, a, b, c, _d, cat) = au_ctx();
        e.add_equation(Equation {
            lhs: Term::op(cat, vec![Term::constant(a), Term::var(0, s)]), // a X
            rhs: Term::constant(b),
            nr_vars: 1,
        });
        let (a0, c0, c1) = (e.make_const(a), e.make_const(c), e.make_const(c));
        let subject = e.make_au(cat, vec![a0, c0, c1]); // a c c
        let r = e.reduce(subject);
        assert_eq!(e.rewrites(), 1, "a X = b fires once");
        assert_eq!(e.node(r).symbol(), b, "result is b (X absorbed c c)");
    }

    /// CUI construction orders commutative pairs, collapses equal idempotent arguments, and removes
    /// identities immediately.
    #[test]
    fn cui_canonical_comm_idem_identity() {
        let mut e = Engine::new();
        let s = e.add_sort("E");
        e.close_sorts();
        let a = e.add_op("a", vec![], s);
        let b = e.add_op("b", vec![], s);
        let unit = e.add_op("e", vec![], s);
        let f = e.add_op_cui("f", vec![s, s], s, true, false, None);
        let g = e.add_op_cui("g", vec![s, s], s, true, true, None); // idem
        let h = e.add_op_cui("h", vec![s, s], s, true, false, Some(unit)); // id: e

        let fab = {
            let (x, y) = (e.make_const(a), e.make_const(b));
            e.make_cui(f, x, y)
        };
        let fba = {
            let (x, y) = (e.make_const(b), e.make_const(a));
            e.make_cui(f, x, y) // f(b, a) → canonical f(a, b)
        };
        assert!(e.deep_equal(fab, fba), "f(a, b) == f(b, a) (comm)");

        let gaa = {
            let (x, y) = (e.make_const(a), e.make_const(a));
            e.make_cui(g, x, y)
        };
        assert_eq!(e.node(gaa).symbol(), a, "g(a, a) collapses to a (idem)");

        let hae = {
            let (x, u) = (e.make_const(a), e.make_const(unit));
            e.make_cui(h, x, u)
        };
        assert_eq!(e.node(hae).symbol(), a, "h(a, e) collapses to a (id:)");
    }

    /// `eq f(a, b) = c` matches `f(b, a)` modulo commutativity and rewrites it once to `c`.
    #[test]
    fn cui_reduce_modulo_commutativity() {
        let mut e = Engine::new();
        let s = e.add_sort("E");
        e.close_sorts();
        let a = e.add_op("a", vec![], s);
        let b = e.add_op("b", vec![], s);
        let c = e.add_op("c", vec![], s);
        let f = e.add_op_cui("f", vec![s, s], s, true, false, None);
        e.add_equation(Equation {
            lhs: Term::op(f, vec![Term::constant(a), Term::constant(b)]), // f(a, b)
            rhs: Term::constant(c),
            nr_vars: 0,
        });
        let fba = {
            let (x, y) = (e.make_const(b), e.make_const(a));
            e.make_cui(f, x, y) // f(b, a)
        };
        let r = e.reduce(fba);
        assert_eq!(e.rewrites(), 1, "f(a,b)=c matches f(b,a) modulo comm");
        assert_eq!(e.node(r).symbol(), c, "result is c");
    }

    /// Engine with sorts `Zero NzNat < Nat`, `0 : Zero`, and a unary `iter` successor `s_ : Nat -> NzNat`.
    fn iter_ctx() -> (Engine, SortId, SortId, SortId, SymbolId, SymbolId) {
        let mut e = Engine::new();
        let zero = e.add_sort("Zero");
        let nznat = e.add_sort("NzNat");
        let nat = e.add_sort("Nat");
        e.add_subsort(zero, nat);
        e.add_subsort(nznat, nat);
        e.close_sorts();
        let z = e.add_op("0", vec![], zero);
        let s = e.add_op_iter("s", vec![nat], nznat);
        (e, zero, nznat, nat, z, s)
    }

    /// Build `s^n(0)` (a fresh `0` each call, so subjects don't alias).
    fn iter_num(e: &mut Engine, z: SymbolId, s: SymbolId, n: u64) -> DagId {
        let z0 = e.make_const(z);
        e.make_iter(s, n, z0)
    }

    /// Decode an `s^n(0)` numeral (or the `0` constant) back to `n`.
    fn decode_nat(e: &Engine, id: DagId) -> u64 {
        match &e.node(id).term {
            NodeTerm::S { count, .. } => count.to_usize().expect("small numeral") as u64,
            _ => 0,
        }
    }

    /// Render a rational/integer result for comparison: `"2"`, `"3/4"`, `"-3/2"`, `"0/5"`.
    fn rat_str(e: &Engine, minus: SymbolId, div: SymbolId, id: DagId) -> String {
        let int_str = |i: DagId| match &e.node(i).term {
            NodeTerm::Free { symbol, args } if *symbol == minus && args.len() == 1 => {
                format!("-{}", decode_nat(e, args[0]))
            }
            _ => decode_nat(e, i).to_string(),
        };
        match &e.node(id).term {
            NodeTerm::Free { symbol, args } if *symbol == div && args.len() == 2 => {
                format!("{}/{}", int_str(args[0]), int_str(args[1]))
            }
            _ => int_str(id),
        }
    }

    /// Compact iteration stores the exponent, collapses `s^0(x)` to `x`, flattens nested successors,
    /// and derives the result sort from the successor declaration.
    #[test]
    fn iter_node_construction_and_sort() {
        let (mut e, zero, nznat, _nat, z, s) = iter_ctx();
        let z0 = e.make_const(z);
        assert_eq!(e.sort_of(z0), zero, "0 : Zero");
        let s1 = e.make_iter(s, 1, z0);
        assert_eq!(e.sort_of(s1), nznat, "s 0 : NzNat");
        let s5 = e.make_iter(s, 5, z0);
        assert_eq!(e.sort_of(s5), nznat, "s^5 0 : NzNat");

        let collapse = e.make_iter(s, 0, z0);
        assert_eq!(collapse, z0, "s^0(0) collapses to 0");

        let s3 = e.make_iter(s, 3, z0);
        let s2_s3 = e.make_iter(s, 2, s3); // s^2(s^3(0))
        assert!(e.deep_equal(s2_s3, s5), "s^2(s^3(0)) flattens to s^5(0)");
        assert_eq!(
            e.node(s2_s3).children().count(),
            1,
            "an S node has one child (the base)"
        );
    }

    /// S-theory soundness gate: the S `count` is scalar payload, not a child,
    /// so `deep_equal`/`dag_compare` must compare it — else `s^2(0)` and `s^3(0)` (both child `[0]`)
    /// would compare equal.
    #[test]
    fn iter_equality_and_order_use_the_count() {
        let (mut e, _zero, _nznat, _nat, z, s) = iter_ctx();
        let z0 = e.make_const(z);
        let (s2a, s2b, s3) = (
            e.make_iter(s, 2, z0),
            e.make_iter(s, 2, z0),
            e.make_iter(s, 3, z0),
        );
        assert!(
            e.deep_equal(s2a, s2b),
            "s^2(0) == s^2(0) (distinct ids, equal count)"
        );
        assert!(
            !e.deep_equal(s2a, s3),
            "s^2(0) != s^3(0) — count distinguishes them"
        );
        assert_eq!(
            e.runtime().dag_compare(s2a, s3),
            Ordering::Less,
            "s^2 < s^3 by count"
        );
        assert_eq!(e.runtime().dag_compare(s3, s2a), Ordering::Greater);
        assert_eq!(e.runtime().dag_compare(s2a, s2b), Ordering::Equal);
    }

    /// With `eq s s 0 = 0`, successor extension rewrites `s^5(0)` through exponents 3 and 1 in two
    /// rewrites, yielding `s 0 : NzNat`.
    #[test]
    fn iter_reduce_ground_equation() {
        let (mut e, _zero, nznat, _nat, z, s) = iter_ctx();
        e.add_equation(Equation {
            lhs: Term::op(s, vec![Term::op(s, vec![Term::constant(z)])]), // s s 0
            rhs: Term::constant(z),
            nr_vars: 0,
        });
        let s5 = iter_num(&mut e, z, s, 5);
        let r = e.reduce(s5);
        assert_eq!(e.rewrites(), 2, "s^5 -> s^3 -> s^1 (2 rewrites)");
        assert_eq!(e.sort_of(r), nznat, "result s 0 : NzNat");
        let s1 = iter_num(&mut e, z, s, 1);
        assert!(e.deep_equal(r, s1), "result is s 0");
    }

    /// For `eq s s s X = s X`, the variable absorbs the successor surplus: `s^5(0)` reaches `s 0`
    /// in two rewrites and `s^3(0)` reaches it in one.
    #[test]
    fn iter_reduce_variable_equation() {
        let (mut e, _zero, _nznat, nat, z, s) = iter_ctx();
        let sx = |t| Term::op(s, vec![t]);
        e.add_equation(Equation {
            lhs: sx(sx(sx(Term::var(0, nat)))), // s s s X
            rhs: sx(Term::var(0, nat)),         // s X
            nr_vars: 1,
        });
        let s5 = iter_num(&mut e, z, s, 5);
        let r = e.reduce(s5);
        assert_eq!(e.rewrites(), 2, "s^5 -> s^3 -> s^1");
        let s1 = iter_num(&mut e, z, s, 1);
        assert!(e.deep_equal(r, s1), "s^5 -> s 0");

        e.reset_rewrites();
        let s3 = iter_num(&mut e, z, s, 3);
        let r2 = e.reduce(s3);
        assert_eq!(e.rewrites(), 1, "s^3 -> s 0");
        let s1b = iter_num(&mut e, z, s, 1);
        assert!(e.deep_equal(r2, s1b));
    }

    /// A rule step below an iter node keeps the node's count. With `rl a => 0`, `s^3(a)` denotes
    /// `s(s(s(a)))`, so rule-fair rewriting, position-fair rewriting, and the one-step successor that
    /// search explores all give `s^3(0)`, not `s 0`. A rewritten argument that is itself a successor
    /// folds in: with `rl b => s b`, one step takes `s^3(b)` to `s^4(b)`.
    #[test]
    fn rule_steps_below_an_iter_node_keep_its_count() {
        let (mut e, _zero, _nznat, nat, z, s) = iter_ctx();
        let a = e.add_op("a", vec![], nat);
        let b = e.add_op("b", vec![], nat);
        e.add_rule(Term::constant(a), Term::constant(z), 0);
        e.add_rule(Term::constant(b), Term::op(s, vec![Term::constant(b)]), 0);
        let s3_a = |e: &mut Engine| {
            let a0 = e.make_const(a);
            e.make_iter(s, 3, a0)
        };
        let expected = iter_num(&mut e, z, s, 3);

        let subject = s3_a(&mut e);
        let step = e.rewrite(subject).run(&mut e, None);
        assert!(step.done, "rewrite reaches a normal form");
        assert!(
            e.deep_equal(step.term, expected),
            "rewrite: s^3(a) => s^3(0)"
        );

        let subject = s3_a(&mut e);
        let step = e.frewrite(subject, 1).run(&mut e, None);
        assert!(step.done, "frewrite reaches a normal form");
        assert!(
            e.deep_equal(step.term, expected),
            "frewrite: s^3(a) => s^3(0)"
        );

        let subject = s3_a(&mut e);
        let mut search = e.search(subject, Term::var(0, nat), 1, Vec::new(), Arrow::One, None);
        let solution = search.next_solution(&mut e).expect("one successor");
        assert!(
            e.deep_equal(solution.bindings[0], expected),
            "search =>1: the successor of s^3(a) is s^3(0)"
        );
        assert!(search.next_solution(&mut e).is_none(), "only one successor");

        let b0 = e.make_const(b);
        let subject = e.make_iter(s, 3, b0);
        let step = e.rewrite(subject).run(&mut e, Some(1));
        let b1 = e.make_const(b);
        let grown = e.make_iter(s, 4, b1);
        assert!(
            e.deep_equal(step.term, grown),
            "rewrite [1]: s^3(b) => s^4(b)"
        );
    }

    /// Built-in equality returns `tt` or `ff` from structural equality in one rewrite. A decided
    /// branch selects one arm without reducing the unused arm; an undecidable condition normalizes
    /// every arm before user equations are considered.
    #[test]
    fn builtin_equality_and_branch_over_bool() {
        use crate::symbol::SpecialOp;
        let mut e = Engine::new();
        let truth = e.add_sort("Truth");
        let zero = e.add_sort("Zero");
        let nznat = e.add_sort("NzNat");
        let nat = e.add_sort("Nat");
        e.add_subsort(zero, nat);
        e.add_subsort(nznat, nat);
        e.close_sorts();
        let tt = e.add_op("tt", vec![], truth);
        let ff = e.add_op("ff", vec![], truth);
        let unknown = e.add_op("unknown", vec![], truth);
        let z = e.add_op("0", vec![], zero);
        let s = e.add_op_iter("s", vec![nat], nznat);
        let big = e.add_op("big", vec![], nat);
        e.add_equation(Equation {
            lhs: Term::constant(big), // eq big = s s 0
            rhs: Term::op(s, vec![Term::op(s, vec![Term::constant(z)])]),
            nr_vars: 0,
        });
        let eq = e.add_op("~", vec![nat, nat], truth);
        e.set_special(eq, SpecialOp::Equality { eq: tt, neq: ff });
        let myif = e.add_op("myif", vec![truth, nat, nat], nat);
        e.set_special(
            myif,
            SpecialOp::Branch {
                tests: vec![tt, ff],
            },
        );

        // _~_ over (reduced) Nat numerals: structural equality → tt/ff, 1 rewrite each.
        let mut eqtest = |a: u64, b: u64| -> (SymbolId, u64) {
            e.reset_rewrites();
            let (na, nb) = (iter_num(&mut e, z, s, a), iter_num(&mut e, z, s, b));
            let q = e.make_free(eq, vec![na, nb]);
            let r = e.reduce(q);
            (e.node(r).symbol(), e.rewrites())
        };
        assert_eq!(eqtest(2, 2), (tt, 1), "s^2 0 ~ s^2 0 = tt");
        assert_eq!(eqtest(2, 3), (ff, 1), "s^2 0 ~ s^3 0 = ff");
        assert_eq!(eqtest(0, 0), (tt, 1), "0 ~ 0 = tt");

        // myif(tt, 0, big) -> 0, 1 rewrite (dead `big` never reduced).
        e.reset_rewrites();
        let (c, t0, ebig) = (
            e.make_const(tt),
            iter_num(&mut e, z, s, 0),
            e.make_const(big),
        );
        let q = e.make_free(myif, vec![c, t0, ebig]);
        let r = e.reduce(q);
        assert_eq!(e.node(r).symbol(), z, "myif(tt, 0, big) = 0");
        assert_eq!(e.rewrites(), 1, "selection only — big unreduced");

        // myif(tt, big, 0) -> s s 0, 2 rewrites (selection + big reduces).
        e.reset_rewrites();
        let (c, tbig, e0) = (
            e.make_const(tt),
            e.make_const(big),
            iter_num(&mut e, z, s, 0),
        );
        let q = e.make_free(myif, vec![c, tbig, e0]);
        let r = e.reduce(q);
        assert_eq!(e.rewrites(), 2, "selection + big = s s 0");
        let s2 = iter_num(&mut e, z, s, 2);
        assert!(e.deep_equal(r, s2), "myif(tt, big, 0) = s s 0");

        // myif(ff, big, 0) -> 0, 1 rewrite (else branch; big unreduced).
        e.reset_rewrites();
        let (c, tbig, e0) = (
            e.make_const(ff),
            e.make_const(big),
            iter_num(&mut e, z, s, 0),
        );
        let q = e.make_free(myif, vec![c, tbig, e0]);
        let r = e.reduce(q);
        assert_eq!(e.node(r).symbol(), z, "myif(ff, big, 0) = 0");
        assert_eq!(e.rewrites(), 1, "else branch — big unreduced");

        // An unhooked condition leaves the BranchSymbol in place but normalizes every physical branch
        // occurrence. The shared input node must still account for `big` twice.
        e.reset_rewrites();
        let condition = e.make_const(unknown);
        let shared = e.make_const(big);
        let q = e.make_free(myif, vec![condition, shared, shared]);
        let r = e.reduce(q);
        assert_eq!(e.node(r).symbol(), myif);
        assert_eq!(e.rewrites(), 2, "each stuck branch occurrence reduces");
        assert_eq!(
            e.sort_of(r),
            nznat,
            "result sort follows normalized branches"
        );
        let children: Vec<DagId> = e.node(r).children().collect();
        let s2 = iter_num(&mut e, z, s, 2);
        assert_eq!(e.node(children[0]).symbol(), unknown);
        assert!(e.deep_equal(children[1], s2));
        assert!(e.deep_equal(children[2], s2));

        // User equations are deferred until after stuck branches normalize. `hold` is top-only, making
        // an incorrect early equation observable as the unreduced child `big`.
        let hold = e.add_op("hold", vec![nat, nat], nat);
        e.set_strategy(hold, &[0]);
        e.add_equation(Equation {
            lhs: Term::op(
                myif,
                vec![Term::var(0, truth), Term::var(1, nat), Term::var(2, nat)],
            ),
            rhs: Term::op(hold, vec![Term::var(1, nat), Term::var(2, nat)]),
            nr_vars: 3,
        });
        e.reset_rewrites();
        let condition = e.make_const(unknown);
        let big_arg = e.make_const(big);
        let zero_arg = iter_num(&mut e, z, s, 0);
        let q = e.make_free(myif, vec![condition, big_arg, zero_arg]);
        let r = e.reduce(q);
        assert_eq!(e.node(r).symbol(), hold);
        assert_eq!(e.rewrites(), 2, "big reduction, then the user equation");
        let children: Vec<DagId> = e.node(r).children().collect();
        let s2 = iter_num(&mut e, z, s, 2);
        assert!(e.deep_equal(children[0], s2));
        assert_eq!(e.node(children[1]).symbol(), z);
    }

    /// NAT addition, multiplication, and GCD fold ACU multisets with multiplicity. Quotient,
    /// remainder, exponentiation, and comparisons are binary. Each built-in takes one rewrite, result
    /// sorts follow the value, and a non-numeric argument remains as ACU residue.
    #[test]
    fn builtin_nat_arithmetic_and_comparisons() {
        use crate::symbol::{BoolHooks, NatHooks, NumOp, SpecialOp};
        let mut e = Engine::new();
        let truth = e.add_sort("Truth");
        let zero = e.add_sort("Zero");
        let nznat = e.add_sort("NzNat");
        let nat = e.add_sort("Nat");
        e.add_subsort(zero, nat);
        e.add_subsort(nznat, nat);
        e.close_sorts();
        let tt = e.add_op("tt", vec![], truth);
        let ff = e.add_op("ff", vec![], truth);
        let z = e.add_op("0", vec![], zero);
        let s = e.add_op_iter("s", vec![nat], nznat);
        let nh = NatHooks {
            succ: s,
            zero: z,
            minus: None,
        }; // NAT: no negatives
        let bh = BoolHooks {
            true_: tt,
            false_: ff,
        };
        // ACU operators use `NzNat Nat -> NzNat` plus the broader `Nat Nat -> Nat` overload.
        let acu_op = |e: &mut Engine, name: &'static str, op: NumOp| -> SymbolId {
            let o = e.add_op_ac(name, vec![nznat, nat], nznat, None);
            e.add_op_decl(o, vec![nat, nat], nat);
            e.set_special(o, SpecialOp::AcuNumberOp { op, nat: nh });
            o
        };
        let plus = acu_op(&mut e, "+", NumOp::Add);
        let times = acu_op(&mut e, "*", NumOp::Mul);
        let gcd = acu_op(&mut e, "gcd", NumOp::Gcd);
        // free arithmetic → Nat, and relational → Truth.
        let num_op =
            |e: &mut Engine, name: &'static str, op: NumOp, b: Option<BoolHooks>| -> SymbolId {
                let rng = if b.is_some() { truth } else { nat };
                let o = e.add_op(name, vec![nat, nat], rng);
                e.set_special(
                    o,
                    SpecialOp::NumberOp {
                        op,
                        nat: nh,
                        bool_: b,
                    },
                );
                o
            };
        let quo = num_op(&mut e, "quo", NumOp::Quo, None);
        let rem = num_op(&mut e, "rem", NumOp::Rem, None);
        let pow = num_op(&mut e, "^", NumOp::Pow, None);
        let lt = num_op(&mut e, "<", NumOp::Lt, Some(bh));
        let le = num_op(&mut e, "<=", NumOp::Le, Some(bh));
        let x = e.add_op("x", vec![], nat);

        // ACU op of two numerals → (decoded value, sort, rewrites).
        let acu = |e: &mut Engine, op: SymbolId, a: u64, b: u64| -> (u64, SortId, u64) {
            e.reset_rewrites();
            let (na, nb) = (iter_num(e, z, s, a), iter_num(e, z, s, b));
            let q = e.make_ac(op, vec![na, nb]);
            let r = e.reduce(q);
            (decode_nat(e, r), e.sort_of(r), e.rewrites())
        };
        assert_eq!(acu(&mut e, plus, 2, 3), (5, nznat, 1), "2 + 3 = 5");
        assert_eq!(
            acu(&mut e, plus, 2, 2),
            (4, nznat, 1),
            "2 + 2 = 4 (multiplicity fold)"
        );
        assert_eq!(acu(&mut e, plus, 0, 5), (5, nznat, 1), "0 + 5 = 5");
        assert_eq!(acu(&mut e, times, 3, 4), (12, nznat, 1), "3 * 4 = 12");
        assert_eq!(acu(&mut e, times, 2, 2), (4, nznat, 1), "2 * 2 = 4");
        assert_eq!(acu(&mut e, gcd, 12, 18), (6, nznat, 1), "gcd(12, 18) = 6");

        // Free arithmetic op of two numerals → (decoded value, rewrites).
        let arith = |e: &mut Engine, op: SymbolId, a: u64, b: u64| -> (u64, u64) {
            e.reset_rewrites();
            let (na, nb) = (iter_num(e, z, s, a), iter_num(e, z, s, b));
            let q = e.make_free(op, vec![na, nb]);
            let r = e.reduce(q);
            (decode_nat(e, r), e.rewrites())
        };
        assert_eq!(arith(&mut e, quo, 7, 2), (3, 1), "7 quo 2 = 3");
        assert_eq!(arith(&mut e, rem, 7, 2), (1, 1), "7 rem 2 = 1");
        assert_eq!(arith(&mut e, pow, 2, 10), (1024, 1), "2 ^ 10 = 1024");

        // Relational op → Truth constant.
        let cmp = |e: &mut Engine, op: SymbolId, a: u64, b: u64| -> (SymbolId, u64) {
            e.reset_rewrites();
            let (na, nb) = (iter_num(e, z, s, a), iter_num(e, z, s, b));
            let q = e.make_free(op, vec![na, nb]);
            let r = e.reduce(q);
            (e.node(r).symbol(), e.rewrites())
        };
        assert_eq!(cmp(&mut e, lt, 2, 3), (tt, 1), "2 < 3 = tt");
        assert_eq!(cmp(&mut e, lt, 3, 2), (ff, 1), "3 < 2 = ff");
        assert_eq!(cmp(&mut e, le, 3, 3), (tt, 1), "3 <= 3 = tt");

        // Residue: x + 2 + 3 = x + 5 (the non-numeric x survives), NzNat, 1 rewrite.
        e.reset_rewrites();
        let (xn, n2, n3) = (
            e.make_const(x),
            iter_num(&mut e, z, s, 2),
            iter_num(&mut e, z, s, 3),
        );
        let q = e.make_ac(plus, vec![xn, n2, n3]);
        let r = e.reduce(q);
        assert_eq!(e.rewrites(), 1, "x + 2 + 3 = x + 5 in 1 rewrite");
        assert_eq!(e.sort_of(r), nznat, "x + 5 retains the NzNat result sort");
        assert_eq!(e.node(r).symbol(), plus, "result is still a + node");
        let kids: Vec<DagId> = e.node(r).children().collect();
        assert_eq!(kids.len(), 2, "x + 5 has two operands");
        let mut has_x = false;
        let mut has_5 = false;
        for k in kids {
            if e.node(k).symbol() == x {
                has_x = true;
            } else if decode_nat(&e, k) == 5 {
                has_5 = true;
            }
        }
        assert!(has_x && has_5, "x + 5 = {{x, s^5(0)}}");
    }

    /// Signed INT arithmetic represents a negative numeral as `-(s^n(0))`. Canonical negatives take
    /// no rewrite, while double negation and negative zero reduce once. Quotient and remainder
    /// truncate toward zero; the result sort follows the signed value.
    #[test]
    fn builtin_int_signed_arithmetic() {
        use crate::symbol::{BoolHooks, NatHooks, NumOp, SpecialOp};
        let mut e = Engine::new();
        let truth = e.add_sort("Truth");
        let zero = e.add_sort("Zero");
        let nznat = e.add_sort("NzNat");
        let nat = e.add_sort("Nat");
        let nzint = e.add_sort("NzInt");
        let int = e.add_sort("Int");
        e.add_subsort(zero, nat);
        e.add_subsort(nznat, nat);
        e.add_subsort(nznat, nzint);
        e.add_subsort(nat, int);
        e.add_subsort(nzint, int);
        e.close_sorts();
        let tt = e.add_op("tt", vec![], truth);
        let ff = e.add_op("ff", vec![], truth);
        let z = e.add_op("0", vec![], zero);
        let s = e.add_op_iter("s", vec![nat], nznat);
        let minus = e.add_op("-", vec![nznat], nzint); // -_ : NzNat -> NzInt
        e.add_op_decl(minus, vec![int], int); //          -_ : Int -> Int
        let nh = NatHooks {
            succ: s,
            zero: z,
            minus: Some(minus),
        };
        let bh = BoolHooks {
            true_: tt,
            false_: ff,
        };
        e.set_special(minus, SpecialOp::Minus { nat: nh });
        let plus = e.add_op_ac("+", vec![int, int], int, None);
        e.set_special(
            plus,
            SpecialOp::AcuNumberOp {
                op: NumOp::Add,
                nat: nh,
            },
        );
        let times = e.add_op_ac("*", vec![int, int], int, None);
        e.set_special(
            times,
            SpecialOp::AcuNumberOp {
                op: NumOp::Mul,
                nat: nh,
            },
        );
        let sub = e.add_op("-bin", vec![int, int], int);
        e.set_special(
            sub,
            SpecialOp::NumberOp {
                op: NumOp::Sub,
                nat: nh,
                bool_: None,
            },
        );
        let quo = e.add_op("quo", vec![int, nzint], int);
        e.set_special(
            quo,
            SpecialOp::NumberOp {
                op: NumOp::Quo,
                nat: nh,
                bool_: None,
            },
        );
        let rem = e.add_op("rem", vec![int, nzint], int);
        e.set_special(
            rem,
            SpecialOp::NumberOp {
                op: NumOp::Rem,
                nat: nh,
                bool_: None,
            },
        );
        let lt = e.add_op("<", vec![int, int], truth);
        e.set_special(
            lt,
            SpecialOp::NumberOp {
                op: NumOp::Lt,
                nat: nh,
                bool_: Some(bh),
            },
        );

        // Build a signed numeral `v` (`s^v(0)`, or `-(s^|v|(0))`).
        let mk = |e: &mut Engine, v: i64| -> DagId {
            if v >= 0 {
                iter_num(e, z, s, v as u64)
            } else {
                let p = iter_num(e, z, s, (-v) as u64);
                e.make_free(minus, vec![p])
            }
        };
        // Decode a signed numeral.
        let di = |e: &Engine, id: DagId| -> i64 {
            match &e.node(id).term {
                NodeTerm::Free { symbol, args } if *symbol == minus && args.len() == 1 => {
                    -(decode_nat(e, args[0]) as i64)
                }
                _ => decode_nat(e, id) as i64,
            }
        };

        // Negation: `- 3` is canonical (0 rewrites); `- - 3` and `- 0` reduce in 1.
        e.reset_rewrites();
        let m3 = mk(&mut e, -3);
        let r = e.reduce(m3);
        assert_eq!((di(&e, r), e.rewrites()), (-3, 0), "- 3 = -3 (canonical)");
        assert_eq!(e.sorts().name(e.sort_of(r)), "NzInt", "-3 : NzInt");
        e.reset_rewrites();
        let p3 = mk(&mut e, 3);
        let m3a = e.make_free(minus, vec![p3]);
        let mm3 = e.make_free(minus, vec![m3a]);
        let r = e.reduce(mm3);
        assert_eq!((di(&e, r), e.rewrites()), (3, 1), "- - 3 = 3");
        e.reset_rewrites();
        let z0 = e.make_const(z);
        let m0 = e.make_free(minus, vec![z0]);
        let r = e.reduce(m0);
        assert_eq!((di(&e, r), e.rewrites()), (0, 1), "- 0 = 0");

        // Binary ops over an ACU operator (+, *) → (decoded value, rewrites).
        let acu = |e: &mut Engine, op: SymbolId, a: i64, b: i64| -> (i64, u64) {
            e.reset_rewrites();
            let (na, nb) = (mk(e, a), mk(e, b));
            let q = e.make_ac(op, vec![na, nb]);
            let r = e.reduce(q);
            (di(e, r), e.rewrites())
        };
        assert_eq!(acu(&mut e, plus, 2, -5), (-3, 1), "2 + -5 = -3");
        assert_eq!(acu(&mut e, plus, -2, -3), (-5, 1), "-2 + -3 = -5");
        assert_eq!(acu(&mut e, times, 3, -2), (-6, 1), "3 * -2 = -6");
        assert_eq!(acu(&mut e, times, -2, -3), (6, 1), "-2 * -3 = 6");

        // Binary free arithmetic (-, quo, rem) → (decoded value, rewrites).
        let bin = |e: &mut Engine, op: SymbolId, a: i64, b: i64| -> (i64, u64) {
            e.reset_rewrites();
            let (na, nb) = (mk(e, a), mk(e, b));
            let q = e.make_free(op, vec![na, nb]);
            let r = e.reduce(q);
            (di(e, r), e.rewrites())
        };
        assert_eq!(bin(&mut e, sub, 2, 5), (-3, 1), "2 - 5 = -3");
        assert_eq!(bin(&mut e, sub, 5, 2), (3, 1), "5 - 2 = 3");
        assert_eq!(
            bin(&mut e, quo, 7, -2),
            (-3, 1),
            "7 quo -2 = -3 (toward zero)"
        );
        assert_eq!(
            bin(&mut e, rem, -7, 2),
            (-1, 1),
            "-7 rem 2 = -1 (dividend's sign)"
        );

        // Comparison → Truth.
        let cmp = |e: &mut Engine, a: i64, b: i64| -> SymbolId {
            e.reset_rewrites();
            let (na, nb) = (mk(e, a), mk(e, b));
            let q = e.make_free(lt, vec![na, nb]);
            let r = e.reduce(q);
            assert_eq!(e.rewrites(), 1);
            e.node(r).symbol()
        };
        assert_eq!(cmp(&mut e, -2, 3), tt, "-2 < 3 = tt");
        assert_eq!(cmp(&mut e, 3, -2), ff, "3 < -2 = ff");
    }

    /// `_^_`, `_<<_`, and `_>>_` take `Nat` counts of any width. Bases `0` and `±1`, `0 << k`, and
    /// `x >> k` reduce in one rewrite for counts of `2^64` or more. Other bases and nonzero left
    /// shifts that far, powers whose size `bits(|x|) · e` overflows `u64`, and negative (non-`Nat`)
    /// counts stay unreduced.
    #[test]
    fn builtin_pow_and_shift_counts_past_u64() {
        use crate::symbol::{NatHooks, NumOp, SpecialOp};
        let mut e = Engine::new();
        let zero = e.add_sort("Zero");
        let nznat = e.add_sort("NzNat");
        let nat = e.add_sort("Nat");
        let nzint = e.add_sort("NzInt");
        let int = e.add_sort("Int");
        e.add_subsort(zero, nat);
        e.add_subsort(nznat, nat);
        e.add_subsort(nznat, nzint);
        e.add_subsort(nat, int);
        e.add_subsort(nzint, int);
        e.close_sorts();
        let z = e.add_op("0", vec![], zero);
        let s = e.add_op_iter("s", vec![nat], nznat);
        let minus = e.add_op("-", vec![nznat], nzint);
        e.add_op_decl(minus, vec![int], int);
        let nh = NatHooks {
            succ: s,
            zero: z,
            minus: Some(minus),
        };
        e.set_special(minus, SpecialOp::Minus { nat: nh });
        let num_op = |e: &mut Engine, name: &'static str, op: NumOp| -> SymbolId {
            let o = e.add_op(name, vec![int, nat], int);
            e.set_special(
                o,
                SpecialOp::NumberOp {
                    op,
                    nat: nh,
                    bool_: None,
                },
            );
            o
        };
        let pow = num_op(&mut e, "^", NumOp::Pow);
        let shl = num_op(&mut e, "<<", NumOp::Shl);
        let shr = num_op(&mut e, ">>", NumOp::Shr);
        // A signed decimal numeral: `s^n(0)`, or `-(s^n(0))`.
        let num = |e: &mut Engine, v: &str| -> DagId {
            let z0 = e.make_const(z);
            let p = e
                .make_iter_decimal(s, v.trim_start_matches('-'), z0)
                .expect("decimal");
            if v.starts_with('-') {
                e.make_free(minus, vec![p])
            } else {
                p
            }
        };
        // `op(x, k)` → (the result as a signed decimal, or "stuck" if unreduced; rewrites).
        let red = |e: &mut Engine, op: SymbolId, x: &str, k: &str| -> (String, u64) {
            e.reset_rewrites();
            let (x, k) = (num(e, x), num(e, k));
            let q = e.make_free(op, vec![x, k]);
            let r = e.reduce(q);
            let magnitude = |id: DagId| match &e.node(id).term {
                NodeTerm::S { count, .. } => Some(count.to_decimal()),
                _ if e.node(id).symbol() == z => Some("0".to_string()),
                _ => None,
            };
            let shown = match &e.node(r).term {
                NodeTerm::Free { symbol, args } if *symbol == minus => {
                    magnitude(args[0]).map(|m| format!("-{m}"))
                }
                _ => magnitude(r),
            };
            (shown.unwrap_or_else(|| "stuck".into()), e.rewrites())
        };
        let ok = |v: &str| -> (String, u64) { (v.to_string(), 1) };
        let stuck = ("stuck".to_string(), 0);
        let two_64 = "18446744073709551616";
        let odd_wide = "55340232221128654849"; // 3 · 2^64 + 1
        assert_eq!(red(&mut e, pow, "1", two_64), ok("1"));
        assert_eq!(red(&mut e, pow, "-1", two_64), ok("1"));
        assert_eq!(red(&mut e, pow, "-1", odd_wide), ok("-1"));
        assert_eq!(red(&mut e, pow, "0", odd_wide), ok("0"));
        assert_eq!(red(&mut e, shl, "0", two_64), ok("0"));
        assert_eq!(red(&mut e, shr, "7", two_64), ok("0"));
        assert_eq!(red(&mut e, shr, "-7", odd_wide), ok("-1"));
        // No representable result for any other base, or a nonzero left shift, that far.
        assert_eq!(red(&mut e, pow, "2", two_64), stuck);
        assert_eq!(red(&mut e, shl, "-3", two_64), stuck);
        // The power's size `bits(|x|) · e` overflows `u64`.
        assert_eq!(red(&mut e, pow, "2", "9223372036854775808"), stuck);
        assert_eq!(red(&mut e, pow, "7", "6148914691236517206"), stuck);
        // A negative count is off the `Nat` domain.
        assert_eq!(red(&mut e, shr, "7", "-1"), stuck);
        assert_eq!(red(&mut e, shl, "7", "-1"), stuck);
        assert_eq!(red(&mut e, shl, "0", &format!("-{two_64}")), stuck);
        assert_eq!(red(&mut e, pow, "2", "-1"), stuck);
        // Machine-word counts compute as before.
        assert_eq!(red(&mut e, pow, "-3", "3"), ok("-27"));
        assert_eq!(red(&mut e, shl, "-5", "2"), ok("-20"));
        assert_eq!(red(&mut e, shr, "-8", "1"), ok("-4"));
    }

    /// Strings and quoted identifiers are atomic `NodeTerm::Na` constants. String hooks provide
    /// concatenation, length, substring, and comparisons; quoted identifiers match only themselves.
    #[test]
    fn builtin_string_and_qid() {
        use crate::dag::NaValue;
        use crate::symbol::{BoolHooks, NatHooks, SpecialOp, StrOp};
        let mut e = Engine::new();
        let truth = e.add_sort("Truth");
        let zero = e.add_sort("Zero");
        let nznat = e.add_sort("NzNat");
        let nat = e.add_sort("Nat");
        let str_s = e.add_sort("Str");
        let qid_s = e.add_sort("Qid");
        e.add_subsort(zero, nat);
        e.add_subsort(nznat, nat);
        e.close_sorts();
        let tt = e.add_op("tt", vec![], truth);
        let ff = e.add_op("ff", vec![], truth);
        let z = e.add_op("0", vec![], zero);
        let s = e.add_op_iter("s", vec![nat], nznat);
        let strsym = e.add_op("<Strings>", vec![], str_s);
        let qidsym = e.add_op("<Qids>", vec![], qid_s);
        let nh = NatHooks {
            succ: s,
            zero: z,
            minus: None,
        };
        let bh = BoolHooks {
            true_: tt,
            false_: ff,
        };
        let concat = e.add_op(".", vec![str_s, str_s], str_s);
        e.set_special(
            concat,
            SpecialOp::StringOp {
                op: StrOp::Concat,
                str_sym: strsym,
                nat: None,
                bool_: None,
                not_found: None,
            },
        );
        let len = e.add_op("len", vec![str_s], nat);
        e.set_special(
            len,
            SpecialOp::StringOp {
                op: StrOp::Length,
                str_sym: strsym,
                nat: Some(nh),
                bool_: None,
                not_found: None,
            },
        );
        let sub = e.add_op("sub", vec![str_s, nat, nat], str_s);
        e.set_special(
            sub,
            SpecialOp::StringOp {
                op: StrOp::Substr,
                str_sym: strsym,
                nat: Some(nh),
                bool_: None,
                not_found: None,
            },
        );
        let lt = e.add_op("lt", vec![str_s, str_s], truth);
        e.set_special(
            lt,
            SpecialOp::StringOp {
                op: StrOp::Lt,
                str_sym: strsym,
                nat: None,
                bool_: Some(bh),
                not_found: None,
            },
        );
        let se = e.add_op("se", vec![str_s, str_s], truth);
        e.set_special(se, SpecialOp::Equality { eq: tt, neq: ff });
        let qe = e.add_op("qe", vec![qid_s, qid_s], truth);
        e.set_special(qe, SpecialOp::Equality { eq: tt, neq: ff });

        let dstr = |e: &Engine, id: DagId| -> String {
            match &e.node(id).term {
                NodeTerm::Na {
                    value: NaValue::Str(v),
                    ..
                } => String::from_utf8_lossy(v).into_owned(),
                _ => panic!("not a string node"),
            }
        };

        // concat
        e.reset_rewrites();
        let (a, b) = (e.make_string(strsym, b"ab"), e.make_string(strsym, b"cd"));
        let q = e.make_free(concat, vec![a, b]);
        let r = e.reduce(q);
        assert_eq!(
            (dstr(&e, r), e.rewrites()),
            ("abcd".into(), 1),
            "\"ab\" . \"cd\" = \"abcd\""
        );

        // length → Nat (sort follows the value)
        e.reset_rewrites();
        let h = e.make_string(strsym, b"hello");
        let q = e.make_free(len, vec![h]);
        let r = e.reduce(q);
        assert_eq!(
            (decode_nat(&e, r), e.rewrites()),
            (5, 1),
            "len(\"hello\") = 5"
        );
        assert_eq!(e.sorts().name(e.sort_of(r)), "NzNat");
        let empty = e.make_string(strsym, b"");
        let q = e.make_free(len, vec![empty]);
        let r = e.reduce(q);
        assert_eq!(decode_nat(&e, r), 0, "len(\"\") = 0");
        assert_eq!(e.sorts().name(e.sort_of(r)), "Zero");

        // substr(s, start, len)
        e.reset_rewrites();
        let (hh, n1, n3) = (
            e.make_string(strsym, b"hello"),
            iter_num(&mut e, z, s, 1),
            iter_num(&mut e, z, s, 3),
        );
        let q = e.make_free(sub, vec![hh, n1, n3]);
        let r = e.reduce(q);
        assert_eq!(
            (dstr(&e, r), e.rewrites()),
            ("ell".into(), 1),
            "sub(\"hello\", 1, 3) = \"ell\""
        );

        // string comparison + NA equality (string + qid)
        let cmp = |e: &mut Engine, op: SymbolId, x: &str, y: &str| -> SymbolId {
            e.reset_rewrites();
            let (a, b) = (
                e.make_string(strsym, x.as_bytes()),
                e.make_string(strsym, y.as_bytes()),
            );
            let q = e.make_free(op, vec![a, b]);
            let r = e.reduce(q);
            assert_eq!(e.rewrites(), 1);
            e.node(r).symbol()
        };
        assert_eq!(cmp(&mut e, lt, "abc", "abd"), tt, "\"abc\" < \"abd\"");
        assert_eq!(cmp(&mut e, lt, "b", "abc"), ff, "\"b\" < \"abc\" is false");
        assert_eq!(cmp(&mut e, se, "abc", "abc"), tt, "\"abc\" == \"abc\"");
        assert_eq!(
            cmp(&mut e, se, "abc", "abd"),
            ff,
            "\"abc\" == \"abd\" is false"
        );

        // quoted-id NA equality (matches only itself)
        let qcmp = |e: &mut Engine, x: &str, y: &str| -> SymbolId {
            e.reset_rewrites();
            let (a, b) = (e.make_qid(qidsym, x), e.make_qid(qidsym, y));
            let q = e.make_free(qe, vec![a, b]);
            let r = e.reduce(q);
            e.node(r).symbol()
        };
        assert_eq!(qcmp(&mut e, "foo", "foo"), tt, "'foo == 'foo");
        assert_eq!(qcmp(&mut e, "foo", "bar"), ff, "'foo == 'bar is false");
    }

    /// `find`, `rfind`, and `substr` are total over `Nat` indices: an index or count of `2^64` or
    /// more is past the end like any other, and the application reduces in one rewrite.
    #[test]
    fn builtin_string_index_past_machine_width() {
        use crate::dag::NaValue;
        use crate::symbol::{NatHooks, SpecialOp, StrOp};
        let mut e = Engine::new();
        let zero = e.add_sort("Zero");
        let nznat = e.add_sort("NzNat");
        let nat = e.add_sort("Nat");
        let found = e.add_sort("FindResult");
        let str_s = e.add_sort("Str");
        e.add_subsort(zero, nat);
        e.add_subsort(nznat, nat);
        e.add_subsort(nat, found);
        e.close_sorts();
        let z = e.add_op("0", vec![], zero);
        let s = e.add_op_iter("s", vec![nat], nznat);
        let strsym = e.add_op("<Strings>", vec![], str_s);
        let not_found = e.add_op("notFound", vec![], found);
        let nh = NatHooks {
            succ: s,
            zero: z,
            minus: None,
        };
        let str_op = |e: &mut Engine, op: StrOp, dom: Vec<SortId>, range: SortId| -> SymbolId {
            let o = e.add_op(format!("{op:?}"), dom, range);
            e.set_special(
                o,
                SpecialOp::StringOp {
                    op,
                    str_sym: strsym,
                    nat: Some(nh),
                    bool_: None,
                    not_found: Some(not_found),
                },
            );
            o
        };
        let find = str_op(&mut e, StrOp::Find, vec![str_s, str_s, nat], found);
        let rfind = str_op(&mut e, StrOp::Rfind, vec![str_s, str_s, nat], found);
        let substr = str_op(&mut e, StrOp::Substr, vec![str_s, nat, nat], str_s);
        let text = |e: &mut Engine, v: &[u8]| e.make_string(strsym, v);
        let num = |e: &mut Engine, v: &str| {
            let z0 = e.make_const(z);
            e.make_iter_decimal(s, v, z0).expect("decimal")
        };
        // `op(args)` → (the result shown as a string, numeral, or `notFound`; rewrites).
        let red = |e: &mut Engine, op: SymbolId, args: Vec<DagId>| -> (String, u64) {
            e.reset_rewrites();
            let q = e.make_free(op, args);
            let r = e.reduce(q);
            let shown = match &e.node(r).term {
                NodeTerm::Na {
                    value: NaValue::Str(v),
                    ..
                } => format!("{:?}", String::from_utf8_lossy(v)),
                NodeTerm::S { count, .. } => count.to_decimal(),
                _ if e.node(r).symbol() == not_found => "notFound".to_string(),
                _ => "stuck".to_string(),
            };
            (shown, e.rewrites())
        };
        for wide in ["18446744073709551616", "98765432109876543210987"] {
            let args = vec![
                text(&mut e, b"pqrpqr"),
                text(&mut e, b"qr"),
                num(&mut e, wide),
            ];
            assert_eq!(
                red(&mut e, find, args),
                ("notFound".into(), 1),
                "find @ {wide}"
            );
            let args = vec![
                text(&mut e, b"pqrpqr"),
                text(&mut e, b"qr"),
                num(&mut e, wide),
            ];
            assert_eq!(red(&mut e, rfind, args), ("4".into(), 1), "rfind @ {wide}");
            let args = vec![text(&mut e, b"lmnopq"), num(&mut e, "3"), num(&mut e, wide)];
            let opq = (format!("{:?}", "opq"), 1);
            assert_eq!(red(&mut e, substr, args), opq, "substr length @ {wide}");
            let args = vec![text(&mut e, b"lmnopq"), num(&mut e, wide), num(&mut e, "3")];
            let empty = (format!("{:?}", ""), 1);
            assert_eq!(red(&mut e, substr, args), empty, "substr start @ {wide}");
        }
    }

    /// FLOAT hooks provide arithmetic, negation, absolute value, square root, and comparisons over
    /// atomic `NodeTerm::Na` float values. Each hook takes one rewrite; nested hooks compose.
    #[test]
    fn builtin_float_ops() {
        use crate::dag::NaValue;
        use crate::symbol::{BoolHooks, FltOp, SpecialOp};
        let mut e = Engine::new();
        let truth = e.add_sort("Truth");
        let flt = e.add_sort("Flt");
        e.close_sorts();
        let tt = e.add_op("tt", vec![], truth);
        let ff = e.add_op("ff", vec![], truth);
        let fsym = e.add_op("<Floats>", vec![], flt);
        let bh = BoolHooks {
            true_: tt,
            false_: ff,
        };
        let unary = |e: &mut Engine, op: FltOp| -> SymbolId {
            let o = e.add_op("uf", vec![flt], flt);
            e.set_special(
                o,
                SpecialOp::FloatOp {
                    op,
                    float_sym: fsym,
                    bool_: None,
                },
            );
            o
        };
        let binary = |e: &mut Engine, op: FltOp| -> SymbolId {
            let o = e.add_op("bf", vec![flt, flt], flt);
            e.set_special(
                o,
                SpecialOp::FloatOp {
                    op,
                    float_sym: fsym,
                    bool_: None,
                },
            );
            o
        };
        let (neg, abs, sqrt) = (
            unary(&mut e, FltOp::Neg),
            unary(&mut e, FltOp::Abs),
            unary(&mut e, FltOp::Sqrt),
        );
        let (add, sub, mul, div) = (
            binary(&mut e, FltOp::Add),
            binary(&mut e, FltOp::Sub),
            binary(&mut e, FltOp::Mul),
            binary(&mut e, FltOp::Div),
        );
        let lt = e.add_op("lt", vec![flt, flt], truth);
        e.set_special(
            lt,
            SpecialOp::FloatOp {
                op: FltOp::Lt,
                float_sym: fsym,
                bool_: Some(bh),
            },
        );

        let df = |e: &Engine, id: DagId| -> f64 {
            match &e.node(id).term {
                NodeTerm::Na {
                    value: NaValue::Float(b),
                    ..
                } => f64::from_bits(*b),
                _ => panic!("not a float node"),
            }
        };
        // Binary arithmetic (results are exact f64 values).
        let bf = |e: &mut Engine, op: SymbolId, a: f64, b: f64| -> (f64, u64) {
            e.reset_rewrites();
            let (na, nb) = (e.make_float(fsym, a), e.make_float(fsym, b));
            let q = e.make_free(op, vec![na, nb]);
            let r = e.reduce(q);
            (df(e, r), e.rewrites())
        };
        assert_eq!(bf(&mut e, add, 1.5, 2.5), (4.0, 1), "1.5 + 2.5 = 4.0");
        assert_eq!(bf(&mut e, sub, 5.0, 1.5), (3.5, 1), "5.0 - 1.5 = 3.5");
        assert_eq!(bf(&mut e, mul, 2.0, 3.0), (6.0, 1), "2.0 * 3.0 = 6.0");
        assert_eq!(bf(&mut e, div, 7.0, 2.0), (3.5, 1), "7.0 / 2.0 = 3.5");
        // Unary functions.
        let uf = |e: &mut Engine, op: SymbolId, a: f64| -> (f64, u64) {
            e.reset_rewrites();
            let na = e.make_float(fsym, a);
            let q = e.make_free(op, vec![na]);
            let r = e.reduce(q);
            (df(e, r), e.rewrites())
        };
        assert_eq!(uf(&mut e, neg, 1.5), (-1.5, 1), "neg(1.5) = -1.5");
        assert_eq!(uf(&mut e, sqrt, 4.0), (2.0, 1), "sqrt(4.0) = 2.0");
        // Nested: abs(neg(3.0)) = 3.0 in 2 rewrites.
        e.reset_rewrites();
        let n3 = e.make_float(fsym, 3.0);
        let negn3 = e.make_free(neg, vec![n3]);
        let absq = e.make_free(abs, vec![negn3]);
        let r = e.reduce(absq);
        assert_eq!(
            (df(&e, r), e.rewrites()),
            (3.0, 2),
            "abs(neg(3.0)) = 3.0 in 2 rewrites"
        );
        // Comparison → Truth.
        let cf = |e: &mut Engine, a: f64, b: f64| -> SymbolId {
            e.reset_rewrites();
            let (na, nb) = (e.make_float(fsym, a), e.make_float(fsym, b));
            let q = e.make_free(lt, vec![na, nb]);
            let r = e.reduce(q);
            assert_eq!(e.rewrites(), 1);
            e.node(r).symbol()
        };
        assert_eq!(cf(&mut e, 1.5, 2.5), tt, "1.5 < 2.5 = tt");
        assert_eq!(cf(&mut e, 2.5, 1.5), ff, "2.5 < 1.5 = ff");
    }

    /// Rational division canonicalizes `I / N` to lowest terms and returns an integer for denominator
    /// one. Zero numerators and already-canonical fractions remain for equations to handle.
    #[test]
    fn builtin_division_canonicalizes_rationals() {
        use crate::symbol::{NatHooks, SpecialOp};
        let mut e = Engine::new();
        let zero = e.add_sort("Zero");
        let nznat = e.add_sort("NzNat");
        let nat = e.add_sort("Nat");
        let nzint = e.add_sort("NzInt");
        let int = e.add_sort("Int");
        let nzrat = e.add_sort("NzRat");
        let rat = e.add_sort("Rat");
        e.add_subsort(zero, nat);
        e.add_subsort(nznat, nat);
        e.add_subsort(nznat, nzint);
        e.add_subsort(nat, int);
        e.add_subsort(nzint, int);
        e.add_subsort(nzint, nzrat);
        e.add_subsort(int, rat);
        e.add_subsort(nzrat, rat);
        e.close_sorts();
        let z = e.add_op("0", vec![], zero);
        let s = e.add_op_iter("s", vec![nat], nznat);
        let minus = e.add_op("-", vec![nznat], nzint);
        e.add_op_decl(minus, vec![int], int);
        let nh = NatHooks {
            succ: s,
            zero: z,
            minus: Some(minus),
        };
        e.set_special(minus, SpecialOp::Minus { nat: nh });
        let div = e.add_op("/", vec![nzint, nznat], nzrat);
        e.add_op_decl(div, vec![int, nznat], rat);
        e.set_special(div, SpecialOp::Division { nat: nh });

        // Build I / N (numerator `n` signed via `-`, denominator `d` positive), reduce, render result.
        let frac = |e: &mut Engine, n: i64, d: u64| -> (String, u64) {
            e.reset_rewrites();
            let nn = if n >= 0 {
                iter_num(e, z, s, n as u64)
            } else {
                let p = iter_num(e, z, s, (-n) as u64);
                e.make_free(minus, vec![p])
            };
            let dn = iter_num(e, z, s, d);
            let q = e.make_free(div, vec![nn, dn]);
            let r = e.reduce(q);
            (rat_str(e, minus, div, r), e.rewrites())
        };
        assert_eq!(frac(&mut e, 4, 2), ("2".into(), 1), "4/2 = 2");
        assert_eq!(frac(&mut e, 12, 16), ("3/4".into(), 1), "12/16 = 3/4");
        assert_eq!(frac(&mut e, 6, 4), ("3/2".into(), 1), "6/4 = 3/2");
        assert_eq!(frac(&mut e, -6, 4), ("-3/2".into(), 1), "-6/4 = -3/2");
        assert_eq!(frac(&mut e, 5, 1), ("5".into(), 1), "5/1 = 5");
        assert_eq!(
            frac(&mut e, 3, 4),
            ("3/4".into(), 0),
            "3/4 already canonical (0 rewrites)"
        );
        assert_eq!(
            frac(&mut e, 0, 5),
            ("0/5".into(), 0),
            "0/5 left to the user eq (0 rewrites)"
        );
    }

    #[test]
    fn reduces_peano_addition() {
        // sorts Nat; ops 0, s_, _+_; eqs  N + 0 = N  and  N + s M = s (N + M)
        let mut e = Engine::new();
        let nat = e.add_sort("Nat");
        e.close_sorts();
        let zero = e.add_op("0", vec![], nat);
        let s = e.add_op("s", vec![nat], nat);
        let plus = e.add_op("+", vec![nat, nat], nat);

        e.add_equation(Equation {
            lhs: Term::op(plus, vec![Term::var(0, nat), Term::constant(zero)]),
            rhs: Term::var(0, nat),
            nr_vars: 1,
        });
        e.add_equation(Equation {
            lhs: Term::op(
                plus,
                vec![Term::var(0, nat), Term::op(s, vec![Term::var(1, nat)])],
            ),
            rhs: Term::op(
                s,
                vec![Term::op(plus, vec![Term::var(0, nat), Term::var(1, nat)])],
            ),
            nr_vars: 2,
        });

        // peano(n): build s^n(0)
        fn peano(e: &mut Engine, zero: SymbolId, s: SymbolId, n: u32) -> DagId {
            let mut acc = e.make_const(zero);
            for _ in 0..n {
                acc = e.make_free(s, vec![acc]);
            }
            acc
        }

        let two_a = peano(&mut e, zero, s, 2);
        let two_b = peano(&mut e, zero, s, 2);
        let sum = e.make_free(plus, vec![two_a, two_b]); // 2 + 2

        let result = e.reduce(sum);
        let four = peano(&mut e, zero, s, 4);
        assert!(
            e.deep_equal(result, four),
            "2 + 2 should reduce to s s s s 0"
        );
        assert_eq!(e.rewrites(), 3, "three rewrites");
    }

    #[test]
    fn reduces_peano_multiplication() {
        let mut e = Engine::new();
        let nat = e.add_sort("Nat");
        e.close_sorts();
        let zero = e.add_op("0", vec![], nat);
        let s = e.add_op("s", vec![nat], nat);
        let plus = e.add_op("+", vec![nat, nat], nat);
        let times = e.add_op("*", vec![nat, nat], nat);

        let v = |i| Term::var(i, nat);
        let s_of = |t| Term::op(s, vec![t]);
        // N + 0 = N ; N + s M = s (N + M)
        e.add_equation(Equation {
            lhs: Term::op(plus, vec![v(0), Term::constant(zero)]),
            rhs: v(0),
            nr_vars: 1,
        });
        e.add_equation(Equation {
            lhs: Term::op(plus, vec![v(0), s_of(v(1))]),
            rhs: s_of(Term::op(plus, vec![v(0), v(1)])),
            nr_vars: 2,
        });
        // N * 0 = 0 ; N * s M = (N * M) + N
        e.add_equation(Equation {
            lhs: Term::op(times, vec![v(0), Term::constant(zero)]),
            rhs: Term::constant(zero),
            nr_vars: 1,
        });
        e.add_equation(Equation {
            lhs: Term::op(times, vec![v(0), s_of(v(1))]),
            rhs: Term::op(plus, vec![Term::op(times, vec![v(0), v(1)]), v(0)]),
            nr_vars: 2,
        });

        fn peano(e: &mut Engine, zero: SymbolId, s: SymbolId, n: u32) -> DagId {
            let mut acc = e.make_const(zero);
            for _ in 0..n {
                acc = e.make_free(s, vec![acc]);
            }
            acc
        }

        let three = peano(&mut e, zero, s, 3);
        let four = peano(&mut e, zero, s, 4);
        let prod = e.make_free(times, vec![three, four]); // 3 * 4
        let result = e.reduce(prod);
        let twelve = peano(&mut e, zero, s, 12);
        assert!(
            e.deep_equal(result, twelve),
            "3 * 4 should reduce to s^12 0"
        );
        assert_eq!(e.rewrites(), 21, "twenty-one rewrites");
    }

    #[test]
    fn reduced_flag_invalidated_by_new_equation() {
        // A node reduced before an equation is added must not stay
        // cached as canonical. Reduce `a` (no equations) → a; add `a = b`; reduce `a` → b.
        let mut e = Engine::new();
        let s = e.add_sort("S");
        e.close_sorts();
        let a = e.add_op("a", vec![], s);
        let b = e.add_op("b", vec![], s);

        let a0 = e.make_const(a);
        let r1 = e.reduce(a0);
        assert_eq!(
            e.node(r1).symbol(),
            a,
            "no equations yet: a is its own normal form"
        );

        e.add_equation(Equation {
            lhs: Term::constant(a),
            rhs: Term::constant(b),
            nr_vars: 0,
        });
        let r2 = e.reduce(a0); // same id; must re-reduce despite the earlier REDUCED stamp
        assert_eq!(
            e.node(r2).symbol(),
            b,
            "after adding a = b, reducing a yields b"
        );
    }

    #[test]
    fn ill_sorted_argument_blocks_rewrite_and_lands_in_error_sort() {
        // f : Nat -> Nat applied to a Bool (a different kind): the node lands in Nat's error sort,
        // and `eq f(N:Nat) = z` must NOT fire (a Bool can't match a Nat variable). This guards
        // monotone, safe error-sort propagation.
        let mut e = Engine::new();
        let nat = e.add_sort("Nat");
        let boolean = e.add_sort("Bool"); // separate kind
        e.close_sorts();
        let z = e.add_op("z", vec![], nat);
        let f = e.add_op("f", vec![nat], nat);
        let t = e.add_op("t", vec![], boolean);
        e.add_equation(Equation {
            lhs: Term::op(f, vec![Term::var(0, nat)]),
            rhs: Term::constant(z),
            nr_vars: 1,
        });

        let tb = e.make_const(t);
        let ft = e.make_free(f, vec![tb]); // f(t): Bool arg not <= Nat
        assert!(
            e.sorts().sort(e.sort_of(ft)).is_error,
            "ill-sorted f(t) is in the error sort"
        );
        let r = e.reduce(ft);
        assert_eq!(
            e.node(r).symbol(),
            f,
            "f(t) does not rewrite: N:Nat cannot match a Bool"
        );
    }

    /// Build the unary numeral `s^n 0`.
    fn numeral(e: &mut Engine, zero: SymbolId, s: SymbolId, n: u32) -> DagId {
        let mut acc = e.make_const(zero);
        for _ in 0..n {
            acc = e.make_free(s, vec![acc]);
        }
        acc
    }

    /// Decode a canonical Peano numeral `s^k 0` back to `k` (iteratively, so the *test* can't be the
    /// thing that overflows).
    fn decode(e: &Engine, mut id: DagId, zero: SymbolId, s: SymbolId) -> u32 {
        let mut k = 0;
        loop {
            let sym = e.node(id).symbol();
            if sym == zero {
                return k;
            }
            assert_eq!(sym, s, "not a Peano numeral");
            id = e
                .node(id)
                .children()
                .next()
                .expect("successor has one child");
            k += 1;
        }
    }

    /// Depth 200_000 exercises normalization well beyond ordinary call-stack limits. The iterative
    /// work stack must reduce it without overflowing. `s^N + s^N` drives the deepest path because the
    /// addition loop rebuilds `s(plus(..))` and descends through approximately `N` frames.
    #[test]
    fn iterative_reduce_handles_deep_addition_without_overflow() {
        let mut e = Engine::new();
        let nat = e.add_sort("Nat");
        e.close_sorts();
        let zero = e.add_op("0", vec![], nat);
        let s = e.add_op("s", vec![nat], nat);
        let plus = e.add_op("+", vec![nat, nat], nat);
        e.add_equation(Equation {
            lhs: Term::op(plus, vec![Term::var(0, nat), Term::constant(zero)]),
            rhs: Term::var(0, nat),
            nr_vars: 1,
        });
        e.add_equation(Equation {
            lhs: Term::op(
                plus,
                vec![Term::var(0, nat), Term::op(s, vec![Term::var(1, nat)])],
            ),
            rhs: Term::op(
                s,
                vec![Term::op(plus, vec![Term::var(0, nat), Term::var(1, nat)])],
            ),
            nr_vars: 2,
        });

        const N: u32 = 200_000;
        let a = numeral(&mut e, zero, s, N);
        let b = numeral(&mut e, zero, s, N);
        let sum = e.make_free(plus, vec![a, b]);
        let r = e.reduce(sum);
        assert_eq!(decode(&e, r, zero, s), 2 * N, "s^N + s^N = s^2N");
    }

    /// An equation-free chain 200,000 nodes deep is already normal. Iterative traversal must return
    /// the original shared DAG id without overflowing or rebuilding it.
    #[test]
    fn iterative_reduce_walks_deep_spine_without_overflow() {
        let mut e = Engine::new();
        let nat = e.add_sort("Nat");
        e.close_sorts();
        let zero = e.add_op("0", vec![], nat);
        let s = e.add_op("s", vec![nat], nat);
        let chain = numeral(&mut e, zero, s, 200_000);
        let r = e.reduce(chain);
        assert_eq!(
            r, chain,
            "no equations: a deep chain is its own normal form (shared id kept)"
        );
    }

    /// The iterative reducer follows a stable redex sequence: `fib(22) = 17711` in 186579 rewrites.
    #[test]
    fn fib_22_has_stable_rewrite_count() {
        let mut e = Engine::new();
        let nat = e.add_sort("Nat");
        e.close_sorts();
        let zero = e.add_op("0", vec![], nat);
        let s = e.add_op("s", vec![nat], nat);
        let plus = e.add_op("+", vec![nat, nat], nat);
        let fib = e.add_op("fib", vec![nat], nat);

        let v = |i| Term::var(i, nat);
        let s_of = |t| Term::op(s, vec![t]);
        let zero_t = || Term::constant(zero);
        e.add_equation(Equation {
            lhs: Term::op(plus, vec![v(0), zero_t()]),
            rhs: v(0),
            nr_vars: 1,
        });
        e.add_equation(Equation {
            lhs: Term::op(plus, vec![v(0), s_of(v(1))]),
            rhs: s_of(Term::op(plus, vec![v(0), v(1)])),
            nr_vars: 2,
        });
        e.add_equation(Equation {
            lhs: Term::op(fib, vec![zero_t()]),
            rhs: zero_t(),
            nr_vars: 0,
        });
        e.add_equation(Equation {
            lhs: Term::op(fib, vec![s_of(zero_t())]),
            rhs: s_of(zero_t()),
            nr_vars: 0,
        });
        e.add_equation(Equation {
            lhs: Term::op(fib, vec![s_of(s_of(v(0)))]),
            rhs: Term::op(
                plus,
                vec![Term::op(fib, vec![s_of(v(0))]), Term::op(fib, vec![v(0)])],
            ),
            nr_vars: 1,
        });

        let n = numeral(&mut e, zero, s, 22);
        let q = e.make_free(fib, vec![n]);
        let r = e.reduce(q);
        assert_eq!(decode(&e, r, zero, s), 17711, "fib(22) = 17711");
        assert_eq!(e.rewrites(), 186579, "stable rewrite count for fib(22)");
    }

    /// A shared reducible redex is normalized once; normal-form forwarding lets every later reference
    /// reuse the cached result.
    #[test]
    fn shared_reducible_redex_is_reduced_once() {
        let mut e = Engine::new();
        let nat = e.add_sort("Nat");
        e.close_sorts();
        let zero = e.add_op("0", vec![], nat);
        let s = e.add_op("s", vec![nat], nat);
        let plus = e.add_op("+", vec![nat, nat], nat);
        let f = e.add_op("f", vec![nat, nat], nat);
        // eq N + 0 = N
        e.add_equation(Equation {
            lhs: Term::op(plus, vec![Term::var(0, nat), Term::constant(zero)]),
            rhs: Term::var(0, nat),
            nr_vars: 1,
        });

        // C = s 0 + 0, built once and shared into both children of f (a genuine DAG share).
        let s0 = numeral(&mut e, zero, s, 1);
        let z = e.make_const(zero);
        let c = e.make_free(plus, vec![s0, z]);
        let root = e.make_free(f, vec![c, c]); // f(C, C), C shared
        let r = e.reduce(root);

        // f(s 0, s 0): the shared C fired `N + 0 = N` once; the second reference forwarded to the result.
        assert_eq!(e.node(r).symbol(), f);
        assert_eq!(e.rewrites(), 1, "shared reducible redex reduced once total");
    }

    /// A [`RootGuard`] pins its node across `gc`; dropping it releases the root.
    #[test]
    fn root_guard_keeps_node_alive_then_releases_on_drop() {
        let mut e = Engine::new();
        let nat = e.add_sort("Nat");
        e.close_sorts();
        let a = e.add_op("a", vec![], nat);
        let node = e.make_const(a);
        {
            let _g = e.root(node);
            assert_eq!(
                e.gc(Vec::new()),
                0,
                "a guarded node survives gc with no extra roots"
            );
            assert_eq!(e.live_nodes(), 1);
        } // guard dropped here
        assert_eq!(
            e.gc(Vec::new()),
            1,
            "after the guard drops, the node is collected"
        );
        assert_eq!(e.live_nodes(), 0);
    }

    /// `RootGuard::set` retargets the root — e.g. to follow a term as a reduction rewrites it.
    #[test]
    fn root_guard_set_retargets() {
        let mut e = Engine::new();
        let nat = e.add_sort("Nat");
        e.close_sorts();
        let a = e.add_op("a", vec![], nat);
        let b = e.add_op("b", vec![], nat);
        let na = e.make_const(a);
        let nb = e.make_const(b);
        let g = e.root(na);
        g.set(nb); // now protecting nb instead of na
        assert_eq!(
            e.gc(Vec::new()),
            1,
            "na is no longer rooted and is collected"
        );
        assert_eq!(e.live_nodes(), 1);
        assert_eq!(e.node(g.get()).symbol(), b, "the guard now protects nb");
    }

    /// Safe-point GC keeps arena capacity near the live working set during one reduction while
    /// preserving the result. The disabled run records the full allocation high-water; the enabled
    /// run verifies that the work stack and pending child result keep every in-flight root alive.
    #[test]
    fn safe_point_gc_bounds_memory_within_one_reduction() {
        fn run(interval: Option<u64>) -> (u32, u64, usize) {
            let mut e = Engine::new();
            let nat = e.add_sort("Nat");
            e.close_sorts();
            let zero = e.add_op("0", vec![], nat);
            let s = e.add_op("s", vec![nat], nat);
            let plus = e.add_op("+", vec![nat, nat], nat);
            let fib = e.add_op("fib", vec![nat], nat);
            let v = |i| Term::var(i, nat);
            let s_of = |t| Term::op(s, vec![t]);
            let zero_t = || Term::constant(zero);
            e.add_equation(Equation {
                lhs: Term::op(plus, vec![v(0), zero_t()]),
                rhs: v(0),
                nr_vars: 1,
            });
            e.add_equation(Equation {
                lhs: Term::op(plus, vec![v(0), s_of(v(1))]),
                rhs: s_of(Term::op(plus, vec![v(0), v(1)])),
                nr_vars: 2,
            });
            e.add_equation(Equation {
                lhs: Term::op(fib, vec![zero_t()]),
                rhs: zero_t(),
                nr_vars: 0,
            });
            e.add_equation(Equation {
                lhs: Term::op(fib, vec![s_of(zero_t())]),
                rhs: s_of(zero_t()),
                nr_vars: 0,
            });
            e.add_equation(Equation {
                lhs: Term::op(fib, vec![s_of(s_of(v(0)))]),
                rhs: Term::op(
                    plus,
                    vec![Term::op(fib, vec![s_of(v(0))]), Term::op(fib, vec![v(0)])],
                ),
                nr_vars: 1,
            });
            e.set_gc_interval(interval);
            let n = numeral(&mut e, zero, s, 20);
            let q = e.make_free(fib, vec![n]);
            let r = e.reduce(q);
            (decode(&e, r, zero, s), e.rewrites(), e.node_capacity())
        }

        let (val_off, rw_off, cap_off) = run(None);
        let (val_on, rw_on, cap_on) = run(Some(20_000));
        assert_eq!(val_off, 6765, "fib(20) = 6765");
        assert_eq!(val_on, 6765, "safe-point GC does not change the result");
        assert_eq!(
            rw_on, rw_off,
            "safe-point GC does not change the rewrite count"
        );
        assert!(
            cap_on < cap_off,
            "safe-point GC bounds the arena high-water: {cap_on} (on) vs {cap_off} (off)"
        );
    }

    /// Locks the `set_gc_interval` rooting contract: with safe-point GC enabled, a
    /// result held across a later reduction survives *iff* it is pinned by a [`RootGuard`]. Here the
    /// rooted result of `2 + 2` is still `s^4 0` after a second, allocation-heavy reduction triggers
    /// collection. (Without the guard the second reduction would reclaim it — a debug stale-handle
    /// panic / release silent error — which is the documented footgun, not tested here.)
    #[test]
    fn safe_point_gc_preserves_a_rooted_result_across_reductions() {
        let mut e = Engine::new();
        let nat = e.add_sort("Nat");
        e.close_sorts();
        let zero = e.add_op("0", vec![], nat);
        let s = e.add_op("s", vec![nat], nat);
        let plus = e.add_op("+", vec![nat, nat], nat);
        e.add_equation(Equation {
            lhs: Term::op(plus, vec![Term::var(0, nat), Term::constant(zero)]),
            rhs: Term::var(0, nat),
            nr_vars: 1,
        });
        e.add_equation(Equation {
            lhs: Term::op(
                plus,
                vec![Term::var(0, nat), Term::op(s, vec![Term::var(1, nat)])],
            ),
            rhs: Term::op(
                s,
                vec![Term::op(plus, vec![Term::var(0, nat), Term::var(1, nat)])],
            ),
            nr_vars: 2,
        });
        e.set_gc_interval(Some(100)); // collect several times during a reduction

        let two_a = numeral(&mut e, zero, s, 2);
        let two_b = numeral(&mut e, zero, s, 2);
        let sum = e.make_free(plus, vec![two_a, two_b]);
        let four = e.reduce(sum); // s^4 0
        let g = e.root(four); // pin it across the next reduction

        // A second, disjoint reduction whose collections (every ~100 allocs) must not reclaim `four`.
        let big_a = numeral(&mut e, zero, s, 600);
        let big_b = numeral(&mut e, zero, s, 600);
        let big_sum = e.make_free(plus, vec![big_a, big_b]);
        let _ = e.reduce(big_sum);

        assert_eq!(
            decode(&e, g.get(), zero, s),
            4,
            "the rooted result survives intact"
        );
    }

    /// With in-reduction GC enabled, a re-entrant condition reduction must preserve the outer reduction's
    /// live state. Reducing `pair(a, cond(b))` fires a conditional equation whose condition reduces `b + b`
    /// on both sides and triggers several collections. The already-reduced `a` exists only in the outer
    /// frame, so `condition_holds` must protect that frame, its bindings, and its redex until the nested
    /// reduction finishes. The result remains `pair(a, b)`; omitting any of those roots can reclaim `a`
    /// and leave a dangling or reused id.
    #[test]
    fn safe_point_gc_during_condition_preserves_outer_frame() {
        let mut e = Engine::new();
        let nat = e.add_sort("Nat");
        e.close_sorts();
        let zero = e.add_op("0", vec![], nat);
        let s = e.add_op("s", vec![nat], nat);
        let plus = e.add_op("+", vec![nat, nat], nat);
        e.add_equation(Equation {
            lhs: Term::op(plus, vec![Term::var(0, nat), Term::constant(zero)]),
            rhs: Term::var(0, nat),
            nr_vars: 1,
        });
        e.add_equation(Equation {
            lhs: Term::op(
                plus,
                vec![Term::var(0, nat), Term::op(s, vec![Term::var(1, nat)])],
            ),
            rhs: Term::op(
                s,
                vec![Term::op(plus, vec![Term::var(0, nat), Term::var(1, nat)])],
            ),
            nr_vars: 2,
        });
        let pair = e.add_op("pair", vec![nat, nat], nat); // a free ctor, no equations
        // cond(X) = X  if  X + X = X + X  — the condition reduces X + X on both sides (allocating), so a
        // nested safe-point GC fires *inside* it; the equality always holds, so cond(X) → X.
        let cond = e.add_op("cond", vec![nat], nat);
        let x = Term::var(0, nat);
        e.add_conditional_equation(
            Term::op(cond, vec![x.clone()]),
            x.clone(),
            1,
            vec![ConditionFragment::Equality {
                lhs: Term::op(plus, vec![x.clone(), x.clone()]),
                rhs: Term::op(plus, vec![x.clone(), x.clone()]),
            }],
        );
        e.set_gc_interval(Some(20)); // collect frequently — several times within the condition reduce

        // Distinct values (so `a` and `b` are distinct nodes): `a` lives only in `pair`'s frame while
        // `cond(b)`'s condition reduces.
        let a = numeral(&mut e, zero, s, 100);
        let b = numeral(&mut e, zero, s, 120);
        let cb = e.make_free(cond, vec![b]);
        let subj = e.make_free(pair, vec![a, cb]);
        let r = e.reduce(subj);

        let children: Vec<DagId> = e.node(r).children().collect();
        assert_eq!(children.len(), 2, "pair keeps its two arguments");
        assert_eq!(
            decode(&e, children[0], zero, s),
            100,
            "outer-frame sibling survived the condition GC"
        );
        assert_eq!(
            decode(&e, children[1], zero, s),
            120,
            "cond(b) reduced to b"
        );
    }

    /// Matching (`:=`) condition variant: locks the `solve_condition` matching arm's rooting of the
    /// reduced subject — and thus the fresh-var bindings, which are its subterms — across the recursive
    /// solve, under in-reduction GC (a distinct path from the equality arm above). `pickm(X) = Y if
    /// Y := X + X` returns `X + X`; reducing `pickm(b)` reduces `b + b` (allocating → GC fires), and
    /// `pair`'s sibling `a` (outer frame), the subject `b + b`, and the matched `Y` must all survive.
    #[test]
    fn safe_point_gc_during_matching_condition() {
        let mut e = Engine::new();
        let nat = e.add_sort("Nat");
        e.close_sorts();
        let zero = e.add_op("0", vec![], nat);
        let s = e.add_op("s", vec![nat], nat);
        let plus = e.add_op("+", vec![nat, nat], nat);
        e.add_equation(Equation {
            lhs: Term::op(plus, vec![Term::var(0, nat), Term::constant(zero)]),
            rhs: Term::var(0, nat),
            nr_vars: 1,
        });
        e.add_equation(Equation {
            lhs: Term::op(
                plus,
                vec![Term::var(0, nat), Term::op(s, vec![Term::var(1, nat)])],
            ),
            rhs: Term::op(
                s,
                vec![Term::op(plus, vec![Term::var(0, nat), Term::var(1, nat)])],
            ),
            nr_vars: 2,
        });
        let pair = e.add_op("pair", vec![nat, nat], nat);
        let pickm = e.add_op("pickm", vec![nat], nat);
        // pickm(X) = Y  if  Y := X + X  — the `:=` reduces `X + X` (allocating) and binds the fresh `Y` to it.
        e.add_conditional_equation(
            Term::op(pickm, vec![Term::var(0, nat)]),
            Term::var(1, nat),
            2,
            vec![ConditionFragment::Matching {
                pattern: Term::var(1, nat),
                subject: Term::op(plus, vec![Term::var(0, nat), Term::var(0, nat)]),
                fresh_vars: vec![1],
            }],
        );
        e.set_gc_interval(Some(20));

        let a = numeral(&mut e, zero, s, 100);
        let b = numeral(&mut e, zero, s, 60);
        let pb = e.make_free(pickm, vec![b]);
        let subj = e.make_free(pair, vec![a, pb]);
        let r = e.reduce(subj);

        let children: Vec<DagId> = e.node(r).children().collect();
        assert_eq!(children.len(), 2, "pair keeps its two arguments");
        assert_eq!(
            decode(&e, children[0], zero, s),
            100,
            "outer-frame sibling survived the condition GC"
        );
        assert_eq!(
            decode(&e, children[1], zero, s),
            120,
            "pickm(b) = b + b = 120 (matched subject survived)"
        );
    }

    /// Pending rewrite-condition successors remain rooted while an earlier successor is reduced under
    /// per-allocation collection.
    #[test]
    fn rewrite_condition_pending_successors_survive_safe_point_gc() {
        fn run(interval: Option<u64>) -> (bool, bool, u64) {
            let mut e = Engine::new();
            let s = e.add_sort("S");
            e.close_sorts();
            let trigger = e.add_op("trigger", vec![], s);
            let start = e.add_op("start", vec![], s);
            let first = e.add_op("first", vec![], s);
            let value = e.add_op("value", vec![], s);
            let box_ = e.add_op("box", vec![s], s);
            let got = e.add_op("got", vec![s], s);

            e.add_rule(Term::constant(start), Term::constant(first), 0);
            e.add_rule(
                Term::constant(start),
                Term::op(box_, vec![Term::constant(value)]),
                0,
            );
            let y = Term::var(0, s);
            e.add_conditional_rule(
                Term::constant(trigger),
                Term::op(got, vec![y.clone()]),
                1,
                vec![ConditionFragment::Rewrite {
                    lhs: Term::constant(start),
                    pattern: Term::op(box_, vec![y]),
                    fresh_vars: vec![0],
                }],
            );

            e.set_gc_interval(interval);
            let initial = e.make_const(trigger);
            let mut rewriting = e.rewrite(initial);
            let result = rewriting.run(&mut e, Some(1)).term;
            let (symbol, children) = {
                let node = e.node(result);
                (node.symbol(), node.children().collect::<Vec<_>>())
            };
            (
                symbol == got,
                children.len() == 1 && e.node(children[0]).symbol() == value,
                e.rewrites(),
            )
        }

        let off = run(None);
        assert_eq!(off, (true, true, 3), "later successor binds Y: value");
        assert_eq!(
            run(Some(1)),
            off,
            "pending successor survives nested safe-point GC"
        );
    }

    /// Discovered search states and fresh bindings remain rooted while a later equality condition allocates
    /// and reduces before the RHS consumes the binding.
    #[test]
    fn rewrite_condition_discovered_states_and_bindings_survive_safe_point_gc() {
        fn run(interval: Option<u64>) -> (bool, bool, u64) {
            let mut e = Engine::new();
            let s = e.add_sort("S");
            e.close_sorts();
            let trigger = e.add_op("trigger", vec![], s);
            let start = e.add_op("start", vec![], s);
            let middle = e.add_op("middle", vec![], s);
            let value = e.add_op("value", vec![], s);
            let zero = e.add_op("zero", vec![], s);
            let box_ = e.add_op("box", vec![s], s);
            let got = e.add_op("got", vec![s], s);
            let burn = e.add_op("burn", vec![s], s);

            e.add_equation(Equation {
                lhs: Term::op(burn, vec![Term::var(0, s)]),
                rhs: Term::var(0, s),
                nr_vars: 1,
            });
            e.add_rule(Term::constant(start), Term::constant(middle), 0);
            e.add_rule(
                Term::constant(middle),
                Term::op(box_, vec![Term::constant(value)]),
                0,
            );
            let y = Term::var(0, s);
            e.add_conditional_rule(
                Term::constant(trigger),
                Term::op(got, vec![y.clone()]),
                1,
                vec![
                    ConditionFragment::Rewrite {
                        lhs: Term::constant(start),
                        pattern: Term::op(box_, vec![y]),
                        fresh_vars: vec![0],
                    },
                    ConditionFragment::Equality {
                        lhs: Term::op(burn, vec![Term::constant(zero)]),
                        rhs: Term::constant(zero),
                    },
                ],
            );

            e.set_gc_interval(interval);
            let initial = e.make_const(trigger);
            let mut rewriting = e.rewrite(initial);
            let result = rewriting.run(&mut e, Some(1)).term;
            let (symbol, children) = {
                let node = e.node(result);
                (node.symbol(), node.children().collect::<Vec<_>>())
            };
            (
                symbol == got,
                children.len() == 1 && e.node(children[0]).symbol() == value,
                e.rewrites(),
            )
        }

        let off = run(None);
        assert_eq!(
            off,
            (true, true, 4),
            "two search steps + one equality + outer rule"
        );
        assert_eq!(
            run(Some(1)),
            off,
            "discovered states and fresh binding survive later-fragment GC"
        );
    }

    /// Normal-form forwarding needs no construction deduplication. A manually shared `g(a)` referenced
    /// twice under `<_,_>` is reduced once; its forwarding record supplies the cached `b` to the second
    /// argument, yielding `< b, b >`.
    #[test]
    fn forwarding_reduces_a_shared_redex_once() {
        let mut e = Engine::new();
        let elem = e.add_sort("E");
        let pair_sort = e.add_sort("P");
        e.close_sorts();
        let a = e.add_op("a", vec![], elem);
        let b = e.add_op("b", vec![], elem);
        let g = e.add_op("g", vec![elem], elem);
        let pair = e.add_op("<_,_>", vec![elem, elem], pair_sort);
        e.add_equation(Equation {
            lhs: Term::op(g, vec![Term::constant(a)]),
            rhs: Term::constant(b),
            nr_vars: 0,
        });

        let a0 = e.make_const(a);
        let ga = e.make_free(g, vec![a0]); // ONE g(a) node…
        let subj = e.make_free(pair, vec![ga, ga]); // …referenced twice (a real shared DAG)
        e.reset_rewrites();
        let r = e.reduce(subj);

        assert_eq!(
            e.rewrites(),
            1,
            "a shared redex reduces once (forwarding), not once per reference"
        );
        let children: Vec<DagId> = e.node(r).children().collect();
        let bsym = |id| e.node(id).symbol() == b;
        assert!(
            bsym(children[0]) && bsym(children[1]),
            "both arguments forwarded to b: < b, b >"
        );
    }

    #[test]
    fn compound_identity_materializes_as_reduced_canonical_dag() {
        let mut e = Engine::new();
        let s = e.add_sort("S");
        e.close_sorts();
        let a = e.add_op("a", vec![], s);
        let b = e.add_op("b", vec![], s);
        let g = e.add_op("g", vec![s], s);
        let f = e.add_op_ac("f", vec![s, s], s, None);
        e.add_equation(Equation {
            lhs: Term::op(g, vec![Term::constant(a)]),
            rhs: Term::constant(b),
            nr_vars: 0,
        });
        e.reserve_identity(f, s);
        e.set_identity_term(f, Term::op(g, vec![Term::constant(a)]));

        e.reset_rewrites();
        e.prepare_identities();
        let identity = e.sig.symbol(f).identity().expect("reserved identity");
        let first = e.make_identity(identity);
        let second = e.make_identity(identity);

        assert_eq!(
            first, second,
            "repeated fetches reuse the canonical identity DAG"
        );
        assert_eq!(
            e.node(first).symbol(),
            b,
            "g(a) is reduced before the identity is cached"
        );
        assert_eq!(
            e.rewrites(),
            0,
            "identity-cache maintenance does not enter user rewrite statistics"
        );
        let a0 = e.make_const(a);
        let ga = e.make_free(g, vec![a0]);
        let ga = e.reduce(ga);
        let other = e.make_const(a);
        assert_eq!(
            e.make_ac(f, vec![ga, other]),
            other,
            "a value-equal reduced DAG is recognized as identity"
        );
    }

    #[test]
    fn compound_identity_cache_is_a_permanent_explicit_gc_root() {
        let mut e = Engine::new();
        let s = e.add_sort("S");
        e.close_sorts();
        let a = e.add_op("a", vec![], s);
        let b = e.add_op("b", vec![], s);
        let g = e.add_op("g", vec![s], s);
        let f = e.add_op_ac("f", vec![s, s], s, None);
        e.reserve_identity(f, s);
        e.set_identity_term(f, Term::op(g, vec![Term::constant(a)]));
        e.prepare_identities();
        let identity = e.sig.symbol(f).identity().expect("reserved identity");
        let cached = e.make_identity(identity);

        for _ in 0..32 {
            let garbage_a = e.make_const(a);
            let _ = e.make_free(g, vec![garbage_a]);
        }
        assert!(e.gc([]) > 0, "forced collection reclaims unrelated DAGs");

        let fetched = e.make_identity(identity);
        assert_eq!(
            fetched, cached,
            "the permanent cache entry survives explicit collection"
        );
        let child = e
            .node(fetched)
            .children()
            .next()
            .expect("compound identity child");
        assert_eq!(
            e.node(child).symbol(),
            a,
            "collection keeps the full cached identity graph live"
        );
        let b0 = e.make_const(b);
        assert_eq!(
            e.make_ac(f, vec![fetched, b0]),
            b0,
            "the surviving cache still drives identity collapse"
        );
    }

    #[test]
    fn compact_million_count_iter_identity_materializes_without_expansion() {
        let mut e = Engine::new();
        let s = e.add_sort("S");
        e.close_sorts();
        let a = e.add_op("a", vec![], s);
        let g = e.add_op_iter("g", vec![s], s);
        let f = e.add_op_ac("f", vec![s, s], s, None);
        e.reserve_identity(f, s);
        e.set_identity_term(
            f,
            Term::iter(g, Nat::from_u64(1_000_000), Term::constant(a)),
        );

        e.prepare_identities();
        let identity = e.sig.symbol(f).identity().expect("reserved identity");
        let cached = e.make_identity(identity);
        match &e.node(cached).term {
            NodeTerm::S { symbol, count, arg } => {
                assert_eq!(*symbol, g);
                assert_eq!(count, &Nat::from_u64(1_000_000));
                assert_eq!(e.node(*arg).symbol(), a);
            }
            other => {
                panic!("million-count identity expanded instead of using one S node: {other:?}")
            }
        }
        assert_eq!(
            e.live_nodes(),
            2,
            "identity uses only its base and one compact iter DAG node"
        );
        assert_eq!(
            e.make_identity(identity),
            cached,
            "compact identity remains canonical on repeat fetch"
        );
    }
    #[test]
    fn binding_host_reducer_invalidates_prebinding_normal_form_stamp() {
        #[derive(Clone)]
        struct CountingDecline(Arc<AtomicUsize>);

        impl StrictReducer for CountingDecline {
            fn reduce<'ctx>(
                &self,
                _ctx: &mut StrictReduceCtx<'ctx>,
                _call: StrictCall<'ctx>,
            ) -> Result<StrictOutcome<'ctx>, ReducerFault> {
                self.0.fetch_add(1, AtomicOrdering::SeqCst);
                Ok(StrictOutcome::Decline)
            }
        }

        let calls = Arc::new(AtomicUsize::new(0));
        let catalog = HostFunctionCatalog::builder()
            .register(
                "epoch.decline",
                CountingDecline(Arc::clone(&calls)),
                StrictReducerDescriptor::builder(0).build(),
            )
            .expect("register counting reducer")
            .build();
        let mut e = Engine::with_host_functions(catalog);
        let sort = e.add_sort("S");
        e.close_sorts();
        let host = e.add_op("host", vec![], sort);
        let stale_result = e.add_op("stale", vec![], sort);
        let redex = e.make_const(host);
        let stale = e.make_const(stale_result);

        let prebinding_epoch = e.sig.eq_epoch();
        {
            let node = e.rt.dags.get_mut(redex);
            node.reduced_epoch = prebinding_epoch;
            node.nf = Some(stale);
        }

        e.bind_host_function(
            host,
            "epoch.decline",
            ResolvedHostHooks::builder()
                .build()
                .expect("empty hook table"),
        )
        .expect("bind counting reducer");
        assert_eq!(e.sig.eq_epoch(), prebinding_epoch + 1);
        assert_ne!(e.node(redex).reduced_epoch, e.sig.eq_epoch());

        let reduced = e.try_reduce(redex).expect("dispatch newly bound reducer");
        assert_eq!(reduced, redex);
        assert_eq!(calls.load(AtomicOrdering::SeqCst), 1);
        assert_eq!(e.node(redex).reduced_epoch, e.sig.eq_epoch());
    }

    #[test]
    fn successor_enumeration_fault_restores_every_counter_and_trace() {
        #[derive(Clone)]
        struct CountingFault(Arc<AtomicUsize>);

        impl StrictReducer for CountingFault {
            fn reduce<'ctx>(
                &self,
                _ctx: &mut StrictReduceCtx<'ctx>,
                _call: StrictCall<'ctx>,
            ) -> Result<StrictOutcome<'ctx>, ReducerFault> {
                self.0.fetch_add(1, AtomicOrdering::SeqCst);
                Err(ReducerFault::new("successor enumeration fault"))
            }
        }

        let calls = Arc::new(AtomicUsize::new(0));
        let catalog = HostFunctionCatalog::builder()
            .register(
                "successors.fail",
                CountingFault(Arc::clone(&calls)),
                StrictReducerDescriptor::builder(0).build(),
            )
            .expect("register successor fault reducer")
            .build();
        let mut e = Engine::with_host_functions(catalog);
        let smaller = e.add_sort("Smaller");
        let top = e.add_sort("Top");
        e.add_subsort(smaller, top);
        e.close_sorts();
        let state = e.add_op("state", vec![], top);
        let target = e.add_op("target", vec![], top);
        let membership_subject = e.add_op("membershipSubject", vec![], top);
        let helper_start = e.add_op("helperStart", vec![], top);
        let helper_done = e.add_op("helperDone", vec![], top);
        let faulting = e.add_op("faulting", vec![], top);
        e.bind_host_function(
            faulting,
            "successors.fail",
            ResolvedHostHooks::builder()
                .build()
                .expect("empty hook table"),
        )
        .expect("bind successor fault reducer");
        e.add_membership(Membership {
            lhs: Term::constant(membership_subject),
            sort: smaller,
            nr_vars: 0,
        });
        e.add_rule(Term::constant(helper_start), Term::constant(helper_done), 0);
        e.add_conditional_rule(
            Term::constant(state),
            Term::constant(target),
            0,
            vec![
                ConditionFragment::SortTest {
                    term: Term::constant(membership_subject),
                    sort: smaller,
                },
                ConditionFragment::Rewrite {
                    lhs: Term::constant(helper_start),
                    pattern: Term::constant(helper_done),
                    fresh_vars: Vec::new(),
                },
                ConditionFragment::Equality {
                    lhs: Term::constant(faulting),
                    rhs: Term::constant(target),
                },
            ],
        );
        e.add_rule(Term::constant(state), Term::constant(target), 0);
        e.set_trace(true);

        let root = e.make_const(state);
        let fault = match e.state_successors(root) {
            Err(fault) => fault,
            Ok(_) => panic!("successor enumeration must stop at the reducer fault"),
        };
        assert_eq!(fault.key().expect("fault key").as_str(), "successors.fail");
        assert_eq!(fault.message(), "successor enumeration fault");
        assert_eq!(calls.load(AtomicOrdering::SeqCst), 1);
        assert_eq!(e.rewrites(), 0);
        assert_eq!(e.rewrite_breakdown(), (0, 0, 0, 0));
        assert!(e.take_trace().is_empty());
    }
}
