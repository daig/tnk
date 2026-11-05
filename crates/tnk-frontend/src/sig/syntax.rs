//! Frontend syntax and resolution tables produced by [`build_module`](super::build_sig::build_module)
//! and consumed by the grammar builder and pretty-printer.

use crate::lex::{Frag, Token};
use crate::surface::ast::{GatherElem, IdSide, Statement};
use std::collections::{HashMap, HashSet};
use tnk_core::engine::Engine;
use tnk_core::host::ResolvedHostHooks;
use tnk_core::sort::SortId;
use tnk_core::symbol::SymbolId;
use tnk_core::term::{ConditionFragment, Term};

/// One operator's surface syntax — the per-symbol record the kernel does not store. Holds the mixfix
/// fragments, resolved domain/range, and user `prec`/`gather`; the grammar builder supplies defaults.
#[derive(Debug, Clone)]
pub struct SymbolSyntax {
    pub frags: Vec<Frag>,
    pub domain: Vec<SortId>,
    pub range: SortId,
    pub prec: Option<u32>,
    pub gather: Option<Vec<GatherElem>>,
    /// A constructor of `Attribute` with the reserved canonical `name:_` shape. Retained
    /// independently of the kernel's merged constructor flag for META Qid encoding.
    pub object_attribute: bool,
    /// Whether source spelling separated the attribute label from `:_`; retained for printing.
    pub spaced_label_colon: bool,
    /// Whether the operator carries the `assoc` axiom (ACU/AU). Recorded from the attributes (the kernel
    /// keeps the theory `pub(crate)`); the grammar builder uses it to choose the flattened assoc-list
    /// prefix form `f(<assocList>)` over the positional `f(a, …)` form, and the right-associating gather.
    pub assoc: bool,
    /// Whether the operator carries `iter`; the grammar uses it to accept `f^count(t)`.
    pub iter: bool,
    /// Per-gap `format (…)` directives for spacing and indentation. `None` selects default spacing.
    pub format: Option<Vec<String>>,
}

impl SymbolSyntax {
    pub fn arity(&self) -> usize {
        self.domain.len()
    }
    pub fn is_constant(&self) -> bool {
        self.domain.is_empty()
    }
}

/// One source operator declaration after sort resolution. Distinct connected-component overloads have
/// distinct [`symbol`](Self::symbol)s; subsort overloads in the same component share one symbol but retain
/// each declaration profile here. Grammar-aware view maps use this table to resolve a disambiguated source
/// signature to the same symbol identity as the term parser.
#[derive(Debug, Clone)]
pub struct OpProfile {
    pub symbol: SymbolId,
    pub domain: Vec<SortId>,
    pub range: SortId,
}

/// Source-form trace metadata for one equation, keyed by the kernel's dense equation id
/// (`BuiltModule::eq_traces[id]`). The kernel keeps no source `Term`s, so the full trace renderer reads
/// the body from here: it Term-prints `[c]eq {lhs} = {rhs}[ if {condition}][ \[owise\]] .` and labels the
/// `Var --> binding` substitution lines from `var_names` (statement-local index → name).
#[derive(Debug, Clone)]
pub struct EqTrace {
    pub lhs: Term,
    pub rhs: Term,
    /// The condition fragments (empty for an unconditional `eq`), in source form for Term-printing the
    /// `if …` clause and the per-fragment `solving/success/failure condition fragment` lines.
    pub condition: Vec<ConditionFragment>,
    /// Statement-local variable names, indexed as the kernel's substitution is (first occurrence order).
    pub var_names: Vec<String>,
    pub owise: bool,
    /// Whether the equation carries `[variant]`.
    pub variant: bool,
    /// The `[label …]` name, if any — retained for META `upEqs`/`upModule` (renders `[label('l)]`), not
    /// used by execution.
    pub label: Option<String>,
    /// A `[nonexec]` axiom (a proof obligation). Engine-registered traces are always `false` because loading
    /// skips these axioms. Reflective encoding parses a module's own `[nonexec]` equations on demand through
    /// [`parse_statement_trace`](crate::load::parse_statement_trace).
    pub nonexec: bool,
}

/// Source-form trace metadata for one membership axiom, keyed by the kernel's dense membership id
/// (`BuiltModule::mb_traces[id]`). Its fields correspond to membership syntax and reuse [`EqTrace`] conventions.
#[derive(Debug, Clone)]
pub struct MbTrace {
    pub lhs: Term,
    pub sort: SortId,
    pub condition: Vec<ConditionFragment>,
    pub var_names: Vec<String>,
    /// The `[label …]` name, if any — retained for META `upMbs`/`upModule`. See [`EqTrace::label`].
    pub label: Option<String>,
    /// A `[nonexec]` membership axiom — see [`EqTrace::nonexec`].
    pub nonexec: bool,
}

/// Source-form trace metadata for one rule, keyed by the kernel's dense rule id
/// (`BuiltModule::rl_traces[id]`). The full trace renderer uses it for `*********** rule`, and
/// `show path` uses it for `===[ rl … ]===>`.
#[derive(Debug, Clone)]
pub struct RlTrace {
    pub lhs: Term,
    pub rhs: Term,
    pub condition: Vec<ConditionFragment>,
    pub var_names: Vec<String>,
    /// The `[label]` of a labelled rule (`rl [foo] : …`), if any — rendered in the body and on the
    /// `show path` arc.
    pub label: Option<std::rc::Rc<str>>,
    /// A `[nonexec]` rule — see [`EqTrace::nonexec`].
    pub nonexec: bool,
    /// A `[narrowing]` rule. It remains available to symbolic narrowing even when `nonexec` is set.
    pub narrowing: bool,
}

#[derive(Debug, Clone)]
pub struct IdentitySpec {
    pub symbol: SymbolId,
    pub sort: SortId,
    pub side: IdSide,
    pub tokens: Vec<Token>,
}

pub(crate) struct PendingHostBinding {
    pub symbol: SymbolId,
    pub key: String,
    pub hooks: ResolvedHostHooks,
}

/// A built module: kernel engine plus frontend resolution tables and raw statements. Statement term
/// bubbles are parsed only after the per-module grammar has been built.
pub struct BuiltModule {
    pub engine: Engine,
    pub name: String,
    /// Sort name → id.
    pub sorts: HashMap<String, SortId>,
    /// `(canonical mixfix name, arity)` → symbol id (overloads/`ditto` share one id).
    pub ops: HashMap<(String, usize), SymbolId>,
    /// Per-symbol surface syntax.
    pub syntax: HashMap<SymbolId, SymbolSyntax>,
    /// Every resolved source operator declaration, including overloads folded into one symbol.
    pub op_profiles: Vec<OpProfile>,
    /// Declared variables `(name, sort)` (from `var`/`vars`). Used by the grammar builder (variable
    /// productions) and `build_term` (resolving a variable token to its sort + statement-local index).
    pub vars: Vec<(String, SortId)>,
    /// Raw statement bubbles, parsed and installed by `load_statements`.
    pub statements: Vec<Statement>,
    /// Validated source host attachments, committed after source equations have been installed.
    pub(crate) pending_host_bindings: Vec<PendingHostBinding>,
    /// Per-equation trace metadata, indexed by the kernel's dense equation id (populated by
    /// `load_statements`; empty until statements are loaded). See [`EqTrace`].
    pub eq_traces: Vec<EqTrace>,
    /// Per-membership trace metadata, indexed by the kernel's dense membership id. See [`MbTrace`].
    pub mb_traces: Vec<MbTrace>,
    /// Per-rule trace metadata, indexed by the kernel's dense rule id (populated by `load_statements`).
    /// See [`RlTrace`].
    pub rl_traces: Vec<RlTrace>,
    /// Verbose `omod` object-completion notices for statements defined by this module. Each entry is
    /// preformatted but unwrapped; the REPL emits it once when the defining module is entered.
    pub oo_completion_diagnostics: Vec<String>,
    /// Built-in literal anchors (for the grammar's literal productions + `make_*` in build_term).
    pub nat_succ: Option<SymbolId>,
    pub nat_zero: Option<SymbolId>,
    pub string_sym: Option<SymbolId>,
    pub float_sym: Option<SymbolId>,
    pub qid_sym: Option<SymbolId>,
    /// Unary minus, when present; used to render negative numerals compactly.
    pub minus_sym: Option<SymbolId>,
    /// The `_/_` division operator, if present; rational values render compactly as `num/den`.
    pub division_sym: Option<SymbolId>,
    /// Boolean truth anchors tagged `SystemTrue` and `SystemFalse`. They desugar a bare Boolean
    /// condition into equality with true and support sort-test predicates. Absent until declared.
    pub true_sym: Option<SymbolId>,
    pub false_sym: Option<SymbolId>,
    /// Per-symbol overload flags for print disambiguation. Cross-kind overloads print `(term).Sort`
    /// when context cannot determine a range. [`OVL_ADHOC`] means another symbol shares the name;
    /// [`OVL_DOMAIN`] also shares domain kinds; [`OVL_RANGE`] also shares the range kind;
    /// [`OVL_ITER`] marks two `iter` operators sharing the name.
    pub overload: HashMap<SymbolId, u8>,
    /// Number of kinds whose built-in values use positive decimal syntax. An unknown-range numeral
    /// requires sort qualification when more than one such kind exists.
    pub(crate) integer_literal_kind_count: usize,
    /// Canonical positive decimal spellings also declared as nullary user operators. These collide with
    /// built-in natural pseudo-literals even when there is only one numeral kind.
    pub(crate) overloaded_naturals: HashSet<String>,
    /// Nullary operators whose declared name is a literal token that one of this module's literal
    /// productions also accepts (`op "hi" : -> Foo` beside `STRING`, `op 42 : -> Foo` beside `NAT`).
    /// Their bare spelling also denotes the literal, so printing qualifies them as `(c).Sort` whenever
    /// context does not fix the range. Zero-valued numeral spellings are never included: the successor
    /// production accepts only positive values, so `0` parses as the declared zero constant alone.
    pub(crate) literal_named_constants: HashSet<SymbolId>,
    /// String values (decoded bytes) spelled by a [`literal_named_constants`](Self::literal_named_constants)
    /// member. Such a string literal prints `("…").Sort` when context does not fix the range.
    pub(crate) overloaded_strings: HashSet<Vec<u8>>,
    /// Quoted-identifier names (without the leading `'`) spelled by a literal-named constant.
    pub(crate) overloaded_qids: HashSet<String>,
    /// Float values (`f64` bit patterns) spelled by a literal-named constant.
    pub(crate) overloaded_floats: HashSet<u64>,
    /// Strategy declarations after module flattening. The interpreter coalesces these by
    /// `(name, domain kinds, subject kind)` while retaining donation origins for conflict handling.
    pub strat_decls: Vec<crate::surface::ast::StratDecl>,
    /// Strategy definitions (`sd`/`csd`) indexed by the strategy interpreter. Empty outside strategy
    /// modules.
    pub strat_defs: Vec<crate::surface::ast::StratDef>,
    /// Identity attribute bubbles retained until the module grammar exists, then parsed and installed
    /// as signature-owned ground terms before statements are compiled.
    pub identity_specs: Vec<IdentitySpec>,
}

/// Another symbol shares this one's name ([`BuiltModule::overload`]).
pub const OVL_ADHOC: u8 = 1;
/// Another symbol shares this one's name and domain kinds — printing must disambiguate `(t).Sort` when
/// the range is not determined by context.
pub const OVL_DOMAIN: u8 = 2;
/// Another symbol shares this one's name and range kind.
pub const OVL_RANGE: u8 = 4;
/// This `iter` operator and another `iter` operator share the name. They lie in different kinds, so
/// the compact `f^N(t)` form parses as either and only context or the argument selects one.
pub const OVL_ITER: u8 = 8;
