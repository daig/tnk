//! Operator symbols.
//!
//! A symbol owns its overloaded sort declarations, structural axioms and identities, evaluation
//! attributes, and optional built-in hook. The closed `Theory` enum classifies structural behavior;
//! parsing remains the frontend's responsibility.
//!
//! Fields are `pub(crate)`; read access is through getters.

use crate::id::Id;
use crate::smt::SmtOp;
use crate::sort::SortId;
use crate::term::Term;

pub type SymbolId = Id<Symbol>;

pub(crate) type IdentityId = Id<Identity>;

/// A ground identity term owned by the signature. Symbols carry an [`IdentityId`] rather than
/// assuming the identity is a nullary operator; the runtime materializes `term` once as a rooted,
/// reduced DAG for collapse, matching, and symbolic identity insertion.
#[derive(Debug, Clone)]
pub(crate) struct Identity {
    pub(crate) term: Option<Term>,
    pub(crate) sort: SortId,
}

/// The structural axioms declared on an operator. Two-sided and one-sided identities are stored
/// separately because they may be arbitrary ground terms.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub(crate) struct Axioms {
    pub assoc: bool,
    pub comm: bool,
    /// Idempotence (`f(a, a) = a`) — only meaningful for the commutative, non-associative CUI theory
    /// in this slice (`idem` cannot combine with `assoc`).
    pub idem: bool,
    /// Iteration: a unary stacked successor whose DAG node stores the count compactly.
    pub iter: bool,
}

/// Which equational theory selects an operator's canonical DAG representation and matching automaton.
/// This closed set covers free, ACU, AU, CUI, and iterated-successor operators; atomic built-in constants
/// use [`NodeTerm::Na`](crate::dag::NodeTerm).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Theory {
    /// No structural axioms: `symbol(args...)` matched by direct structural recursion.
    Free,
    /// Associative + commutative (with an optional two-sided identity): a flattened **multiset** of
    /// arguments, matched modulo AC(+U).
    Acu,
    /// Associative (with an optional two-sided identity), **not** commutative: a flattened **ordered
    /// sequence** of arguments, matched modulo A(+U) — e.g. lists, string concatenation.
    Au,
    /// Commutative (with optional identity and/or idempotence), **not** associative: a binary node
    /// with canonically-ordered arguments, matched modulo C(+U+I).
    Cui,
    /// Iterated successor represented as `s^count(arg)` and matched by count prefix.
    S,
}

/// One operator declaration: argument sorts (`domain`) → `range`, plus whether it is a constructor
/// (`[ctor]`). An operator may carry several declarations (ad-hoc / subsort overloading); the least
/// sort of an application is resolved across all of them (`Signature::compute_sort`). `ctor` is
/// reduction-inert metadata consumed by constructor-sensitive symbolic analyses.
#[derive(Debug, Clone)]
pub(crate) struct OpDeclaration {
    pub domain: Vec<SortId>,
    pub range: SortId,
    /// `[ctor]` flag. Constructors use ordinary reduction; constructor-theory checks consume this
    /// metadata for analyses such as variant-satisfiability eligibility and decomposition.
    pub ctor: bool,
}

/// One normalized instruction in an operator's equational evaluation strategy. Surface `strat`
/// entries use 1-based argument numbers and `0` for a root attempt; the signature converts them
/// once into zero-based [`EvalStep::Argument`] and [`EvalStep::Top`] values.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum EvalStep {
    Argument(u32),
    Top,
}

/// Runtime form of a nonstandard operator evaluation strategy.
#[derive(Debug, Clone)]
pub(crate) enum EvalStrategy {
    /// An ordinary fixed-arity strategy, including its final [`EvalStep::Top`].
    Sequence(Vec<EvalStep>),
    /// Associative operators cannot retain their two declared positions after flattening. A
    /// top-first, non-lazy strategy therefore expands dynamically to a root attempt, every physical
    /// argument, and another root attempt.
    PermutativeSemiEager,
}

#[derive(Debug, Clone)]
pub struct Symbol {
    pub(crate) name: String,
    /// Operator declarations (≥ 1; the first is the first registered). Overloads share name + arity;
    /// sort resolution walks them **in declaration order**, so order determines the non-preregular
    /// least-sort tie-break.
    pub(crate) decls: Vec<OpDeclaration>,
    /// The structural axioms this operator is declared with.
    pub(crate) axioms: Axioms,
    /// Sticky signature-build diagnostic: constructor overload declarations in this symbol did not
    /// agree on their structural axiom/identity profile. The runtime keeps the first declaration's
    /// executable theory; semantic clients must reject the inconsistent constructor family.
    pub(crate) inconsistent_constructor_axioms: bool,
    /// The operator's two-sided identity (`id: <term>`), if any. The referenced signature entry owns
    /// the general ground term; the runtime caches its normalized DAG as a permanent GC root.
    pub(crate) identity: Option<IdentityId>,
    /// A **one-sided** identity (`left id:` / `right id:`), recorded for construction and symbolic
    /// collapse with the same general identity-term representation.
    pub(crate) one_sided_id: Option<(IdentitySide, IdentityId)>,
    /// Normalized nonstandard equational evaluation strategy (`strat (…)`). `None` reduces every
    /// physical argument left-to-right before trying the root. A custom sequence retains interleaved
    /// root attempts; associative semi-eager strategies use a dynamic form because a flattened
    /// runtime node can have more arguments than its binary declaration.
    pub(crate) strategy: Option<EvalStrategy>,
    /// Whether the last raw strategy supplied to the signature was exactly the strict eager argument
    /// order, with an optional sole final top attempt. Unlike `strategy`, this retains rejected
    /// duplicate and incremental source steps after normalization.
    pub(crate) strict_eager_source_strategy: bool,
    /// Frozen arguments (`frozen` / `frozen (…)`): the 0-based argument positions that
    /// `rewrite`/`frewrite`/`search` must **not** rewrite within. `None` = no frozen args; `Some([])` =
    /// all arguments frozen (`[frozen]`); `Some([0,2])` = those positions. Inert for equational `reduce`.
    pub(crate) frozen: Option<Vec<u32>>,
    /// Built-in reduction rule (`special (id-hook …)`), if any — tried before user equations.
    pub(crate) special: Option<SpecialOp>,
    /// Object-system role flags (`config`/`obj`/`msg`/`portal`). Ordinary reduction and rewriting treat
    /// the configuration as an ACU soup; the `erewrite` scheduler uses these flags to partition objects,
    /// messages, and portals.
    pub(crate) oo: OoFlags,
    /// Classification used by decompose-equality stability analysis. `Standard` covers ordinary user
    /// operators.
    pub(crate) class: SymbolClass,
}

/// Which side a one-sided identity collapses on (`left id:` / `right id:`). Two-sided identities use
/// the symbol's ordinary identity field.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum IdentitySide {
    Left,
    Right,
}

/// Classification consulted by decompose equality. A symbol is equationally stable only when it is
/// `Standard`, has no special hook or identity, and has no equations indexed at it.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub enum SymbolClass {
    #[default]
    Standard,
    /// A command-subject variable represented by a fresh nullary constant. It is never stable or
    /// ground. `rank` is the interned name-token index used to order same-sort variables.
    Variable { rank: u32 },
    /// The per-sort symbol backing genuine unification-variable leaves. It gives each variable a
    /// total symbol and range sort but never heads a `Free` node. It is never stable or ground.
    SortVariable,
    /// A built-in marker class whose identity hook attaches no [`SpecialOp`], including successor,
    /// literal-family, Boolean, and object-constructor symbols. Marker symbols are not equationally
    /// stable.
    Marker,
    /// An SMT numeric-literal pseudo-constructor. It uses the atomic NA representation rather than an
    /// inert ordinary constant; the frontend gives it integer/rational literal productions.
    SmtNumber,
}

/// Object-system roles set by the `config`, `obj`/`object`, `msg`/`message`, and `portal`
/// operator attributes. Roles are independent bits. The `erewrite` scheduler partitions the
/// configuration using these flags rather than the `Object` and `Msg` sorts.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub(crate) struct OoFlags {
    /// `config` — the configuration multiset constructor.
    pub(crate) config: bool,
    /// `obj`/`object` — the object constructor (`<_:_|_>`).
    pub(crate) object: bool,
    /// `msg`/`message` — a message operator.
    pub(crate) message: bool,
    /// `portal` — the external-IO portal (`<>`).
    pub(crate) portal: bool,
}

impl Symbol {
    /// Whether argument position `arg` (0-based) is frozen, preventing rule rewrites below it.
    /// See [`Symbol::frozen`].
    pub(crate) fn is_frozen_arg(&self, arg: usize) -> bool {
        match &self.frozen {
            None => false,
            Some(v) if v.is_empty() => true, // `[frozen]` = every argument
            Some(v) => v.contains(&(arg as u32)),
        }
    }

    pub fn is_smt_number(&self) -> bool {
        self.class == SymbolClass::SmtNumber
    }
}

/// Symbols attached to the model-checker hook. Temporal connectives share one formula-descent
/// contract; the remaining hooks construct satisfaction tests and lasso results.
#[derive(Debug, Clone)]
pub struct ModelCheckerHooks {
    pub temporal: crate::ltl::TemporalHooks,
    pub satisfies_symbol: SymbolId,
    pub qid_symbol: SymbolId,
    pub unlabeled_symbol: SymbolId,
    pub deadlock_symbol: SymbolId,
    pub transition_symbol: SymbolId,
    pub transition_list_symbol: SymbolId,
    pub nil_transition_list_symbol: SymbolId,
    pub counterexample_symbol: SymbolId,
    pub true_term: SymbolId,
}

/// Hooks for SAT solving. Temporal hooks recognize negative-normal-form formulae; the remainder build
/// `model(lead-in, cycle)` or the configured false result.
#[derive(Debug, Clone)]
pub struct SatSolverHooks {
    pub temporal: crate::ltl::TemporalHooks,
    pub formula_list_symbol: SymbolId,
    pub nil_formula_list_symbol: SymbolId,
    pub model_symbol: SymbolId,
    pub false_term: SymbolId,
}

/// A built-in operator's typed reduction hook. The frontend resolves `term-hook` and `op-hook`
/// references to [`SymbolId`]s at module-build time; programmatic clients can attach the same hooks
/// directly.
#[derive(Debug, Clone)]
pub enum SpecialOp {
    /// Host-provided pure strict reducer resolved through the signature's immutable catalog.
    HostFunction(crate::host::HostBindingId),
    /// `_==_` / `_=/=_`: reduce both arguments, compare them structurally, and return the configured
    /// equality or inequality constant.
    Equality { eq: SymbolId, neq: SymbolId },
    /// Initial-model equality `_.=._`. Symbolic arguments decompose over equationally stable
    /// constructors into smaller conjunctions or disjunctions; provably distinct tops yield false,
    /// and undecidable cases remain unreduced. `siblings[k]` is the per-kind polymorphic instance.
    DecomposeEquality {
        eq: SymbolId,
        neq: SymbolId,
        conj: Option<SymbolId>,
        disj: Option<SymbolId>,
        siblings: std::rc::Rc<[Option<SymbolId>]>,
    },
    /// For `if_then_else_fi`, reduce the condition and select the branch whose `tests` position matches.
    /// The selected branch remains unreduced; dead branches are skipped. If no test matches, every
    /// branch is normalized before user equations are tried on the rebuilt conditional.
    Branch { tests: Vec<SymbolId> },
    /// `_+_` / `_*_` / `gcd` / `lcm` / `min` / `max` / `_xor_` / `_&_` / `_|_`: fold the
    /// **numeric** operands of an ACU multiset, respecting multiplicity, then rebuild from the result
    /// number and any non-numeric residue operands.
    AcuNumberOp { op: NumOp, nat: NatHooks },
    /// `_quo_` / `_rem_` / `_^_` / `_<<_` / `_>>_` / `_<_` / `_<=_` / `_>_` / `_>=_` /
    /// `_divides_`: evaluate a free operator over numeric arguments. Relational operations return a Bool;
    /// arithmetic operations build a Nat or Int according to `nat.minus`. Non-numeric arguments, zero
    /// divisors, negative exponents and shift counts, unrepresentable results, and negative results
    /// without a minus hook fall through.
    NumberOp {
        op: NumOp,
        nat: NatHooks,
        bool_: Option<BoolHooks>,
    },
    /// `sd`: a commutative binary numeric operation computing symmetric difference
    /// `sd(m, n) = |m − n|`. It returns a Nat; a non-numeric argument falls through to user
    /// equations.
    CuiNumberOp { op: NumOp, nat: NatHooks },
    /// `-_`: integer negation. `-(s^n(0))` is already canonical; `-(-x)` reduces to `x`, and `-0`
    /// reduces to `0`. `nat.minus` identifies this operator.
    Minus { nat: NatHooks },
    /// `_+_` (concat) / `length` / `substr` / `ascii` / `char` / `find` / `rfind` /
    /// `upperCase` / `lowerCase` / comparisons over strings. These operate on `NodeTerm::Na`
    /// string values. `str_sym` builds string and character results; `nat`, `bool_`, and
    /// `not_found` provide operation-specific result hooks.
    StringOp {
        op: StrOp,
        str_sym: SymbolId,
        nat: Option<NatHooks>,
        bool_: Option<BoolHooks>,
        not_found: Option<SymbolId>,
    },
    /// Float arithmetic, functions, and comparisons over `NodeTerm::Na` `f64` values. `float_sym`
    /// builds float results; `bool_` provides comparison results.
    FloatOp {
        op: FltOp,
        float_sym: SymbolId,
        bool_: Option<BoolHooks>,
    },
    /// `random : Nat -> Nat`: the `n`th 32-bit output of MT19937 (Mersenne Twister) seeded with
    /// zero, making the operation a deterministic pure function of `n`.
    Random { nat: NatHooks },
    /// `counter : -> [Nat]`: a stateful rule-special that is inert under `reduce`. Each
    /// `rewrite`/`frewrite` step at a counter redex yields that operator's next natural, starting at
    /// zero and resetting for each top-level rewriting command. Every operator carrying this special
    /// has its own sequence. The rewrite traversal handles it directly.
    Counter { nat: NatHooks },
    /// `string : Qid -> String` / `qid : String ~> Qid`: convert between a quoted identifier and
    /// its text. `qid_sym` and `str_sym` build the respective atomic results.
    QidOp {
        op: QidOp,
        qid_sym: SymbolId,
        str_sym: SymbolId,
    },
    /// Cross-type coercions from the CONVERSION module (`float`, `rat`, `string`, and `decFloat`).
    /// Each `op` uses only the hooks it needs: `float_sym` builds floats, `str_sym` strings, `nat`
    /// numerals, `division` rational applications, and `dec_float` decomposition triples.
    Conversion {
        op: ConvOp,
        float_sym: Option<SymbolId>,
        str_sym: Option<SymbolId>,
        nat: Option<NatHooks>,
        division: Option<SymbolId>,
        dec_float: Option<SymbolId>,
    },
    /// Canonicalize `_/_` to lowest terms, returning an integer when the denominator becomes one.
    Division { nat: NatHooks },

    /// Native LTL model checking over the module's ordinary rewrite state graph.
    ModelCheck {
        hooks: std::rc::Rc<ModelCheckerHooks>,
    },
    /// Native LTL satisfiability solving over the generalized Büchi automaton.
    SatSolve { hooks: std::rc::Rc<SatSolverHooks> },
    /// Solver-language operator consumed by the SMT translator and inert under ordinary reduction.
    Smt { op: SmtOp },
    /// An upper-layer META-LEVEL or LEXICAL descent hook. The frontend resolves hook symbols and the
    /// host layer performs the operation. Unknown hook codes use [`MetaOp::Unknown`].
    Meta {
        op: MetaOp,
        hooks: std::rc::Rc<MetaHooks>,
    },
    /// The local synchronous meta-interpreter manager. The kernel only recognizes the external target;
    /// request decoding and child-session ownership stay behind `LocalInterpreterManager` in the host
    /// layer.
    InterpreterManager,
    /// A standard-stream external-object manager: the zero-arity `Oid` constant
    /// `stdin`, `stdout`, or `stderr`. In `erewrite`'s EXTERNAL mode, with a `<>` portal in the soup,
    /// `write(self, me, str)` emits to the selected output stream and replies `wrote(me, self)`;
    /// `getLine(self, me, prompt)` reads the scripted input buffer and replies `gotLine(me, self, line)`.
    /// Hook symbols are resolved from the operator's `op-hook` list.
    StreamManager {
        stream: StdStream,
        /// The `<Strings>` constructor hook builds the `gotLine` payload from a read line.
        string_sym: Option<SymbolId>,
        write_msg: Option<SymbolId>,
        wrote_msg: Option<SymbolId>,
        get_line_msg: Option<SymbolId>,
        got_line_msg: Option<SymbolId>,
    },
}

/// The standard stream driven by [`SpecialOp::StreamManager`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum StdStream {
    Stdin,
    Stdout,
    Stderr,
}

/// Upper-layer META-LEVEL and LEXICAL operations dispatched through [`SpecialOp::Meta`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MetaOp {
    Reduce,
    Normalize,
    Rewrite,
    Frewrite,
    Apply,
    Xapply,
    Match,
    Xmatch,
    Search,
    SearchPath,
    Check,
    SmtSearch,
    /// Native variant satisfiability over a reflected constructor theory with the finite variant
    /// property and order-sorted compactness.
    VariantSat {
        validity: bool,
        explicit_sorts: bool,
    },
    /// Advisory syntactic eligibility check for the variant-satisfiability procedure.
    VariantSatWellFormed,
    SortLeq,
    SameKind,
    LesserSorts,
    GlbSorts,
    LeastSort,
    CompleteName,
    GetKind,
    GetKinds,
    MaximalSorts,
    MinimalSorts,
    MaximalAritySet,
    Parse,
    PrettyPrint,
    PrintToString,
    WellFormedModule,
    WellFormedTerm,
    WellFormedSubstitution,
    UpModule,
    UpImports,
    UpSorts,
    UpSubsortDecls,
    UpOpDecls,
    UpMbs,
    UpEqs,
    UpRls,
    UpStratDecls,
    UpSds,
    UpView,
    UpTerm,
    DownTerm,
    /// LEXICAL's `tokenize : String -> QidList` hook. It uses the frontend scanner through the descent
    /// seam because strings are byte-valued kernel nodes while token interning lives above `tnk-core`.
    Tokenize,
    /// LEXICAL's `printTokens : QidList -> String` hook.
    PrintTokens,
    /// Order-sorted unification descent. `disjoint` splits the solution across the two sides'
    /// variables (`UnificationTriple`); `irredundant` filters to the most-general unifiers.
    Unify {
        disjoint: bool,
        irredundant: bool,
    },
    /// Incremental folding-variant generation. `irredundant` selects the final survivor set;
    /// `nat_family` selects `Nat` fresh-variable indices instead of Qid family names.
    GetVariant {
        irredundant: bool,
        nat_family: bool,
    },
    /// Variant unification. `disjoint` splits lhs/rhs bindings; `nat_family` selects `Nat` indices.
    VariantUnify {
        disjoint: bool,
        nat_family: bool,
    },
    /// Complete-set variant matching (the current Qid-family signature).
    VariantMatch,
    /// `metaNarrow`; `state_only` identifies the separately recognized, inert `metaNarrow2`.
    Narrow {
        state_only: bool,
    },
    /// One-step variant narrowing with optional irreducibility constraints.
    NarrowingApply,
    /// Variant-based narrowing search, with either a solution or a full path result.
    NarrowingSearch {
        path: bool,
    },
    /// Strategy rewrite requested by the local META-INTERPRETER transport.
    Srewrite {
        depth_first: bool,
    },
    /// Unrecognized hook code; evaluation remains inert.
    Unknown,
}

/// The meta-representation symbols a [`SpecialOp::Meta`] descent function needs, resolved from its
/// operator's `op-hook`/`term-hook` list at module-build time and keyed by hook purpose. The down/up
/// maps use these ids to decode and construct meta-terms.
#[derive(Debug, Clone, Default)]
pub struct MetaHooks {
    pub ops: std::collections::HashMap<String, SymbolId>,
    pub terms: std::collections::HashMap<String, SymbolId>,
}

/// An IEEE `f64` operation performed by [`SpecialOp::FloatOp`]: arithmetic, unary functions
/// (`floor`, `ceiling`, `exp`, `log`, `sqrt`, and trigonometry), `rem`, exponentiation, min/max,
/// or comparison. Float/rational conversions use [`SpecialOp::Conversion`] instead.
#[derive(Debug, Clone, Copy)]
pub enum FltOp {
    // Unary.
    Neg,
    Abs,
    Sqrt,
    Floor,
    Ceiling,
    Exp,
    Log,
    Sin,
    Cos,
    Tan,
    Asin,
    Acos,
    Atan,
    // Binary arithmetic.
    Add,
    Sub,
    Mul,
    Div,
    Rem,
    Pow,
    Min,
    Max,
    Atan2,
    // Binary comparison → Bool.
    Lt,
    Le,
    Gt,
    Ge,
}

/// A CONVERSION coercion a [`SpecialOp::Conversion`] performs (distinguished by code + arity at build
/// time, since `float`/`rat`/`string` are overloaded across argument types).
#[derive(Debug, Clone, Copy)]
pub enum ConvOp {
    /// `float : Rat -> Float` — the nearest double to a rational.
    RatToFloat,
    /// `rat : FiniteFloat -> Rat` — the exact rational value of a double.
    FloatToRat,
    /// `string : Rat NzNat -> String` — a rational rendered in a base.
    RatToString,
    /// `rat : String NzNat -> Rat` — a rational parsed from a base.
    StringToRat,
    /// `string : Float -> String` — a float's canonical decimal string.
    FloatToString,
    /// `float : String -> Float` — a float parsed from a string.
    StringToFloat,
    /// `decFloat : Float Nat -> DecFloat` — a float decomposed into `< sign·int, "digits", exp >`.
    DecFloat,
}

/// A quoted-identifier conversion performed by [`SpecialOp::QidOp`]: text extraction or parsing.
#[derive(Debug, Clone, Copy)]
pub enum QidOp {
    /// `string : Qid -> String` — the identifier text (without the leading quote).
    String,
    /// `qid : String ~> Qid` — a quoted identifier from text (partial: a single-token identifier).
    Qid,
}

/// A string operation performed by [`SpecialOp::StringOp`]: concatenation, length, slicing,
/// character conversion, search, case mapping, character classes, trimming, or comparison.
#[derive(Debug, Clone, Copy)]
pub enum StrOp {
    Concat,
    Length,
    Substr,
    /// `ascii : Char -> Nat` — the code of a single-character string.
    Ascii,
    /// `char : Nat ~> Char` — the one-character string for a code (partial: a valid scalar value).
    Char,
    /// `find : String String Nat -> FindResult` — first index of the pattern at/after the start.
    Find,
    /// `rfind : String String Nat -> FindResult` — last index of the pattern at/before the start.
    Rfind,
    UpperCase,
    LowerCase,
    /// A character-class predicate `isX : Char -> Bool` (STRING-OPS — C `iscntrl`/`isalpha`/…).
    IsClass(CharClass),
    /// `startsWith` / `endsWith : String String -> Bool`.
    StartsWith,
    EndsWith,
    /// `trimStart` / `trimEnd` / `trim : String -> String` (strip C-whitespace).
    TrimStart,
    TrimEnd,
    Trim,
    Lt,
    Le,
    Gt,
    Ge,
}

/// A C `ctype` character class (STRING-OPS's `isControl`/`isAlphabetic`/… predicates), tested per byte in
/// the C locale (a non-ASCII char is in no class).
#[derive(Debug, Clone, Copy)]
pub enum CharClass {
    Control,
    Printable,
    Space,
    Blank,
    Graphic,
    Punct,
    Alnum,
    Alpha,
    Upper,
    Lower,
    Digit,
    XDigit,
}

/// The `op-hook succSymbol` (an `iter` successor) and its `Zero` constant (the successor's `zeroTerm`),
/// plus the optional `op-hook minusSymbol` (`-_`). The numeral bridge uses these to recognise and build
/// `0` / `s^n(0)` / `-(s^n(0))`. `minus` is `None` for `NAT` (no negatives — a negative result falls
/// through to user equations) and `Some` for `INT`.
#[derive(Debug, Clone, Copy)]
pub struct NatHooks {
    pub succ: SymbolId,
    pub zero: SymbolId,
    pub minus: Option<SymbolId>,
}

/// A relational number op's `term-hook trueTerm`/`falseTerm` result constants.
#[derive(Debug, Clone, Copy)]
pub struct BoolHooks {
    pub true_: SymbolId,
    pub false_: SymbolId,
}

/// Arithmetic or relational behavior of a numeric built-in. Arithmetic variants return a Nat or Int
/// according to the attached [`NatHooks`]; relational variants return Bool.
#[derive(Debug, Clone, Copy)]
pub enum NumOp {
    // ACU (fold the multiset) — `_+_` `_*_` `gcd` `lcm` `min` `max`.
    Add,
    Mul,
    Gcd,
    Lcm,
    Min,
    Max,
    // ACU **bitwise** (fold the multiset, multiplicity-aware) — `_xor_` `_&_` `_|_`. `xor` cancels in
    // pairs (an element folded an even number of times contributes nothing); `&`/`|` are idempotent.
    Xor,
    And,
    Or,
    // CUI (commutative 2-arg) — `sd` (symmetric difference `|m − n|`).
    Sd,
    // free arithmetic → Nat/Int — `_-_` (INT) `_quo_` `_rem_` `_^_` `modExp` `_>>_` `_<<_` `abs` `~`.
    Sub,
    Quo,
    Rem,
    Pow,
    ModExp,
    Shr,
    Shl,
    /// `abs : Int -> Nat` — magnitude. Free unary.
    Abs,
    /// `~_ : Int -> Int` — bitwise complement (`~x = -(x+1)`, two's complement). Free unary.
    BitNot,
    // free relational → Bool — `_<_` `_<=_` `_>_` `_>=_` `_divides_`.
    Lt,
    Le,
    Gt,
    Ge,
    Divides,
}

impl Symbol {
    pub fn name(&self) -> &str {
        &self.name
    }
    pub fn arity(&self) -> usize {
        self.decls[0].domain.len()
    }
    pub(crate) fn is_commutative(&self) -> bool {
        self.axioms.comm
    }

    /// The operator's declarations (≥ 1); least-sort resolution walks them in declaration order.
    pub(crate) fn decls(&self) -> &[OpDeclaration] {
        &self.decls
    }

    pub(crate) fn has_inconsistent_constructor_axioms(&self) -> bool {
        self.inconsistent_constructor_axioms
    }

    /// The operator's equational theory, classified from its [`Axioms`]. Associative-commutative
    /// operators use [`Acu`](Theory::Acu), associative-only operators use [`Au`](Theory::Au), and
    /// non-associative operators with commutativity, identity, or idempotence use
    /// [`Cui`](Theory::Cui). Operators with none of those axioms use [`Free`](Theory::Free).
    /// Non-commutative CUI operators preserve positional argument order; only their collapse axioms
    /// apply.
    pub(crate) fn theory(&self) -> Theory {
        if self.axioms.iter {
            return Theory::S; // `iter` is mutually exclusive with assoc/comm (checked at registration)
        }
        match (self.axioms.assoc, self.axioms.comm) {
            (true, true) => Theory::Acu,
            (true, false) => Theory::Au,
            (false, true) => Theory::Cui,
            (false, false) => {
                if self.identity.is_some() || self.axioms.idem {
                    Theory::Cui
                } else {
                    Theory::Free
                }
            }
        }
    }

    /// The signature-owned identity term, if this operator was declared with `id:`.
    pub(crate) fn identity(&self) -> Option<IdentityId> {
        self.identity
    }

    /// The identity that collapses on the **left** (`f(e, x) = x).
    pub(crate) fn left_identity(&self) -> Option<IdentityId> {
        self.identity.or(match self.one_sided_id {
            Some((IdentitySide::Left, id)) => Some(id),
            _ => None,
        })
    }

    /// The identity that collapses on the **right** (`f(x, e) = x).
    pub(crate) fn right_identity(&self) -> Option<IdentityId> {
        self.identity.or(match self.one_sided_id {
            Some((IdentitySide::Right, id)) => Some(id),
            _ => None,
        })
    }

    /// Whether this operator has an identity on exactly one side. Associative one-sided identity
    /// unification is unsupported.
    pub(crate) fn one_sided_identity(&self) -> bool {
        self.one_sided_id.is_some()
    }

    /// The operator's built-in reduction rule, if any.
    pub(crate) fn special(&self) -> Option<&SpecialOp> {
        self.special.as_ref()
    }
    /// Whether this symbol is an upper-layer META-LEVEL/LEXICAL descent operation.
    pub fn is_meta_operation(&self) -> bool {
        matches!(self.special, Some(SpecialOp::Meta { .. }))
    }
    pub(crate) fn class(&self) -> SymbolClass {
        self.class
    }

    /// Whether every declaration of this operator is a constructor (`[ctor]`). This does not affect
    /// reduction; constructor-sensitive symbolic analyses consume the metadata.
    pub(crate) fn is_constructor(&self) -> bool {
        self.decls.iter().all(|d| d.ctor)
    }
}
