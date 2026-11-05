//! Surface AST produced before per-module mixfix parsing. Term-carrying identities, statements,
//! conditions, and commands remain raw token bubbles.

use crate::lex::Token;

/// Severity carried by a frontend/build diagnostic. Rendering belongs to the Session layer.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum DiagnosticSeverity {
    Warning,
    Error,
}

/// An owned, source-ordered diagnostic produced while parsing or building a module.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Diagnostic {
    pub severity: DiagnosticSeverity,
    pub module: Option<String>,
    pub line: Option<u32>,
    pub subject: Option<String>,
    pub message: String,
}

impl Diagnostic {
    pub fn warning(
        module: impl Into<String>,
        line: Option<u32>,
        subject: impl Into<String>,
        message: impl Into<String>,
    ) -> Self {
        Self {
            severity: DiagnosticSeverity::Warning,
            module: Some(module.into()),
            line,
            subject: Some(subject.into()),
            message: message.into(),
        }
    }
}

/// Parsed module skeleton. `Clone` supports import-closure flattening and module transformations.
#[derive(Debug, Clone)]
pub struct PreModule {
    pub name: String,
    /// Line of the module-opening keyword when the declaration came from source text.
    pub source_line: Option<u32>,
    /// Nonfatal source diagnostics retained until the Session renders them.
    pub diagnostics: Vec<Diagnostic>,
    /// Functional (`fmod`/`fth`) or system (`mod`/`th`). A system module/theory may declare rules
    /// (`rl`/`crl`); a functional one may not. This is the *rule-gating* axis only.
    pub kind: ModuleKind,
    /// Whether this is a theory rather than a module. Orthogonal to functional/system kind. Theory
    /// statements are specifications and proof obligations rather than executable statements.
    pub is_theory: bool,
    /// Formal parameters `{X :: T, …}`. Each parameter imports a renamed copy of its theory under the
    /// `X$` prefix; empty for an ordinary module. The stored module name remains the bare base.
    pub params: Vec<Parameter>,
    /// Imported modules (`protecting`/`extending`/`including <module-expr> .`), in declaration order.
    pub imports: Vec<Import>,
    pub sorts: Vec<String>,
    /// Each subsort chain `A B < C < D` as ordered groups (every group is below the next).
    pub subsorts: Vec<Vec<Vec<String>>>,
    pub ops: Vec<OpDecl>,
    pub vars: Vec<VarDecl>,
    pub statements: Vec<Statement>,
    /// `true` for a **strategy module/theory** (`smod`/`ssth`) — a system module that additionally permits
    /// strategy declarations/definitions ([`strat_decls`](Self::strat_decls)/[`strat_defs`](Self::strat_defs)).
    /// Orthogonal to [`kind`](Self::kind) (a strategy module is a system module). Plain `mod`/`fmod` = `false`.
    pub is_strategy: bool,
    /// `true` for an object-oriented module or theory (`omod`/`oth`). Its class, subclass, and message
    /// declarations are desugared to ordinary signature entries, and `CONFIGURATION` is imported
    /// implicitly. During statement loading, object patterns are completed with an AttributeSet variable
    /// and class constants are generalized to class-sorted variables; see
    /// [`completes_object_patterns`](Self::completes_object_patterns).
    pub is_object: bool,
    /// Build-time statement provenance recorded by flattening, parallel to
    /// [`statements`](Self::statements): whether each statement was declared by an object module or
    /// theory, directly or through a renamed, instantiated, or parameter-copy donation. Empty for a module
    /// that was not flattened, whose statements are all its own. Like statement homes, this is not
    /// reflected statement metadata.
    pub object_statements: Vec<bool>,
    /// Strategy declarations and definitions; empty for a non-strategy module.
    pub strat_decls: Vec<StratDecl>,
    /// `sd`/`csd` definitions; empty for a non-strategy module.
    pub strat_defs: Vec<StratDef>,
}

impl PreModule {
    /// Whether statement loading completes the object patterns of `statements[index]`: every statement
    /// of an object module or theory, the statements it imports included, and every statement that an
    /// object module or theory donates to a non-object importer.
    pub fn completes_object_patterns(&self, index: usize) -> bool {
        self.is_object || self.object_statements.get(index).copied().unwrap_or(false)
    }
}

/// A formal module/view parameter `X :: T`: parameter name and its bounding theory.
#[derive(Debug, Clone)]
pub struct Parameter {
    pub name: String,
    pub theory: String,
}

/// Whether a module/theory is functional (`fmod`/`fth` — equations + memberships only) or a system one
/// (`mod`/`th` — may additionally declare rules). The kind gates rule statements (`rl`/`crl`). Whether it
/// is a *theory* is the orthogonal [`PreModule::is_theory`] flag.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ModuleKind {
    Functional,
    System,
}

/// An import declaration. Flattening imports the same declarations for all three modes; the mode is
/// retained for reflection, while no-junk and no-confusion obligations are not enforced.
#[derive(Debug, Clone)]
pub struct Import {
    pub mode: ImportMode,
    pub expr: ModuleExpr,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ImportMode {
    Protecting,
    Extending,
    Including,
}

/// A module expression: named module, sum, renaming, or parameterized instantiation with one module/view
/// argument per formal parameter.
#[derive(Debug, Clone)]
pub enum ModuleExpr {
    Named(String),
    Sum(Box<ModuleExpr>, Box<ModuleExpr>),
    Rename(Box<ModuleExpr>, Vec<RenameItem>),
    /// Instantiate a parameterized module with view names, nested view/module instantiations, or enclosing
    /// parameter names classified contextually during flattening.
    Instantiation(Box<ModuleExpr>, Vec<ModuleExpr>),
}

/// One mapping inside a renaming `* (…)`. Operator renaming uses canonical mixfix names (`_,_ to _;_`).
/// Optional `[ … ]` attributes override the target declaration, for example `[prec 43]`. A
/// signature-qualified rename `op f : A B -> C to g` stores the selecting domain and range in
/// [`dom_range`](RenameItem::Op::dom_range), so only the overload family that profile names is renamed.
/// A `label l to m` item renames a statement label.
// Renames are short-lived parser ASTs; retaining attributes inline avoids one allocation per op mapping.
#[derive(Debug, Clone)]
#[allow(clippy::large_enum_variant)]
pub enum RenameItem {
    Sort {
        from: String,
        to: String,
    },
    Op {
        from: String,
        to: String,
        /// `Some((domain, range))` for a disambiguated rename `op f : A B -> C to g` — selects the overload
        /// family of `from` that this declared profile belongs to (the same arity, every sort in the same
        /// kind); `None` renames every overload of the name.
        dom_range: Option<(Vec<String>, String)>,
        attrs: Attrs,
    },
    /// `label l to m` — rename a statement label (rule/eq/mb label) `l` to `m`.
    Label {
        from: String,
        to: String,
    },
}

/// A view maps a source theory into a target module or theory, providing sort and operator mappings for
/// module instantiation. Parameterized views retain formal parameters and may target a structured module
/// expression; instantiating the view substitutes arguments through its target and maps.
#[derive(Debug, Clone)]
pub struct ViewDecl {
    pub name: String,
    /// Line of the `view` keyword when the declaration came from source text.
    pub source_line: Option<u32>,
    /// Formal parameters of a parameterized view. Instantiation substitutes their arguments into the
    /// target expression and all sort/operator maps.
    pub params: Vec<Parameter>,
    pub from: ModuleExpr,
    pub to: ModuleExpr,
    /// Variables declared in the view body. They scope operator-to-term mappings but are not part of the
    /// reflected `View` value.
    pub vars: Vec<VarDecl>,
    /// `sort A to B .` — map a (theory-declared) sort `A` to a sort `B` of the target. Unmapped theory
    /// sorts default to identity (must exist in the target).
    pub sort_maps: Vec<(String, String)>,
    /// `op … to … .` mappings.
    pub op_maps: Vec<OpMap>,
}

/// One operator mapping in a view: `op f to g .` (to another operator) or `op f to term t .` (to a target
/// term, e.g. `op 0 to term 0.0`). A disambiguated source `op f : A -> B to …` carries its domain/range
/// profile so one overload can be mapped without affecting another.
#[derive(Debug, Clone)]
pub enum OpMap {
    Op {
        from: Vec<Token>,
        to: Vec<Token>,
        dom_range: Option<(Vec<String>, String)>,
    },
    Term {
        from: Vec<Token>,
        to: Vec<Token>,
        dom_range: Option<(Vec<String>, String)>,
    },
}

/// One operator declaration `op <name> : <domain> -> <range> [<attrs>] .` (or `ops …` expanded to one
/// `OpDecl` per name).
#[derive(Debug, Clone)]
pub struct OpDecl {
    /// The mixfix name as raw tokens (`[_+_]`, `[s_]`, `[<_, ,, _>]`, `[gcd]`).
    pub name: Vec<Token>,
    pub domain: Vec<String>,
    pub range: String,
    /// Whether the declaration used the **partial** arrow `~>` (`op _/_ : Float Float ~> Float`).
    /// Signature construction lifts every domain and range sort to its kind, allowing kind-level
    /// arguments and assigning an unreduced application to the result kind.
    pub partial: bool,
    pub attrs: Attrs,
}

#[derive(Debug, Clone)]
pub struct VarDecl {
    pub names: Vec<String>,
    pub sort: String,
}

/// Operator attributes (`[assoc comm id: … ctor iter prec gather strat special ditto]`).
#[derive(Debug, Default, Clone)]
pub struct Attrs {
    pub assoc: bool,
    pub comm: bool,
    pub idem: bool,
    pub iter: bool,
    pub ctor: bool,
    /// `id: <term>` identity element (a token bubble).
    pub id: Option<Vec<Token>>,
    pub prec: Option<u32>,
    pub gather: Option<Vec<GatherElem>>,
    /// `strat (…)` — the raw 1-based positions (ending in `0`).
    pub strat: Option<Vec<u32>>,
    /// `frozen` / `frozen (1 2)` — `None` = not frozen; `Some([])` = all arguments frozen (`[frozen]`);
    /// `Some([1,3])` = those 1-based argument positions frozen. Rewriting does not descend into them.
    pub frozen: Option<Vec<u32>>,
    pub special: Option<SpecialSpec>,
    pub ditto: bool,
    /// `memo` — retained for an explicit unsupported-feature warning; it has no kernel semantics.
    pub memo: bool,
    /// Polymorphic argument/range positions: arguments use `1..n`, range uses `0`. Each listed position
    /// expands to the error sort of every kind; `None` is monomorphic.
    pub poly: Option<Vec<u32>>,
    /// `format (<word> …)` — one format directive word per **gap** of the operator's mixfix form (gaps =
    /// tokens + 1: before each token/hole, plus a trailing one). Each word is a directive string (`d`
    /// default, `s` space, `t` tab, `n` newline, `i` indent, `+`/`-` indent level — e.g. `n++i`, `ni`).
    /// The pretty-printer consumes these directives; `None` selects default spacing.
    pub format: Option<Vec<String>>,
    /// `config` / `configuration` — marks the configuration-multiset constructor used by `erewrite`
    /// object/message partitioning.
    pub config: bool,
    /// `obj` / `object` — the object constructor (`<_:_|_>`).
    pub object: bool,
    /// `msg` / `message` — a message operator.
    pub message: bool,
    /// `portal` — the external-IO portal (`<>`).
    pub portal: bool,
    /// `pconst` — a **parameter constant** of a theory (`op c : -> Elt [pconst]`). In a parameterized
    /// module `P{X :: T}` such a constant is referred to as `X$c` (the parameter prefix, like a parameter
    /// sort `X$s`); instantiating `P{V}` maps `X$c` through `V`'s op map for `c`.
    pub pconst: bool,
    /// Sides on which an identity collapses. Meaningful only when [`id`](Self::id) is present.
    pub id_side: IdSide,
}

/// Identity-collapse sides for associative operators.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum IdSide {
    /// Collapse on either side.
    #[default]
    Both,
    /// `left id:` — only a leading identity argument collapses.
    Left,
    /// `right id:` — only a trailing identity argument collapses.
    Right,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum GatherElem {
    /// `E` — argument precedence bound = the operator's prec.
    Strong,
    /// `e` — bound = prec − 1.
    Weak,
    /// `&` — no bound (`ANY`).
    Any,
}

/// A `special (id-hook … op-hook … term-hook …)` directive, resolved to a typed kernel hook while the
/// signature is built.
#[derive(Debug, Default, Clone)]
pub struct SpecialSpec {
    /// `(class_name, data_tokens)` — e.g. `("ACU_NumberOpSymbol", ["+"])`, `("BranchSymbol", [])`.
    pub id_hook: Option<(String, Vec<String>)>,
    /// `op-hook <purpose> (<op-signature>)` — e.g. `("succSymbol", ["s_", ":", "Nat", "~>", "NzNat"])`.
    pub op_hooks: Vec<(String, Vec<Token>)>,
    /// `term-hook <purpose> (<term>)` — e.g. `("zeroTerm", ["0"])`, `("1", ["true"])`.
    pub term_hooks: Vec<(String, Vec<Token>)>,
}

/// A statement: equation, membership axiom, or rule. Term parts remain raw bubbles until module loading.
/// The `[nonexec]` statement attribute marks an axiom that is *not* applied during
/// reduction/rewriting — a proof obligation (theory axioms are all `[nonexec]`, but a module statement may
/// be too). Such statements parse and carry through flattening, but are skipped when loading the engine.
#[derive(Debug, Clone)]
pub enum Statement {
    Eq {
        lhs: Vec<Token>,
        rhs: Vec<Token>,
        cond: Option<Vec<Token>>,
        owise: bool,
        variant: bool,
        nonexec: bool,
        label: Option<String>,
    },
    Mb {
        lhs: Vec<Token>,
        sort: Vec<Token>,
        cond: Option<Vec<Token>>,
        nonexec: bool,
        label: Option<String>,
    },
    /// A rule condition can contain a rewrite fragment `t => p` in addition to equation-style fragments.
    Rule {
        label: Option<String>,
        lhs: Vec<Token>,
        rhs: Vec<Token>,
        cond: Option<Vec<Token>>,
        nonexec: bool,
        /// A rule selected by variant-based narrowing. Independent of `nonexec`: nonexec narrowing
        /// rules participate in symbolic narrowing but never ordinary rewriting.
        narrowing: bool,
    },
}

/// A strategy declaration names a strategy, its argument sorts, and the subject sort after `@`.
/// `strats` expands to one declaration per name.
#[derive(Debug, Clone)]
pub struct StratDecl {
    pub name: String,
    pub domain: Vec<String>,
    pub subject: String,
    /// Stable donation identity assigned by the module flattener. Declarations copied from the same
    /// source module share an origin; independently imported declarations do not.
    pub origin: Option<String>,
    /// Position in the source module's strategy-declaration list; paired with `origin` for diamond dedup.
    pub source_index: Option<usize>,
    /// Source module whose grammar owns this declaration. Cleared by source-transforming module
    /// expressions (renaming/instantiation), whose tokens are rewritten for the destination grammar.
    pub home: Option<String>,
}

/// A **strategy definition** `sd name(params) := body .` / `csd … := body if cond .`. The call-pattern
/// arguments (`params`) and any condition are raw token bubbles; the `body` strategy structure is parsed
/// now. An unconditional definition's parameters and body term bubbles are parsed against its home grammar
/// whenever the strategy program is compiled: for each strategy command, and once per module build to report
/// a definition that does not resolve.
#[derive(Debug, Clone)]
pub struct StratDef {
    pub name: String,
    pub params: Vec<Vec<Token>>,
    pub body: StratExpr,
    pub cond: Option<Vec<Token>>,
    /// Stable donation identity assigned by the module flattener (parallel to [`StratDecl::origin`]).
    pub origin: Option<String>,
    /// Position in the source module's strategy-definition list; paired with `origin` for diamond dedup.
    pub source_index: Option<usize>,
    /// Source module whose grammar owns the raw parameter/body term bubbles.
    pub home: Option<String>,
    /// Source line of the `sd`/`csd` keyword, for diagnostics; `None` for a reflected definition.
    pub line: Option<u32>,
}

/// A test/matchrew matching mode: `match` (top), `xmatch` (with extension), `amatch` (anywhere).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TestKind {
    Match,
    XMatch,
    AMatch,
}

/// A **strategy expression** combinator tree. Term-carrying parts (a rule label's initial
/// substitution / its rewrite-condition substrategies, a test/matchrew pattern + condition, a call's
/// arguments) are raw token bubbles, parsed against the module grammar at execution time. The derived forms
/// `try`/`not`/`test`/`or-else` keep their surface spelling ([`StratExpr::Sugar`]) for the command echo
/// and desugar to [`StratExpr::Branch`] at resolution.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum StratSugar {
    Try,
    NotS,
    TestS,
    OrElse,
}

#[derive(Debug, Clone)]
pub enum StratExpr {
    /// `idle` — pass the subject through unchanged (one solution).
    Idle,
    /// `fail` — no solution.
    Fail,
    /// `all` — apply any rule once, anywhere (every one-step rewrite).
    All,
    /// `label[σ]{E,…}` — apply the rule(s) labelled `label`; `subst` is the optional initial substitution
    /// (`x <- t` bubbles), `substrats` the substrategies for the rule's rewrite conditions.
    Apply {
        label: String,
        subst: Vec<(Vec<Token>, Vec<Token>)>,
        substrats: Vec<StratExpr>,
    },
    /// `top(E)` — apply `E` only at the top of the subject.
    Top(Box<StratExpr>),
    /// `one(E)` — at most the first solution of `E`.
    One(Box<StratExpr>),
    /// `E ; F` — run `F` on each solution of `E`.
    Seq(Box<StratExpr>, Box<StratExpr>),
    /// `E | F` — the union of the solutions of `E` and `F`.
    Union(Box<StratExpr>, Box<StratExpr>),
    /// `E *` — zero-or-more iterations (`idle | (E ; E*)`).
    Star(Box<StratExpr>),
    /// `E +` — one-or-more iterations (`E ; E*`).
    Plus(Box<StratExpr>),
    /// `E !` — normalization: iterate `E` to a fixpoint (`E ? (E !) : idle`).
    Normalize(Box<StratExpr>),
    /// `test ? success : failure` — if `test` has ≥1 solution, run `success` on each; else `failure` on the
    /// original subject. The primitive behind `try`/`not`/`test`/`or-else`.
    Branch {
        test: Box<StratExpr>,
        success: Box<StratExpr>,
        failure: Box<StratExpr>,
    },
    /// `match P [s.t. C]` / `xmatch` / `amatch` — a test (no rewrite): succeed iff `P` matches.
    Test {
        kind: TestKind,
        pattern: Vec<Token>,
        cond: Option<Vec<Token>>,
    },
    /// `matchrew P [s.t. C] by x1 using E1, …` — match `P`, run `Eᵢ` on the subterm bound to `xᵢ`, rebuild.
    MatchRew {
        kind: TestKind,
        pattern: Vec<Token>,
        cond: Option<Vec<Token>>,
        subs: Vec<(Vec<Token>, StratExpr)>,
    },
    /// A derived branch form kept in its SURFACE spelling for the command echo — `try(α)`, `not(α)`,
    /// `test(α)`, `or-else(α, β)` — resolution desugars to the `? :` branch;
    /// the round-trip must preserve the surface form.
    Sugar {
        kind: StratSugar,
        args: Vec<StratExpr>,
    },
    /// A named strategy `s` / `s(args)`, resolved against the module's `sd`/`csd` definitions.
    Call { name: String, args: Vec<Vec<Token>> },
}

/// A top-level command covering reduction, matching, rewriting/search, strategies, SMT, variants,
/// narrowing, reflection, inspection, and session controls.
#[derive(Debug)]
pub enum Command {
    /// Reduce in an optional one-command module override without changing the current module.
    Reduce {
        module: Option<String>,
        term: Vec<Token>,
    },
    /// `check [in M :] formula .` — object-level SMT query over the given formula.
    Check {
        module: Option<String>,
        term: Vec<Token>,
    },
    Match {
        module: Option<String>,
        pattern: Vec<Token>,
        subject: Vec<Token>,
        xmatch: bool,
    },
    /// `rewrite [bound] term .` — rule-fair rewriting to a normal form (or `bound` rule applications).
    Rewrite {
        module: Option<String>,
        bound: Option<u64>,
        term: Vec<Token>,
    },
    /// Position-fair rewriting. `gas` defaults to one rule application per position per pass.
    Frewrite {
        module: Option<String>,
        bound: Option<u64>,
        gas: Option<u64>,
        term: Vec<Token>,
    },
    /// Object-message-fair rewriting of a configuration. `bound` caps config-level deliveries; `gas`
    /// controls the non-config position-fair fallback.
    ERewrite {
        module: Option<String>,
        bound: Option<u64>,
        gas: Option<u64>,
        term: Vec<Token>,
    },
    /// `search [n,m] subject =>arrow pattern [such that cond] .`: reachability search.
    /// `max_solutions` is `[n]`; `max_depth` is the second bound in `[n,m]`.
    Search {
        module: Option<String>,
        max_solutions: Option<u64>,
        max_depth: Option<u64>,
        subject: Vec<Token>,
        arrow: SearchArrow,
        pattern: Vec<Token>,
        such_that: Option<Vec<Token>>,
    },
    /// Object-level `smt-search`, with the same surface bounds and arrows as `search`.
    /// Runtime validates which arrows the configured SMT engine supports.
    SmtSearch {
        module: Option<String>,
        max_solutions: Option<u64>,
        max_depth: Option<u64>,
        subject: Vec<Token>,
        arrow: SearchArrow,
        pattern: Vec<Token>,
        such_that: Option<Vec<Token>>,
    },
    /// Order-sorted unification. `bound` limits returned unifiers; `irredundant` requests the
    /// minimal-complete-set filter; `body` retains the raw `=?`/`/\`-separated term bubble.
    Unify {
        module: Option<String>,
        bound: Option<u64>,
        irredundant: bool,
        body: Vec<Token>,
    },
    /// Folding variant generation, optionally computing only the final irredundant survivor set.
    GetVariants {
        module: Option<String>,
        bound: Option<u64>,
        irredundant: bool,
        term: Vec<Token>,
        /// Raw comma-separated terms from `such that … irreducible`.
        blockers: Vec<Token>,
    },
    /// Plain or filtered variant unification. `body` contains one or more `/\`-joined `=?` pairs.
    VariantUnify {
        module: Option<String>,
        bound: Option<u64>,
        filtered: bool,
        body: Vec<Token>,
        blockers: Vec<Token>,
    },
    /// Variant matching; variables in `subject` are treated as constants.
    VariantMatch {
        module: Option<String>,
        bound: Option<u64>,
        pattern: Vec<Token>,
        subject: Vec<Token>,
        blockers: Vec<Token>,
    },
    /// Variant-based narrowing (`vu-narrow` / `fvu-narrow`) with its two option blocks.
    Narrow {
        module: Option<String>,
        max_solutions: Option<u64>,
        max_depth: Option<u64>,
        subject: Vec<Token>,
        arrow: SearchArrow,
        goal: Vec<Token>,
        condition: Option<Vec<Token>>,
        fold: bool,
        vfold: bool,
        path: bool,
        filter: bool,
        delay: bool,
        fvu: bool,
    },
    ShowNarrowing {
        display: NarrowDisplay,
        state: Option<u64>,
    },
    /// `continue [bound] .` — resume the last `rewrite`/`frewrite`/`search` for more steps/solutions.
    Continue { bound: Option<u64> },
    /// Fair (`srewrite`) or depth-first (`dsrewrite`) strategy-controlled rewriting.
    Srewrite {
        module: Option<String>,
        depth_first: bool,
        term: Vec<Token>,
        strategy: StratExpr,
    },
}

#[derive(Debug, Clone, Copy)]
pub enum NarrowDisplay {
    MostGeneral,
    Frontier,
    Path,
    PathStates,
}

/// The reachability arrow of a `search` command (`=>1` / `=>+` / `=>*` / `=>!`).
#[derive(Debug, Clone, Copy)]
pub enum SearchArrow {
    One,
    Plus,
    Star,
    Bang,
}

/// One top-level item: a module definition, a view definition, or a command. The unit the REPL consumes
/// one at a time (a command here is *untagged* — the REPL binds it to its persistent current module).
#[derive(Debug)]
pub enum TopItem {
    Module(PreModule),
    View(ViewDecl),
    Command(Command),
}

/// The result of surface-parsing a source file: modules, view definitions, and top-level commands. Each
/// command is tagged with the index of the most recently entered module in `modules`.
#[derive(Debug, Default)]
pub struct Source {
    pub modules: Vec<PreModule>,
    pub views: Vec<ViewDecl>,
    pub commands: Vec<(usize, Command)>,
}
