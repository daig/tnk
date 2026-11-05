# The TNK Language and System Reference

**Document status:** normative for the repository at workspace version `0.1.0`
**Reference edition:** 2026-08-01
**Implementation name:** tambanokano (`tnk`)

This document specifies TNK as an independent rewriting-logic system. It defines the product's user-visible semantics and embedding contracts. Maude is part of the implementation lineage and can supply historical regression baselines, but it does not define TNK or set a compatibility target.

The key words **MUST**, **MUST NOT**, **SHOULD**, **SHOULD NOT**, and **MAY** are normative. A paragraph carrying a `TNK-*` identifier is a stable contract clause.

## 0. How to read this reference

Use [TNK Quick Reference](cheatsheet.md) for a compact recall aid: core syntax, command selection, common controls, and high-impact gotchas. Use [The TNK Book](book.md) for a guided, nonnormative introduction: mental models, progressive syntax, practical workflows, debugging guidance, extended examples, and exercises. Use this Reference for exact syntax and semantics, feature states and profiles, error and Session-state contracts, completeness and resource boundaries, and API contracts; [Appendix L](#appendix-l--normative-clause-index) provides stable clause lookup. If the Book, Quick Reference, and this Reference differ, this Reference is authoritative.

### 0.1 Normative hierarchy

**TNK-DOC-001 — Authority.** Contract clauses define intended TNK behavior. If this Reference is ambiguous, the behavior is unspecified until a clause resolves it. Rustdoc and the compiler define the exact Rust type and ownership surface of the installed release; this Reference defines its semantic behavior. `TNK-RECOVERY-001` separately records tentative current-release behavior at named invalid-input seams, including known deviations from the intended contracts.

### 0.2 Feature states

**TNK-DOC-002 — Feature classification.** Every public feature has exactly one of these states:

| State | Meaning |
|---|---|
| **Stable** | Supported behavior whose documented contract applies to every conforming implementation. |
| **Experimental** | Implemented and usable, but subject to incompatible change between releases. |
| **Optional** | Supported only with a named build feature, backend, or loaded-library capability; absence has a specified result. |
| **Unsupported** | Recognized or adjacent syntax has no supported semantics and is rejected, left inert, or warned about as specified. |

“Accepted by the parser” is not a separate state. Accepted syntax whose semantic hook is unavailable is **Unsupported**, not silently partially supported.

### 0.3 Behavior vocabulary

The feature state and the variability of one behavior are separate classifications:

- **specified** behavior is fixed by a clause and is required of every conforming implementation in the applicable profile;
- **unspecified** behavior has no promised value, order, spelling, or consistency between calls or releases;
- **implementation-defined** behavior is not portable, but an implementation MUST document its choice for the referenced release and obey every invariant stated here;
- **backend-dependent** behavior may vary only over the outcomes named for the selected backend/profile. The active backend MUST be discoverable from build configuration or the embedding boundary.

An implementation-defined order is not an Experimental feature, and an Optional feature is not unspecified when enabled.

### 0.4 Scope of conformance

**TNK-DOC-003 — Conforming implementation.** A conforming TNK implementation MUST:

- accept every Stable source and command form specified here;
- produce the specified mathematical result, state transition, and completion classification;
- enforce the specified bounds and recovery boundaries;
- preserve documented Session state transitions;
- distinguish success, finite failure, incompleteness, unsupported capability, and resource exhaustion where this Reference distinguishes them;
- avoid panic, memory unsafety, and process abort for accepted source and documented invalid-input paths.

It need not reproduce internal DAG layouts, solver traversal order, allocation counts, external
implementation enumeration order, or human-oriented whitespace unless a clause makes one observable.

### 0.5 Diagnostics, limits, and invalid input

**TNK-DOC-006 — Failure classification.** A public operation classifies failure at the narrowest owning boundary: lexical/parse, static declaration or statement, module/view composition, command construction, Unsupported capability, backend `Unknown`/`BadDag`, user bound, internal incompleteness, external I/O, or resource exhaustion. A diagnostic's category and documented state effect are semantic; incidental prose is not. Accepted input MUST NOT panic, abort the process, or cause memory unsafety.

Invalid module/view definitions are atomic unless a clause explicitly permits statement-local isolation. Invalid commands do not partially apply their requested semantic transition. Low-level Rust API precondition violations, such as using an engine-relative ID with another `Engine`, are programmer errors rather than accepted source input.

The current workspace does not satisfy this policy uniformly for incorrect input. Appendix H.4 is the release-specific exception ledger: it records what the implementation presently does, but does not make those inputs accepted language or relax the intended conformance rules.

**TNK-DOC-007 — Resource policy.** A user bound is a requested finite prefix, not a timeout and not proof of exhaustion. An implementation resource limit MUST be reported separately from no-solution. External harness timeouts and operating-system termination are outside TNK semantics.

### 0.6 Conformance profiles

**TNK-PROFILE-001 — Named profiles.** The **default** profile builds every workspace crate with default features and uses the pure-Rust null SMT backend, whose answer is `Unknown`. The **smt-z3** profile enables the crate feature `smt-z3` on `tnk-core` directly or through the forwarding feature on `tnk-session`/`tnk-repl`. There is no root workspace feature of that name.

Loaded hook libraries form runtime capability sets, not hidden language defaults. A clause guarded by “when hooks resolve” applies only after the defining module is loaded; the missing-hook behavior remains specified as Optional or Unsupported.

### 0.7 Product boundary

TNK comprises five layers:

| Crate | Responsibility | Public role |
|---|---|---|
| `tnk-core` | sorts, symbols, terms, matching, reduction, rewriting, search, symbolic solvers, GC | semantic kernel and low-level embedding API |
| `tnk-frontend` | lexer, module/command parser, mixfix grammar, term building, pretty-printing | source-language layer |
| `tnk-modules` | module/view databases, imports, renaming, instantiation, reflection descent | composition layer |
| `tnk-session` | persistent host-owned state, command execution, continuations, diagnostics | primary embedding boundary |
| `tnk-repl` | terminal wrapping, prompts, history, CLI policy | executable adapter |

**TNK-DOC-004 — No implicit stock prelude in libraries.** The kernel, frontend, module, and Session layers do not load `prelude.maude`. Only the `tnk-repl` binary attempts to load that external file. The sole in-process module synthesis is `CONFIGURATION`, inserted by `tnk_modules::prelude::ensure_builtins` when an object module/import needs it and no user definition exists. Every other library-defined semantic surface exists only after its module has been loaded.

### 0.8 Compact feature contract

Each normative feature is read through the same ten fields: **status** (the matrix in §23), **surface** (syntax/API block), **static requirements**, **meaning**, **observable contract**, **errors and recovery**, **completeness/resource boundary**, **unspecified behavior**, **minimal example**, and stable **`TNK-*` anchor**. Closely related clauses compress these fields into prose and tables rather than repeating ten headings; omission means “not applicable,” never “whatever the implementation happens to do.” Appendix L provides linkable anchors for every clause.

---

# Part I — Semantic foundations

## 1. Signatures, sorts, and kinds

### 1.1 Sort order

A TNK signature contains named sorts and a strict declared subsort relation. Its reflexive-transitive closure is written `<=`.

**TNK-SORT-001 — Partial order.** Distinct user sorts MUST NOT be mutually reachable through subsort declarations. A subsort cycle invalidates the signature. Reflexivity and transitivity are implicit; users do not declare them.

A cycle is checked on the flattened signature, so it is detected whether it lies within one module's own declarations (including a self-loop such as `subsort A < A`) or forms only through imports. It is a declaration-category failure (H.3): `Session::eval` reports an `error:` diagnostic naming the module, and the definition is not installed; any prior definition of that name, the current module, and later input in the same submission are unaffected.

**TNK-SORT-002 — Kinds.** The undirected connected components of the subsort graph are kinds. Each kind has one synthesized error/top sort, written by the printer as a bracketed list of the component's maximal user sorts, for example `[Nat]` or `[Nat,Bool]`. Every user sort is below its kind error sort. Error sorts are not below user sorts.

A term has a **least sort**. If no operator declaration applies to the argument sorts, the application has the result kind's error sort rather than becoming an untyped node.

### 1.2 Operators and overloading

An operator declaration has a canonical name, arity, domain sorts, range sort, and attributes. Declarations with the same canonical name and the same domain-kind vector and result kind form one overload family (one semantic symbol).

**TNK-SORT-003 — Applicability and least result.** A declaration `f : S1 ... Sn -> S` is applicable to arguments of least sorts `A1 ... An` exactly when `Ai <= Si` for every position. The application's least sort is the greatest lower bound of applicable range sorts when unique. If incomparable applicable ranges have no unique least choice, TNK currently chooses the earliest declared applicable range and classifies the signature as non-preregular at that application. The choice is Stable for a fixed declaration order; warning presentation is not yet part of the contract.

**TNK-SORT-004 — Kind coherence.** One overload-family symbol has a fixed arity, one kind for every domain position, and one result kind. A shared source name with a different arity, domain-kind profile, or result kind denotes a separate semantic symbol.

**TNK-SORT-005 — Partial operators.** `~>` declares a partial operator. Its domain and range positions are lifted to their kinds. Inputs outside the intended user sorts may therefore build a kind-sorted unreduced application. Partiality does not synthesize an exception or an option value.

### 1.3 Variables and substitutions

A variable is identified by a written name, declared sort, and command- or statement-local slot. A colon variable such as `X:Nat` declares its sort at the occurrence; its written name is `X`. A bare variable must be declared by `var` or `vars` in its source scope. Within one statement or command, occurrences with the same written name and the same resolved sort are one variable, whatever their spelling. A declared `X` of sort `Nat` and `X:Nat` are one variable, and so are `X:[A]` and `X:[B]` when `A` and `B` lie in one kind. The same name at another sort is another variable. Which spelling names the variable in command output is Implementation-defined.

**TNK-SORT-006 — Sort-respecting substitution.** A substitution may bind a variable of sort `S` only to a term whose least sort is `<= S`. Repeated occurrences of the same variable MUST receive equal values modulo the operator axioms and equations applicable at the operation's semantic boundary.

Variable slot numbers and internal fresh-family names are not semantic identities across independent commands. Printed fresh names are presentation unless an indexed metalevel API explicitly returns them.

## 2. Terms and equality

A term is a variable, an operator application, an iterated operator application, or a literal represented by a hooked operator. Runtime terms are DAGs: equal subterms may be shared, but sharing is not semantic.

### 2.1 Operator theories

TNK assigns one matching/canonicalization theory to an operator from its attributes:

| Attributes | Theory | Canonical meaning |
|---|---|---|
| none of `assoc`, `comm`, `id:`, `idem`, `iter` | Free | ordered fixed-arity application |
| `assoc` | AU/A | flattened ordered word, with optional identity removal |
| `assoc comm` | ACU/AC | flattened multiset, with optional identity removal |
| any non-associative combination of `comm`, `id:`, `idem` | CUI family | binary commutation and/or collapse laws |
| `iter` | S | compact repeated unary application |

**TNK-TERM-001 — Quotient equality.** Semantic equality of runtime terms is structural equality after canonicalization by the declared operator axioms. It ignores DAG sharing and allocation identity. User equations are not part of structural equality; they are part of reduction. Calling a reduced normal form “equal” therefore means both equation-normal and axiom-canonical only when the context says so.

**TNK-TERM-002 — Associativity.** An associative application is flattened without changing left-to-right argument order. For an associative-commutative application, arguments form a deterministic canonical multiset. The internal sort order of equal-kind elements is Implementation-defined; clients that need mathematical AC equality compare multisets or canonical terms.

**TNK-TERM-003 — Identities.** `id: e` is two-sided and participates in AU, ACU, and CUI construction and matching. On an associative operator, `left id: e` and `right id: e` collapse only the corresponding AU end. On a commutative operator a one-sided declaration becomes two-sided. A non-associative, non-commutative operator with only a one-sided identity remains a free binary constructor for ordinary construction/matching; no general CUI collapse is promised. Identity terms must be ground and sort-compatible. At a supported identity-matching boundary, a pattern rooted at the operator can match a subject whose canonical form is not rooted there, with omitted operands bound to the identity.

**TNK-TERM-004 — Idempotence.** `[idem]` identifies `f(x,x)` with `x` at canonicalization and matching boundaries supported by the CUI matcher. Non-ground unification under an idempotent operator is Unsupported; ground terms still canonicalize.

**TNK-TERM-005 — Iteration.** `[iter]` is unary. `f^n(t)` denotes `n` applications without allocating an `n`-node chain. Iteration counts are arbitrary-precision positive decimal values at the source boundary. `f^0(t)` is represented semantically by `t`, not by an iter node.

### 2.2 Literals

The frontend can build literals only when the loaded signature supplies the corresponding hooked symbols.

- Natural and integer numerals use a zero/successor/minus hook family and arbitrary-precision values.
- Glued rationals such as `-7/3` are canonical exact rationals when a rational/division surface is loaded.
- Floats use IEEE 754 binary64 (`f64`).
- Strings are owned string values; quoted identifiers are interned identifier values.

**TNK-TERM-006 — Exact and inexact numbers.** Integer and rational equality, hashing, and ordering are mathematical and exact. Rational values are reduced to canonical form. Float operations follow the host's IEEE `f64` behavior; NaN and infinity behavior is therefore float behavior, not exact-number behavior.

### 2.3 Runtime handles and garbage collection

`DagId`, `SortId`, and `SymbolId` are engine-relative handles. They are not serializable semantic identifiers and MUST NOT cross engines.

**TNK-RUNTIME-001 — DAG lifetime.** A `DagId` remains usable across collection only while reachable from an engine root or a live `RootGuard`. `Engine::root(id)` returns the RAII guard. Dropping the guard releases the pin; `RootGuard::set` retargets it.

**TNK-RUNTIME-002 — Non-moving collection.** Collection is mark-and-sweep and does not move live nodes. Freed slots may be reused. Debug builds detect stale and cross-engine handles; release builds do not promise such detection. `contains` and `try_get` are not liveness proofs for unrooted handles across a collection.

**TNK-RUNTIME-003 — Semantic transparency.** Garbage collection MUST NOT change reduction, matching, search, solver, printing, or continuation results for properly rooted terms. GC timing, arena capacity, and node sharing are not observable semantics.

## 3. Equations, memberships, rules, and conditions

### 3.1 Statement classes

- `eq` and `ceq` define equational reduction.
- `mb` and `cmb` refine the least sort of matching terms.
- `rl` and `crl` define transition rules used by rewriting and search.
- `[nonexec]` retains a statement as specification metadata but excludes it from ordinary execution.
- `[variant]` makes an equation available to folding variant narrowing in addition to ordinary equational reduction.
- `[narrowing]` makes a rule available to variant-based narrowing. A rule may be both `[narrowing]` and `[nonexec]`: it then participates in narrowing but not ordinary rewriting.

Theory declarations retain statements as specification material. `[nonexec]` statements are proof obligations and do not execute; unmarked theory equations remain executable when a theory is built and reduced directly. Views still require a theory source.

### 3.2 Equational reduction

**TNK-REDUCE-001 — Normalization.** `reduce` repeatedly evaluates permitted arguments and applies successful hooked specials or executable equations until neither applies. A successful special or equation application counts as one rewrite. Its replacement is reduced under the same strategy until normal form.

**TNK-REDUCE-002 — Top-rewrite choice.** At one redex, an implemented `special` hook is attempted before user equations. If it declines, executable ordinary equations are tried in flattened declaration order. Each equation matcher may enumerate several substitutions; the first whose condition succeeds is used. `[owise]` equations are considered only after every ordinary equation and all condition solutions fail. The first applicable `[owise]` equation is used.

**TNK-REDUCE-003 — Evaluation strategy.** Operator `strat (...)` controls argument/top evaluation order using 1-based argument positions and `0` for a top-rewrite attempt. Without an explicit strategy TNK uses its standard eager strategy. `[frozen]` and `frozen (positions)` suppress rule-rewrite descent at the designated arguments; equations required to form canonical terms still govern reduction according to the operator strategy.

Configured `HostFunctionSymbol` attachments are the open strict-eager special class. Their additional admission, scoped-callback, decline, result-validation, fault, and purity contracts are `TNK-HOST-001` through `TNK-HOST-004` in §16.1.1.

### 3.3 Membership evaluation

**TNK-MB-001 — Sort refinement.** A successful membership axiom lowers a node's least sort but does not replace its term. Only strict lowering counts. Memberships are retried to a fixpoint after each lowering.

**TNK-MB-002 — Priority.** Applicable memberships are considered by target specificity (smaller target sort first), with declaration order breaking equivalent choices. Each successful strict lowering counts as one rewrite. A failed match or condition has no membership count.

### 3.4 Conditions

A condition is a conjunction of fragments evaluated left-to-right:

| Form | Meaning |
|---|---|
| `u = v` | instantiate and reduce both sides; require quotient-structural equality |
| `u : S` | instantiate and reduce `u`; require `least-sort(u) <= S` |
| `p := u` | reduce `u`, match `p`, and bind variables first introduced in `p` |
| `u => p` | in a `crl` only, breadth-first rewrite-search from `u` until `p` matches |
| `b` | abbreviated Boolean fragment; desugars to `b = true` using the loaded truth hook |

**TNK-COND-001 — Backtracking.** If a later fragment fails, evaluation resumes the nearest earlier multi-solution matching or rewrite fragment. It then propagates outward to the statement matcher. Bindings introduced on a failed branch MUST be rolled back.

The first complete condition branch is accepted. Enumeration among otherwise tied matcher solutions or rewrite states is Implementation-defined under `TNK-CMD-002`. A statement that uses a branch-introduced binding in its right side is portable only when the accepted branch is unique or every accepted branch produces the same canonical right side.

**TNK-COND-002 — Variable discipline.** An equation or membership right side/target condition may use only variables bound by its left side or by earlier condition fragments. A rule may similarly introduce variables through earlier condition fragments; an executable statement with an unbound right-side variable is rejected. Rewrite fragments are legal only in rule conditions.

**TNK-COND-003 — Divergence.** Rewrite conditions can explore an unbounded state space and recursive conditions can diverge. TNK avoids process-stack overflow at the recursive condition seam, but it does not impose a semantic timeout and exposes no cooperative cancellation token.

### 3.5 Rules

**TNK-RULE-001 — Transition.** One rule transition selects a non-frozen position, matches one executable rule left side modulo the symbol theories, satisfies its condition, replaces the redex with the instantiated right side, and equationally reduces the resulting term where required by the driving command.

Rule transitions are distinct from equation normalization. `reduce` never applies rules. `rewrite`, `frewrite`, `erewrite`, ordinary `search`, strategies, LTL model checking, and some condition fragments do.

**TNK-RULE-002 — Model-theoretic obligations.** TNK does not prove termination or confluence of $E$, or coherence of $R$ with $E$ modulo $A$. Rule-fair rewriting and ordinary search canonicalize states before matching rules. A model that expects the transition relation to be well-defined modulo $E$ MUST make rule behavior coherent across $E$-equivalent representatives; otherwise a rule matching only a noncanonical representative can be absent from the explored graph.

### 3.6 Semantic relations and environments

A flattened module environment is written

$$\mathcal{M}=(\Sigma,A,E,M,R,H),$$

where $\Sigma$ is the order-sorted signature, $A$ the declared structural axioms, $E$ executable equations, $M$ executable memberships, $R$ executable rules, and $H$ resolved hook metadata. Source imports, views, and renamings construct this environment; they are not extra rewrite steps inside it.

**TNK-SEM-001 — Core relations.** The Reference uses:

- $\Gamma \vdash t:s$ when $s$ is the least sort of term $t$ under variable environment $\Gamma$;
- $t =_A u$ when axiom-canonical forms of $t$ and $u$ are structurally equal;
- $t \rightarrow_{E/A} u$ for one permitted hooked/equational reduction step modulo $A$, and $\rightarrow^*_{E/A}$ for its reflexive-transitive closure;
- $t \Rightarrow_{R/E,A} u$ for one admissible rule transition modulo $A$, with the equation-normalization required by the driving command;
- $\sigma \models_A p \preceq t$ when sort-respecting substitution $\sigma$ makes pattern $p$ equal to subject $t$ modulo $A$;
- $\theta \models_A \{u_i =? v_i\}$ when every $u_i\theta =_A v_i\theta$;
- $t \Rightarrow^n u$ for reachability by exactly $n$ rule transitions between canonical states.

Matching does not include $E$ unless a command explicitly normalizes its boundary. Search nodes are equation-normal, so their equality is $=_{E/A}$ by normalizing both sides and then comparing modulo $A$. LTL satisfaction is over infinite paths of this canonical transition system; a deadlock receives only the semantic self-loop specified by `TNK-LTL-001`.
---

# Part II — Source language

## 4. Lexical syntax

### 4.1 Tokens

**TNK-LEX-001 — Token separation and terminators.** Whitespace and the characters `(`, `)`, `[`, `]`, `{`, `}`, and `,` separate tokens; each punctuation character is a token. Other characters, including `_`, `+`, `-`, `<`, `=`, `:`, and ordinary periods, may belong to an identifier. A backquote escapes a splitting character into the current identifier.

A `.` is a terminator when, after spaces/tabs/carriage returns, it is followed by end of input, newline, a `***`/`---` line-comment marker, or a keyword in the release's same-line **SEEN_DOT** set:

```text
fmod mod fth th endfm endm endfth endth view endv
sort sorts subsort subsorts op ops var vars
protecting pr extending ex including inc
eq ceq mb cmb rl crl
red reduce check match xmatch rew rewrite search smt-search
```

Otherwise `.` remains an identifier character, including the `_._` operator. Same-line separation before a top-level opener absent from this list is Implementation-defined recovery; portable source puts a newline after the terminator.

**TNK-LEX-002 — Comments.** `***` and `---` begin line comments. If the first nonblank character after either marker is `(`, it begins a balanced parenthesized comment that may cross lines; backquoted parentheses do not affect its balance. Comments produce no tokens.

**TNK-LEX-003 — Literal tokens.** The lexer recognizes:

- naturals: `0` or a nonzero digit followed by digits;
- negative integers: a glued `-` and decimal digits with nonzero magnitude (`-0` is not a negative-integer token);
- rationals: `[ - ] num/den` with no spaces, canonical leading-zero rules, and a positive nonzero denominator; `-0/n`, `00/n`, and `n/0` are not rational tokens;
- floats with optional sign, at least one digit, and a decimal point or exponent, plus signed `Infinity`; examples include `+1.5`, `1.`, `.5`, `1e3`, `.5e2`, and `-Infinity`;
- strings only when an unescaped closing quote is the token's final character; a glued `"x"y` is an identifier;
- quoted identifiers beginning with `'`;
- iter tokens whose last suffix is `^` plus a positive, leading-nonzero decimal count.

Spacing is semantic at tokenization: `1/6` is a rational token while `1 / 6` is an operator application; `-7` is one integer token while `- 7` uses an operator token; `5 -7` is not the same token stream as `5 - 7`.

### 4.2 Term grammar

TNK constructs a per-module context-free grammar from sort and operator declarations.

**TNK-PARSE-001 — Mixfix holes.** Each `_` in an operator name is an argument hole. A valid declaration has exactly as many holes as its declared arity. Literal fragments, precedence, and gather annotations determine admissible parses. Prefix operators and constants use their declared spelling. Parentheses group terms. `(t).Sort` explicitly disambiguates an overloaded term at a sort. The current fallback for an invalid hole/arity mismatch is catalogued in Appendix H.4.

`prec n` assigns precedence. `gather (E e & ...)` constrains each hole (`E` strong, `e` weak, `&` unconstrained). If omitted, TNK derives defaults from fixity and precedence.

**TNK-PARSE-002 — Parse outcomes.** Statement terms and membership target sorts require one parse. Unique parse is also required for a `match`/`xmatch` pattern, a search goal, and an `srewrite`/`dsrewrite` subject. The current command surface selects the first packed-forest parse for reduce/check/rewrite/frewrite/erewrite subjects, match subjects, search subjects, unification pairs, variant terms/blockers, and narrowing subject/goal terms. The selected first-parse order is Implementation-defined; portable source disambiguates it.

No parse rejects the owning statement or command under the intended parser contract. Ambiguity rejects only the bubbles listed as unique-parse above. Statement-local rejection follows `TNK-STMT-001`; command rejection follows the Session transition table. Current invalid-input exceptions, including skipped top-level tokens and nonuniform trailing-attribute handling, are catalogued in Appendix H.4.

**TNK-PARSE-003 — Resource bound.** Production parsing uses a deterministic effort limit of `100,000,000` parser work units. Exceeding it is resource exhaustion, not a malformed-term result. The diagnostic identifies the furthest token. The limit is Stable until an explicit Reference revision changes it.

The generated grammar does not provide redundant hole-bearing prefix spellings such as `_+_(a,b)` or `s_(t)`. Use the declared mixfix form or declare a separate prefix operator.

## 5. Modules, theories, and declarations

### 5.1 Module forms

The accepted open/close pairs are:

| Form | Meaning | Close |
|---|---|---|
| `fmod M is ... endfm` | functional module; equations and memberships | `endfm` |
| `mod M is ... endm` | system module; additionally rules | `endm` |
| `fth T is ... endfth` | functional theory; statements may be executable unless `[nonexec]` | `endfth` |
| `th T is ... endth` | system theory; rules allowed as specification or execution according to attributes | `endth` |
| `smod M is ... endsm` | strategy system module | `endsm` |
| `sth T is ... endsth` | strategy system theory | `endsth` |
| `omod M is ... endom` | object-oriented system module | `endom` |
| `oth T is ... endoth` | object-oriented system theory | `endoth` |

A parameterized declaration inserts `{ X :: THEORY, ... }` after the module or view name; `::` is one token.

**TNK-MOD-001 — Functional/system gate.** Functional modules and theories reject rules. Strategy declarations/definitions are accepted only in strategy modules/theories. Object declarations are accepted only in object modules/theories.

### 5.2 Declaration grammar

The declaration surface is:

```text
SortName  ::= Id | SortName "{" SortName ("," SortName)* "}"
            | "[" SortName ("," SortName)* "]"

sort SortName .
sorts SortName+ .
subsort SortName < SortName .
subsorts SortName+ ("<" SortName+)+ .

op  OpName : SortName* ("->" | "~>") SortName [OpAttrs] .
ops OpName+ : SortName* ("->" | "~>") SortName [OpAttrs] .
var  Name : SortName .
vars Name+ : SortName .

protecting ModuleExpr .
extending  ModuleExpr .
including  ModuleExpr .
generated-by ModuleExpr .

class Cid [ "|" AttrName ":" SortName ("," AttrName ":" SortName)* ] .
classes ...
subclass Cid+ "<" Cid+ ("<" Cid+)* .
subclasses ...
msg OpName : SortName* "->" SortName [OpAttrs] .
msgs ...

strat Name+ [ ":" SortName* ] "@" SortName .
strats ...
sd  Name [ "(" TermBubble ("," TermBubble)* ")" ] ":=" Strategy .
csd Name [ "(" TermBubble ("," TermBubble)* ")" ] ":=" Strategy "if" Condition .
```

`pr`, `ex`, and `inc` abbreviate the three ordinary import modes. `generated-by` is accepted as a protecting-equivalent donation form; because import-mode obligations are Experimental, reflected mode-tag distinctions for this spelling are not portable. `class`/`subclass`/`msg` are object-only; `strat`/`sd`/`csd` are strategy-only. `csd` parses but is Unsupported at strategy resolution.

In `ops` and `msgs`, each top-level parenthesized group is one OpName, and its pair of quoting parentheses is removed, as in `op (_+_) : S S -> S .`. Only the punctuation tokens `(` and `)` delimit a group; a backquoted `` `( `` or `` `) `` is part of an identifier (`TNK-LEX-001`). Every other token is one OpName. So `ops (m{X}) (n{X}) c : -> S .` declares the constants `m{X}`, `n{X}`, and `c`, `ops (_+_) (_*_) : S S -> S .` declares `_+_` and `_*_`, and `` ops `( `) : -> S . `` declares `(` and `)`. An empty group or an unmatched `)` in the name list is a parse error.

A user sort identifier cannot contain `.`. Bracketed sort names denote kinds; structured sorts and parameter sorts such as `List{Nat}` and `X$Elt` are semantic names, not punctuation-free aliases.

In a `var`/`vars` name list, in a module or a view, a `,` token separates names and is never itself declared: `vars W, X : S .` declares exactly `W` and `X`, like `vars W X : S .`. A `,` in a term is therefore never a declared variable.

### 5.3 Operator attributes

| Attribute | TNK behavior |
|---|---|
| `assoc`, `comm`, `idem` | select algebraic canonicalization and matching laws |
| `id: t`, `left id: t`, `right id: t` | two- or one-sided identity |
| `iter` | compact iteration theory |
| `ctor` | constructor metadata used by symbolic analyses; no direct rewrite |
| `prec n`, `gather (...)` | grammar |
| `strat (...)` | equational evaluation strategy |
| `frozen`, `frozen (...)` | rule/narrowing descent barrier |
| `format (...)` | pretty-printer layout controls |
| `poly (...)` | expand listed argument/range positions (`1..n`, range `0`) over each kind |
| `special (...)` | bind an implemented built-in or a configured strict Rust reducer |
| `config`, `obj`, `msg`, `portal` and long aliases | object/external scheduler roles |
| `pconst` | parameter-theory constant, mapped through views |
| `ditto` | inherit the preceding declaration's attributes where valid |
| `metadata`, `latex`, `rpo` | accepted non-semantic metadata/termination hints |
| `memo` | Unsupported: accepted, warned about, and has no execution effect |

**TNK-DECL-001 — Unknown attributes and hooks.** An unknown operator attribute or unknown `special` subdirective is rejected. `HostFunctionSymbol` is supported only when its key resolves in the configured `HostFunctionCatalog`; a missing capability or invalid attachment rejects the module atomically. Other recognized `id-hook` classes with no TNK implementation attach no `SpecialOp`; the operator remains ordinary and may still reduce by user equations. This Unsupported non-host binding is currently silent at build time, so an unchanged term is not evidence that the hook ran.

`special` accepts `id-hook CLASS (...)`, `op-hook PURPOSE (...)`, and `term-hook PURPOSE (...)`. Hook names are library integration interfaces. §16.1 and Appendix G classify the supported classes.

### 5.4 Statements

```text
[Label] ":" eq  lhs = rhs [StmtAttrs] .
[Label] ":" ceq lhs = rhs if Condition [StmtAttrs] .
[Label] ":" mb  term : SortName [StmtAttrs] .
[Label] ":" cmb term : SortName if Condition [StmtAttrs] .
[Label] ":" rl  lhs => rhs [StmtAttrs] .
[Label] ":" crl lhs => rhs if Condition [StmtAttrs] .
```

The leading `[Label] :` is optional for every statement family. For rules, the familiar `rl [Label] : ...` token arrangement is accepted by the same label peeling. Retained execution attributes are `owise`, `variant`, `nonexec`, `narrowing`, and `label Name`; `print` is retained for validation/trace presentation. `metadata`, `format`, and `dnt` are parsed but semantically ignored. Unknown trailing statement-attribute tokens do not have one uniform current treatment; Appendix H.4 records the parser-path-dependent behavior. Portable source uses only the listed attributes.

`Condition` is a `/\`-separated conjunction of the fragments in §3.4; `\/` is not a statement-condition connective.

Operator names may contain `:`, `=`, `:=`, `=>`, `if`, and `fi` as literal fragments, as in object syntax `< O : C | a : v >` and BOOL's `if_then_else_fi`. The delimiters below are therefore not simply the first token with their spelling. A token inside parentheses is never one of them.

- **Membership target.** The `:` before the target sort of `mb` is the first `:` followed only by a sort name and an optional attribute group before the terminator. For `cmb`, it is the first `:` followed by a sort name and `if`. If no `:` has that shape, the first `:` is the delimiter.
- **Condition keyword.** In `ceq` and `crl`, `if` and `fi` tokens outside parentheses, brackets, and braces pair like brackets. The condition keyword is the first `if` that no later `fi` closes. If every such `if` is closed, the keyword is the first of them.
- **Fragment connective.** A condition fragment with a `:=`, `=>`, `=`, or `:` token is read at the first one whenever both sides build there; after a `:`, that means a sort name. Otherwise the fragment needs exactly one reading. The candidates are its later such tokens (a `:` only before a sort name) and the whole fragment as a term `b` of the kind of the loaded `true`, read as `b = true` (§3.4). A fragment with no reading is invalid, and so is an ambiguous fragment with several. If parsing a candidate exceeds the effort limit, that resource-exhaustion diagnostic (`TNK-PARSE-003`) rejects the fragment.

The fragment rule also reads the `such that` conditions of `search`, `smt-search`, and the `matchrew` strategy family. Portable source parenthesizes a term that contains these tokens.

**TNK-STMT-001 — Invalid statement isolation.** Under the intended statement boundary, a statement whose terms, variable discipline, print metadata, or supported condition forms are invalid is dropped with a diagnostic when the enclosing module can otherwise be built. Dropping one statement MUST NOT shift the source identity of later executable statements or corrupt reflection metadata. Appendix H.4 records current invalid-input seams that silently retain a statement or otherwise differ from this rule.

### 5.5 Views

A view has the form:

```text
view V { P :: T, ... } from ModuleExpr to ModuleExpr is
  sort S to T .
  op f to g .
  op f : A B ("->" | "~>") C to g .
  op c to term TargetTerm .
  var X : S .
  class C to D .
  attr a [ "." Class ] to b .
  msg SourceBubble to term TargetTerm .
endv
```

**TNK-VIEW-001 — View validity.** The source must be a named theory or an instantiation rooted at one; source and target cannot be sums or renamings. Source sorts map explicitly or by identity. For an unparameterized view with a plain named target, install-time validation checks target sort existence, kind preservation, and a compatible operator or operator-to-term image for every source profile. Invalid views are not installed.

Parameterized views and views with a nontrivial instantiated target receive partial install-time checks; remaining homomorphism obligations are discharged when instantiated. A partially validated stored view is not evidence that every future instantiation is valid. View variables scope only operator-to-term/message mappings. An `attr` map's optional class qualifier is accepted but does not narrow the map, as in renamings (`TNK-MOD-005`).

## 6. Module expressions and composition

The complete shape is:

```text
ModuleExpr ::= Rename ("+" Rename)*
Rename     ::= Atom ("*" "(" RenameItem ("," RenameItem)* ")")*
Atom       ::= Name | "(" ModuleExpr ")" | Atom "{" ModuleExpr ("," ModuleExpr)* "}"
RenameItem ::= "sort"  SortName "to" SortName
             | "op"    OpName [ ":" SortName* ("->" | "~>") SortName ]
                       "to" OpName [OpAttrs]
             | "label" Name "to" Name
             | "class" SortName "to" SortName
             | "attr"  Name [ "." Class ] "to" Name
             | "msg"   OpName "to" OpName
```

Instantiation arguments are a view name, a parameterized-view instantiation, or an enclosing formal parameter name. Bare modules, sums, and renamings are not legal arguments; define an identity view when a module is the intended target.

**TNK-MOD-002 — Flattening and order.** Declaration donation is depth-first, imports before importer. The root module's own statements and strategy declarations/definitions are then moved before imported ones; imported blocks retain post-order. Each canonical module expression contributes at most once, so diamonds do not duplicate a common base. Sort and variable names are name-deduplicated; ops, subsorts, and statements are appended. Strategy declarations/definitions carry origin and source index so the strategy compiler deduplicates diamond donation without merging independent text-identical definitions. Statement home modules are build-time reparse data, not reflected statement metadata.

**TNK-MOD-003 — Import modes.** `protecting`, `extending`, and `including` donate the same closure. Their source mode remains available to reflection, but a flattened executable image has no import list and TNK enforces no no-junk/no-confusion obligations. The semantic mode distinction is Experimental.

**TNK-MOD-004 — Parameters.** A formal parameter copies only sorts declared by its bounding theory under `X$`; sorts donated to that theory by ordinary modules remain shared. `[pconst]` operators receive corresponding parameter names and map through views. Structured sort parameters substitute structurally (`Base{X}` to `Base{Arg}`), including chained instances. A theory-target view can deliberately leave a parameter free for a later instantiation; importing an instance that still has free parameters is an error. An apparent `X$Name` not owned by the bound theory is not rewritten merely because of its spelling.

**TNK-MOD-005 — Renaming.** Sort, operator, label, class, attribute, and message renamings apply structurally. An operator profile selects one overload family (§1.2): every declaration of that name and arity whose domain and range sorts lie in the profile's kinds, together with the statements and `op-hook` references that use the family. The profile must spell the sorts of a declared overload of that name, without kind brackets; otherwise, or when two profile maps select one family, the renaming is an error. For the family it selects, a profile map takes precedence over a plain map of the same name. Without a profile, the name map applies to every matching declaration. An attribute item's optional `. C` class qualifier is accepted but does not narrow the map: attribute operators are shared by name across classes, so `attr a . C to b` renames attribute `a` of every class, exactly like `attr a to b`. Optional target attributes override the renamed operator attributes. Mixfix applications, special hook references, identity/term-hook bubbles, and required sort qualification are reconstructed structurally rather than by blind text replacement. Strategy names themselves are not ordinary operator renames.

**TNK-MOD-006 — Atomic definition.** A successful module definition makes that module current, clears reflection state, drops the continuation, and rebuilds transitive dependents. A successful view definition leaves the current module unchanged; it rebuilds dependent modules and drops the continuation iff a module was rebuilt. A failed module/view definition preserves the prior database, built dependents, current selection, and continuation.

**TNK-MOD-007 — Import hygiene.** Self/mutually recursive imports and closed-module imports that retain free parameters are hard flattening errors. A non-theory module silently ignores an ordinary import of a theory; a non-strategy module silently ignores an imported strategy module. These silent skips are specified recovery, not successful donation. Parameter bounds are not ordinary imports.

---

# Part III — Commands and evaluation

## 7. Common command rules

Most semantic commands accept an optional `in M :` qualifier. It selects module `M` for that command only and does not change the Session's current module.

Supported bracketed bounds use positive decimal components:

- `[n]` limits results or rule applications as described by the command;
- `[n,m]` supplies the command-specific second bound;
- a `0` component in a bracketed bound is rejected with a parse-category diagnostic for rewrite, frewrite, erewrite, search, SMT-search, variants, variant unification/matching, and narrowing;
- ordinary `unify [0]` is a known unsupported parser/driver edge: it currently prints `No unifier.` and MUST NOT be used as a semantic query;
- `continue 0 .` is valid and performs no additional work.

**TNK-CMD-001 — Bounds and completion.** Reaching a user bound is not semantic exhaustion. A bounded command MUST retain a continuation when its command class is resumable and MUST NOT print an exhaustion claim merely because the bound was reached. Exhaustion means the underlying finite enumerator or state space has been explored to its defined boundary.

**TNK-CMD-002 — Result order.** TNK guarantees equation/rule declaration priority, breadth-first search depth, fair-vs-depth-first strategy policy, and source-order state effects. Tie order among independent equal-depth matches, AC partitions, unifiers, or graph successors is deterministic within one run but otherwise Implementation-defined unless an indexed API clause says otherwise. A bounded command returns a deterministic prefix; callers that need an unordered mathematical result compare canonical sets and reject duplicates.

The command surface and saved-operation behavior are:

| Command family | First bound | Second bound | Saves a continuation |
|---|---|---|---|
| `rewrite` | rule applications | — | yes |
| `frewrite` | rule applications | per-position gas | yes |
| `erewrite` | configuration deliveries | fallback gas | yes |
| `search` | solutions | rule depth | yes |
| `smt-search` | solutions | rule depth | yes, except Unsupported `=>!` |
| `get variants` | variants | — | yes |
| `variant unify` / `variant match` | results | — | yes |
| `vu-narrow` / `fvu-narrow` | solutions | narrowing depth | yes |
| `reduce`, `check`, `match`, `xmatch`, strategy rewrite, ordinary `unify` | command-specific eager result | — | no |

Ordinary unification is currently eager and not resumable. A bound limits only the results rendered by that command.

## 8. Reduction and matching

### 8.1 Reduce

```text
reduce [in M :] term .
red    [in M :] term .
```

**TNK-CMD-REDUCE-001 — Reduce result.** The operand is built, equationally normalized, assigned its final least sort, and printed as `result SORT: TERM`. Open variables in a command subject are treated as stable symbolic constants for reduction, not as existential matcher variables. The command reports the aggregate rewrite count for that evaluation.

### 8.2 Match and extension match

```text
match  [in M :] pattern <=? subject .
xmatch [in M :] pattern <=? subject .
```

**TNK-MATCH-001 — Whole matching.** `match` enumerates sort-correct substitutions under which the pattern equals the whole subject modulo declared operator axioms. It does not use user equations to discover a binding, except for reductions explicitly performed while building/evaluating the command boundary.

**TNK-MATCH-002 — Extension matching.** `xmatch` permits a theory-rooted pattern to match a proper associative/AC portion where that theory defines extension. A result includes the matched portion/residue distinction in the command presentation. Without extension, an unmatched residue makes the candidate fail.

**TNK-MATCH-003 — Enumeration.** Every returned substitution is sound, duplicate-free under semantic substitution equality, and sort-correct. For a finite matcher, unbounded enumeration is complete. Enumeration order is Implementation-defined.

## 9. Rewriting modes

### 9.1 Rule-fair rewriting

```text
rewrite [n] [in M :] term .
rew     [n] [in M :] term .
```

**TNK-REWRITE-001 — Rule-fair mode.** The session first equationally normalizes the current term, then applies one rule at the first top-down non-frozen redex admitted by the rule scheduler. Per-symbol rule cursors rotate after success so repeated applications do not permanently starve later rules. It repeats until no rule applies or `n` rule applications have occurred.

The bound counts rule applications, not equation, condition, membership, or built-in rewrites. Those operations still contribute to the aggregate `rewrites:` diagnostic.

### 9.2 Position-fair rewriting

```text
frewrite [n]     [in M :] term .
frewrite [n,gas] [in M :] term .
frew     ...
```

**TNK-REWRITE-002 — Position-fair mode.** `frewrite` traverses non-frozen positions in repeated passes and allows at most `gas` successful rule applications at each position per pass. Default `gas` is `1`. The first bound limits total rule applications. A bounded stop may leave a noncanonical intermediate whose least sort has not been recalculated; it is reported as `result (sort not calculated)`.

### 9.3 Object/message rewriting

```text
erewrite [n]     [in M :] configuration .
erewrite [n,gas] [in M :] configuration .
erew ...
```

**TNK-REWRITE-003 — External/object mode.** At a symbol marked `config`, `erewrite` delivers queued messages object-by-object, respecting object, message, portal, and external-manager roles. At a non-configuration node it falls back to position-fair rewriting with the supplied gas. The first bound caps configuration-level deliveries.

External requests are synchronous. An accepted request is consumed and its response is inserted; a rejected request remains in the configuration. A stale external request token cannot consume a pending request. Standard stream managers support `write` to captured stdout/stderr and `getLine` from the Session's scripted input buffer.

### 9.4 Continue

```text
continue .
continue n .
cont ...
```

**TNK-CONT-001 — Continuations.** A Session owns at most one last continuation. `continue` resumes the saved rewrite, search, SMT-search, variant, variant-unifier/matcher, or narrowing object with its graph, solver, roots, counters, and numbering intact. A continuation is usable only while its originating module remains current and unchanged. `select`, including selection of the already-current name, always clears it. A successful module redefinition clears it; a successful view definition clears it only when dependent modules were rebuilt.

For rewrite sessions, an omitted continuation bound runs to rule normal form; a numeric bound permits that many additional rule applications. For enumerators, a numeric bound emits at most that many additional results; an omitted bound emits until exhaustion or divergence. `continue` with no current module, or without a usable continuation for the current module, emits an `error:` diagnostic and no records.

Continuation invalidation on a failed replacement command is currently Experimental and command-family-dependent: some builders clear before validation while others replace only on success. Portable hosts MUST NOT attempt `continue` after any intervening execution command, successful or failed. This boundary should become a uniform typed Session transition before continuation behavior is promoted beyond the current command contract.

## 10. Reachability search

```text
search [n]   [in M :] initial ARROW goal [such that condition] .
search [n,m] [in M :] initial ARROW goal [such that condition] .
```

`ARROW` is one of:

| Arrow | Candidate depths |
|---|---|
| `=>1` | exactly one rule transition |
| `=>+` | one or more transitions |
| `=>*` | zero or more transitions; initial state is eligible |
| `=>!` | terminal states with no successors |

The first bound limits solutions and the second bounds rule-transition depth.

**TNK-SEARCH-001 — Graph.** Search equationally normalizes each state and interns semantically equal states into one graph node. It explores lazily in breadth-first discovery order. Distinct paths to an equal canonical state do not create duplicate states; all discovered rule labels reaching a forward arc remain available for graph inspection.

**TNK-SEARCH-002 — Results.** A state is a solution when its depth satisfies the arrow, the goal matches, and `such that` succeeds. Search is sound and duplicate-state-free. In a finite graph with no depth bound it is complete. In an infinite graph an unbounded search may not terminate. Solution depths are nondecreasing; ordering within one depth is Implementation-defined.

**TNK-SEARCH-003 — Counts and paths.** Each solution reports its graph state, discovered-state count, and rewrite-count snapshot after its condition succeeds. `show path N .` follows the stored BFS predecessor tree. `show search graph .` reports discovered nodes and known arcs; because expansion is lazy, a bounded search may expose only a prefix of the reachable graph.

## 11. Strategies

```text
srewrite  [in M :] term using Strategy .
srew      [in M :] term using Strategy .
dsrewrite [in M :] term using Strategy .
dsrew     [in M :] term using Strategy .
```

Strategy precedence from low to high is branch `? :`, union `|`, sequence `;`, postfix `* + !`, then atoms:

```text
Strategy ::= Strategy "?" Strategy ":" Strategy
           | Strategy "|" Strategy
           | Strategy ";" Strategy
           | Strategy ("*" | "+" | "!")*
           | "(" Strategy ")"
           | "idle" | "fail" | "all"
           | ("top" | "one" | "try" | "not" | "test") "(" Strategy ")"
           | "or-else" "(" Strategy "," Strategy ")"
           | ("match" | "xmatch" | "amatch") Pattern
               [ "such" "that" Condition ]
           | ("matchrew" | "xmatchrew" | "amatchrew") Pattern
               [ "such" "that" Condition ]
               "by" Var "using" Strategy
               ("," Var "using" Strategy)*
           | Label [ "[" Var "<-" Term ("," Var "<-" Term)* "]" ]
               [ "{" Strategy ("," Strategy)* "}" ]
           | StrategyName [ "(" Term ("," Term)* ")" ]
```

`idle` succeeds unchanged; `fail` has no result; `all` applies every applicable rule at the current strategy seam. A label application may carry an initial substitution and one condition substrategy per rewrite-condition fragment. A named call resolves an `sd` whose declaration profile and left pattern match its arguments.

**TNK-STRAT-001 — Scheduling.** `srewrite` schedules processes FIFO and interleaves child tasks fairly. `dsrewrite` schedules depth-first. A process with no pending strategy emits one solution. `one(E)` emits at most the first `E` solution in this scheduling order; `E!` continues until `E` fails and then emits the normal form. Sub-searches are child tasks of the same schedule, including `matchrew` by-variable strategies and the condition substrategies of a rule application. A strategy-controlled conditional rule rewrites the subject for each condition solution as soon as that solution is found.

**TNK-STRAT-002 — Branching.** `T ? S : F` runs `S` on every solution of `T`; if `T` has none it runs `F` on the original subject. Derived branch forms desugar to this rule: `try(E)` is `E ? idle : idle`, `not(E)` is `E ? fail : idle`, `test(E)` is `not(not(E))`, and `or-else(E, F)` is `E ? idle : F`. So `try(E)` yields every `E` solution, or the unchanged subject when `E` has none, and `test(E)` yields the unchanged subject once when `E` has a solution and nothing otherwise. `matchrew` evaluates the named subterm strategies and rebuilds the enclosing match for their result combinations, each as soon as all of its subterm results are found; `dsrewrite` explores the named subterms in order. Each `by` variable must be a distinct variable of the pattern. The pattern's variables, and the variables that `:=` fragments of its `such that` condition bind, are bound in every `using` strategy, with the current match's values before any substrategy rewrites them. This includes strategy-call arguments, rule-application substitutions, and nested patterns and conditions. A `using` strategy that mentions any other condition variable is rejected. A `by` variable that the enclosing definition or matchrew already binds is matched at that value, and its occurrences are rebuilt from the substrategy results.

**TNK-STRAT-003 — Unsupported forms.** `xmatchrew` and conditional strategy definitions (`csd`) parse but are rejected during strategy resolution. Unconditional `sd` is Stable. `xmatch` as a strategy test is supported even though `xmatchrew` is not.

Strategy result values and fair/depth-first reachability are semantic. Aggregate rewrite-count interleaving among unequal-depth parallel branches is diagnostic and not a cross-release contract.

## 12. Order-sorted unification

```text
unify [n] [in M :] u =? v [ /\ u2 =? v2 ... ] .
irredundant unify [n] [in M :] ... .
irred unify ...
```

**TNK-UNIFY-001 — Meaning.** A result is a sort-correct substitution that makes every `=?` pair equal modulo declared algebraic axioms. Multiple `/\`-joined pairs are solved simultaneously. Free variables introduced by the solver receive sort-constrained fresh names. Every returned unifier is sound.

**TNK-UNIFY-002 — Supported theories.** Non-ground unification supports free and iteration operators, commutative/identity CUI combinations without idempotence, AC/ACU, and associative/AU word theories. It combines theory solved forms with maximal order-sorted assignments. ACU solving is finitary. AU solving may discover an infinite family or reach a bounded nonlinear exploration, in which case the low-level problem is incomplete.

**TNK-UNIFY-003 — Unsupported theories.** A non-ground subterm under an idempotent CUI operator or under an associative operator with a one-sided identity is an Unsupported unification problem. The low-level `UnifyProblem` marks `problem_okay = false` and yields no ordinary stream. Ground terms under those operators remain comparable/canonicalizable.

**TNK-UNIFY-004 — Completion.** Low-level finite exhaustion with `is_incomplete() == false` means the returned set is complete for the implemented theories. `is_incomplete() == true` means returned unifiers remain sound but completeness is not claimed. “No unifier,” “unsupported theory,” and “incomplete exploration” are distinct semantic outcomes.

The object-level Session renderer does not currently expose `UnifyProblem::is_incomplete`, unsupported-theory readiness, or a completion marker and is therefore an Experimental presentation boundary for completeness-sensitive clients. An unsupported ordinary unification command can produce only its command echo, as recorded in Appendix H.4. The Session also does not save an ordinary-unification continuation. Use the low-level API when the distinction is required.

`irredundant unify` filters the collected stream to a minimal complete set under substitution instantiation. Result order and fresh-variable spelling are Implementation-defined.

## 13. Variants and narrowing

### 13.1 Folding variants

```text
get variants [n] [in M :] term [such that B1, ... irreducible] .
get irredundant variants [n] [in M :] term [such that ... irreducible] .
```

**TNK-VARIANT-001 — Variant meaning.** A variant consists of an equation-normal form and the accumulated substitution for the original variables, generated by narrowing with executable `[variant]` equations modulo operator axioms. The initial renamed/reduced term is the first incremental variant. Folding removes states subsumed by retained variants.

Incremental mode exposes completed layers as they become available. Irredundant mode computes to exhaustion before exposing the final surviving set. The latter may therefore fail to return a first result on a nonterminating variant theory.

**TNK-VARIANT-002 — Irreducibility blockers.** Every `such that ... irreducible` term is normalized and must not be reducible by a variant equation. A reducible blocker rejects the query. Blockers constrain generated unifiers; they are not post-hoc text filters.

### 13.2 Variant unification and matching

```text
variant unify [n] [in M :] u =? v [ /\ ... ] [such that ... irreducible] .
filtered variant unify [n] [in M :] ... .
variant match [n] [in M :] pattern <=? subject [such that ... irreducible] .
```

**TNK-VARIANT-003 — Variant unification.** Variant unification completes simultaneous unification over generated variants. `filtered` computes the retained non-subsumed result set before presentation; plain mode may stream results. Returned unifiers are sound. A final completeness claim requires both variant exploration and all nested unifiers to exhaust without an incomplete flag.

**TNK-VARIANT-004 — Variant matching.** Variant matching treats variables in the subject as distinct symbolic constants while solving, then restores them in returned bindings. The Session saves the same variant-unifier stream as a continuation with `matching = true`. Matchers are filtered through the same variant-instance relation when requested by the operation.

### 13.3 Variant-based narrowing

```text
[{fold|vfold|path}, ...] vu-narrow [{filter|delay}, ...]
  [n] or [n,m] [in M :] initial ARROW goal [such that condition] .

fvu-narrow ...
```

`fvu-narrow` implies fold mode. Prefix options select state folding and retained path data; the post-command option block selects unifier filtering and delayed filtering.

**TNK-NARROW-001 — Narrowing graph.** Narrowing uses rules marked `[narrowing]`, including such rules marked `[nonexec]`. Conditional narrowing rules are Unsupported. In the current loader, such a rule is diagnosed and dropped as one invalid statement while the enclosing module and later valid statements are retained; Appendix H.4 records the exact recovery boundary. Narrowing explores non-variable, non-frozen positions and composes rule unifiers with each state's accumulated substitution. Below an associative-commutative operator, the copies of a repeated element are one position; equal arguments of other operators are separate positions. When the two arguments of a commutative operator are equal, both choices give the same states modulo commutativity, and narrowing may explore only one of them.

**TNK-NARROW-002 — Search options.** `fold` removes states matched by retained states. `vfold` uses variant subsumption. `filter` retains most-general unifiers; `delay` defers that filtering as defined by the search. `path` retains step substitutions and rule/position records for `show path`. `=>1`, `=>+`, `=>*`, and `=>!` have the same depth qualification as ordinary search; the second bound is narrowing depth.

**TNK-NARROW-003 — Outcomes.** Returned narrowing solutions are sound and include the accumulated original-variable substitution. Finite exhaustion is complete only if no nested unification/variant solver reported incompleteness and no user depth bound truncated exploration.

Inspection commands for the last narrowing search are `show frontier states .`, `show most general states .`, `show path N .`, and `show path states N .`.

## 14. SMT-constrained operations

### 14.1 Build profiles

The `smt-z3` feature on `tnk-core`, forwarded by same-named features on `tnk-session` and `tnk-repl`, selects the native Z3 backend. The default build uses a null backend. At workspace scope, `--all-features` enables the per-crate features; there is no root package feature.

**TNK-SMT-001 — Optional backend.** With `smt-z3`, a well-formed supported SMT formula returns `Sat`, `Unsat`, `Unknown`, or `BadDag` according to translation and solver outcome. Without it, SMT checks return `Unknown`; they MUST NOT pretend satisfiability or unsatisfiability. Push, pop, and clear remain safe no-ops on the null backend. Merely compiling the feature is not evidence that a provisioned Z3 backend solved a query.

### 14.2 Check and SMT search

```text
check [in M :] formula .
smt-search [n] or [n,m] [in M :] initial ARROW goal [such that constraint] .
```

**TNK-SMT-002 — Formula surface.** SMT sorts and operators exist only when resolved from loaded hooks. TNK supports Boolean, integer, and real SMT values; Boolean connectives; arithmetic; comparisons; divisibility; integer tests; and the hook-defined conversions represented by the SMT operator catalogue. Unsupported operator/arity bindings reject the hook at build time.

**TNK-SMT-003 — SMT search.** SMT search carries an accumulated constraint with each rewrite state. A successor or goal match is retained only when the selected backend returns `Sat` for its constraint; `Unsat`, `Unknown`, and `BadDag` are all pruned, but only `Unsat` proves impossibility. Goal matching adds its constraint and returns the symbolic state, non-SMT bindings, and final `where` formula. It supports `=>1`, `=>+`, and `=>*`; `=>!` is Unsupported. Completeness therefore requires a backend that decides every encountered constraint; the default null backend cannot establish constrained reachability.

A `Sat`/`Unsat` answer is semantic. `Unknown` is not `Sat`, and a malformed/untranslatable DAG is not `Unsat`.

## 15. LTL and variant satisfiability

### 15.1 LTL

LTL model checking and LTL satisfiability are hooked operators supplied by a loaded library surface (normally `model-checker.maude`). They are not standalone parser commands.

**TNK-LTL-001 — Model checking.** The model checker builds the ordinary reduced rewrite graph lazily and checks the synchronous product with the negated property using nested DFS. A deadlock state has a self-loop for LTL semantics only; ordinary `search` still reports it as terminal. A counterexample records a finite lead-in and accepting cycle in the result representation supplied by the loaded hooks.

**TNK-LTL-002 — Formula semantics.** Supported formulas include propositions, Boolean connectives, next, until, and release; derived temporal operators are reduced through the loaded formula equations/hooks. Formula construction and automata simplification must preserve the accepted infinite-word language. Exact internal VWAA/Büchi state numbers, BDD variable numbers, and automaton dumps are not public contracts.

**TNK-LTL-003 — Termination.** Finite reachable graphs yield a decision. Infinite-state rewriting may make model checking diverge; there is no implicit cutoff.

### 15.2 Variant satisfiability

The TNK-authored `share/tnk/variant-satisfiability.maude` facade exposes native variant satisfiability.

**TNK-VSAT-001 — Decision domain.** Variant satisfiability is a separate procedure from SMT. It decides supported formulas over FVP, OS-compact constructor theories using constructor analysis, folding variants, and order-sorted unification. Eligibility rejection is distinct from `Sat` and `Unsat`. Explicit sort overrides may resolve identity-classification cases where inference is insufficient.

## 16. Built-ins, reflection, and objects

### 16.1 Built-in classes

When the loaded signature supplies valid hooks, TNK implements these classes:

- structural equality and initial/decomposing equality;
- lazy branch/conditional selection;
- arbitrary-precision natural/integer arithmetic, bit operations, comparisons, gcd/lcm/min/max, division and rational canonicalization;
- deterministic MT19937 `random(n)` seeded with zero;
- the per-rewrite-command stateful `counter` special;
- string concatenation, indexing/search, conversion, case, trim, comparison, and ASCII/C-locale character predicates;
- IEEE float arithmetic, common elementary functions, comparison, and numeric/string conversions;
- quoted-identifier/string conversion;
- SMT, LTL model checking, LTL satisfiability;
- META-LEVEL and LEXICAL descent operations listed below;
- local meta-interpreter and standard-stream external managers.

**TNK-BUILTIN-001 — Fallthrough.** A partial built-in applied outside its domain does not invent a value. It remains unreduced or falls through to user equations as appropriate. Division by zero, invalid character conversion, malformed Qid conversion, and negative results in a natural-only family follow this rule unless the loaded source defines an equation for them.

`counter` is inert under `reduce`; during `rewrite`/`frewrite` it yields `0,1,2,...` and resets for each new top-level rewriting command, not for `continue`. This holds separately for each `CounterSymbol`-attached operator: every such operator has its own sequence, no other counter operator advances it, and all of them reset together.

### 16.1.1 Strict Rust reducers

Strict Rust reducers are an **Optional** host capability. They are in-process, trusted Rust implementations of pure deterministic equational functions—not dynamic plugins and not general evaluator-control hooks.

**TNK-HOST-001 — Capability binding.** A host constructs one immutable `tnk_core::host::HostFunctionCatalog` before module construction and supplies it through `Session::builder().host_functions(...)`, a catalog-aware frontend/module loader, or `Engine::with_host_functions`. Source binds one operator with:

```maude
[special (id-hook HostFunctionSymbol (text.normalize-tag)
          op-hook stringSymbol (<Strings> : ~> String))]
```

The key is a dotted lowercase identifier matching `^[a-z](?:[a-z0-9-]*[a-z0-9])?(?:\.[a-z](?:[a-z0-9-]*[a-z0-9])?)+$`. Each segment starts with `a`–`z`, continues with lowercase ASCII letters, digits, or interior `-`, and cannot end in `-`; at least one `.` separates two segments. Registration and source use the same canonical spelling. Keys name capabilities, not Rust paths or dynamic-library symbols. Duplicate registrations fail. Missing keys, duplicate bindings, mismatched arity, non-free root theories, nonstandard strategies, polymorphic declarations, incompatible overload profiles, and missing/unexpected or sort-incompatible supporting hooks reject attachment before semantic execution. A valid binding is sealed when semantic execution begins and cannot be replaced in that Engine. Module sums, renaming, views, parameter instantiation, dependent rebuilds, reflection, and child interpreters preserve the configured catalog and transform TNK hook references without changing the key.

**TNK-HOST-002 — Invocation and precedence.** The attached root must have fixed arity, free theory, and the standard left-to-right eager schedule. TNK normalizes every direct argument at the active equation epoch, then invokes the reducer once at the final top attempt. `StrictOutcome::Decline` adds no rewrite and falls through to ordinary equations, then `[owise]`. `StrictOutcome::Reduced` suppresses both equation classes, counts one host rewrite, validates the returned term against the selected declaration range, and resumes ordinary normalization from the returned term. Its structured trace identity is `TraceEvent::Rewrite { kind: RewriteKind::HostFunction, host_key: Some(canonical_key), ... }`; every other `TraceEvent::Rewrite` has `host_key: None`. Rendered host trace output includes that same canonical key, never only a catalog- or signature-relative dense ID. Renaming can change the rendered TNK redex/result but not the host key. A normal argument may be symbolic or may contain descendants suspended by their own strategy; normality does not imply groundness or native decodability.

**TNK-HOST-003 — Scoped callback boundary.** `StrictReducer::reduce` receives `StrictCall`, callback-scoped `NormalDag` arguments and `RedexDag`, and a `StrictReduceCtx`. `StrictCall::hooks()` returns `ScopedHostHooks<'ctx>`; its purpose lookups return opaque invariant-lifetime `HostSymbol<'ctx>` construction capabilities rather than raw hook IDs. `StrictCall::argument(position)` panics outside `arguments()`, and scoped hook lookups panic for a purpose absent from the successfully bound descriptor. The context can inspect `DagView`/`ChildView`, test groundness, fallibly decode supported native values, reuse an argument, and build constants, applications, or byte strings through the active signature. Its raw `top` result is observation-only and cannot be passed to a builder. `StrictReduceCtx::app` is theory-aware rather than free-only: after checking signature membership, arity, and a compatible declaration, it routes construction through the active free/ACU/AU/CUI representation, including declared associativity, commutativity, idempotence, and identity canonicalization/collapse. The context exposes no raw `DagId`, owning `Engine`, signature mutation, nested reduction, or collection API. `BuiltDag` proves same-callback construction/provenance, not normality. Returned terms from another kind, the kind error sort, or a sort not below the selected range are reducer faults and never become decline.

**TNK-HOST-004 — Fault, atomicity, and trust boundary.** `ReducerFault` is an implementation or contract failure, distinct from domain decline. The owning fallible semantic operation restores its TNK-owned checkpoint: aggregate and breakdown counts, trace/event append state, and operation state roll back; no ordinary-equation or `[owise]` fallback is attempted. A resumable owner is faulted and returns the same fault on later calls. Session commands render one `error: strict reducer ... failed: ...` diagnostic and retain no continuation. Lower-level embeddings use fallible operations such as `Engine::try_reduce`, `Rewriting::try_run`, and `Search::try_next_solution`; corresponding infallible convenience methods panic on `ReducerFault` as stated in their `# Panics` sections. This atomicity does not roll back callback-authored external side effects. A callback panic is a trusted-code panic: TNK neither catches nor converts it to `ReducerFault`, guarantees rollback, nor guarantees process survival; it follows the embedding's Rust unwind/abort policy. Every `StrictReducer` and typed callback MUST be deterministic and referentially transparent for the canonical redex, immutable signature, and binding. It MUST NOT make ordinary reduction depend on time, I/O, randomness, nondeterministic services, mutable result-affecting host state, or externally visible side effects. Callback execution is synchronous and offers no cancellation token, timeout, async yield, preemption, general user transaction, or callback-side-effect rollback; it may diverge, block, or exhaust CPU/memory. Reducer authors are responsible for termination and resource bounds, and hosts evaluating untrusted callbacks or terms must enforce interruption through outer process isolation.

### 16.2 Reflection

The reflection layer supports native descent for reduction/normalization, rewrite/frewrite/apply/xapply, match/xmatch, search/path, SMT check/search, sort queries, parsing/printing, well-formedness, up/down term and module/view components, unification, variants, variant matching, narrowing, strategy rewrite, and LEXICAL tokenize/printTokens when their hook signatures resolve.

`metaXmatch` and `metaXapply` number their solutions across the positions of the reduced subject. Below an associative-commutative operator, the copies of a repeated element are one position, so a match or rewrite inside a repeated element is reported once, not once per copy. Equal arguments of any other operator are separate positions.

**TNK-META-001 — Owned boundary.** Reflected module/term values are translated at the module/session boundary. Engine-local IDs never cross a child-interpreter or external-manager boundary. A metalevel operation whose `MetaOp` is `Unknown`, whose reflected value is malformed, or whose required hook cannot resolve remains inert or returns the loaded facade's explicit failure value; it MUST NOT dispatch to an unrelated operation.

**TNK-META-002 — Current limitations.** Conditional `metaMatch` constraints are Unsupported. The separately recognized state-only `metaNarrow2` path is inert. General up-mapping of some flat modules containing special/poly declarations may remain deferred; named-module facade requests are handled directly where specified by the loaded meta-interpreter surface.

### 16.3 Object modules and local interpreters

Object module `class`, `subclass`, and `msg` declarations are desugared to ordinary signature declarations; `CONFIGURATION` is imported implicitly. Object patterns are completed with an attribute-set variable, and class constants in patterns are generalized to class-sorted variables, as limited by `TNK-OO-002`.

**TNK-OO-001 — Local interpreter isolation.** A local interpreter is an independent child `Session` owned by its parent. Its module/current/continuation state does not alias the parent. Requests and replies use owned reflected envelopes. Create, operation, and quit are synchronous; malformed or invalidated target traffic is rejected without consuming the request.

**TNK-OO-002 — Object-pattern completion.** Completion transforms an object-module statement as a whole or leaves it exactly as written; either way the result is then checked like any other statement (`TNK-COND-002`, `TNK-STMT-001`). Completion applies to the statements that an object module or theory declares, in that module and in every module that imports them, directly, transitively, through a renaming or an instantiation, or through a parameter theory, whether or not the importing module is itself an object module. An object term on the right side or in the condition whose object name is the same term as that of a left-side object pattern is another occurrence of that object. A statement in which such an occurrence carries a class argument different from the pattern's changes the object's class and is left as written, whether the pattern's class argument is a class constant or a class variable. An attribute term has a unary head operator: a statement in which the attribute set of a left-side object pattern, or of another occurrence of that object, contains an element whose head operator ranges on a strict subsort of `AttributeSet` but is not unary, such as an `Attribute`-sorted constant, is left as written. A variable that completion introduces has a base name that no variable of the statement uses, so printing or reflecting the completed statement keeps it distinct from the statement's own variables; its spelling is otherwise Implementation-defined (Appendix K.3). Which unary operators are attribute operators, the other conditions under which completion leaves a statement as written, whether doing so is reported, and whether an object module or theory also completes the statements it imports from non-object modules are not specified here.

---

# Part IV — Session, presentation, and CLI

## 17. Session state machine

`tnk_session::Session` is the primary host API. `Session::eval(input, color)` synchronously evaluates one submission and returns:

```rust
pub struct Eval {
    pub output: String,
    pub exit: bool,
}
```

`Eval` is a presentation result, not a typed semantic event stream. It has no structured diagnostic, completion, unsupported, or resource-exhaustion field.

**TNK-SESSION-001 — Persistence.** A Session persistently owns its interner, parsed and built module/view databases, current module, settings, reflection caches, local interpreters, loaded-file set, and at most one continuation. Independent Session values share no semantic state.

**TNK-SESSION-002 — Submission boundary.** A submission may contain several complete top-level statements on separate physical lines. Definitions and commands run in source order. Two commands on one physical line are parsed as one invalid command submission. A module/view followed by commands on later lines is permitted. Output blocks are joined by a single newline and the final output has no trailing newline.

**TNK-SESSION-003 — Completeness probe.** `input_complete` returns true for a complete module/view terminator, a top-level period, a line-terminated `load`/`sload`, or bare `quit`/`q`/`exit`. It returns false for blank/comment-only input and incomplete module nesting. The probe may intern tokens into the Session but MUST NOT execute semantic state transitions.

**TNK-SESSION-004 — Synchronous execution.** `eval` does not return until the submission completes, reaches its command bound, or fails. There is no cancellation token, timeout, thread-safety, or reentrancy guarantee. Hosts requiring interruption MUST isolate execution at a process boundary.

### 17.1 Current module and inspection

```text
select NAME .
show modules .
show module [NAME] .
show views .
show view NAME .
show path [states] N .
show search graph .
show frontier states .
show most general states .
```

**TNK-SESSION-005 — Selection.** Successfully entering a module makes it current. `select NAME .` changes the current module only if the named built module exists and always clears the continuation, even when `NAME` was already current. `in M :` never changes current selection. Continuation inspection requires the originating module still to be current.

A `select` that names no built module, an unknown `show` form, and an inspection that cannot be displayed (no current module, or an absent module, view, search graph, narrowing graph, state, or state number) emit an `error:` diagnostic; Appendix D.1 gives the `parse error:` case for a `show` that shares a physical line with a definition. A rejected `select` leaves the current module unchanged. A rejected `show` leaves the current module, the continuation, and all settings unchanged.

### 17.2 Settings

```text
set trace [condition|whole|substitution|rewrite|body|builtin|eqs|mbs|rls] on|off .
set include BOOL on|off .
set show breakdown on|off .
set verbose on|off .
set show timing on|off .
set memo ... .
set clear memo .
do clear memo .
```

**TNK-SESSION-006 — Settings.** Trace is off by default. `include BOOL` is off in a bare Session; while on, a newly entered module receives an implicit `including BOOL .` if `BOOL` exists. Breakdown and verbose output are off by default. Timing measurement and memoization controls are Unsupported: enabling timing or using memo controls emits an unavailable-capability warning and has no semantic effect. Other unknown `set` controls are currently silent no-ops and are Implementation-defined recovery, not supported features.

A `set trace` request outside the form above (an unknown section, a value other than `on` or `off`, or a missing or extra word) is rejected with an `error:` diagnostic and changes no trace flag.

### 17.3 Loading

`load FILE` and `sload FILE` are line-terminated and do not require a period.

**TNK-LOAD-001 — Resolution.** Session `load FILE`/`sload FILE` tries the written path and then the path with `.maude` appended, first relative to the process working directory and then under each nonempty colon-separated directory in `MAUDE_LIB`. It reads UTF-8 source and evaluates it in the current Session. It does not resolve a nested load relative to the containing source file.

**TNK-LOAD-002 — Skip load.** `sload` canonicalizes a found path and silently skips it after the first load in that Session. `load` always evaluates it again. A missing/unreadable file produces an `error:` result and leaves semantic state intact except for token interning. The CLI's positional `FILE` is different: it is read exactly as written, without `.maude` completion or `MAUDE_LIB` search, and read failure is written to stderr.

### 17.4 Exit

`quit`, `q`, and `exit` set `Eval.exit = true` and produce `Bye.`. A library host decides what that means; `Session` does not terminate the process.

## 18. Output contract

### 18.1 Semantic records

**TNK-OUT-001 — Current text records.** At the Session boundary, these semantic fields are Stable when their command emits them:

- a reduce/rewrite result identifies its least sort (or explicit unknown-sort state) and term;
- a match/unifier/variant/search/narrowing record is numbered and includes its complete displayed substitution/result fields;
- an empty substitution is printed explicitly rather than by omitting the result;
- `No match.`, `No unifier.`, `No solution.`, and `No more ...` remain distinct human records;
- search solutions identify graph state plus state/rewrite statistics;
- SMT-search solutions identify symbolic state and final `where` constraint;
- diagnostic lines begin with `parse error:`, `error:`, or `warning:` according to current category.

Finite exhaustion versus a bound stop is visible only for renderers that emit a `No more ...` record. Ordinary unification and some unsupported/error paths expose no complete machine-readable classification. Clients requiring typed outcomes use the lower-level APIs.

**TNK-OUT-002 — Term rendering.** Pretty-printing MUST produce a term that reparses to a semantically equal term in the same module, subject to literal and supported grammar boundaries. It honors mixfix syntax, precedence/gather, `format`, sort disambiguation, and variable names. ANSI color never changes non-color text. Incidental parenthesis choice, whitespace, and internal AC argument order are not stable unless this Reference names the case.

**TNK-OUT-003 — Diagnostics.** At the current text boundary, severity prefix and documented state effect are Stable; full prose, punctuation, and incidental source context are human-oriented and Experimental. `Eval` does not expose structured categories. Production clients MUST NOT infer semantic control flow by matching arbitrary prose; if the stable prefix is insufficient, use a typed lower-layer `Result` or treat the operation as not programmatically classifiable.

### 18.2 Rewrite accounting

The aggregate `rewrites:` value includes successful equational/built-in replacements, membership lowerings, rule applications, symbolic variant-narrowing/narrowing steps, condition work, and explicitly transferred metalevel/external work as performed by that command. Breakdown mode reports membership, rule, variant-narrowing, and narrowing subcounts already included in the aggregate.

**TNK-COUNT-001 — Accounting scope.** A local successful equation, membership lowering, rule application, variant-narrowing step, or narrowing step contributes exactly once at its defined seam. Failed attempts do not contribute that seam's unit. A top-level command resets aggregate accounting as defined by its driver; `continue` extends the same operation.

**TNK-COUNT-002 — Diagnostic totals.** Exact large aggregate totals are diagnostic, not mathematical semantics. Evaluation strategy, canonical construction reuse, condition scheduling, and equivalent built-in implementations may change them. Clients MUST rely on exact totals only where a clause specifically defines accounting.

### 18.3 Terminal adapter

`tnk_repl::Repl` wraps `Session` and applies output wrapping once. It uses an 80-column model, keeps column 79 clear, indents continuation lines by four spaces, and breaks only at legal ASCII boundaries outside strings/ANSI sequences. Oversized tokens remain intact. The Session itself returns unwrapped output.

## 19. Command-line executable

The binary accepts:

```text
tnk-repl [-no-prelude] [-no-banner] [FILE]
```

The first non-flag argument is loaded as source. A second file argument or an unknown flag is an argument error reported to stderr with process status `2`.

**TNK-CLI-001 — Startup.** Unless `-no-banner` is supplied, the binary prints its banner. Unless `-no-prelude` is supplied, it searches `MAUDE_LIB` and then the current directory for `prelude.maude`; failure prints a warning and continues without a prelude. It then loads the optional file and enters the input loop.

Color is enabled only when stdout is a terminal. Prompts/history are enabled for terminal input. `Ctrl-C` abandons the current input buffer; `Ctrl-D` exits. A requested file or located prelude that cannot be read is reported to stderr with process status `1`; a prelude that cannot be located emits a warning and continues successfully without one. Evaluation diagnostics inside a readable file remain Session output and do not currently force a nonzero process exit.

Recommended prelude-free invocation:

```sh
cargo run --release -p tnk-repl -- -no-banner -no-prelude program.maude
```

---

# Part V — Rust embedding APIs

## 20. Primary Session API

```rust
use tnk_session::Session;

let mut session = Session::new();
let entered = session.eval(
    "fmod BOOLISH is sort B . ops t f : -> B . endfm",
    false,
);
assert!(!entered.exit);
assert_eq!(session.current(), Some("BOOLISH"));

let reduced = session.eval("reduce t .", false);
assert_eq!(
    reduced.output,
    "reduce in BOOLISH : t .\nrewrites: 0\nresult B: t"
);
```

**TNK-API-001 — Host ownership.** The host owns a mutable `Session` and passes complete submissions to `Session::eval`. Interactive partial input is first accumulated by the host using `Session::input_complete`; `Session::eval` itself is not a cross-call input buffer. It returns unwrapped text and never writes stdout/stderr. `Session::set_stdin` replaces the scripted input consumed by later `erewrite` `getLine` requests. `Session::current` exposes the selected module name.

`Eval.output` is presentation suitable for display, not typed control flow. A host needing typed values or completion uses the lower-level APIs; the current crate has no typed Session result surface.

Configure a typed byte-string reducer before entering any module:

```rust
use tnk_core::host::{HostFunctionCatalog, codecs};
use tnk_session::Session;

fn normalize_tag(input: &[u8]) -> Vec<u8> {
    let mut output = Vec::with_capacity(input.len());
    let mut separator = false;
    for &byte in input {
        if byte.is_ascii_alphanumeric() {
            if separator && !output.is_empty() {
                output.push(b'-');
            }
            output.push(byte.to_ascii_lowercase());
            separator = false;
        } else {
            separator = !output.is_empty();
        }
    }
    output
}

let catalog = HostFunctionCatalog::builder()
    .register_typed1(
        "text.normalize-tag",
        codecs::string(),
        codecs::string(),
        normalize_tag,
    )
    .expect("register text.normalize-tag")
    .build();
let mut session = Session::builder().host_functions(catalog).build();

let entered = session.eval(
    r#"fmod HOST-TEXT is
         sort String .
         op <Strings> : -> String
           [ctor special (id-hook StringSymbol)] .
         op normalizeTag : String -> String
           [special (id-hook HostFunctionSymbol (text.normalize-tag)
                     op-hook stringSymbol (<Strings> : ~> String))] .
       endfm"#,
    false,
);
assert_eq!(entered.output, "");

let reduced = session.eval(
    r#"reduce in HOST-TEXT : normalizeTag(" Release / V1 ") ."#,
    false,
);
assert!(reduced.output.contains(r#"result String: "release-v1""#));
```

The typed adapters borrow each decoded TNK byte-string payload directly as `&[u8]`, without cloning the input bytes or allocating an input buffer. `register_typed2` decodes both arguments before invoking the callback; if either decode misses, the adapter declines without calling it. The callback returns an owned `Vec<u8>`, which is encoded as a new TNK byte string through the descriptor-required, signature-resolved `stringSymbol`; that nullary marker must satisfy every declared argument/result compatibility check. Use the lower-level `StrictReducer` trait and `StrictReducerDescriptor` when a reducer must inspect symbolic DAGs, require declaration-relative `op-hook`/`term-hook` symbols, build another term shape, or report `ReducerFault`.

## 21. Frontend and module APIs

The reusable source pipeline and its principal entry points are:

| Layer | Entry points | Result/error boundary |
|---|---|---|
| lexical | `lex::Interner`, `lex::tokenize` | token vector; lexer recovery is represented by token classes |
| surface | `surface::parser::Parser::new`, `parse_top_item`, `parse_source` | `Result<..., String>` plus retained module diagnostics |
| grammar | `grammar::build::compile_module_grammar`, `cfparser::parse_forest`/`parse_forest_pick` | compiled grammar or parse/effort error |
| direct frontend | `load::{load_source,load_source_with_host_functions,build_loaded_module,build_loaded_module_with_host_functions,try_build_loaded_module_with_host_functions,build_loaded_module_with_host_functions_and_inline_statements,try_build_loaded_module_with_host_functions_and_inline_statements}`; homed/traced string and typed build variants; public `sig::build_sig::build_module`; command builders; `pretty::print_pretty` | `LoadedModule`/command owner, string diagnostic, or typed `LoadedModuleBuildError::{Invalid,Reducer}` |
| module algebra | `ModuleDb`, `ViewDb`, `validate_view`, `flatten_and_build`, `load_program` and their `_with_host_functions` variants | transactional `Result` at composition/build boundary |
| Session | `Session::{new,builder,input_complete,eval,set_stdin,current}`, `SessionBuilder::host_functions` | unwrapped `Eval` text/exit flag |
| terminal | `Repl::{new,input_complete,eval,set_stdin,current}` | wrapped `Eval`; binary owns actual terminal I/O |

**TNK-API-002 — Shared interner.** Tokens, module source, built variable names, and pretty-printing that exchange raw intern indices MUST use the same `Interner`. Intern indices are process-local implementation data, not persistent IDs.
`tnk_frontend::load_source` builds one import-free source directly. A source containing imports must go through `tnk-modules` flattening. This distinction is Stable.

## 22. Kernel API

`tnk_core::Engine` can be used without source syntax. The primary sequence is `Engine::new`, `add_sort`/`add_subsort`, `close_sorts`, signature declaration/hook registration, `Term` construction and `instantiate`, then reduction, match, rewriting, search, unification, variant, narrowing, SMT, or LTL owners. `SortId`, `KindId`, `SymbolId`, and `DagId` are engine-relative handles. `RootGuard` pins a DAG across GC-capable calls.

For strict host reducers, construct an immutable `HostFunctionCatalog`, create the Engine with `Engine::with_host_functions`, build signature-local supporting-hook inputs with `ResolvedHostHooks::builder`, and call `validate_host_function_binding`/`bind_host_function` before semantic execution. `ResolvedHostHooks` is build-time binding data; its raw symbol lookup is not callback API. A `StrictCall` instead exposes `ScopedHostHooks<'ctx>`, whose purpose lookups produce opaque invariant-lifetime `HostSymbol<'ctx>` construction capabilities. The binding is sealed after execution begins; construct a new Engine to change catalog semantics. Callback-facing proof wrappers and theory-aware builders are in `tnk_core::host`.

**TNK-API-003 — Engine isolation.** Every ID is relative to one Engine. An Engine is instance state; there is no global signature or DAG arena. A client MUST close sorts before operations that require kinds and MUST finish signature mutation before relying on cached term sorts. It MUST root DAGs that survive a GC-capable call. Passing a stale or cross-engine ID, mutating the signature out of order, or indexing a missing substitution slot violates a Rust API precondition and may panic; accepted source text must not reach those paths.

**TNK-API-004 — Resumable owners.** `Rewriting`, `Search`, `SmtSearch`, `VariantSearch`, `FilteredVariantUnifierStream`, and `NarrowSearch` retain the roots/traversal state needed between calls while borrowing an Engine only for each advancement. Dropping an owner releases its roots. The caller MUST resume with the same Engine and compatible signature. Each advancement returns a typed step/solution or `None`; algorithm-specific `incomplete` flags remain separate from exhaustion.

**TNK-API-005 — Compatibility level.** The workspace is version `0.1.0`; Rust source compatibility, exhaustive enum shape, and module path stability are Experimental. Engine memory safety, instance isolation, result soundness, and every Stable semantic clause remain release contracts.

---

# Part VI — Feature matrix and explicit boundaries

## 23. Current feature classification

| Surface | State | Profile / boundary | Primary contract |
|---|---|---|---|
| sort posets, kinds, overloading, partial operators | Stable | all | `TNK-SORT-*` |
| tokenization and literal classes | Stable | all | `TNK-LEX-*` |
| mixfix parse/print semantic roundtrip | Stable | all | `TNK-PARSE-001`, `003`, `TNK-OUT-002` |
| first-packed-parse choices on named command bubbles | Experimental | all; disambiguate portable source | `TNK-PARSE-002` |
| equations, memberships, executable conditions | Stable | all | `TNK-REDUCE-*`, `TNK-MB-*`, `TNK-COND-*` |
| free/AU/ACU/CUI canonicalization and matching | Stable | listed theory boundary | `TNK-TERM-*`, `TNK-MATCH-*` |
| rule semantics, rule-fair/position-fair rewriting, BFS search | Stable | model obligations in `TNK-RULE-002` | `TNK-RULE-*`, `TNK-REWRITE-001/002`, `TNK-SEARCH-*` |
| saved-operation continuation without an intervening command | Stable | supported owners only | `TNK-CONT-001` |
| failed-command continuation invalidation details | Experimental | Session renderer | `TNK-CONT-001` |
| current invalid-input recovery and diagnostic gaps | Experimental | incorrect input only; do not rely on it | `TNK-RECOVERY-001`, Appendix H.4 |
| external/object rewriting, streams, child interpreters | Experimental | hook-loaded object modules | `TNK-REWRITE-003`, `TNK-OO-001` |
| strategy combinators and unconditional definitions | Stable | strategy modules | `TNK-STRAT-*` |
| order-sorted unification | Stable | theories in `TNK-UNIFY-002` | `TNK-UNIFY-*` |
| variants, variant unify/match, narrowing | Experimental | finite/incomplete boundary explicit | `TNK-VARIANT-*`, `TNK-NARROW-*` |
| variant satisfiability | Experimental | loaded TNK facade | `TNK-VSAT-001` |
| SMT null backend | Stable | default; answer `Unknown` | `TNK-SMT-001` |
| native Z3 backend | Optional | per-crate `smt-z3` feature + provisioned Z3 | `TNK-SMT-*` |
| LTL model checking/satisfiability | Optional | hooks resolved from loaded modules | `TNK-LTL-*` |
| ordinary flattening, sums, structural renaming | Stable | all | `TNK-MOD-002/005/006/007` |
| import-mode protection obligations | Experimental | modes currently donate equally | `TNK-MOD-003` |
| parameter instantiation and full view validation | Experimental | deferred cases named in §5.5 | `TNK-MOD-004`, `TNK-VIEW-001` |
| object-module desugaring | Experimental | object modules | `TNK-OO-002` |
| listed reflection descent | Experimental | loaded hook/facade capability | `TNK-META-*` |
| built-in operator families | Optional | only after hooks resolve | `TNK-BUILTIN-001`, Appendix G |
| strict host-provided Rust reducers | Optional | configured immutable `HostFunctionCatalog`; trusted in-process callbacks | `TNK-HOST-*`, Appendix G.3 |
| semantic term rendering | Stable | supported grammar/literal domain | `TNK-OUT-002` |
| Session text record/completion schema | Experimental | `Eval` is not typed | `TNK-OUT-001/003` |
| exact large aggregate rewrite totals | Experimental diagnostic | not a semantic contract | `TNK-COUNT-002` |
| Rust API source compatibility | Experimental | workspace version `0.1.0` | `TNK-API-005` |
| terminal wrapper and CLI | Experimental | host/TTY/process environment | `TNK-CLI-001` |

Output spelling, enumeration order, warning prose, and aggregate-count parity with other implementations are not TNK conformance guarantees.

## 24. Unsupported and intentionally absent behavior

The following boundaries are explicit:

1. Memoization attributes/controls have no execution semantics.
2. Timing measurement is unavailable.
3. `xmatchrew` and conditional `csd` are rejected.
4. Conditional `[narrowing]` rules are diagnosed and dropped while the rest of a buildable module is retained.
5. Non-ground unification under CUI idempotence or associative one-sided identity is rejected as unsupported.
6. `smt-search =>!` is unsupported.
7. Without `smt-z3`, SMT answers are `Unknown`.
8. Conditional `metaMatch` is unsupported; deferred metalevel hook codes stay inert.
9. Ordinary search tracing is unsupported; graph/path inspection remains available.
10. Import modes do not enforce protection obligations.
11. LaTeX and filename scanner modes are outside the TNK source lexer.
12. There is no evaluation cancellation API, semantic timeout, general transaction rollback beyond the documented `ReducerFault` atomicity, or concurrency guarantee.
13. Strict reducers cannot implement lazy selection, evaluator-controlled argument demand, stateful/nondeterministic computation, asynchronous work, or external I/O; those require a different control/rewrite/external contract.

**TNK-BOUNDARY-001 — No silent success.** Unsupported behavior MUST NOT be reported as a successful semantic result. A recognized inert hook may leave its term unreduced, but that is an explicit Unsupported outcome, not evidence the operation ran.

## 25. Resource and completeness boundaries

**TNK-RESOURCE-001 — Unbounded work.** Equational reduction, rewrite conditions, rewriting, search, strategy iteration, variants, narrowing, model checking, and solver enumeration can diverge on accepted input. A missing result before external interruption says nothing about validity.

**TNK-RESOURCE-002 — Explicit classifications.** Low-level algorithms that own an internal completeness signal expose it. User bounds, parser effort exhaustion, backend `Unknown`, solver incompleteness, unsupported theory, and finite no-solution remain distinct facts. The `Eval` text surface does not expose every distinction; completeness-sensitive clients use the typed lower-level APIs.

---

# Part VII — Worked normative examples

## 26. Equational normalization

```maude
fmod NAT-MINI is
  sort Nat .
  op z : -> Nat [ctor] .
  op s_ : Nat -> Nat [ctor] .
  op _+_ : Nat Nat -> Nat .

  vars M N : Nat .
  eq z + N = N .
  eq (s M) + N = s (M + N) .
endfm

reduce (s z) + (s (s z)) .
```

By `TNK-TERM-002`, `TNK-TERM-003`, and `TNK-REDUCE-001`, the result is the normal form denoting three successors of `z`, at sort `Nat`. The exact number of aggregate rewrites is not the arithmetic specification.

## 27. Reachability and continuation

```maude
mod LIGHT is
  sort State .
  ops off on broken : -> State [ctor] .
  rl [flip-on]  : off => on .
  rl [flip-off] : on  => off .
  rl [break]    : on  => broken .
endm

search [1] off =>+ broken .
continue 1 .
show path 2 .
```

`TNK-SEARCH-001` requires a deduplicated BFS graph. `broken` is reachable at depth two. `show path` uses the state number printed by the actual search result; clients must not assume a fixed number when independent same-depth successors are present.

## 28. Parameterized composition

```maude
fth TRIV is
  sort Elt .
endfth

fmod BOX{X :: TRIV} is
  sort Box{X} .
  op box : X$Elt -> Box{X} [ctor] .
endfm

fmod NAT-ELEM is
  sort Nat .
  op z : -> Nat [ctor] .
endfm

view NatAsElt from TRIV to NAT-ELEM is
  sort Elt to Nat .
endv

fmod NAT-BOX is
  protecting BOX{NatAsElt} .
endfm
```

By `TNK-MOD-004` and `TNK-VIEW-001`, instantiation maps `X$Elt` to `Nat`, producing a `box` constructor over `Nat` in the flattened module.

## 29. Host-owned Session

```rust
use tnk_session::Session;

let mut tnk = Session::new();
let definition = tnk.eval(
    "fmod ONE is sort N . op one : -> N [ctor] . endfm",
    false,
);
assert!(!definition.exit);
assert_eq!(tnk.current(), Some("ONE"));

let result = tnk.eval("reduce one .", false);
assert_eq!(
    result.output,
    "reduce in ONE : one .\nrewrites: 0\nresult N: one"
);

let quit = tnk.eval("quit", false);
assert!(quit.exit);
```

This demonstrates `TNK-SESSION-001`, `TNK-SESSION-005`, and `TNK-API-001`. A robust host should not parse arbitrary diagnostic prose from `output`; it should expose the text to a human or use a typed lower-layer interface.

---

# Appendix A — Command catalogue

| Command | Aliases | Resumable | Primary clauses |
|---|---|---:|---|
| `reduce` | `red` | no | `TNK-CMD-REDUCE-001` |
| `match` | — | no (eager all results) | `TNK-MATCH-001`, `003` |
| `xmatch` | — | no (eager all results) | `TNK-MATCH-002`, `003` |
| `rewrite` | `rew` | yes | `TNK-REWRITE-001`, `TNK-CONT-001` |
| `frewrite` | `frew` | yes | `TNK-REWRITE-002` |
| `erewrite` | `erew` | yes | `TNK-REWRITE-003` |
| `search` | — | yes | `TNK-SEARCH-*` |
| `srewrite` | `srew` | no (eager all results) | `TNK-STRAT-*` |
| `dsrewrite` | `dsrew` | no (eager all results) | `TNK-STRAT-*` |
| `unify` | — | no (bounded eager results) | `TNK-UNIFY-*` |
| `irredundant unify` | `irred unify` | no (bounded eager results) | `TNK-UNIFY-*` |
| `get variants` | — | yes | `TNK-VARIANT-001`, `002` |
| `variant unify` | — | yes | `TNK-VARIANT-003` |
| `filtered variant unify` | — | yes | `TNK-VARIANT-003` |
| `variant match` | — | yes | `TNK-VARIANT-004` |
| `vu-narrow` | — | yes | `TNK-NARROW-*` |
| `fvu-narrow` | — | yes | `TNK-NARROW-*` |
| `check` | — | no | `TNK-SMT-001`, `002` |
| `smt-search` | — | yes | `TNK-SMT-003` |
| `continue` | `cont` | resumes prior | `TNK-CONT-001` |
| `select` | — | state command | `TNK-SESSION-005` |
| `show ...` | — | inspection | `TNK-SEARCH-003`, `TNK-NARROW-003` |
| `set ...` | — | settings | `TNK-SESSION-006` |
| `load`, `sload` | — | file evaluation | `TNK-LOAD-*` |
| `quit` | `q`, `exit` | no | §17.4 |

# Appendix B — Glossary

- **Axiom canonicalization:** normalization by declared `assoc`, `comm`, `id`, `idem`, or `iter` structure, not by user equations.
- **Canonical state:** an equation-normal, axiom-canonical runtime term used as a search-graph key.
- **Complete result set:** every solution in the specified domain has a representative and exploration ended without a bound or incomplete flag.
- **Condition solution:** one consistent branch of left-to-right condition evaluation, including bindings introduced by matching/rewrite fragments.
- **Continuation:** a Session-owned resumable operation retaining graph/traversal state and roots.
- **Error sort:** synthesized top sort of one connected sort component (kind).
- **Flattening:** resolving a module expression/import closure into one declaration stream before frontend build.
- **Kind:** connected component of the subsort graph plus its error sort.
- **Least sort:** most specific sort assigned to a term under declarations and memberships.
- **Normal form:** a term to which no executable equation applies; for rewriting commands, “rule normal form” additionally means no selected rule transition applies.
- **Residue/extension:** the associative/AC subject portion left outside an extension match.
- **Sound solution:** substituting its bindings satisfies the defining equations/match/reachability relation.
- **Variant:** a normal form paired with the accumulated substitution that produced it by variant narrowing.

# Appendix C — Implementation map

These links locate the current implementation; they explain but do not supersede the clauses:

- kernel facade and accounting: [`crates/tnk-core/src/engine.rs`](../crates/tnk-core/src/engine.rs)
- DAG arena and roots: [`arena.rs`](../crates/tnk-core/src/arena.rs), [`root.rs`](../crates/tnk-core/src/root.rs)
- sort model: [`sort.rs`](../crates/tnk-core/src/sort.rs), [`sort_bdds.rs`](../crates/tnk-core/src/sort_bdds.rs)
- operator theories and built-ins: [`symbol.rs`](../crates/tnk-core/src/symbol.rs), [`builtin.rs`](../crates/tnk-core/src/builtin.rs)
- rewriting and search: [`rewrite.rs`](../crates/tnk-core/src/rewrite.rs), [`search.rs`](../crates/tnk-core/src/search.rs)
- unification: [`unify/`](../crates/tnk-core/src/unify/)
- variants and narrowing: [`variant.rs`](../crates/tnk-core/src/variant.rs), [`narrow.rs`](../crates/tnk-core/src/narrow.rs)
- SMT and LTL: [`smt.rs`](../crates/tnk-core/src/smt.rs), [`smt_search.rs`](../crates/tnk-core/src/smt_search.rs), [`ltl/`](../crates/tnk-core/src/ltl/)
- lexer and source parser: [`lex.rs`](../crates/tnk-frontend/src/lex.rs), [`surface/parser.rs`](../crates/tnk-frontend/src/surface/parser.rs)
- grammar, loader, and printer: [`grammar/`](../crates/tnk-frontend/src/grammar/), [`load.rs`](../crates/tnk-frontend/src/load.rs), [`pretty.rs`](../crates/tnk-frontend/src/pretty.rs)
- strategy execution: [`strategy.rs`](../crates/tnk-frontend/src/strategy.rs)
- module composition: [`flatten.rs`](../crates/tnk-modules/src/flatten.rs), [`view.rs`](../crates/tnk-modules/src/view.rs), [`load.rs`](../crates/tnk-modules/src/load.rs)
- reflection: [`meta.rs`](../crates/tnk-modules/src/meta.rs)
- Session state machine: [`crates/tnk-session/src/lib.rs`](../crates/tnk-session/src/lib.rs)
- terminal adapter and CLI: [`crates/tnk-repl/src/lib.rs`](../crates/tnk-repl/src/lib.rs), [`main.rs`](../crates/tnk-repl/src/main.rs)

# Appendix D — Surface grammar

This appendix defines the accepted surface grammar. `Id`, `Name`, `OpName`, and `Term` are token bubbles whose final interpretation is described by §§4–6; they are not restricted to ASCII identifier syntax. A final `.` is a terminator only under `TNK-LEX-001`.

```text
Source       ::= Item*
Item         ::= Module | View | Command | SessionCommand

Module       ::= ModOpen Name Params? "is" Declaration* ModClose "."?
ModOpen      ::= "fmod" | "mod" | "fth" | "th"
               | "smod" | "sth" | "omod" | "oth"
ModClose     ::= "endfm" | "endm" | "endfth" | "endth"
               | "endsm" | "endsth" | "endom" | "endoth"
Params       ::= "{" Parameter ("," Parameter)* "}"
Parameter    ::= Name "::" Name

Declaration  ::= Import | SortDecl | SubsortDecl | OpDecl | VarDecl
               | Statement | StrategyDecl | StrategyDef | ObjectDecl
Import       ::= ("protecting" | "pr" | "extending" | "ex"
               | "including" | "inc" | "generated-by") ModuleExpr "."
SortDecl     ::= ("sort" SortName | "sorts" SortName+) "."
SubsortDecl  ::= ("subsort" | "subsorts") SortName+
                 ("<" SortName+)+ "."
OpDecl       ::= ("op" | "ops" | "msg" | "msgs") OpName+
                 ":" SortName* ("->" | "~>") SortName OpAttrs? "."
VarDecl      ::= ("var" | "vars") Name+ ":" SortName "."
Statement    ::= ("mb" Term ":" SortName
                 | "cmb" Term ":" SortName "if" Condition
                 | "eq" Term "=" Term
                 | "ceq" Term "=" Term "if" Condition
                 | "rl" Term "=>" Term
                 | "crl" Term "=>" Term "if" Condition) StmtAttrs? "."
Condition    ::= CondFrag ("/\\" CondFrag)*
CondFrag     ::= Term "=" Term | Term ":=" Term | Term ":" SortName
               | Term "=>" Term

StrategyDecl ::= ("strat" | "strats") Name+
                 [":" SortName*] "@" SortName "."
StrategyDef  ::= ("sd" | "csd") Name ["(" Term ("," Term)* ")"]
                 ":=" Strategy ["if" Condition] "."
ObjectDecl   ::= ("class" | "classes") ClassSpec+
               | ("subclass" | "subclasses") SortName+
                 ("<" SortName+)+ "."
ClassSpec    ::= SortName ["|" AttrSpec ("," AttrSpec)*] "."
AttrSpec     ::= Name ":" SortName

View         ::= "view" Name Params? "from" ModuleExpr "to" ModuleExpr
                 "is" ViewItem* "endv" "."?
ViewItem     ::= "sort" SortName "to" SortName "."
               | VarDecl
               | "op" OpSelector "to" ("term" Term | OpName) "."
               | "class" SortName "to" SortName "."
               | "attr" Name ["." SortName] "to" Name "."
               | "msg" Term "to" "term" Term "."
OpSelector   ::= OpName [":" SortName* ("->" | "~>") SortName]

ModuleExpr   ::= ModuleRename ("+" ModuleRename)*
ModuleRename ::= ModuleAtom ("*" "(" Rename ("," Rename)* ")")*
ModuleAtom   ::= (Name | "(" ModuleExpr ")")
                 ("{" ModuleExpr ("," ModuleExpr)* "}")*
Rename       ::= "sort" SortName "to" SortName
               | "label" Name "to" Name
               | "op" OpSelector "to" OpName OpAttrs?
               | "class" SortName "to" SortName
               | "attr" Name ["." SortName] "to" Name
               | "msg" OpName "to" OpName
```

The matching close keyword is required. Module-kind gates are normative in `TNK-MOD-001`. `op` and `msg` take one OpName. In `ops` and `msgs`, the `OpName+` list holds one OpName per top-level parenthesized group and one per remaining token (§5.2). In `VarDecl`, a `,` separates names and is not a declared `Name` (§5.2). `class`/`classes` use the parser's class-list surface; `msg`/`msgs` reuse operator declaration syntax but are object-only. `csd` is accepted but its conditional execution is Unsupported.

### D.1 Command grammar

`Bound` is a positive decimal. Bracketed `[n]` supplies a command's first bound and `[n,m]` its command-specific pair. `continue n` instead uses one bare decimal. An explicit zero is rejected; absence means unbounded within the documented algorithm and implementation resource policy.

```text
ModuleOpt      ::= ["in" ModuleExpr ":"]
BoundOpt       ::= ["[" Bound "]"]
SearchBoundOpt ::= ["[" Bound ["," Bound] "]"]
ContinueBoundOpt ::= [Bound]
ConditionOpt   ::= ["such" "that" Condition]
BlockersOpt    ::= ["such" "that" Term ("," Term)* "irreducible"]

Command      ::= ("reduce" | "red") ModuleOpt Term "."
               | "check" ModuleOpt Formula "."
               | ("match" | "xmatch") ModuleOpt Term "<=?" Term "."
               | ["irredundant" | "irred"] "unify" BoundOpt
                 ModuleOpt Term "=?" Term ("/\\" Term "=?" Term)* "."
               | "get" ["irredundant"] "variants" BoundOpt
                 ModuleOpt Term BlockersOpt "."
               | ["filtered"] "variant" "unify" BoundOpt
                 ModuleOpt Term "=?" Term ("/\\" Term "=?" Term)*
                 BlockersOpt "."
               | "variant" "match" BoundOpt ModuleOpt
                 Term "<=?" Term BlockersOpt "."
               | ("rewrite" | "rew") BoundOpt ModuleOpt Term "."
               | ("frewrite" | "frew") SearchBoundOpt ModuleOpt Term "."
               | ("erewrite" | "erew") SearchBoundOpt ModuleOpt Term "."
               | "search" SearchBoundOpt ModuleOpt Term SearchArrow Term
                 ConditionOpt "."
               | "smt-search" SearchBoundOpt ModuleOpt
                 Term SearchArrow Term ConditionOpt "."
               | NarrowPrefixOpt ("vu-narrow" | "fvu-narrow")
                 NarrowPostOpt SearchBoundOpt ModuleOpt
                 Term SearchArrow Term ConditionOpt "."
               | ("srewrite" | "srew" | "dsrewrite" | "dsrew")
                 ModuleOpt Term "using" Strategy "."
               | ("continue" | "cont") ContinueBoundOpt "."

SearchArrow   ::= "=>1" | "=>+" | "=>*" | "=>!"
NarrowPrefixOpt ::= ["{" ("fold" | "vfold" | "path")
                     ("," ("fold" | "vfold" | "path"))* "}"]
NarrowPostOpt ::= ["{" ("filter" | "delay")
                   ("," ("filter" | "delay"))* "}"]

SessionCommand ::= "select" Name "."
               | "show" ("modules" | "module" [Name]
                 | "views" | "view" Name
                 | "path" ["states"] Bound
                 | "frontier" "states"
                 | "most" "general" "states"
                 | "search" "graph") "."
               | "set" SetControl "."
               | ("load" | "sload") Path
               | "quit" | "q" | "exit"
SetControl   ::= "trace" [TraceSection] ("on" | "off")
               | ["clear"] "memo"
               | "include" "BOOL" ("on" | "off")
               | "show" ("timing" | "breakdown") ("on" | "off")
               | "verbose" ("on" | "off")
TraceSection ::= "condition" | "whole" | "substitution" | "rewrite"
               | "body" | "builtin" | "eqs" | "mbs" | "rls"
```

`load` and `sload` accept the rest of their submission line as the path after trimming whitespace and an optional final command dot. The command dot is a final `.` that is the whole operand or follows whitespace; a `.` glued to the path is part of the path, so `load lib .` names `lib` and `load lib.` names `lib.`. The CLI's optional positional file is a separate adapter surface. Unknown `show` commands diagnose with an `error:` line, or with a `parse error:` line when the `show` follows a module or view definition on the same physical line; unknown `set` controls are currently inert and are catalogued as Unsupported in Appendix K.

### D.2 Strategy grammar

Strategy precedence, from tightest to loosest, is postfix iteration, sequencing, choice, and ternary branch. Parentheses override it.

```text
Strategy     ::= Branch
Branch       ::= Choice ["?" Strategy ":" Branch]
Choice       ::= Sequence ("|" Sequence)*
Sequence     ::= Postfix (";" Postfix)*
Postfix      ::= StrategyAtom ("*" | "+" | "!")*
StrategyAtom ::= "idle" | "fail" | "all"
               | ("match" | "xmatch" | "amatch") Term ConditionOpt
               | ("matchrew" | "xmatchrew" | "amatchrew")
                 Term ConditionOpt "by" UsingClause
                 ("," UsingClause)*
               | ("top" | "one" | "try" | "not" | "test")
                 "(" Strategy ")"
               | "or-else" "(" Strategy "," Strategy ")"
               | RuleApplication | StrategyCall | "(" Strategy ")"
UsingClause  ::= Term "using" Strategy
RuleApplication ::= Name ["[" Term "<-" Term
                          ("," Term "<-" Term)* "]"]
                     ["{" Strategy ("," Strategy)* "}"]
StrategyCall ::= Name ["(" Term ("," Term)* ")"]
```

Rule applications may carry a label, substitutions, and `using` strategies for rule-condition fragments. Strategy calls retain term arguments as source bubbles and resolve them against declarations in the selected module. The parser accepts `csd`; resolution rejects conditional strategy definitions.

# Appendix E — Mixfix precedence and term resolution

### E.1 Grammar construction

For each valid operator declaration, TNK splits the canonical name at unescaped `_`; the number of holes equals arity. Literal fragments become terminals and holes become sort/kind nonterminals. Constants and true prefix operators add ordinary productions; a valid hole-bearing operator does not also gain a synthetic `f(a,b)` spelling. The current prefix-only fallback for a declaration whose hole count is invalid is recorded in Appendix H.4.

The current numeric precedence model is:

| Form | Default production precedence | Default gather |
|---|---:|---|
| constant or outfix/mixfix with neither end bare | `0` | internal holes `127` |
| bare unary prefix/postfix | `15` | end hole `15` |
| bare operator with two or more arguments | `41` | end/adjacent holes `41`; internal holes `127` |
| bare binary associative infix | `41` | `(e E)` = `(40, 41)` |
| explicit `prec p` | `p` | derived as below |

`127` is the unbounded `ANY` gather value. For explicit `gather`, `E` maps to `p`, `e` maps to `max(p-1,0)`, and `&` maps to `127`. Gather arity MUST equal operator arity. A child production of precedence `q` is admissible in a hole bounded by `b` iff `q <= b`. Thus smaller numbers bind more tightly, and a hole bounded below an operator's precedence excludes that operator there.

### E.2 Overload filtering

The generated grammar carries one nonterminal per sort/kind applicability profile. Parsing first enforces token shape, precedence, gather, and sort-profile reachability. Term construction then resolves overloads by canonical name and arity, retains declarations whose domains admit the argument sorts, and chooses the declaration with the greatest lower range sort. If there is no applicable declaration, or no unique least result where the owning bubble requires uniqueness, the bubble is rejected. The current first-packed-forest selection cases remain Implementation-defined under `TNK-PARSE-002`.

### E.3 Variables, literals, and disambiguation

Declared variables take their module sort. `X:Sort` creates an on-the-fly variable, and `X:[S]` creates one at the kind of user sort `S`. A kind with several maximal sorts is also written with its printed name, `X:[M1,...,Mn]` (`TNK-SORT-002`), which is how generated kind-level variables print; other multi-sort bracket lists are not colon-variable spellings. A bare identifier may resolve as a declared variable, a zero-arity operator, or a recognized literal anchor; the applicable grammar and expected kind decide. Parentheses group, and `(term).Sort` selects the parse of `term` in the kind of the user sort `Sort`; it neither checks nor changes the term's least sort. The printer qualifies a kind-level term (least sort = its kind's error sort) with a user sort of that kind, never with the bracketed kind name, so the output reparses (`TNK-OUT-002`). Literal families and spacing boundaries are fixed by `TNK-LEX-003`.

# Appendix F — Declaration and statement attributes

### F.1 Operator attributes

| Source spelling | Stored meaning | Runtime effect | Status |
|---|---|---|---|
| `assoc` | associative theory | canonicalization, match/unify theory | Stable |
| `comm` | commutative theory | canonicalization, match/unify theory | Stable |
| `idem` | idempotent theory | canonicalization and matching | Stable |
| `id: t` | two-sided identity | canonicalization and theory solving | Stable |
| `left id: t` / `right id: t` | one-sided identity | reduction/canonicalization; not promoted to two-sided ACU | Stable |
| `iter` | iteration theory | compact `f^n(...)` syntax and reduction | Stable |
| `ctor` | constructor flag | constructor-sensitive symbolic analyses | Stable |
| `prec n` | production precedence | mixfix parsing | Stable |
| `gather (...)` | per-hole precedence bounds | mixfix parsing | Stable |
| `strat (...)` | 1-based positions ending in `0` | equational argument evaluation order | Stable |
| `frozen` / `frozen (...)` | all or selected 1-based positions | blocks rule and narrowing descent | Stable |
| `special (...)` | typed id/op/term hook attachment | built-in dispatch after hook resolution | Optional by loaded hooks |
| `ditto` | reuse preceding declaration attributes | source expansion | Stable |
| `poly (...)` | universal argument/range positions, range is `0` | one declaration instance per kind | Stable |
| `format (...)` | retained presentation metadata | no semantic reduction effect | Experimental |
| `config` | configuration constructor marker | object configuration semantics | Stable |
| `object` | object constructor role | object-message scheduling | Stable |
| `msg` | message role | object-message scheduling | Stable |
| `portal` | portal role | retained role metadata | Experimental |
| `pconst` | parameter-constant role | parameterized module composition | Stable |
| `memo` | accepted flag | warning; no memoization | Unsupported |

Attributes not listed above are rejected as unsupported operator attributes. `left` or `right` is valid only as part of an identity attribute.

### F.2 Statement attributes

| Source spelling | Applies to | Runtime effect | Status |
|---|---|---|---|
| `[label]` | mb/eq/rule/strategy definition | names trace/rule/strategy selection | Stable |
| `[owise]` | membership/equation | tried after ordinary statements for the symbol | Stable |
| `[nonexec]` | membership/equation/rule | retained for symbolic use, excluded from ordinary execution | Stable |
| `[variant]` | membership/equation | included in variant equation family | Stable |
| `[narrowing]` | rule | included in narrowing rule family | Stable |
| `[metadata "text"]` | statement | retained metadata, no execution change | Stable |
| `[print ...]` | statement | presentation metadata only | Experimental |

Statement attributes may be comma-separated or adjacent inside one bracket list. `owise`, `variant`, and `nonexec` are semantic selectors, not comments. Unknown statement attributes are invalid input; their current equation/rule and membership recovery paths are nonuniform and are catalogued in Appendix H.4. Portable source MUST NOT rely on either rejection or silent retention.

# Appendix G — Built-in hook catalogue

Built-ins are activated by resolved `special` attachments; spelling alone does not make an operator built-in. The id-hook names below are the accepted dispatch keys in this release.

### G.1 Literal anchors and ordinary special operators

| Id-hook class | Required/recognized data | Behavior |
|---|---|---|
| `SuccSymbol` | `zeroTerm`; optional minus hook | natural numeral anchor |
| `StringSymbol`, `FloatSymbol`, `QuotedIdentifierSymbol` | class marker | literal anchor |
| `SystemTrue`, `SystemFalse` | class marker | Boolean result anchors |
| `SMT_NumberSymbol` | `integers` or `reals` | SMT literal anchor |
| `ObjectConstructorSymbol` | object/configuration hooks | ordinary constructor plus object-pattern metadata |
| `MinusSymbol`, `DivisionSymbol` | natural hooks | signed integer and rational construction |
| `EqualitySymbol` | `equalTerm`, `notEqualTerm` | structural equality |
| `CommutativeDecomposeEqualitySymbol` | equality terms; optional conjunction/disjunction | constructor-sensitive decomposing equality |
| `BranchSymbol` | numbered term hooks | lazy branch selection |
| `RandomOpSymbol` | natural hooks | deterministic MT19937 stream |
| `CounterSymbol` | natural hooks | per-operator, per-top-level-rewrite counter |

Numeric operation classes are `ACU_NumberOpSymbol`, `CUI_NumberOpSymbol`, and `NumberOpSymbol`. Supported operation codes are `+`, `*`, `gcd`, `lcm`, `min`, `max`, `xor`, `&`, `|`, `sd`, `-`, `quo`, `rem`, `^`, `modExp`, `>>`, `<<`, `abs`, `~`, `<`, `<=`, `>`, `>=`, and `divides`, subject to the class's arity/theory and `TNK-BUILTIN-001`.

`StringOpSymbol` supports `+`, `length`, `substr`, `ascii`, `char`, `find`, `rfind`, `upperCase`, `lowerCase`, `cntrl`, `print`, `space`, `blank`, `graph`, `punct`, `alnum`, `alpha`, `isupper`, `islower`, `digit`, `xdigit`, `startsWith`, `endsWith`, `ltrim`, `rtrim`, `trim`, `<`, `<=`, `>`, and `>=`.

`FloatOpSymbol` supports unary `-`, `abs`, `sqrt`, `floor`, `ceiling`, `exp`, `log`, `sin`, `cos`, `tan`, `asin`, `acos`, unary/binary `atan`, `+`, binary `-`, `*`, `/`, `rem`, `^`, `min`, `max`, `<`, `<=`, `>`, and `>=`. Conversion hooks cover rational-to-float, float-to-rational, rational/float-to-string, string-to-rational/float, and decimal-float formatting. `QuotedIdentifierOpSymbol` supports Qid/string conversion plus `tokenize` and `printTokens`.

### G.2 SMT, temporal, meta, and external classes

| Id-hook class | Supported family | Capability condition |
|---|---|---|
| `SMT_Symbol` | Boolean connectives; integer/real arithmetic and order; equality, `ite`, divisibility, casts and `isInteger` | representation always; solving depends on profile |
| `ModelCheckerSymbol` | LTL model checking and counterexample construction | all temporal/result hooks resolve |
| `SatSolverSymbol` | LTL satisfiability/model construction | all temporal/formula/model hooks resolve |
| `MetaLevelOpSymbol` | reflected descent operations below | canonical meta hooks resolve |
| `InterpreterManagerSymbol` | synchronous child-Session manager | META-INTERPRETER protocol loaded |
| `StreamManagerSymbol` | `stdin`, `stdout`, `stderr` manager | stream code and message hooks resolve |

The exact `SMT_Symbol` codes are `true`, `false`, `not`, `and`, `or`, `xor`, `implies`, `===`, `=/==`, `ite`, unary/binary `-`, `+`, `*`, `div`, `mod`, `<`, `<=`, `>`, `>=`, `divisible`, `/`, `toReal`, `toInteger`, and `isInteger`.

The native META-LEVEL dispatch keys are:

- execution: `metaReduce`, `metaNormalize`, `metaRewrite`, `metaFrewrite`, `metaApply`, `metaXapply`;
- matching/search: `metaMatch`, `metaXmatch`, `metaSearch`, `metaSearchPath`, `metaCheck`, `metaSmtSearch`;
- variant satisfiability: `variantSat`, `variantSatWithSorts`, `variantValid`, `variantValidWithSorts`, `variantSatWellFormed`;
- sort inspection: `metaSortLeq`, `metaSameKind`, `metaLesserSorts`, `metaGlbSorts`, `metaLeastSort`, `metaCompleteName`, `metaGetKind`, `metaGetKinds`, `metaMaximalSorts`, `metaMinimalSorts`, `metaMaximalAritySet`;
- parsing and validation: `metaParse`, `metaPrettyPrint`, `metaPrintToString`, `metaWellFormedModule`, `metaWellFormedTerm`, `metaWellFormedSubstitution`;
- reflection: `metaUpModule`, `metaUpImports`, `metaUpSorts`, `metaUpSubsortDecls`, `metaUpOpDecls`, `metaUpMbs`, `metaUpEqs`, `metaUpRls`, `metaUpStratDecls`, `metaUpSds`, `metaUpView`, `metaUpTerm`, `metaDownTerm`;
- unification: `metaUnify`, `metaDisjointUnify`, `metaIrredundantUnify`, `metaIrredundantDisjointUnify`, and the two `legacyMeta*Unify` forms;
- variants/narrowing: `metaGetVariant`, `metaGetIrredundantVariant`, their supported signatures, `metaVariantUnify`, `metaVariantDisjointUnify`, `metaVariantMatch`, `metaNarrow`, `metaNarrowingApply`, `metaNarrowingSearch`, and `metaNarrowingSearchPath`.

`metaNarrow2` is recognized but inert. An unknown `MetaLevelOpSymbol` code maps to an inert `Unknown` operation. Unsupported id-hook classes such as `MatrixOpSymbol` and `LoopSymbol` leave their operators ordinary and currently produce no explicit diagnostic.

### G.3 Strict host-function attachments

`HostFunctionSymbol` selects a host capability rather than a TNK-owned built-in:

```text
id-hook HostFunctionSymbol (KEY)
op-hook PURPOSE (OperatorSignature)
term-hook PURPOSE (GroundConstant)
```

Exactly one canonical `KEY` is required. The configured `StrictReducerDescriptor` fixes arity and the complete set of required supporting-hook purposes. `HookSort::Argument(i)` and `HookSort::Result` express each hook's declaration-relative sort contract; source positions remain 1-based strategy positions, while Rust descriptor argument indices are 0-based. Each required `op-hook` must resolve to one compatible signature-local symbol and each required `term-hook` to one compatible ground constant. Extra, duplicate, missing, ambiguous, or cross-kind hooks reject the attachment. Ordinary structural renaming rewrites referenced TNK symbols and sorts but leaves `KEY` unchanged.

Only fixed-arity free operators under the standard eager strategy are admitted. Existing TNK-owned id-hook classes retain their bespoke dispatch contracts. In particular, `BranchSymbol`, `CounterSymbol`, META descent, and external managers are not `StrictReducer`s. `HostControlSymbol` is a reserved, Unsupported name for a possible future strategy-aware protocol: it never consults `HostFunctionCatalog`, never installs a strict binding, and remains ordinary/inert in this release even when its data token exactly matches a registered strict key.

# Appendix H — Observable result and diagnostic schema

### H.1 Public record

The only stable public Session record shape in this release is:

```text
Eval {
  output: String,  // zero or more unwrapped presentation blocks
  exit: bool       // true only for quit/q/exit
}
```

`Session::eval` does not expose a typed status, semantic value, solution vector, diagnostic code, completion bit, or continuation handle. A caller MUST NOT infer control flow from arbitrary prose. Clients that need algebraic results, completeness, or structured failures use the frontend, module, or kernel APIs.

### H.2 Presentation records

With color disabled, the stable semantic fields are:

| Record | Required fields | Completion marker |
|---|---|---|
| reduce/rewrite/frewrite/erewrite | command echo; `rewrites: N`; `result SORT: TERM` or `result (sort not calculated): TERM` | result line |
| match/xmatch | command echo; zero or more numbered matcher blocks; bindings; xmatch residue when present | `No match.`, `No more matches.`, or eager end |
| search | command echo; `Solution N (state K)`; `states: S  rewrites: R`; bindings | `No more solutions.` only on exhaustion |
| SMT search | solution number; rewrite count; `state: TERM`; bindings; `where FORMULA` | `No solution.` / `No more solutions.` |
| unification | command echo; numbered `Unifier` blocks; bindings | `No unifier.` / `No more unifiers.` when represented |
| variants | numbered `Variant`; rewrite count; `SORT: TERM`; bindings | `No more variants.` |
| variant unify/match | numbered `Unifier` or `Matcher`; rewrite count; bindings | `No ...` / `No more ...` |
| narrowing | numbered state/solution, rewrite count, state term, accumulated substitution, optional variant unifier | no-more marker only on exhaustion |
| strategy rewrite | numbered result; rewrite count; `result SORT: TERM` | eager end after all results |
| check | command presentation plus a `Sat`, `Unsat`, or `Unknown` backend answer; current `BadDag` omission is recorded in Appendix H.4 | one answer except for the current `BadDag` gap |
| show/select/set/load | command-specific text or empty success | return from call |

A bounded resumable invocation that stops exactly at its requested prefix emits no no-more marker and retains a matching continuation. Eager commands (`match`, `xmatch`, strategy rewrite, and bounded object-level unify) do not create a continuation. `continue` output appends records from the saved operation and emits its completion marker only when exhaustion is observed.

Trace blocks, breakdown rows, verbose statistics, ANSI color, whitespace wrapping, source excerpts, and diagnostic prose are Experimental presentation. Counts are semantic only where `TNK-COUNT-*` or a command clause names them.

### H.3 Diagnostic ownership and state effect

This table is the intended ownership model. The current implementation exceptions in H.4 control the description of what workspace version `0.1.0` actually does for the specifically named invalid inputs; they are not accepted-language guarantees.

| Category | Owner | Required Session state effect |
|---|---|---|
| lexical/source parse | frontend source parser | current module, databases, and continuation unchanged |
| declaration/statement | frontend builder | invalid module definition is not installed; statement-local failures follow `TNK-STMT-001` |
| module/view composition | module layer | attempted definition is atomic; prior definition and dependents remain |
| strict host attachment | frontend/signature builder | invalid or missing capability rejects the attempted module atomically; a prior definition and its built dependents remain active |
| command parse/build | frontend/Session command boundary | no semantic execution; prior continuation remains only where `TNK-CONT-001` permits |
| unsupported capability | owning feature boundary | no false success or exhaustion claim |
| user bound | command enumerator | finite prefix; continuation retained only for resumable families |
| solver `Unknown`/`BadDag` | SMT boundary | intended to be reported distinctly from `Sat`/`Unsat`; the current Session `BadDag` omission is in H.4 |
| internal incompleteness | unification/variant/narrowing boundary | distinct from exhausted/no-solution |
| external I/O | Session external manager/load boundary | error returned as text; process remains live |
| strict reducer fault | owning semantic driver | no semantic result or successful host rewrite is recorded; Session emits one `error: strict reducer ... failed: ...` diagnostic and stores no continuation |
| resource exhaustion | parser/algorithm boundary | distinct from malformed input and semantic exhaustion |

The category table defines semantic ownership; `Eval` does not currently carry a machine-readable category enum. Clients use a stable documented prefix plus state effect or a typed lower-level API.

### H.4 Tentative invalid-input and recovery ledger

**TNK-RECOVERY-001 — Current invalid-input behavior.** The tables below record actual workspace-version-`0.1.0` behavior at known malformed, statically invalid, or unsupported input seams. This entire surface is **Experimental, tentative, and in flux**. It is diagnostic documentation, not a supported recovery API: it does not enlarge the accepted grammar, promise that a repaired declaration or retained statement will keep working, or grant compatibility to a missing diagnostic or panic. For the named cases, the tables describe the current implementation even where it deviates from `TNK-DOC-003`, `TNK-DOC-006`, `TNK-STMT-001`, or H.3.

Developer planning is intentionally outside this Reference. This ledger states only the current user-visible diagnostic and state effects; it does not assign implementation priority or promise that an Unsupported or Experimental case will be implemented.

**Practical rule:** submit only well-formed, statically valid, supported TNK input. Do not use skipped tokens, repaired declarations, dropped statements, inert hooks, silent commands, or process failure as a programming technique. Portable programs MUST NOT depend on any behavior in this section. If input satisfies the grammar and static requirements in Parts I–III, these invalid-input seams are avoidable.

Here, **silent** means that `Session::eval` adds no diagnostic text for the named problem. A later recognized item may still produce its ordinary output.

#### H.4.1 Source, declaration, and statement seams

| Incorrect input or seam | Current diagnostic | Current state/evaluation effect |
|---|---|---|
| unrecognized top-level tokens before a recognized module, view, or command opener | silent for the skipped tokens | tokens are discarded one at a time; the next recognized suffix in the same submission is parsed and executed with its normal state effects |
| two commands on one physical line | `error: more than one command on a line.` | the physical-line command group is rejected before either command is dispatched |
| mixfix operator name whose `_` count differs from its arity | silent | no mixfix production is installed; the declaration remains callable in prefix form using its full declared name and arity |
| nonbinary or kind-incompatible `assoc`, `comm`, `idem`, identity, or `iter` attribute | silent | the invalid algebraic flag is cleared; the declaration remains installed with any independently valid surviving flags, otherwise as a free operator |
| `frozen (...)` containing an argument position outside the declaration's arity | silent | the complete `frozen` attribute is ignored and the declaration remains installed |
| unknown operator attribute or unknown `special` subdirective | `parse error:` | the submitted module definition is not installed; this differs from an unknown `id-hook` class below |
| ordinary statement whose term, variables, condition, or `[print ...]` data fails frontend construction | `warning:` naming a dropped equation, membership, or rule | that statement is omitted; the enclosing buildable module and later valid statements are retained |
| trailing equation/rule bracket group whose first token is not a recognized statement attribute | no attribute-specific diagnostic; a downstream dropped-statement warning is emitted if the resulting term bubble does not parse | the bracket group remains part of the statement term bubble rather than being peeled as attributes; if that bubble parses, its term meaning controls |
| unknown token after a recognized first attribute in an equation/rule bracket group | silent for the unknown token | the token is consumed, recognized attributes still apply, and the statement remains installed if its terms build |
| unknown token in a membership attribute group | silent for the unknown token | the token is consumed and the membership remains installed if its term and target sort build |
| conditional rule carrying `[narrowing]` | `warning:` naming a dropped rule | the entire rule is omitted; the enclosing module and later valid statements are retained |
| executable equation, membership, or rule whose whole left-hand side is a variable, such as `X` or `X:S` (`[nonexec]` statements and `[narrowing]` rules excepted), including an instance statement that a view maps to a variable | `warning:` naming a dropped equation, membership, or rule whose left-hand side is a variable | the statement is not executed and is omitted from reflection; the enclosing module and later valid statements are retained. A reflected module value containing such a statement does not down-translate: metalevel descent operations on it remain inert (`getKinds`, which reads only the sort signature, still answers), `wellFormed` returns `false`, and `insertModule` receives an interpreter error. This is the current boundary pending a decision on these statements; §5.4 does not make them invalid |
| reflected module value containing an executable statement that the source loader drops for its variables or condition: a right-side or condition variable that neither the left side nor an earlier `:=` or `=>` fragment binds (`TNK-COND-002`; an executable `[narrowing]` rule is included), or an equation or membership with a rewrite (`=>`) condition | silent | the module value does not down-translate, as for a variable left-hand side above: metalevel descent operations on it remain inert (`getKinds`, which reads only the sort signature, still answers), `wellFormed` returns `false`, and `insertModule` receives an interpreter error. `[nonexec]` statements are exempt, as at the source level: a reflected rule with a fresh right-side variable descends when it is `[nonexec]`, and narrowing uses it when it is `[nonexec narrowing]` |

#### H.4.2 Unsupported and silent command/hook seams

| Input or outcome | Current diagnostic/output | Current state/evaluation effect |
|---|---|---|
| recognized non-host `id-hook` class with no TNK implementation, or an unknown special id-hook class | silent | no `SpecialOp` is attached; the operator remains ordinary and may still reduce through user equations; missing `HostFunctionSymbol` capabilities instead follow `TNK-HOST-001` and reject the module |
| unknown `set` control, unsupported `set include` module, or unrecognized value on the include/breakdown/verbose/timing paths | silent | the directive is consumed and the corresponding Session setting is unchanged |
| `set memo ...`, `set clear memo`, `do clear memo`, or `set show timing on` | `warning:` that the capability is unavailable | no memo table or timing mode is enabled; other Session state is unchanged |
| ordinary unification rejected by low-level unsupported-theory readiness | command echo only; no warning, unifier, `No unifier.`, or completion marker | no unifier stream or continuation is created |
| `check` whose configured SMT backend returns `BadDag` | command echo only; no backend-answer line | the prior continuation has already been cleared; no satisfiability claim is made |

These rows expose current inconsistencies rather than synthesizing a general recovery principle. They are not compatibility guarantees; later releases may replace them with behavior consistent with H.3.

# Appendix I — Rust API map

### I.1 Supported public entry points

| Crate | Entry point | Contract and principal clauses |
|---|---|---|
| `tnk-session` | `Session::new()` | creates isolated persistent state; `TNK-SESSION-001` |
| `tnk-session` | `Session::eval(&str, bool) -> Eval` | complete submission to unwrapped output; `TNK-SESSION-*`, `TNK-OUT-*`, Appendix H |
| `tnk-session` | `Session::input_complete(&mut self, &str) -> bool` | host-side submission completeness probe; `TNK-SESSION-004` |
| `tnk-session` | `Session::set_stdin(impl Into<String>)` | replaces scripted input for external `getLine`; `TNK-API-001` |
| `tnk-session` | `Session::current() -> Option<&str>` | current selected module name |
| `tnk-session` | `Session::builder() -> SessionBuilder`, `SessionBuilder::{host_functions,reduce_gc_interval,build}` | configures one immutable reducer capability set inherited by modules and child interpreters; `TNK-HOST-*` |
| `tnk-repl` | `Repl::new(bool)` | terminal policy wrapper with fixed color selection |
| `tnk-repl` | `Repl::eval(&mut self, &str) -> Eval` | Session evaluation plus exactly one wrapping pass |
| `tnk-repl` | `Repl::input_complete`, `set_stdin`, `current` | forwards the corresponding Session behavior |
| `tnk-frontend` | `lex::tokenize`, `Interner` | lexical tokenization and interned source names; `TNK-LEX-*` |
| `tnk-frontend` | `surface::parser::Parser::{new,parse_top_item,parse_source}` | parses modules, views, and top-level command AST; `TNK-PARSE-*` |
| `tnk-frontend` | `load::{load_source,load_source_with_host_functions,build_loaded_module,build_loaded_module_with_host_functions,try_build_loaded_module_with_host_functions,build_loaded_module_with_host_functions_and_inline_statements,try_build_loaded_module_with_host_functions_and_inline_statements,build_loaded_module_homed,build_loaded_module_homed_with_host_functions,build_loaded_module_homed_traced,build_loaded_module_homed_traced_with_host_functions,try_build_loaded_module_homed_traced_with_host_functions,LoadedModuleBuildError}`, public `sig::build_sig::build_module` | import-free, reflected-inline, or homed source/signature build; typed configured boundaries preserve `ReducerFault`, and every listed `*_with_host_functions` loader receives the immutable reducer catalog; `TNK-API-002`, `TNK-HOST-*` |
| `tnk-frontend` | `pretty::{print_pretty,print_raw}` | term rendering; presentation clauses apply |
| `tnk-frontend` | `strategy::execute` | strategy execution over a loaded module; `TNK-STRAT-*` |
| `tnk-modules` | `db::ModuleDb`, `view::ViewDb` | persistent named source storage |
| `tnk-modules` | `load::{load_program,load_program_with_host_functions,flatten_and_build,flatten_and_build_with_host_functions}`, `view::{validate_view,validate_view_with_host_functions}`, `meta::MetaDescent::{new,with_host_functions}`, `prelude` | composition/build/reflection/prelude mechanisms and explicit catalog propagation; `TNK-MOD-*`, `TNK-VIEW-001`, `TNK-HOST-*` |
| `tnk-core` | `Engine` and public term/sort/symbol IDs; `Engine::{with_host_functions,host_functions,validate_host_function_binding,bind_host_function,try_prepare_identities,try_normalize_for_unify,try_symbol_identity_dag}` | engine-relative kernel construction/evaluation, syntax-free host binding, and typed reducer-fault preservation at identity/symbolic-normalization boundaries; `TNK-HOST-*` |
| `tnk-core` | `host::{HostFunctionCatalog,HostFunctionCatalogBuilder,HostFunctionKey,HostFunctionId,HostFunctionRegistrationError}`, `HostFunctionCatalog::{builder,is_empty,contains,descriptor_for}`, `HostFunctionCatalogBuilder::{register,build}` | immutable registration, canonical capability identity, typed registration failures, and one-way catalog lifecycle |
| `tnk-core` | `host::{StrictReducerDescriptor,StrictReducerDescriptorBuilder,HookSort,OpHookRequirement,TermHookRequirement,ResolvedHostHooks,ResolvedHostHooksBuilder,HostBindingId,HostBindingError}`, `StrictReducerDescriptor::{builder,arity,required_op_hooks,required_term_hooks}`, `StrictReducerDescriptorBuilder::{require_op_hook,require_constant_term_hook,build}`, `ResolvedHostHooks::builder`, `ResolvedHostHooksBuilder::{op,constant_term,build}` | descriptor requirements and build-time signature binding; raw resolved-hook lookup remains crate-private |
| `tnk-core` | `host::{StrictReducer,StrictCall,StrictReduceCtx,ScopedHostHooks,HostSymbol,NormalDag,RedexDag,DagRef,DagView,ChildView,BuiltDag,StrictOutcome,ReducerFault,BuildError}` | trusted scoped callback protocol, opaque hook capabilities, inspection, theory-aware construction, outcomes, and faults; `TNK-HOST-*` |
| `tnk-core` | `host::codecs::{StringCodec,string}` and `HostFunctionCatalogBuilder::{register_typed1,register_typed2}` | borrowed zero-copy byte-string inputs, all-decodes callback gating, and owned output encoded through `stringSymbol` |
| `tnk-core` | public rewrite/search/unify/variant/narrow/SMT records and their `try_*` drivers | lower-level resumable semantic engines; corresponding Part III clauses and documented `ReducerFault`/panic boundaries |

The crate roots expose additional structural types needed to construct signatures and inspect lower-level results. Those types are supported only with their Rust type invariants; source-language conformance belongs to the frontend/module/Session entry points. Engine-relative IDs MUST NOT be mixed across engines.

### I.2 Ownership and lifetime invariants

- A `Session` owns its `Interner`, module/view databases, loaded engines, continuations, reflection caches, and external managers.
- A `LoadedModule` owns one `Engine`; its `DagId`, `SortId`, `SymbolId`, and continuation records are engine-relative.
- GC safety requires live DAGs retained by engine roots/guards or by owning sessions. Callers do not receive stable raw references through `Session::eval`.
- Module flattening transforms source `PreModule` values before frontend build; redefining a source invalidates and rebuilds transitive dependents.
- A `HostFunctionCatalog` is immutable and may be cloned into several independent Engines/Sessions. Dense function and binding IDs are catalog/signature-relative and are not persistent capability identifiers; the canonical key is the user-facing identity.
- `ResolvedHostHooks` may carry raw signature-local IDs only into the pre-execution binding API. `StrictCall::hooks` returns `ScopedHostHooks<'ctx>`; its opaque `HostSymbol<'ctx>` results are invariant in the callback lifetime, cannot be forged/extracted/retained, and are accepted only by same-scope context builders.
- Public Rust signatures, not examples in this appendix, are the compile-time authority. Semantic methods link back to the relevant `TNK-*` clauses.
- The standalone Rust examples in `README.md`, `docs/book.md`, and `docs/cheatsheet.md` have behavior-level compile coverage in `crates/tnk-session/tests/public_doc_examples.rs`, which is included by `cargo test --workspace`.

### I.3 Host pattern

```rust
use tnk_session::{Eval, Session};

fn submit(session: &mut Session, source: &str) -> Eval {
    assert!(session.input_complete(source));
    session.eval(source, false)
}
```

Hosts accumulating interactive lines call `input_complete` on the accumulated buffer and call `eval` only when it returns true. Batch hosts may pass complete multi-statement submissions directly. `Eval.output` is displayed, not reparsed as a typed protocol.

# Appendix J — Feature status and conformance profiles

This ledger applies the §0.2 state vocabulary. A narrower row overrides a broader one.

| Surface | State | Applicability and obligation |
|---|---|---|
| sorts, kinds, terms, algebraic canonicalization, equations, memberships, rules | Stable | default profile |
| lexer, source/module/view grammar, mixfix grammar, term construction | Stable | default profile, except first-parse choices named Implementation-defined |
| modules, theories, imports, renaming, instantiation, views, dependency rebuild | Stable | import-mode protection obligations remain Experimental |
| reduce, match/xmatch, rewrite/frewrite/erewrite, search | Stable | command semantics; presentation qualified separately |
| strategies and strategy rewrite | Stable | except conditional strategy definitions |
| supported order-sorted unification theories | Stable | completeness only when low-level incomplete flag is false |
| variants, variant unification/matching, variant narrowing | Stable | same explicit completeness boundary |
| SMT representation and null-backend `Unknown` | Stable | default profile |
| native Z3 solving | Optional | `smt-z3` build profile and provisioned backend |
| LTL model checking/satisfiability | Optional | loaded temporal hooks |
| numeric/string/float/Qid built-ins | Optional | matching loaded hook signatures |
| META-LEVEL/LEXICAL descent | Optional | loaded facade and resolved canonical hooks |
| object modules and synchronous local interpreters | Optional | loaded `CONFIGURATION`/META-INTERPRETER surfaces |
| standard stream external managers | Optional | loaded protocol hooks and host/CLI stream |
| strict Rust reducers (`HostFunctionSymbol`) | Optional | embedding supplies an immutable matching `HostFunctionCatalog`; otherwise attachment is rejected atomically |
| Session persistence, loading, continuations, settings | Stable | default profile |
| REPL adapter, CLI flags, fixed 80-column wrapping | Stable | executable profile |
| human output prose, whitespace, color, trace formatting, verbose/breakdown layout | Experimental | semantic fields in Appendix H remain contractual |
| exact result enumeration order unless explicitly named | Implementation-defined behavior | clients must not rely on one ordering |

### J.1 Build profiles

| Profile | Selection | Required behavior |
|---|---|---|
| default | default crate features | pure-Rust build; SMT requests return `Unknown` |
| `smt-z3` | enable the member crate's `smt-z3` feature | real `Sat`, `Unsat`, `Unknown`, and `BadDag` outcomes from the configured backend |
| default no-prelude CLI | `tnk-repl -no-banner -no-prelude` | no stock module is assumed; self-contained source works |
| library-backed CLI | set `MAUDE_LIB`, run ordinary `tnk-repl` | prelude and hook-backed capabilities are available only after successful load |

There is no root package feature named `smt-z3`; workspace `--all-features` enables the same-named features in member crates.

### J.2 Runtime capability sets

Loaded modules form an explicit runtime capability set:

- no prelude is injected into the kernel, frontend, module, or Session libraries;
- `tnk-repl` alone attempts to locate and load `prelude.maude`, unless `-no-prelude`;
- object modules request the bundled `CONFIGURATION` source through module-layer injection;
- optional `share/tnk` facades still require their referenced stock/external libraries;
- a hook-dependent clause applies only after its declaration and every required hook resolve.
- strict host reducers exist only in Engines/Sessions built with a catalog containing the exact source key; `Session::new()` and catalog-unaware loaders use the empty catalog;

Missing optional libraries must produce a load/build/unsupported outcome. They must not silently replace a solver with a positive answer or claim a language feature is active.

# Appendix K — Unsupported, incomplete, and deferred surfaces

This appendix describes current product boundaries, not a development backlog. **Unsupported** and **deferred** do not promise future implementation; developer decisions and work records are maintained separately from this normative Reference.

### K.1 Explicitly Unsupported

| Surface | Current behavior | Observable boundary |
|---|---|---|
| `memo` operator attribute and `set memo`/`set clear memo` | accepted; warning; no cache semantics | warning and unchanged reduction semantics |
| `set show timing on` | warning; timing remains disabled | no timing rows and state unchanged |
| conditional strategy definition `csd` | parses; rejected during strategy resolution | rejection, no partial definition |
| `matchrew` substrategy using a variable bound to a non-ground subterm, reachable only through a reflected strategy rewrite of a non-ground term | rejected during execution | `metaSrewrite` remains unreduced and an interpreter `srewriteTerm` request receives `interpreterError` (`Bad strategy.`); no partial result |
| conditional narrowing rule | warning; the invalid rule statement is dropped | enclosing module and later valid statements remain installed; see H.4 |
| non-ground unification under idempotent CUI or one-sided-identity associative theories | low-level problem is unsupported; no ordinary unifier stream | object-level Session currently emits only the command echo; no warning or no-unifier marker |
| SMT-search `=>!` | command rejects mode with an `error:` diagnostic and no command echo | no search/continuation created |
| conditional constraint in reflected `metaMatch` | unsupported at reflected boundary | no unrelated dispatch |
| `metaNarrow2` state-only dispatch | recognized but inert | term remains unreduced or explicit facade failure |
| unknown META-LEVEL operation code | maps to inert `Unknown` | no fallback to another MetaOp |
| unknown special id-hook classes, including matrix/loop families | operator remains ordinary/inert | no explicit diagnostic and no false built-in result |
| reserved `HostControlSymbol` | recognized only as a nonbinding future boundary; no control protocol is installed | never resolves through `HostFunctionCatalog`; operator remains ordinary/inert |
| unknown Session `set` control | inert | no explicit diagnostic and no state change |
| cooperative cancellation, semantic timeouts, and async Session evaluation | no API | hosts must provide process/thread policy; timeout is not no-solution |
| typed Session result/diagnostic stream | no API; `Eval` is text plus exit | use lower-level APIs for typed control flow |

Unsupported syntax recognized at a public boundary should diagnose under `TNK-DOC-006`. Appendix H.4 catalogs the current silent, repaired, dropped, and panic paths without promoting them to supported behavior.

### K.2 Sound but potentially incomplete

| Operation | Incompleteness source | Machine-readable boundary |
|---|---|---|
| AU/nonlinear unification | infinite family or bounded word exploration | `UnifyProblem::is_incomplete()` |
| ordinary Session unify | low-level incompleteness may occur | not exposed in `Eval`; Experimental presentation |
| variant unification/matching | variant search or nested unifier incomplete | low-level stream/search state |
| variant narrowing | nested unification/variant incomplete or depth bound | low-level narrowing result/session |
| search/narrowing | explicit depth/result bound | absence of no-more marker plus retained continuation where supported |
| SMT search | any encountered `Unknown` or `BadDag`, or an explicit search bound | backend result is available internally; Session output does not enumerate pruned unknown states |
| infinite rewrite/search/model-check state space | semantic divergence | no implicit timeout/cutoff |

Every returned result remains subject to its soundness clause. Incomplete means “no completeness claim,” never “probably complete” and never “no solution.”

Variant satisfiability returns `Decision::Rejected(EligibilityRejection)` rather than a Boolean for membership axioms; associative noncommutative constructors; inconsistent overloaded constructor axioms; overlapping, unknown, or false sort overrides; identity classifications requiring an override; an empty requested finite sort; constructor preregularity failure; variant-search setup failure; or incomplete variant search.

### K.3 Deferred and implementation-defined

- META-LEVEL up-mapping for some flat modules containing `special` or `poly` declarations may return the facade's deferred/failure value.
- Executable equations, memberships, and rules whose whole left-hand side is a variable are not executed in this release: a source statement of this shape is dropped with a warning, and a reflected module containing one does not down-translate (Appendix H.4.1). `[nonexec]` statements and `[narrowing]` rules are outside this boundary: a variable left-hand side does not cause them to be dropped, and a reflected module containing them still down-translates (Appendix H.4.1). This is the current boundary pending a decision; §5.4 does not make such statements invalid.
- Result ordering, generated fresh-variable spelling, internal state numbers outside documented graph records, packed-forest first-choice order, and many diagnostic wordings are Implementation-defined.
- `format`, `[print ...]`, portal metadata, trace prose, and line wrapping are Experimental presentation.
- Import-mode algebraic obligations beyond the current flattening effect are Experimental.
- Source/command resource limits are fixed where a clause names one; execution has no general semantic timeout.


# Appendix L — Normative clause index

The identifier is the stable reference; section numbers are navigational. The index is exhaustive for this edition.

| Family | Clauses | Defined in |
|---|---|---|
| authority and edition | `TNK-DOC-001`, `TNK-DOC-002`, `TNK-DOC-003`, `TNK-DOC-004`, `TNK-DOC-006`, `TNK-DOC-007` | §§0.1–0.7 |
| conformance profiles | `TNK-PROFILE-001` | §0.6 |
| sorts and kinds | `TNK-SORT-001`, `TNK-SORT-002`, `TNK-SORT-003`, `TNK-SORT-004`, `TNK-SORT-005`, `TNK-SORT-006` | §1 |
| terms and substitutions | `TNK-TERM-001`, `TNK-TERM-002`, `TNK-TERM-003`, `TNK-TERM-004`, `TNK-TERM-005`, `TNK-TERM-006` | §2 |
| runtime and GC | `TNK-RUNTIME-001`, `TNK-RUNTIME-002`, `TNK-RUNTIME-003` | §2.4 |
| equations/reduction | `TNK-REDUCE-001`, `TNK-REDUCE-002`, `TNK-REDUCE-003` | §3.1 |
| memberships | `TNK-MB-001`, `TNK-MB-002` | §3.2 |
| conditions | `TNK-COND-001`, `TNK-COND-002`, `TNK-COND-003` | §3.4 |
| rules and semantic notation | `TNK-RULE-001`, `TNK-RULE-002`, `TNK-SEM-001` | §§3.5–3.6 |
| lexer | `TNK-LEX-001`, `TNK-LEX-002`, `TNK-LEX-003` | §4 |
| term parser | `TNK-PARSE-001`, `TNK-PARSE-002`, `TNK-PARSE-003` | §4.2 |
| module/declaration/view surface | `TNK-MOD-001`, `TNK-DECL-001`, `TNK-STMT-001`, `TNK-VIEW-001` | §§5–6 |
| composition | `TNK-MOD-002`, `TNK-MOD-003`, `TNK-MOD-004`, `TNK-MOD-005`, `TNK-MOD-006`, `TNK-MOD-007` | §6.3 |
| common command rules | `TNK-CMD-001`, `TNK-CMD-002`, `TNK-CMD-REDUCE-001` | §§7–8 |
| matching | `TNK-MATCH-001`, `TNK-MATCH-002`, `TNK-MATCH-003` | §8.2 |
| rewriting | `TNK-REWRITE-001`, `TNK-REWRITE-002`, `TNK-REWRITE-003`, `TNK-CONT-001` | §9 |
| search | `TNK-SEARCH-001`, `TNK-SEARCH-002`, `TNK-SEARCH-003` | §10 |
| strategies | `TNK-STRAT-001`, `TNK-STRAT-002`, `TNK-STRAT-003` | §11 |
| unification | `TNK-UNIFY-001`, `TNK-UNIFY-002`, `TNK-UNIFY-003`, `TNK-UNIFY-004` | §12 |
| variants | `TNK-VARIANT-001`, `TNK-VARIANT-002`, `TNK-VARIANT-003`, `TNK-VARIANT-004` | §13.1–13.2 |
| narrowing | `TNK-NARROW-001`, `TNK-NARROW-002`, `TNK-NARROW-003` | §13.3 |
| SMT | `TNK-SMT-001`, `TNK-SMT-002`, `TNK-SMT-003` | §14 |
| LTL | `TNK-LTL-001`, `TNK-LTL-002`, `TNK-LTL-003` | §15.1 |
| variant satisfiability | `TNK-VSAT-001` | §15.2 |
| built-ins | `TNK-BUILTIN-001` | §16.1 |
| strict host reducers | `TNK-HOST-001`, `TNK-HOST-002`, `TNK-HOST-003`, `TNK-HOST-004` | §16.1.1 |
| reflection | `TNK-META-001`, `TNK-META-002` | §16.2 |
| objects/interpreters | `TNK-OO-001`, `TNK-OO-002` | §16.3 |
| Session state | `TNK-SESSION-001`, `TNK-SESSION-002`, `TNK-SESSION-003`, `TNK-SESSION-004`, `TNK-SESSION-005`, `TNK-SESSION-006` | §17 |
| loading | `TNK-LOAD-001`, `TNK-LOAD-002` | §17.3 |
| output and diagnostics | `TNK-OUT-001`, `TNK-OUT-002`, `TNK-OUT-003` | §18 |
| tentative invalid-input recovery | `TNK-RECOVERY-001` | Appendix H.4 |
| accounting | `TNK-COUNT-001`, `TNK-COUNT-002` | §18.2 |
| CLI | `TNK-CLI-001` | §19 |
| Rust APIs | `TNK-API-001`, `TNK-API-002`, `TNK-API-003`, `TNK-API-004`, `TNK-API-005` | §§20–22 |
| boundaries and resources | `TNK-BOUNDARY-001`, `TNK-RESOURCE-001`, `TNK-RESOURCE-002` | §§24–25 |

The index intentionally omits Appendix prose that has no independent `TNK-*` identifier. Such prose elaborates the cited clauses and cannot override them.

