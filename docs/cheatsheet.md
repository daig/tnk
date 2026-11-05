# TNK Quick Reference

*A compact recall aid for tambanokano syntax, commands, controls, and high-impact modeling gotchas*

**Document status:** explanatory and nonnormative  
**Quick Reference edition:** 2026-08-01  
**Target Reference edition:** 2026-08-01  
**Target workspace version:** `0.1.0`

> **Authority boundary:** [The TNK Language and System Reference](manual.md) defines TNK. This sheet compresses that Reference; it does not replace it. [The TNK Book](book.md) teaches the concepts and workflows. Maude documentation is useful lineage, not a TNK compatibility contract.

**Use this sheet when:** you know the concept and need to recall a spelling, choose a command, check a control, or scan common failure modes. Follow the linked `TNK-*` contract family before making a production or completeness-sensitive decision.

**Notation:** `NAME` and `term` are slots; `[x]` is optional syntax; `a | b` lists alternatives; `...` means repeated material, not a TNK token. All positions and strategy argument indexes are 1-based unless a referenced contract says otherwise.

---

## Quick reference card

### Minimal units

```maude
fmod DATA is
  sorts S T .
  subsort S < T .
  op c : -> S [ctor] .
  op f : T -> T .
  var X : T .
  eq f(c) = c .
endfm

mod SYSTEM is
  including DATA .
  op state : T -> T [ctor] .
  var X : T .
  rl [step] : state(X) => state(f(X)) .
endm

smod CONTROLLED is
  including SYSTEM .
  strat run : @ T .
  sd run := step ! .
endsm
```

- `fmod ... endfm`: equations and memberships.
- `mod ... endm`: additionally rules.
- `smod ... endsm`: additionally strategy declarations/definitions.
- `fth`/`th`/`sth`: corresponding theories.
- `omod`/`oth`: object-oriented units.
- Do **not** put a period after an `end...` keyword.

[Reference §§5–6](manual.md#5-modules-theories-and-declarations) · `TNK-MOD-*`, `TNK-STMT-001`

### Declarations and statements

```text
sort S .                         sorts S T ... .
subsort S < T .                  subsorts S T < U V < W .
op  name : S1 ... Sn -> R [attributes] .
ops name1 name2 ... : S1 ... Sn -> R [attributes] .
var X : S .                      vars X Y ... : S .

protecting MODULE-EXPR .         pr MODULE-EXPR .
extending  MODULE-EXPR .         ex MODULE-EXPR .
including  MODULE-EXPR .         inc MODULE-EXPR .

eq  lhs = rhs [attributes] .
ceq lhs = rhs if condition [attributes] .
mb  term : Sort [attributes] .
cmb term : Sort if condition [attributes] .
rl  [label] : lhs => rhs [attributes] .
crl [label] : lhs => rhs if condition [attributes] .
```

A partial operator uses `~>` instead of `->`; it produces a kind-sorted stuck term outside its intended user-sort domain, not an exception or option.

### Core command chooser

| Question | Use | Resumable |
|---|---|---:|
| What is the equation-normal value? | `reduce` / `red` | no |
| How does a pattern fit a whole subject? | `match` | no; eager result set |
| How does it fit an associative/AC portion? | `xmatch` | no; eager result set |
| Give one scheduler-driven rule path | `rewrite [n]` / `rew` | yes |
| Share rule attention among positions | `frewrite [n,gas]` / `frew` | yes |
| Drive object/external messages | `erewrite [n,gas]` / `erew` | yes |
| Explore the reachable graph | `search [n,depth]` | yes |
| Apply explicit control | `srewrite` / `dsrewrite` | no; eager result set |
| Solve equality modulo operator axioms | `unify` | no; eager result set |
| Enumerate symbolic normal forms | `get variants` | yes |
| Explore symbolic rule reachability | `vu-narrow` / `fvu-narrow` | yes |
| Ask the selected SMT backend | `check` / `smt-search` | search is resumable |

`check` is an SMT formula command. It is not a general type checker, confluence checker, or LTL model-checking command.

### Core command spellings

```text
reduce [in M :] term .
match  [in M :] pattern <=? subject .
xmatch [in M :] pattern <=? subject .

rewrite  [n]     [in M :] term .
frewrite [n]     [in M :] term .
frewrite [n,gas] [in M :] term .
erewrite [n]     [in M :] configuration .
erewrite [n,gas] [in M :] configuration .
continue [n] .

search [n]       [in M :] initial ARROW goal [such that condition] .
search [n,depth] [in M :] initial ARROW goal [such that condition] .

srewrite  [in M :] term using Strategy .
dsrewrite [in M :] term using Strategy .
```

### Bounds and search arrows

| Form | Meaning |
|---|---|
| `[n]` | positive first bound: results or rule applications, by command |
| `[n,m]` | positive command-specific second bound: depth or gas |
| `continue n .` | at most `n` additional results/applications; `0` is valid here |
| `=>1` | exactly one rule transition |
| `=>+` | one or more transitions |
| `=>*` | zero or more; the initial state is eligible |
| `=>!` | terminal states only |

Bracketed zero components are rejected for `rewrite`, `frewrite`, `erewrite`, search/SMT-search, variants, variant unification/matching, and narrowing. Ordinary `unify [0]` is a known unsupported parser/driver edge and must not be used as a semantic query. A bound returns a prefix; it is **not** proof of exhaustion or unreachability. `continue 0 .` is valid; `smt-search =>!` is Unsupported.

[Reference §§7–11](manual.md#7-common-command-rules) · [command catalogue](manual.md#appendix-a--command-catalogue) · `TNK-CMD-*`, `TNK-REWRITE-*`, `TNK-SEARCH-*`

---

## Top gotchas

1. **TNK is not defined by Maude.** Similar syntax does not imply identical commands, defaults, libraries, unsupported edges, result order, or diagnostics.
2. **There is no implicit library prelude.** `Session` and lower layers start bare. The `tnk-repl` executable merely *tries* to load `prelude.maude` unless `-no-prelude` is supplied.
3. **Terminator rules are selective.** Declarations, statements, and most commands end in ` .`; module/view closing keywords do not. `load` and `sload` are line-terminated; a final ` .` is optional.
4. **Put portable top-level items on separate physical lines.** Two commands on one physical line form one invalid Session submission. A period is also allowed inside an identifier, so whitespace and line boundaries matter.
5. **`in M :` is local to one command.** It does not select `M`. `select M .` changes the current module and always clears the saved continuation—even if `M` was already current.
6. **A bound is a prefix, not a proof.** No reported solution before a bound says nothing about unreachability. Finite exhaustion, truncation, solver incompleteness, `Unknown`, Unsupported, and resource exhaustion are different outcomes.
7. **`rewrite` follows one path; `search` explores a graph.** One rewrite result is never evidence that every transition path has the same outcome.
8. **Equation normalization can hide an incoherent rule.** Rule-fair rewriting and ordinary search canonicalize before rule matching. Rules must agree across equation-equivalent representatives. TNK does not prove termination, confluence, or coherence. See [the Book example](book.md#keep-rules-coherent-with-equation-canonicalization) and `TNK-RULE-002`.
9. **An identity can erase the apparent pattern root.** With `op __ ... [assoc id: nil]`, pattern `a X` can match bare `a` by binding `X` to `nil`. See [the Book example](book.md#an-identity-can-remove-the-pattern-root) and `TNK-TERM-003`.
10. **A binding condition is multi-solution unless the model makes it functional.** A `:=` or rewrite fragment may offer several branches; the first complete branch wins. Do not use its binding as a function result without uniqueness or equal-result invariants. See [the Book guidance](book.md#treat-a-binding-condition-as-a-relation) and `TNK-COND-001`.
11. **Matching uses structural axioms, not arbitrary user equations.** Normalize explicitly when that is the intended boundary.
12. **Lower precedence numbers bind tighter.** Each `_` in a mixfix name is one argument hole. Parenthesize or use `(term).Sort` rather than depending on an ambiguous packed-forest choice.
13. **`frozen` blocks rule/narrowing descent, not required equation normalization.** `strat (...)` controls equational evaluation order.
14. **Result ordering is usually not semantics.** Equal-depth successors, AC partitions, unifiers, generated fresh names, internal AC print order, and many diagnostic details are implementation-defined or presentation-only.
15. **Aggregate `rewrites:` is diagnostic.** It can include equations, memberships, rules, conditions, symbolic steps, and built-ins. Rule/search depth counts rule transitions, not that aggregate.
16. **Parser recognition does not prove capability.** Built-ins need loaded hooks; Z3 needs the per-crate `smt-z3` feature and a provisioned backend; LTL is a hooked operator surface, not a standalone command.
17. **`Unknown` proves neither satisfiable nor unsatisfiable.** The default null SMT backend returns `Unknown`; SMT-search prunes it but that pruning is not an impossibility proof.
18. **Accepted work may diverge.** Reduction, rewrite conditions, rewriting, search, strategies, variants, narrowing, model checking, and solver enumeration have no semantic timeout or cancellation token.
19. **Import modes currently donate equally.** `protecting`, `extending`, and `including` retain their source tags, but protection obligations are Experimental and not enforced.
20. **Text output is not a typed event API.** Stable semantic fields coexist with experimental prose and incomplete completion classification. Hosts needing typed outcomes must use lower-level owners.

---

## Source syntax

### Lexical essentials

- Token separators: whitespace and `(` `)` `[` `]` `{` `}` `,`.
- `_`, operators, and ordinary periods may be identifier characters.
- A backquote escapes a splitting character into an identifier.
- `***` and `---` start line comments; a balanced parenthesized comment may cross lines.
- Spacing changes literal tokenization: `1/6` is a rational literal; `1 / 6` is an operator application. `-7` is one integer token; `- 7` is not.
- Numerals, rationals, floats, strings, and quoted identifiers obtain semantics only when the loaded signature supplies their hooks.
- Redundant hole-bearing prefix syntax such as `_+_(a,b)` is not generated. Use the declared mixfix form.

[Reference §4](manual.md#4-lexical-syntax) · `TNK-LEX-*`, `TNK-PARSE-*`

### Sorts, kinds, and variables

```maude
sort Nat .
sorts NzNat Int .
subsort NzNat < Nat .
op pred : Nat ~> Nat .
var N : Nat .
```

- `<` declares subsort inclusion; it is not a conversion.
- Each connected sort component has a synthesized bracketed error/top sort called its **kind**.
- A partial `~>` application can remain at kind sort.
- A substitution must bind a variable only to a term of the variable's sort or a subsort.
- An occurrence such as `X:Nat` declares its sort inline in that local term scope. A bare `X` must be declared in source scope.
- Overload resolution uses applicable domains and a least result. Use `(term).Sort` to disambiguate explicitly.

### Mixfix operators

```maude
op _+_ : Nat Nat -> Nat [ctor assoc comm id: 0 prec 33 gather (E e)] .
op if_then_else_fi : Bool Nat Nat -> Nat [strat (1 0)] .
```

- Number of `_` holes = arity.
- Lower `prec` = tighter binding.
- Gather marks each hole: `E` strong, `e` weak, `&` unconstrained.
- Parentheses are the first-choice disambiguation tool.

### Operator attributes

| Family | Attributes | Effect / boundary |
|---|---|---|
| algebraic | `assoc`, `comm`, `id: t`, `left id: t`, `right id: t`, `idem`, `iter` | canonicalization and theory matching; only documented combinations are supported |
| constructors | `ctor` | constructor metadata for symbolic analyses |
| grammar | `prec n`, `gather (...)` | generated term grammar |
| evaluation | `strat (...)` | equation argument/top order (`0` = top attempt) |
| descent | `frozen`, `frozen (...)` | blocks rule/narrowing descent at all or selected positions |
| polymorphism | `poly (...)` | expands listed argument/range positions over kinds |
| presentation | `format (...)` | pretty-printer layout |
| built-ins | `special (...)` | attaches a supported hook after resolution |
| object/external | `config`, `obj`, `msg`, `portal` | scheduler roles |
| metadata | `metadata`, `latex`, `rpo` | accepted metadata/hints; no direct execution semantics |
| unsupported execution | `memo` | accepted with warning; no memoization effect |

Supported structural families:

| Attributes | Semantic shape |
|---|---|
| none | free ordered fixed-arity tree |
| `assoc` with optional identity | AU/A flattened ordered word |
| `assoc comm` with optional identity | ACU/AC flattened multiset |
| supported non-associative `comm`/`id:`/`idem` combinations | binary CUI family |
| unary `iter` | compact repeated application |

A lone one-sided identity on a non-associative, noncommutative operator remains free for ordinary construction and matching; commutativity makes a one-sided identity two-sided.

Do not infer `[assoc idem]` or `[assoc comm idem]` support from the separate AU/ACU and CUI implementations.

### Statement attributes

| Attribute | Meaning |
|---|---|
| `[label]` | stable name for trace, rule, and strategy selection |
| `[owise]` | equation/membership tried after ordinary statements for the symbol |
| `[nonexec]` | retained as specification material, excluded from ordinary execution |
| `[variant]` | equation/membership participates in variant generation |
| `[narrowing]` | rule participates in narrowing |
| `[metadata "text"]` | retained metadata |
| `[print ...]` | experimental presentation metadata |

Unknown attributes are invalid input. `memo` is recognized but semantically unavailable.

---

## Computation model

### Keep the three layers separate

| Layer | Source | Meaning |
|---|---|---|
| structural axioms $A$ | operator attributes | quotient canonicalization, matching, theory solving |
| deterministic computation $E/M/H$ | equations, memberships, hooks | normalize data and refine least sorts |
| transitions $R$ | rules | produce graph edges and evolving states |

- `reduce` uses equations, memberships, and hooks; never ordinary rules.
- Rule drivers and search use rules around command-required equation normalization.
- Search interns equal equation-normal states modulo structural axioms.
- Put deterministic representation cleanup in equations. Put observable change in rules.

### Conditions

```text
u = v      reduce both sides; require axiom-canonical equality
u : S      reduce u; require least-sort(u) <= S
p := u     reduce u; match p; introduce fresh pattern bindings
u => p     crl only; breadth-first nested rewrite search; bind from p
b          abbreviation for b = true; requires the loaded truth hook
```

Join fragments with `/\`; evaluation and variable introduction are left-to-right. Later failure backtracks to the nearest earlier multi-solution match/rewrite fragment and restores failed bindings. Rewrite conditions may explore an infinite graph.

### Rule coherence check by hand

Before relying on search/model checking:

1. Identify the intended canonical forms under equations and attributes.
2. Reduce representative rule left sides.
3. Confirm every intended transition is still matchable from those normal forms.
4. Confirm equation-equivalent representatives induce the same rule behavior.
5. Separately justify equation termination/confluence where the model needs unique normal forms.

TNK executes the resulting system; it does not discharge those proof obligations.

---

## Commands in more detail

### Matching

```text
match  [in M :] pattern <=? subject .
xmatch [in M :] pattern <=? subject .
```

`match` covers the whole subject. `xmatch` may expose a proper associative/AC portion plus residue. Both enumerate sound, duplicate-free, sort-correct substitutions; finite unbounded enumeration is complete. Enumeration order is implementation-defined.

### Rewriting modes

| Command | Scheduler | Bound counts | Important boundary |
|---|---|---|---|
| `rewrite [n]` | normalize, then first top-down redex; rotates per-symbol rule cursors | rule applications | one path, not all paths |
| `frewrite [n,gas]` | repeated non-frozen position passes | rule applications; gas per position/pass | bounded stop may be noncanonical with unknown sort |
| `erewrite [n,gas]` | object/message deliveries; position-fair fallback | configuration deliveries | experimental and hook-loaded |

A new bounded resumable command saves one continuation. `continue` resumes its retained graph/solver/roots/counters. Do not rely on continuation after an intervening execution command. `select` always clears it.

### Search

```text
search [solutions,depth] [in M :] initial ARROW goal [such that condition] .
```

- Breadth-first; solution depths are nondecreasing.
- Equal canonical states become one graph node.
- In a finite graph with no depth bound, ordinary search is complete.
- `show path N .` uses the retained BFS predecessor tree.
- `show search graph .` reports only the portion discovered so far.
- `show frontier states .` / `show most general states .` inspect supported retained symbolic searches.

### Strategies

```text
srewrite  [in M :] term using Strategy .
dsrewrite [in M :] term using Strategy .
```

| Form | Recall |
|---|---|
| `idle`, `fail`, `all` | unchanged success, no result, every applicable rule |
| `E ; F` | sequence |
| `E | F` | union |
| `T ? S : F` | run `S` on every `T` result; otherwise `F` on original |
| `E*`, `E+`, `E!` | iteration; `!` emits a strategy normal form |
| `top(E)`, `one(E)`, `try(E)`, `not(E)`, `test(E)` | focused/derived controls |
| `or-else(E,F)` | fallback |
| `match` / `xmatch` / `amatch` | strategy tests |
| `matchrew ... by X using E` | rewrite named matched subterms and rebuild |
| `label[X <- term]` | apply labeled rule with initial substitution |
| `name(args)` | call an unconditional `sd` definition |

`srewrite` is fair/FIFO; `dsrewrite` is depth-first. `xmatchrew` and conditional `csd` definitions parse but are Unsupported.

---

## Symbolic and verification facilities

### Unification

```text
unify [n] [in M :] u =? v [ /\ u2 =? v2 ... ] .
irredundant unify [n] [in M :] ... .
```

Ordinary unification is eager and not resumable. Supported non-ground families include free, iteration, commutative/identity CUI without idempotence, AC/ACU, and associative/AU. Non-ground idempotent CUI and associative one-sided-identity problems are Unsupported. AU exploration can be incomplete; the Session text renderer does not expose every low-level completion flag.

### Variants

```text
get variants [n] [in M :] term [such that B1, ... irreducible] .
get irredundant variants [n] [in M :] term [such that ... irreducible] .
variant unify [n] [in M :] u =? v [ /\ ... ] [such that ... irreducible] .
filtered variant unify [n] [in M :] ... .
variant match [n] [in M :] pattern <=? subject [such that ... irreducible] .
```

Variant generation uses executable equations selected by `[variant]`; `[variant]` memberships join the same symbolic family. Incremental mode can stream; irredundant/filtered modes may need exhaustion before emitting final survivors. Sound results do not imply complete exhaustion.

### Narrowing

```text
[{fold|vfold|path}, ...] vu-narrow [{filter|delay}, ...]
  [n] or [n,depth] [in M :] initial ARROW goal [such that condition] .
fvu-narrow ...
```

Narrowing uses rules marked `[narrowing]`, including `[nonexec narrowing]`. Conditional narrowing rules are Unsupported. Completion requires graph exhaustion and no nested solver incompleteness or depth truncation.

### SMT, LTL, and variant satisfiability

| Facility | Boundary |
|---|---|
| `check formula .` | `Sat`/`Unsat`/`Unknown`/`BadDag`; hooked SMT symbols required |
| `smt-search` | carries path constraints; only `Sat` successors survive |
| default build | null SMT backend; returns `Unknown` |
| `smt-z3` profile | per-crate feature plus provisioned native Z3 |
| LTL | hooked operators, normally from `model-checker.maude`; finite graphs decide |
| variant satisfiability | TNK facade over eligible FVP/OS-compact constructor theories; separate from SMT |

[Reference §§12–16](manual.md#12-order-sorted-unification) · [feature matrix](manual.md#23-current-feature-classification) · `TNK-UNIFY-*`, `TNK-VARIANT-*`, `TNK-NARROW-*`, `TNK-SMT-*`, `TNK-LTL-*`

---

## Session, loading, and CLI

### Session state

One `Session` persistently owns modules/views, current selection, settings, loaded-file set, reflection state, local interpreters, and at most one continuation. Independent Sessions share no semantic state.

```text
select NAME .
show modules .                  show module [NAME] .
show views .                    show view NAME .
show path [states] N .          show search graph .
show frontier states .          show most general states .
```

Bare `quit`, `q`, or `exit` is line-terminated and sets `Eval.exit = true`; a library host decides whether that ends anything.

### Settings

```text
set trace [condition|whole|substitution|rewrite|body|builtin|eqs|mbs|rls] on|off .
set include BOOL on|off .
set show breakdown on|off .
set verbose on|off .
```

Trace, implicit `BOOL`, breakdown, and verbose output are off by default in a bare Session. `set show timing`, `set memo`, and memo-clear controls are recognized but unavailable and have no semantic effect.

### Loading

```text
load FILE
sload FILE
```

The period is optional: a final ` .` after whitespace is dropped, but a `.` glued to the name stays part of the path. Session loading tries the written path and then `.maude`, first from the process working directory and then each `MAUDE_LIB` directory. `sload` skips a canonical path after its first load in that Session. Nested loads are not resolved relative to the containing file.

The CLI positional `FILE` is different: it is opened exactly as written, without extension completion or `MAUDE_LIB` search.

### CLI

```sh
tnk-repl [-no-prelude] [-no-banner] [FILE]

# workspace, reproducible prelude-free run
cargo run --release -p tnk-repl -- -no-banner -no-prelude program.maude
```

The REPL attempts `prelude.maude` via `MAUDE_LIB`, then the current directory, unless disabled. Failure to locate it warns and continues bare.

### Embedding

```rust
use tnk_session::Session;

let mut session = Session::new();
let eval = session.eval("reduce in M : term .", false);
if eval.exit {
    // Host chooses how to interpret quit.
}
println!("{}", eval.output);
```

Strict Rust reducer capability:

```rust
use tnk_core::host::{HostFunctionCatalog, codecs};
use tnk_session::Session;

fn slug(input: &[u8]) -> Vec<u8> {
    input.to_ascii_lowercase()
}

let catalog = HostFunctionCatalog::builder()
    .register_typed1("text.slug", codecs::string(), codecs::string(), slug)
    .expect("register text.slug")
    .build();
let mut session = Session::builder().host_functions(catalog).build();
```

```maude
[special (id-hook HostFunctionSymbol (text.slug)
          op-hook stringSymbol (<Strings> : ~> String))]
```

Register before module construction. A key has at least two dot-separated segments; each begins with lowercase ASCII, contains only lowercase ASCII letters/digits/interior hyphens, and never ends in a hyphen. The root must be fixed-arity, free-theory, and standard eager. Arguments arrive normal but may be symbolic or undecodable. Typed adapters borrow byte-string inputs without cloning, gate callback invocation on all arguments decoding, and encode the owned output through `stringSymbol`. Decode miss/`Decline` falls through to equations; `Reduced` counts once, is recorded as `RewriteKind::HostFunction` with the canonical key in both structured and rendered traces, and its checked result is normalized. Every other `TraceEvent::Rewrite` carries no host key. `ReducerFault` aborts the semantic operation. Catalog-unaware constructors use an empty catalog.

This is a trusted, pure, deterministic, synchronous callback boundary—not lazy control, I/O, state, dynamic loading, or a panic sandbox. `ReducerFault` restores TNK-owned operation state, aggregate/breakdown counts, and trace append state; it never falls through, and a faulted resumable owner returns the same error thereafter. This is not a general user transaction and does not roll back callback-authored external side effects. Callback panics are not converted to `ReducerFault` and have no rollback guarantee. `HostControlSymbol` is only a reserved inert/nonbinding future boundary; it never consults the strict catalog, even for a registered key. `Eval { output, exit }` is synchronous presentation output, not a typed semantic result stream; there is no cancellation, timeout, preemption, reentrancy, or thread-safety guarantee. Reducer authors own termination and CPU/memory bounds; use process isolation for interruption and lower-level typed owners for completeness-sensitive control flow.

---

## TNK versus familiar Maude assumptions

| Familiar assumption | TNK 0.1.0 reality |
|---|---|
| Maude behavior is the compatibility oracle | TNK Reference clauses are authoritative |
| library APIs implicitly load predefined modules | no implicit prelude; hooks exist only after their modules load |
| every Maude command/flag is available | only the documented TNK surface is supported |
| import modes enforce their traditional proof obligations | modes currently donate equally; obligations are Experimental |
| `memo` and timing controls execute | recognized but semantically unavailable |
| `xmatchrew` and conditional strategy definitions execute | parsed, then rejected as Unsupported |
| ordinary search tracing is available | use graph/path inspection; search tracing is Unsupported |
| model checking is a parser command | LTL is a loaded hooked operator surface |
| textual result order/format matches another implementation | only TNK's named semantic fields and ordering invariants apply |

For migration boundaries, see [Book Appendix E](book.md#appendix-e--maude-lineage-and-migration) and [Reference §24](manual.md#24-unsupported-and-intentionally-absent-behavior).

---

## Debugging checklist

1. **Capability:** Which build profile and loaded modules/hooks does this input require?
2. **Selection:** What is the current module? Did `in M :` merely qualify one command?
3. **Lex/parse:** Are periods line-delimited? Are mixfix holes, precedence, gather, and overloads unambiguous?
4. **Normalize:** Run `reduce` on the subject and important rule/equation subterms.
5. **Match:** Run `match`/`xmatch` on the exact left side and canonical subject. Check identity bindings and AC alternatives.
6. **Conditions:** Enable focused condition/substitution tracing; check left-to-right binding and backtracking.
7. **Transitions:** Use a small `rewrite [n]` to inspect one path, then bounded `search` to inspect branching.
8. **Retained graph:** Use `show path N .` and `show search graph .`; remember a bounded graph is only a discovered prefix.
9. **Stop reason:** Separate finite exhaustion, user bound, divergence, unsupported theory, incompleteness, backend `Unknown`, and resource exhaustion.
10. **Model obligations:** Check equation termination/confluence assumptions and rule coherence at canonical forms.
11. **Automation:** Consume typed lower-level outcomes when text prefixes and fields cannot classify the result safely.

[Book Chapter 21](book.md#chapter-21--diagnostics-tracing-and-debugging) · [Reference output contract](manual.md#18-output-contract) · `TNK-OUT-*`, `TNK-RESOURCE-*`

---

## Where to go next

| Need | Document |
|---|---|
| Learn concepts progressively | [The TNK Book](book.md) |
| See exact syntax and semantics | [TNK Language and System Reference](manual.md) |
| Choose a command | [Book Appendix D](book.md#appendix-d--command-and-capability-quick-guide) |
| Find every command and alias | [Reference Appendix A](manual.md#appendix-a--command-catalogue) |
| Check operator/statement attributes | [Reference Appendix F](manual.md#appendix-f--declaration-and-statement-attributes) |
| Check hooks and libraries | [Reference Appendix G](manual.md#appendix-g--built-in-hook-catalogue) |
| Classify output and recovery | [Reference Appendix H](manual.md#appendix-h--observable-result-and-diagnostic-schema) |
| Inspect public Rust entry points | [Reference Appendix I](manual.md#appendix-i--rust-api-map) |
| Check build/runtime capabilities | [Reference Appendix J](manual.md#appendix-j--feature-status-and-conformance-profiles) |
| Check Unsupported/incomplete surfaces | [Reference Appendix K](manual.md#appendix-k--unsupported-incomplete-and-deferred-surfaces) |
| Resolve a normative question | [Reference Appendix L](manual.md#appendix-l--normative-clause-index) |
