# Changelog

All notable user-visible changes are documented here. This project follows Semantic Versioning for release identifiers; compatibility guarantees are qualified by the feature states in the normative reference.

## [Unreleased]

### Added

- Added immutable host-function catalogs and strict Rust reducers: source operators can bind typed or scoped in-process callbacks through `HostFunctionSymbol`, with eager argument normalization, build-time strategy/hook validation, equation fallthrough, checked result normalization, structured tracing/accounting, and fault propagation across Session, reflection, child-interpreter, rewrite, search, variant, and narrowing paths.
- Added catalog-aware Session, frontend, module, reflection, and low-level Engine construction paths. Catalogs survive module sums, views, parameter instantiation, renaming, dependent rebuilds, and nested execution without process-global registration or live callback replacement.

### Correctness and hardening

- Scoped callback DAG wrappers and callback-lifetime `HostSymbol` capabilities prevent raw engine-handle escape, captured or cross-engine callback construction, reentrant reduction, and unsafe collection. Host bindings are sealed before semantic execution; missing capabilities and incompatible eager schedules, overloads, sorts, theories, or supporting hooks reject module construction.

- Cyclic subsort declarations, including self-loops and cycles formed only through imports, are now rejected with an ordinary `error:` module diagnostic instead of panicking (the CLI previously exited with status `101`). The invalid module is not installed and the Session continues. `Sorts::subsort_cycle` and `Engine::subsort_cycle` expose the check to low-level callers.

- `modExp(B, E, M)` now reduces to `B^E mod M` for every natural base, including a base at or above the modulus and any base with modulus `1`, instead of panicking (the CLI previously exited with status `101` and printed nothing for the whole submission). This also covers `metaReduce` of such terms. A zero modulus still leaves the term unreduced.

- The CONVERSION built-ins no longer read the kind-level `I / 0` that the division built-in leaves unreduced as a rational: `float(I / 0)` now stays unreduced instead of panicking, and `string(I / 0, B)` stays unreduced instead of producing the invented string `"I/0"`. `rat(S, B)` likewise falls through when the denominator in `S` is negative, instead of dropping its sign (`rat("3/-2", 10)` gave `3/2`).

- `irredundant unify`, `metaIrredundantUnify`, and variant generation (for example `get variants`) no longer panic when a binding under an operator with a one-sided identity contains an `iter` count of `2^64` or more; the redundancy filter now keeps the arbitrary-precision count.

- `find`, `rfind`, and `substr` now reduce when an index or count argument is `2^64` or more. The answer is the same as for any other position past the end of the string: `notFound` for `find`, the last occurrence for `rfind`, and a clamped slice for `substr`. These applications previously stayed unreduced, so for example `find("ab", "b", 18446744073709551616) == notFound` gave `false`.

- `_^_`, `_<<_`, and `_>>_` now reduce for an exponent or shift count of `2^64` or more whenever the exact result is small: `0 ^ N`, `1 ^ N`, `(-1) ^ N` (by parity), `0 << N`, and `I >> N` (`0`, or `-1` for a negative `I`). Previously these applications stayed unreduced, so `1 ^ 18446744073709551616 == 1` gave `false`. Any other base, and any nonzero value shifted left, still stays unreduced for such counts. A negative shift count lies outside `_<<_`/`_>>_ : Int Nat -> Int`, so the application now stays unreduced, as one with a negative exponent already does. Previously it shifted by the count's magnitude: `7 >> -1` gave `3`.

- `I ^ N` no longer returns a wrong value, panics, or aborts when `N` fits 64 bits but the power's size bound, the bit length of `|I|` times `N`, overflows 64 bits (such a power has more than `2^63` bits). In these cases the numeric backend's unchecked size arithmetic wrapped: `2 ^ 9223372036854775808` reduced to `1`, `7 ^ 6148914691236517206` panicked (the CLI exited with status `101`), and `3 ^ 18446744073709551615` aborted. Both crashes lost the whole submission's output. Such a power now stays unreduced, as one with an exponent of `2^64` or more already did. Other powers too large to allocate, such as `3 ^ 9223372036854775807`, are unchanged by this fix.

- Each `CounterSymbol` operator now has its own `0, 1, 2, ...` sequence. Previously all counter operators in a module drew from one shared value. This affected two directly declared counters as well as a renamed copy such as `COUNTER * (op counter to counter2)`. With such a copy, `rewrite counter counter2 counter counter2 .` gave `0 1 2 3` instead of `0 0 1 1`, and in a fresh `rewrite counter2 counter2 counter .` the `counter` gave `2` instead of `0`. The fix applies to `rewrite`, `frewrite`, `erewrite`, `continue`, `metaRewrite`, and `metaFrewrite`. All counters still restart at `0` for each top-level rewriting command. Modules with a single counter operator are unaffected.
- Within one statement or command, a variable is now identified by its written name and resolved sort. A declared `X : S` and an on-the-fly `X:S` are therefore one variable, and so are the kind spellings `X:[A]` and `X:[B]` of one kind. Previously each spelling got its own slot, but the unifier treated them as one, which caused four failures:
  - `unify` and `metaUnify` could return unsound unifiers;
  - `match`, `search`, variant, and narrowing commands bound the spellings independently;
  - equations such as `eq g(X) = X:S` were dropped as having an unbound right-hand-side variable;
  - a `search` condition that named the goal variable by its other spelling panicked.

  A matchrew `by` variable may now use any spelling of a pattern variable. Object-pattern completion no longer reuses a written `V:Class` as its fresh class variable.

### Documentation

- Documented the public reducer API, source attachment grammar, purity/trust boundary, fault policy, supported typed adapters, feature status, and end-to-end configured Session workflow.

## [0.1.0] - 2026-07-29

Initial supported release of tambanokano.

### Added

- Order-sorted signatures with kinds, subsorts, overload resolution, memberships, partial operators, and free, AU, ACU, and CUI canonical term representations.
- Equation reduction, conditional rewriting, fair rewriting, breadth-first reachability search, saved continuations, search graph inspection, and path reconstruction.
- A strategy engine with fair and depth-first scheduling, combinators, rule applications, tests, match-rewrite, and lazy recursive parameterized strategy calls.
- Order-sorted unification, irredundant unifier filtering, variants, variant unification and matching, narrowing, variant satisfiability, and explicit incompleteness outcomes.
- Native LTL model checking and satisfiability, a default null SMT backend, and an optional Z3 backend behind `smt-z3`.
- Module and view databases with imports, sums, structural renaming, parameter instantiation, dependent rebuilds, import hygiene checks, and transactional definition failure.
- Object-module desugaring, external stream objects, interpreter-manager objects, metalevel command descent, module/term reflection, and child interpreter state.
- Reusable `tnk-core`, `tnk-frontend`, `tnk-modules`, and `tnk-session` APIs plus the interactive `tnk-repl` executable.
- A documentation suite comprising the normative language and system Reference, a guided TNK Book, and a compact Quick Reference for syntax, commands, controls, and modeling gotchas.

### Correctness and hardening

- Preserved DAG roots across GC-capable reduction, matching, unification, strategy, reflection, and condition-evaluation paths; engine-relative handles now fail fast when used with the wrong engine.
- Made deeply nested condition evaluation heap-growing rather than dependent on the native call-stack limit.
- Enforced declaration-group kind coherence, least-sort selection, safe fresh-variable families, unsupported-theory screening, import-cycle rejection, and free-parameter import rejection.
- Kept rewrite counts, continuation state, module selection, source diagnostics, and failed-definition rollback consistent across direct, imported, renamed, instantiated, and reflected modules.
- Made recursive parameterized strategy definitions runtime-lazy, removing any resolution-time expansion bound.
- Added strict CLI argument parsing: unknown flags and extra files exit with status 2; unreadable requested files exit with status 1; evaluation diagnostics remain session output.
- Hardened differential tooling against timeouts, missing binaries and libraries, subprocess failures, stale expected output, and shell word-splitting of library paths.

### Verification

- Added deterministic unit and integration coverage across every workspace layer, including behavioral boundary tests for parsers, continuations, GC safety, unsupported unification, metalevel caches, object systems, and CLI process behavior.
- Added retained conformance fixtures for the supported source language, prelude surfaces, strategies, modules/views, reflection, SMT, LTL, objects, variants, narrowing, and recursive parameterized strategy calls.
- Added per-fixture historical differential regression checks using Maude, subsystem and audit scoreboards, and a pinned native variant-satisfiability value contract.

### Explicit boundaries

- Rust source compatibility and surfaces marked Experimental may change during the 0.x series.
- `xmatchrew`, conditional strategy definitions, memoization execution, conditional narrowing rules, semantic timing, and the other cases listed in §24 of the reference are not supported in this release.
- Stock Maude companion libraries in `share/maude-gpl` and specified prelude-derived fixtures remain GPLv2-or-later; original TNK code and materials are MIT licensed.
