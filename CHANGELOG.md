# Changelog

All notable user-visible changes are documented here. This project follows Semantic Versioning for release identifiers; compatibility guarantees are qualified by the feature states in the normative reference.

## [Unreleased]

### Added

- Added immutable host-function catalogs and strict Rust reducers: source operators can bind typed or scoped in-process callbacks through `HostFunctionSymbol`, with eager argument normalization, build-time strategy/hook validation, equation fallthrough, checked result normalization, structured tracing/accounting, and fault propagation across Session, reflection, child-interpreter, rewrite, search, variant, and narrowing paths.
- Added catalog-aware Session, frontend, module, reflection, and low-level Engine construction paths. Catalogs survive module sums, views, parameter instantiation, renaming, dependent rebuilds, and nested execution without process-global registration or live callback replacement.

### Correctness and hardening

- Scoped callback DAG wrappers and callback-lifetime `HostSymbol` capabilities prevent raw engine-handle escape, captured or cross-engine callback construction, reentrant reduction, and unsafe collection. Host bindings are sealed before semantic execution; missing capabilities and incompatible eager schedules, overloads, sorts, theories, or supporting hooks reject module construction.

- Cyclic subsort declarations, including self-loops and cycles formed only through imports, are now rejected with an ordinary `error:` module diagnostic instead of panicking (the CLI previously exited with status `101`). The invalid module is not installed and the Session continues. `Sorts::subsort_cycle` and `Engine::subsort_cycle` expose the check to low-level callers.

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
