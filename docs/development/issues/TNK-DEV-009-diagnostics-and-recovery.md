# TNK-DEV-009 — Diagnostics and invalid-input recovery

**Status:** Known gap  
**Type:** Correctness and user experience  
**Current contract:** [`docs/manual.md` §0.5 and Appendix H.3–H.4](../../manual.md#05-diagnostics-limits-and-invalid-input)

## Current behavior

Appendix H.4 is the user-facing ledger for known invalid-input and unsupported seams. It records silent token skipping, repaired declarations, nonuniform attribute handling, dropped statements, inert hooks/controls, and incomplete command output. The former cyclic-subsort panic is resolved (see item 1), as are the variable-left-hand-side panics (see item 7). These behaviors are Experimental and are not accepted-input guarantees.

## Developer work

The long-term direction is uniform ownership and state effects, not exact Maude warning prose. Work should be split by owning boundary while preserving the common classifications in `TNK-DOC-006`:

1. ~~eliminate process panic for cyclic subsorts and return a sort/declaration diagnostic without installing a partial definition;~~ **Done.** The frontend signature builder checks the flattened subsort graph before sort closure (so within-module cycles, self-loops, and import-formed cycles are all caught) and rejects the module with an ordinary `error:` declaration diagnostic; nothing is installed and the Session continues. Pinned by `crates/tnk-session/tests/session.rs` and `crates/tnk-repl/tests/cli.rs`; the H.4 row is removed;
2. make invalid declaration attributes reject or recover consistently and visibly;
3. make equation/rule/membership attribute parsing follow one policy;
4. diagnose unsupported hooks and unknown Session controls without claiming success; *partial:* rejected `show`, `select`, `set trace`, and `continue` requests, and commands with no current module, now carry the Stable `error:` prefix (pinned by `crates/tnk-session/tests/session.rs`); `smt-search` requests rejected during command construction (`=>!`, the SMT-rewriting restrictions, unsupported `such that` conditions) now report an `error:` diagnostic instead of printing nothing (same test file; see TNK-DEV-012); unknown `set` controls and unsupported hooks remain silent;
5. expose unsupported unification and SMT `BadDag` outcomes distinctly from no result;
6. retain atomic module/view and command state transitions on failure;
7. ~~eliminate process panics for executable statements whose whole left-hand side is a variable~~ **Done for the panic only.** Source equations now take the membership/rule drop-with-warning path; reflected equations, memberships, and rules of this shape make META descent fail like any other invalid reflected statement (inert descent, `wellFormed` false, `insertModule` error) instead of panicking or being skipped silently; and an imported statement keeps the boundary verdict of its home grammar, so an importer declaration cannot reinterpret it. Pinned by `crates/tnk-frontend/src/load.rs`, `crates/tnk-modules/src/load.rs`, `crates/tnk-repl/src/tests.rs`, and `crates/tnk-repl/tests/cli.rs`; the current boundary is recorded in Appendix H.4.1 and K.3. **Open decision:** whether these statements should execute (offered to every symbol of the variable's kind) or become a §5.4 static requirement. Execution would touch the kernel's top-symbol statement indexes, collapse-pattern and substitution-layout bookkeeping, variant and narrowing tables, strict host-function sealing, symbols created after statements are installed, and the matching-extension semantics of such rules.
8. **Partial:** an unconditional strategy definition whose parameter or body does not resolve, or whose name and parameter kinds match no strategy declaration, is still dropped on its own, but its module build now reports it with a `warning:` naming the definition and the reason, like a dropped statement, instead of leaving its calls to answer `No solution.` silently. The warning comes from the same compilation that strategy commands run, so each warning names a definition those commands really leave out. Pinned by `crates/tnk-frontend/src/strategy.rs` and `crates/tnk-repl/src/tests.rs`; the current boundary is recorded in Appendix H.4.1. **Open decision:** whether an invalid strategy definition stays isolated in this way or makes the module definition invalid. `TNK-STMT-001` permits statement-local isolation only for the statements of §5.4, so the default of `TNK-DOC-006` would be atomic rejection, while the retained conformance fixture `conformance/audit/A3i-strategy-import-home.maude` relies on the module surviving a malformed definition. Still silent (H.4.1): a strategy declaration naming an undeclared sort, and a `csd` or `xmatchrew` definition beside an executable definition of the same name and arity, whose calls run the other definitions alone although Appendix K.1 promises no partial definition. Also still silent: a definition whose strategy profile is declared by more than one origin (for example an importer redeclaring an imported profile), which is left out without a warning.

## Constraints

- Accepted valid input must not change behavior while invalid-input recovery is corrected.
- Diagnostics need stable category and state effect; prose need not become a compatibility surface.
- A repaired declaration must never retain a silently different semantic theory without a documented policy.
- Panic-hook output is not a Session diagnostic.
- Fixes should defend public `Session` and CLI behavior, not source-text implementation details.

## Completion gate

Appendix H.4 shrinks as cases acquire behavior consistent with H.3. The issue closes only when no listed case panics, silently performs a different semantic operation, or produces an ambiguous success/no-result record. Remaining deliberate unsupported behavior moves to Appendix K with an explicit diagnostic/effect.

## Provenance

This issue replaces future-work commentary embedded in the user-facing recovery ledger. The manual continues to describe current observable behavior until each fix ships.
