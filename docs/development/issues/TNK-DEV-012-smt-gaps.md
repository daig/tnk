# TNK-DEV-012 — SMT search and result-reporting gaps

**Status:** Known gap  
**Type:** SMT feature and presentation  
**Current contract:** [`docs/manual.md` §14 and Appendix H/K](../../manual.md#14-smt-constrained-operations)

## Current behavior

- `smt-search =>!` is unsupported and rejected with an `error:` diagnostic, without a command echo, search, or continuation.
- Other `smt-search` requests rejected while the command is built report an `error:` diagnostic in the same way: a module or goal outside the SMT-rewriting restrictions below, and a `such that` condition that does not parse or is not a conjunction of equalities on kinds with an `===` hook (`unsupported SMT-search condition`). Before this was fixed, every such request printed nothing.
- An `=>*` search reports its initial state only when the backend returns `Sat` for the initial (`such that`) constraint, except that the literal SMT `true` constraint is exempt. The exemption is provisional. The null backend answers `Unknown` for `true` as well, so it still reports the initial state of an unconstrained search whose goal has no SMT-sorted variable, yet prunes every successor, including those whose constraint is still `true`. `TNK-SMT-003` as written prunes every `Unknown`; whether a trivial constraint needs a backend `Sat` is undecided.
- A configured backend `BadDag` result currently produces the command echo without a distinct backend-answer line.
- `Unknown`, `BadDag`, explicit bounds, finite no-solution, and incompleteness are semantically distinct even when `Eval` cannot represent every distinction structurally.

## Missing work

### Normal-form SMT search

Supporting `=>!` requires a precise normal-form acceptance rule under accumulated constraints, including how unknown feasibility affects terminal-state classification and continuation.

### Result reporting

`BadDag` needs an explicit user-visible outcome consistent with `TNK-DOC-006`. A future typed Session API should carry the backend result directly; the text API still needs an unambiguous record.

### SMT-rewriting restrictions (decision needed)

The Reference does not state which modules and goals SMT search accepts. The current gate (`LoadedModule::smt_rewrite_valid`, `Engine::valid_for_smt_rewriting`, `Engine::valid_smt_goal`) rejects a request, with the single diagnostic `module or goal does not satisfy SMT rewriting restrictions`, unless:

- the SMT conjunction hook is resolved;
- the module has at least one rule (including `[nonexec]` rules) and no equations or memberships;
- every rule left-hand side is linear and contains no SMT operator or SMT number;
- no non-polymorphic operator declares `idem` or `id:`;
- the goal pattern is linear and contains no SMT operator or SMT number.

This gate is more permissive than Maude's in two places: it admits polymorphic operators with a collapse axiom and non-SMT operators whose range is an SMT sort. Separately, an SMT rule whose condition has a fragment other than an equality on an SMT kind with an `===` hook is never applied during SMT search, and nothing reports it (`Engine::smt_state_successors` skips the successor). Specifying the restriction set, a diagnostic that names the violated restriction, and the treatment of such rules needs a decision before any of it becomes normative text.

## Constraints

- Never reinterpret `Unknown` or `BadDag` as satisfiable, unsatisfiable, or no solution.
- The default null backend remains a valid profile and returns `Unknown` rather than pretending to solve.
- Query-local solver state and push/pop isolation must remain intact.
- Bounds and backend uncertainty cannot produce an exhaustion claim.

## Completion gate

The reporting slice closes when every backend result has an unambiguous Session record and tests cover state/continuation effects. The `=>!` slice requires constrained terminal-state tests for Sat, Unsat, Unknown, bounds, and continuation before the Reference can list it as supported.
