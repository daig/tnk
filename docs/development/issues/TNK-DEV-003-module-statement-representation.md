# TNK-DEV-003 — Compiled, import-stable module statements

**Status:** Decision needed  
**Type:** Architecture  
**Current contract:** [`docs/manual.md` §§5–6](../../manual.md#5-modules-theories-and-declarations)

## Current behavior

The module layer stores source modules and composes them through flattening. Imported statement bubbles use their home grammar for the implemented point-fix path, while renamed and instantiated composition still depends on merged-grammar reconstruction at some seams. The Reference specifies current observable composition behavior; it does not promise a compiled semantic module algebra.

Flattening also records, per statement, whether an object module or theory declared it (`PreModule::object_statements`), so object-pattern completion follows an object-module statement into every importer (`TNK-OO-002`). Like statement homes, this is build-time provenance carried beside the flattened statements, not a compiled statement representation. One context dependence remains: an object module also completes the object-syntax statements it imports from plain modules, so such a statement means one thing under an object-module root and another under a plain root. Maude completes a statement only in its declaring module. Whether TNK should stop completing imported plain-module statements is left open by the Reference; it reverses behavior that current compositions rely on and belongs with the decision below.

## Decision

Decide whether TNK should retain the current `PreModule` plus home-grammar strategy or introduce compiled, import-stable statements as the module-algebra representation.

The larger rework could improve:

- context-independent statement identity across import, renaming, and instantiation;
- build-time checking of parameterized modules;
- faithful source/flat reflection boundaries;
- source-form module inspection;
- a possible Full Maude substrate.

It would also touch every layer that consumes flattened modules and therefore must not begin as incidental cleanup.

## Constraints

- Existing module/view redefinition atomicity and dependent invalidation must remain intact.
- Statement execution order and home-scope variable meaning cannot drift.
- Engine-local term handles cannot become persistent cross-engine module data.
- The design must specify source provenance, renamed/instantiated identity, reflection form, and cache invalidation before implementation.

## Decision gate

Record one of:

1. retain the current representation and document its permanent boundary;
2. approve a compiled representation with a migration design and contract tests;
3. approve a narrower representation change for one independently justified surface.

No implementation starts until the chosen representation, migration boundary, and rollback plan are explicit.

## Provenance

Recovered decision D10 and the architecture concern described in the historical migration audit. The home-grammar point fix is complete; only the larger representation choice remains open.
