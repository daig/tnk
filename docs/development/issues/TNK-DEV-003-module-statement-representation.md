# TNK-DEV-003 — Compiled, import-stable module statements

**Status:** Decision needed  
**Type:** Architecture  
**Current contract:** [`docs/manual.md` §§5–6](../../manual.md#5-modules-theories-and-declarations)

## Current behavior

The module layer stores source modules and composes them through flattening. Imported statement bubbles use their home grammar for the implemented point-fix path, while renamed and instantiated composition still depends on merged-grammar reconstruction at some seams. The home path parses an equation or rule right side in its left side's home kind. A home grammar comes from the home module's cached build, and imported strategy definitions compile against those builds too. A Session therefore rebuilds the dependents of a redefined module or view imports first: each dependent follows every rebuilt dependent it imports, directly or through a view argument, and ties go to the earliest first definition. A rebuilt dependent then reparses against the same rebuilt homes as a fresh build. Import cycles, which a redefinition can still create, have no such order. A plain-imported statement whose home parse still fails falls back to the flattened grammar, where importer declarations can re-bind its bare variables. Renamed imports and parameter copies donate statements without a home. Each records its home module's variable table, and the variables the final flattened grammar would bind differently are inlined lexically as colon variables at their home sort. An instantiated module inlines only the variables it declares itself, so one it uses through its own import is still bound by the flattened grammar. The Reference specifies current observable composition behavior; it does not promise a compiled semantic module algebra.

Inlining a variable rewrites every token spelled like it, as instantiation and shadowed-import inlining also do, so it cannot tell a variable from an operator token with the same spelling. One case is handled: a variable spelled like a constant that the renaming itself introduces (`var m` under `op n to m`) is inlined before renaming, while each bare `m` still means the variable. Other operator tokens are not handled. When the importer binds the name differently, a home variable spelled like an operator token is also inlined inside that operator's applications, and the statement is dropped. Examples are `var s` with `op s_` in `h(s z) = z`, and a name that a renaming gives to a non-constant operator. Before home variable scopes were recorded, the importer's grammar re-bound the variable instead, so `h(s z) = z` was kept while statements using the variable were dropped or silently changed. Grammar-aware inlining would close this seam: parse each statement in its home grammar and rewrite only variable positions.

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
