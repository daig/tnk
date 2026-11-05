# Recorded accepted divergences

A top-level fixture with a recorded diff here is CLEAN iff its current diff is
byte-identical to the recording (`tools/conformance-suite.sh`); any drift beyond
the recording fails the suite.

- `objects.diff` — mixed-symbol ACU argument print order in the search-goal echo.
- `acu-match.diff` — AC match-solution enumeration order; programmatically
  verified set-equal.
- `strategy.diff`, `prelude-meta.diff` — per-solution rewrite counts only; values, solution order, and
  echoes remain byte-identical. The differing counts come from `amatchrew` sub-search scheduling
  and indexed `metaSearch` exploration order. Object-level search and strategy counts remain exact.

Only these four recorded diffs are accepted. Every other fixture must match the live oracle under the
normalization contract in `tools/diffmaude.sh`.
