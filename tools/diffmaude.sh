#!/usr/bin/env bash
# tools/diffmaude.sh — oracle-diff harness for conformance fixtures.
#
# Usage: tools/diffmaude.sh <fixture.maude> [-v]
#   -v            report the pinned oracle version and print normalized output on PASS
#
# Exit codes:
#   0  normalized outputs identical (PASS)
#   1  outputs differ (unified diff on stdout)
#   3  oracle timed out (60s)
#   4  tnk timed out (60s)
#   2  usage / setup error
#
# Oracle:  MAUDE_LIB=$ORACLE_LIB $ORACLE_BIN -no-banner -no-advise <fixture> </dev/null
#          ORACLE_BIN defaults to a cached pinned release, else `maude` on PATH, else a verified
#          download of the pinned release (resolution order and knobs: tools/oracle.sh).
# tnk:     target/release/tnk-repl
#   Fixtures without `*** PRELUDE` run with `-no-prelude`; marked fixtures use the standing prelude,
#   matching the oracle environment.
#
# Normalization (exact — NOTHING else may be stripped):
#   - `====…` separator lines
#   - the tnk banner line, `Bye.`, `Maude>` prompts
#   - timing-only text: the tail of `rewrites: N in …` / `states: N rewrites: M in …` lines
#     (counts stay), and the standalone `Decision time:` line
#   - diagnostic bodies are deliberately OUT OF parity:
#     `Warning:` / `Advisory:` blocks and symmetric tnk `warning:` / `error:` / `parse error:` /
#     `error in module` blocks are stripped through the next recognizable output line.
#     Incompleteness and exhaustion result forms remain contractual; warning prose does not.
#   Everything else — echoes, result/Solution lines, sorts, counts, bindings,
#   traces — compares byte-exact.

set -u

ROOT=$(cd "$(dirname "$0")/.." && pwd)
# Companion libs: GPLv2 stock files + MIT tnk facades. External oracle prelude stays last so
# `prelude.maude` resolves from the Maude install while `load smt` etc. hit the bundled copies.
TNK_SHARE_LIB=${TNK_SHARE_LIB:-$ROOT/share/maude-gpl:$ROOT/share/tnk}
ORACLE_LIB=${ORACLE_LIB:-}
ORACLE_BIN=${ORACLE_BIN:-}
ORACLE_VERSION=${ORACLE_VERSION:-3.5.1}
# Oracle lookup, pinned-release fetch, and portable timeout: see tools/oracle.sh.
. "$ROOT/tools/oracle.sh"
TNK_BIN=${TNK_BIN:-$ROOT/target/release/tnk-repl}
TIMEOUT_SECS=${TIMEOUT_SECS:-60}

fixture=${1:-}
verbose=${2:-}
if [ -z "$fixture" ] || [ ! -f "$fixture" ]; then
  echo "usage: $0 <fixture.maude> [-v]" >&2
  exit 2
fi
fixture=$(cd "$(dirname "$fixture")" && pwd)/$(basename "$fixture")
fixdir=$(dirname "$fixture")

if [ ! -x "$TNK_BIN" ]; then
  echo "error: tnk binary not found at $TNK_BIN (cargo build --release first)" >&2
  exit 2
fi
resolve_oracle || exit 2
if [ -z "$ORACLE_LIB" ] || [ ! -f "$ORACLE_LIB/prelude.maude" ]; then
  echo "error: no prelude.maude for the oracle; set ORACLE_LIB, or include its directory in MAUDE_LIB" >&2
  exit 2
fi
IFS= read -r oracle_version < <("$ORACLE_BIN" --version 2>/dev/null)
if [ "$oracle_version" != "$ORACLE_VERSION" ]; then
  echo "error: oracle version '$oracle_version' does not match pinned '$ORACLE_VERSION'" >&2
  exit 2
fi
[ "$verbose" = "-v" ] && echo "oracle: Maude $oracle_version (diagnostics ignored)" >&2

tmpdir=$(mktemp -d "${TMPDIR:-/tmp}/diffmaude.XXXXXX") || exit 2
trap 'rm -rf "$tmpdir"' EXIT

normalize() {
  awk '
  {
    # strip interactive prompts (any run of them at line start)
    while (sub(/^Maude> /, "")) { }

    # The ambiguity warning has a second paragraph after a blank line. Keep consuming it without
    # preserving that internal blank as an output separator.
    if ($0 ~ /^Warning:.*ambiguous term/) {
      inblock = 2
      next
    }
    # diagnostic-block openers (both sides; symmetric)
    if ($0 ~ /^(Warning:|Advisory:|warning:|error:|parse error:|error in module)/) {
      inblock = 1
      next
    }

    if (inblock) {
      if (inblock == 2 && ($0 == "" || $0 ~ /^Arbitrarily taking the first as correct\./)) {
        next
      }
      # Preserve the diagnostic terminating blank as the surrounding output separator. Without
      # this, an ignored eager warning between two unifiers collapses their normal blank line only
      # on the oracle side.
      if ($0 == "") {
        print
        inblock = 0
        next
      }
      # a block runs until the next recognizable real-output line
      if ($0 ~ /^=+$/ || $0 ~ /^Bye\.$/ ||
          $0 ~ /^(check|get variants|filtered variant unify|reduce|rewrite|frewrite|erewrite|search|smt-search|match|xmatch|srewrite|dsrewrite|continue|parse|unify|irredundant unify|variant) / ||
          $0 ~ /^(\{v?fold\} )?(f?vu-narrow|narrow) / ||
          $0 ~ /^(rewrites:|states:|Decision time:|result |Solution |Unifier [0-9]+|Matcher [0-9]+|Variant [0-9]+|No solution|No more solutions|No unifier|No more unifiers|No match|empty substitution)/ ||
          $0 ~ /^(state [0-9]|arc [0-9]|Narrowing solution [0-9]+)/ || $0 ~ /^\*\*\*\*/ ||
          $0 ~ /^Considering object completion on:$/ ||
          $0 ~ /^(op |fmod |mod |fth |th |smod |omod |oth |view |tambanokano REPL )/) {
        inblock = 0
      } else {
        next
      }
    }

    # separators / banner / Bye.
    if ($0 ~ /^=+$/) next
    if ($0 ~ /^tambanokano REPL /) next
    if ($0 ~ /^Bye\.$/) next

    # timing-only text (observable rewrite/state counts stay)
    if ($0 ~ /^Decision time: /) next
    if ($0 ~ /^rewrites: [0-9]+ in /) { sub(/ in .*/, "") }
    else if ($0 ~ /^states: [0-9]+ +rewrites: [0-9]+ in /) { sub(/ in .*/, "") }

    print
  }'
}

# ---- oracle side -----------------------------------------------------------
# BOTH_NO_PRELUDE=1: run both binaries prelude-free. The prelude-copy fixtures define protected
# modules from scratch, so the comparison must begin without a standing prelude.
oracle_flags=()
[ "${BOTH_NO_PRELUDE:-0}" = "1" ] && oracle_flags+=(-no-prelude)
( cd "$fixdir" && MAUDE_LIB="$ORACLE_LIB" run_with_timeout "$TIMEOUT_SECS" \
    "$ORACLE_BIN" -no-banner -no-advise ${oracle_flags[@]+"${oracle_flags[@]}"} "$fixture" </dev/null ) \
    >"$tmpdir/oracle.raw" 2>&1
rc=$?
if [ $rc -eq 124 ]; then
  echo "TIMEOUT(oracle) $fixture"
  exit 3
elif [ $rc -ne 0 ]; then
  echo "error: oracle exited with status $rc for $fixture" >&2
  cat "$tmpdir/oracle.raw" >&2
  exit 2
fi

# ---- tnk side --------------------------------------------------------------
tnk_flags=()
if [ "${BOTH_NO_PRELUDE:-0}" = "1" ]; then
  tnk_flags+=(-no-prelude)
elif [ "${TNK_ASSUME_PRELUDE:-0}" != "1" ] && ! grep -q '^\*\*\* PRELUDE' "$fixture"; then
  # TNK_ASSUME_PRELUDE=1 supports fixture sets that omit the marker.
  tnk_flags+=(-no-prelude)
fi
( cd "$fixdir" && MAUDE_LIB="$TNK_SHARE_LIB:$ORACLE_LIB" run_with_timeout "$TIMEOUT_SECS" \
    "$TNK_BIN" -no-banner ${tnk_flags[@]+"${tnk_flags[@]}"} "$fixture" </dev/null ) \
    >"$tmpdir/tnk.raw" 2>&1
rc=$?
if [ $rc -eq 124 ]; then
  echo "TIMEOUT(tnk) $fixture"
  exit 4
elif [ $rc -ne 0 ]; then
  echo "error: tnk exited with status $rc for $fixture" >&2
  cat "$tmpdir/tnk.raw" >&2
  exit 2
fi

# ---- compare ---------------------------------------------------------------
normalize <"$tmpdir/oracle.raw" >"$tmpdir/oracle.norm"
normalize <"$tmpdir/tnk.raw"    >"$tmpdir/tnk.norm"

if diff -u --label oracle --label tnk "$tmpdir/oracle.norm" "$tmpdir/tnk.norm"; then
  [ "$verbose" = "-v" ] && cat "$tmpdir/oracle.norm"
  exit 0
else
  exit 1
fi
