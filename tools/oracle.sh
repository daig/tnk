# tools/oracle.sh — locate (or fetch) the pinned Maude oracle; portable timeout.
#
# Sourced, not executed. The caller sets ROOT and ORACLE_VERSION first.
#
# resolve_oracle sets ORACLE_BIN and ORACLE_LIB. Oracle resolution (first hit wins):
#   1. ORACLE_BIN, when set (used as given; a version mismatch is still an error downstream)
#   2. the cached pinned release in ORACLE_CACHE (default: $ROOT/.oracle/maude-$ORACLE_VERSION)
#   3. `maude` on PATH, when it reports ORACLE_VERSION
#   4. download the pinned release from github.com/maude-lang/Maude into ORACLE_CACHE and verify
#      its SHA-256; skipped when ORACLE_FETCH=0
# ORACLE_LIB keeps its existing meaning. When it is unset, the first MAUDE_LIB entry containing
# prelude.maude wins, then the resolved binary's own directory (release zips ship prelude.maude
# next to the binary).
#
# Release checksums are pinned for 3.5.1. For another ORACLE_VERSION, set ORACLE_SHA256 to the
# zip's checksum, or install that version yourself and point ORACLE_BIN at it.
#
# run_with_timeout SECS CMD... runs CMD under `timeout`, `gtimeout`, or a perl alarm fallback
# (macOS ships none of the coreutils timeouts). A timeout exits 124 in all three cases.

ORACLE_CACHE=${ORACLE_CACHE:-$ROOT/.oracle/maude-$ORACLE_VERSION}

oracle_platform() {
  case "$(uname -s)/$(uname -m)" in
    Darwin/arm64) echo macos-arm64 ;;
    Darwin/x86_64) echo macos-x86_64 ;;
    Linux/x86_64) echo linux-x86_64 ;;
    *) return 1 ;;
  esac
}

oracle_pinned_sha256() {
  case "$1/$2" in
    3.5.1/macos-arm64) echo 95851274f57b3853aab833674e2b770ed800f38fb1f3d03c97dcac56346c13dc ;;
    3.5.1/macos-x86_64) echo 938eb55fbca44f7f8de71fdb8eeb41f8004ed0a440a3caa37702fee3fc3c79bf ;;
    3.5.1/linux-x86_64) echo 72ed1ca87e3b3d0dfc6ee1436baf154bf04c45ff97d521bec040c5e8dfc8f92c ;;
    *) return 1 ;;
  esac
}

oracle_sha256_of() {
  if command -v shasum >/dev/null 2>&1; then
    shasum -a 256 "$1" | cut -d' ' -f1
  else
    sha256sum "$1" | cut -d' ' -f1
  fi
}

oracle_reports_version() {
  local v
  IFS= read -r v < <("$1" --version 2>/dev/null)
  [ "$v" = "$ORACLE_VERSION" ]
}

fetch_oracle() {
  local plat sha url tmp got
  plat=$(oracle_platform) || {
    echo "error: no Maude $ORACLE_VERSION release build for $(uname -s)/$(uname -m); set ORACLE_BIN" >&2
    return 2
  }
  sha=${ORACLE_SHA256:-$(oracle_pinned_sha256 "$ORACLE_VERSION" "$plat")} || {
    echo "error: no pinned checksum for Maude $ORACLE_VERSION ($plat); set ORACLE_SHA256 or ORACLE_BIN" >&2
    return 2
  }
  url="https://github.com/maude-lang/Maude/releases/download/Maude$ORACLE_VERSION/Maude-$ORACLE_VERSION-$plat.zip"
  echo "fetching Maude $ORACLE_VERSION ($plat) into $ORACLE_CACHE" >&2
  mkdir -p "$(dirname "$ORACLE_CACHE")" || return 2
  tmp=$(mktemp -d "$(dirname "$ORACLE_CACHE")/.fetch.XXXXXX") || return 2
  if ! curl -fsSL -o "$tmp/maude.zip" "$url"; then
    echo "error: download failed: $url" >&2
    rm -rf "$tmp"
    return 2
  fi
  got=$(oracle_sha256_of "$tmp/maude.zip")
  if [ "$got" != "$sha" ]; then
    echo "error: checksum mismatch for $url" >&2
    echo "  expected $sha" >&2
    echo "  got      $got" >&2
    rm -rf "$tmp"
    return 2
  fi
  if ! unzip -q "$tmp/maude.zip" -d "$tmp/x" || [ ! -f "$tmp/x/maude" ] || [ ! -f "$tmp/x/prelude.maude" ]; then
    echo "error: unexpected archive layout in $url (want maude and prelude.maude at the top level)" >&2
    rm -rf "$tmp"
    return 2
  fi
  chmod +x "$tmp/x/maude"
  # A concurrent fetch may have landed first; keep whichever copy arrived (both are verified).
  if [ ! -x "$ORACLE_CACHE/maude" ] && ! mv "$tmp/x" "$ORACLE_CACHE" 2>/dev/null && [ ! -x "$ORACLE_CACHE/maude" ]; then
    echo "error: could not install the oracle into $ORACLE_CACHE" >&2
    rm -rf "$tmp"
    return 2
  fi
  rm -rf "$tmp"
}

resolve_oracle() {
  local path_maude dir
  local -a maude_lib_dirs
  if [ -z "${ORACLE_BIN:-}" ]; then
    path_maude=$(command -v maude 2>/dev/null || true)
    if [ -x "$ORACLE_CACHE/maude" ]; then
      ORACLE_BIN=$ORACLE_CACHE/maude
    elif [ -n "$path_maude" ] && oracle_reports_version "$path_maude"; then
      ORACLE_BIN=$path_maude
    elif [ "${ORACLE_FETCH:-1}" != "0" ]; then
      fetch_oracle || return 2
      ORACLE_BIN=$ORACLE_CACHE/maude
    elif [ -n "$path_maude" ]; then
      ORACLE_BIN=$path_maude # wrong version: the caller's version check reports it
    else
      echo "error: no Maude oracle found (set ORACLE_BIN, put maude on PATH, or unset ORACLE_FETCH=0)" >&2
      return 2
    fi
  fi

  if [ -z "${ORACLE_LIB:-}" ] && [ -n "${MAUDE_LIB:-}" ]; then
    IFS=: read -r -a maude_lib_dirs <<< "$MAUDE_LIB"
    for dir in ${maude_lib_dirs[@]+"${maude_lib_dirs[@]}"}; do
      if [ -n "$dir" ] && [ -f "$dir/prelude.maude" ]; then
        ORACLE_LIB=$dir
        break
      fi
    done
  fi
  if [ -z "${ORACLE_LIB:-}" ]; then
    dir=$(dirname "$(command -v "$ORACLE_BIN" 2>/dev/null || echo "$ORACLE_BIN")")
    [ -f "$dir/prelude.maude" ] && ORACLE_LIB=$dir
  fi
  return 0
}

run_with_timeout() {
  local secs=$1 rc
  shift
  if command -v timeout >/dev/null 2>&1; then
    timeout "$secs" "$@"
  elif command -v gtimeout >/dev/null 2>&1; then
    gtimeout "$secs" "$@"
  else
    # The alarm survives exec; SIGALRM's default action kills the command (status 128+14).
    perl -e 'alarm shift; exec { $ARGV[0] } @ARGV or exit 127' "$secs" "$@"
    rc=$?
    [ $rc -eq 142 ] && return 124
    return $rc
  fi
}
