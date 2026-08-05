#!/usr/bin/env bash
# Fail-closed coverage ratchet for historically declined, spec-valid programs.
#
# Guji D (the native self-hosted interpreter) is the semantic authority and
# Guji C (the native self-hosted compiler) must compile every pinned program.
# The resulting executable must match D byte-for-byte on stdout and stderr and
# exactly on exit status. There are no archived-backend exemptions.

set -uo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
CORPUS_DIR="${1:-${CORPUS_DIR:-$REPO_ROOT/selfhost/audit_corpus}}"
PROLOGUE="${PROLOGUE:-$REPO_ROOT/selfhost/rt/runtime_prologue.c}"
PROG_TIMEOUT="${PROG_TIMEOUT:-120}"
COMPILE_TIMEOUT="${COMPILE_TIMEOUT:-120}"
GUJI="${GUJI:-}"
GUJI2C="${GUJI2C:-}"

# This exact set is the historical decline inventory. Adding, removing, or
# renaming a fixture requires a deliberate ratchet update here.
AUDIT_CASES=(
  carrier_list_bound.guji
  carrier_map_returned.guji
  covered_enum_annot_bound.guji
  covered_enum_param.guji
  covered_hatch_enum_class.guji
  covered_hatch_in_sub.guji
  covered_int_arith.guji
  covered_scalar_match.guji
  covered_select_carrier_enum.guji
  covered_select_heap.guji
  covered_str_print.guji
  enum_match_bound_inferred.guji
  enum_match_inline.guji
  enum_match_niladic.guji
  enum_match_returned.guji
  oraclelimit_carrier_list_enum.guji
  oraclelimit_carrier_list_recursive.guji
  oraclelimit_chan_list_list_list.guji
  oraclelimit_chan_list_map.guji
  oraclelimit_chan_map_list_list.guji
  oraclelimit_chan_map_map_list.guji
  oraclelimit_chan_map_map_map.guji
  oraclelimit_hatch_capture_class.guji
  oraclelimit_hatch_capture_option.guji
  oraclelimit_hatch_enum_option_payload.guji
  oraclelimit_map_valued_if.guji
)

fail_setup() {
  echo "decline-audit SETUP: $*"
  exit 2
}

is_infrastructure_status() {
  local rc="$1"
  case "$rc" in
    124|125|126|127) return 0 ;;
  esac
  [ "$rc" -ge 129 ] && [ "$rc" -le 192 ]
}

[ "$#" -le 1 ] || fail_setup "usage: decline_audit.sh [corpus-dir]"
[ -n "$GUJI" ] || fail_setup "set GUJI=<canonical native Guji interpreter>"
[[ "$GUJI" = /* ]] || fail_setup "GUJI must be an absolute path: $GUJI"
[ -x "$GUJI" ] || fail_setup "native Guji interpreter is not executable: $GUJI"
[ -n "$GUJI2C" ] || fail_setup "set GUJI2C=<canonical native Guji compiler>"
[[ "$GUJI2C" = /* ]] || fail_setup "GUJI2C must be an absolute path: $GUJI2C"
[ -x "$GUJI2C" ] || fail_setup "native Guji compiler is not executable: $GUJI2C"
[[ "$PROLOGUE" = /* ]] || fail_setup "PROLOGUE must be an absolute path: $PROLOGUE"
[ -f "$PROLOGUE" ] || fail_setup "runtime prologue missing: $PROLOGUE"
[[ "$CORPUS_DIR" = /* ]] || fail_setup "corpus directory must be an absolute path: $CORPUS_DIR"
[ -d "$CORPUS_DIR" ] || fail_setup "audit corpus missing: $CORPUS_DIR"
[[ "$PROG_TIMEOUT" =~ ^[1-9][0-9]*$ ]] \
  || fail_setup "PROG_TIMEOUT must be a positive integer"
[[ "$COMPILE_TIMEOUT" =~ ^[1-9][0-9]*$ ]] \
  || fail_setup "COMPILE_TIMEOUT must be a positive integer"
command -v timeout >/dev/null 2>&1 || fail_setup "timeout command is required"

tmp="$(mktemp -d)" || fail_setup "cannot create temporary directory"
trap 'rm -rf "$tmp"' EXIT

if ! printf '%s\n' "${AUDIT_CASES[@]}" \
    | LC_ALL=C sort -u >"$tmp/expected-corpus"; then
  fail_setup "cannot materialize pinned audit inventory"
fi
if [ "$(wc -l <"$tmp/expected-corpus")" -ne "${#AUDIT_CASES[@]}" ]; then
  fail_setup "pinned audit inventory contains duplicate names"
fi
find "$CORPUS_DIR" -maxdepth 1 -type f -name '*.guji' -printf '%f\n' \
  | LC_ALL=C sort -u >"$tmp/actual-corpus" \
  || fail_setup "cannot enumerate audit corpus: $CORPUS_DIR"

if ! cmp -s "$tmp/expected-corpus" "$tmp/actual-corpus"; then
  echo "decline-audit SETUP: historical audit corpus does not match the pinned inventory"
  diff -u "$tmp/expected-corpus" "$tmp/actual-corpus" || true
  exit 2
fi

pass=0
fail=0
for name in "${AUDIT_CASES[@]}"; do
  src="$CORPUS_DIR/$name"
  rundir="$(dirname "$src")"
  program="$tmp/program"
  rm -f "$program" "$program.c"

  (
    cd "$rundir" || exit 125
    timeout "$PROG_TIMEOUT" "$GUJI" "$src"
  ) </dev/null >"$tmp/d.out" 2>"$tmp/d.err"
  d_rc=$?
  if is_infrastructure_status "$d_rc"; then
    echo "D-ERROR      $name - canonical interpreter returned infrastructure status (rc=$d_rc)"
    sed 's/^/  D: /' "$tmp/d.err" | head -n 8
    fail=$((fail + 1))
    continue
  fi
  # Every pinned row is a successful spec program. Some deliberately return a
  # nonzero Int from main, but none is entitled to panic or emit diagnostics.
  # Exact D/C agreement alone would otherwise let both engines share a failure.
  if [ -s "$tmp/d.err" ]; then
    echo "D-ERROR      $name - spec-valid program emitted stderr (rc=$d_rc)"
    sed 's/^/  D: /' "$tmp/d.err" | head -n 8
    fail=$((fail + 1))
    continue
  fi

  timeout "$COMPILE_TIMEOUT" "$GUJI2C" "$src" "$program" "$PROLOGUE" \
    >"$tmp/build.out" 2>"$tmp/build.err"
  c_build_rc=$?
  if [ "$c_build_rc" -eq 126 ] || [ "$c_build_rc" -eq 127 ]; then
    fail_setup "could not execute canonical Guji compiler (rc=$c_build_rc)"
  fi
  if [ "$c_build_rc" -ne 0 ]; then
    case "$c_build_rc" in
      4) label="C-DECLINE" ;;
      1) label="C-REJECT" ;;
      *) label="C-ERROR" ;;
    esac
    printf '%-12s %s - canonical compiler failed (rc=%s)\n' \
      "$label" "$name" "$c_build_rc"
    sed 's/^/  C: /' "$tmp/build.err" | head -n 8
    fail=$((fail + 1))
    continue
  fi
  if [ ! -x "$program" ]; then
    echo "C-ERROR      $name - compiler returned success without an executable"
    fail=$((fail + 1))
    continue
  fi

  (
    cd "$rundir" || exit 125
    timeout "$PROG_TIMEOUT" "$program"
  ) </dev/null >"$tmp/c.out" 2>"$tmp/c.err"
  c_rc=$?
  if is_infrastructure_status "$c_rc"; then
    echo "C-ERROR      $name - compiled program returned infrastructure status (rc=$c_rc)"
    sed 's/^/  C: /' "$tmp/c.err" | head -n 8
    fail=$((fail + 1))
    continue
  fi

  if [ "$d_rc" -eq "$c_rc" ] \
      && cmp -s "$tmp/d.out" "$tmp/c.out" \
      && cmp -s "$tmp/d.err" "$tmp/c.err"; then
    echo "PASS         $name (rc=$d_rc)"
    pass=$((pass + 1))
    continue
  fi

  echo "MISMATCH     $name - D/C behavior differs (D rc=$d_rc, C rc=$c_rc)"
  if ! cmp -s "$tmp/d.out" "$tmp/c.out"; then
    echo "  stdout diff:"
    diff -u "$tmp/d.out" "$tmp/c.out" | sed 's/^/    /' | head -n 30 || true
  fi
  if ! cmp -s "$tmp/d.err" "$tmp/c.err"; then
    echo "  stderr diff:"
    diff -u "$tmp/d.err" "$tmp/c.err" | sed 's/^/    /' | head -n 30 || true
  fi
  fail=$((fail + 1))
done

total=$((pass + fail))
echo "-- canonical decline audit: $total pinned cases, $pass exact, $fail failed --"
if [ "$fail" -ne 0 ]; then
  echo "DECLINE AUDIT RED: every pinned spec-valid program must compile and match D exactly."
  exit 1
fi
echo "DECLINE AUDIT GREEN"
