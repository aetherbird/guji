#!/usr/bin/env bash
# Repeat the concurrency rows that have historically exposed native-D races.

set -uo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
CORPUS_DIR="${CORPUS_DIR:-$REPO_ROOT/selfhost/eval_corpus}"
GUJI="${GUJI:-}"
STRESS_ITERS="${STRESS_ITERS:-500}"
BLOCKING_STRESS_ITERS="${BLOCKING_STRESS_ITERS:-10}"
PROG_TIMEOUT="${PROG_TIMEOUT:-120}"

fail_setup() {
  echo "interpreter-stress SETUP: $*"
  exit 2
}

is_infrastructure_status() {
  local rc="$1"
  case "$rc" in
    124|125|126|127) return 0 ;;
  esac
  [ "$rc" -ge 129 ] && [ "$rc" -le 192 ]
}

[ -x "$GUJI" ] || fail_setup "native Guji interpreter missing; set GUJI=<path>"
[[ "$STRESS_ITERS" =~ ^[1-9][0-9]*$ ]] || fail_setup "STRESS_ITERS must be a positive integer"
[ "$STRESS_ITERS" -ge 500 ] \
  || fail_setup "STRESS_ITERS must be at least 500 for the canonical stress gate"
[[ "$BLOCKING_STRESS_ITERS" =~ ^[1-9][0-9]*$ ]] \
  || fail_setup "BLOCKING_STRESS_ITERS must be a positive integer"
[ "$BLOCKING_STRESS_ITERS" -ge 10 ] \
  || fail_setup "BLOCKING_STRESS_ITERS must be at least 10 for the canonical stress gate"
[[ "$PROG_TIMEOUT" =~ ^[1-9][0-9]*$ ]] \
  || fail_setup "PROG_TIMEOUT must be a positive integer"

rows=(
  channel_text_carriers
  hatch_carrier_capture
  hatch_class_capture
  hatch_function_capture
  hatch_tasks
  select_lifecycle
)

blocking_rows=(
  select_scalar_deadlock
)

stack_rows=(
  while_loop
  for_range
  for_loop
  channel_iteration
)

tmp="$(mktemp -d)" || fail_setup "cannot create temporary directory"
trap 'rm -rf "$tmp"' EXIT

for name in "${stack_rows[@]}"; do
  src="$CORPUS_DIR/$name.guji"
  expected="$CORPUS_DIR/$name.expected"
  expected_err=/dev/null
  expected_rc=0
  [ -f "$src" ] || fail_setup "stack source missing: $src"
  [ -f "$expected" ] || fail_setup "stack expectation missing: $expected"
  [ -f "$CORPUS_DIR/$name.stderr" ] && expected_err="$CORPUS_DIR/$name.stderr"
  if [ -f "$CORPUS_DIR/$name.exit" ]; then
    expected_rc="$(tr -d '[:space:]' <"$CORPUS_DIR/$name.exit")"
    [[ "$expected_rc" =~ ^[0-9]+$ ]] || fail_setup "malformed expected exit for $name"
  fi
  if is_infrastructure_status "$expected_rc"; then
    fail_setup "expected exit for $name uses reserved infrastructure status $expected_rc"
  fi

  (
    ulimit -s 8192 || exit 125
    cd "$CORPUS_DIR" || exit 125
    timeout "$PROG_TIMEOUT" "$GUJI" "$src"
  ) >"$tmp/out" 2>"$tmp/err"
  rc=$?
  if is_infrastructure_status "$rc" \
      || [ "$rc" -ne "$expected_rc" ] \
      || ! cmp -s "$tmp/out" "$expected" \
      || ! cmp -s "$tmp/err" "$expected_err"; then
    echo "interpreter-stress RED: $name at 8 MiB stack (rc=$rc, expected=$expected_rc)"
    diff -u "$expected" "$tmp/out" | head -n 30 || true
    diff -u "$expected_err" "$tmp/err" | head -n 30 || true
    exit 1
  fi
  echo "interpreter-stress: $name exact at 8 MiB stack"
done

for name in "${rows[@]}"; do
  src="$CORPUS_DIR/$name.guji"
  expected="$CORPUS_DIR/$name.expected"
  expected_err=/dev/null
  expected_rc=0
  [ -f "$src" ] || fail_setup "stress source missing: $src"
  [ -f "$expected" ] || fail_setup "stress expectation missing: $expected"
  [ -f "$CORPUS_DIR/$name.stderr" ] && expected_err="$CORPUS_DIR/$name.stderr"
  if [ -f "$CORPUS_DIR/$name.exit" ]; then
    expected_rc="$(tr -d '[:space:]' <"$CORPUS_DIR/$name.exit")"
    [[ "$expected_rc" =~ ^[0-9]+$ ]] || fail_setup "malformed expected exit for $name"
  fi
  if is_infrastructure_status "$expected_rc"; then
    fail_setup "expected exit for $name uses reserved infrastructure status $expected_rc"
  fi

  for ((i=1; i<=STRESS_ITERS; i++)); do
    (cd "$CORPUS_DIR" && timeout "$PROG_TIMEOUT" "$GUJI" "$src") \
      >"$tmp/out" 2>"$tmp/err"
    rc=$?
    if is_infrastructure_status "$rc" \
        || [ "$rc" -ne "$expected_rc" ] \
        || ! cmp -s "$tmp/out" "$expected" \
        || ! cmp -s "$tmp/err" "$expected_err"; then
      echo "interpreter-stress RED: $name iteration $i/$STRESS_ITERS (rc=$rc, expected=$expected_rc)"
      diff -u "$expected" "$tmp/out" | head -n 30 || true
      diff -u "$expected_err" "$tmp/err" | head -n 30 || true
      exit 1
    fi
  done
  echo "interpreter-stress: $name $STRESS_ITERS/$STRESS_ITERS exact"
done

for name in "${blocking_rows[@]}"; do
  src="$CORPUS_DIR/$name.guji"
  expected="$CORPUS_DIR/$name.expected"
  expected_err=/dev/null
  expected_rc=0
  [ -f "$src" ] || fail_setup "blocking source missing: $src"
  [ -f "$expected" ] || fail_setup "blocking expectation missing: $expected"
  [ -f "$CORPUS_DIR/$name.stderr" ] && expected_err="$CORPUS_DIR/$name.stderr"
  if [ -f "$CORPUS_DIR/$name.exit" ]; then
    expected_rc="$(tr -d '[:space:]' <"$CORPUS_DIR/$name.exit")"
    [[ "$expected_rc" =~ ^[0-9]+$ ]] || fail_setup "malformed expected exit for $name"
  fi
  if is_infrastructure_status "$expected_rc"; then
    fail_setup "expected exit for $name uses reserved infrastructure status $expected_rc"
  fi

  for ((i=1; i<=BLOCKING_STRESS_ITERS; i++)); do
    (cd "$CORPUS_DIR" && timeout "$PROG_TIMEOUT" "$GUJI" "$src") \
      >"$tmp/out" 2>"$tmp/err"
    rc=$?
    if is_infrastructure_status "$rc" \
        || [ "$rc" -ne "$expected_rc" ] \
        || ! cmp -s "$tmp/out" "$expected" \
        || ! cmp -s "$tmp/err" "$expected_err"; then
      echo "interpreter-stress RED: $name iteration $i/$BLOCKING_STRESS_ITERS (rc=$rc, expected=$expected_rc)"
      diff -u "$expected" "$tmp/out" | head -n 30 || true
      diff -u "$expected_err" "$tmp/err" | head -n 30 || true
      exit 1
    fi
  done
  echo "interpreter-stress: $name $BLOCKING_STRESS_ITERS/$BLOCKING_STRESS_ITERS exact"
done

echo "interpreter-stress GREEN: ${#stack_rows[@]} stack rows at 8 MiB; ${#rows[@]} concurrency rows x $STRESS_ITERS; ${#blocking_rows[@]} blocking rows x $BLOCKING_STRESS_ITERS"
