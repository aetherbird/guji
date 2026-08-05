#!/usr/bin/env bash
# Exact behavioral differential for the Guji-owned interpreter (D) and compiler (C).
# Both inputs are native artifacts produced by the Guji compiler. Go is not used.

set -uo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
CORPUS_DIR="${CORPUS_DIR:-$REPO_ROOT/selfhost/eval_corpus}"
COVERED_MANIFEST="${COVERED_MANIFEST:-$REPO_ROOT/selfhost/interpreter_corpus.txt}"
FRONTIER_MANIFEST="${FRONTIER_MANIFEST:-$REPO_ROOT/selfhost/interpreter_frontier.txt}"
PROLOGUE="${PROLOGUE:-$REPO_ROOT/selfhost/rt/runtime_prologue.c}"
PROG_TIMEOUT="${PROG_TIMEOUT:-120}"
SANITIZE="${SANITIZE:-1}"
SANITIZE_INTERPRETER="${SANITIZE_INTERPRETER:-0}"
EXPECTED_COVERED="${EXPECTED_COVERED:-}"
EXPECTED_FRONTIER="${EXPECTED_FRONTIER:-}"
CC="${CC:-cc}"

GUJI2C="${GUJI2C:-}"
GUJI="${GUJI:-}"
GUJI_SAN="${GUJI_SAN:-}"

fail_setup() {
  echo "interpreter-diff SETUP: $*"
  exit 2
}

is_infrastructure_status() {
  local rc="$1"
  case "$rc" in
    124|125|126|127) return 0 ;;
  esac
  [ "$rc" -ge 129 ] && [ "$rc" -le 192 ]
}

[ -x "$GUJI2C" ] || fail_setup "native Guji compiler missing: $GUJI2C"
[ -x "$GUJI" ] || fail_setup "native Guji interpreter missing; set GUJI=<path>"
[ "$SANITIZE_INTERPRETER" != 1 ] || [ -x "$GUJI_SAN" ] \
  || fail_setup "SANITIZE_INTERPRETER=1 requires GUJI_SAN=<sanitized native interpreter>"
[ -d "$CORPUS_DIR" ] || fail_setup "corpus directory missing: $CORPUS_DIR"
[ -f "$COVERED_MANIFEST" ] || fail_setup "covered manifest missing: $COVERED_MANIFEST"
[ -f "$FRONTIER_MANIFEST" ] || fail_setup "frontier manifest missing: $FRONTIER_MANIFEST"
[ -f "$PROLOGUE" ] || fail_setup "runtime prologue missing: $PROLOGUE"
[[ "$PROG_TIMEOUT" =~ ^[1-9][0-9]*$ ]] \
  || fail_setup "PROG_TIMEOUT must be a positive integer"
[[ "$SANITIZE" =~ ^[01]$ ]] || fail_setup "SANITIZE must be 0 or 1"
[[ "$SANITIZE_INTERPRETER" =~ ^[01]$ ]] \
  || fail_setup "SANITIZE_INTERPRETER must be 0 or 1"
if [ -n "$EXPECTED_COVERED" ]; then
  [[ "$EXPECTED_COVERED" =~ ^[0-9]+$ ]] \
    || fail_setup "EXPECTED_COVERED must be a nonnegative integer"
fi
if [ -n "$EXPECTED_FRONTIER" ]; then
  [[ "$EXPECTED_FRONTIER" =~ ^[0-9]+$ ]] \
    || fail_setup "EXPECTED_FRONTIER must be a nonnegative integer"
fi
if [ "$SANITIZE" = 1 ]; then
  command -v "$CC" >/dev/null 2>&1 || fail_setup "C compiler missing: $CC"
fi

tmp="$(mktemp -d)" || fail_setup "cannot create temporary directory"
trap 'rm -rf "$tmp"' EXIT

covered_manifest_names() {
  local manifest="$1" output="$2" parsed="$tmp/covered-parsed"
  sed \
    -e 's/[[:space:]]*#.*$//' \
    -e 's/^[[:space:]]*//' \
    -e 's/[[:space:]]*$//' \
    -e '/^$/d' \
    "$manifest" >"$parsed" \
    || fail_setup "cannot parse covered manifest"
  if LC_ALL=C grep -nEv '^[a-z0-9][a-z0-9_.-]*[.]guji$' "$parsed" \
      >"$tmp/covered-invalid"; then
    sed 's/^/  /' "$tmp/covered-invalid"
    fail_setup "covered manifest contains a malformed row"
  fi
  LC_ALL=C sort "$parsed" >"$tmp/covered-all" \
    || fail_setup "cannot sort covered manifest"
  LC_ALL=C sort -u "$parsed" >"$output" \
    || fail_setup "cannot normalize covered manifest"
  cmp -s "$tmp/covered-all" "$output" \
    || fail_setup "covered manifest contains duplicate rows"
}

covered_manifest_names "$COVERED_MANIFEST" "$tmp/covered"
sed -e 's/#.*$//' -e '/^[[:space:]]*$/d' -e 's/[[:space:]].*$//' \
  "$FRONTIER_MANIFEST" | LC_ALL=C sort -u >"$tmp/frontier" \
  || fail_setup "cannot normalize frontier manifest"
find "$CORPUS_DIR" -maxdepth 1 -type f -name '*.guji' -printf '%f\n' | sort -u >"$tmp/all"

if comm -12 "$tmp/covered" "$tmp/frontier" | grep -q .; then
  echo "interpreter-diff SETUP: covered/frontier manifests overlap:"
  comm -12 "$tmp/covered" "$tmp/frontier" | sed 's/^/  /'
  exit 2
fi
cat "$tmp/covered" "$tmp/frontier" | sort -u >"$tmp/classified"
if ! cmp -s "$tmp/all" "$tmp/classified"; then
  echo "interpreter-diff SETUP: eval corpus is not exactly partitioned by covered/frontier manifests"
  diff -u "$tmp/all" "$tmp/classified" || true
  exit 2
fi
covered_count="$(wc -l <"$tmp/covered")"
frontier_count="$(wc -l <"$tmp/frontier")"
if [ -n "$EXPECTED_COVERED" ] && [ "$covered_count" -ne "$EXPECTED_COVERED" ]; then
  fail_setup "expected $EXPECTED_COVERED covered rows, found $covered_count"
fi
if [ -n "$EXPECTED_FRONTIER" ] && [ "$frontier_count" -ne "$EXPECTED_FRONTIER" ]; then
  fail_setup "expected $EXPECTED_FRONTIER frontier rows, found $frontier_count"
fi

read_args() {
  FIXTURE_ARGS=()
  [ -f "$1.args" ] && mapfile -t FIXTURE_ARGS <"$1.args"
}

pass=0
fail=0
while IFS= read -r name; do
  [ -n "$name" ] || continue
  src="$CORPUS_DIR/$name"
  base="${src%.guji}"
  [ -f "$base.expected" ] || fail_setup "spec expectation missing: $base.expected"
  expected_rc=0
  if [ -f "$base.exit" ]; then
    expected_rc="$(tr -d '[:space:]' <"$base.exit")"
    [[ "$expected_rc" =~ ^[0-9]+$ ]] || fail_setup "malformed expected exit: $base.exit"
  fi
  expected_err=/dev/null
  [ -f "$base.stderr" ] && expected_err="$base.stderr"
  stdin_file=/dev/null
  [ -f "$base.stdin" ] && stdin_file="$base.stdin"
  read_args "$base"
  rundir="$(dirname "$src")"

  (cd "$rundir" && timeout "$PROG_TIMEOUT" "$GUJI" "$src" "${FIXTURE_ARGS[@]}") \
    <"$stdin_file" >"$tmp/interp.out" 2>"$tmp/interp.err"
  interp_rc=$?

  interp_sanitized_rc="$interp_rc"
  cp "$tmp/interp.out" "$tmp/interp-sanitized.out"
  cp "$tmp/interp.err" "$tmp/interp-sanitized.err"
  if [ "$SANITIZE_INTERPRETER" = 1 ]; then
    (cd "$rundir" && ASAN_OPTIONS=detect_leaks=1:halt_on_error=1 \
        UBSAN_OPTIONS=halt_on_error=1 timeout "$PROG_TIMEOUT" \
        "$GUJI_SAN" "$src" "${FIXTURE_ARGS[@]}") \
      <"$stdin_file" >"$tmp/interp-sanitized.out" 2>"$tmp/interp-sanitized.err"
    interp_sanitized_rc=$?
  fi

  rm -f "$tmp/program" "$tmp/program.c" "$tmp/program.asan" \
    || fail_setup "cannot clear per-row compiler artifacts"
  timeout "$PROG_TIMEOUT" "$GUJI2C" "$src" "$tmp/program" "$PROLOGUE" \
    >"$tmp/build.out" 2>"$tmp/build.err"
  build_rc=$?
  if [ "$build_rc" -ne 0 ]; then
    # A front-end rejection is itself an exact D/C outcome when the fixture
    # explicitly expects exit 1. No generated program exists to sanitize, but
    # both normal and sanitized interpreters must make the same static decision
    # and the compiler diagnostic must match byte-for-byte.
    if [ "$build_rc" -eq 1 ] \
        && [ "$expected_rc" -eq 1 ] \
        && [ "$interp_rc" -eq 1 ] \
        && [ "$interp_sanitized_rc" -eq 1 ] \
        && cmp -s "$tmp/interp.out" "$tmp/build.out" \
        && cmp -s "$tmp/interp.err" "$tmp/build.err" \
        && cmp -s "$tmp/interp.out" "$tmp/interp-sanitized.out" \
        && cmp -s "$tmp/interp.err" "$tmp/interp-sanitized.err" \
        && cmp -s "$tmp/interp.out" "$base.expected" \
        && cmp -s "$tmp/interp.err" "$expected_err"; then
      echo "PASS $name (static reject rc=1)"
      pass=$((pass + 1))
    else
      echo "FAIL $name: canonical compiler declined or failed (rc=$build_rc)"
      sed 's/^/  /' "$tmp/build.err" | head -n 12
      fail=$((fail + 1))
    fi
    continue
  fi
  if [ ! -x "$tmp/program" ]; then
    echo "FAIL $name: canonical compiler did not produce a fresh executable"
    fail=$((fail + 1))
    continue
  fi
  (cd "$rundir" && timeout "$PROG_TIMEOUT" "$tmp/program" "${FIXTURE_ARGS[@]}") \
    <"$stdin_file" >"$tmp/compiler.out" 2>"$tmp/compiler.err"
  compiler_rc=$?

  sanitized_rc="$compiler_rc"
  cp "$tmp/compiler.out" "$tmp/sanitized.out"
  cp "$tmp/compiler.err" "$tmp/sanitized.err"
  if [ "$SANITIZE" = 1 ]; then
    if [ ! -f "$tmp/program.c" ]; then
      echo "FAIL $name: canonical compiler did not produce fresh generated C"
      fail=$((fail + 1))
      continue
    fi
    if ! "$CC" -O1 -g -fwrapv \
          -fsanitize=address,undefined -fno-omit-frame-pointer \
          "$tmp/program.c" -o "$tmp/program.asan" -lm -pthread \
          >"$tmp/sanitize-build.out" 2>"$tmp/sanitize-build.err" \
        || [ ! -x "$tmp/program.asan" ]; then
      echo "FAIL $name: sanitizer build failed"
      sed 's/^/  /' "$tmp/sanitize-build.err" | head -n 12
      fail=$((fail + 1))
      continue
    fi
    (cd "$rundir" && ASAN_OPTIONS=detect_leaks=1:halt_on_error=1 \
        UBSAN_OPTIONS=halt_on_error=1 timeout "$PROG_TIMEOUT" \
        "$tmp/program.asan" "${FIXTURE_ARGS[@]}") \
      <"$stdin_file" >"$tmp/sanitized.out" 2>"$tmp/sanitized.err"
    sanitized_rc=$?
  fi

  if is_infrastructure_status "$interp_rc" \
      || is_infrastructure_status "$interp_sanitized_rc" \
      || is_infrastructure_status "$compiler_rc" \
      || is_infrastructure_status "$sanitized_rc"; then
    echo "FAIL $name: runtime returned infrastructure status (interpreter rc=$interp_rc, interpreter-sanitized rc=$interp_sanitized_rc, compiler rc=$compiler_rc, compiler-sanitized rc=$sanitized_rc)"
    fail=$((fail + 1))
    continue
  fi

  if [ "$interp_rc" -eq "$compiler_rc" ] \
      && [ "$interp_rc" -eq "$interp_sanitized_rc" ] \
      && [ "$compiler_rc" -eq "$sanitized_rc" ] \
      && cmp -s "$tmp/interp.out" "$tmp/compiler.out" \
      && cmp -s "$tmp/interp.err" "$tmp/compiler.err" \
      && cmp -s "$tmp/interp.out" "$tmp/interp-sanitized.out" \
      && cmp -s "$tmp/interp.err" "$tmp/interp-sanitized.err" \
      && cmp -s "$tmp/compiler.out" "$tmp/sanitized.out" \
      && cmp -s "$tmp/compiler.err" "$tmp/sanitized.err" \
      && [ "$interp_rc" -eq "$expected_rc" ] \
      && cmp -s "$tmp/interp.out" "$base.expected" \
      && cmp -s "$tmp/interp.err" "$expected_err"; then
    echo "PASS $name (rc=$interp_rc)"
    pass=$((pass + 1))
  else
    echo "FAIL $name: D/C behavior differs (interpreter rc=$interp_rc, interpreter-sanitized rc=$interp_sanitized_rc, compiler rc=$compiler_rc, compiler-sanitized rc=$sanitized_rc)"
    if ! cmp -s "$tmp/interp.out" "$tmp/compiler.out"; then
      echo "  stdout diff:"
      diff -u "$tmp/interp.out" "$tmp/compiler.out" | sed 's/^/    /' | head -n 30 || true
    fi
    if ! cmp -s "$tmp/interp.err" "$tmp/compiler.err"; then
      echo "  stderr diff:"
      diff -u "$tmp/interp.err" "$tmp/compiler.err" | sed 's/^/    /' | head -n 30 || true
    fi
    if [ "$interp_rc" -ne "$interp_sanitized_rc" ] \
        || ! cmp -s "$tmp/interp.out" "$tmp/interp-sanitized.out" \
        || ! cmp -s "$tmp/interp.err" "$tmp/interp-sanitized.err"; then
      echo "  interpreter sanitizer diff:"
      diff -u "$tmp/interp.out" "$tmp/interp-sanitized.out" | sed 's/^/    /' | head -n 30 || true
      diff -u "$tmp/interp.err" "$tmp/interp-sanitized.err" | sed 's/^/    /' | head -n 30 || true
    fi
    if [ "$compiler_rc" -ne "$sanitized_rc" ] \
        || ! cmp -s "$tmp/compiler.out" "$tmp/sanitized.out" \
        || ! cmp -s "$tmp/compiler.err" "$tmp/sanitized.err"; then
      echo "  sanitizer diff:"
      diff -u "$tmp/compiler.out" "$tmp/sanitized.out" | sed 's/^/    /' | head -n 30 || true
      diff -u "$tmp/compiler.err" "$tmp/sanitized.err" | sed 's/^/    /' | head -n 30 || true
    fi
    if [ "$interp_rc" -ne "$expected_rc" ] \
        || ! cmp -s "$tmp/interp.out" "$base.expected" \
        || ! cmp -s "$tmp/interp.err" "$expected_err"; then
      echo "  spec expectation mismatch (expected rc=$expected_rc):"
      diff -u "$base.expected" "$tmp/interp.out" | sed 's/^/    /' | head -n 30 || true
      diff -u "$expected_err" "$tmp/interp.err" | sed 's/^/    /' | head -n 30 || true
    fi
    fail=$((fail + 1))
  fi
done <"$tmp/covered"

echo "-- canonical interpreter differential: $pass exact+sanitized, $fail failed, $frontier_count explicit frontier --"
[ "$fail" -eq 0 ]
