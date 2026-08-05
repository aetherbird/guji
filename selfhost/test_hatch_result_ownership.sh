#!/usr/bin/env bash
# Fail-closed ownership gate for hatch-captured Result payloads. Runtime
# sanitizers can be skipped structurally when main exits with a live task, so
# generated C must independently prove active-arm copy and task-exit release.

set -uo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
FIXTURE="$REPO_ROOT/selfhost/eval_corpus/hatch_carrier_capture.guji"
EXPECTED="$REPO_ROOT/selfhost/eval_corpus/hatch_carrier_capture.expected"
PROLOGUE="${PROLOGUE:-$REPO_ROOT/selfhost/rt/runtime_prologue.c}"
GUJI2C="${GUJI2C:-}"
GUJI="${GUJI:-}"
GUJI_SAN="${GUJI_SAN:-}"
CC="${CC:-cc}"
PROG_TIMEOUT="${PROG_TIMEOUT:-120}"
D_SANITIZE_ITERS="${D_SANITIZE_ITERS:-500}"

fail_setup() {
  echo "hatch-result-ownership SETUP: $*"
  exit 2
}

fail_shape() {
  echo "hatch-result-ownership RED: $*"
  exit 1
}

[ -x "$GUJI2C" ] || fail_setup "native Guji compiler missing; set GUJI2C=<path>"
[ -x "$GUJI" ] || fail_setup "native Guji interpreter missing; set GUJI=<path>"
[ -x "$GUJI_SAN" ] \
  || fail_setup "sanitized native Guji interpreter missing; set GUJI_SAN=<path>"
command -v "$CC" >/dev/null 2>&1 || fail_setup "C compiler missing: $CC"
[ -f "$FIXTURE" ] || fail_setup "fixture missing: $FIXTURE"
[ -f "$EXPECTED" ] || fail_setup "expectation missing: $EXPECTED"
[ -f "$PROLOGUE" ] || fail_setup "runtime prologue missing: $PROLOGUE"
[[ "$PROG_TIMEOUT" =~ ^[1-9][0-9]*$ ]] \
  || fail_setup "PROG_TIMEOUT must be a positive integer"
[[ "$D_SANITIZE_ITERS" =~ ^[1-9][0-9]*$ ]] \
  || fail_setup "D_SANITIZE_ITERS must be a positive integer"
[ "$D_SANITIZE_ITERS" -ge 500 ] \
  || fail_setup "D_SANITIZE_ITERS must be at least 500"

tmp="$(mktemp -d)" || fail_setup "cannot create temporary directory"
trap 'rm -rf "$tmp"' EXIT

cur_stack="$(ulimit -s 2>/dev/null || echo 0)"
if [ "$cur_stack" != "unlimited" ] && [ "${cur_stack:-0}" -lt 65536 ] 2>/dev/null; then
  ulimit -s 65536 || fail_setup "cannot raise compiler stack soft limit"
fi

if ! timeout "$PROG_TIMEOUT" "$GUJI2C" \
    "$FIXTURE" "$tmp/program" "$PROLOGUE" \
    >"$tmp/build.out" 2>"$tmp/build.err"; then
  echo "hatch-result-ownership RED: canonical compiler failed"
  sed -n '1,80p' "$tmp/build.err"
  exit 1
fi
[ -x "$tmp/program" ] || fail_shape "compiler produced no executable"
[ -f "$tmp/program.c" ] || fail_shape "compiler produced no generated C"

# Extract the one hatch body that adopts all four carrier captures. Restricting
# release checks to this function prevents an unrelated local with the same
# generated name from satisfying the gate.
awk '
  /^static int64_t ghatch_[0-9]+_body\(void\* arg\)/ {
    in_body = 1
    body = $0 ORS
    target = 0
    next
  }
  in_body && /^static void ghatch_[0-9]+\(void\* arg\)/ {
    if (target) {
      printf "%s", body
      exit
    }
    in_body = 0
    body = ""
    next
  }
  in_body {
    body = body $0 ORS
    if ($0 ~ /env->cap_match_result/) {
      target = 1
    }
  }
' "$tmp/program.c" >"$tmp/hatch-body.c"
[ -s "$tmp/hatch-body.c" ] \
  || fail_shape "cannot isolate four-carrier hatch body"

assert_carrier_shape() {
  local field="$1" copy_fn="$2" arm="$3" op="$4"
  local fill src dest copy_line adopt local_name release_line

  fill="$(
    grep -E -m1 -- \
      "->[[:space:]]*cap_${field} = [A-Za-z_][A-Za-z0-9_]*;" \
      "$tmp/program.c" || true
  )"
  [ -n "$fill" ] || fail_shape "missing capture fill for $field"
  src="$(
    printf '%s\n' "$fill" \
      | sed -E "s/.*cap_${field} = ([A-Za-z_][A-Za-z0-9_]*);.*/\\1/"
  )"
  dest="$(
    printf '%s\n' "$fill" \
      | sed -E "s/^[[:space:]]*([A-Za-z_][A-Za-z0-9_]*)->cap_${field}.*/\\1/"
  )"
  copy_line="if (${src}.tag ${op} 0LL) { ${dest}->cap_${field}.${arm} = ${copy_fn}(${src}.${arm}); }"
  grep -F -q -- "$copy_line" "$tmp/program.c" \
    || fail_shape "missing active-$arm deep copy for $field"

  adopt="$(
    grep -E -m1 -- \
      "^[[:space:]]*[A-Za-z_][A-Za-z0-9_]* = env->cap_${field};" \
      "$tmp/hatch-body.c" || true
  )"
  [ -n "$adopt" ] || fail_shape "missing child adoption for $field"
  local_name="$(
    printf '%s\n' "$adopt" \
      | sed -E 's/^[[:space:]]*([A-Za-z_][A-Za-z0-9_]*) =.*/\1/'
  )"
  release_line="if (${local_name}.tag ${op} 0LL) { guji_release((const void*)${local_name}.${arm}); ${local_name}.${arm} = NULL; }"
  grep -F -q -- "$release_line" "$tmp/hatch-body.c" \
    || fail_shape "missing active-$arm task-exit release for $field"
}

assert_carrier_shape bush_ok_result guji_bush_copy ok "=="
assert_carrier_shape bush_result guji_bush_copy err "!="
assert_carrier_shape match_ok_result guji_match_copy ok "=="
assert_carrier_shape match_result guji_match_copy err "!="

if ! "$CC" -O1 -g -fwrapv \
    -fsanitize=address,undefined -fno-omit-frame-pointer \
    "$tmp/program.c" -o "$tmp/program.asan" -lm -pthread \
    >"$tmp/sanitize-build.out" 2>"$tmp/sanitize-build.err"; then
  echo "hatch-result-ownership RED: sanitizer build failed"
  sed -n '1,80p' "$tmp/sanitize-build.err"
  exit 1
fi

for i in 1 2 3 4 5; do
  if ! timeout "$PROG_TIMEOUT" "$GUJI" "$FIXTURE" \
      >"$tmp/d.out" 2>"$tmp/d.err" \
      || ! cmp -s "$tmp/d.out" "$EXPECTED" || [ -s "$tmp/d.err" ]; then
    echo "hatch-result-ownership RED: D normal run $i/5 failed"
    sed -n '1,80p' "$tmp/d.err"
    exit 1
  fi

  if ! timeout "$PROG_TIMEOUT" "$tmp/program" \
      >"$tmp/c.out" 2>"$tmp/c.err" \
      || ! cmp -s "$tmp/c.out" "$EXPECTED" || [ -s "$tmp/c.err" ]; then
    echo "hatch-result-ownership RED: C normal run $i/5 failed"
    sed -n '1,80p' "$tmp/c.err"
    exit 1
  fi

  if ! ASAN_OPTIONS=detect_leaks=1:halt_on_error=1 \
      UBSAN_OPTIONS=halt_on_error=1 \
      timeout "$PROG_TIMEOUT" "$tmp/program.asan" \
      >"$tmp/c-san.out" 2>"$tmp/c-san.err" \
      || ! cmp -s "$tmp/c-san.out" "$EXPECTED" || [ -s "$tmp/c-san.err" ]; then
    echo "hatch-result-ownership RED: C sanitized run $i/5 failed"
    sed -n '1,80p' "$tmp/c-san.err"
    exit 1
  fi
done

for ((i=1; i<=D_SANITIZE_ITERS; i++)); do
  if ! ASAN_OPTIONS=detect_leaks=1:halt_on_error=1 \
      UBSAN_OPTIONS=halt_on_error=1 \
      timeout "$PROG_TIMEOUT" "$GUJI_SAN" "$FIXTURE" \
      >"$tmp/d-san.out" 2>"$tmp/d-san.err" \
      || ! cmp -s "$tmp/d-san.out" "$EXPECTED" || [ -s "$tmp/d-san.err" ]; then
    echo "hatch-result-ownership RED: D sanitized run $i/$D_SANITIZE_ITERS failed"
    sed -n '1,80p' "$tmp/d-san.err"
    exit 1
  fi
done

echo "hatch-result-ownership GREEN: four active carrier arms shaped; D/C normal and C sanitized 5/5; D sanitized $D_SANITIZE_ITERS/$D_SANITIZE_ITERS"
