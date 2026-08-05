#!/usr/bin/env bash
# Native self-hosting gate.
#
# The previous verified native Guji compiler builds the candidate compiler. The
# candidate then rebuilds itself twice at the same canonical output path.
# Generations 2 and 3, both emitted by the candidate compiler, must be
# byte-identical, after which the reproduced compiler must pass pinned smokes.
#
# This gate deliberately has no interpreter bootstrap path. The native seed is
# the only executable input to the production compiler chain.
#
# Env: GUJI2C=<path>  explicit caller-trusted previous native compiler. The
#                     public bootstrap entrypoint verifies and builds this seed
#                     from bootstrap/guji2c.c before invoking this gate.
#      CANDIDATE_OUT  optional path receiving the reproduced compiler on success.
#      GEN_TIMEOUT    timeout for each full native self-compile leg (default 60m).
#      PROG_TIMEOUT   timeout for each smoke compile/run (default 120s).
#      SELF_COMPILE_LOCK_FILE  host-wide serialization lock.
#      KEEP_TMP=1     retain artifacts after success.
#      KEEP_TMP_ON_FAILURE=0  delete artifacts after failure (default retains).
#
# Exit codes: 0 green; 1 failed proof; 2 setup error.
set -uo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
DRIVER="$REPO_ROOT/selfhost/compile_driver.guji"
PROLOGUE="$REPO_ROOT/selfhost/rt/runtime_prologue.c"
GEN_TIMEOUT="${GEN_TIMEOUT:-60m}"
PROG_TIMEOUT="${PROG_TIMEOUT:-120}"
KEEP_TMP="${KEEP_TMP:-0}"
KEEP_TMP_ON_FAILURE="${KEEP_TMP_ON_FAILURE:-1}"
SELF_COMPILE_LOCK_FILE="${SELF_COMPILE_LOCK_FILE:-${TMPDIR:-/tmp}/guji-selfcompile.lock}"
CANDIDATE_OUT="${CANDIDATE_OUT:-}"

GUJI2C="${GUJI2C:-}"

elapsed() {
  local seconds="$1"
  printf '%dm%02ds' "$((seconds / 60))" "$((seconds % 60))"
}

fail_setup() {
  echo "sc-gate SETUP: $*"
  exit 2
}

[ -f "$DRIVER" ] || fail_setup "driver missing: $DRIVER"
[ -f "$PROLOGUE" ] || fail_setup "prologue missing: $PROLOGUE"
[ -n "$GUJI2C" ] || fail_setup "GUJI2C is unset; use bootstrap.sh or provide an authenticated seed"
[ -x "$GUJI2C" ] || fail_setup "trusted native compiler is missing or not executable: $GUJI2C"
SEED_COMPILER="$GUJI2C"
if [ -n "$CANDIDATE_OUT" ] \
   && [ "$(readlink -m "$CANDIDATE_OUT")" = "$(readlink -m "$SEED_COMPILER")" ]; then
  fail_setup "CANDIDATE_OUT must not overwrite the trusted seed"
fi

# guji2c's codegen of compile_driver.guji is deeply recursive. The default 8MiB
# soft stack sits on an overflow cliff (flaky SIGSEGV ~10s on gen1/gen3). Raise
# it for this process and its children; 16MiB already stabilizes I5e/I5e2, 64MiB
# leaves headroom for later collection work.
cur_stack="$(ulimit -s 2>/dev/null || echo 0)"
if [ "$cur_stack" != "unlimited" ] && [ "${cur_stack:-0}" -lt 65536 ] 2>/dev/null; then
  ulimit -s 65536 || fail_setup "cannot raise stack soft limit for native self-compile"
fi

# Concurrent builds and detached verification share one seed and one CPU-heavy
# fixed-point proof. Serializing them avoids false timeouts without changing the
# proof performed by either caller.
if [ "${SELF_COMPILE_LOCK_HELD:-0}" != 1 ]; then
  command -v flock >/dev/null 2>&1 || fail_setup "flock is required"
  exec 9>"$SELF_COMPILE_LOCK_FILE" || fail_setup "cannot open lock $SELF_COMPILE_LOCK_FILE"
  lock_started="$SECONDS"
  echo "sc-gate: waiting for host lock $SELF_COMPILE_LOCK_FILE"
  flock 9 || fail_setup "cannot acquire host lock"
  echo "sc-gate: acquired host lock after $((SECONDS - lock_started))s"
fi

tmp="$(mktemp -d)" || fail_setup "cannot create temporary directory"
cleanup() {
  local rc=$?
  if [ "$KEEP_TMP" = 1 ] || { [ "$rc" -ne 0 ] && [ "$KEEP_TMP_ON_FAILURE" = 1 ]; }; then
    echo "sc-gate: retained artifacts: $tmp"
  else
    rm -rf "$tmp"
  fi
}
trap cleanup EXIT

# Snapshot the caller-selected seed only after acquiring the host lock. The
# second hash check guarantees that every generation uses one immutable byte
# sequence even if the caller replaces the original path during the proof.
echo "sc-gate: using explicit GUJI2C seed; caller owns seed authentication"
seed_hash="$(sha256sum "$GUJI2C" | cut -d' ' -f1)" \
  || fail_setup "cannot hash trusted native compiler"
seed_snapshot="$tmp/trusted-seed"
cp "$GUJI2C" "$seed_snapshot" || fail_setup "cannot snapshot trusted native compiler"
chmod 0555 "$seed_snapshot" || fail_setup "cannot protect trusted compiler snapshot"
[ "$(sha256sum "$seed_snapshot" | cut -d' ' -f1)" = "$seed_hash" ] \
  || fail_setup "trusted compiler changed while it was being snapshotted"
GUJI2C="$seed_snapshot"

canon="$tmp/guji2c"

run_generation() {
  local label="$1" compiler="$2" log="$tmp/$1.log" started rc
  echo "sc-gate: $label with native compiler $(sha256sum "$compiler" | cut -d' ' -f1)"
  started="$SECONDS"
  rm -f "$canon" "$canon.c" \
    || fail_setup "cannot clear canonical outputs before $label"
  timeout "$GEN_TIMEOUT" "$compiler" "$DRIVER" "$canon" "$PROLOGUE" >"$log" 2>&1
  rc=$?
  if [ "$rc" -ne 0 ]; then
    if [ "$rc" -eq 124 ]; then
      echo "sc-gate RED: $label timed out after $GEN_TIMEOUT ($(elapsed "$((SECONDS - started))"))"
    else
      echo "sc-gate RED: $label failed (rc=$rc after $(elapsed "$((SECONDS - started))"))"
    fi
    tail -n 15 "$log" | sed 's/^/  /'
    return 1
  fi
  [ -x "$canon" ] || { echo "sc-gate RED: $label produced no compiler executable"; return 1; }
  [ -f "$canon.c" ] || { echo "sc-gate RED: $label produced no generated C"; return 1; }
  cp "$canon" "$tmp/$label.bin" || return 1
  cp "$canon.c" "$tmp/$label.c" || return 1
  echo "sc-gate: $label green ($(elapsed "$((SECONDS - started))"))"
}

# Generation 1 advances the trusted compiler chain to the candidate source.
run_generation gen1 "$GUJI2C" || exit 1

# Generation 2 is the first compiler emitted by the candidate implementation.
# It may legitimately differ from gen1 because gen1 was emitted by the older
# trusted compiler's code generator.
run_generation gen2 "$tmp/gen1.bin" || exit 1

# Generation 3 must reproduce generation 2 exactly. Every leg targets $canon, so
# cc observes the same input path and binary equality is meaningful.
run_generation gen3 "$tmp/gen2.bin" || exit 1

if ! cmp -s "$tmp/gen2.c" "$tmp/gen3.c"; then
  echo "sc-gate RED: candidate did not reproduce byte-identical generated C"
  diff -u "$tmp/gen2.c" "$tmp/gen3.c" | head -n 40 || true
  exit 1
fi
if ! cmp -s "$tmp/gen2.bin" "$tmp/gen3.bin"; then
  echo "sc-gate RED: candidate compiler binary is not a fixed point"
  exit 1
fi
echo "sc-gate: fixed point green (gen2 == gen3 C and binary)"

run_smoke() {
  local fx="$1" want_rc="$2" want_out="$3"
  local src="$REPO_ROOT/selfhost/compile_corpus/$fx.guji"
  local bin="$tmp/$fx.bin" build_log="$tmp/$fx.build.log" run_err="$tmp/$fx.run.err"
  local started rc got_out
  [ -f "$src" ] || fail_setup "smoke fixture missing: $src"
  started="$SECONDS"
  timeout "$PROG_TIMEOUT" "$tmp/gen3.bin" "$src" "$bin" "$PROLOGUE" >"$build_log" 2>&1
  rc=$?
  if [ "$rc" -ne 0 ]; then
    echo "sc-gate RED: reproduced compiler failed to compile $fx (rc=$rc)"
    tail -n 10 "$build_log" | sed 's/^/  /'
    return 1
  fi
  got_out="$(timeout "$PROG_TIMEOUT" "$bin" 2>"$run_err")"
  rc=$?
  if [ "$rc" -ne "$want_rc" ] || [ "$got_out" != "$want_out" ] || [ -s "$run_err" ]; then
    echo "sc-gate RED: smoke $fx mismatch"
    printf '  got:  rc=%s stdout=[%s] stderr=[%s]\n' "$rc" "$got_out" "$(cat "$run_err")"
    printf '  want: rc=%s stdout=[%s] stderr=[]\n' "$want_rc" "$want_out"
    return 1
  fi
  echo "sc-gate: smoke $fx green ($(elapsed "$((SECONDS - started))"))"
}

run_smoke answer 42 "" || exit 1
run_smoke lambda_capture_str_call 90 $'105\n107\n-3' || exit 1

if [ -n "$CANDIDATE_OUT" ]; then
  mkdir -p "$(dirname "$CANDIDATE_OUT")" || fail_setup "cannot create candidate output directory"
  candidate_tmp="$CANDIDATE_OUT.tmp.$$"
  candidate_hash_tmp="$CANDIDATE_OUT.sha256.tmp.$$"
  if ! cp "$tmp/gen3.bin" "$candidate_tmp" \
     || ! chmod 0755 "$candidate_tmp" \
     || ! sha256sum "$candidate_tmp" | cut -d' ' -f1 >"$candidate_hash_tmp"; then
    rm -f "$candidate_tmp" "$candidate_hash_tmp"
    fail_setup "cannot stage candidate compiler and hash"
  fi
  if ! rm -f "$CANDIDATE_OUT.sha256"; then
    rm -f "$candidate_tmp" "$candidate_hash_tmp"
    fail_setup "cannot invalidate previous candidate compiler hash"
  fi
  if ! mv -fT "$candidate_tmp" "$CANDIDATE_OUT"; then
    rm -f "$candidate_tmp" "$candidate_hash_tmp"
    fail_setup "cannot publish candidate compiler"
  fi
  if ! mv -fT "$candidate_hash_tmp" "$CANDIDATE_OUT.sha256"; then
    rm -f "$candidate_hash_tmp"
    fail_setup "cannot publish candidate compiler hash"
  fi
fi

echo "sc-gate GREEN: native compiler chain advanced and candidate is a fixed point"
