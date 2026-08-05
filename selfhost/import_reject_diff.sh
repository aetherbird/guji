#!/usr/bin/env bash
# Exact native D/C load-rejection differential for §16 import graph failures.
# These rows cannot enter interpreter_diff.sh's runtime corpus because the
# compiler must reject before it can produce a binary.

set -uo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
CORPUS_DIR="${IMPORT_REJECT_CORPUS_DIR:-$REPO_ROOT/selfhost/import_reject_corpus}"
MANIFEST="${IMPORT_REJECT_MANIFEST:-$REPO_ROOT/selfhost/import_reject_corpus.txt}"
PROLOGUE="${PROLOGUE:-$REPO_ROOT/selfhost/rt/runtime_prologue.c}"
PROG_TIMEOUT="${PROG_TIMEOUT:-120}"

GUJI2C="${GUJI2C:-}"
GUJI="${GUJI:-}"

fail_setup() {
  echo "import-reject-diff SETUP: $*"
  exit 2
}

[ -x "$GUJI2C" ] || fail_setup "native Guji compiler missing; set GUJI2C=<path>"
[ -x "$GUJI" ] || fail_setup "native Guji interpreter missing; set GUJI=<path>"
[ -d "$CORPUS_DIR" ] || fail_setup "corpus directory missing: $CORPUS_DIR"
[ -f "$MANIFEST" ] || fail_setup "manifest missing: $MANIFEST"
[ -f "$PROLOGUE" ] || fail_setup "runtime prologue missing: $PROLOGUE"

tmp="$(mktemp -d)" || fail_setup "cannot create temporary directory"
trap 'rm -rf "$tmp"' EXIT

sed -e 's/#.*$//' -e '/^[[:space:]]*$/d' -e 's/[[:space:]].*$//' "$MANIFEST" | sort -u >"$tmp/manifest"
find "$CORPUS_DIR" -maxdepth 1 -type f -name '*.guji' -printf '%f\n' | sort -u >"$tmp/all"
if ! cmp -s "$tmp/all" "$tmp/manifest"; then
  echo "import-reject-diff SETUP: corpus is not exactly enumerated by manifest"
  diff -u "$tmp/all" "$tmp/manifest" || true
  exit 2
fi

pass=0
fail=0
while IFS= read -r name; do
  [ -n "$name" ] || continue
  base="${name%.guji}"
  [ -f "$CORPUS_DIR/$base.expected" ] || fail_setup "stdout expectation missing: $base.expected"
  [ -f "$CORPUS_DIR/$base.stderr" ] || fail_setup "stderr expectation missing: $base.stderr"
  [ -f "$CORPUS_DIR/$base.exit" ] || fail_setup "exit expectation missing: $base.exit"
  expected_rc="$(tr -d '[:space:]' <"$CORPUS_DIR/$base.exit")"
  [[ "$expected_rc" =~ ^[0-9]+$ ]] || fail_setup "malformed expected exit: $base.exit"

  (cd "$CORPUS_DIR" && timeout "$PROG_TIMEOUT" "$GUJI" "$name") \
    >"$tmp/interp.out" 2>"$tmp/interp.err"
  interp_rc=$?
  (cd "$CORPUS_DIR" && timeout "$PROG_TIMEOUT" "$GUJI2C" "$name" "$tmp/program" "$PROLOGUE") \
    >"$tmp/compiler.out" 2>"$tmp/compiler.err"
  compiler_rc=$?

  if [ "$interp_rc" -eq "$compiler_rc" ] \
      && [ "$interp_rc" -eq "$expected_rc" ] \
      && cmp -s "$tmp/interp.out" "$tmp/compiler.out" \
      && cmp -s "$tmp/interp.err" "$tmp/compiler.err" \
      && cmp -s "$tmp/interp.out" "$CORPUS_DIR/$base.expected" \
      && cmp -s "$tmp/interp.err" "$CORPUS_DIR/$base.stderr"; then
    echo "PASS $name (load reject rc=$interp_rc)"
    pass=$((pass + 1))
  else
    echo "FAIL $name: D/C load rejection differs (interpreter rc=$interp_rc, compiler rc=$compiler_rc, expected rc=$expected_rc)"
    diff -u "$tmp/interp.out" "$tmp/compiler.out" | sed 's/^/  /' | head -n 30 || true
    diff -u "$tmp/interp.err" "$tmp/compiler.err" | sed 's/^/  /' | head -n 30 || true
    diff -u "$CORPUS_DIR/$base.expected" "$tmp/interp.out" | sed 's/^/  /' | head -n 30 || true
    diff -u "$CORPUS_DIR/$base.stderr" "$tmp/interp.err" | sed 's/^/  /' | head -n 30 || true
    fail=$((fail + 1))
  fi
done <"$tmp/manifest"

echo "-- canonical import rejection differential: $pass exact, $fail failed --"
[ "$fail" -eq 0 ]
