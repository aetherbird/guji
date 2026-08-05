#!/usr/bin/env bash
# Runtime contract: completed language tasks are joined internally before a
# later spawn or normal process exit, making thread teardown deterministic.

set -uo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
PROLOGUE="$REPO_ROOT/selfhost/rt/runtime_prologue.c"
CONC="$REPO_ROOT/selfhost/rt/guji_conc.c"
HARNESS="$REPO_ROOT/selfhost/rt/guji_conc_reaper_test.c"
CC="${CC:-cc}"

fail_setup() {
  echo "concurrency-reaper SETUP: $*"
  exit 2
}

command -v "$CC" >/dev/null 2>&1 || fail_setup "C compiler missing: $CC"
[ -f "$PROLOGUE" ] || fail_setup "runtime prologue missing: $PROLOGUE"
[ -f "$CONC" ] || fail_setup "concurrency runtime missing: $CONC"
[ -f "$HARNESS" ] || fail_setup "reaper harness missing: $HARNESS"

tmp="$(mktemp -d)" || fail_setup "cannot create temporary directory"
trap 'rm -rf "$tmp"' EXIT

cat "$PROLOGUE" "$CONC" "$HARNESS" >"$tmp/reaper.c" \
  || fail_setup "cannot assemble reaper harness"

if ! "$CC" -O2 -g -fwrapv "$tmp/reaper.c" -o "$tmp/reaper" -lm -pthread \
    >"$tmp/normal-build.out" 2>"$tmp/normal-build.err"; then
  echo "concurrency-reaper RED: normal build failed"
  sed -n '1,80p' "$tmp/normal-build.err"
  exit 1
fi

if ! "$CC" -O1 -g -fwrapv \
    -fsanitize=address,undefined -fno-omit-frame-pointer \
    "$tmp/reaper.c" -o "$tmp/reaper.asan" -lm -pthread \
    >"$tmp/sanitize-build.out" 2>"$tmp/sanitize-build.err"; then
  echo "concurrency-reaper RED: sanitizer build failed"
  sed -n '1,80p' "$tmp/sanitize-build.err"
  exit 1
fi

printf '%s\n' 'concurrency-reaper: PASS' >"$tmp/expected"
for i in 1 2 3 4 5; do
  if ! timeout 30 "$tmp/reaper" >"$tmp/normal.out" 2>"$tmp/normal.err" \
      || ! cmp -s "$tmp/normal.out" "$tmp/expected" \
      || [ -s "$tmp/normal.err" ]; then
    echo "concurrency-reaper RED: normal run $i/5 failed"
    sed -n '1,80p' "$tmp/normal.err"
    exit 1
  fi

  if ! ASAN_OPTIONS=detect_leaks=1:halt_on_error=1 \
      UBSAN_OPTIONS=halt_on_error=1 \
      timeout 30 "$tmp/reaper.asan" >"$tmp/sanitize.out" 2>"$tmp/sanitize.err" \
      || ! cmp -s "$tmp/sanitize.out" "$tmp/expected" \
      || [ -s "$tmp/sanitize.err" ]; then
    echo "concurrency-reaper RED: sanitized run $i/5 failed"
    sed -n '1,80p' "$tmp/sanitize.err"
    exit 1
  fi
done

echo "concurrency-reaper GREEN: normal and ASan/UBSan/LSan 5/5"
