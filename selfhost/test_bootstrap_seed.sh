#!/usr/bin/env bash
# Fast fail-closed contract tests for build_bootstrap_seed.sh.

set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
HELPER="$REPO_ROOT/selfhost/build_bootstrap_seed.sh"
SOURCE="$REPO_ROOT/bootstrap/guji2c.c"
CHECKSUM="$REPO_ROOT/bootstrap/guji2c.c.sha256"
tmp="$(mktemp -d)"
cleanup() {
  rm -rf "$tmp"
}
trap cleanup EXIT

source_before="$(sha256sum "$SOURCE" | cut -d' ' -f1)"
checksum_before="$(sha256sum "$CHECKSUM" | cut -d' ' -f1)"

if bash "$HELPER" "$SOURCE" >"$tmp/source.log" 2>&1; then
  echo "bootstrap-seed-contract RED: source overwrite was accepted" >&2
  exit 1
fi
grep -q 'output must not overwrite bootstrap input' "$tmp/source.log"

if bash "$HELPER" "$CHECKSUM" >"$tmp/checksum.log" 2>&1; then
  echo "bootstrap-seed-contract RED: checksum overwrite was accepted" >&2
  exit 1
fi
grep -q 'output must not overwrite bootstrap input' "$tmp/checksum.log"

[ "$(sha256sum "$SOURCE" | cut -d' ' -f1)" = "$source_before" ]
[ "$(sha256sum "$CHECKSUM" | cut -d' ' -f1)" = "$checksum_before" ]

# A disposable miniature tree exercises checksum tampering without touching the
# checked-in artifact and must fail before the C compiler is invoked.
mkdir -p "$tmp/tree/selfhost" "$tmp/tree/bootstrap"
cp "$HELPER" "$tmp/tree/selfhost/build_bootstrap_seed.sh"
printf 'int main(void) { return 2; }\n' >"$tmp/tree/bootstrap/guji2c.c"
printf '%064d  guji2c.c\n' 0 >"$tmp/tree/bootstrap/guji2c.c.sha256"
if CC=false bash "$tmp/tree/selfhost/build_bootstrap_seed.sh" "$tmp/out" \
    >"$tmp/tamper.log" 2>&1; then
  echo "bootstrap-seed-contract RED: checksum tampering was accepted" >&2
  exit 1
fi
grep -q 'source seed checksum mismatch' "$tmp/tamper.log"

echo "bootstrap-seed-contract GREEN: tampering and protected outputs fail closed"
