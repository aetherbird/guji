#!/usr/bin/env bash
# Verify and compile the checked-in source-form bootstrap compiler.
#
# Usage: bash selfhost/build_bootstrap_seed.sh <output-path>
#
# The source checksum protects against an accidental or partial local rewrite.
# The generation lineage is recorded in bootstrap/PROVENANCE.

set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
SOURCE="$REPO_ROOT/bootstrap/guji2c.c"
CHECKSUM="$REPO_ROOT/bootstrap/guji2c.c.sha256"
COMPILER="${CC:-cc}"

fail_setup() {
  echo "bootstrap-seed SETUP: $*" >&2
  exit 2
}

[ "$#" -eq 1 ] \
  || fail_setup "usage: bash selfhost/build_bootstrap_seed.sh <output-path>"
[ -f "$SOURCE" ] || fail_setup "source seed missing: $SOURCE"
[ -f "$CHECKSUM" ] || fail_setup "source checksum missing: $CHECKSUM"
command -v sha256sum >/dev/null 2>&1 || fail_setup "sha256sum is required"
command -v "$COMPILER" >/dev/null 2>&1 \
  || fail_setup "C compiler is unavailable: $COMPILER"

expected_hash="$(awk 'NF == 2 && $2 == "guji2c.c" { print $1 }' "$CHECKSUM")"
[[ "$expected_hash" =~ ^[0-9a-f]{64}$ ]] \
  || fail_setup "invalid checksum file: $CHECKSUM"
actual_hash="$(sha256sum "$SOURCE" | cut -d' ' -f1)"
[ "$actual_hash" = "$expected_hash" ] \
  || fail_setup "source seed checksum mismatch"

output="$1"
[ ! -d "$output" ] || fail_setup "output is a directory: $output"
output_abs="$(readlink -m "$output")" \
  || fail_setup "cannot resolve output path: $output"
protected_inputs=(
  "$SOURCE"
  "$CHECKSUM"
  "$REPO_ROOT/bootstrap/PROVENANCE"
  "$REPO_ROOT/selfhost/compile_driver.guji"
  "$REPO_ROOT/selfhost/lexer.guji"
  "$REPO_ROOT/selfhost/rt/runtime_prologue.c"
  "$REPO_ROOT/selfhost/rt/guji_conc.c"
)
for protected in "${protected_inputs[@]}"; do
  if [ "$output_abs" = "$(readlink -m "$protected")" ]; then
    fail_setup "output must not overwrite bootstrap input: $protected"
  fi
done
output_dir="$(dirname "$output")"
mkdir -p "$output_dir" || fail_setup "cannot create output directory: $output_dir"
tmp="$(mktemp "$output_dir/.guji2c-bootstrap.XXXXXX")" \
  || fail_setup "cannot create temporary output in $output_dir"
cleanup() {
  rm -f "$tmp"
}
trap cleanup EXIT

echo "bootstrap-seed: verified guji2c.c sha256=$actual_hash"
echo "bootstrap-seed: compiling with $COMPILER -O2 -fwrapv -lm -pthread"
if ! "$COMPILER" -O2 -fwrapv "$SOURCE" -o "$tmp" -lm -pthread; then
  fail_setup "C compiler failed"
fi
chmod 0755 "$tmp" || fail_setup "cannot make bootstrap compiler executable"

set +e
"$tmp" >/dev/null 2>&1
smoke_rc=$?
set -e
[ "$smoke_rc" -eq 2 ] \
  || fail_setup "bootstrap compiler usage smoke returned $smoke_rc, expected 2"

mv -f "$tmp" "$output" || fail_setup "cannot publish bootstrap compiler: $output"
trap - EXIT
echo "bootstrap-seed GREEN: $(sha256sum "$output" | cut -d' ' -f1)  $output"
