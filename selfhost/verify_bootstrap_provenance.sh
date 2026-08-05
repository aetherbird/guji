#!/usr/bin/env bash
# Validate the checked-in bootstrap artifact and its declared public inputs.

set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
PROVENANCE="$REPO_ROOT/bootstrap/PROVENANCE"
CHECKSUM="$REPO_ROOT/bootstrap/guji2c.c.sha256"
ARTIFACT="$REPO_ROOT/bootstrap/guji2c.c"

fail() {
  printf 'bootstrap-provenance RED: %s\n' "$*" >&2
  exit 1
}

for input in "$PROVENANCE" "$CHECKSUM" "$ARTIFACT"; do
  [ -f "$input" ] && [ ! -L "$input" ] \
    || fail "required input is not a regular file: $input"
done

declare -A value=()
while IFS='=' read -r key item; do
  [ -n "$key" ] && [ -n "$item" ] && [[ "$key" =~ ^[a-z][a-z0-9_]*$ ]] \
    || fail "malformed provenance row"
  [ -z "${value[$key]+x}" ] || fail "duplicate provenance key: $key"
  value["$key"]="$item"
done <"$PROVENANCE"

required_keys=(
  format
  artifact
  artifact_sha256
  generator
  generator_sha256
  compile_driver_sha256
  lexer_sha256
  runtime_prologue_sha256
  concurrency_runtime_sha256
  generator_cc
  generator_cc_flags
  reference_binary_sha256
)
[ "${#value[@]}" -eq "${#required_keys[@]}" ] \
  || fail "provenance has unexpected or missing keys"
for key in "${required_keys[@]}"; do
  [ -n "${value[$key]:-}" ] || fail "provenance key is missing: $key"
done

[ "${value[format]}" = 1 ] || fail "unsupported provenance format"
[ "${value[artifact]}" = guji2c.c ] || fail "unexpected artifact name"
[ "${value[generator]}" = guji2c ] || fail "unexpected generator name"
for key in \
  artifact_sha256 \
  generator_sha256 \
  compile_driver_sha256 \
  lexer_sha256 \
  runtime_prologue_sha256 \
  concurrency_runtime_sha256 \
  reference_binary_sha256; do
  [[ "${value[$key]}" =~ ^[0-9a-f]{64}$ ]] \
    || fail "invalid SHA-256 in $key"
done

checksum_row="$(cat "$CHECKSUM")"
[ "$checksum_row" = "${value[artifact_sha256]}  guji2c.c" ] \
  || fail "checksum file and provenance disagree"
[ "$(sha256sum "$ARTIFACT" | cut -d' ' -f1)" = "${value[artifact_sha256]}" ] \
  || fail "generated C digest does not match provenance"

check_input() {
  local key="$1" path="$2" actual
  [ -f "$path" ] && [ ! -L "$path" ] \
    || fail "declared source input is not a regular file: $path"
  actual="$(sha256sum "$path" | cut -d' ' -f1)"
  [ "$actual" = "${value[$key]}" ] \
    || fail "declared source input changed without bootstrap regeneration: ${path#$REPO_ROOT/}"
}

check_input compile_driver_sha256 "$REPO_ROOT/selfhost/compile_driver.guji"
check_input lexer_sha256 "$REPO_ROOT/selfhost/lexer.guji"
check_input runtime_prologue_sha256 "$REPO_ROOT/selfhost/rt/runtime_prologue.c"
check_input concurrency_runtime_sha256 "$REPO_ROOT/selfhost/rt/guji_conc.c"

[ "${value[reference_binary_sha256]}" = "${value[generator_sha256]}" ] \
  || fail "reference binary did not reproduce the recorded generator"

printf 'bootstrap-provenance GREEN: artifact and four public inputs match\n'
