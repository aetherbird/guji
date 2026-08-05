#!/usr/bin/env bash
# Source-bootstrap and native self-hosting acceptance entrypoint.
#
# Kept under its historical name because P-accept and operator workflows invoke
# it directly. The proof itself is entirely native:
#
#   checked-in generated C -> seed guji2c -> gen1 -> gen2 -> gen3
#
# Generations 2 and 3 must reproduce byte-identical generated C and compiler
# binaries, and the reproduced compiler must pass the pinned smoke programs.
# When GUJI2C is provided, that caller-selected compiler remains the seed. When
# it is unset, build_bootstrap_seed.sh verifies and compiles the checked-in C
# seed. The fixed-point implementation still lives in selfcompile_gate.sh so
# there is one definition of self-hosting throughout the pipeline.
#
set -uo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

if [ -n "${GUJI2C:-}" ]; then
  exec bash "$REPO_ROOT/selfhost/selfcompile_gate.sh"
fi

bootstrap_tmp="$(mktemp -d)" || {
  echo "bootstrap SETUP: cannot create a temporary directory" >&2
  exit 2
}
cleanup() {
  rm -rf "$bootstrap_tmp"
}
trap cleanup EXIT

seed="$bootstrap_tmp/guji2c"
bash "$REPO_ROOT/selfhost/build_bootstrap_seed.sh" "$seed" || exit $?

echo "bootstrap: entering native fixed-point proof with the verified source seed"
GUJI2C="$seed" bash "$REPO_ROOT/selfhost/selfcompile_gate.sh"
