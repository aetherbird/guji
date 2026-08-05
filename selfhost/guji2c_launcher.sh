#!/usr/bin/env bash
# Stack-safe launcher installed beside the fixed-point guji2c.bin.

set -uo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
COMPILER="${GUJI2C_BINARY:-$SCRIPT_DIR/guji2c.bin}"
REQUIRED_STACK_KIB=65536

fail_setup() {
  echo "guji2c SETUP: $*" >&2
  exit 2
}

[ -x "$COMPILER" ] || fail_setup "native compiler is missing or not executable: $COMPILER"

current_stack="$(ulimit -Ss 2>/dev/null || echo 0)"
if [ "$current_stack" != "unlimited" ] \
   && [ "${current_stack:-0}" -lt "$REQUIRED_STACK_KIB" ] 2>/dev/null; then
  ulimit -S -s "$REQUIRED_STACK_KIB" \
    || fail_setup "cannot raise stack soft limit to ${REQUIRED_STACK_KIB} KiB"
fi

exec "$COMPILER" "$@"
