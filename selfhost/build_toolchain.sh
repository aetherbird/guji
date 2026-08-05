#!/usr/bin/env bash
# Build the self-hosted Guji compiler and interpreter under dist/.

set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
OUT_DIR="${1:-$REPO_ROOT/dist}"
PROLOGUE="$REPO_ROOT/selfhost/rt/runtime_prologue.c"
EVAL_DRIVER="$REPO_ROOT/selfhost/eval_driver.guji"

fail_setup() {
  echo "build-toolchain SETUP: $*" >&2
  exit 2
}

for command_name in cc sha256sum timeout; do
  command -v "$command_name" >/dev/null 2>&1 \
    || fail_setup "required command is unavailable: $command_name"
done
[ -f "$PROLOGUE" ] || fail_setup "runtime prologue is missing: $PROLOGUE"
[ -f "$EVAL_DRIVER" ] || fail_setup "interpreter driver is missing: $EVAL_DRIVER"

stage="$(mktemp -d)" || fail_setup "cannot create a temporary directory"
cleanup() {
  rm -rf "$stage"
}
trap cleanup EXIT

compiler="$stage/guji2c.bin"
interpreter="$stage/guji"
launcher="$stage/guji2c"

cp "$REPO_ROOT/selfhost/guji2c_launcher.sh" "$launcher" \
  || fail_setup "cannot stage the compiler launcher"
chmod 0755 "$launcher" || fail_setup "cannot set compiler launcher mode"

echo "build-toolchain: reproducing the self-hosted compiler"
CANDIDATE_OUT="$compiler" bash "$REPO_ROOT/selfhost/bootstrap.sh"
[ -x "$compiler" ] || fail_setup "bootstrap did not produce the compiler"

echo "build-toolchain: compiling the interpreter"
timeout "${INTERPRETER_BUILD_TIMEOUT:-20m}" \
  "$launcher" "$EVAL_DRIVER" "$interpreter" "$PROLOGUE"
[ -x "$interpreter" ] || fail_setup "compiler did not produce the interpreter"

chmod 0755 "$compiler" "$interpreter" \
  || fail_setup "cannot set executable modes"

sha256sum "$launcher" | cut -d' ' -f1 >"$stage/guji2c.sha256"
sha256sum "$compiler" | cut -d' ' -f1 >"$stage/guji2c.bin.sha256"
sha256sum "$interpreter" | cut -d' ' -f1 >"$stage/guji.sha256"

publish_file() {
  local source="$1" name="$2" mode="$3" temporary
  temporary="$OUT_DIR/.$name.tmp.$$"
  cp "$source" "$temporary" \
    && chmod "$mode" "$temporary" \
    && mv -f "$temporary" "$OUT_DIR/$name"
}

mkdir -p "$OUT_DIR" || fail_setup "cannot create output directory: $OUT_DIR"
publish_file "$launcher" guji2c 0755 || fail_setup "cannot write compiler launcher"
publish_file "$compiler" guji2c.bin 0755 || fail_setup "cannot write compiler"
publish_file "$interpreter" guji 0755 || fail_setup "cannot write interpreter"
publish_file "$stage/guji2c.sha256" guji2c.sha256 0644 \
  || fail_setup "cannot write launcher checksum"
publish_file "$stage/guji2c.bin.sha256" guji2c.bin.sha256 0644 \
  || fail_setup "cannot write compiler checksum"
publish_file "$stage/guji.sha256" guji.sha256 0644 \
  || fail_setup "cannot write interpreter checksum"

echo "build-toolchain: compiler and interpreter written to $OUT_DIR"
