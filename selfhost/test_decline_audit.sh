#!/usr/bin/env bash
# Focused contract tests for decline_audit.sh using fake canonical engines.

set -uo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
AUDIT="$REPO_ROOT/selfhost/decline_audit.sh"
CORPUS="$REPO_ROOT/selfhost/audit_corpus"
PROLOGUE="$REPO_ROOT/selfhost/rt/runtime_prologue.c"

tmp="$(mktemp -d)" || exit 2
trap 'rm -rf "$tmp"' EXIT

cat >"$tmp/guji" <<'EOF'
#!/usr/bin/env bash
name="${1##*/}"
if [ "${FAKE_MODE:-pass}" = d_error ] \
    && [ "$name" = carrier_list_bound.guji ]; then
  echo "panic: shared failure" >&2
  exit 1
fi
if [ "${FAKE_MODE:-pass}" = shared_signal ] \
    && [ "$name" = carrier_list_bound.guji ]; then
  kill -SEGV "$$"
fi
printf '%s\n' "$name"
[ "$name" != enum_match_inline.guji ] || exit 7
EOF

cat >"$tmp/guji2c" <<'EOF'
#!/usr/bin/env bash
src="$1"
out="$2"
name="${src##*/}"
if [ "$name" = carrier_list_bound.guji ]; then
  case "${FAKE_MODE:-pass}" in
    decline) exit 4 ;;
    reject) exit 1 ;;
    error) exit 9 ;;
  esac
fi
{
  echo '#!/usr/bin/env bash'
  if [ "${FAKE_MODE:-pass}" = mismatch ] \
      && [ "$name" = carrier_list_bound.guji ]; then
    printf 'printf '\''%%s\\n'\'' %q\n' "wrong-$name"
  elif [ "${FAKE_MODE:-pass}" = shared_signal ] \
      && [ "$name" = carrier_list_bound.guji ]; then
    echo 'kill -SEGV "$$"'
  else
    printf 'printf '\''%%s\\n'\'' %q\n' "$name"
  fi
  if [ "$name" = enum_match_inline.guji ]; then
    echo 'exit 7'
  fi
} >"$out"
chmod 0755 "$out"
EOF
chmod 0755 "$tmp/guji" "$tmp/guji2c"

tests=0

expect() {
  local label="$1" expected_rc="$2" expected_text="$3"
  shift 3
  local output rc
  output="$("$@" 2>&1)"
  rc=$?
  if [ "$rc" -ne "$expected_rc" ] || ! grep -Fq -- "$expected_text" <<<"$output"; then
    echo "FAIL $label (expected rc=$expected_rc and '$expected_text', got rc=$rc)"
    printf '%s\n' "$output" | sed 's/^/  /'
    exit 1
  fi
  echo "PASS $label"
  tests=$((tests + 1))
}

common=(
  env
  "GUJI=$tmp/guji"
  "GUJI2C=$tmp/guji2c"
  "PROLOGUE=$PROLOGUE"
  "PROG_TIMEOUT=5"
  "COMPILE_TIMEOUT=5"
)

expect "explicit engines" 2 \
  "decline-audit SETUP: set GUJI=<canonical native Guji interpreter>" \
  env -u GUJI -u GUJI2C bash "$AUDIT" "$CORPUS"

mkdir "$tmp/drift"
cp "$CORPUS"/*.guji "$tmp/drift/"
: >"$tmp/drift/unratcheted.guji"
expect "corpus ratchet" 2 \
  "historical audit corpus does not match the pinned inventory" \
  "${common[@]}" bash "$AUDIT" "$tmp/drift"

expect "exact pass" 0 \
  "-- canonical decline audit: 26 pinned cases, 26 exact, 0 failed --" \
  "${common[@]}" bash "$AUDIT" "$CORPUS"
expect "compiler decline" 1 "C-DECLINE    carrier_list_bound.guji" \
  env FAKE_MODE=decline "${common[@]:1}" bash "$AUDIT" "$CORPUS"
expect "compiler reject" 1 "C-REJECT     carrier_list_bound.guji" \
  env FAKE_MODE=reject "${common[@]:1}" bash "$AUDIT" "$CORPUS"
expect "compiler error" 1 "C-ERROR      carrier_list_bound.guji" \
  env FAKE_MODE=error "${common[@]:1}" bash "$AUDIT" "$CORPUS"
expect "interpreter failure" 1 "D-ERROR      carrier_list_bound.guji" \
  env FAKE_MODE=d_error "${common[@]:1}" bash "$AUDIT" "$CORPUS"
expect "behavior mismatch" 1 "MISMATCH     carrier_list_bound.guji" \
  env FAKE_MODE=mismatch "${common[@]:1}" bash "$AUDIT" "$CORPUS"
expect "shared runtime signal" 1 "infrastructure status (rc=139)" \
  env FAKE_MODE=shared_signal "${common[@]:1}" bash "$AUDIT" "$CORPUS"

echo "-- decline audit contract: $tests/$tests passed --"
