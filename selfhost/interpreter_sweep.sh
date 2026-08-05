#!/usr/bin/env bash
# Measure canonical interpreter (D) coverage against canonical compiler (C)
# across the accepted 975-program compiler surface. The report is also fail-closed:
# any semantic mismatch or compiler decline makes the sweep fail.

set -uo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
FIX_DIR="$REPO_ROOT/tests/compile"
CONC_DIR="$FIX_DIR/concurrency"
CORPUS_DIR="$REPO_ROOT/selfhost/compile_corpus"
PARITY_DIR="$REPO_ROOT/selfhost/parity_corpus"
PROLOGUE="$REPO_ROOT/selfhost/rt/runtime_prologue.c"
SCOPE="${SCOPE:-gate,corpus,parity}"
LIMIT="${LIMIT:-0}"
VERBOSE="${VERBOSE:-0}"
PROG_TIMEOUT="${PROG_TIMEOUT:-120}"
REPORT="${REPORT:-$REPO_ROOT/selfhost/INTERPRETER_BASELINE.md}"
EXPECTED_TOTAL="${EXPECTED_TOTAL:-}"
EXPECTED_SURFACE_SHA256="${EXPECTED_SURFACE_SHA256:-}"
CANONICAL_SURFACE_SHA256="3917b9e155707b3e1a0e2f9b63bca76bc8730a097a75ea0ca6db4a64e5640a0b"

GUJI2C="${GUJI2C:-}"
GUJI="${GUJI:-}"

fail_setup() {
  echo "interpreter-sweep SETUP: $*"
  exit 2
}

want() { case ",$SCOPE," in *",$1,"*) return 0 ;; *) return 1 ;; esac; }

[ -x "$GUJI2C" ] || fail_setup "set GUJI2C to native canonical compiler"
[ -x "$GUJI" ] || fail_setup "set GUJI to native canonical interpreter"
[ -f "$PROLOGUE" ] || fail_setup "runtime prologue missing: $PROLOGUE"
[[ "$LIMIT" =~ ^[0-9]+$ ]] || fail_setup "LIMIT must be a nonnegative integer"
[[ "$PROG_TIMEOUT" =~ ^[1-9][0-9]*$ ]] \
  || fail_setup "PROG_TIMEOUT must be a positive integer"
[[ "$VERBOSE" =~ ^[01]$ ]] || fail_setup "VERBOSE must be 0 or 1"
if [ -n "$EXPECTED_TOTAL" ]; then
  [[ "$EXPECTED_TOTAL" =~ ^[1-9][0-9]*$ ]] \
    || fail_setup "EXPECTED_TOTAL must be a positive integer"
fi
if [ -n "$EXPECTED_SURFACE_SHA256" ]; then
  [[ "$EXPECTED_SURFACE_SHA256" =~ ^[0-9a-f]{64}$ ]] \
    || fail_setup "EXPECTED_SURFACE_SHA256 must be a lowercase SHA-256"
fi

IFS=',' read -r -a requested_scopes <<<"$SCOPE"
[ "${#requested_scopes[@]}" -gt 0 ] || fail_setup "SCOPE is empty"
seen_scopes=","
for requested_scope in "${requested_scopes[@]}"; do
  case "$requested_scope" in
    gate|corpus|parity) ;;
    *) fail_setup "unknown SCOPE bucket: ${requested_scope:-<empty>}" ;;
  esac
  case "$seen_scopes" in
    *",$requested_scope,"*) fail_setup "duplicate SCOPE bucket: $requested_scope" ;;
  esac
  seen_scopes="$seen_scopes$requested_scope,"
done

if want gate; then
  [ -d "$FIX_DIR" ] || fail_setup "gate fixture directory missing: $FIX_DIR"
  [ -d "$CONC_DIR" ] || fail_setup "concurrency fixture directory missing: $CONC_DIR"
fi
if want corpus; then
  [ -d "$CORPUS_DIR" ] || fail_setup "compiler corpus directory missing: $CORPUS_DIR"
fi
if want parity; then
  [ -d "$PARITY_DIR" ] || fail_setup "parity corpus directory missing: $PARITY_DIR"
fi
[ -d "$(dirname "$REPORT")" ] || fail_setup "report directory missing: $(dirname "$REPORT")"

# The unfiltered canonical acceptance surface is a compatibility ratchet. Its exact
# source-path set is pinned as well as its size, so replacing a hard row with a
# trivial row cannot preserve a green "full" sweep.
if [ -z "$EXPECTED_TOTAL" ] && [ "$SCOPE" = "gate,corpus,parity" ] && [ "$LIMIT" -eq 0 ]; then
  EXPECTED_TOTAL=975
fi
if [ "$SCOPE" = "gate,corpus,parity" ] && [ "$LIMIT" -eq 0 ]; then
  EXPECTED_SURFACE_SHA256="$CANONICAL_SURFACE_SHA256"
fi

tmp="$(mktemp -d)" || exit 2
trap 'rm -rf "$tmp"' EXIT
: >"$tmp/rows"
shopt -s nullglob

sidecar_stdin() { [ -f "$1.stdin" ] && printf '%s' "$1.stdin" || printf '%s' /dev/null; }
read_args() { ARGS=(); [ -f "$1.args" ] && mapfile -t ARGS <"$1.args"; }

is_infrastructure_status() {
  local rc="$1"
  case "$rc" in
    124|125|126|127) return 0 ;;
  esac
  [ "$rc" -ge 129 ] && [ "$rc" -le 192 ]
}

feature_of() {
  case "$1" in
    *regex*) echo "regex" ;;
    *grammar*) echo "grammar" ;;
    *channel*|*select*|*hatch*|concurrency/*|*task*|*spawn*) echo "concurrency" ;;
    *lambda*|*closure*|*func*) echo "lambda" ;;
    *generic*|*carrier*) echo "generics" ;;
    *class*|*method*) echo "classes" ;;
    *enum*|*variant*) echo "enums" ;;
    *option*|*result*|*question*|*try_*) echo "option-result" ;;
    *map*|*list*|*collection*|*filter*|*reduce*|*sort*) echo "collections" ;;
    *import*|*module*|*cross_cycle*) echo "modules" ;;
    *io*|*file*|*run_proc*|*args*|*stdin*) echo "io-process" ;;
    *for*|*loop*|*while*|*range*) echo "control-flow" ;;
    *) echo "core" ;;
  esac
}

bucket_files() {
  local kind="$1" n=0 f d corpus_files
  case "$kind" in
    gate)
      for f in "$FIX_DIR"/*.guji; do
        printf '%s\t%s\t%s\n' "$(basename "$f" .guji)" "$f" "${f%.guji}" || return 2
        n=$((n + 1))
        [ "$LIMIT" -gt 0 ] && [ "$n" -ge "$LIMIT" ] && return 0
      done
      for d in "$FIX_DIR"/*/; do
        [ "$d" = "$CONC_DIR/" ] && continue
        [ -f "$d/main.guji" ] || continue
        printf '%s\t%s\t%s\n' "$(basename "$d")" "$d/main.guji" "$d/main" || return 2
        n=$((n + 1))
        [ "$LIMIT" -gt 0 ] && [ "$n" -ge "$LIMIT" ] && return 0
      done
      for f in "$CONC_DIR"/*.guji; do
        printf '%s\t%s\t%s\n' "concurrency/$(basename "$f" .guji)" "$f" "${f%.guji}" || return 2
        n=$((n + 1))
        [ "$LIMIT" -gt 0 ] && [ "$n" -ge "$LIMIT" ] && return 0
      done
      for d in "$CONC_DIR"/*/; do
        [ -f "$d/main.guji" ] || continue
        printf '%s\t%s\t%s\n' "concurrency/$(basename "$d")" "$d/main.guji" "$d/main" || return 2
        n=$((n + 1))
        [ "$LIMIT" -gt 0 ] && [ "$n" -ge "$LIMIT" ] && return 0
      done ;;
    corpus)
      corpus_files="$(find "$CORPUS_DIR" -name '*.guji' -print | LC_ALL=C sort)" \
        || return 2
      while IFS= read -r f; do
        [ -n "$f" ] || continue
        printf '%s\t%s\t%s\n' "corpus/${f#$CORPUS_DIR/}" "$f" "${f%.guji}" || return 2
        n=$((n + 1))
        [ "$LIMIT" -gt 0 ] && [ "$n" -ge "$LIMIT" ] && return 0
      done <<<"$corpus_files" ;;
    parity)
      for f in "$PARITY_DIR"/*.guji; do
        printf '%s\t%s\t%s\n' "parity/$(basename "$f" .guji)" "$f" "${f%.guji}" || return 2
        n=$((n + 1))
        [ "$LIMIT" -gt 0 ] && [ "$n" -ge "$LIMIT" ] && return 0
      done ;;
  esac
  return 0
}

candidate_rows="$tmp/candidate-rows"
: >"$candidate_rows" || fail_setup "cannot create acceptance-surface inventory"
for bucket in gate corpus parity; do
  want "$bucket" || continue
  bucket_files "$bucket" >>"$candidate_rows" \
    || fail_setup "cannot enumerate $bucket acceptance rows"
done

if [ -n "$EXPECTED_SURFACE_SHA256" ]; then
  cut -f2 "$candidate_rows" \
    | sed "s#^$REPO_ROOT/##" \
    | LC_ALL=C sort -u >"$tmp/surface-inventory" \
    || fail_setup "cannot enumerate acceptance-surface inventory"
  inventory_hash="$(sha256sum "$tmp/surface-inventory" | cut -d' ' -f1)" \
    || fail_setup "cannot hash acceptance-surface inventory"
  [ "$inventory_hash" = "$EXPECTED_SURFACE_SHA256" ] \
    || fail_setup "acceptance-surface inventory hash mismatch: expected $EXPECTED_SURFACE_SHA256, found $inventory_hash"
fi

classify() {
  local label="$1" src="$2" base="$3" feat rundir stdin_file d_rc c_rc build_rc detail
  local expected_out="" expected_err="" expected_rc="" pin_detail=""
  feat="$(feature_of "$label")"
  rundir="$(dirname "$src")"
  stdin_file="$(sidecar_stdin "$base")"
  read_args "$base"
  if [ -f "$base.out" ]; then
    expected_out="$base.out"
  elif [ -f "$base.expected" ]; then
    expected_out="$base.expected"
  fi
  [ ! -f "$base.stderr" ] || expected_err="$base.stderr"
  if [ -f "$base.exit" ]; then
    expected_rc="$(tr -d '[:space:]' <"$base.exit")"
    [[ "$expected_rc" =~ ^[0-9]+$ ]] \
      || fail_setup "malformed expected exit status: $base.exit"
    if is_infrastructure_status "$expected_rc"; then
      fail_setup "expected exit status is reserved for infrastructure failures: $base.exit ($expected_rc)"
    fi
  fi

  (cd "$rundir" && timeout "$PROG_TIMEOUT" "$GUJI" "$src" "${ARGS[@]}") \
    <"$stdin_file" >"$tmp/d.out" 2>"$tmp/d.err"
  d_rc=$?

  rm -f "$tmp/program" "$tmp/program.c" \
    || fail_setup "cannot clear per-row compiler artifacts"
  timeout "$PROG_TIMEOUT" "$GUJI2C" "$src" "$tmp/program" "$PROLOGUE" \
    >"$tmp/build.out" 2>"$tmp/build.err"
  build_rc=$?
  if [ "$build_rc" -ne 0 ] || [ ! -x "$tmp/program" ]; then
    if [ "$build_rc" -eq 0 ]; then
      detail="compiler rc=0: fresh executable missing"
    else
      detail="compiler rc=$build_rc: $(head -n 1 "$tmp/build.err" | tr '\t' ' ')"
    fi
    printf 'COMPILER-GAP\t%s\t%s\t%s\n' "$feat" "$label" "$detail" >>"$tmp/rows"
    return
  fi

  (cd "$rundir" && timeout "$PROG_TIMEOUT" "$tmp/program" "${ARGS[@]}") \
    <"$stdin_file" >"$tmp/c.out" 2>"$tmp/c.err"
  c_rc=$?

  if is_infrastructure_status "$d_rc" || is_infrastructure_status "$c_rc"; then
    detail="infrastructure status: D rc=$d_rc C rc=$c_rc"
    printf 'BUG\t%s\t%s\t%s\n' "$feat" "$label" "$detail" >>"$tmp/rows"
    return
  fi

  if [ -n "$expected_out" ]; then
    cmp -s "$expected_out" "$tmp/d.out" && cmp -s "$expected_out" "$tmp/c.out" \
      || pin_detail="${pin_detail:+$pin_detail; }expected stdout"
  fi
  if [ -n "$expected_err" ]; then
    cmp -s "$expected_err" "$tmp/d.err" && cmp -s "$expected_err" "$tmp/c.err" \
      || pin_detail="${pin_detail:+$pin_detail; }expected stderr"
  fi
  if [ -n "$expected_rc" ]; then
    [ "$d_rc" -eq "$expected_rc" ] && [ "$c_rc" -eq "$expected_rc" ] \
      || pin_detail="${pin_detail:+$pin_detail; }expected exit=$expected_rc"
  fi

  if [ "$d_rc" -eq "$c_rc" ] \
      && cmp -s "$tmp/d.out" "$tmp/c.out" \
      && cmp -s "$tmp/d.err" "$tmp/c.err" \
      && [ -z "$pin_detail" ]; then
    printf 'COVERED\t%s\t%s\texit=%s\n' "$feat" "$label" "$d_rc" >>"$tmp/rows"
  elif [ "$d_rc" -eq "$c_rc" ] \
      && cmp -s "$tmp/d.out" "$tmp/c.out" \
      && cmp -s "$tmp/d.err" "$tmp/c.err"; then
    printf 'BUG\t%s\t%s\t%s\n' "$feat" "$label" "$pin_detail" >>"$tmp/rows"
  elif [ "$d_rc" -ne 0 ] && [ "$c_rc" -eq 0 ]; then
    detail="D rc=$d_rc: $(head -n 1 "$tmp/d.err" | tr '\t' ' ')"
    printf 'GAP\t%s\t%s\t%s\n' "$feat" "$label" "$detail" >>"$tmp/rows"
  else
    detail="D rc=$d_rc C rc=$c_rc"
    cmp -s "$tmp/d.out" "$tmp/c.out" || detail="$detail; stdout"
    cmp -s "$tmp/d.err" "$tmp/c.err" || detail="$detail; stderr"
    printf 'BUG\t%s\t%s\t%s\n' "$feat" "$label" "$detail" >>"$tmp/rows"
  fi
}

count=0
echo "-- canonical interpreter sweep (SCOPE=$SCOPE) --"
while IFS=$'\t' read -r label src base; do
  [ -n "$src" ] || continue
  classify "$label" "$src" "$base"
  count=$((count + 1))
  [ $((count % 25)) -eq 0 ] && echo "  $count programs classified" >&2
done <"$candidate_rows"

n_covered="$(grep -c '^COVERED' "$tmp/rows" || true)"
n_gap="$(grep -c '^GAP' "$tmp/rows" || true)"
n_bug="$(grep -c '^BUG' "$tmp/rows" || true)"
n_cgap="$(grep -c '^COMPILER-GAP' "$tmp/rows" || true)"
n_total="$(wc -l <"$tmp/rows")"

write_report() {
  echo "# Canonical interpreter coverage baseline"
  echo
  echo "SCOPE=$SCOPE total=$n_total"
  echo
  echo "| class | count |"
  echo "|---|---:|"
  echo "| COVERED | $n_covered |"
  echo "| GAP | $n_gap |"
  echo "| BUG | $n_bug |"
  echo "| COMPILER-GAP | $n_cgap |"
  echo
  for class in GAP BUG COMPILER-GAP; do
    n="$(grep -c "^$class" "$tmp/rows" || true)"
    [ "$n" -gt 0 ] || continue
    echo "## $class rows"
    echo
    grep "^$class" "$tmp/rows" | sort -t$'\t' -k2,2 -k3,3 | \
      awk -F'\t' '{print "- **" $2 "** " $3 " (" $4 ")"}'
    echo
  done
  if [ "$VERBOSE" = 1 ]; then
    echo "## Covered rows"
    echo
    grep '^COVERED' "$tmp/rows" | awk -F'\t' '{print "- " $3 " (" $2 ")"}' || true
  fi
  return 0
}

if ! write_report | tee "$REPORT"; then
  fail_setup "cannot write report: $REPORT"
fi

echo "-- interpreter sweep: $n_covered COVERED, $n_gap GAP, $n_bug BUG, $n_cgap COMPILER-GAP (of $n_total) --"
if [ -n "$EXPECTED_TOTAL" ] && [ "$n_total" -ne "$EXPECTED_TOTAL" ]; then
  echo "interpreter-sweep RED: expected $EXPECTED_TOTAL acceptance rows, classified $n_total"
  exit 1
fi
if [ "$n_gap" -ne 0 ] || [ "$n_bug" -ne 0 ] || [ "$n_cgap" -ne 0 ]; then
  exit 1
fi
exit 0
