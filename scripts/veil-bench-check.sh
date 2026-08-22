#!/bin/bash
# Stable-environment smoke guard for catastrophic succinct VEIL regressions.
set -euo pipefail
cd "$(dirname "$0")/.."

batch=${VEIL_BENCH_BATCH:-256}
runs=${VEIL_BENCH_RUNS:-5}
max_prove=${VEIL_BENCH_MAX_PROVE_OVERHEAD:-3.5}
max_verify=${VEIL_BENCH_MAX_VERIFY_OVERHEAD:-3.5}
max_size=${VEIL_BENCH_MAX_SIZE_OVERHEAD:-2.5}

output=$(mktemp)
trap 'rm -f "$output"' EXIT
VEIL_BENCH_BATCH="$batch" VEIL_BENCH_RUNS="$runs" \
  cargo bench -p flock-prover --features veil --bench veil_vs_flock 2>&1 | tee "$output"

overheads=$(awk -F '\t' '$1 == "overhead" { print $2, $3, $4 }' "$output" | tail -1)
if [ -z "$overheads" ]; then
  echo 'ERROR: benchmark did not report an overhead row' >&2
  exit 1
fi
read -r prove verify size <<< "$overheads"
prove=${prove%x}
verify=${verify%x}
size=${size%x}

check() {
  local label="$1" actual="$2" limit="$3"
  if ! awk -v actual="$actual" -v limit="$limit" 'BEGIN { exit !(actual <= limit) }'; then
    printf 'ERROR: %s overhead %sx exceeds %sx\n' "$label" "$actual" "$limit" >&2
    return 1
  fi
  printf '%s overhead %sx <= %sx\n' "$label" "$actual" "$limit"
}

check prover "$prove" "$max_prove"
check verifier "$verify" "$max_verify"
check proof-size "$size" "$max_size"
