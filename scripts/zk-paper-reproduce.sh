#!/bin/bash
# Reproduce the executable certificates and the performance measurements cited
# by the Flock-ZK paper. The benchmark remains hardware-dependent; its output
# prints the machine, compiler, flags, commit, medians, MADs, and ranges.
set -euo pipefail
cd "$(dirname "$0")/.."

scripts/zk-certify.sh
ZK_BENCH_RUNS="${ZK_BENCH_RUNS:-20}" \
  ZK_BENCH_THREADS="${ZK_BENCH_THREADS:-12}" \
  scripts/zk-benchmark.sh
