#!/bin/bash
# Compare the registered Flock-ZK prover with current non-ZK Flock and native
# hashing. The reference bench reports medians, MAD, ranges, proof sizes, peak
# incremental heap, commit, compiler, flags, and thread count.
set -euo pipefail
cd "$(dirname "$0")/.."

runs=${ZK_BENCH_RUNS:-10}
threads=${ZK_BENCH_THREADS:-}

if [ -z "$threads" ]; then
  if command -v sysctl >/dev/null 2>&1; then
    threads=$(sysctl -n hw.ncpu 2>/dev/null || true)
  fi
  if [ -z "$threads" ] && command -v nproc >/dev/null 2>&1; then
    threads=$(nproc)
  fi
  threads=${threads:-1}
fi

printf '=== Native scalar hash baseline (one thread) ===\n'
RAYON_NUM_THREADS=1 cargo bench --bench native_hash

printf '\n=== Flock-ZK versus non-ZK Flock (one thread) ===\n'
RAYON_NUM_THREADS=1 ZKA1_NS=256 ZKA1_RUNS="$runs" \
  cargo bench --features zk,symbolic --bench zk_a1_reference

if [ "$threads" -ne 1 ]; then
  printf '\n=== Flock-ZK versus non-ZK Flock (%s threads) ===\n' "$threads"
  RAYON_NUM_THREADS="$threads" ZKA1_NS=256 ZKA1_RUNS="$runs" \
    cargo bench --features zk,symbolic --bench zk_a1_reference
fi
