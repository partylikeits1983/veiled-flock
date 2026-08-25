#!/bin/bash
# Reproduce the executable certificates for the sole VEIL-FLOCK full-ZK path.
set -euo pipefail
cd "$(dirname "$0")/.."

MANIFEST=zk-certify-manifest.txt
: > "$MANIFEST"

run() {
  local label="$1"
  shift
  printf '=== %s ===\n' "$label"
  if "$@"; then
    printf '%s ok\n' "$label" >> "$MANIFEST"
  else
    printf '%s FAILED\n' "$label" >> "$MANIFEST"
    return 1
  fi
}

run core cargo test --release -p flock-core --features zk,symbolic --tests
run veil cargo test --release -p veil-f128 --lib
run prover cargo test --release -p flock-prover --features veil --lib --bins --tests

# Every production SHA-256 invocation must pass through the reviewed random-
# oracle implementations. Circuit modules and comments are excluded.
if rg -n 'use sha2::|sha2::compress|Sha256::digest|Sha256::new' \
     crates/flock-core/src crates/flock-prover/src --glob '*.rs' \
     | rg -v 'crates/flock-core/src/(ro|challenger)\.rs'; then
  echo 'ERROR: direct SHA-256 call outside ro.rs/challenger.rs' >&2
  exit 1
fi

# No superseded protocol labels, proof types, or versioned domains may return.
if rg -n 'R1csProofZkA1|prove_r1cs_zk_a1|verify_r1cs_zk_a1|veil-flock[^" ]*-v[0-9]' \
     crates docs SPEC.md README.md; then
  echo 'ERROR: superseded or versioned ZK surface found' >&2
  exit 1
fi

printf '\n=== manifest ===\n'
cat "$MANIFEST"
