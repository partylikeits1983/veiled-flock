#!/bin/bash
# Run the offline exact ZK certificates and the m=22 end-to-end A1' gates.
#
# This script is the single source of truth for what counts as certificate
# evidence: every test it runs is recorded in zk-certify-manifest.txt, and a
# unit test asserts that the ZkCertificate registry's `evidence` field lists
# exactly these names (see crates/flock-prover/src/zk_certificate.rs).
#
# These are the tests that are `#[ignore]`d in the normal suite because they
# perform tens of thousands of real prover runs. Expect multiple hours of
# wall time on a 16-core machine.
#
# Usage: scripts/zk-certify.sh   (from the repo root)
set -euo pipefail
cd "$(dirname "$0")/.."

MANIFEST=zk-certify-manifest.txt
: > "$MANIFEST"

run() {
  local pkg="$1" testbin="$2" name="$3"
  echo "=== $pkg :: $testbin :: $name ==="
  local t0=$SECONDS
  if [ "$testbin" = "--lib" ]; then
    cargo test --release -p "$pkg" --features zk --lib "$name" -- --ignored --exact --nocapture
  else
    cargo test --release -p "$pkg" --features zk --test "$testbin" "$name" -- --ignored --exact --nocapture
  fi
  echo "$pkg::$testbin::$name ok $((SECONDS - t0))s" >> "$MANIFEST"
}

# --- Exact image-coverage certificates (toy-real fixture, m=15) -------------
run flock-prover zk_leakage_certificate affine_classes_exactly_covered
run flock-prover zk_leakage_certificate full_conditional_coverage_zk_zerocheck
run flock-prover zk_leakage_certificate conditional_coverage_p_rho

# --- Joint full-transcript certificate + negative controls (fixture A) ------
# (added by the zk_joint_certificate suite as it lands)
if cargo test --release -p flock-prover --features zk --test zk_joint_certificate -- --list > /dev/null 2>&1; then
  echo "=== flock-prover :: zk_joint_certificate (all) ==="
  t0=$SECONDS
  cargo test --release -p flock-prover --features zk --test zk_joint_certificate -- --ignored --nocapture
  echo "flock-prover::zk_joint_certificate::all ok $((SECONDS - t0))s" >> "$MANIFEST"
fi

# --- End-to-end A1' reference path on real 256-block BLAKE3 (m=22) ----------
run flock-prover --lib prove_verify_r1cs_zk_a1_roundtrip
run flock-prover --lib prove_fast_zk_ligerito_roundtrip

echo
echo "=== manifest ==="
cat "$MANIFEST"
