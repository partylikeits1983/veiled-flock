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

# Run one test by exact name, whether or not it is #[ignore]d (--include-ignored
# covers both, so the runner does not have to track which is which).
run() {
  local pkg="$1" testbin="$2" name="$3"
  echo "=== $pkg :: $testbin :: $name ==="
  local t0=$SECONDS
  if [ "$testbin" = "--lib" ]; then
    cargo test --release -p "$pkg" --features zk --lib "$name" -- --include-ignored --exact --nocapture
  else
    cargo test --release -p "$pkg" --features zk --test "$testbin" "$name" -- --include-ignored --exact --nocapture
  fi
  echo "$pkg::$testbin::$name ok $((SECONDS - t0))s" >> "$MANIFEST"
}

# --- Exact image-coverage certificates (toy-real fixture, m=15) -------------
run flock-prover zk_leakage_certificate affine_classes_exactly_covered
run flock-prover zk_leakage_certificate full_conditional_coverage_zk_zerocheck
run flock-prover zk_leakage_certificate conditional_coverage_p_rho

# --- Joint triangular certificate: H1, coverage, negative controls ---------
# The non-ignored tests here are the round-pair-class certificate and the
# controls that make it non-vacuous; they run in the normal suite too and are
# repeated here so one command reproduces the whole evidence set.
run flock-prover zk_joint_certificate h1_inner_image_witness_independent_on_round_block
run flock-prover zk_joint_certificate p_channel_image_requires_nondegenerate_q
run flock-prover zk_joint_certificate joint_certificate_smoke
run flock-prover zk_joint_certificate joint_certificate_negative_controls
run flock-prover zk_joint_certificate mask_only_coordinates_are_witness_independent

# --- Complete-transcript joint certificate (the heavy one) -----------------
echo "=== flock-prover :: zk_joint_certificate :: joint_conditional_coverage_full_transcript ==="
t0=$SECONDS
if cargo test --release -p flock-prover --features zk --test zk_joint_certificate \
     joint_conditional_coverage_full_transcript -- --ignored --exact --nocapture; then
  echo "flock-prover::zk_joint_certificate::joint_conditional_coverage_full_transcript ok $((SECONDS - t0))s" >> "$MANIFEST"
else
  echo "flock-prover::zk_joint_certificate::joint_conditional_coverage_full_transcript FAILED $((SECONDS - t0))s" >> "$MANIFEST"
  echo "  ^ REGRESSION: this certificate passes at the recorded fixture" >> "$MANIFEST"
fi

# --- Simulator: existence and constructive translation exactness -----------
run flock-prover zk_simulator simulator_translation_exact_transcript_equality
run flock-prover zk_simulator simulator_produces_accepting_proof_without_a_witness

# --- Production-configuration measurements (m=22) --------------------------
run flock-prover zk_production_config production_mask_channel_covers_round_block
run flock-prover zk_production_config production_s_hat_v_randomizer_margin
run flock-prover zk_production_config production_checked_prove_verifies
run flock-prover zk_production_config blake3_witness_has_no_linear_difference_family
run flock-prover zk_production_config l3_round1_region_alignment_holds

# --- End-to-end A1' reference path on real 256-block BLAKE3 (m=22) ----------
run flock-prover --lib prove_verify_r1cs_zk_a1_roundtrip
run flock-prover --lib prove_fast_zk_ligerito_roundtrip

echo
echo "=== manifest ==="
cat "$MANIFEST"
