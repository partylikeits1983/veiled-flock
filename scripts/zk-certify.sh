#!/bin/bash
# Run the offline exact ZK certificates and the m=22 end-to-end A1' gates.
#
# This script is the single source of truth for what counts as certificate
# evidence: every test it runs is recorded in zk-certify-manifest.txt, and a
# unit test asserts that the ZkCertificate registry's `evidence` field lists
# exactly these names (see crates/flock-prover/src/zk_certificate.rs).
#
# Contract (any violation is a non-zero exit — there is no advisory mode):
#   - a failing test, INCLUDING the heavy flagship certificate, aborts the
#     script with a non-zero status after recording FAILED in the manifest;
#   - a test filter that matches zero tests is an error, not a pass: `run`
#     asserts at least one test actually executed, so a renamed or moved
#     test cannot turn a gate vacuous (lib tests must be named by their
#     full module path — bare names silently match nothing under --exact);
#   - on abort, the (incomplete) manifest is printed so the failure is
#     visible in the artifact, not only in the scrollback.
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

on_err() {
  local status=$?
  echo
  echo "=== manifest (INCOMPLETE — aborted with status $status) ==="
  cat "$MANIFEST"
  exit "$status"
}
trap on_err ERR

# Run one test by exact name, whether or not it is #[ignore]d (--include-ignored
# covers both, so the runner does not have to track which is which). The name
# must be the full libtest path (module::path::test_name for --lib tests).
# Fails if the test fails OR if the filter matched no tests at all.
# Optional 4th arg: a manifest tag appended to the recorded name.
run() {
  local pkg="$1" testbin="$2" name="$3" tag="${4:-}"
  local label="$pkg::$testbin::$name$tag"
  echo "=== $pkg :: $testbin :: $name$tag ==="
  local t0=$SECONDS
  local out
  out=$(mktemp)
  local target=(--test "$testbin")
  if [ "$testbin" = "--lib" ]; then
    target=(--lib)
  fi
  if ! cargo test --release -p "$pkg" --features zk "${target[@]}" "$name" \
       -- --include-ignored --exact --nocapture 2>&1 | tee "$out"; then
    echo "$label FAILED $((SECONDS - t0))s" >> "$MANIFEST"
    rm -f "$out"
    return 1
  fi
  local passed
  passed=$(grep -Eo '[0-9]+ passed' "$out" | tail -1 | grep -Eo '[0-9]+' || true)
  rm -f "$out"
  if [ "${passed:-0}" -lt 1 ]; then
    echo "$label VACUOUS: filter matched 0 tests $((SECONDS - t0))s" >> "$MANIFEST"
    echo "ERROR: '$name' matched no tests in $pkg $testbin — the gate would be vacuous" >&2
    return 1
  fi
  echo "$label ok $((SECONDS - t0))s" >> "$MANIFEST"
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
run flock-prover zk_joint_certificate mask_reuse_across_proofs_is_a_leak
run flock-prover zk_joint_certificate mask_only_coordinates_are_witness_independent

# --- Complete-transcript joint certificate (the heavy one) -----------------
# A failure here is a certificate regression and MUST fail the pipeline: this
# is the flagship result the registry's evidence list vouches for.
run flock-prover zk_joint_certificate joint_conditional_coverage_full_transcript

# --- Real-statement coverage certificate (m=20, ~15 min per class scope) ----
# The per-class scopes are kept alongside the unrestricted run because they
# are what localized the two gaps A2 and A3 closed; a regression in one of
# them says *where* something broke, not just that it did.
for classes in lincheck zerocheck piop; do
  ZK_BLAKE3_CLASSES=$classes \
    run flock-prover zk_blake3_certificate blake3_witness_difference_lies_in_the_mask_image "[$classes]"
done
run flock-prover zk_blake3_certificate control_same_procedure_on_the_passing_fixture

# --- Simulator: existence and constructive translation exactness -----------
run flock-prover zk_simulator simulator_translation_exact_transcript_equality
run flock-prover zk_simulator simulator_produces_accepting_proof_without_a_witness

# --- Production-configuration measurements (m=22) --------------------------
run flock-prover zk_production_config production_mask_channel_covers_round_block
run flock-prover zk_production_config production_s_hat_v_randomizer_margin
run flock-prover zk_production_config production_checked_prove_verifies
run flock-prover zk_production_config blake3_witness_has_no_linear_difference_family
run flock-prover zk_production_config l3_round1_region_alignment_holds

# --- PCS-layer rank audit (m=13) + its negative control --------------------
# The joint certificate's mask-only conditioning cites this audit for the
# mu/g layer; it is evidence and runs here like everything else it vouches for.
run flock-core --lib pcs::zk_audit::pcs_rank_audit_witness_image_covered
run flock-core --lib pcs::zk_audit::pcs_rank_audit_negative_control_without_g

# --- Amendment completeness at the zerocheck layer (A3 staged roundtrip) ---
run flock-core --lib zerocheck::tests::prove_verify_zk_round1_mask_roundtrip

# --- End-to-end A1' reference path on real 256-block BLAKE3 (m=22) ----------
run flock-prover --lib r1cs_hashes::blake3::tests::prove_verify_r1cs_zk_a1_roundtrip
run flock-prover --lib r1cs_hashes::blake3::tests::prove_fast_zk_ligerito_roundtrip

echo
echo "=== manifest ==="
cat "$MANIFEST"
