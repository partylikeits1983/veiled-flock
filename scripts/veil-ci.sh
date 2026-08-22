#!/bin/bash
# Exact, non-vacuous regression manifest for the active succinct VEIL path.
set -euo pipefail
cd "$(dirname "$0")/.."

run() {
  local package="$1" test_bin="$2" features="$3" test_name="$4"
  local target=(--test "$test_bin") feature_args=()
  if [ "$test_bin" = "--lib" ]; then
    target=(--lib)
  fi
  if [ "$features" != "-" ]; then
    feature_args=(--features "$features")
  fi

  local output
  output=$(mktemp)
  trap 'rm -f "$output"' RETURN
  printf '=== %s::%s::%s ===\n' "$package" "$test_bin" "$test_name"
  cargo test --release -p "$package" "${feature_args[@]}" \
    "${target[@]}" "$test_name" -- --exact --nocapture 2>&1 | tee "$output"
  if ! grep -Eq '(^|[[:space:]])1 passed' "$output"; then
    printf "ERROR: '%s' did not run exactly one passing test\n" "$test_name" >&2
    return 1
  fi
  rm -f "$output"
  trap - RETURN
}

# Native VEIL algebra, code, padding, and mutation checks.
run veil-f128 --lib - code::tests::product_code_is_multiplicative_and_reduces_pointwise
run veil-f128 --lib - code::tests::every_two_queries_are_masked_by_two_padding_symbols_in_tiny_code
run veil-f128 --lib - block_r1cs::tests::characteristic_two_six_value_padding_map_is_invertible
run veil-f128 --lib - dot_product::tests::dot_product_proof_rejects_claim_and_opening_mutations
run veil-f128 --lib - hadamard::tests::false_hadamard_relation_is_rejected
run veil-f128 --lib - constraints::tests::shifted_circuit_proves_and_verifies
run veil-f128 --lib - constraints::tests::unsatisfied_shifted_circuit_is_not_provable

# Active fixed-digest composition: completeness, tamper rejection, fresh
# transcript masks, and an accepting public-input-only ROM simulator.
run flock-prover --lib veil r1cs_hashes::blake3_preimage::tests::succinct_veil_preimage_roundtrip_and_mutations
run flock-prover --lib veil r1cs_hashes::blake3_preimage::tests::succinct_output_claims_move_with_fresh_randomizers
run flock-prover --lib veil r1cs_hashes::blake3_preimage::tests::succinct_veil_public_only_simulator_is_accepted

# Extractor regression checks. These exercise the generic recording-oracle
# extractor and the older A1 commitment path. They do not yet constitute an
# extractor theorem for the active succinct composition.
run flock-prover --lib zk preimage_extractor::tests::recorded_leaf_queries_reconstruct_committed_message
run flock-prover preimage_zk_certificate zk extractor_recovers_the_preimages_from_an_honest_commitment
run flock-prover preimage_zk_certificate zk extraction_fails_on_the_simulators_commitment
