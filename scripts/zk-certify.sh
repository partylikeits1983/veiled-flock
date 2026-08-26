#!/bin/bash
# Reproduce every executable artifact behind the exact Flock ZK registry.
# A failed, missing, or vacuously filtered test aborts and leaves CERTIFIED
# unsupported. Run from any directory; stable Rust is pinned by the worktree.
set -euo pipefail
cd "$(dirname "$0")/.."

MANIFEST=zk-certify-manifest.txt
: > "$MANIFEST"

on_err() {
  local status=$?
  printf '\n=== manifest (INCOMPLETE, status %s) ===\n' "$status"
  cat "$MANIFEST"
  exit "$status"
}
trap on_err ERR

run() {
  local pkg="$1" testbin="$2" name="$3"
  local label="$pkg::$testbin::$name"
  printf '=== %s ===\n' "$label"
  local t0=$SECONDS out passed
  out=$(mktemp)
  local target=(--test "$testbin")
  if [ "$testbin" = "--lib" ]; then
    target=(--lib)
  fi
  if ! cargo test --release -p "$pkg" --features zk,symbolic \
       "${target[@]}" "$name" -- --include-ignored --exact --nocapture 2>&1 | tee "$out"; then
    printf '%s FAILED %ss\n' "$label" "$((SECONDS - t0))" >> "$MANIFEST"
    rm -f "$out"
    return 1
  fi
  passed=$(grep -Eo '[0-9]+ passed' "$out" | tail -1 | grep -Eo '[0-9]+' || true)
  rm -f "$out"
  if [ "${passed:-0}" -lt 1 ]; then
    printf '%s VACUOUS %ss\n' "$label" "$((SECONDS - t0))" >> "$MANIFEST"
    printf "ERROR: '%s' matched no tests in %s %s\n" "$name" "$pkg" "$testbin" >&2
    return 1
  fi
  printf '%s ok %ss\n' "$label" "$((SECONDS - t0))" >> "$MANIFEST"
}

# Framed random oracle, nonce/domain separation, and SIMD parity.
run flock-core --lib ro::tests::native_tree_hasher_matches_one_shot_reference
run flock-core --lib ro::tests::external_backend_reproduces_native_digests_and_records
run flock-core --lib merkle::tests::tree_root_separates_nonce_channel_depth_level_index
run flock-core --lib merkle::tests::external_framed_tree_matches_native_and_records_every_node
run flock-core --lib merkle::tests::framed_midstate_simd_matches_scalar_all_tail_shapes

# Generic symbolic kernels, exact S2 coverage, and the S3 opening translator.
run flock-core symbolic_kernels concrete_symbolic_kernels_match_native_references
run flock-core symbolic_kernels toy_exact_polynomials_match_evaluation_and_degree_semantics
run flock-core symbolic_kernels challenge_dependent_inversion_is_not_part_of_sym_scalar
run flock-core symbolic_mask_coverage symbolic_mask_matrix_matches_native_and_has_100_bit_margin
run flock-core symbolic_pcs_translator closed_form_translation_preserves_open_rows_and_combined_vector
run flock-core symbolic_pcs_translator structural_l0_rank_certificate_matches_actual_ntt_on_every_small_query_set
run flock-core symbolic_pcs_translator l0_entropy_counting_gate_holds_for_fixture_and_production

# Public affine Q-star parity/rank and exhaustive transcript schema.
run flock-prover zk_qstar_rank qstar_functional_matrix_matches_dense_schedule
run flock-prover zk_qstar_rank affine_linear_qstar_has_full_conditioned_rank_across_certified_shapes
run flock-prover zk_transcript_schema a1_schema_manifest_and_bijectivity
run flock-prover zk_transcript_schema a1_schema_matches_wire_order
run flock-prover --lib sim_oracle::tests::oracle_pow_state_digest_is_an_oracle_query

# Game ledger, recording extractor, and fresh-prefix weak sim-extractability.
run flock-prover --lib sim_game::tests::game_hops_are_complete_and_ordered
run flock-prover --lib sim_game::tests::production_ledger_exposes_recursive_sibling_gate_at_q64
run flock-prover --lib preimage_extractor::tests::recorded_leaf_queries_reconstruct_committed_message
run flock-prover --lib sim_ext::tests::prefix_diverges_on_statement_nonce_and_protocol_tuple
run flock-prover --lib sim_ext::tests::simulated_prefix_is_rejected_and_fresh_prefix_reaches_extractor

# Fixed-digest production relation: non-vacuous rank, public binding,
# extraction, sealed simulation, and honest/simulated separation.
run flock-prover preimage_zk_certificate field_mask_spans_conditioned_round_block_for_fixed_digest
run flock-prover preimage_zk_certificate undersized_mask_does_not_span_the_round_block
run flock-prover preimage_zk_certificate the_digest_claim_is_a_public_function_of_the_statement
run flock-prover preimage_zk_certificate fixed_digest_circuit_is_not_the_batch_circuit
run flock-prover preimage_zk_certificate extractor_recovers_the_preimages_from_an_honest_commitment
run flock-prover preimage_zk_certificate extraction_fails_on_the_simulators_commitment
run flock-prover --lib r1cs_hashes::blake3_preimage::tests::simulator_produces_an_accepting_proof_without_any_preimage
run flock-prover --lib r1cs_hashes::blake3_preimage::tests::production_random_oracle_ledger_matches_artifact
run flock-prover --lib r1cs_hashes::blake3_preimage::tests::honest_prover_on_the_patched_vector_is_rejected
run flock-prover --lib r1cs_hashes::blake3_preimage::tests::zk_preimage_roundtrip

# Registered batch profile remains live under the same protocol identifier.
run flock-prover --lib r1cs_hashes::blake3::tests::prove_verify_r1cs_zk_a1_roundtrip

# Machine-checked bound adapters and the dual-column knowledge ledger.
(cd lean && lake build)
python3 scripts/knowledge-ledger.py --check docs/artifacts/knowledge-ledger.json

# All production SHA-256 invocations must pass through the two reviewed RO
# implementations. Names of SHA circuits and comments are intentionally not
# matched here.
if rg -n 'use sha2::|sha2::compress|Sha256::digest|Sha256::new' \
     crates/flock-core/src crates/flock-prover/src --glob '*.rs' \
     | rg -v 'crates/flock-core/src/(ro|challenger)\.rs'; then
  echo 'ERROR: direct SHA-256 call outside ro.rs/challenger.rs' >&2
  exit 1
fi

printf '\n=== manifest ===\n'
cat "$MANIFEST"
