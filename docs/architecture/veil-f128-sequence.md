# veil-f128 Sequence Diagrams

`veil-f128` is the native GF(2^128) VEIL backend — the zero-knowledge compiler. It takes
a masked FLOCK verifier transcript expressed as an arithmetic circuit and proves the
circuit is satisfied, without revealing the witness. It depends only on `flock-core`
(with `features = ["zk"]`) and re-exports `F128` from it at
`crates/veil-f128/src/lib.rs:32`.

The crate exists because upstream VEIL does not instantiate over this field. VEIL's
Reed-Solomon construction needs a two-adic multiplicative subgroup; GF(2^128) has a
multiplicative group of odd order 2^128 - 1 and therefore has none. `AdditiveRsCode`
supplies the additive-domain construction instead: messages are evaluations on an
additive GF(2) subspace, interpolated and evaluated on a disjoint affine coset, so a
pointwise codeword product lands in a twice-degree square code — exactly what VEIL's
Hadamard reduction needs. See `docs/DECISIONS.md` D002.

Lane pipes hold a fixed column on every row; `*` marks a call that stays inside its own
lane. An arrowhead lands one column short of the receiving lane so no pipe is erased.

## Diagram 1 — masked transcript

Two phases. `commit_constraint_inputs` (messages 1-7) commits before any challenge is
drawn; `prove_constraints_from_commitment` (messages 8-19) runs the reduction against
that commitment. Splitting them is what lets the caller bind the commitment root into an
outer transcript before challenges exist.

Participants:

- `call` = the driver, on the active path `prove_succinct_veil_r1cs`
  `crates/flock-prover/src/succinct_veil.rs:596`
- `cons` = `constraints`
  `crates/veil-f128/src/constraints.rs:418`
- `dot` = `dot_product`
  `crates/veil-f128/src/dot_product.rs:131`
- `had` = `hadamard`
  `crates/veil-f128/src/hadamard.rs:75`
- `code` = `AdditiveRsCode`
  `crates/veil-f128/src/code.rs:95`
- `ntt` = `AdditiveCosetNtt`
  `crates/veil-f128/src/ntt.rs:167`
- `cmt` = `MerkleMatrix`
  `crates/veil-f128/src/commitment.rs:14`
- `CH` = `Challenger` (from flock-core)
  `crates/flock-core/src/challenger.rs:30`

```text
  call  cons  dot   had   code  ntt   cmt   CH
  |     |     |     |     |     |     |     |
  |---->|     |     |     |     |     |     |     1 commit_constraint_inputs
  |     |*    |     |     |     |     |     |     2 parameters.validate + shape checks
  |     |*    |     |     |     |     |     |     3 rng.fill_f128 -> [r, s, t] padding
  |     |---->|     |     |     |     |     |     4 commit_vectors
  |     |     |---------->|     |     |     |     5 encode_batch
  |     |     |     |     |---->|     |     |     6 forward / inverse
  |     |     |---------------------->|     |     7 MerkleMatrix::new
  |<----|     |     |     |     |     |     |     8 ConstraintCommitment
  |---->|     |     |     |     |     |     |     9 prove_constraints_from_commitment
  |     |*    |     |     |     |     |     |     10 padded_circuit + is_satisfied
  |     |---------------------------------->|     11 observe_label + observe_bytes(root)
  |     |*    |     |     |     |     |     |     12 multiplication_vectors
  |     |---------->|     |     |     |     |     13 commit_hadamard
  |     |     |     |---->|     |     |     |     14 encode_square (square code)
  |     |     |     |---------------->|     |     15 MerkleMatrix::new
  |     |---------------------------------->|     16 observe_bytes(hadamard root)
  |     |<----------------------------------|     17 sample_f128 x2 (mult + constraint rlc)
  |     |---------->|     |     |     |     |     18 prove_hadamard_and_dots
  |     |     |     |---------------->|     |     19 MerkleMatrix::open
  |     |---->|     |     |     |     |     |     20 prove_dot_product (linear)
  |     |     |---------------------->|     |     21 MerkleMatrix::open
  |<----|     |     |     |     |     |     |     22 ConstraintProof
```

Anchors:

1. `commit_constraint_inputs`
   `crates/veil-f128/src/constraints.rs:418`
2. `ConstraintParameters::validate`, called at `crates/veil-f128/src/constraints.rs:424`
   `crates/veil-f128/src/constraints.rs:304`
3. `MaskSampler::fill_f128`, called at `crates/veil-f128/src/constraints.rs:441`
   `crates/flock-core/src/zk.rs:36`
4. `commit_vectors` — the unframed entry point
   `crates/veil-f128/src/dot_product.rs:131`
5. `AdditiveRsCode::encode_batch`
   `crates/veil-f128/src/code.rs:144`
6. `AdditiveCosetNtt::forward`
   `crates/veil-f128/src/ntt.rs:196`
7. `MerkleMatrix::new` — not `new_framed`; `commit_vectors` resolves `framed = None`
   `crates/veil-f128/src/commitment.rs:29`
8. `ConstraintCommitment`, constructed at `crates/veil-f128/src/constraints.rs:458`
   `crates/veil-f128/src/constraints.rs:290`
9. `prove_constraints_from_commitment`
   `crates/veil-f128/src/constraints.rs:468`
10. `padded_circuit`, called at `crates/veil-f128/src/constraints.rs:487`, with
    `ArithmeticCircuit::is_satisfied` at `crates/veil-f128/src/constraints.rs:483`
    `crates/veil-f128/src/constraints.rs:596`
11. `Challenger::observe_label` then `Challenger::observe_bytes`, at
    `crates/veil-f128/src/constraints.rs:500`
    `crates/flock-core/src/challenger.rs:34`
12. `multiplication_vectors`
    `crates/veil-f128/src/constraints.rs:631`
13. `commit_hadamard` — the unframed entry point
    `crates/veil-f128/src/hadamard.rs:75`
14. `AdditiveRsCode::encode_square`
    `crates/veil-f128/src/code.rs:162`
15. `MerkleMatrix::new`
    `crates/veil-f128/src/commitment.rs:29`
16. `Challenger::observe_bytes`, at `crates/veil-f128/src/constraints.rs:513`
    `crates/flock-core/src/challenger.rs:49`
17. `Challenger::sample_f128`, twice — `multiplication_rlc` at
    `crates/veil-f128/src/constraints.rs:514` and `constraint_rlc` at
    `crates/veil-f128/src/constraints.rs:522`
    `crates/flock-core/src/challenger.rs:54`
18. `prove_hadamard_and_dots`
    `crates/veil-f128/src/hadamard.rs:151`
19. `MerkleMatrix::open`
    `crates/veil-f128/src/commitment.rs:84`
20. `prove_dot_product`
    `crates/veil-f128/src/dot_product.rs:199`
21. return of message 19 — same definition
    `crates/veil-f128/src/commitment.rs:84`
22. `ConstraintProof`
    `crates/veil-f128/src/constraints.rs:277`

The verifier mirror is `verify_constraints` at
`crates/veil-f128/src/constraints.rs:539`, backed by `verify_hadamard_and_dots_framed`
(`crates/veil-f128/src/hadamard.rs:244`) and `verify_dot_product_framed`
(`crates/veil-f128/src/dot_product.rs:276`). The standalone block-R1CS entry points
`prove_block_r1cs_framed` (`crates/veil-f128/src/block_r1cs.rs:118`) and
`verify_block_r1cs_framed` (`crates/veil-f128/src/block_r1cs.rs:261`) run the same
reduction for a whole block R1CS instance rather than a circuit; the succinct path does
not use them.

## Diagram 2 — simulator

The simulator produces a transcript indistinguishable from a real one **without a
witness**. It is the zero-knowledge argument's evidence, so its call order matters: it
must sample in exactly the order the prover does.

Participants:

- `call` = the driver
  `crates/veil-f128/src/simulator.rs:60`
- `sim` = `simulate_block_r1cs`
  `crates/veil-f128/src/simulator.rs:60`
- `prog` = `OracleProgrammer`
  `crates/veil-f128/src/simulator.rs:32`
- `had` = `simulate_hadamard`
  `crates/veil-f128/src/simulator.rs:193`
- `code` = `AdditiveRsCode`
  `crates/veil-f128/src/code.rs:95`
- `CH` = `Challenger`
  `crates/flock-core/src/challenger.rs:30`

```text
  call  sim   prog  had   code  CH
  |     |     |     |     |     |
  |---->|     |     |     |     |     1 simulate_block_r1cs
  |     |*    |     |     |     |     2 validate_public + vector_parameters
  |     |*    |     |     |     |     3 random_hash (roots, no witness)
  |     |---------------------->|     4 observe_bytes (fake roots)
  |     |<----------------------|     5 sample_not_zero_or_one
  |     |*    |     |     |     |     6 powers -> dot_vector
  |     |---------->|     |     |     7 simulate_hadamard
  |     |     |<----|     |     |     8 program oracle answers
  |     |     |---->|     |     |     9 Err(OracleProgrammingError) -> abort
  |     |     |     |---->|     |     10 decode_square / square_to_base
  |     |*    |     |     |     |     11 simulate_dot_product
  |<----|     |     |     |     |     12 BlockR1csProof (indistinguishable)

```

Anchors:

1. `simulate_block_r1cs`
   `crates/veil-f128/src/simulator.rs:60`
2. `validate_public` (`crates/veil-f128/src/block_r1cs.rs:353`) and `vector_parameters`
   `crates/veil-f128/src/block_r1cs.rs:327`
3. `random_hash`
   `crates/veil-f128/src/simulator.rs:384`
4. `Challenger::observe_bytes`
   `crates/flock-core/src/challenger.rs:49`
5. `sample_not_zero_or_one`, a `pub(crate)` helper in `block_r1cs`
   `crates/veil-f128/src/block_r1cs.rs:452`
6. `powers`, a `pub(crate)` helper in `block_r1cs`
   `crates/veil-f128/src/block_r1cs.rs:438`
7. `simulate_hadamard`
   `crates/veil-f128/src/simulator.rs:193`
8. `OracleProgrammer`
   `crates/veil-f128/src/simulator.rs:32`
9. `OracleProgrammingError`
   `crates/veil-f128/src/simulator.rs:37`
10. `AdditiveRsCode::decode_square` (`crates/veil-f128/src/code.rs:153`) and
    `AdditiveRsCode::square_to_base`
    `crates/veil-f128/src/code.rs:179`
11. `simulate_dot_product`
    `crates/veil-f128/src/simulator.rs:120`
12. `BlockR1csProof`
    `crates/veil-f128/src/block_r1cs.rs:68`

## Notes

- The simulator deliberately reaches into `block_r1cs` `pub(crate)` helpers —
  `build_link_claim` (`crates/veil-f128/src/block_r1cs.rs:366`), `powers`
  (`crates/veil-f128/src/block_r1cs.rs:438`), `sample_not_zero_or_one`
  (`crates/veil-f128/src/block_r1cs.rs:452`), `validate_public`
  (`crates/veil-f128/src/block_r1cs.rs:353`), and `vector_parameters`
  (`crates/veil-f128/src/block_r1cs.rs:327`). This white-box coupling is intentional: a
simulator that diverged
  from prover sampling would be unsound. It is recorded in
  `.claude/PROJECT-KNOWLEDGE.md` under LAYER_RULE, not a violation to "fix".
- **Nothing in this file is covered by CI.** The `veil` feature is built by no workflow —
  `lint.yml` uses default features, `test.yml` and `scripts/zk-certify.sh` use `zk` and
  `zk,symbolic`, and `veil-f128` is an optional dependency. `simulator.rs` additionally
  has no inline tests and there is no `crates/veil-f128/tests/`. These diagrams are
  derived by reading the source, and no green CI run corroborates them.
- `crates/veil-f128/src/ntt.rs` is a deliberate reimplementation, not a reuse of
  flock-core's NTT: the optimized flock-core additive NTT hard-codes the affine offset to
  zero, while VEIL needs two disjoint domains. Its doc comment calls it "a
  correctness-first path" — it is expected to be slower, on purpose.
- Error-trait coverage is uneven here. Only `CodeError` implements `Display` and
  `std::error::Error` (`crates/veil-f128/src/code.rs:66`); `BlockR1csError`,
  `DotProductError`, `HadamardError`, `ConstraintError`, and `SimulationError` do not.
- **This path commits unframed.** `commit_constraint_inputs` calls `commit_vectors` and
  `prove_constraints_from_commitment` calls `commit_hadamard`, not their `_framed`
  twins, so `framed` resolves to `None` in the `*_inner` helpers and
  `MerkleMatrix::new` (`crates/veil-f128/src/commitment.rs:29`) is used rather than
  `new_framed` (`crates/veil-f128/src/commitment.rs:33`). Read the `*_inner` signatures
  before assuming a hash domain.
- Messages 5 and 14 use different code paths of the same object: `encode_batch` produces
  base codewords, `encode_square` produces the twice-degree square code that carries the
  pointwise product. Confusing the two silently breaks the Hadamard argument.
