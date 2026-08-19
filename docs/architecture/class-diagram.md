# Workspace Class Diagram

Types and relations across the three crates. Sequence diagrams live alongside this file;
see [`README.md`](README.md).

## Legend

```text
   A ---> B     A uses / calls B
   A ---|> T    A implements trait T
   A *--- B     A owns B (field, by value)
   A o--- B     A holds B (reference / Arc / borrow)
   A ..> B      A converts into or produces B
```

## Crate dependencies

Verified against the three manifests, not assumed. `crates/flock-core/Cargo.toml` lists
no workspace dependency — it is the leaf. `crates/veil-f128/Cargo.toml` lists
`flock-core = { path = "../flock-core", features = ["zk"] }` and nothing else from the
workspace. `crates/flock-prover/Cargo.toml` lists `flock-core` unconditionally and
`veil-f128 = { path = "../veil-f128", optional = true }`, activated by
`veil = ["zk", "dep:veil-f128"]`.

```text
  +----------------+          +----------------+          +----------------+
  |  flock-core    |<---------|   veil-f128    |<---------|  flock-prover  |
  |  (tier 0)      |          |   (tier 1)     |  opt.    |   (tier 2)     |
  |  no workspace  |          | features=["zk"]|  "veil"  |  has [[bin]]   |
  |  dependencies  |          |                |          |                |
  +----------------+          +----------------+          +----------------+
          ^                                                        |
          |                    always (no feature gate)            |
          +--------------------------------------------------------+

  re-exports:
    flock-prover ..> flock_core::*              (crates/flock-prover/src/lib.rs:15)
    veil-f128    ..> flock_core::field::F128    (crates/veil-f128/src/lib.rs:32)
```

Arrows point from dependent to dependency. Cargo enforces this direction at compile
time, so no cycle is possible across crates.

## flock-core

```text
+----------------------------------+    +------------------------------------+
| F128                             |    | BlockR1cs                          |
|----------------------------------|    |------------------------------------|
| + lo: u64                        |    | + layout: WitnessLayout            |
| + hi: u64   repr(C, align(16))   |    | + k_log: usize                     |
|----------------------------------|    | + zk: Option<ZkBlockLayout>        |
| + ZERO / ONE                     |    |------------------------------------|
| + inv(self) -> Self              |    | + padding_spec() -> PaddingSpec    |
+----------------------------------+    | + x_ab_from_mlv(..) -> F128        |
                                        | + csc_lincheck_circuit()           |
                                        +------------------------------------+

+----------------------------------+    +------------------------------------+
| PcsParams                        |    | Commitment / ProverData            |
|----------------------------------|    |------------------------------------|
| + m: usize                       |    | + root: Hash                       |
| + log_inv_rate, log_batch_size   |    | + zk_mask, zk_blind                |
|----------------------------------|    |------------------------------------|
| + zk: bool, profile              |    | (commit_zk_with_ro: free fn)       |
+----------------------------------+    +------------------------------------+

+----------------------------------+    +------------------------------------+
| ZerocheckProof / ZerocheckClaim  |    | LincheckProof / LincheckClaim      |
|----------------------------------|    |------------------------------------|
| + z: F128                        |    | + rounds: Vec<(F128, F128)>        |
| + mlv_challenges: Vec<F128>      |    | + z_partial, r_inner_rest, w       |
+----------------------------------+    +------------------------------------+

+----------------------------------+    +------------------------------------+
| <<trait>> Challenger             |    | <<trait>> MaskSampler              |
|----------------------------------|    |------------------------------------|
|----------------------------------|    |------------------------------------|
| + observe_label / observe_bytes  |    | + fill_u64s(&mut [u64])            |
| + observe_f128(_slice)           |    +------------------------------------+
| + sample_f128(_vec)              |    
+----------------------------------+    
```

Anchors:

- `F128` — `crates/flock-core/src/field/gf2_128.rs:24`, re-exported at
  `crates/flock-core/src/field.rs:14`
- `F256Unreduced` — `crates/flock-core/src/field/gf2_128.rs:141`
- `BlockR1cs` — `crates/flock-core/src/r1cs.rs:56`
- `WitnessLayout` — `crates/flock-core/src/r1cs.rs:39`
- `SparseBinaryMatrix` — `crates/flock-core/src/r1cs.rs:14`
- `PcsParams` — `crates/flock-core/src/pcs/commit.rs:32`
- `Commitment` — `crates/flock-core/src/pcs/commit.rs:123`
- `ProverData` — `crates/flock-core/src/pcs/commit.rs:134`
- `BatchOpeningProofLigerito` — `crates/flock-core/src/pcs.rs:51`
- `ZkBlindOpening` — `crates/flock-core/src/pcs.rs:65`
- `pcs::VerifyError` — `crates/flock-core/src/pcs.rs:71`
- `ZerocheckProof` — `crates/flock-core/src/zerocheck.rs:313`
- `ZerocheckClaim` — `crates/flock-core/src/zerocheck.rs:293`
- `PaddingSpec` — `crates/flock-core/src/zerocheck.rs:258`
- `zerocheck::VerifyError` — `crates/flock-core/src/zerocheck.rs:331`
- `LincheckProof` — `crates/flock-core/src/lincheck.rs:379`
- `LincheckClaim` — `crates/flock-core/src/lincheck.rs:394`
- `QuirkyPoint` — `crates/flock-core/src/lincheck.rs:361`
- `lincheck::VerifyError` — `crates/flock-core/src/lincheck.rs:478`
- `R1csProofLigerito` — `crates/flock-core/src/proof.rs:18`
- `ZClaim` — `crates/flock-core/src/proof.rs:26`
- `RoContext` — `crates/flock-core/src/ro.rs:83`
- `RoChannel` — `crates/flock-core/src/ro.rs:56`
- `ZkRng` — `crates/flock-core/src/zk.rs:56`
- traits: `Challenger` `crates/flock-core/src/challenger.rs:30`, `ByteOracle`
  `crates/flock-core/src/ro.rs:204`, `MaskSampler` `crates/flock-core/src/zk.rs:36`,
  `LincheckCircuit` `crates/flock-core/src/lincheck.rs:173`
- implementors: `FsChallenger` `crates/flock-core/src/challenger.rs:184` and
  `RandomChallenger` `crates/flock-core/src/challenger.rs:101` implement `Challenger`;
  `CscCircuit` `crates/flock-core/src/lincheck.rs:249` and `SparseMatrixCircuit`
  `crates/flock-core/src/lincheck.rs:197` implement `LincheckCircuit`; `ZkRng`,
  `PlaybackSampler` `crates/flock-core/src/zk.rs:124` and `ZeroSampler`
  `crates/flock-core/src/zk.rs:148` implement `MaskSampler`

## veil-f128

```text
+------------------------------------+    +--------------------------------------+
| AdditiveRsCode                     |    | CodeParameters                       |
|------------------------------------|    |--------------------------------------|
| - parameters: CodeParameters       |    | + message_length: usize              |
|------------------------------------|    | + code_length: usize                 |
| + encode / encode_batch            |    |--------------------------------------|
| + encode_square / decode_square    |    | + new(..) -> Result<_, CodeError>    |
| + square_to_base                   |    | + square_message_length()            |
+------------------------------------+    +--------------------------------------+

+------------------------------------+    +--------------------------------------+
| MerkleMatrix                       |    | ArithmeticCircuit / CircuitBuilder   |
|------------------------------------|    |--------------------------------------|
| - rows, columns                    |    | - num_inputs, num_variables          |
|------------------------------------|    | - multiplications, linear_cons       |
| + new_framed(..)                   |    |--------------------------------------|
| + root() -> Hash                   |    | + num_inputs(), num_variables()      |
| + open(&[usize])                   |    | + is_satisfied(&self, witness)       |
+------------------------------------+    +--------------------------------------+

+------------------------------------+    +--------------------------------------+
| ConstraintProof                    |    | <<trait>> OracleProgrammer           |
|------------------------------------|    |--------------------------------------|
| + parameters: ConstraintParameters |    |--------------------------------------|
| + linear: DotProductProof          |    | + program_fresh(point, value)        |
| + hadamard: Option<HadamardProof>  |    |     -> Result<(), OracleProgErr>     |
+------------------------------------+    +--------------------------------------+
```

Anchors:

- `AdditiveRsCode` — `crates/veil-f128/src/code.rs:95`
- `CodeParameters` — `crates/veil-f128/src/code.rs:18`
- `CodeError` — `crates/veil-f128/src/code.rs:57` (the only error type in this crate that
  implements `Display` + `std::error::Error`, at `crates/veil-f128/src/code.rs:66`)
- `AdditiveCosetNtt` — `crates/veil-f128/src/ntt.rs:167`
- `MerkleMatrix` — `crates/veil-f128/src/commitment.rs:14`
- `MerkleMatrixOpening` — `crates/veil-f128/src/commitment.rs:22`
- `VectorParameters` — `crates/veil-f128/src/dot_product.rs:28`
- `DotProductProverData` — `crates/veil-f128/src/dot_product.rs:93`
- `DotProductProof` — `crates/veil-f128/src/dot_product.rs:102`
- `DotProductError` — `crates/veil-f128/src/dot_product.rs:113`
- `HadamardProverData` — `crates/veil-f128/src/hadamard.rs:24`
- `HadamardProof` — `crates/veil-f128/src/hadamard.rs:37`
- `HadamardError` — `crates/veil-f128/src/hadamard.rs:50`
- `BlockR1csParameters` — `crates/veil-f128/src/block_r1cs.rs:36`
- `BlockR1csProof` — `crates/veil-f128/src/block_r1cs.rs:68`
- `BlockR1csError` — `crates/veil-f128/src/block_r1cs.rs:76`
- `PublicEquality` — `crates/veil-f128/src/block_r1cs.rs:62`
- `LinearCombination` — `crates/veil-f128/src/constraints.rs:29`
- `ArithmeticCircuit` — `crates/veil-f128/src/constraints.rs:119`
- `CircuitBuilder` — `crates/veil-f128/src/constraints.rs:191`
- `ConstraintProof` — `crates/veil-f128/src/constraints.rs:277`
- `ConstraintCommitment` — `crates/veil-f128/src/constraints.rs:290`
- `ConstraintParameters` — `crates/veil-f128/src/constraints.rs:304`
- `ConstraintError` — `crates/veil-f128/src/constraints.rs:362`
- `SimulationError` — `crates/veil-f128/src/simulator.rs:40`
- trait `OracleProgrammer` — `crates/veil-f128/src/simulator.rs:32`

Error conversions inside the crate: `From<DotProductError> for BlockR1csError`
(`crates/veil-f128/src/block_r1cs.rs:89`), `From<HadamardError> for BlockR1csError`
(`crates/veil-f128/src/block_r1cs.rs:95`), `From<CodeError> for DotProductError`
(`crates/veil-f128/src/dot_product.rs:125`), `From<CodeError> for HadamardError`
(`crates/veil-f128/src/hadamard.rs:63`), `From<BlockR1csError> for SimulationError`
(`crates/veil-f128/src/simulator.rs:47`), `From<CodeError> for SimulationError`
(`crates/veil-f128/src/simulator.rs:53`).

## flock-prover

```text
+--------------------------------------+    +----------------------------------------+
| SealedStatement<'a>                  |    | ZkCertificate                          |
|--------------------------------------|    |----------------------------------------|
| - witness is unreachable by type     |    | + family: StatementFamily              |
+--------------------------------------+    |----------------------------------------|
                                            | (require_certified is a free fn)       |
                                            +----------------------------------------+
```

Anchors:

- `Blake3PreimageZkSetup` — `crates/flock-prover/src/r1cs_hashes/blake3_preimage.rs:413`
- `SuccinctVeilProof` — `crates/flock-prover/src/succinct_veil.rs:33`
- `SuccinctVeilError` — `crates/flock-prover/src/succinct_veil.rs:48`
- `SuccinctZerocheckInputs<'a>` — `crates/flock-prover/src/succinct_veil.rs:57`
- `RomZerocheckSimulator` — `crates/flock-prover/src/succinct_veil.rs:80`
- trait `SuccinctZerocheckSource` — `crates/flock-prover/src/succinct_veil.rs:68`
- `SealedStatement<'a>` — `crates/flock-prover/src/sim_seal.rs:10`
- `SimCoins` — `crates/flock-prover/src/sim_seal.rs:57`
- `ZkCertificate` — `crates/flock-prover/src/zk_certificate.rs:52`
- `StatementFamily` — `crates/flock-prover/src/zk_certificate.rs:45`
- `ZkGateError` — `crates/flock-prover/src/zk_certificate.rs:79`
- `SimGameLedger` — `crates/flock-prover/src/sim_game.rs:58`
- `SimGameHop` — `crates/flock-prover/src/sim_game.rs:8`
- `ProgrammableOracle` — `crates/flock-prover/src/sim_oracle.rs:58`
- `OracleChallenger` — `crates/flock-prover/src/sim_oracle.rs:206`
- `SimulatedProof` — `crates/flock-prover/src/preimage_simulator.rs:442`
- `SimError` — `crates/flock-prover/src/preimage_simulator.rs:160`
- `HashKind` — `crates/flock-prover/src/proof_io.rs:56`
- `DeserializeError` — `crates/flock-prover/src/proof_io.rs:103`
- `BundleReadError` — `crates/flock-prover/src/proof_io.rs:303`
- `R1csProofBundleLigerito` — `crates/flock-prover/src/proof_io.rs:150`
- `ChainProofBundleLigerito` — `crates/flock-prover/src/proof_io.rs:161`
- `R1csProofBundleZkA1` — `crates/flock-prover/src/proof_io.rs:191`

## Cross-crate relations

Only edges that cross a crate boundary.

```text
  flock-prover                         veil-f128                     flock-core
  ------------                         ---------                     ----------
  Blake3PreimageZkSetup *--- BlockR1cs -----------------------------------> (owns)
  Blake3PreimageZkSetup *--- PcsParams -----------------------------------> (owns)
  prove_succinct_veil_r1cs ---> commit_constraint_inputs
  prove_succinct_veil_r1cs ---> prove_constraints_from_commitment
  prove_succinct_veil_r1cs -------------------------------> zerocheck::prove_*
  prove_succinct_veil_r1cs -------------------------------> lincheck::prove_*
  prove_succinct_veil_r1cs -------------------------------> pcs::commit::commit_zk_*
  SuccinctVeilProof     *--- ConstraintProof
  SuccinctVeilProof     *------------------------------------ ZerocheckProof
  ConstraintError       ..> SuccinctVeilError    (From, never leaked bare)
  pcs::VerifyError      ..>-------------------------------->  SuccinctVeilError
  RomZerocheckSimulator ---|> SuccinctZerocheckSource
  AdditiveRsCode        ---------------------------------> F128 (re-exported)
  MerkleMatrix          ---------------------------------> merkle::Hash
  block_r1cs / hadamard / dot_product ---> Challenger  (generic bound C)
```

The wrapping rule is load-bearing and enforced by review, not by the compiler: veil-f128
error types must not appear in a non-`veil`-gated signature in flock-prover. They are
wrapped by `SuccinctVeilError` (`From<ConstraintError>` at
`crates/flock-prover/src/succinct_veil.rs:280`) or by `VeiledPreimageError` on the legacy
path, never leaked bare.

## Reading the boxes

`+` and `-` are the member's actual Rust visibility, not a stylistic convention. Where a
type exposes a private field through a `pub fn` accessor — `ArithmeticCircuit` is the
main case — the field is listed `-` and the accessor `+`. Free functions that operate on
a type (`commit_zk_with_ro`, `require_certified`) appear in the anchor lists rather than
in a type's method compartment, because they are not methods.

## Not shown

Deliberate omissions, so the caps above are not mistaken for completeness.

- **flock-core numeric kernels.** `field/gf2_128.rs`, `field/gf2_8.rs`, `field/phi8.rs`,
  `field/f128_slice.rs`, `ntt/additive_ntt_f128.rs`, `ntt/parallel_f128.rs`,
  `ntt/inv_table.rs`, `ntt/inv_table_deg4.rs`, `merkle/aarch64.rs`, `merkle/x86_64.rs`,
  `linalg.rs`, `bits.rs`, `scratch.rs`, `permutation.rs`. These are hand-tuned
  arithmetic with no outward relations — boxes for them would carry no edges.
- **The five zerocheck round-1 variants and the ligerito internals.**
  `zerocheck/univariate_skip*.rs` (4 files) and `pcs/ligerito.rs` (7498 lines) are drawn
  as single participants in the sequence diagrams instead; their internal types are
  implementation detail of one call.
- **`pcs/jagged.rs`** — an unreferenced module. Nothing in the workspace calls
  `jagged::`; it is declared at `crates/flock-core/src/pcs.rs:23` and mentioned once in a
  doc comment at `crates/flock-core/src/r1cs.rs:28`. Excluded because a class box would
  imply relations that do not exist.
- **`pcs/tensor_algebra.rs`, `pcs/symbolic_opening.rs`, `pcs/zk_audit.rs`** — offline
  audit and symbolic-execution support behind the `symbolic` feature, not on the
  production prove or verify path.
- **flock-prover primitives with fan-out 0-1** — `chain.rs`, `merkle_path.rs`,
  `digest_bind.rs`, `ligerito_decode.rs`, `r1cs_hashes.rs` encoders, `sim_ext.rs`,
  `zk_audit_support.rs`, `zk_rank_check.rs`, `transcript_schema.rs`, `r1cs_hashes.rs`
  per-hash modules (`blake3.rs`, `sha2.rs`, `keccak.rs`, `keccak3.rs`, and the shared
  `common.rs` helpers).
- **`veiled_preimage.rs` types** — the legacy whole-R1CS path, superseded by the
  succinct path. Shown in the sequence diagrams only where a name collides with the
  active path.
- **Trait `SymScalar`** (`crates/flock-core/src/symbolic/scalar.rs:6`) and the rest of
  the `symbolic` module — `symbolic`-feature only, offline exact symbolic execution for
  generating and re-verifying ZK theorem artifacts.
