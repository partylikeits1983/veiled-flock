import VeiledFlock.Production.Merkle.UniquePositionSampler

/-!
# Exact bounded production proof-of-work search

`FsChallenger::grind_pow_bounded` hashes
`ROLE_POW || state_digest || nonce_le`, scans nonces from zero in order, fails
closed at the supplied cap, and absorbs the first successful nonce.  The
acceptance predicate is kept explicit here; its separate finite probability
lemma depends only on the uniformly random 256-bit answer.
-/

namespace VeiledFlock.ProductionGrinding

open VeiledFlock.ConcreteOracle
open VeiledFlock.Framing
open VeiledFlock.ProductionBoundedOracle
open VeiledFlock.ProductionCombinedMerkleTransport
open VeiledFlock.ProductionFraming
open VeiledFlock.ProductionMerkleFamilyTransport
open VeiledFlock.ProductionThreeTree
open VeiledFlock.ProductionTranscriptFraming

/-- Scan consecutive mathematical counters, serialized modulo `2^64` exactly
as Rust's `u64`.  Production caps are far below the wrap boundary. -/
noncomputable def grindFrom (good : OracleBlock → Prop) [DecidablePred good]
    (oracle : List Byte → OracleBlock) (state : Nonce256) :
    ℕ → ℕ → Option Word64
  | _, 0 => none
  | start, trials + 1 =>
      let nonce := BitVec.ofNat 64 start
      if good (oracle (encodePowPoint state nonce)) then some nonce
      else grindFrom good oracle state (start + 1) trials

noncomputable def grindPowBounded (good : OracleBlock → Prop)
    [DecidablePred good] (oracle : List Byte → OracleBlock)
    (state : Nonce256) (trials : ℕ) : Option Word64 :=
  grindFrom good oracle state 0 trials

/-- Exact transcript update after a successful grind. -/
def afterGrind (transcript : List Byte) (nonce : Word64) : List Byte :=
  transcript ++ observeBytes (encodeLEList (byteCount := 8) nonce)

@[simp]
theorem encodePowPoint_length (state : Nonce256) (nonce : Word64) :
    (encodePowPoint state nonce).length = 41 := by
  simp [encodePowPoint]

@[simp]
theorem afterGrind_length (transcript : List Byte) (nonce : Word64) :
    (afterGrind transcript nonce).length = transcript.length + 17 := by
  simp [afterGrind]

/-- The bounded search depends only on its exact sequence of PoW-role points. -/
theorem grindFrom_oracle_congr
    (good : OracleBlock → Prop) [DecidablePred good]
    (leftOracle rightOracle : List Byte → OracleBlock)
    (state : Nonce256) (start trials : ℕ)
    (horacle : ∀ offset, offset < trials →
      rightOracle
          (encodePowPoint state (BitVec.ofNat 64 (start + offset))) =
        leftOracle
          (encodePowPoint state (BitVec.ofNat 64 (start + offset)))) :
    grindFrom good rightOracle state start trials =
      grindFrom good leftOracle state start trials := by
  induction trials generalizing start with
  | zero => rfl
  | succ trials inductionHypothesis =>
      simp only [grindFrom]
      have hzero := horacle 0 (by omega)
      simp only [Nat.add_zero] at hzero
      rw [hzero]
      split
      · rfl
      · apply inductionHypothesis
        intro offset hoffset
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          horacle (offset + 1) (by omega)

theorem grindPowBounded_oracle_congr
    (good : OracleBlock → Prop) [DecidablePred good]
    (leftOracle rightOracle : List Byte → OracleBlock)
    (state : Nonce256) (trials : ℕ)
    (horacle : ∀ candidate, candidate < trials →
      rightOracle (encodePowPoint state (BitVec.ofNat 64 candidate)) =
        leftOracle (encodePowPoint state (BitVec.ofNat 64 candidate))) :
    grindPowBounded good rightOracle state trials =
      grindPowBounded good leftOracle state trials := by
  exact grindFrom_oracle_congr good leftOracle rightOracle state 0 trials
    (by simpa using horacle)

/-- The simultaneous three-tree transport leaves the entire canonical
bounded grind unchanged. -/
theorem threeTree_grindPowBounded_exact {Coins : Type*}
    {maxLength : ℕ} (good : OracleBlock → Prop) [DecidablePred good]
    (coinEquiv : Coins ≃ Coins) (outer linear hadamard : TreeShape)
    (leftMaterial rightMaterial : ∀ tree,
      TreeMaterial (productionGeometry outer linear hadamard tree) Coins)
    (hleft : FamilyFits (maxLength := maxLength)
      (productionGeometry outer linear hadamard) leftMaterial)
    (hright : FamilyFits (maxLength := maxLength)
      (productionGeometry outer linear hadamard) rightMaterial)
    (hpow : 41 ≤ maxLength) (fallback : OracleBlock)
    (input : Coins × (BoundedBytes maxLength → OracleBlock))
    (state : Nonce256) (trials : ℕ) :
    let transported := boundedFamilyCoinOracleEquiv coinEquiv
      (productionGeometry outer linear hadamard)
      (productionGeometry_channel_injective outer linear hadamard)
      leftMaterial rightMaterial hleft hright input
    grindPowBounded good (answerBounded fallback transported.2) state trials =
      grindPowBounded good (answerBounded fallback input.2) state trials := by
  classical
  dsimp only
  apply grindPowBounded_oracle_congr good (answerBounded fallback input.2)
    (answerBounded fallback
      (boundedFamilyCoinOracleEquiv coinEquiv
        (productionGeometry outer linear hadamard)
        (productionGeometry_channel_injective outer linear hadamard)
        leftMaterial rightMaterial hleft hright input).2)
    state trials
  intro candidate _
  apply threeTree_answer_pow coinEquiv outer linear hadamard leftMaterial
    rightMaterial hleft hright fallback input state (BitVec.ofNat 64 candidate)
  simpa using hpow

end VeiledFlock.ProductionGrinding
