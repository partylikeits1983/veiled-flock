import VeiledFlock.Concrete.ConcreteRandomTape

/-!
# Audited concrete statistical distance

The Rust diagnostic tests a conservative deployment envelope of at most
1,024 proofs, at most `2^64` adversarial oracle queries, at most one million
protocol oracle queries per proof, and 32 programmable points per proof.
The registered shapes actually program at most 20 points.  This file evaluates
the complete exact-rational Lean ledger under that larger envelope.
-/

namespace VeiledFlock.ConcreteSecurityBound

open VeiledFlock.ConcreteParameters
open VeiledFlock.SecurityLedger

def reviewedParameters : Parameters where
  proofs := 1024
  programmedPoints := 32
  adversaryQueries := 2 ^ 64
  protocolQueriesPerProof := maxProtocolOracleQueriesPerProof

theorem registeredProgrammedPoints_le_reviewed (shape : BatchShape) :
    programmedPoints shape ≤ reviewedParameters.programmedPoints := by
  cases shape <;> decide

theorem reviewedParameters_fields :
    reviewedParameters.proofs = 1024 ∧
      reviewedParameters.programmedPoints = 32 ∧
      reviewedParameters.adversaryQueries = 2 ^ 64 ∧
      reviewedParameters.protocolQueriesPerProof = 1_000_000 := by
  decide

/-- Even the 1,024-proof conservative envelope has statistical distance
strictly below `2^-126` in the classical programmable random-oracle model. -/
theorem reviewed_zkBound_lt_two_pow_neg_126 :
    zkBound reviewedParameters < 1 / (2 : ℚ) ^ 126 := by
  native_decide

theorem reviewed_zkBound_negligible :
    zkBound reviewedParameters < 1 / (2 : ℚ) ^ 126 :=
  reviewed_zkBound_lt_two_pow_neg_126

end VeiledFlock.ConcreteSecurityBound
