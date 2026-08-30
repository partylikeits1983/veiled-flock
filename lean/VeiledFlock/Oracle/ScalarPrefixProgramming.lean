import VeiledFlock.Algebra.Field128Serialization

/-!
# Vectorized scalar-prefix oracle programming

The Rust simulator chooses one `F128` value per programmed scalar site,
overwrites bytes 0--15 of the corresponding 32-byte oracle block, and leaves
bytes 16--31 unchanged.  This file lifts the single-block equivalence to the
complete adaptive answer vector and records both halves pointwise.
-/

namespace VeiledFlock.ScalarPrefixProgramming

open VeiledFlock.ConcreteOracle
open VeiledFlock.Field128Ghash
open VeiledFlock.Field128Serialization

abbrev ScalarAnswers (sites : ℕ) := Fin sites → GhashField
abbrev BlockAnswers (sites : ℕ) := Fin sites → OracleBlock
abbrev DiscardedPrefixes (sites : ℕ) := Fin sites → OracleHalf

/-- Pointwise form of `programScalarCoinEquiv`, with products moved outside
the finite function space. -/
noncomputable def answerCoinEquiv (sites : ℕ) :
    ScalarAnswers sites × BlockAnswers sites ≃
      BlockAnswers sites × DiscardedPrefixes sites where
  toFun coins :=
    (fun site ↦ (programScalarCoinEquiv
      (coins.1 site, coins.2 site)).1,
    fun site ↦ (programScalarCoinEquiv
      (coins.1 site, coins.2 site)).2)
  invFun output :=
    (fun site ↦ (programScalarCoinEquiv.symm
      (output.1 site, output.2 site)).1,
    fun site ↦ (programScalarCoinEquiv.symm
      (output.1 site, output.2 site)).2)
  left_inv coins := by
    apply Prod.ext <;> funext site
    · exact congrArg Prod.fst
        (programScalarCoinEquiv.symm_apply_apply
          (coins.1 site, coins.2 site))
    · exact congrArg Prod.snd
        (programScalarCoinEquiv.symm_apply_apply
          (coins.1 site, coins.2 site))
  right_inv output := by
    apply Prod.ext <;> funext site
    · exact congrArg Prod.fst
        (programScalarCoinEquiv.apply_symm_apply
          (output.1 site, output.2 site))
    · exact congrArg Prod.snd
        (programScalarCoinEquiv.apply_symm_apply
          (output.1 site, output.2 site))

@[simp]
theorem answerCoinEquiv_programmedBlock (sites : ℕ)
    (coins : ScalarAnswers sites × BlockAnswers sites) (site : Fin sites) :
    (answerCoinEquiv sites coins).1 site =
      programScalarPrefix (encodeGhashField (coins.1 site))
        (coins.2 site) := by
  rfl

@[simp]
theorem answerCoinEquiv_discardedPrefix (sites : ℕ)
    (coins : ScalarAnswers sites × BlockAnswers sites) (site : Fin sites) :
    (answerCoinEquiv sites coins).2 site =
      (oracleBlockSplit (coins.2 site)).1 := by
  rfl

/-- The programmed block decodes to the simulator-selected field value. -/
theorem programmedBlock_decodes (sites : ℕ)
    (coins : ScalarAnswers sites × BlockAnswers sites) (site : Fin sites) :
    encodeGhashFieldEquiv.symm
        (oracleBlockSplit ((answerCoinEquiv sites coins).1 site)).1 =
      coins.1 site := by
  rw [answerCoinEquiv_programmedBlock,
    oracleBlockSplit_programScalarPrefix]
  exact encodeGhashFieldEquiv.symm_apply_apply (coins.1 site)

/-- Bytes 16--31 are literally the unmodified high half of the original
random-oracle block at every programmed site. -/
theorem programmedBlock_preservesHighHalf (sites : ℕ)
    (coins : ScalarAnswers sites × BlockAnswers sites) (site : Fin sites) :
    (oracleBlockSplit ((answerCoinEquiv sites coins).1 site)).2 =
      (oracleBlockSplit (coins.2 site)).2 := by
  rw [answerCoinEquiv_programmedBlock,
    oracleBlockSplit_programScalarPrefix]

/-- The vectorized operation is an exact uniform reparameterization. -/
theorem uniform_answerCoinEquiv (sites : ℕ) :
    (PMF.uniformOfFintype
      (ScalarAnswers sites × BlockAnswers sites)).map
        (answerCoinEquiv sites) =
      PMF.uniformOfFintype
        (BlockAnswers sites × DiscardedPrefixes sites) := by
  exact VeiledFlock.Probability.uniform_map_equiv (answerCoinEquiv sites)

end VeiledFlock.ScalarPrefixProgramming
