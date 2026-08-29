import Mathlib
import VeiledFlock.ConcreteParameters

/-!
# Bounded distinct-position sampling

The concrete VEIL prover samples codeword positions with replacement until it
has collected the requested number of distinct coordinates.  The production
loop is fail-closed after a fixed number of trials.  This module proves a
finite coupon-collector tail bound for exactly that event.

If a run contains fewer than `target` distinct coordinates, its image is
contained in some `(target - 1)`-element subset of the domain.  A union bound
over those subsets gives

`choose(domain, target - 1) * ((target - 1) / domain) ^ trials`.
-/

namespace VeiledFlock.UniquePositionSampling

open VeiledFlock.ConcreteParameters

/-- Coordinates observed in a fixed finite sampling run. -/
def observedPositions {domain trials : ℕ}
    (run : Fin trials → Fin domain) : Finset (Fin domain) :=
  Finset.univ.image run

/-- Runs on which the capped sampler has not collected `target` positions. -/
def abortRuns (domain target trials : ℕ) :
    Finset (Fin trials → Fin domain) :=
  Finset.univ.filter fun run => (observedPositions run).card < target

/-- Runs whose every coordinate lies in a fixed support. -/
def containedRuns {domain : ℕ} (support : Finset (Fin domain))
    (trials : ℕ) : Finset (Fin trials → Fin domain) :=
  Fintype.piFinset fun _ : Fin trials => support

theorem mem_containedRuns {domain trials : ℕ}
    (support : Finset (Fin domain)) (run : Fin trials → Fin domain) :
    run ∈ containedRuns support trials ↔ ∀ i, run i ∈ support := by
  simp [containedRuns]

theorem card_containedRuns {domain trials : ℕ}
    (support : Finset (Fin domain)) :
    (containedRuns support trials).card = support.card ^ trials := by
  simpa [containedRuns] using
    (Fintype.card_piFinset_const support trials)

/-- Every aborting run is covered by an event indexed by a support of size
`target - 1`. -/
theorem abortRuns_subset_supportCover {domain target trials : ℕ}
    (htarget : 0 < target) (hsize : target ≤ domain) :
    abortRuns domain target trials ⊆
      (Finset.univ.powersetCard (target - 1)).biUnion
        (fun support => containedRuns support trials) := by
  intro run hrun
  rw [abortRuns, Finset.mem_filter] at hrun
  have himage : (observedPositions run).card ≤ target - 1 := by omega
  have htargetDomain : target - 1 ≤ (Finset.univ : Finset (Fin domain)).card := by
    simp
    omega
  obtain ⟨support, hobs, huniv, hcard⟩ :=
    Finset.exists_subsuperset_card_eq
      (s := observedPositions run)
      (t := (Finset.univ : Finset (Fin domain)))
      (n := target - 1) (by simp) himage htargetDomain
  rw [Finset.mem_biUnion]
  refine ⟨support, Finset.mem_powersetCard.mpr ⟨huniv, hcard⟩, ?_⟩
  rw [mem_containedRuns]
  intro i
  apply hobs
  exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩

/-- Counting form of the finite coupon-collector union bound. -/
theorem card_abortRuns_le {domain target trials : ℕ}
    (htarget : 0 < target) (hsize : target ≤ domain) :
    (abortRuns domain target trials).card ≤
      domain.choose (target - 1) * (target - 1) ^ trials := by
  calc
    (abortRuns domain target trials).card ≤
        (((Finset.univ : Finset (Fin domain)).powersetCard
          (target - 1)).biUnion
            (fun support => containedRuns support trials)).card :=
      Finset.card_le_card (abortRuns_subset_supportCover htarget hsize)
    _ ≤ ∑ support ∈
          (Finset.univ : Finset (Fin domain)).powersetCard (target - 1),
          (containedRuns support trials).card := Finset.card_biUnion_le
    _ = domain.choose (target - 1) * (target - 1) ^ trials := by
      calc
        ∑ support ∈
            (Finset.univ : Finset (Fin domain)).powersetCard (target - 1),
            (containedRuns support trials).card =
            ∑ _support ∈
              (Finset.univ : Finset (Fin domain)).powersetCard (target - 1),
              (target - 1) ^ trials := by
                apply Finset.sum_congr rfl
                intro support hsupport
                rw [card_containedRuns,
                  (Finset.mem_powersetCard.mp hsupport).2]
        _ = domain.choose (target - 1) * (target - 1) ^ trials := by
          simp [Finset.card_powersetCard]

/-- Probability form of the bound under uniform independent draws. -/
theorem abortProbability_le {domain target trials : ℕ}
    (htarget : 0 < target) (hsize : target ≤ domain) :
    ((abortRuns domain target trials).card : ℚ) /
        Fintype.card (Fin trials → Fin domain) ≤
      (domain.choose (target - 1) : ℚ) *
        (((target - 1 : ℕ) : ℚ) / domain) ^ trials := by
  have hdomain : 0 < domain := lt_of_lt_of_le htarget hsize
  have hcount := card_abortRuns_le (trials := trials) htarget hsize
  rw [Fintype.card_pi_const, Fintype.card_fin]
  norm_num only [Nat.cast_pow]
  calc
    ((abortRuns domain target trials).card : ℚ) / (domain : ℚ) ^ trials ≤
        ((domain.choose (target - 1) * (target - 1) ^ trials : ℕ) : ℚ) /
          (domain : ℚ) ^ trials := by
      apply div_le_div_of_nonneg_right
      · exact_mod_cast hcount
      · positivity
    _ = (domain.choose (target - 1) : ℚ) *
        (((target - 1 : ℕ) : ℚ) / domain) ^ trials := by
      push_cast
      rw [div_pow]
      ring

/-- Active production query count and fail-closed trial cap. -/
def queryCount : ℕ := 160
def samplingTrials : ℕ := 4096

/-- The padded three-product Hadamard instance uses a 2,048-coordinate code. -/
def hadamardDomain : ℕ := 2048

/-- Every registered shifted-transcript instance uses an 8,192-coordinate
linear code. -/
def linearDomain : ℕ := 8192

def positionAbortBound (domain : ℕ) : ℚ :=
  (domain.choose (queryCount - 1) : ℚ) *
    (((queryCount - 1 : ℕ) : ℚ) / domain) ^ samplingTrials

def hadamardAbortBound : ℚ := positionAbortBound hadamardDomain
def linearAbortBound : ℚ := positionAbortBound linearDomain

/-- Shape-specific failure bound for the Secure-profile outer L0 sampler.
Unlike the two VEIL samplers, its domain and target both depend on the
registered batch shape. -/
def outerAbortBound (shape : BatchShape) : ℚ :=
  ((2 ^ (m shape - 11)).choose (outerL0QueryCount shape - 1) : ℚ) *
    (((outerL0QueryCount shape - 1 : ℕ) : ℚ) /
      (2 ^ (m shape - 11) : ℕ)) ^ samplingTrials

theorem hadamardAbortProbability_le :
    ((abortRuns hadamardDomain queryCount samplingTrials).card : ℚ) /
        Fintype.card (Fin samplingTrials → Fin hadamardDomain) ≤
      hadamardAbortBound := by
  exact abortProbability_le (by decide) (by decide)

theorem linearAbortProbability_le :
    ((abortRuns linearDomain queryCount samplingTrials).card : ℚ) /
        Fintype.card (Fin samplingTrials → Fin linearDomain) ≤
      linearAbortBound := by
  exact abortProbability_le (by decide) (by decide)

theorem outerAbortProbability_le (shape : BatchShape) :
    ((abortRuns (2 ^ (m shape - 11)) (outerL0QueryCount shape)
        samplingTrials).card : ℚ) /
        Fintype.card
          (Fin samplingTrials → Fin (2 ^ (m shape - 11))) ≤
      outerAbortBound shape := by
  exact abortProbability_le
    (outerL0QueryCount_positive shape)
    (by cases shape <;> decide)

end VeiledFlock.UniquePositionSampling
