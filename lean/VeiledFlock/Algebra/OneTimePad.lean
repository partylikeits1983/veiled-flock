import Flockzk.MaskingSurjective

/-!
# Coordinate-wise masking

The active FLOCK compiler serializes every private field coordinate as
`private + freshMask`.  This file specializes the generic masking theorem to
that identity channel.  The result is exact equality of distributions, not a
computational approximation.
-/

namespace VeiledFlock.OneTimePad

variable {F I W : Type*}
variable [AddCommGroup F] [Fintype F] [DecidableEq F]
variable [Fintype I]
variable [Fintype (I → F)] [DecidableEq (I → F)]

/-- The mask-to-visible-coordinate map used by a coordinate-wise one-time pad. -/
def identityMask : (I → F) →+ (I → F) := AddMonoidHom.id (I → F)

theorem identityMask_surjective : Function.Surjective (identityMask (F := F) (I := I)) :=
  fun value ↦ ⟨value, rfl⟩

/-- Adding one independent uniform mask per coordinate makes the complete
visible vector exactly independent of the private vector. -/
theorem maskedVector_witness_independent (secret : W → I → F) (left right : W) :
    (PMF.uniformOfFintype (I → F)).map
        (fun mask ↦ identityMask mask + secret left) =
      (PMF.uniformOfFintype (I → F)).map
        (fun mask ↦ identityMask mask + secret right) :=
  FlockZk.pmf_transcript_witness_indep_of_surjective
    identityMask secret identityMask_surjective left right

end VeiledFlock.OneTimePad
