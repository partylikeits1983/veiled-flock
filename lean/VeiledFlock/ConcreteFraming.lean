import VeiledFlock.Framing
import VeiledFlock.NonceSerialization

/-!
# Production nonce frames

These specializations connect the numeric 256-bit nonce used by the finite
probability game to the exact byte offsets used by the Rust Fiat--Shamir and
Merkle encodings.  Prefixes and suffixes may depend on the complete prior
interaction; injectivity follows solely from the fixed nonce field.
-/

namespace VeiledFlock.ConcreteFraming

open VeiledFlock.Framing
open VeiledFlock.NonceSerialization

/-- A Fiat--Shamir point containing Rust's tagged 32-byte proof nonce. -/
noncomputable def transcriptPoint (head : List Byte)
    (suffix : NumericNonce → List Byte) (nonce : NumericNonce) : List Byte :=
  fixedOffsetFrame head
    (fun value => transcriptNonceFrame (numericNonceBytes value)) suffix nonce

theorem transcriptPoint_injective (head : List Byte)
    (suffix : NumericNonce → List Byte) :
    Function.Injective (transcriptPoint head suffix) := by
  apply fixedOffsetFrame_injective head
    (fun value => transcriptNonceFrame (numericNonceBytes value)) suffix 41
  · intro value
    exact length_transcriptNonceFrame (numericNonceBytes value)
  · exact Framing.transcriptNonceFrame_injective.comp
      numericNonceBytes.injective

/-- A Merkle header point containing its numeric 32-byte tree nonce after the
fixed 16-byte header prefix. -/
noncomputable def merkleHeaderPoint (headerPrefix : Fin 16 → Byte)
    (suffix : NumericNonce → List Byte) (nonce : NumericNonce) : List Byte :=
  fixedOffsetFrame (List.ofFn headerPrefix)
    (fun value => nonceBytes (numericNonceBytes value)) suffix nonce

theorem merkleHeaderPoint_injective (headerPrefix : Fin 16 → Byte)
    (suffix : NumericNonce → List Byte) :
    Function.Injective (merkleHeaderPoint headerPrefix suffix) := by
  apply fixedOffsetFrame_injective (List.ofFn headerPrefix)
    (fun value => nonceBytes (numericNonceBytes value)) suffix 32
  · intro value
    exact length_nonceBytes (numericNonceBytes value)
  · exact Framing.nonceBytes_injective.comp numericNonceBytes.injective

/-- A salted Merkle leaf point containing its numeric 32-byte leaf salt after
the exact 64-byte header and 12-byte node-location prefix. -/
noncomputable def merkleLeafPoint (headerLocationPrefix : Fin 76 → Byte)
    (suffix : NumericNonce → List Byte) (salt : NumericNonce) : List Byte :=
  fixedOffsetFrame (List.ofFn headerLocationPrefix)
    (fun value => nonceBytes (numericNonceBytes value)) suffix salt

theorem merkleLeafPoint_injective (headerLocationPrefix : Fin 76 → Byte)
    (suffix : NumericNonce → List Byte) :
    Function.Injective (merkleLeafPoint headerLocationPrefix suffix) := by
  apply fixedOffsetFrame_injective (List.ofFn headerLocationPrefix)
    (fun value => nonceBytes (numericNonceBytes value)) suffix 32
  · intro value
    exact length_nonceBytes (numericNonceBytes value)
  · exact Framing.nonceBytes_injective.comp numericNonceBytes.injective

theorem merkleLeafFamily_injective {Index : Type*}
    (headerLocationPrefix : Index → Fin 76 → Byte)
    (hprefix : Function.Injective headerLocationPrefix)
    (suffix : Index → NumericNonce → List Byte)
    (salts : Index → NumericNonce) :
    Function.Injective (fun site =>
      merkleLeafPoint (headerLocationPrefix site) (suffix site) (salts site)) :=
  Framing.fixedPrefixFrame_family_injective 76 headerLocationPrefix hprefix
    (fun value => nonceBytes (numericNonceBytes value)) suffix salts

/-- Cross-family index recovery for real and simulated hidden leaves.  The
payloads and salts may differ; the exact 76-byte header/location prefix alone
recovers the common leaf index. -/
theorem merkleLeafPoint_cross_index {Index : Type*}
    (headerLocationPrefix : Index → Fin 76 → Byte)
    (hprefix : Function.Injective headerLocationPrefix)
    (leftSuffix rightSuffix : Index → NumericNonce → List Byte)
    (leftSalts rightSalts : Index → NumericNonce)
    {left right : Index}
    (heq :
      merkleLeafPoint (headerLocationPrefix left) (leftSuffix left)
          (leftSalts left) =
        merkleLeafPoint (headerLocationPrefix right) (rightSuffix right)
          (rightSalts right)) :
    left = right := by
  exact Framing.fixedPrefixFrame_cross_index 76 headerLocationPrefix hprefix
    (fun value => nonceBytes (numericNonceBytes value))
    leftSuffix rightSuffix leftSalts rightSalts heq

end VeiledFlock.ConcreteFraming
