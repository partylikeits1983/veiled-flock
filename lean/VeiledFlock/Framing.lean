import Mathlib

/-!
# Injective byte framing

The classical-pROM bounds require every programmed point and every salted
Merkle input to depend injectively on its fresh 256-bit value.  These lemmas
prove the byte-level fact used by the Rust encodings: a fixed-length value at a
fixed offset can always be recovered, even when the remaining suffix depends
arbitrarily on that value.
-/

namespace VeiledFlock.Framing

abbrev Byte := Fin 256
abbrev NonceBytes (length : ℕ) := Fin length → Byte
abbrev Nonce256 := NonceBytes 32

/-- Finite representation of every byte string whose length is at most
`maxLength`.  The length is stored explicitly, so no padding ambiguity is
introduced. -/
abbrev BoundedBytes (maxLength : ℕ) :=
  Σ length : Fin (maxLength + 1), List.Vector Byte length

def boundBytes {maxLength : ℕ} (bytes : List Byte)
    (hbound : bytes.length ≤ maxLength) : BoundedBytes maxLength :=
  ⟨⟨bytes.length, Nat.lt_succ_of_le hbound⟩, ⟨bytes, rfl⟩⟩

def unboundBytes {maxLength : ℕ} (bytes : BoundedBytes maxLength) : List Byte :=
  bytes.2.toList

/-- The explicit length stored by `BoundedBytes` is exactly the list length,
so forgetting the bound loses no information. -/
theorem unboundBytes_injective {maxLength : ℕ} :
    Function.Injective (unboundBytes : BoundedBytes maxLength → List Byte) := by
  intro left right heq
  rcases left with ⟨leftLength, leftBytes⟩
  rcases right with ⟨rightLength, rightBytes⟩
  have hlength : leftLength = rightLength := by
    apply Fin.ext
    have := congrArg List.length heq
    simpa only [unboundBytes, List.Vector.toList_length] using this
  subst rightLength
  have hbytes : leftBytes = rightBytes :=
    List.Vector.eq leftBytes rightBytes heq
  subst rightBytes
  rfl

@[simp]
theorem unbound_boundBytes {maxLength : ℕ} (bytes : List Byte)
    (hbound : bytes.length ≤ maxLength) :
    unboundBytes (boundBytes bytes hbound) = bytes := rfl

theorem boundBytes_injective {maxLength : ℕ}
    {left right : List Byte} {hleft : left.length ≤ maxLength}
    {hright : right.length ≤ maxLength}
    (heq : boundBytes left hleft = boundBytes right hright) : left = right := by
  exact congrArg unboundBytes heq

/-- Generic fixed-offset framing. -/
def fixedOffsetFrame {A : Type*} (head : List Byte)
    (encode : A → List Byte) (suffix : A → List Byte) (value : A) :
    List Byte :=
  head ++ encode value ++ suffix value

/-- A fixed-length injective middle field remains injective when surrounded by
a fixed prefix and an arbitrary value-dependent suffix. -/
theorem fixedOffsetFrame_injective {A : Type*} (head : List Byte)
    (encode : A → List Byte) (suffix : A → List Byte) (length : ℕ)
    (hlength : ∀ value, (encode value).length = length)
    (hinjective : Function.Injective encode) :
    Function.Injective (fixedOffsetFrame head encode suffix) := by
  intro left right heq
  simp only [fixedOffsetFrame] at heq
  rw [List.append_assoc, List.append_assoc] at heq
  have heq' : encode left ++ suffix left = encode right ++ suffix right :=
    List.append_cancel_left heq
  have htake := congrArg (List.take length) heq'
  have hleft : (encode left ++ suffix left).take length = encode left := by
    rw [List.take_append_of_le_length (by simp [hlength])]
    simp [hlength]
  have hright : (encode right ++ suffix right).take length = encode right := by
    rw [List.take_append_of_le_length (by simp [hlength])]
    simp [hlength]
  rw [hleft, hright] at htake
  exact hinjective htake

def nonceBytes {length : ℕ} (nonce : NonceBytes length) : List Byte :=
  List.ofFn nonce

@[simp]
theorem length_nonceBytes {length : ℕ} (nonce : NonceBytes length) :
    (nonceBytes nonce).length = length := by
  simp [nonceBytes]

theorem nonceBytes_injective {length : ℕ} :
    Function.Injective (nonceBytes : NonceBytes length → List Byte) :=
  List.ofFn_injective

/-- Rust's tagged `observe_bytes` frame for a 32-byte proof nonce:
`OP_BYTES || 32_u64_le || nonce`. -/
def transcriptNoncePrefix : List Byte :=
  [(5 : Byte), (32 : Byte)] ++ List.replicate 7 0

def transcriptNonceFrame (nonce : Nonce256) : List Byte :=
  transcriptNoncePrefix ++ nonceBytes nonce

@[simp]
theorem length_transcriptNonceFrame (nonce : Nonce256) :
    (transcriptNonceFrame nonce).length = 41 := by
  simp [transcriptNonceFrame, transcriptNoncePrefix]

theorem transcriptNonceFrame_injective :
    Function.Injective transcriptNonceFrame := by
  intro left right heq
  exact nonceBytes_injective (List.append_cancel_left heq)

/-- A Fiat--Shamir squeeze point containing the tagged proof nonce at its
protocol-fixed offset is injective in that nonce. -/
theorem transcriptPoint_injective (head : List Byte)
    (suffix : Nonce256 → List Byte) :
    Function.Injective
      (fixedOffsetFrame head transcriptNonceFrame suffix) :=
  fixedOffsetFrame_injective head transcriptNonceFrame suffix 41
    length_transcriptNonceFrame transcriptNonceFrame_injective

/-- A Merkle header contains its 32-byte tree nonce directly at bytes 16--47.
The first 16 bytes encode role, magic, channel, depth and reserved bytes; all
remaining header/location/payload bytes may vary with the nonce without
affecting injectivity. -/
theorem merkleHeaderPoint_injective (headerPrefix : Fin 16 → Byte)
    (suffix : Nonce256 → List Byte) :
    Function.Injective
      (fixedOffsetFrame (List.ofFn headerPrefix) nonceBytes suffix) :=
  fixedOffsetFrame_injective (List.ofFn headerPrefix) nonceBytes suffix 32
    length_nonceBytes nonceBytes_injective

/-- A salted Merkle leaf oracle input contains the 32-byte leaf salt at bytes
76--107: the 64-byte Merkle header is followed by the 12-byte node location,
then the witness-dependent leaf payload begins with the salt.  The fixed
76-byte prefix may contain the independently sampled tree nonce. -/
theorem merkleLeafPoint_injective (headerLocationPrefix : Fin 76 → Byte)
    (suffix : Nonce256 → List Byte) :
    Function.Injective
      (fixedOffsetFrame (List.ofFn headerLocationPrefix) nonceBytes suffix) :=
  fixedOffsetFrame_injective (List.ofFn headerLocationPrefix) nonceBytes suffix
    32 length_nonceBytes nonceBytes_injective

/-- Distinct fixed prefixes make a whole family of framed points distinct,
even when each site's hidden value and suffix are unrelated. -/
theorem fixedPrefixFrame_family_injective {Index A : Type*}
    (prefixLength : ℕ) (head : Index → Fin prefixLength → Byte)
    (hhead : Function.Injective head)
    (encode : A → List Byte) (suffix : Index → A → List Byte)
    (values : Index → A) :
    Function.Injective (fun site =>
      fixedOffsetFrame (List.ofFn (head site)) encode (suffix site) (values site)) := by
  intro left right heq
  have htake := congrArg (List.take prefixLength) heq
  have hleft :
      (fixedOffsetFrame (List.ofFn (head left)) encode (suffix left)
        (values left)).take prefixLength = List.ofFn (head left) := by
    simp [fixedOffsetFrame]
  have hright :
      (fixedOffsetFrame (List.ofFn (head right)) encode (suffix right)
        (values right)).take prefixLength = List.ofFn (head right) := by
    simp [fixedOffsetFrame]
  rw [hleft, hright] at htake
  apply hhead
  exact List.ofFn_injective htake

/-- Two differently populated framed families with the same injective fixed
prefix can coincide only at the same family index. -/
theorem fixedPrefixFrame_cross_index {Index A : Type*}
    (prefixLength : ℕ) (head : Index → Fin prefixLength → Byte)
    (hhead : Function.Injective head)
    (encode : A → List Byte)
    (leftSuffix rightSuffix : Index → A → List Byte)
    (leftValues rightValues : Index → A)
    {left right : Index}
    (heq :
      fixedOffsetFrame (List.ofFn (head left)) encode (leftSuffix left)
          (leftValues left) =
        fixedOffsetFrame (List.ofFn (head right)) encode (rightSuffix right)
          (rightValues right)) :
    left = right := by
  have htake := congrArg (List.take prefixLength) heq
  have hleft :
      (fixedOffsetFrame (List.ofFn (head left)) encode (leftSuffix left)
        (leftValues left)).take prefixLength = List.ofFn (head left) := by
    simp [fixedOffsetFrame]
  have hright :
      (fixedOffsetFrame (List.ofFn (head right)) encode (rightSuffix right)
        (rightValues right)).take prefixLength = List.ofFn (head right) := by
    simp [fixedOffsetFrame]
  rw [hleft, hright] at htake
  exact hhead (List.ofFn_injective htake)

/-- Cross-leaf distinctness for the exact 76-byte production prefix.  This is
stronger than salt injectivity at one site and is the premise needed to split
all initial-leaf oracle answers into independent coordinates. -/
theorem merkleLeafFamily_injective {Index : Type*}
    (headerLocationPrefix : Index → Fin 76 → Byte)
    (hprefix : Function.Injective headerLocationPrefix)
    (suffix : Index → Nonce256 → List Byte) (salts : Index → Nonce256) :
    Function.Injective (fun site =>
      fixedOffsetFrame (List.ofFn (headerLocationPrefix site)) nonceBytes
        (suffix site) (salts site)) :=
  fixedPrefixFrame_family_injective 76 headerLocationPrefix hprefix nonceBytes
    suffix salts

end VeiledFlock.Framing
