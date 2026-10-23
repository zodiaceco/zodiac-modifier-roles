import ConditionCheck.Stored
import ConditionPacking.Bytes

/-!
# What the comparison operators decide

Transcribes the comparison branch of `ConditionEvaluator.evaluate`
(`__compare`, `__compareSigned`, for `EqualTo`, `GreaterThan`, `LessThan`,
`SignedIntGreaterThan`, `SignedIntLessThan`) on top of `__input`, and states
what it decides about the value the decoder proof says the node reads.

keccak256 is a parameter `keccak : Bytes → Nat`. The `EqualTo` theorems
assume it has no collisions among the inputs involved (`KeyInjective`), the
usual collision-resistance assumption.
-/

namespace ConditionCheck
open DecoderFaithfulness DecoderFaithfulness.Roles

/-- `bytes32(compValue)`: the first 32 bytes, zero-padded on the right. -/
def bytes32 (cv : Bytes) : Nat := wordVal ((cv ++ zeros 32).take 32)

/-- `__compare`'s right-hand side: hashed if longer than 32 bytes. -/
def cvKey (keccak : Bytes → Nat) (cv : Bytes) : Nat :=
  if cv.length > 32 then keccak cv else bytes32 cv

/-- `int256(uint256(x))`. -/
def toInt (x : Nat) : Int := if x < 2 ^ 255 then x else (x : Int) - 2 ^ 256

/-- `__input`'s result as a number (`etherValue`: `msg.value`), or overflow. -/
def inputVal (keccak : Bytes → Nat) (value : Nat) : Input → Option Nat
  | .etherValue => some value
  | .overflow => none
  | .word n => some n
  | .hash p => some (keccak p)

/-- The comparison branch of `evaluate`: does the node pass? -/
def comparePasses (keccak : Bytes → Nat) (value : Nat) (inp : Input) (op : Operator)
    (cv : Bytes) : Bool :=
  match inputVal keccak value inp with
  | none => false
  | some v =>
    match op with
    | .EqualTo => v == cvKey keccak cv
    | .GreaterThan => decide (v > cvKey keccak cv)
    | .LessThan => decide (v < cvKey keccak cv)
    | .SignedIntGreaterThan => decide (toInt v > toInt (bytes32 cv))
    | .SignedIntLessThan => decide (toInt v < toInt (bytes32 cv))
    | _ => false

/-- The key `__compare` uses for a byte string of at least 32 bytes: the word
    itself, or its hash. -/
def key (keccak : Bytes → Nat) (x : Bytes) : Nat :=
  if x.length = 32 then wordVal x else keccak x

/-- No byte string gets the same key as a different compValue of at least 32
    bytes (keccak256 has no collisions, and no hash equals a 32-byte word it
    is compared against). -/
def KeyInjective (keccak : Bytes → Nat) : Prop :=
  ∀ x y : Bytes, 32 ≤ y.length → key keccak x = key keccak y → x = y

theorem bytes32_of_length {cv : Bytes} (h : cv.length = 32) : bytes32 cv = wordVal cv := by
  unfold bytes32
  rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]

theorem cvKey_eq_key (keccak : Bytes → Nat) {cv : Bytes} (h : 32 ≤ cv.length) :
    cvKey keccak cv = key keccak cv := by
  unfold cvKey key
  by_cases h32 : cv.length = 32
  · simp [h32, bytes32_of_length h32]
  · simp [show cv.length > 32 by omega, h32]

theorem inputVal_expect (keccak : Bytes → Nat) (value : Nat) (bs : Bytes) :
    inputVal keccak value (expectInput bs) = some (key keccak bs) := by
  unfold expectInput key
  split <;> rfl

/-- **`EqualTo` on a parameter.** It passes exactly when the parameter's spec
    encoding equals the (stored) compValue. -/
theorem equalTo_iff {keccak : Bytes → Nat} (hk : KeyInjective keccak) (value : Nat) {u : Val}
    {cv : Bytes} (hcv : 32 ≤ cv.length) :
    comparePasses keccak value (expectInput (enc u)) .EqualTo cv = true ↔ enc u = cv := by
  unfold comparePasses
  rw [inputVal_expect keccak value, cvKey_eq_key keccak hcv]
  simp only [beq_iff_eq]
  exact ⟨hk _ _ hcv, fun h => by rw [h]⟩

/-- `abi.encode(v)` for one value, as the SDK writes an `EqualTo` compValue. -/
def abiEncode (v : Val) : Bytes := encTuple [v]

/-- What the packer stores for it (`_transform`): the leading offset word is
    dropped for a value that is not inlined (dynamic). -/
def storedCv (v : Val) : Bytes := if v.isStatic then abiEncode v else (abiEncode v).drop 32

theorem storedCv_eq (v : Val) : storedCv v = enc v := by
  unfold storedCv abiEncode encTuple
  cases hs : v.isStatic
  · simp [encParts, headLen, hs, List.length_append, length_natBE, word]
  · simp [encParts, headLen, hs]

/-- **`EqualTo(v)` checks equality with `v`.** For an `EqualTo` node whose
    compValue the SDK set to `abi.encode(v)` (`storedCv v` after packing),
    reading parameter `u`: it passes exactly when `u` and `v` have the same
    spec encoding. -/
theorem equalTo_intended {keccak : Bytes → Nat} (hk : KeyInjective keccak) (value : Nat)
    {u v : Val} (hv : 32 ≤ (enc v).length) :
    comparePasses keccak value (expectInput (enc u)) .EqualTo (storedCv v) = true ↔
      enc u = enc v := by
  rw [storedCv_eq]; exact equalTo_iff hk value hv

/-- **Unsigned comparisons on a word.** -/
theorem compare_word (keccak : Bytes → Nat) (value : Nat) {w cv : Bytes} (hw : w.length = 32)
    (hcv : cv.length = 32) :
    (comparePasses keccak value (expectInput w) .GreaterThan cv = decide (wordVal w > wordVal cv)) ∧
    (comparePasses keccak value (expectInput w) .LessThan cv = decide (wordVal w < wordVal cv)) ∧
    (comparePasses keccak value (expectInput w) .SignedIntGreaterThan cv =
      decide (toInt (wordVal w) > toInt (wordVal cv))) ∧
    (comparePasses keccak value (expectInput w) .SignedIntLessThan cv =
      decide (toInt (wordVal w) < toInt (wordVal cv))) := by
  have hi : inputVal keccak value (expectInput w) = some (wordVal w) := by
    unfold expectInput; simp [hw, inputVal]
  have hk : cvKey keccak cv = wordVal cv := by
    unfold cvKey; simp [hcv, bytes32_of_length hcv]
  simp only [comparePasses, hi, hk, bytes32_of_length hcv]
  simp

/-- `toInt` is two's complement: the signed value of a 256-bit word. -/
theorem toInt_spec (x : Nat) :
    toInt x = if x < 2 ^ 255 then (x : Int) else (x : Int) - 2 ^ 256 := rfl

/-- **End to end, `EqualTo`.** On a stored array the check accepts, with a
    typed root: for every well-typed calldata, every visited `EqualTo` node
    passes exactly when its operand's spec encoding equals its compValue,
    unless it reads a `Slice` window, the ether value, or sits in an
    interpretation that does not fit (only with `s = true`). -/
theorem checked_equalTo {keccak : Bytes → Nat} (hk : KeyInjective keccak) (value : Nat)
    {s : Bool} {fs : List ConditionPacking.Flat} {lb : Nat} {ts : List Ty} {o : Bool}
    (h : checkStored s fs = some (.typed (.call lb ts o))) (avatar : Bytes)
    {pre : Bytes} {args : List Val} (hpre : pre.length = lb)
    (hargs : if o then HasTPre s args ts else HasTAll s args ts)
    (suffix : Bytes) (hlen : (calldata pre args suffix).length < 2 ^ 255)
    {p : List Nat} {d : Condition} {l : Nat}
    (hv : Eval (calldata pre args suffix) (annotate (ConditionPacking.rawTree avatar fs 0)) p d l)
    (hop : d.operator = .EqualTo) (hcv : 32 ≤ d.compValue.length) :
    (∃ u, (Val.call pre args).sub p = some u ∧
      (comparePasses keccak value (input (calldata pre args suffix) l d) .EqualTo d.compValue = true ↔
        enc u = d.compValue)) ∨
    (∃ u bs, (Val.call pre args).sub p = some u ∧ IsWindow bs (content u) ∧
      input (calldata pre args suffix) l d = .word (wordVal bs)) ∨
    input (calldata pre args suffix) l d = .etherValue ∨
    InStray s (calldata pre args suffix) (.call pre args) p d l := by
  have hs := checkStored_sound h avatar (fun _ => 0) (fun _ => 0)
  obtain ⟨_, _, _, hr, hz, hd⟩ := hs
  have hD := hd pre args (.inr ⟨lb, ts, o, rfl, .inl ⟨hpre, hargs⟩⟩) ⟨pre, args, rfl, hpre, hargs⟩
  rcases decoder_input _ pre args suffix hD hr hz hlen hv (by rw [hop]; rfl) with
    ⟨u, hsub, hin⟩ | hw | he | hst
  · left
    refine ⟨u, hsub, ?_⟩
    rw [hin]
    exact equalTo_iff hk value hcv
  · exact .inr (.inl hw)
  · exact .inr (.inr (.inl he))
  · exact .inr (.inr (.inr hst))

end ConditionCheck
