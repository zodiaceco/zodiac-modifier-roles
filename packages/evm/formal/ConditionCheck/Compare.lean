import ConditionCheck.Stored
import ConditionPacking.Bytes

/-!
# What the comparison operators decide

Transcribes `ConditionEvaluator._compare` (for `EqualTo`, `GreaterThan`,
`LessThan`, `SignedIntGreaterThan`, `SignedIntLessThan`) on top of `_read`,
and states what it decides about the value the decoder proof says the node
reads.

keccak256 is a parameter `keccak : Bytes → Nat`. `_compare` compares an
operand of up to 32 bytes as a word and a longer one by its hash, and
`EqualTo` asks the compValue to be as long as the operand (32 bytes for a
word). The `EqualTo` theorems say the check passes exactly when the operand
equals the compValue, or the two are different values of one length with
the same key (`KeyCollides`). For words that never happens
(`keyCollides_word`); for longer values it is a keccak256 collision on
exactly these two byte strings.
-/

namespace ConditionCheck
open DecoderFaithfulness DecoderFaithfulness.Roles

/-- `bytes32(compValue)`: the first 32 bytes, zero-padded on the right. -/
def bytes32 (cv : Bytes) : Nat := wordVal ((cv ++ zeros 32).take 32)

/-- `int256(uint256(x))`. -/
def toInt (x : Nat) : Int := if x < 2 ^ 255 then x else (x : Int) - 2 ^ 256

/-- `signextend(length - 1, x)` as an `int256`: a value of fewer than 32
    bytes carries its sign in its top bit. (For 32 bytes and more, and for
    0, where `length - 1` wraps, `signextend` leaves `x` as it is.) -/
def signExtend (length x : Nat) : Int :=
  if 0 < length ∧ length < 32 then
    if x % 2 ^ (8 * length) < 2 ^ (8 * length - 1) then ((x % 2 ^ (8 * length) : Nat) : Int)
    else ((x % 2 ^ (8 * length) : Nat) : Int) - 2 ^ (8 * length)
  else toInt x

/-- `_read`'s word as a number (`etherValue`: `msg.value`), or overflow. -/
def inputVal (keccak : Bytes → Nat) (value : Nat) : Input → Option Nat
  | .etherValue => some value
  | .overflow => none
  | .word n => some n
  | .hash p => some (keccak p)

/-- `_compare`: does the node pass? `length` is the length of the operand
    (32 for the ether value). -/
def comparePasses (keccak : Bytes → Nat) (value : Nat) (inp : Input) (length : Nat)
    (op : Operator) (cv : Bytes) : Bool :=
  match inputVal keccak value inp with
  | none => false
  | some v =>
    match op with
    | .EqualTo =>
      if length > 32 then cv.length == length && v == keccak cv
      else cv.length == 32 && v == bytes32 cv
    | .GreaterThan => decide (v > bytes32 cv)
    | .LessThan => decide (v < bytes32 cv)
    | .SignedIntGreaterThan => decide (signExtend length v > toInt (bytes32 cv))
    | .SignedIntLessThan => decide (signExtend length v < toInt (bytes32 cv))
    | _ => false

/-- The key `_compare` uses for a byte string of at least 32 bytes: the word
    itself, or its hash. -/
def key (keccak : Bytes → Nat) (x : Bytes) : Nat :=
  if x.length = 32 then wordVal x else keccak x

/-- `x` and `y` are different values of one length with the same key: never
    for words (`keyCollides_word`), a keccak256 collision on `x` and `y` for
    longer ones. -/
def KeyCollides (keccak : Bytes → Nat) (x y : Bytes) : Prop :=
  x.length = y.length ∧ x ≠ y ∧ key keccak x = key keccak y

theorem bytes32_of_length {cv : Bytes} (h : cv.length = 32) : bytes32 cv = wordVal cv := by
  unfold bytes32
  rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]

/-- Two words never collide. -/
theorem keyCollides_word (keccak : Bytes → Nat) {x cv : Bytes} (h : cv.length = 32) :
    ¬ KeyCollides keccak x cv := by
  rintro ⟨hx, hne, hk⟩
  have hx32 : x.length = 32 := by omega
  unfold key at hk
  rw [ite_eq_left hx32, ite_eq_left h] at hk
  exact hne (by rw [← ConditionPacking.natBE_wordVal x, ← ConditionPacking.natBE_wordVal cv, hx32,
    h, hk])

theorem inputVal_expect (keccak : Bytes → Nat) (value : Nat) (bs : Bytes) :
    inputVal keccak value (expectInput bs) = some (key keccak bs) := by
  unfold expectInput key
  split <;> rfl

/-- `EqualTo` passes exactly when the compValue is as long as the operand
    and has its key. -/
theorem equalTo_key {keccak : Bytes → Nat} {cv x : Bytes} (value : Nat) (hx : 32 ≤ x.length) :
    comparePasses keccak value (expectInput x) x.length .EqualTo cv = true ↔
      cv.length = x.length ∧ key keccak x = key keccak cv := by
  unfold comparePasses
  rw [inputVal_expect keccak value]
  simp only
  by_cases h32 : x.length = 32
  · rw [ite_eq_right (by omega), h32]
    simp only [Bool.and_eq_true, beq_iff_eq]
    constructor
    · rintro ⟨hl, hk⟩
      refine ⟨hl, ?_⟩
      rw [hk, bytes32_of_length hl]; unfold key; rw [ite_eq_left hl]
    · rintro ⟨hl, hk⟩
      refine ⟨hl, ?_⟩
      rw [hk, bytes32_of_length hl]; unfold key; rw [ite_eq_left hl]
  · rw [ite_eq_left (by omega)]
    simp only [Bool.and_eq_true, beq_iff_eq]
    have hkey : ∀ hl : cv.length = x.length, key keccak cv = keccak cv := by
      intro hl; unfold key; rw [ite_eq_right (by omega)]
    constructor
    · rintro ⟨hl, hk⟩
      exact ⟨hl, by rw [hk, hkey hl]⟩
    · rintro ⟨hl, hk⟩
      exact ⟨hl, by rw [hk, hkey hl]⟩

/-- **`EqualTo` on a parameter.** It passes exactly when the parameter's spec
    encoding equals the (stored) compValue, or the two collide. -/
theorem equalTo_iff {keccak : Bytes → Nat} {cv : Bytes} (value : Nat)
    {u : Val} (hu : 32 ≤ (enc u).length) :
    comparePasses keccak value (expectInput (enc u)) (enc u).length .EqualTo cv = true ↔
      enc u = cv ∨ KeyCollides keccak (enc u) cv := by
  rw [equalTo_key value hu]
  constructor
  · rintro ⟨hl, hk⟩
    by_cases he : enc u = cv
    · exact .inl he
    · exact .inr ⟨hl.symm, he, hk⟩
  · rintro (h | ⟨hl, _, hk⟩)
    · rw [← h]; exact ⟨rfl, rfl⟩
    · exact ⟨hl.symm, hk⟩

/-- For a 32-byte compValue, exactly equality. -/
theorem equalTo_iff_word {keccak : Bytes → Nat} {cv : Bytes} (value : Nat)
    {u : Val} (hu : 32 ≤ (enc u).length) (hcv : cv.length = 32) :
    comparePasses keccak value (expectInput (enc u)) (enc u).length .EqualTo cv = true ↔
      enc u = cv := by
  rw [equalTo_iff value hu]
  exact ⟨fun h => h.resolve_right (keyCollides_word keccak hcv), .inl⟩

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
theorem equalTo_intended {keccak : Bytes → Nat} {u v : Val}
    (value : Nat) (hu : 32 ≤ (enc u).length) :
    comparePasses keccak value (expectInput (enc u)) (enc u).length .EqualTo (storedCv v) = true ↔
      enc u = enc v ∨ KeyCollides keccak (enc u) (enc v) := by
  rw [storedCv_eq]; exact equalTo_iff value hu

theorem signExtend_word (x : Nat) : signExtend 32 x = toInt x := by
  unfold signExtend; simp

/-- **Comparisons on a word.** -/
theorem compare_word (keccak : Bytes → Nat) (value : Nat) {w cv : Bytes} (hw : w.length = 32)
    (hcv : cv.length = 32) :
    (comparePasses keccak value (expectInput w) 32 .GreaterThan cv =
      decide (wordVal w > wordVal cv)) ∧
    (comparePasses keccak value (expectInput w) 32 .LessThan cv =
      decide (wordVal w < wordVal cv)) ∧
    (comparePasses keccak value (expectInput w) 32 .SignedIntGreaterThan cv =
      decide (toInt (wordVal w) > toInt (wordVal cv))) ∧
    (comparePasses keccak value (expectInput w) 32 .SignedIntLessThan cv =
      decide (toInt (wordVal w) < toInt (wordVal cv))) := by
  have hi : inputVal keccak value (expectInput w) = some (wordVal w) := by
    unfold expectInput; simp [hw, inputVal]
  simp only [comparePasses, hi, bytes32_of_length hcv, signExtend_word]
  simp

/-- `toInt` is two's complement: the signed value of a 256-bit word. -/
theorem toInt_spec (x : Nat) :
    toInt x = if x < 2 ^ 255 then (x : Int) else (x : Int) - 2 ^ 256 := rfl

/-- **End to end, `EqualTo`.** On a stored array the check accepts, with a
    typed root: for every well-typed calldata, every visited `EqualTo` node
    passes exactly when its operand's spec encoding equals its compValue (or
    the two collide), unless it reads a `Slice` window, the ether value, or
    sits in a variant branch that does not fit (`InStray`, only with
    `s = true`). -/
theorem checked_equalTo {keccak : Bytes → Nat} (value : Nat)
    {s : Bool} {fs : List ConditionPacking.Flat} {lb : Nat} {ts : List Ty} {o : Bool}
    (h : checkStored s fs = some (.typed (.call lb ts o))) (avatar : Bytes)
    {pre : Bytes} {args : List Val} (hpre : pre.length = lb)
    (hargs : if o then HasTPre s args ts else HasTAll s args ts)
    (suffix : Bytes) (hlen : (calldata pre args suffix).length < 2 ^ 255)
    {p : List Nat} {d : Condition} {l : Slice} {y : Nat}
    (hv : Eval (calldata pre args suffix) (annotate (ConditionPacking.rawTree avatar fs 0))
      p d l y)
    (hop : d.operator = .EqualTo) :
    (∃ u, (Val.call pre args).sub p = some u ∧
      (comparePasses keccak value (input (calldata pre args suffix) l y d)
          (inputLength (calldata pre args suffix) l y d) .EqualTo d.compValue = true ↔
        enc u = d.compValue ∨ KeyCollides keccak (enc u) d.compValue)) ∨
    (∃ u bs, (Val.call pre args).sub p = some u ∧ IsWindow bs (content u) ∧
      input (calldata pre args suffix) l y d = .word (wordVal bs) ∧
      inputLength (calldata pre args suffix) l y d = bs.length) ∨
    input (calldata pre args suffix) l y d = .etherValue ∨
    InStray s (calldata pre args suffix) (ConditionPacking.rawTree avatar fs 0)
      (rootSlice pre args suffix) (.call pre args) p d l y := by
  have hs := checkStored_sound h avatar (fun _ => 0) (fun _ => 0)
  obtain ⟨_, _, _, hr, hz, hd⟩ := hs
  have hD := hd pre args (.inr ⟨lb, ts, o, rfl, .inl ⟨hpre, hargs⟩⟩) ⟨pre, args, rfl, hpre, hargs⟩
  rcases decoder_input _ pre args suffix hD hr hz hlen hv (by rw [hop]; rfl) with
    ⟨u, hsub, hin, hil, hge⟩ | hw | he | hst
  · left
    refine ⟨u, hsub, ?_⟩
    rw [hin, hil]
    exact equalTo_iff value hge
  · exact .inr (.inl hw)
  · exact .inr (.inr (.inl he))
  · exact .inr (.inr (.inr hst))

end ConditionCheck
