import ConditionCheck.Stored
import ConditionPacking.Bytes

/-!
# What the comparison operators decide

Transcribes the comparison branch of `ConditionEvaluator.evaluate`
(`__compare`, `__compareSigned`, for `EqualTo`, `GreaterThan`, `LessThan`,
`SignedIntGreaterThan`, `SignedIntLessThan`) on top of `__input`, and states
what it decides about the value the decoder proof says the node reads.

keccak256 is a parameter `keccak : Bytes → Nat`. `__compare` compares a
32-byte value as the word itself and a longer one by its hash. The `EqualTo`
theorems assume no other value of the operand's length class (32 bytes, or
longer) has the compValue's key (`CollisionFree`): for 32 bytes that is a
theorem (`collisionFree_word`), for longer ones it is keccak256's
second-preimage resistance. Across classes no such assumption could hold (a
32-byte value can be any hash), so the theorems ask the operand and the
compValue to be of one class (`SameClass`).
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

/-- Both 32 bytes (compared as words), or both longer (compared by hash). -/
def SameClass (x y : Bytes) : Prop := (x.length = 32 ↔ y.length = 32)

/-- No other byte string of its class has `cv`'s key: for a longer `cv`,
    keccak256 has no second preimage of it. -/
def CollisionFree (keccak : Bytes → Nat) (cv : Bytes) : Prop :=
  ∀ x : Bytes, SameClass x cv → key keccak x = key keccak cv → x = cv

theorem bytes32_of_length {cv : Bytes} (h : cv.length = 32) : bytes32 cv = wordVal cv := by
  unfold bytes32
  rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]

theorem cvKey_eq_key (keccak : Bytes → Nat) {cv : Bytes} (h : 32 ≤ cv.length) :
    cvKey keccak cv = key keccak cv := by
  unfold cvKey key
  by_cases h32 : cv.length = 32
  · simp [h32, bytes32_of_length h32]
  · simp [show cv.length > 32 by omega, h32]

/-- Words need no assumption. -/
theorem collisionFree_word (keccak : Bytes → Nat) {cv : Bytes} (h : cv.length = 32) :
    CollisionFree keccak cv := by
  intro x hx hk
  have hx32 : x.length = 32 := hx.2 h
  unfold key at hk
  rw [if_pos hx32, if_pos h] at hk
  rw [← ConditionPacking.natBE_wordVal x, ← ConditionPacking.natBE_wordVal cv, hx32, h, hk]

theorem inputVal_expect (keccak : Bytes → Nat) (value : Nat) (bs : Bytes) :
    inputVal keccak value (expectInput bs) = some (key keccak bs) := by
  unfold expectInput key
  split <;> rfl

/-- **`EqualTo` on a parameter.** It passes exactly when the parameter's spec
    encoding equals the (stored) compValue. -/
theorem equalTo_iff {keccak : Bytes → Nat} {cv : Bytes} (hk : CollisionFree keccak cv) (value : Nat)
    {u : Val} (hcv : 32 ≤ cv.length) (hcl : SameClass (enc u) cv) :
    comparePasses keccak value (expectInput (enc u)) .EqualTo cv = true ↔ enc u = cv := by
  unfold comparePasses
  rw [inputVal_expect keccak value, cvKey_eq_key keccak hcv]
  simp only [beq_iff_eq]
  exact ⟨hk _ hcl, fun h => by rw [h]⟩

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
theorem equalTo_intended {keccak : Bytes → Nat} {u v : Val} (hk : CollisionFree keccak (enc v))
    (value : Nat) (hv : 32 ≤ (enc v).length) (hcl : SameClass (enc u) (enc v)) :
    comparePasses keccak value (expectInput (enc u)) .EqualTo (storedCv v) = true ↔
      enc u = enc v := by
  rw [storedCv_eq]; exact equalTo_iff hk value hv hcl

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
    passes exactly when its operand's spec encoding equals its compValue
    (when the two are of one length class, which the check ensures for a
    static operand: its compValue has exactly its size), unless it reads a
    `Slice` window, the ether value, or sits in an interpretation that does
    not fit (only with `s = true`). -/
theorem checked_equalTo {keccak : Bytes → Nat} (value : Nat)
    {s : Bool} {fs : List ConditionPacking.Flat} {lb : Nat} {ts : List Ty} {o : Bool}
    (h : checkStored s fs = some (.typed (.call lb ts o))) (avatar : Bytes)
    {pre : Bytes} {args : List Val} (hpre : pre.length = lb)
    (hargs : if o then HasTPre s args ts else HasTAll s args ts)
    (suffix : Bytes) (hlen : (calldata pre args suffix).length < 2 ^ 255)
    {p : List Nat} {d : Condition} {l : Nat}
    (hv : Eval (calldata pre args suffix) (annotate (ConditionPacking.rawTree avatar fs 0)) p d l)
    (hop : d.operator = .EqualTo) (hcv : 32 ≤ d.compValue.length) (hk : CollisionFree keccak d.compValue) :
    (∃ u, (Val.call pre args).sub p = some u ∧ (SameClass (enc u) d.compValue →
      (comparePasses keccak value (input (calldata pre args suffix) l d) .EqualTo d.compValue = true ↔
        enc u = d.compValue))) ∨
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
    refine ⟨u, hsub, fun hcl => ?_⟩
    rw [hin]
    exact equalTo_iff hk value hcv hcl
  · exact .inr (.inl hw)
  · exact .inr (.inr (.inl he))
  · exact .inr (.inr (.inr hst))

end ConditionCheck
