import ConditionCheck.Stored
import ConditionCheck.Compare

/-!
# Non-vacuity of `checkStored_sound`

Concrete flat arrays that `checkStored` accepts (so `Packable`,
`assigned` and `checkCondition` hold on non-trivial inputs), calldata that
satisfies the `HasT`/`Strict` hypotheses of the typed conclusion, and a
`Run` that does end in `bad` on a tree the slot rule rejects (so
`o ≠ .bad` is not trivially true of `Run`).
-/

namespace ConditionCheck.NonVacuity
open ConditionCheck DecoderFaithfulness DecoderFaithfulness.Roles
open ConditionPacking (Flat Packable)

def w32 (n : Byte) : Bytes := List.replicate 31 (0 : Byte) ++ [n]

/-- `f(uint256 a, bytes b)`: `Matches[EqualTo(a = 7), EqualTo(b = "")]`.
    The `Dynamic` `EqualTo` compValue is `abi.encode(bytes(""))`
    (offset word, length word). -/
def fs1 : List Flat :=
  [ ⟨0, .AbiEncoded, .Matches, []⟩,
    ⟨0, .Static, .EqualTo, w32 7⟩,
    ⟨0, .Dynamic, .EqualTo, w32 0x20 ++ w32 0⟩ ]

example : checkStored false fs1 = some (.typed (.call 4 [.static, .dynamic] true)) := by
  decide +kernel
example : checkStored true fs1 = some (.typed (.call 4 [.static, .dynamic] true)) := by
  decide +kernel

/-- `Packable` (the hypothesis of `pack_roundtrip`) holds on a 3-node array. -/
example : Packable fs1 := packableB_sound (by decide +kernel)

/-- `f(uint256[] a, uint256[] b)`:
    `And[Matches[Pluck₀ Array[Static], Pluck₁ Array[Static]], ZipEvery₀,₁[Matches[EqualTo, Pass]]]`
    (the decoder proof's `root3`, as a flat array). -/
def fs2 : List Flat :=
  [ ⟨0, .None, .And, []⟩,
    ⟨0, .AbiEncoded, .Matches, []⟩,
    ⟨0, .None, .ZipEvery, [0, 1]⟩,
    ⟨1, .Array, .Pluck, [0]⟩,
    ⟨1, .Array, .Pluck, [1]⟩,
    ⟨2, .Tuple, .Matches, []⟩,
    ⟨3, .Static, .Pass, []⟩,
    ⟨4, .Static, .Pass, []⟩,
    ⟨5, .Static, .EqualTo, w32 1⟩,
    ⟨5, .Static, .Pass, []⟩ ]

example : checkStored false fs2 =
    some (.typed (.call 4 [.array .static, .array .static] true)) := by
  decide +kernel

/-- The same with the Zip before the `Matches` (no Pluck has run yet when
    the Zip reads its slots): rejected. -/
def fs2bad : List Flat :=
  [ ⟨0, .None, .And, []⟩,
    ⟨0, .None, .ZipEvery, [0, 1]⟩,
    ⟨0, .AbiEncoded, .Matches, []⟩,
    ⟨1, .Tuple, .Matches, []⟩,
    ⟨2, .Array, .Pluck, [0]⟩,
    ⟨2, .Array, .Pluck, [1]⟩,
    ⟨3, .Static, .EqualTo, w32 1⟩,
    ⟨3, .Static, .Pass, []⟩,
    ⟨4, .Static, .Pass, []⟩,
    ⟨5, .Static, .Pass, []⟩ ]

example : checkStored false fs2bad = none := by decide +kernel
example : checkStored true fs2bad = none := by decide +kernel

/-- `Run` can end in `bad`: a Zip reading unwritten slots. So the conclusion
    `o ≠ .bad` of `checkStored_sound` is not true of every `Run`. -/
example : Run (Example.zipNode) (fun _ => false) .bad (fun _ => false) :=
  .zipBad (.inr rfl) (by decide)

/-- The typed conclusion's hypotheses hold on real calldata:
    `f(7, "")` with a 4-byte selector has type `call 4 [static, dynamic] true`
    and is `Strict`, in both modes. -/
def pre1 : Bytes := [0xde, 0xad, 0xbe, 0xef]
def args1 : List Val := [.word (w32 7), .bytes []]

theorem hasT1 (s : Bool) : HasT s (.call pre1 args1) (.call 4 [.static, .dynamic] true) := by
  refine .inr ⟨4, [.static, .dynamic], true, rfl, .inl ⟨rfl, ?_⟩⟩
  simp only [ite_true, args1]
  exact ⟨⟨rfl, rfl⟩, .inl rfl, trivial⟩

theorem strict1 (s : Bool) : Strict s (.call pre1 args1) (.call 4 [.static, .dynamic] true) := by
  refine ⟨pre1, args1, rfl, rfl, ?_⟩
  simp only [ite_true, args1]
  exact ⟨⟨rfl, rfl⟩, .inl rfl, trivial⟩

/-- So `checkStored_sound` yields `Desc` for a concrete calldata. -/
example (avatar : Bytes) : Desc false (ConditionPacking.rawTree avatar fs1 0) (.call pre1 args1) := by
  have h : checkStored false fs1 = some (.typed (.call 4 [.static, .dynamic] true)) := by
    decide +kernel
  have := checkStored_sound h avatar (fun _ => 0) (fun _ => 0)
  exact this.2.2.2.2.2 pre1 args1 (hasT1 false) (strict1 false)

/-- With `s = false`, a calldata whose `bytes` argument is replaced by a word
    does not have the type: `HasT` is not trivially true. -/
example : ¬ HasT false (.call pre1 [.word (w32 7), .word (w32 0)])
    (.call 4 [.static, .dynamic] true) := by
  simp [HasT, HasTPre, pre1]

end ConditionCheck.NonVacuity

#print axioms ConditionCheck.checkStored_sound
#print axioms ConditionCheck.checkCondition_sound
#print axioms ConditionCheck.assigned_no_bad
#print axioms ConditionCheck.run_sound
#print axioms ConditionCheck.packableB_sound
#print axioms ConditionCheck.checkCondition_avatar
#print axioms ConditionCheck.ns_root_input
#print axioms ConditionCheck.stored_input
#print axioms ConditionCheck.checked_input
#print axioms ConditionCheck.equalTo_iff
#print axioms ConditionCheck.equalTo_intended
#print axioms ConditionCheck.compare_word
#print axioms ConditionCheck.checked_equalTo
#print axioms ConditionPacking.pack_roundtrip
#print axioms ConditionPacking.packBuffer_eq
