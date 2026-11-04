import ConditionPacking.Main
import ConditionCheck.Flat

/-!
# Non-vacuity of `pack_roundtrip`

`Packable` holds on non-trivial arrays (several levels, a non-inlined
`EqualTo`, Plucks), and the right-hand side `rawTree` is the expected tree.
`packableB = true` (from `ConditionCheck.Flat`) implies `Packable`
(`packableB_sound`).
-/

namespace ConditionPacking.NonVacuity
open ConditionPacking DecoderFaithfulness DecoderFaithfulness.Roles

def w32 (n : Byte) : Bytes := List.replicate 31 (0 : Byte) ++ [n]

/-- `f(uint256 a, bytes b)`: `Matches[EqualTo(7), EqualTo(abi.encode(""))]`. -/
def fs1 : List Flat :=
  [ ⟨0, .AbiEncoded, .Matches, []⟩,
    ⟨0, .Static, .EqualTo, w32 7⟩,
    ⟨0, .Dynamic, .EqualTo, w32 0x20 ++ w32 0⟩ ]

theorem packable1 : Packable fs1 := ConditionCheck.packableB_sound (by decide +kernel)

/-- `root3` of the decoder proof as a flat array: three levels, Plucks, a Zip. -/
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

theorem packable2 : Packable fs2 := ConditionCheck.packableB_sound (by decide +kernel)

/-- The tree on the right-hand side is the intended one: the root has the two
    parameters, the `AbiEncoded` default leading bytes are 4, and the
    non-inlined `EqualTo` lost its offset word. -/
example : (rawTree (w32 9) fs1 0).children.length = 2 := by decide +kernel
example : (rawTree (w32 9) fs1 0).leadingBytes = 4 := by decide +kernel
example : ((rawTree (w32 9) fs1 0).children.map (·.compValue)) = [w32 7, w32 0] := by
  decide +kernel
example : maxPluck fs2 = 2 := by decide
example :
    ((rawTree (w32 9) fs2 0).children.map (·.children.length)) = [2, 1] := by decide +kernel

/-- A non-packable array (1-byte `AbiEncoded` compValue) is rejected. -/
example : ConditionCheck.packableB [⟨0, .AbiEncoded, .Matches, [0]⟩] = false := by decide +kernel

/-- So the round trip applies to `fs2` for every avatar and memory. -/
example (avatar : Bytes) (junk junk' : Mem) :
    unpack avatar (bufMem (pack junk fs2) junk') =
      some (annotate (rawTree avatar fs2 0), 2) := by
  rw [pack_roundtrip avatar junk junk' fs2 packable2]; rfl

end ConditionPacking.NonVacuity
