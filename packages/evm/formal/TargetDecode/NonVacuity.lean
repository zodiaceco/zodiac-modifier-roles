import TargetDecode.Walk
import DecoderFaithfulness.Example

/-!
# Non-vacuity of the target-decoding hypotheses

`ex_full`: on `ex_LPCall`'s non-canonical layout (`f(bytes, bytes)`, tails
reversed), solc's decoder model accepts; a strict (`s = false`) tree
`Matches[EqualTo(bytes), EqualTo(bytes)]` describes the arguments; the
evaluator really visits the second leaf at byte 68 (where its tail is); and
`target_input` applies to it.

(The statement review that added this file also found that `InStrayL` did
not tie the interpretation to the tree, so with `s = true` every reached
node satisfied case (iv). `InStrayL` now requires the walk to reach a node
of the tree that does not describe the bytes value, where the target reads
that value.)

No `native_decide`.
-/

namespace TargetDecode.NonVacuity
open DecoderFaithfulness DecoderFaithfulness.Roles TargetDecode

/-! ## 1. All hypotheses hold on a non-canonical layout -/

set_option maxRecDepth 100000 in
/-- solc's decoder (the model) accepts the reversed-tail layout. -/
theorem ex_decode : (decodeCall exData 4 [.bytes, .bytes]).isSome = true := by
  have h4 : ¬ exData.length < 4 := by decide +kernel
  simp only [decodeCall, h4, ite_false]
  simp only [decodeBlock, decode, STy.headSize, STy.isStatic, STy.isWord, STy.depthAll, STy.depth]
  decide +kernel

theorem ex_LPCall' : ∃ args, LPCall exData (exData.take 4) args := by
  obtain ⟨args, h⟩ := Option.isSome_iff_exists.mp ex_decode
  exact ⟨args, decodeCall_LPCall h⟩

def leafD : Condition := ⟨.Dynamic, .EqualTo, [], false, 0, 0, []⟩
def rootT : Condition := ⟨.AbiEncoded, .Matches, [leafD, leafD], false, 0, 4, []⟩

theorem rootT_desc : Desc false rootT (.call exSel exArgs) :=
  .call rfl rfl (by simp [rootT]) (by simp [rootT, exArgs])
    (.cons (.desc (.bytes rfl rfl rfl trivial)) (.cons (.desc (.bytes rfl rfl rfl trivial)) .nil))
    (.inl rfl)

theorem annotate_rootT : annotate rootT = rootT := by
  simp [rootT, leafD, annotate_eq, isInlined_eq]

set_option maxRecDepth 100000 in
/-- Roles finds `a`'s tail at 132 and `b`'s at 68 (reversed). -/
theorem children_rootT : children exData 4 rootT = some [132, 68] := by decide +kernel

theorem visit_b : Eval exData (annotate rootT) [1] leafD 68 := by
  rw [annotate_rootT]
  exact .visit (.matchesChild [132, 68] 1 (by decide) rfl (by exact children_rootT) rfl .here)

/-- `target_input` applies with every hypothesis discharged, in strict mode. -/
example := target_input rootT_desc (.abi rfl) (.of_noZip rfl) ex_LPCall
  (by decide +kernel) visit_b rfl

/-- And it is the informative case: the node describes `b = [2]`, read at 68. -/
example : LP exData 68 (.bytes [2]) := .bytes (by decide +kernel) (by decide +kernel)
  ⟨by decide +kernel, by decide +kernel⟩

end TargetDecode.NonVacuity
