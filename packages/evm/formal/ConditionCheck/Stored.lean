import ConditionCheck.Ops
import ConditionCheck.Slots
import ConditionCheck.EndToEnd

/-!
# The check on what a `...Packed` setter stores

`checkStored s fs` is the full check for a flat condition array `fs`, the
specification for the SDK:

* `packableB`: `Packable` (BFS order, field widths, compValue shapes);
* `opsOk`: Integrity's per-operator rules;
* `assigned`: every slot a Zip or `WithinRatio` reads is written first;
* `checkCondition` (a typed root), or a root that reads no calldata.

`checkStored_sound` collects what this guarantees, for any avatar and any
memory around the buffers.
-/

namespace ConditionCheck
open DecoderFaithfulness DecoderFaithfulness.Roles
open ConditionPacking (Flat rawTree Packable)

inductive Verdict where
  /-- The root describes calldata of this type. -/
  | typed (t : Ty)
  /-- The root reads no calldata (e.g. only `EtherValue` checks). -/
  | noCalldata
  deriving DecidableEq

/-- The tree the check runs on (the avatar does not matter, see
    `checkCondition_avatar`). -/
def treeOf (fs : List Flat) : Condition := rawTree (zeros 32) fs 0

def checkStored (s : Bool) (fs : List Flat) : Option Verdict :=
  if packableB fs && opsOk fs && (assigned (treeOf fs) fun _ => false).isSome then
    match checkCondition s (treeOf fs) with
    | some t => some (.typed t)
    | none => if classify s (treeOf fs) = some .ns then some .noCalldata else none
  else none

/-- **What the check guarantees.** For every avatar and memory contents:
    packing and unpacking `fs` returns its tree; no execution reads an
    unwritten Pluck slot; and either the decoder theorems' hypotheses hold
    for every calldata of the root's type, or `evaluate` reads no calldata. -/
theorem checkStored_sound {s : Bool} {fs : List Flat} {v : Verdict}
    (h : checkStored s fs = some v) (avatar : Bytes) (junk junk' : ConditionPacking.Mem) :
    let root := rawTree avatar fs 0
    Packable fs ∧
    ConditionPacking.unpack avatar (ConditionPacking.bufMem (ConditionPacking.pack junk fs) junk') =
      some (annotate root, ConditionPacking.maxPluck fs) ∧
    (∀ o A', Run (annotate root) (fun _ => false) o A' → o ≠ .bad) ∧
    match v with
    | .typed t => RootOK root ∧ ZipOK s root ∧
        ∀ pre args, HasT s (.call pre args) t → Strict s (.call pre args) t →
          Desc s root (.call pre args)
    | .noCalldata => ∀ data p d l, Eval data (annotate root) p d l → input data l d = .etherValue := by
  intro root
  unfold checkStored at h
  split at h
  · rename_i hc
    simp only [Bool.and_eq_true] at hc
    obtain ⟨⟨hp, _⟩, ha⟩ := hc
    have hP := packableB_sound hp
    obtain ⟨B, hB⟩ := Option.isSome_iff_exists.mp ha
    have hB' : assigned (annotate root) (fun _ => false) = some B := by
      rw [assigned_annotate, assigned_avatar avatar (zeros 32)]; exact hB
    refine ⟨hP, ConditionPacking.pack_roundtrip avatar junk junk' fs hP,
      fun o A' hrun => assigned_no_bad hB' hrun, ?_⟩
    split at h
    · rename_i t ht
      simp only [Option.some.injEq] at h; subst h
      rw [treeOf, ← checkCondition_avatar s avatar] at ht
      exact checkCondition_sound ht
    · split at h
      · rename_i hns
        simp only [Option.some.injEq] at h; subst h
        rw [treeOf, ← classify_avatar s avatar] at hns
        exact fun data p d l hv => ns_root_input hns hv
      · cases h
  · cases h

end ConditionCheck
