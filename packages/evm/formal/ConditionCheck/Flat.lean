import ConditionCheck.Sound
import ConditionPacking.Main

/-!
# The check on the flat array

The SDK stores a flat `ConditionFlat[]` array `fs`. `packableB fs` decides
`ConditionPacking.Packable fs` (the hypothesis of `pack_roundtrip`), and the
tree check runs on `rawTree avatar fs 0`, the tree the array describes.

`rawTree` puts the avatar into `EqualToAvatar` compValues, and the avatar can
change after the tree is stored. `checkCondition_avatar` shows the check does
not depend on it: it only reads the compValues of `Slice`, `Pluck` and Zip
nodes (`skel` clears all others).
-/

namespace ConditionCheck
open DecoderFaithfulness DecoderFaithfulness.Roles
open ConditionPacking (Flat at! shapes childBounds kids rawTree Packable BFS)

/-! ## `Packable`, decided -/

/-- `Packable`, with the per-node conditions under one bounded quantifier. -/
def PackableP (fs : List Flat) : Prop :=
  0 < fs.length ∧ fs.length ≤ 65535 ∧
  ∀ j, j < fs.length →
    (0 < j → (at! fs j).parent < j) ∧
    (0 < j → j + 1 < fs.length → (at! fs j).parent ≤ (at! fs (j + 1)).parent) ∧
    (at! fs j).compValue.length ≤ 65535 ∧
    (childBounds (shapes fs) j).2 ≤ 1023 ∧
    (ConditionPacking.isInlined (shapes fs) j = true →
      ConditionPacking.inlinedSize (shapes fs) j ≤ 8191) ∧
    ((at! fs j).operator = .Pluck →
      (at! fs j).compValue ≠ [] ∧ ((at! fs j).compValue.headD 0).val ≤ 254) ∧
    ((at! fs j).operator = .EqualTo → ConditionPacking.isInlined (shapes fs) j = false →
      32 ≤ (at! fs j).compValue.length) ∧
    ((at! fs j).paramType = .AbiEncoded →
      (at! fs j).compValue.length ≠ 1 ∧ (at! fs j).operator ≠ .EqualTo)

instance (fs : List Flat) : Decidable (PackableP fs) := by unfold PackableP; infer_instance

def packableB (fs : List Flat) : Bool := decide (PackableP fs)

theorem packableB_sound {fs : List Flat} (h : packableB fs = true) : Packable fs := by
  have h := of_decide_eq_true h
  obtain ⟨h0, h1, h⟩ := h
  exact
    { nonempty := h0
      node_count := h1
      bfs := ⟨fun j hj hl => (h j hl).1 hj, fun j hj hl => (h j (by omega)).2.1 hj hl⟩
      comp_value_length := fun j hj => (h j hj).2.2.1
      child_count := fun j hj => (h j hj).2.2.2.1
      inlined_size := fun j hj => (h j hj).2.2.2.2.1
      pluck := fun j hj => (h j hj).2.2.2.2.2.1
      equal_to := fun j hj => (h j hj).2.2.2.2.2.2.1
      abi_encoded := fun j hj => (h j hj).2.2.2.2.2.2.2 }

/-! ## The compValues the check reads -/

def keepsCv (op : Operator) : Bool :=
  op == .Slice || op == .Pluck || op == .ZipSome || op == .ZipEvery || op == .WithinRatio

mutual
  /-- The tree with every compValue the check ignores cleared. -/
  def skel : Condition → Condition
    | ⟨e, op, cs, _, _, lb, cv⟩ => ⟨e, op, skelAll cs, false, 0, lb, if keepsCv op then cv else []⟩

  def skelAll : List Condition → List Condition
    | [] => []
    | c :: cs => skel c :: skelAll cs
end

theorem skelAll_eq : ∀ cs : List Condition, skelAll cs = cs.map skel
  | [] => rfl
  | c :: cs => by simp [skelAll, skelAll_eq cs]

@[simp] theorem skel_encoding (c : Condition) : (skel c).encoding = c.encoding := by
  cases c; simp [skel]
@[simp] theorem skel_operator (c : Condition) : (skel c).operator = c.operator := by
  cases c; simp [skel]
@[simp] theorem skel_leadingBytes (c : Condition) : (skel c).leadingBytes = c.leadingBytes := by
  cases c; simp [skel]
@[simp] theorem skel_children (c : Condition) : (skel c).children = c.children.map skel := by
  cases c; simp [skel, skelAll_eq]
theorem skel_compValue (c : Condition) :
    (skel c).compValue = if keepsCv c.operator then c.compValue else [] := by
  cases c; simp [skel]

theorem skel_default : skel default = default := rfl

mutual
  theorem exactTy_skel : ∀ c : Condition, exactTy (skel c) = exactTy c
    | ⟨e, op, cs, i, sz, lb, cv⟩ => by simp only [skel, exactTy, exactTyAll_skel cs]
  theorem exactTyAll_skel : ∀ cs : List Condition, exactTyAll (skelAll cs) = exactTyAll cs
    | [] => rfl
    | c :: cs => by simp only [skelAll, exactTyAll, exactTy_skel c, exactTyAll_skel cs]
end

theorem classifyNode_congr {s : Bool} {e : Encoding} {op : Operator} {cs cs' : List Condition}
    {lb : Nat} {cv cv' : Bytes} {ks : List K}
    (hcs : cs'.map (·.encoding) = cs.map (·.encoding)) (hcv : op = .Slice → cv' = cv)
    (hnn : exactTyAll cs' = exactTyAll cs) :
    classifyNode s e op cs' lb cv' ks = classifyNode s e op cs lb cv ks := by
  have hl : cs'.isEmpty = cs.isEmpty := by
    have := congrArg List.length hcs
    simp only [List.length_map] at this
    cases cs <;> cases cs' <;> simp_all
  by_cases hop : op = .Slice
  · rw [hcv hop]
    unfold classifyNode leafOk sliceOk
    rw [hl, hcs, hnn]
  · have hs : ∀ c c' : Bytes, sliceOk op cs' c' ks = sliceOk op cs c ks := by
      have hb : (op == Operator.Slice) = false := by simp [hop]
      intro c c'; simp [sliceOk, hb]
    unfold classifyNode leafOk
    rw [hl, hs cv cv', hnn]

theorem classify_skel (s : Bool) (c : Condition) : classify s (skel c) = classify s c := by
  have hall : classifyAll s (c.children.map skel) = classifyAll s c.children := by
    have : ∀ cs : List Condition, (∀ ch, ch ∈ cs → classify s (skel ch) = classify s ch) →
        classifyAll s (cs.map skel) = classifyAll s cs := by
      intro cs
      induction cs with
      | nil => intro _; rfl
      | cons a cs ih =>
        intro h
        simp only [List.map_cons, classifyAll, h a (by simp), ih fun ch hm => h ch (by simp [hm])]
    exact this _ fun ch hm => classify_skel s ch
  rw [classify_eq, classify_eq, skel_children, hall, skel_encoding, skel_operator,
    skel_leadingBytes]
  congr 1
  funext ks
  apply classifyNode_congr
  · simp [List.map_map, Function.comp_def]
  · intro hop; rw [skel_compValue, hop]; rfl
  · rw [← skelAll_eq]; exact exactTyAll_skel _
termination_by sizeOf c
decreasing_by exact sizeOf_child hm

theorem rootOk_skel (s : Bool) (c : Condition) : rootOk s (skel c) = rootOk s c := by
  have hall : rootOkAll s (c.children.map skel) = rootOkAll s c.children := by
    have : ∀ cs : List Condition, (∀ ch, ch ∈ cs → rootOk s (skel ch) = rootOk s ch) →
        rootOkAll s (cs.map skel) = rootOkAll s cs := by
      intro cs
      induction cs with
      | nil => intro _; rfl
      | cons a cs ih =>
        intro h
        simp only [List.map_cons, rootOkAll, h a (by simp), classify_skel,
          ih fun ch hm => h ch (by simp [hm])]
    exact this _ fun ch hm => rootOk_skel s ch
  rw [rootOk_eq, rootOk_eq, skel_children, hall, skel_encoding, skel_operator]
termination_by sizeOf c
decreasing_by exact sizeOf_child hm

mutual
  theorem nodes_skel : ∀ c : Condition, Example.nodes (skel c) = (Example.nodes c).map skel
    | ⟨e, op, cs, i, sz, lb, cv⟩ => by
      simp only [skel, Example.nodes, List.map_cons, nodesAll_skel cs]

  theorem nodesAll_skel : ∀ cs : List Condition,
      Example.nodesAll (skelAll cs) = (Example.nodesAll cs).map skel
    | [] => rfl
    | c :: cs => by
      simp only [skelAll, Example.nodesAll, List.map_append, nodes_skel c, nodesAll_skel cs]
end

theorem zipFields_skel (z : Condition) : zipFields (skel z) = (zipFields z).map skel := by
  unfold zipFields
  rw [skel_children]
  cases z.children with
  | nil => simp only [List.map_nil, List.headD_nil, skel_children]; rfl
  | cons a _ => simp

theorem getD_map_skel (l : List Condition) (f : Nat) :
    (l.map skel).getD f default = skel (l.getD f default) := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[f]? with
  | none => simp [skel_default]
  | some x => simp

theorem headD_map_skel (l : List Condition) :
    (l.map skel).headD default = skel (l.headD default) := by
  cases l with
  | nil => simp [skel_default]
  | cons a _ => simp

theorem zipFieldOk_skel (s : Bool) (l : List Condition) (z : Condition) (f : Nat)
    (hz : z.operator = .ZipSome ∨ z.operator = .ZipEvery) :
    zipFieldOk s (l.map skel) (skel z) f = zipFieldOk s l z f := by
  have hzc : (skel z).compValue = z.compValue := by
    rw [skel_compValue]; rcases hz with hz | hz <;> simp [hz, keepsCv]
  unfold zipFieldOk
  rw [List.all_map]
  apply List.all_congr rfl
  intro pk
  simp only [Function.comp_apply, skel_operator, skel_encoding, skel_children,
    headD_map_skel, getD_map_skel, classify_skel, zipFields_skel, hzc]
  by_cases hp : pk.operator = .Pluck
  · simp [skel_compValue, hp, keepsCv]
  · have hb : (pk.operator == Operator.Pluck) = false := by simp [hp]
    simp [hb]

theorem zipCheck_skel (s : Bool) (c : Condition) : zipCheck s (skel c) = zipCheck s c := by
  unfold zipCheck
  rw [nodes_skel, List.all_map]
  apply List.all_congr rfl
  intro z
  rw [Function.comp_apply, skel_operator, zipFields_skel, List.length_map]
  by_cases hz : z.operator = .ZipSome ∨ z.operator = .ZipEvery
  · congr 1
    apply List.all_congr rfl
    intro f
    exact zipFieldOk_skel s _ z f hz
  · simp only [not_or] at hz
    have h1 : (z.operator == Operator.ZipSome) = false := by simp [hz.1]
    have h2 : (z.operator == Operator.ZipEvery) = false := by simp [hz.2]
    simp [h1, h2]

theorem checkCondition_skel (s : Bool) (c : Condition) :
    checkCondition s (skel c) = checkCondition s c := by
  unfold checkCondition
  rw [classify_skel, rootOk_skel, zipCheck_skel]

theorem skel_rawTree (a b : Bytes) (fs : List Flat) (i : Nat) :
    skel (rawTree a fs i) = skel (rawTree b fs i) := by
  rw [ConditionPacking.rawTree_eq a, ConditionPacking.rawTree_eq b]
  simp only [skel, skelAll_eq, List.map_map]
  congr 1
  · apply List.map_congr_left
    intro j hj
    have := (ConditionPacking.mem_kids hj).1
    exact skel_rawTree a b fs j
  · by_cases h : (at! fs i).operator = .EqualToAvatar
    · simp [h, keepsCv]
    · simp [h]
termination_by fs.length - i
decreasing_by
  have := ConditionPacking.mem_kids hj
  omega

/-- The check does not depend on the avatar. -/
theorem checkCondition_avatar (s : Bool) (a b : Bytes) (fs : List Flat) :
    checkCondition s (rawTree a fs 0) = checkCondition s (rawTree b fs 0) := by
  rw [← checkCondition_skel, skel_rawTree a b, checkCondition_skel]

theorem classify_avatar (s : Bool) (a b : Bytes) (fs : List Flat) :
    classify s (rawTree a fs 0) = classify s (rawTree b fs 0) := by
  rw [← classify_skel, skel_rawTree a b, classify_skel]

end ConditionCheck

namespace ConditionCheck
open DecoderFaithfulness DecoderFaithfulness.Roles

/-! ## Roots that read no calldata -/

theorem NonStruct.not_zipOp {c : Condition} (h : NonStruct c) :
    c.operator ≠ .ZipSome ∧ c.operator ≠ .ZipEvery := by
  cases h with
  | leaf _ _ hnav => constructor <;> intro hop <;> rw [hop] at hnav <;> simp [isNavOp] at hnav
  | logical _ hop _ => rcases hop with hop | hop <;> rw [hop] <;> simp

/-- A non-structural root (e.g. only `EtherValue` checks): `evaluate` only
    reaches non-structural nodes, at no component. -/
theorem ns_root_eval {s : Bool} {root : Condition} (h : classify s root = some .ns)
    {data : Bytes} {p : List Nat} {d : Condition} {l : Nat}
    (hv : Eval data (annotate root) p d l) : ∃ d0, d = annotate d0 ∧ NonStruct d0 := by
  induction hv with
  | visit hvis => exact (NonStruct.visit hvis rfl (ns_sound s root h)).2
  | zip _ _ _ _ _ hzop _ _ _ _ _ _ ihz _ =>
    obtain ⟨z0, rfl, hns⟩ := ihz
    have := NonStruct.not_zipOp hns
    rcases hzop with hzop | hzop
    · exact absurd (annotate_op_of hzop (by decide)) this.1
    · exact absurd (annotate_op_of hzop (by decide)) this.2

/-- ... and every node that reads `__input` reads the ether value. -/
theorem ns_root_input {s : Bool} {root : Condition} (h : classify s root = some .ns)
    {data : Bytes} {p : List Nat} {d : Condition} {l : Nat}
    (hv : Eval data (annotate root) p d l) : input data l d = .etherValue := by
  obtain ⟨d0, rfl, hns⟩ := ns_root_eval h hv
  unfold input
  rw [annotate_encoding]
  cases hns with
  | leaf he _ _ => rcases he with he | he <;> simp [he]
  | logical he _ _ => simp [he]

end ConditionCheck
