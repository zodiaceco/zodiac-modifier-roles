import Bridge.Final
import ConditionPacking.Main

/-!
# The SDK pipeline, end to end

The SDK normalizes a tree, flattens it (BFS) and packs it; the contract
unpacks the buffer and evaluates. `sdk_pipeline`: for a well-typed tree
(`inv`, which the SDK check enforces), on every calldata, whenever the
contract's evaluation of the tree it unpacks from the stored buffer does
not revert, it computes the contract's reading of the tree as the user wrote
it: it passes exactly when that reading does, with the same allowance
consumptions and Pluck slots. A revert denies the call.

The flat array is related to the normalized tree by `nest` (read the tree
back from the array: node `i`'s children are the later nodes whose parent is
`i`). That the SDK's `flattenCondition` produces an array that reads back as
its input is a property of the SDK (tested, through the Lean driver's
`buildCond`, by the normalization and check differential tests).
-/

namespace Bridge
open DecoderFaithfulness DecoderFaithfulness.Roles Normalize Evaluate ConditionPacking

/-- The SDK tree a flat array describes, from node `i`. -/
def nest (fs : List Flat) (i : Nat) : Cond :=
  ⟨encCode (at! fs i).paramType, opCode (at! fs i).operator, (at! fs i).compValue.map (·.val),
    (kids fs i).attach.map fun ⟨j, _⟩ => nest fs j⟩
termination_by fs.length - i
decreasing_by
  rename_i hj
  have := mem_kids hj
  omega

theorem nest_eq (fs : List Flat) (i : Nat) :
    nest fs i = ⟨encCode (at! fs i).paramType, opCode (at! fs i).operator,
      (at! fs i).compValue.map (·.val), (kids fs i).map (nest fs)⟩ := by
  rw [nest]; simp only [ConditionPacking.attach_map' (kids fs i) (nest fs)]

theorem toBytes_val (cv : Bytes) : toBytes (cv.map (·.val)) = cv := by
  induction cv with
  | nil => rfl
  | cons b bs ih =>
    simp only [List.map_cons, toBytes, List.cons.injEq] at ih ⊢
    exact ⟨Fin.ext (Nat.mod_eq_of_lt b.isLt), ih⟩

theorem encN_code (e : Encoding) : encN (encCode e) = e := by cases e <;> rfl

theorem opN_code (o : Operator) : opN (opCode o) = if o = .EqualToAvatar then .EqualTo else o := by
  cases o <;> rfl

theorem toRoles_nest (avatar : Bytes) (fs : List Flat) (i : Nat) :
    toRoles avatar (nest fs i) =
      ⟨encN (encCode (at! fs i).paramType), opN (opCode (at! fs i).operator),
        (kids fs i).map (fun j => toRoles avatar (nest fs j)), false, 0, lbOf (nest fs i),
        cvOf avatar (nest fs i)⟩ := by
  have he : (nest fs i).enc = encCode (at! fs i).paramType := by rw [nest_eq]
  have ho : (nest fs i).op = opCode (at! fs i).operator := by rw [nest_eq]
  have hc : (nest fs i).ch = (kids fs i).map (nest fs) := by rw [nest_eq]
  rw [toRoles_eq, he, ho, hc, List.map_map]; rfl

/-- The raw layout of the unpacked tree and of the tree read back agree. -/
theorem raw_nest (avatar : Bytes) (fs : List Flat) (i : Nat) :
    Roles.isInlined (rawTree avatar fs i) = Roles.isInlined (toRoles avatar (nest fs i)) ∧
      Roles.inlinedSize (rawTree avatar fs i) = Roles.inlinedSize (toRoles avatar (nest fs i)) := by
  have ih : ∀ j ∈ kids fs i, Roles.isInlined (rawTree avatar fs j) = Roles.isInlined (toRoles avatar (nest fs j)) ∧
      Roles.inlinedSize (rawTree avatar fs j) = Roles.inlinedSize (toRoles avatar (nest fs j)) :=
    fun j hj => raw_nest avatar fs j
  rw [rawTree_eq, toRoles_nest, encN_code]
  constructor
  · rw [isInlined_eq, isInlined_eq]
    simp only [DecoderFaithfulness.isInlinedAll_eq, List.all_map]
    split
    · rfl
    · exact ConditionPacking.all_congr' fun j hj => (ih j hj).1
  · rw [inlinedSize_eq, inlinedSize_eq]
    simp only
    split
    · rfl
    · rw [ConditionPacking.inlinedSizeLoop_eq, ConditionPacking.inlinedSizeLoop_eq, List.map_map, List.map_map]
      congr 1
      exact List.map_congr_left fun j hj => (ih j hj).2
termination_by fs.length - i
decreasing_by all_goals (have := mem_kids ‹_›; omega)

theorem encCode_abi (e : Encoding) : encCode e = 5 ↔ e = .AbiEncoded := by cases e <;> decide
theorem opCode_avatar (o : Operator) : opCode o = 15 ↔ o = .EqualToAvatar := by cases o <;> decide
theorem opCode_eq (o : Operator) : opCode o = 16 ↔ o = .EqualTo := by cases o <;> decide

theorem isInl_nest (avatar : Bytes) (fs : List Flat) (hb : BFS fs) (hn : 0 < fs.length) (i : Nat) :
    isInl (nest fs i) = isInlined (shapes fs) i := by
  rw [← isInlined_toRoles avatar, ← (raw_nest avatar fs i).1, isInlined_rawTree avatar fs hb hn]

/-- **The contract unpacks the tree the array describes**, with the
    evaluator's metadata: `annotate (rawTree fs i)` (what `pack_roundtrip`
    says `unpack` returns) is the node `D` of the tree read back. -/
theorem unpacked_eq (avatar : Bytes) (fs : List Flat) (hP : Packable fs) (i : Nat) :
    annotate (rawTree avatar fs i) = D avatar (nest fs i) := by
  have ih : ∀ j ∈ kids fs i, annotate (rawTree avatar fs j) = D avatar (nest fs j) :=
    fun j hj => unpacked_eq avatar fs hP j
  have hr := raw_nest avatar fs i
  have hinl := isInl_nest avatar fs hP.bfs hP.nonempty i
  unfold D
  -- the fields
  have hcv : ∀ (f : Flat), f = at! fs i → (f.paramType = .AbiEncoded → f.operator ≠ .EqualTo) →
      (if f.operator = .EqualToAvatar then avatar
        else if f.paramType = .AbiEncoded then (transformCv (shapes fs) i f).drop 2
        else transformCv (shapes fs) i f) = cvOf avatar (nest fs i) ∧
      (if f.paramType = .AbiEncoded then wordVal ((transformCv (shapes fs) i f).take 2) else 0) =
        (if encN (encCode f.paramType) = .AbiEncoded then lbOf (nest fs i) else 0) := by
    intro f hf hab
    have he : (nest fs i).enc = encCode f.paramType := by rw [nest_eq, hf]
    have ho : (nest fs i).op = opCode f.operator := by rw [nest_eq, hf]
    have hc : (nest fs i).cv = f.compValue.map (·.val) := by rw [nest_eq, hf]
    unfold cvOf lbOf transformCv
    rw [he, ho, hc, toBytes_val, encN_code]
    have hnil : (f.compValue.map (·.val) = []) ↔ f.compValue.length = 0 := by simp
    constructor
    · by_cases ha : f.operator = .EqualToAvatar
      · simp [ha, opCode]
      · rw [if_neg ha, if_neg (fun h => ha ((opCode_avatar _).1 h))]
        by_cases hab' : f.paramType = .AbiEncoded
        · have hne := hab hab'
          rw [hab']; simp [encCode, hnil, hne]
        · rw [if_neg hab', if_neg (fun h => hab' ((encCode_abi _).1 h))]
          simp only [hab', false_and, ite_false]
          by_cases heq : f.operator = .EqualTo
          · rw [heq]; simp [opCode, hinl]
          · have hne16 : opCode f.operator ≠ 16 := fun h => heq ((opCode_eq _).1 h)
            simp [heq, hne16]
    · by_cases hab' : f.paramType = .AbiEncoded
      · rw [hab']; simp [encCode, hab hab', hnil]
      · simp [hab']
  have hab : (at! fs i).paramType = .AbiEncoded → (at! fs i).operator ≠ .EqualTo := by
    intro h
    by_cases hi : i < fs.length
    · exact (hP.abi_encoded i hi h).2
    · have hd : at! fs i = default := by
        unfold at!; rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl
      rw [hd] at h; exact absurd h (by decide)
  obtain ⟨h1, h2⟩ := hcv _ rfl hab
  rw [DecoderFaithfulness.annotate_eq (rawTree avatar fs i),
    DecoderFaithfulness.annotate_eq (toRoles avatar (nest fs i)), hr.1, hr.2]
  conv => lhs; rw [rawTree_eq]
  conv => rhs; rw [toRoles_nest]
  congr 1
  all_goals first
    | rfl
    | (rw [← toRoles_nest]; done)
    | exact h1
    | exact h2
    | (rw [encN_code]; done)
    | (rw [opN_code]; by_cases ha : (at! fs i).operator = .EqualToAvatar <;> simp [ha] <;> done)
    | (rw [List.map_map, List.map_map]; exact List.map_congr_left fun j hj => ih j hj)
    | (rw [encN_code] at h2 ⊢
       by_cases hA : (at! fs i).paramType = .AbiEncoded
       · simp only [hA, ite_true] at h2 ⊢; exact h2
       · simp only [hA, ite_false]; done)
termination_by fs.length - i
decreasing_by all_goals (have := mem_kids ‹_›; omega)

theorem depth_eq (d : Condition) : depth d = depthL d.children + 1 := by
  rcases d with ⟨e, o, cs, i, sz, lb, cv⟩; rw [depth]

theorem depth_D (avatar : Bytes) (c : Cond) : depth (D avatar c) = height c := by
  rw [depth_eq, D_children]
  rcases c with ⟨e, o, cv, ch⟩
  simp only [height]
  congr 1
  have : ∀ l : List Cond, (∀ x ∈ l, depth (D avatar x) = height x) → depthL (l.map (D avatar)) = heightL l := by
    intro l hl
    induction l with
    | nil => rfl
    | cons x xs ih =>
      simp only [List.map_cons, depthL, heightL, hl x (by simp), ih (fun y hy => hl y (by simp [hy]))]
  exact this ch fun x hx => depth_D avatar x
termination_by sizeOf c
decreasing_by
  simp_wf
  have := List.sizeOf_lt_of_mem hx
  omega

section
variable (avatar : Bytes) (env : Env) (henv : EnvOk env) (data : Calldata)

include henv in
/-- **The SDK pipeline keeps the meaning of the tree as written.** A
    well-typed user tree `c0` is normalized (`normalize k`), flattened to
    `fs` (which reads back as the normalized tree), packed and stored. On
    every calldata, whenever the contract's evaluation of the tree it unpacks
    from the stored buffer does not revert, it passes exactly when the
    contract's reading of `c0` does, with the same allowance consumptions and
    Pluck slots. -/
theorem sdk_pipeline (c0 : Cond) (hc : inv avatar c0) (k : Nat) (fs : List Flat) (hP : Packable fs)
    (hfs : nest fs 0 = normalize k c0) (junk junk' : Mem) {tree : Condition} {mp : Nat}
    (hu : unpack avatar (bufMem (pack junk fs) junk') = some (tree, mp))
    (hne : (run env data tree mp []).status ≠ revert) :
    Rel (run env data tree mp []) (sem (readWorld avatar env data mp) c0 (.pos 0) Slots.empty (toMap [])) := by
  rw [pack_roundtrip avatar junk junk' fs hP] at hu
  simp only [Option.some.injEq, Prod.mk.injEq] at hu
  obtain ⟨rfl, rfl⟩ := hu
  rw [unpacked_eq avatar fs hP 0, hfs] at hne ⊢
  unfold run at hne ⊢
  exact normalize_meaning avatar env henv data (maxPluck fs) k hc 0 _ (by rw [depth_D]; omega) [] Slots.empty hne

include henv in
/-- The stored tree and the tree as written, evaluated by the contract,
    agree whenever neither reverts. -/
theorem sdk_pipeline_agree (c0 : Cond) (hc : inv avatar c0) (k : Nat) (fs : List Flat) (hP : Packable fs)
    (hfs : nest fs 0 = normalize k c0) (junk junk' : Mem) {tree : Condition} {mp : Nat}
    (hu : unpack avatar (bufMem (pack junk fs) junk') = some (tree, mp))
    (hne : (run env data (D avatar c0) mp []).status ≠ revert)
    (hne' : (run env data tree mp []).status ≠ revert) :
    Agree (run env data (D avatar c0) mp []) (run env data tree mp []) := by
  have h1 := eval_reading avatar env henv data mp hc 0 _ (by rw [depth_D]; omega) [] Slots.empty hne
  exact h1.agree (sdk_pipeline avatar env henv data c0 hc k fs hP hfs junk junk' hu hne')

end
end Bridge
