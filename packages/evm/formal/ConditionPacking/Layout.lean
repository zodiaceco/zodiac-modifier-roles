import ConditionPacking.Main

/-!
# `ConditionPacker._layout`

`_layout` computes every node's child count, whether it is inlined and its
inlined size in one bottom-up pass over the flat array. `layout` transcribes
that loop. `layout_eq` proves that on a BFS-ordered array it computes
`childBounds`, `isInlined` and `inlinedSize` of `Model.lean`, the definitions
the packing proof is stated with. `packL` is `ConditionPacker.pack` reading
those values from the pass, as the Solidity does, and `packL_eq_pack` shows it
is `pack`.
-/

namespace ConditionPacking
open DecoderFaithfulness DecoderFaithfulness.Roles

/-! ## Transcription -/

/-- `struct LayoutNode`. -/
structure LNode where
  childCount : Nat
  notInlined : Bool
  inlinedSize : Nat

/-- A freshly allocated `LayoutNode`: zeroed memory. -/
def LNode.zero : LNode := ⟨0, false, 0⟩

/-- The first half of a loop iteration: the node's own encoding settles
    whether it is inlined, and its size. -/
def finish (e : Encoding) (n : LNode) : LNode :=
  let notInlined := n.notInlined || decide (e = .Dynamic ∨ e = .Array ∨ e = .AbiEncoded)
  ⟨n.childCount, notInlined,
    if notInlined then 0 else if e = .Static then 32 else n.inlinedSize⟩

/-- The second half: what a settled node `c` adds to its parent `p`, whose
    encoding is `pe`. -/
def push (pe : Encoding) (c p : LNode) : LNode :=
  ⟨p.childCount + 1, p.notInlined || c.notInlined,
    if c.notInlined then p.inlinedSize
    else if pe ≠ .None then p.inlinedSize + c.inlinedSize
    else if c.inlinedSize > 0 then c.inlinedSize else p.inlinedSize⟩

/-- One iteration of the loop of `_layout`, for node `i`. -/
def layoutStep (sh : Array Shape) (st : Array LNode) (i : Nat) : Array LNode :=
  let shape := sh[i]?.getD default
  let node := finish shape.paramType (st[i]?.getD LNode.zero)
  let st := st.setIfInBounds i node
  if i = 0 then st
  else
    let parent := shape.parent
    let parentNode := push (sh[parent]?.getD default).paramType node (st[parent]?.getD LNode.zero)
    st.setIfInBounds parent parentNode

/-- The loop, with `next` nodes left: `for (next = count; next > 0; --next)`. -/
def layoutFrom (sh : Array Shape) : Nat → Array LNode → Array LNode
  | 0, st => st
  | next + 1, st => layoutFrom sh next (layoutStep sh st next)

/-- `_layout`. Each iteration updates the array before the next one reads it. -/
def layout (sh : List Shape) : Array LNode :=
  layoutFrom sh.toArray sh.length (Array.replicate sh.length LNode.zero)

/-! ## What the pass should compute -/

/-- The values of `Model.lean` for node `i`, as a `LayoutNode`. -/
def spec (sh : List Shape) (i : Nat) : LNode :=
  ⟨(childBounds sh i).2, !isInlined sh i, if isInlined sh i then inlinedSize sh i else 0⟩

/-- Node `i` while the loop still has `k` nodes left: the children at `k`
    or after have added themselves, the last one first. -/
def part (fs : List Flat) (i k : Nat) : LNode :=
  ((kids fs i).filter fun j => k ≤ j).foldr
    (fun j acc => push (at! fs i).paramType (spec (shapes fs) j) acc) LNode.zero

/-! ## The children's contributions -/

theorem LNode.eq_of {a b : LNode} (h1 : a.childCount = b.childCount)
    (h2 : a.notInlined = b.notInlined) (h3 : a.inlinedSize = b.inlinedSize) : a = b := by
  cases a; cases b; simp_all

/-- The children in `l` added to a zeroed node with encoding `e`, the last
    one first. -/
def foldKids (e : Encoding) (sh : List Shape) (l : List Nat) : LNode :=
  l.foldr (fun j acc => push e (spec sh j) acc) LNode.zero

theorem foldKids_cons (e : Encoding) (sh : List Shape) (j : Nat) (l : List Nat) :
    foldKids e sh (j :: l) = push e (spec sh j) (foldKids e sh l) := rfl

theorem foldKids_count (e : Encoding) (sh : List Shape) (l : List Nat) :
    (foldKids e sh l).childCount = l.length := by
  induction l with
  | nil => rfl
  | cons j l ih => rw [foldKids_cons, List.length_cons, ← ih]; rfl

theorem foldKids_notInlined (e : Encoding) (sh : List Shape) (l : List Nat) :
    (foldKids e sh l).notInlined = !(l.all (isInlined sh)) := by
  induction l with
  | nil => rfl
  | cons j l ih =>
    rw [foldKids_cons, List.all_cons]
    show ((foldKids e sh l).notInlined || !isInlined sh j) = _
    rw [ih]; cases isInlined sh j <;> cases l.all (isInlined sh) <;> rfl

theorem foldKids_size (e : Encoding) (sh : List Shape) (l : List Nat)
    (h : l.all (isInlined sh) = true) :
    (foldKids e sh l).inlinedSize = sizeLoop (decide (e = .None)) (l.map (inlinedSize sh)) := by
  induction l with
  | nil => rfl
  | cons j l ih =>
    rw [List.all_cons, Bool.and_eq_true] at h
    have ihl := ih h.2
    rw [foldKids_cons, List.map_cons, sizeLoop]
    simp only [push, spec, h.1, Bool.not_true, Bool.false_eq_true, ite_false, ite_true, ihl]
    by_cases he : e = .None
    · simp only [he, ne_eq, not_true_eq_false, ite_false, decide_true, true_and]
      split <;> omega
    · simp only [he, ne_eq, not_false_eq_true, ite_true, decide_false, Bool.false_eq_true,
        false_and, ite_false]
      omega

/-! ## One level of the model's definitions, over the children -/

theorem childCount_kids (fs : List Flat) (hb : BFS fs) (hn : 0 < fs.length) (i : Nat) :
    (childBounds (shapes fs) i).2 = (kids fs i).length := by
  rw [childBounds_eq fs hb hn]

theorem isInlined_kids (fs : List Flat) (hb : BFS fs) (hn : 0 < fs.length) (i : Nat) :
    isInlined (shapes fs) i =
      if (at! fs i).paramType = .Dynamic ∨ (at! fs i).paramType = .Array ∨
          (at! fs i).paramType = .AbiEncoded then false
      else (kids fs i).all (isInlined (shapes fs)) := by
  conv => lhs; rw [isInlined]
  simp only [shapes_getD]
  split
  · rfl
  · rw [attach_all (List.range _)
        (fun x => isInlined (shapes fs) ((childBounds (shapes fs) i).1 + x)),
      ← range_childBounds fs hb hn i, List.all_map]
    rfl

theorem inlinedSize_kids (fs : List Flat) (hb : BFS fs) (hn : 0 < fs.length) (i : Nat) :
    inlinedSize (shapes fs) i =
      if (at! fs i).paramType = .Static then 32
      else sizeLoop (decide ((at! fs i).paramType = .None))
        ((kids fs i).map (inlinedSize (shapes fs))) := by
  conv => lhs; rw [inlinedSize]
  simp only [shapes_getD]
  split
  · rfl
  · rw [attach_map' (List.range _)
        (fun x => inlinedSize (shapes fs) ((childBounds (shapes fs) i).1 + x)),
      ← range_childBounds fs hb hn i, List.map_map]
    rfl

/-- A node that has received all its children and is then settled holds the
    model's values. -/
theorem finish_foldKids (fs : List Flat) (hb : BFS fs) (hn : 0 < fs.length) (i : Nat) :
    finish (at! fs i).paramType (foldKids (at! fs i).paramType (shapes fs) (kids fs i)) =
      spec (shapes fs) i := by
  apply LNode.eq_of
  · show (foldKids _ _ _).childCount = (childBounds (shapes fs) i).2
    rw [foldKids_count, childCount_kids fs hb hn]
  · show ((foldKids _ _ _).notInlined || decide _) = !isInlined (shapes fs) i
    rw [foldKids_notInlined, isInlined_kids fs hb hn i]
    by_cases hd : (at! fs i).paramType = .Dynamic ∨ (at! fs i).paramType = .Array ∨
        (at! fs i).paramType = .AbiEncoded
    · simp [hd]
    · simp [hd]
  · show (if ((foldKids _ _ _).notInlined || decide _) = true then 0
        else if (at! fs i).paramType = .Static then 32 else (foldKids _ _ _).inlinedSize) =
      if isInlined (shapes fs) i = true then inlinedSize (shapes fs) i else 0
    rw [foldKids_notInlined, isInlined_kids fs hb hn i]
    by_cases hd : (at! fs i).paramType = .Dynamic ∨ (at! fs i).paramType = .Array ∨
        (at! fs i).paramType = .AbiEncoded
    · simp [hd]
    · cases hall : (kids fs i).all (isInlined (shapes fs))
      · simp [hd]
      · simp only [hd, decide_false, Bool.or_false, Bool.not_true, Bool.false_eq_true,
          ite_false, ite_true]
        rw [inlinedSize_kids fs hb hn i, foldKids_size _ _ _ hall]

/-! ## Children at or after `k` -/

theorem filter_ge_nil (q : Nat → Bool) (n m : Nat) (h : n ≤ m) :
    (((List.range n).filter q).filter fun j => decide (m ≤ j)) = [] := by
  rw [List.filter_eq_nil_iff]
  intro x hx
  simp only [List.mem_filter, List.mem_range] at hx
  simp only [decide_eq_true_eq]
  omega

theorem filter_ge_cons (q : Nat → Bool) : ∀ (n k : Nat), k < n → q k = true →
    (((List.range n).filter q).filter fun j => decide (k ≤ j)) =
      k :: (((List.range n).filter q).filter fun j => decide (k + 1 ≤ j))
  | 0, k, h, _ => by omega
  | n + 1, k, h, hq => by
    rw [List.range_succ, List.filter_append, List.filter_append, List.filter_append]
    by_cases hk : k = n
    · subst hk
      rw [filter_ge_nil q k k (Nat.le_refl _), filter_ge_nil q k (k + 1) (by omega)]
      simp [List.filter, hq]
    · rw [filter_ge_cons q n k (by omega) hq]
      have h1 : decide (k ≤ n) = true := by simp only [decide_eq_true_eq]; omega
      have h2 : decide (k + 1 ≤ n) = true := by simp only [decide_eq_true_eq]; omega
      cases hqn : q n <;> simp [List.filter, hqn, h1, h2]

theorem part_all (fs : List Flat) (i : Nat) :
    part fs i (i + 1) = foldKids (at! fs i).paramType (shapes fs) (kids fs i) := by
  have e : ((kids fs i).filter fun j => decide (i + 1 ≤ j)) = kids fs i := by
    rw [List.filter_eq_self]
    intro j hj
    have := mem_kids hj
    simp only [decide_eq_true_eq]; omega
  unfold part foldKids
  rw [e]

theorem part_none (fs : List Flat) (i : Nat) : part fs i fs.length = LNode.zero := by
  have e : ((kids fs i).filter fun j => decide (fs.length ≤ j)) = [] := by
    rw [List.filter_eq_nil_iff]
    intro j hj
    have := mem_kids hj
    simp only [decide_eq_true_eq]; omega
  unfold part
  rw [e]; rfl

theorem part_push (fs : List Flat) (p k : Nat) (hk : k < fs.length) (hpk : p < k)
    (hp : (at! fs k).parent = p) :
    part fs p k = push (at! fs p).paramType (spec (shapes fs) k) (part fs p (k + 1)) := by
  unfold part kids
  rw [filter_ge_cons _ fs.length k hk (by simp [hp, hpk])]
  rfl

theorem part_skip (fs : List Flat) (i k : Nat) (h : (at! fs k).parent ≠ i) :
    part fs i k = part fs i (k + 1) := by
  have e : ((kids fs i).filter fun j => decide (k ≤ j)) =
      ((kids fs i).filter fun j => decide (k + 1 ≤ j)) := by
    apply List.filter_congr
    intro j hj
    have hjk : j ≠ k := by
      intro e; subst e
      simp only [kids, List.mem_filter, decide_eq_true_eq] at hj
      exact h hj.2.2
    simp only [decide_eq_decide]; omega
  unfold part
  rw [e]

/-! ## The loop invariant -/

/-- With `k` nodes left: nodes at `k` or after hold the model's values, and
    earlier nodes hold what their children at `k` or after added. -/
def LayoutInv (fs : List Flat) (k : Nat) (st : Array LNode) : Prop :=
  st.size = fs.length ∧ ∀ i, i < fs.length →
    (k ≤ i → st[i]?.getD LNode.zero = spec (shapes fs) i) ∧
    (i < k → st[i]?.getD LNode.zero = part fs i k)

theorem inv_step (fs : List Flat) (hb : BFS fs) (hn : 0 < fs.length) (k : Nat)
    (hk : k < fs.length) (st : Array LNode) (h : LayoutInv fs (k + 1) st) :
    LayoutInv fs k (layoutStep (shapes fs).toArray st k) := by
  obtain ⟨hsize, h⟩ := h
  have hkst : k < st.size := by omega
  have hnode : finish (at! fs k).paramType (st[k]?.getD LNode.zero) =
      spec (shapes fs) k := by
    rw [(h k hk).2 (by omega), part_all, finish_foldKids fs hb hn]
  unfold LayoutInv
  unfold layoutStep
  simp only [List.getElem?_toArray, ← List.getD_eq_getElem?_getD, shapes_getD]
  rw [hnode]
  by_cases h0 : k = 0
  · subst h0
    simp only [ite_true]
    refine ⟨by simpa using hsize, ?_⟩
    intro i hi
    refine ⟨fun _ => ?_, fun hlt => by omega⟩
    by_cases hi0 : i = 0
    · simp [hi0, hkst]
    · rw [Array.getElem?_setIfInBounds_ne (Ne.symm hi0)]
      exact (h i hi).1 (by omega)
  · simp only [h0, ite_false]
    have hp := hb.parent_lt k (by omega) hk
    have hpk : (at! fs k).parent ≠ k := by omega
    have hpst : (at! fs k).parent < st.size := by omega
    refine ⟨by simpa using hsize, ?_⟩
    intro i hi
    refine ⟨fun hki => ?_, fun hlt => ?_⟩
    · by_cases hik : i = k
      · subst hik
        simp [hpk, hkst]
      · have hne : (at! fs k).parent ≠ i := by omega
        rw [Array.getElem?_setIfInBounds_ne hne,
          Array.getElem?_setIfInBounds_ne (Ne.symm hik)]
        exact (h i hi).1 (by omega)
    · by_cases hip : i = (at! fs k).parent
      · subst hip
        simp only [Array.getD_getElem?_setIfInBounds, Array.size_setIfInBounds,
          hpst, ite_true, Array.getElem?_setIfInBounds_ne (Ne.symm hpk)]
        rw [(h _ (by omega)).2 (by omega), ← part_push fs _ k hk hp rfl]
      · have hne : i ≠ k := by omega
        rw [Array.getElem?_setIfInBounds_ne (Ne.symm hip),
          Array.getElem?_setIfInBounds_ne (Ne.symm hne)]
        rw [(h i hi).2 (by omega), part_skip fs i k (fun e => hip e.symm)]

theorem inv_layoutFrom (fs : List Flat) (hb : BFS fs) (hn : 0 < fs.length) :
    ∀ (k : Nat) (st : Array LNode), k ≤ fs.length → LayoutInv fs k st →
      LayoutInv fs 0 (layoutFrom (shapes fs).toArray k st)
  | 0, _, _, h => h
  | k + 1, st, hk, h =>
    inv_layoutFrom fs hb hn k _ (by omega) (inv_step fs hb hn k (by omega) st h)

/-- **`_layout` computes the model's values.** On a BFS-ordered array, the
    pass leaves in `nodes[i]` the child count of `childBounds`, whether
    `isInlined` holds, and `inlinedSize` (0 if not inlined). -/
theorem layout_eq (fs : List Flat) (hb : BFS fs) (hn : 0 < fs.length) (i : Nat)
    (hi : i < fs.length) : (layout (shapes fs))[i]?.getD LNode.zero = spec (shapes fs) i := by
  have h0 : LayoutInv fs fs.length (Array.replicate fs.length LNode.zero) := by
    refine ⟨by simp, ?_⟩
    intro j hj
    refine ⟨fun _ => by omega, fun _ => ?_⟩
    simp [hj, part_none]
  have := inv_layoutFrom fs hb hn fs.length _ (Nat.le_refl _) h0
  unfold layout
  rw [shapes_length]
  exact (this.2 i hi).1 (Nat.zero_le _)

/-! ## The packer, reading from the pass -/

/-- `_transform`: whether an `EqualTo` node is inlined is read from the pass. -/
def transformL (nodes : Array LNode) (fs : List Flat) : List Flat :=
  (List.range fs.length).map fun i =>
    let f := at! fs i
    let cv := if f.paramType = .AbiEncoded ∧ f.compValue.length = 0 then [0, 4] else f.compValue
    { f with
      compValue := if f.operator = .EqualTo ∧ (nodes[i]?.getD LNode.zero).notInlined = true
        then cv.drop 32 else cv }

/-- One iteration of the `_packNodes` loop: `packStep`, with the child count
    and the inlined size read from the pass. -/
def packStepL (nodes : Array LNode) (fs : List Flat) (st : PackState) (i : Nat) : PackState :=
  let condition := at! fs i
  let node := nodes[i]?.getD LNode.zero
  let childCount := node.childCount
  let inlinedSz := node.inlinedSize
  let compValue := condition.compValue
  let compValueLength := compValue.length
  let hasCompValue := decide (compValueLength > 0)
  let packed := packedNode (encCode condition.paramType) (opCode condition.operator)
    childCount inlinedSz (if hasCompValue then 1 else 0)
  let m := mstore st.m st.offset (mload st.m st.offset ||| shl 224 packed)
  let offset := st.offset + 4
  if hasCompValue then
    let m := mstore m st.compValueOffset (shl 240 compValueLength)
    let m := m.write (st.compValueOffset + 2) compValue
    ⟨m, offset, st.compValueOffset + 2 + compValueLength⟩
  else ⟨m, offset, st.compValueOffset⟩

/-- `_packNodes`. -/
def packNodesL (nodes : Array LNode) (fs : List Flat) (st : PackState) : PackState :=
  (List.range fs.length).foldl (packStepL nodes fs) st

/-- `ConditionPacker.pack` as written: `_layout`, `_transform`, `_count`,
    `_packNodes`. -/
def packL (junk : Mem) (fs : List Flat) : Bytes :=
  let nodes := layout (shapes fs)
  let fs := transformL nodes fs
  let (compValuesSize, maxPluckCount) := count fs
  let nodeCount := fs.length
  let len := 3 + nodeCount * 4 + compValuesSize
  let m : Mem := fun q => if q < len then 0 else junk q
  let header := (nodeCount <<< 8) ||| maxPluckCount
  let m := mstore m 0 (shl 232 header)
  let st := packNodesL nodes fs ⟨m, 3, 3 + nodeCount * 4⟩
  st.m.read 0 len

theorem foldl_congr_mem {α β : Type} (f g : α → β → α) :
    ∀ (l : List β) (a : α), (∀ x ∈ l, ∀ a, f a x = g a x) → l.foldl f a = l.foldl g a
  | [], _, _ => rfl
  | x :: l, a, h => by
    rw [List.foldl_cons, List.foldl_cons, h x (by simp),
      foldl_congr_mem f g l _ (fun y hy => h y (by simp [hy]))]

theorem transformL_eq (fs : List Flat) (hb : BFS fs) (hn : 0 < fs.length) :
    transformL (layout (shapes fs)) fs = transform fs := by
  unfold transformL transform
  apply List.map_congr_left
  intro i hi
  simp only [List.mem_range] at hi
  simp only [transformCv]
  rw [layout_eq fs hb hn i hi]
  simp [spec]

/-- **The packer as written is the packer of the packing proof.** On a
    BFS-ordered array, `ConditionPacker.pack` with its layout pass returns
    the bytes of `pack`, which is stated with `childBounds`, `isInlined` and
    `inlinedSize`. -/
theorem packL_eq_pack (junk : Mem) (fs : List Flat) (hb : BFS fs) (hn : 0 < fs.length) :
    packL junk fs = pack junk fs := by
  have hp : ∀ st, packNodesL (layout (shapes fs)) (transform fs) st =
      packNodes (shapes (transform fs)) (transform fs) st := by
    intro st
    unfold packNodesL packNodes
    apply foldl_congr_mem
    intro i hi st
    simp only [List.mem_range, transform_length] at hi
    unfold packStepL packStep
    rw [shapes_transform, layout_eq fs hb hn i hi]
    rfl
  unfold packL pack packBuffer
  simp only [transformL_eq fs hb hn, hp]

/-- **Pack/unpack round trip, for the packer as written.** `pack_roundtrip`
    with `_layout` in place of the model's definitions. -/
theorem packL_roundtrip (avatar : Bytes) (junk junk' : Mem) (fs : List Flat) (h : Packable fs) :
    unpack avatar (bufMem (packL junk fs) junk') =
      some (annotate (rawTree avatar fs 0), maxPluck fs) := by
  rw [packL_eq_pack junk fs h.bfs h.nonempty]
  exact pack_roundtrip avatar junk junk' fs h

end ConditionPacking
