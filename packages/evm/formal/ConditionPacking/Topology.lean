import ConditionPacking.Bfs

/-!
# Topology on the flat array = Topology on the tree

On a BFS-ordered array, `Topology.isInlined` / `inlinedSize` (which walk the
flat array through `childBounds`) agree with the tree versions in
`DecoderFaithfulness/Roles.lean`, evaluated on the input tree.
-/

namespace ConditionPacking
open DecoderFaithfulness

theorem all_congr' {α : Type} {l : List α} {f g : α → Bool} (h : ∀ x ∈ l, f x = g x) :
    l.all f = l.all g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.all_cons, h a (by simp), ih (fun x hx => h x (by simp [hx]))]

theorem attach_all {α : Type} (l : List α) (f : α → Bool) :
    (l.attach.all fun x => f x.1) = l.all f := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [List.attach_cons, List.all_cons]

theorem attach_map' {α β : Type} (l : List α) (f : α → β) :
    (l.attach.map fun x => f x.1) = l.map f := List.attach_map_val

theorem isInlinedAll_eq (cs : List Roles.Condition) :
    Roles.isInlinedAll cs = cs.all Roles.isInlined := by
  induction cs with
  | nil => rfl
  | cons c cs ih => rw [Roles.isInlinedAll, ih, List.all_cons]

theorem inlinedSizeLoop_eq (b : Bool) (cs : List Roles.Condition) :
    Roles.inlinedSizeLoop b cs = sizeLoop b (cs.map Roles.inlinedSize) := by
  induction cs with
  | nil => rfl
  | cons c cs ih => rw [Roles.inlinedSizeLoop, ih, List.map_cons, sizeLoop]

/-- `childBounds` as a list of child indices. -/
theorem range_childBounds (fs : List Flat) (hb : BFS fs) (hn : 0 < fs.length) (i : Nat) :
    (List.range (childBounds (shapes fs) i).2).map (fun x => (childBounds (shapes fs) i).1 + x) =
      kids fs i := by
  rw [childBounds_eq fs hb hn]
  dsimp only
  rw [← List.range'_eq_map_range]
  split
  · rename_i h; rw [h, List.eq_nil_of_length_eq_zero h]; rfl
  · rw [kids_eq_range' fs hb hn i, List.length_range']

theorem rawTree_eq (avatar : Bytes) (fs : List Flat) (i : Nat) :
    rawTree avatar fs i =
      let f := at! fs i
      let cv := transformCv (shapes fs) i f
      { encoding := f.paramType
        operator := f.operator
        children := (kids fs i).map (rawTree avatar fs)
        inlined := false
        size := 0
        leadingBytes := if f.paramType = .AbiEncoded then wordVal (cv.take 2) else 0
        compValue :=
          if f.operator = .EqualToAvatar then avatar
          else if f.paramType = .AbiEncoded then cv.drop 2 else cv } := by
  rw [rawTree]
  simp only [attach_map' (kids fs i) (rawTree avatar fs)]

theorem isInlined_rawTree (avatar : Bytes) (fs : List Flat) (hb : BFS fs) (hn : 0 < fs.length)
    (i : Nat) : Roles.isInlined (rawTree avatar fs i) = isInlined (shapes fs) i := by
  rw [rawTree_eq, isInlined]
  simp only [Roles.isInlined, shapes_getD, isInlinedAll_eq]
  split
  · rfl
  · have e : ((List.range (childBounds (shapes fs) i).2).all fun x =>
          isInlined (shapes fs) ((childBounds (shapes fs) i).1 + x)) =
        (kids fs i).all (isInlined (shapes fs)) := by
      rw [← range_childBounds fs hb hn i, List.all_map]; rfl
    rw [attach_all (List.range _) (fun x => isInlined (shapes fs) ((childBounds (shapes fs) i).1 + x)),
      e, List.all_map]
    apply all_congr'
    intro j hj
    exact isInlined_rawTree avatar fs hb hn j
termination_by fs.length - i
decreasing_by
  all_goals (have := mem_kids hj; omega)

theorem inlinedSize_rawTree (avatar : Bytes) (fs : List Flat) (hb : BFS fs) (hn : 0 < fs.length)
    (i : Nat) : Roles.inlinedSize (rawTree avatar fs i) = inlinedSize (shapes fs) i := by
  rw [rawTree_eq, inlinedSize]
  simp only [Roles.inlinedSize, shapes_getD, inlinedSizeLoop_eq]
  split
  · rfl
  · have e : ((List.range (childBounds (shapes fs) i).2).map fun x =>
          inlinedSize (shapes fs) ((childBounds (shapes fs) i).1 + x)) =
        (kids fs i).map (inlinedSize (shapes fs)) := by
      rw [← range_childBounds fs hb hn i, List.map_map]; rfl
    rw [attach_map' (List.range _) (fun x => inlinedSize (shapes fs) ((childBounds (shapes fs) i).1 + x)),
      e, List.map_map]
    congr 1
    apply List.map_congr_left
    intro j hj
    exact inlinedSize_rawTree avatar fs hb hn j
termination_by fs.length - i
decreasing_by
  all_goals (have := mem_kids hj; omega)

end ConditionPacking
