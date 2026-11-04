import ConditionPacking.Bytes

/-!
# BFS order: children are contiguous blocks

With parents that never decrease (`BFS`), the children of node `i` are the
block `[1 + cnt i, 1 + cnt (i + 1))`, where `cnt p` counts the non-root nodes
whose parent is below `p`. `Topology.childBounds` finds exactly that block, and
the unpacker's running child pointer reaches it.
-/

namespace ConditionPacking
open DecoderFaithfulness DecoderFaithfulness.Roles

/-! ## Monotone keys over a range -/

theorem length_filter_lt_add_eq (f : Nat → Nat) (c : Nat) (l : List Nat)
    (h : ∀ x ∈ l, f x ≤ c) :
    (l.filter fun x => f x < c).length + (l.filter fun x => f x = c).length = l.length := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    have ha := h a (by simp)
    have ih := ih (fun x hx => h x (by simp [hx]))
    by_cases hlt : f a < c
    · simp [List.filter_cons, hlt, show f a ≠ c by omega]; omega
    · simp [List.filter_cons, hlt, show f a = c by omega]; omega

theorem length_filter_lt_succ (f : Nat → Nat) (c : Nat) (l : List Nat) :
    (l.filter fun x => f x < c + 1).length =
      (l.filter fun x => f x < c).length + (l.filter fun x => f x = c).length := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    by_cases h1 : f a < c
    · simp [List.filter_cons, h1, show f a < c + 1 by omega, show f a ≠ c by omega]; omega
    · by_cases h2 : f a = c
      · simp [List.filter_cons, h1, h2]; omega
      · simp [List.filter_cons, h1, h2, show ¬ f a < c + 1 by omega]; omega

/-- Over a range where `f` never decreases, the positions with `f x = c` form
    one block, right after those with `f x < c`. -/
theorem filter_eq_range' (f : Nat → Nat) (c s : Nat) :
    ∀ n, (∀ x y, s ≤ x → x ≤ y → y < s + n → f x ≤ f y) →
      (List.range' s n).filter (fun x => f x = c) =
        List.range' (s + ((List.range' s n).filter fun x => f x < c).length)
          ((List.range' s n).filter fun x => f x = c).length := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
    intro hm
    have ih := ih (fun x y h1 h2 h3 => hm x y h1 h2 (by omega))
    have hle : ∀ x ∈ List.range' s n, f x ≤ f (s + n) := by
      intro x hx; simp [List.mem_range'] at hx
      exact hm x (s + n) (by omega) (by omega) (by omega)
    rw [List.range'_concat, Nat.one_mul]
    by_cases hlt : f (s + n) < c
    · -- everything is below `c`
      have hnil : (List.range' s n).filter (fun x => f x = c) = [] := by
        rw [List.filter_eq_nil_iff]; intro x hx; have := hle x hx; simp; omega
      have e1 : ((List.range' s n ++ [s + n]).filter fun x => f x = c) = [] := by
        simp [List.filter_append, hnil]; omega
      rw [e1]; simp
    · by_cases heq : f (s + n) = c
      · have hsum := length_filter_lt_add_eq f c (List.range' s n)
          (fun x hx => heq ▸ hle x hx)
        simp only [List.length_range'] at hsum
        have e1 : ((List.range' s n ++ [s + n]).filter fun x => f x = c) =
            (List.range' s n).filter (fun x => f x = c) ++ [s + n] := by
          simp [List.filter_append, heq]
        have e2 : ((List.range' s n ++ [s + n]).filter fun x => f x < c).length =
            ((List.range' s n).filter fun x => f x < c).length := by
          simp [List.filter_append, heq]
        rw [e1, e2, List.length_append, List.length_singleton]
        conv => lhs; rw [ih]
        rw [List.range'_concat, Nat.one_mul]
        congr 2
        omega
      · have e1 : ((List.range' s n ++ [s + n]).filter fun x => f x = c) =
            (List.range' s n).filter (fun x => f x = c) := by
          simp [List.filter_append, heq]
        have e2 : ((List.range' s n ++ [s + n]).filter fun x => f x < c).length =
            ((List.range' s n).filter fun x => f x < c).length := by
          simp [List.filter_append, hlt]
        rw [e1, e2]
        exact ih

/-! ## The children of a node -/

/-- `parent` of node `j`. -/
abbrev par (fs : List Flat) (j : Nat) : Nat := (at! fs j).parent

/-- Non-root nodes whose parent is below `p`. -/
def cnt (fs : List Flat) (p : Nat) : Nat :=
  ((List.range' 1 (fs.length - 1)).filter fun j => par fs j < p).length

theorem BFS.mono {fs : List Flat} (h : BFS fs) :
    ∀ x y, 1 ≤ x → x ≤ y → y < 1 + (fs.length - 1) → par fs x ≤ par fs y := by
  intro x y h1 h2 h3
  induction y with
  | zero => omega
  | succ y ih =>
    by_cases hxy : x = y + 1
    · subst hxy; exact Nat.le_refl _
    · exact Nat.le_trans (ih (by omega) (by omega)) (h.parent_mono y (by omega) (by omega))

theorem kids_eq_filter (fs : List Flat) (hb : BFS fs) (hn : 0 < fs.length) (i : Nat) :
    kids fs i = (List.range' 1 (fs.length - 1)).filter fun j => par fs j = i := by
  unfold kids
  have : List.range fs.length = 0 :: List.range' 1 (fs.length - 1) := by
    rw [List.range_eq_range', show fs.length = (fs.length - 1) + 1 by omega, List.range'_succ]
    simp
  rw [this, List.filter_cons]
  simp only [Nat.not_lt_zero, false_and, decide_false, Bool.false_eq_true, ite_false]
  apply List.filter_congr
  intro j hj
  simp [List.mem_range'] at hj
  have := hb.parent_lt j (by omega) (by omega)
  simp only [par]
  by_cases h : (at! fs j).parent = i
  · simp [h]; omega
  · simp [h]

/-- The children of `i` are the block after `cnt i` (BFS order). -/
theorem kids_eq_range' (fs : List Flat) (hb : BFS fs) (hn : 0 < fs.length) (i : Nat) :
    kids fs i = List.range' (1 + cnt fs i) (kids fs i).length := by
  rw [kids_eq_filter fs hb hn]
  exact filter_eq_range' (par fs) i 1 _ hb.mono

theorem cnt_succ (fs : List Flat) (hb : BFS fs) (hn : 0 < fs.length) (i : Nat) :
    cnt fs (i + 1) = cnt fs i + (kids fs i).length := by
  unfold cnt; rw [kids_eq_filter fs hb hn, length_filter_lt_succ]

theorem cnt_zero (fs : List Flat) : cnt fs 0 = 0 := by
  simp [cnt]

theorem cnt_le (fs : List Flat) (p : Nat) : cnt fs p ≤ fs.length - 1 := by
  unfold cnt
  exact Nat.le_trans (List.length_filter_le _ _) (by simp)

/-! ## `Topology.childBounds` -/

theorem shapes_getD (fs : List Flat) (j : Nat) :
    (shapes fs).getD j default = ⟨(at! fs j).parent, (at! fs j).paramType⟩ := by
  unfold shapes at!
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases fs[j]? <;> rfl

@[simp] theorem shapes_length (fs : List Flat) : (shapes fs).length = fs.length := by
  simp [shapes]

theorem shapes_getElem (fs : List Flat) (j : Nat) (h : j < (shapes fs).length) :
    (shapes fs)[j].parent = par fs j := by
  have := shapes_getD fs j
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some] at this
  rw [this]

/-- The children of `index` at positions `≥ j`. -/
def blk (fs : List Flat) (index j : Nat) : List Nat :=
  (List.range' j (fs.length - j)).filter fun x => par fs x = index

/-- The scan of `childBounds` from `j`: it finds the block of children of
    `index` among the positions `≥ j`. -/
theorem childBoundsFrom_eq (fs : List Flat) (hb : BFS fs) (index : Nat) (j start count : Nat)
    (hj : 1 ≤ j) :
    childBoundsFrom (shapes fs) index j start count =
      if blk fs index j = [] then (start, count)
      else (if count = 0 then (blk fs index j).headD 0 else start,
        count + (blk fs index j).length) := by
  rw [childBoundsFrom]
  by_cases hlt : j < (shapes fs).length
  · rw [dif_pos hlt, shapes_getElem]
    have hlt' : j < fs.length := by simpa using hlt
    have hr : blk fs index j = (if par fs j = index then [j] else []) ++ blk fs index (j + 1) := by
      unfold blk
      rw [show fs.length - j = (fs.length - (j + 1)) + 1 by omega, List.range'_succ,
        List.filter_cons]
      split <;> simp_all
    by_cases hp : par fs j = index
    · simp only [hp, ite_true]
      rw [childBoundsFrom_eq fs hb index (j + 1) _ _ (by omega), hr]
      simp only [hp, ite_true, List.singleton_append, List.headD_cons, List.length_cons,
        reduceCtorEq, ite_false]
      by_cases hK : blk fs index (j + 1) = []
      · simp [hK]
      · simp only [hK, ite_false, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false]
        congr 1; omega
    · simp only [hp, ite_false]
      by_cases hg : index < par fs j
      · simp only [gt_iff_lt, hg, ite_true]
        -- every later parent is at least `par j > index`
        have hnil : blk fs index j = [] := by
          unfold blk
          rw [List.filter_eq_nil_iff]
          intro x hx; simp [List.mem_range'] at hx
          have := hb.mono j x (by omega) (by omega) (by omega)
          simp; omega
        simp [hnil]
      · simp only [gt_iff_lt, hg, ite_false]
        rw [childBoundsFrom_eq fs hb index (j + 1) _ _ (by omega), hr]
        simp [hp]
  · rw [dif_neg hlt]
    have : blk fs index j = [] := by
      unfold blk; simp at hlt; rw [show fs.length - j = 0 by omega]; rfl
    simp [this]
termination_by fs.length - j

theorem childBounds_eq (fs : List Flat) (hb : BFS fs) (hn : 0 < fs.length) (i : Nat) :
    childBounds (shapes fs) i =
      (if (kids fs i).length = 0 then 0 else 1 + cnt fs i, (kids fs i).length) := by
  unfold childBounds
  rw [childBoundsFrom_eq fs hb i (i + 1) 0 0 (by omega)]
  -- the scan from `i + 1` sees all children: none sits at or before `i`
  have hK : blk fs i (i + 1) = kids fs i := by
    rw [kids_eq_filter fs hb hn]
    unfold blk
    by_cases hi : i + 1 ≤ fs.length
    · have hsplit : List.range' 1 (fs.length - 1) =
          List.range' 1 i ++ List.range' (i + 1) (fs.length - (i + 1)) := by
        rw [show i + 1 = 1 + 1 * i by omega, List.range'_append]; congr 1; omega
      rw [hsplit, List.filter_append]
      have : (List.range' 1 i).filter (fun x => par fs x = i) = [] := by
        rw [List.filter_eq_nil_iff]; intro x hx; simp [List.mem_range'] at hx
        have := hb.parent_lt x (by omega) (by omega); simp only [par] at *; simp; omega
      rw [this, List.nil_append]
    · have h1 : fs.length - (i + 1) = 0 := by omega
      rw [h1, List.range'_zero, List.filter_nil]
      symm; rw [List.filter_eq_nil_iff]; intro x hx; simp [List.mem_range'] at hx
      have := hb.parent_lt x (by omega) (by omega); simp only [par] at *; simp; omega
  rw [hK]
  split
  · rename_i h; simp [h]
  · rename_i h
    have hne : (kids fs i).length ≠ 0 := by intro h0; exact h (List.eq_nil_of_length_eq_zero h0)
    simp only [hne, ite_false, ite_true]
    rw [kids_eq_range' fs hb hn i]
    have : (kids fs i).length = (kids fs i).length - 1 + 1 := by omega
    rw [List.length_range', this, List.range'_succ]
    simp

end ConditionPacking
