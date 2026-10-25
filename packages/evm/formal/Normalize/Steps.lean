import Normalize.Effects

/-!
# Each normalization step keeps the meaning

`Same W a b`: `a` and `b` mean the same, and agree on reading a parameter
(which decides the fields later `Matches` siblings read).
-/

namespace Normalize

section
variable {V S C Ch : Type} {W : World V S C} {step : C → Ch → Option C}

def Same (W : World V S C) (a b : Cond) : Prop := sem W a = sem W b ∧ isStruct a = isStruct b

theorem Same.refl (a : Cond) : Same W a a := ⟨rfl, rfl⟩
theorem Same.symm {a b : Cond} (h : Same W a b) : Same W b a := ⟨h.1.symm, h.2.symm⟩
theorem Same.trans {a b c : Cond} (h1 : Same W a b) (h2 : Same W b c) : Same W a c :=
  ⟨h1.1.trans h2.1, h1.2.trans h2.2⟩

/-- Lists that are pointwise `Same`. -/
inductive Pw (W : World V S C) : List Cond → List Cond → Prop
  | nil : Pw W [] []
  | cons {a b as bs} : Same W a b → Pw W as bs → Pw W (a :: as) (b :: bs)

theorem Pw.refl : ∀ l : List Cond, Pw W l l
  | [] => .nil
  | x :: xs => .cons (Same.refl x) (Pw.refl xs)

theorem Pw.of_map {f : Cond → Cond} : ∀ {l : List Cond}, (∀ x ∈ l, Same W (f x) x) → Pw W (l.map f) l
  | [], _ => .nil
  | x :: xs, h => .cons (h x (by simp)) (Pw.of_map fun y hy => h y (by simp [hy]))

theorem Pw.append {a b a' b' : List Cond} (h1 : Pw W a a') (h2 : Pw W b b') :
    Pw W (a ++ b) (a' ++ b') := by
  induction h1 with
  | nil => exact h2
  | cons h _ ih => exact .cons h ih

theorem Pw.map_sem {l l' : List Cond} (h : Pw W l l') (v : V) :
    l.map (fun c => sem W c v) = l'.map (fun c => sem W c v) := by
  induction h with
  | nil => rfl
  | cons h _ ih => simp [h.1, ih]

theorem Pw.map_sem' {l l' : List Cond} (h : Pw W l l') : l.map (sem W) = l'.map (sem W) := by
  induction h with
  | nil => rfl
  | cons h _ ih => simp [h.1, ih]

theorem Pw.length {l l' : List Cond} (h : Pw W l l') : l.length = l'.length := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [ih]

theorem Pw.any_struct {l l' : List Cond} (h : Pw W l l') : l.any isStruct = l'.any isStruct := by
  induction h with
  | nil => rfl
  | cons h _ ih => simp [h.2, ih]

theorem Pw.assign {l l' : List Cond} (h : Pw W l l') (fs : List V) (v : V) :
    (assign W.dflt l fs v).map (fun p => sem W p.1 p.2) =
      (assign W.dflt l' fs v).map (fun p => sem W p.1 p.2) := by
  induction h generalizing fs with
  | nil => rfl
  | cons h _ ih =>
    simp only [Normalize.assign, h.2]
    split <;> simp [h.1, ih]

theorem matchesT_congr {e cv} {l l' : List Cond}
    (h : ∀ fs v, seqT ((assign W.dflt l fs v).map fun p => sem W p.1 p.2) =
      seqT ((assign W.dflt l' fs v).map fun p => sem W p.1 p.2)) :
    matchesT W e cv l = matchesT W e cv l' := by
  funext v sl cs
  simp only [matchesT, h]

/-- Replacing the children by pointwise `Same` ones. -/
theorem same_congr (c : Cond) {l : List Cond} (h : Pw W l c.ch) :
    Same W { c with ch := l } c := by
  constructor
  · funext v
    rw [sem_eq, sem_eq]
    simp only [h.map_sem, h.map_sem']
    rw [matchesT_congr (l := l) (l' := c.ch) fun fs v => by rw [h.assign]]
  · rw [isStruct_eq, isStruct_eq]
    simp only [h.any_struct]

theorem sem_pass {x : Cond} (h : isPass x = true) (w : V) : sem W x w = passT := by
  rw [sem_eq, ite_pos' (by simpa [isPass] using h)]

theorem sem_and {c : Cond} (h : c.op = 1) (v : V) :
    sem W c v = seqT (c.ch.map fun x => sem W x v) := by
  rw [sem_eq]; simp [h]

theorem sem_or {c : Cond} (h : c.op = 2) (v : V) :
    sem W c v = orT (c.ch.map fun x => sem W x v) := by
  rw [sem_eq]; simp [h]

theorem sem_matches {c : Cond} (h : c.op = 5) (he : c.enc = 3 ∨ c.enc = 5) (v : V) :
    sem W c v = matchesT W c.enc c.cv c.ch v := by
  rw [sem_eq]; simp [h, he]

theorem struct_log {c : Cond} (h : c.op = 1 ∨ c.op = 2) : isStruct c = c.ch.any isStruct := by
  rw [isStruct_eq]; rcases h with h | h <;> simp [h]

theorem struct_nonlog {c : Cond} (h1 : c.op ≠ 1) (h2 : c.op ≠ 2) :
    isStruct c = !(c.enc == 0 || c.enc == 6) := by
  rw [isStruct_eq]; simp [h1, h2]

theorem logical_op {c : Cond} (h : isLogical c = true) : c.op = 1 ∨ c.op = 2 := by
  simpa [isLogical] using h

theorem seqT_pass_cons (l : List (Thunk S C)) : seqT (passT :: l) = seqT l := by
  funext sl cs; rfl

/-! ## Matches children -/

theorem assign_append (d : V) (a b : List Cond) (fs : List V) (v : V) :
    assign d (a ++ b) fs v = assign d a fs v ++ assign d b (fs.drop (a.countP isStruct)) v := by
  induction a generalizing fs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.cons_append, Normalize.assign, List.countP_cons]
    by_cases h : isStruct x
    · simp only [h, ite_true, ih, List.cons_append]
      congr 2
      cases fs <;> simp []
    · simp [h, ih]

/-! ## `flattenNestedBranches`, `dedupeChildren`, `unwrapSingleChild` -/

theorem seqT_flattenCh (l : List Cond) (v : V) :
    seqT ((flattenCh 1 l).map fun x => sem W x v) = seqT (l.map fun x => sem W x v) := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    funext sl cs
    simp only [flattenCh, List.flatMap_cons, List.map_append] at ih ⊢
    rw [seqT_append]
    split
    · rename_i hx
      rw [List.map_cons, seqT_cons, sem_and (by simpa using hx), ih]
    · rw [List.map_cons, List.map_nil, seqT_single, List.map_cons, seqT_cons, ih]

theorem orT_flattenCh (l : List Cond) (v : V) :
    orT ((flattenCh 2 l).map fun x => sem W x v) = orT (l.map fun x => sem W x v) := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    funext sl cs
    have e : flattenCh 2 (x :: xs) = (if x.op == 2 then x.ch else [x]) ++ flattenCh 2 xs := rfl
    rw [e, List.map_append, orT_append, ih, List.map_cons, orT]
    by_cases hx : x.op = 2
    · simp only [hx, beq_self_eq_true, ite_true, sem_or hx]
    · simp only [show (x.op == 2) = false by simpa using hx, Bool.false_eq_true, ite_false,
        List.map_cons, List.map_nil, orT_single]

theorem any_flattenCh {op : Nat} (hop : op = 1 ∨ op = 2) (l : List Cond) :
    (flattenCh op l).any isStruct = l.any isStruct := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [flattenCh, List.flatMap_cons, List.any_append, List.any_cons] at ih ⊢
    rw [ih]
    split
    · rename_i hx
      rw [struct_log (by simp at hx; omega)]
    · simp

theorem flatten_same (c : Cond) : Same W (flatten c) c := by
  unfold flatten
  split
  · rename_i hl
    have hl' := logical_op hl
    constructor
    · funext v
      rcases hl' with h | h
      · rw [sem_and (c := { c with ch := flattenCh c.op c.ch }) h, sem_and h, h, seqT_flattenCh]
      · rw [sem_or (c := { c with ch := flattenCh c.op c.ch }) h, sem_or h, h, orT_flattenCh]
    · rw [struct_log (c := { c with ch := flattenCh c.op c.ch }) hl', struct_log hl']
      exact any_flattenCh hl' c.ch
  · exact Same.refl _

theorem unwrap_same (c : Cond) : Same W (unwrap c) c := by
  unfold unwrap
  split
  · rename_i hl
    have hl' := logical_op hl
    split
    · rename_i x hx
      constructor
      · funext v
        rcases hl' with h | h
        · rw [sem_and h, hx]; simp [seqT_single]
        · rw [sem_or h, hx]; simp [orT_single]
      · rw [struct_log hl', hx]; simp
    · exact Same.refl _
  · exact Same.refl _

theorem dedupeL_any (p : Cond → Bool) (b : Bool) :
    ∀ (seen xs : List Cond), ((dedupeL b seen xs).any p || seen.any p) = (xs.any p || seen.any p)
  | _, [] => rfl
  | seen, x :: xs => by
    simp only [dedupeL]
    by_cases hx : seen.contains x = true
    · have hm : x ∈ seen := by simpa using hx
      have hps : p x = true → seen.any p = true := fun h => List.any_eq_true.2 ⟨x, hm, h⟩
      simp only [hx, ite_true]
      have ih := dedupeL_any p b seen xs
      split
      · simp only [List.any_cons]
        cases h : p x <;> simp_all
      · simp only [List.any_cons]
        cases h : p x <;> simp_all
    · simp only [hx, Bool.false_eq_true, ite_false, List.any_cons]
      have := dedupeL_any p b (x :: seen) xs
      simp only [List.any_cons] at this
      cases h1 : p x <;> simp_all

/-- In an `And`, a duplicate that charges nothing passed already. -/
theorem seqT_dedupeL (hW : W.Ok step) (v : V) (sl : S) :
    ∀ (seen xs : List Cond), (∀ x ∈ xs, writes x = false) →
      (∀ y ∈ seen, charges y = false → ∀ cs, sem W y v sl cs = (some cs, sl)) →
      ∀ cs, seqT ((dedupeL true seen xs).map fun x => sem W x v) sl cs =
        seqT (xs.map fun x => sem W x v) sl cs
  | _, [], _, _, _ => rfl
  | seen, x :: xs, hxs, hseen, cs => by
    have hx := hxs x (by simp)
    have hxs' : ∀ y ∈ xs, writes y = false := fun y hy => hxs y (by simp [hy])
    obtain ⟨r, hr⟩ := keeps_eq (keeps_sem hW x hx v) sl cs
    simp only [dedupeL, Bool.true_and]
    split
    · rename_i hc
      split
      · simp only [List.map_cons, seqT_cons, hr]
        rcases r with _ | c'
        · rfl
        · exact seqT_dedupeL hW v sl seen xs hxs' hseen c'
      · rename_i hch
        have := hseen x (by simpa using hc) (by simpa using hch) cs
        simp only [List.map_cons, seqT_cons, this, bindR_some]
        exact seqT_dedupeL hW v sl seen xs hxs' hseen cs
    · simp only [List.map_cons, seqT_cons, hr]
      rcases r with _ | c'
      · rfl
      · refine seqT_dedupeL hW v sl (x :: seen) xs hxs' ?_ c'
        intro y hy hcy cs2
        rcases List.mem_cons.1 hy with rfl | hy
        · obtain ⟨b, hb⟩ := pure_sem hW y hx hcy v
          have hb1 : b sl = true := by
            rw [hb] at hr; cases h : b sl <;> simp_all
          rw [hb]; simp [hb1]
        · exact hseen y hy hcy cs2

/-- In an `Or`, a duplicate failed already, with the same consumptions and slots. -/
theorem orT_dedupeL (hW : W.Ok step) (v : V) (sl : S) (cs : C) :
    ∀ (seen xs : List Cond), (∀ x ∈ xs, writes x = false) →
      (∀ y ∈ seen, sem W y v sl cs = (none, sl)) →
      orT ((dedupeL false seen xs).map fun x => sem W x v) sl cs =
        orT (xs.map fun x => sem W x v) sl cs
  | _, [], _, _ => rfl
  | seen, x :: xs, hxs, hseen => by
    have hx := hxs x (by simp)
    have hxs' : ∀ y ∈ xs, writes y = false := fun y hy => hxs y (by simp [hy])
    obtain ⟨r, hr⟩ := keeps_eq (keeps_sem hW x hx v) sl cs
    simp only [dedupeL, Bool.false_and, Bool.false_eq_true, ite_false]
    split
    · rename_i hc
      have := hseen x (by simpa using hc)
      simp only [List.map_cons, orT, this]
      exact orT_dedupeL hW v sl cs seen xs hxs' hseen
    · simp only [List.map_cons, orT, hr]
      rcases r with _ | c'
      · refine orT_dedupeL hW v sl cs (x :: seen) xs hxs' ?_
        intro y hy
        rcases List.mem_cons.1 hy with rfl | hy
        · exact hr
        · exact hseen y hy
      · rfl

theorem dedupe_same (hW : W.Ok step) (c : Cond) : Same W (dedupe c) c := by
  unfold dedupe
  split
  · rename_i hc
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hc
    have hl' := logical_op hc.1
    have hw : ∀ x ∈ c.ch, writes x = false := fun x hx => any_false hc.2 hx
    constructor
    · funext v sl cs
      rcases hl' with h | h
      · rw [sem_and (c := { c with ch := dedupeL (c.op == 1) [] c.ch }) h, sem_and h]
        simp only [h, beq_self_eq_true]
        exact seqT_dedupeL hW v sl [] c.ch hw (by simp) cs
      · rw [sem_or (c := { c with ch := dedupeL (c.op == 1) [] c.ch }) h, sem_or h]
        simp only [h, show (2 == 1) = false from rfl]
        exact orT_dedupeL hW v sl cs [] c.ch hw (by simp)
    · rw [struct_log (c := { c with ch := dedupeL (c.op == 1) [] c.ch }) hl', struct_log hl']
      simpa using dedupeL_any isStruct (c.op == 1) [] c.ch
  · exact Same.refl _

/-! ## `sortBranchesCanonical` -/

theorem sortCh_perm (l : List Cond) : (sortCh l).Perm l := by
  have := List.filter_append_perm (fun x : Cond => x.enc == 5) (l.mergeSort sortLe)
  unfold sortCh
  have e : (fun x : Cond => x.enc != 5) = (fun x => !(x.enc == 5)) := by funext x; simp [bne]
  rw [e]
  exact this.trans (List.mergeSort_perm _ _)

theorem sortB_same (hW : W.Ok step) (c : Cond) : Same W (sortB c) c := by
  unfold sortB
  split
  · rename_i hc
    simp only [Bool.and_eq_true] at hc
    have hl' := logical_op hc.1
    have hperm := sortCh_perm c.ch
    constructor
    · funext v
      rcases hl' with h | h
      · rw [sem_and (c := { c with ch := sortCh c.ch }) h, sem_and h]
        have hr : canReorderAnd c.ch = true := by
          simp [canReorder, h] at hc; exact hc.2.1
        have := seqT_perm hW (W := W) (l := c.ch.map (·, v)) (l' := (sortCh c.ch).map (·, v))
          (hperm.symm.map _) (by simpa [List.map_map, Function.comp_def] using hr)
        simpa [List.map_map, Function.comp_def] using this.symm
      · rw [sem_or (c := { c with ch := sortCh c.ch }) h, sem_or h]
        have hr : canReorderOr c.ch = true := by
          have h1 : ¬ c.op = 1 := by omega
          simp [canReorder, h, h1] at hc; exact hc.2.1
        exact (orT_perm hW hperm.symm hr v).symm
    · rw [struct_log (c := { c with ch := sortCh c.ch }) hl', struct_log hl']
      exact any_perm hperm
  · exact Same.refl _

end
end Normalize
