import Normalize.Sem

/-!
# From the syntactic effect checks to effects

`writes`, `charges` and `chooses` (the SDK's `effects.ts`) bound what a
subtree does to the evaluator state. With them, `canReorderAnd` lets any
two children of a list commute, so the list's `And` (or `Matches`) meaning
is the same in every order.
-/

namespace Normalize

section
variable {V S C Ch : Type} {W : World V S C} {step : C → Ch → Option C}

theorem any_false {p : Cond → Bool} {l : List Cond} (h : l.any p = false) {x : Cond}
    (hx : x ∈ l) : p x = false := by
  rw [List.any_eq_false] at h
  simpa using h x hx

theorem keeps_sem (hW : W.Ok step) (c : Cond) (hc : writes c = false) (v : V) :
    KeepsT (sem W c v) := by
  rw [writes_eq, Bool.or_eq_false_iff, beq_eq_false_iff_ne] at hc
  have hch : ∀ x ∈ c.ch, ∀ w, KeepsT (sem W x w) :=
    fun x hx w => keeps_sem hW x (any_false hc.2 hx) w
  rw [sem_eq]
  by_cases h0 : c.op = 0
  · rw [ite_pos' h0]; intro sl cs; rfl
  rw [ite_neg' h0]
  by_cases h1 : c.op = 1
  · rw [ite_pos' h1]; exact seqT_keeps (by simpa using fun x hx => hch x hx v)
  rw [ite_neg' h1]
  by_cases h2 : c.op = 2
  · rw [ite_pos' h2]; exact orT_keeps (by simpa using fun x hx => hch x hx v)
  rw [ite_neg' h2]
  by_cases h5 : c.op = 5 ∧ (c.enc = 3 ∨ c.enc = 5)
  · rw [ite_pos' h5]
    intro sl cs
    simp only [matchesT]
    split
    · exact seqT_keeps (by
        simp only [List.mem_map]
        rintro t ⟨p, hp, rfl⟩
        exact hch p.1 (mem_assign hp) p.2) sl cs
    · rfl
  rw [ite_neg' h5]
  exact hW.keeps _ _ _ _ hc.1 (by simpa using fun x hx => hch x hx) v
termination_by c
decreasing_by exact sizeOf_lt_of_mem ‹_›

theorem pure_sem (hW : W.Ok step) (c : Cond) (hw : writes c = false) (hc : charges c = false)
    (v : V) : PureT (sem W c v) := by
  rw [writes_eq, Bool.or_eq_false_iff, beq_eq_false_iff_ne] at hw
  rw [charges_eq] at hc
  simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne] at hc
  have hch : ∀ x ∈ c.ch, ∀ w, PureT (sem W x w) :=
    fun x hx w => pure_sem hW x (any_false hw.2 hx) (any_false hc.2 hx) w
  rw [sem_eq]
  by_cases h0 : c.op = 0
  · rw [ite_pos' h0]; exact ⟨fun _ => true, fun _ _ => rfl⟩
  rw [ite_neg' h0]
  by_cases h1 : c.op = 1
  · rw [ite_pos' h1]; exact seqT_pure (by simpa using fun x hx => hch x hx v)
  rw [ite_neg' h1]
  by_cases h2 : c.op = 2
  · rw [ite_pos' h2]; exact orT_pure (by simpa using fun x hx => hch x hx v)
  rw [ite_neg' h2]
  by_cases h5 : c.op = 5 ∧ (c.enc = 3 ∨ c.enc = 5)
  · rw [ite_pos' h5]
    have := seqT_pure (S := S) (C := C)
      (l := (assign W.dflt c.ch (W.fields c.enc v) v).map fun p => sem W p.1 p.2) (by
        simp only [List.mem_map]
        rintro t ⟨p, hp, rfl⟩
        exact hch p.1 (mem_assign hp) p.2)
    obtain ⟨b, hb⟩ := this
    refine ⟨fun sl => W.gate c.enc c.cv v && b sl, fun sl cs => ?_⟩
    simp only [matchesT]
    split <;> simp_all
  rw [ite_neg' h5]
  exact hW.pure _ _ _ _ hw.1 hc.1.1.1 hc.1.1.2 hc.1.2 (by simpa using fun x hx => hch x hx) v
termination_by c
decreasing_by exact sizeOf_lt_of_mem ‹_›

theorem charger_sem (hW : W.Ok step) (c : Cond) (hw : writes c = false)
    (hc : chooses c = false) (v : V) : ChargerT step (sem W c v) := by
  have hw' := hw
  rw [writes_eq, Bool.or_eq_false_iff, beq_eq_false_iff_ne] at hw
  rw [chooses_eq, Bool.or_eq_false_iff] at hc
  have hch : ∀ x ∈ c.ch, ∀ w, ChargerT step (sem W x w) :=
    fun x hx w => charger_sem hW x (any_false hw.2 hx) (any_false hc.2 hx) w
  -- a choice over charges is excluded, so a choice node charges nothing
  by_cases ho : c.op = 2 ∨ c.op = 6 ∨ c.op = 10
  · have : charges c = false := by
      have h1 := hc.1
      rcases ho with h | h | h <;> simpa [h] using h1
    exact (pure_sem hW _ hw' this v).charger step
  have h2 : c.op ≠ 2 := fun h => ho (Or.inl h)
  rw [sem_eq]
  by_cases h0 : c.op = 0
  · rw [ite_pos' h0]; exact ⟨fun _ => some [], fun _ _ => rfl⟩
  rw [ite_neg' h0]
  by_cases h1 : c.op = 1
  · rw [ite_pos' h1]; exact seqT_charger (by simpa using fun x hx => hch x hx v)
  rw [ite_neg' h1, ite_neg' h2]
  by_cases h5 : c.op = 5 ∧ (c.enc = 3 ∨ c.enc = 5)
  · rw [ite_pos' h5]
    have := seqT_charger (step := step) (S := S)
      (l := (assign W.dflt c.ch (W.fields c.enc v) v).map fun p => sem W p.1 p.2) (by
        simp only [List.mem_map]
        rintro t ⟨p, hp, rfl⟩
        exact hch p.1 (mem_assign hp) p.2)
    obtain ⟨g, hg⟩ := this
    refine ⟨fun sl => if W.gate c.enc c.cv v then g sl else none, fun sl cs => ?_⟩
    simp only [matchesT]
    split <;> simp_all
  rw [ite_neg' h5]
  exact hW.charger _ _ _ _ hw.1 h2 (fun h => ho (Or.inr (Or.inl h)))
      (fun h => ho (Or.inr (Or.inr h))) (by simpa using fun x hx => hch x hx) v
termination_by c
decreasing_by exact sizeOf_lt_of_mem ‹_›

/-! ## Reordering -/

theorem any_perm {p : Cond → Bool} {l l' : List Cond} (h : l.Perm l') : l.any p = l'.any p := by
  rw [Bool.eq_iff_iff, List.any_eq_true, List.any_eq_true]
  exact ⟨fun ⟨x, hx, hp⟩ => ⟨x, h.mem_iff.1 hx, hp⟩, fun ⟨x, hx, hp⟩ => ⟨x, h.mem_iff.2 hx, hp⟩⟩

theorem canReorderAnd_perm {l l' : List Cond} (h : l.Perm l') :
    canReorderAnd l = canReorderAnd l' := by
  simp only [canReorderAnd, ← List.countP_eq_length_filter, any_perm h, h.countP_eq]

theorem canReorderAnd_tail {x : Cond} {l : List Cond} (h : canReorderAnd (x :: l) = true) :
    canReorderAnd l = true := by
  simp only [canReorderAnd, ← List.countP_eq_length_filter, List.any_cons, List.countP_cons,
    Bool.and_eq_true, Bool.not_eq_true', Bool.or_eq_false_iff, Bool.or_eq_true,
    decide_eq_true_eq] at h ⊢
  refine ⟨h.1.2, ?_⟩
  rcases h.2 with h2 | h2
  · left; split at h2 <;> omega
  · right; exact h2.2

theorem comm_of_canReorder (hW : W.Ok step) {x y : Cond} {l : List Cond}
    (h : canReorderAnd (x :: y :: l) = true) (v w : V) : Comm (sem W x v) (sem W y w) := by
  simp only [canReorderAnd, ← List.countP_eq_length_filter, List.any_cons, List.countP_cons,
    Bool.and_eq_true, Bool.not_eq_true', Bool.or_eq_false_iff, Bool.or_eq_true,
    decide_eq_true_eq] at h
  obtain ⟨⟨hx, hy, -⟩, h2⟩ := h
  rcases h2 with h2 | ⟨hcx, hcy, -⟩
  · by_cases cx : charges x = true
    · have cy : charges y = false := by
        cases hcy : charges y
        · rfl
        · simp only [cx, hcy, ite_true] at h2; omega
      exact (comm_pure (pure_sem hW y hy cy w) (keeps_sem hW x hx v)).symm
    · exact comm_pure (pure_sem hW x hx (by simpa using cx) v) (keeps_sem hW y hy w)
  · exact comm_charger hW.comm (charger_sem hW x hx hcx v) (charger_sem hW y hy hcy w)

/-- An `And` (or `Matches`) list the SDK may reorder means the same in every order. -/
theorem seqT_perm (hW : W.Ok step) {l l' : List (Cond × V)} (hp : l.Perm l')
    (h : canReorderAnd (l.map Prod.fst) = true) :
    seqT (l.map fun p => sem W p.1 p.2) = seqT (l'.map fun p => sem W p.1 p.2) := by
  induction hp with
  | nil => rfl
  | cons x _ ih =>
    funext sl cs
    simp only [List.map_cons, seqT_cons]
    rw [ih (canReorderAnd_tail h)]
  | swap x y l =>
    simp only [List.map_cons]
    exact seqT_swap (comm_of_canReorder hW h _ _) _
  | trans h1 h2 ih1 ih2 =>
    rw [ih1 h, ih2 (by rwa [← canReorderAnd_perm (h1.map Prod.fst)])]

theorem orT_swap_pure {a b : Thunk S C} (ha : PureT a) (hb : PureT b) (l : List (Thunk S C)) :
    orT (a :: b :: l) = orT (b :: a :: l) := by
  obtain ⟨p, hp⟩ := ha
  obtain ⟨q, hq⟩ := hb
  funext sl cs
  simp only [orT, hp, hq]
  by_cases h1 : p sl <;> by_cases h2 : q sl <;> simp [h1, h2]

/-- An `Or` over children that charge nothing and write no slots means the same in every order. -/
theorem orT_perm (hW : W.Ok step) {l l' : List Cond} (hp : l.Perm l')
    (h : canReorderOr l = true) (v : V) :
    orT (l.map fun c => sem W c v) = orT (l'.map fun c => sem W c v) := by
  have hpure : ∀ {l : List Cond}, canReorderOr l = true → ∀ x ∈ l, PureT (sem W x v) := by
    intro l h x hx
    simp only [canReorderOr, Bool.not_eq_true', List.any_eq_false, Bool.or_eq_true,
      not_or, Bool.not_eq_true] at h
    exact pure_sem hW x (h x hx).1 (h x hx).2 v
  induction hp with
  | nil => rfl
  | cons x _ ih =>
    funext sl cs
    simp only [List.map_cons, orT]
    rw [ih (by simp only [canReorderOr, List.any_cons, Bool.not_or] at h ⊢; exact (Bool.and_eq_true _ _ ▸ h).2)]
  | swap x y l =>
    simp only [List.map_cons]
    exact orT_swap_pure (hpure h y (by simp)) (hpure h x (by simp)) _
  | trans h1 h2 ih1 ih2 =>
    rw [ih1 h, ih2 (by
      simp only [canReorderOr] at h ⊢
      rwa [← any_perm h1])]

end
end Normalize
