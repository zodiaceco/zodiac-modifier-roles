import Normalize.Effects

/-!
# Exclusive `Or` branches

`disjoint a b` (the SDK's `disjoint` in `effects.ts`) means that no value
passes both `a` and `b`, whatever the slots and consumptions each starts
from (`disjoint_sound`). An `Or` whose charging children each exclude every
other child has at most one passing branch, so the branch that charges does
not depend on the order: `canReorderOr` lets the `Or` be sorted
(`orT_perm`), and does not depend on the order itself (`canReorderOr_perm`).

The proof reads both branches through the world, so it holds for every
value the world reads, including those of calldata a caller crafts: what
`EqualTo` compares is the word the contract reads (`World.Ok.eqWord`), and
two `Matches` of the same type read the same fields (`World.NormOk.twin`).
-/

namespace Normalize

section
variable {V S C Ch : Type} {W : World V S C} {step : C → Ch → Option C}

theorem sem_and {c : Cond} (h : c.op = 1) (v : V) :
    sem W c v = seqT (c.ch.map fun x => sem W x v) := by
  rw [sem_eq]; simp [h]

theorem sem_or {c : Cond} (h : c.op = 2) (v : V) :
    sem W c v = orT (c.ch.map fun x => sem W x v) := by
  rw [sem_eq]; simp [h]

theorem sem_matches {c : Cond} (h : c.op = 5) (he : c.enc = 3 ∨ c.enc = 5) (v : V) :
    sem W c v = matchesT W c.enc c.cv c.ch v := by
  rw [sem_eq]; simp [h, he]

/-- Passes from some state. -/
def Passes (t : Thunk S C) : Prop := ∃ sl cs c s, t sl cs = (some c, s)

theorem seqT_passes : ∀ {l : List (Thunk S C)} {sl cs c s},
    seqT l sl cs = (some c, s) → ∀ t ∈ l, Passes t
  | [], _, _, _, _, _, t, ht => by simp at ht
  | t :: ts, sl, cs, c, s, h, u, hu => by
    rw [seqT_cons] at h
    rcases e : t sl cs with ⟨_ | c1, s1⟩
    · rw [e] at h; simp at h
    · rw [e, bindR_some] at h
      rcases List.mem_cons.1 hu with rfl | hu
      · exact ⟨sl, cs, c1, s1, e⟩
      · exact seqT_passes h u hu

theorem orT_passes : ∀ {l : List (Thunk S C)} {sl cs c s},
    orT l sl cs = (some c, s) → ∃ t ∈ l, Passes t
  | [], _, _, _, _, h => by simp [orT] at h
  | t :: ts, sl, cs, c, s, h => by
    simp only [orT] at h
    rcases e : t sl cs with ⟨_ | c1, s1⟩
    · rw [e] at h
      obtain ⟨u, hu, hp⟩ := orT_passes h
      exact ⟨u, List.mem_cons_of_mem _ hu, hp⟩
    · exact ⟨t, by simp, sl, cs, c1, s1, e⟩

theorem matchesT_passes {e : Nat} {cv : List Nat} {ch : List Cond} {v : V}
    (h : Passes (matchesT W e cv ch v)) :
    W.gate e cv ch v = true ∧
      ∀ p ∈ assign W.dflt ch (W.fields e cv ch v) v, Passes (sem W p.1 p.2) := by
  obtain ⟨sl, cs, c, s, h⟩ := h
  simp only [matchesT] at h
  split at h
  · rename_i hg
    refine ⟨hg, fun p hp => seqT_passes h _ (List.mem_map.2 ⟨p, hp, rfl⟩)⟩
  · simp at h

/-- The `i`-th structural child of a `Matches` reads field `i`. -/
theorem mem_assign_struct (d : V) (v : V) :
    ∀ (ch : List Cond) (fs : List V) (i : Nat) (hi : i < (ch.filter isStruct).length),
      ((ch.filter isStruct)[i], fs.getD i d) ∈ assign d ch fs v
  | [], _, _, hi => by simp at hi
  | c :: cs, fs, i, hi => by
    by_cases hc : isStruct c = true
    · simp only [List.filter_cons, hc, ite_true] at hi ⊢
      simp only [assign, hc, ite_true]
      cases i with
      | zero => cases fs <;> simp
      | succ j =>
        apply List.mem_cons_of_mem
        have := mem_assign_struct d v cs fs.tail j (by simpa using hi)
        cases fs <;> simpa using this
    · simp only [List.filter_cons, hc] at hi ⊢
      simp only [assign, hc]
      exact List.mem_cons_of_mem _ (mem_assign_struct d v cs fs i (by simpa using hi))

theorem mem_zip_get {a b : List Cond} {p : Cond × Cond} (h : p ∈ a.zip b) :
    ∃ i, ∃ (h1 : i < a.length) (h2 : i < b.length), p = (a[i], b[i]) := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem h
  simp only [List.length_zip] at hi
  exact ⟨i, by omega, by omega, by simp⟩

theorem sem_ext {c : Cond} (h0 : c.op ≠ 0) (h1 : c.op ≠ 1) (h2 : c.op ≠ 2) (h5 : c.op ≠ 5) (v : V) :
    sem W c v = W.ext c (c.ch.map (sem W)) v := by
  rw [sem_eq]; simp [h0, h1, h2, h5]

theorem pinned_op {c : Cond} {w : List Nat} (h : pinned c = some w) : c.op = 16 := by
  unfold pinned at h; split at h
  · rename_i hc; exact hc.1
  · simp at h

/-- **Disjoint conditions never both pass on one value**, from any states. -/
theorem disjoint_sound (hW : W.Ok step) {inv : Cond → Prop} (hN : W.NormOk inv) :
    ∀ (a b : Cond), disjoint a b = true → ∀ v, Passes (sem W a v) → Passes (sem W b v) → False
  | a, b, hd, v, ha, hb => by
    rw [disjoint] at hd
    by_cases a1 : a.op = 1
    · rw [if_pos a1] at hd
      obtain ⟨x, -, hx⟩ := List.any_eq_true.1 hd
      obtain ⟨sl, cs, c, s, e⟩ := ha
      rw [sem_and a1] at e
      have hxp := seqT_passes e _ (List.mem_map.2 ⟨x.1, x.2, rfl⟩)
      exact disjoint_sound hW hN x.1 b hx v hxp hb
    rw [if_neg a1] at hd
    by_cases b1 : b.op = 1
    · rw [if_pos b1] at hd
      obtain ⟨y, -, hy⟩ := List.any_eq_true.1 hd
      obtain ⟨sl, cs, c, s, e⟩ := hb
      rw [sem_and b1] at e
      have hyp := seqT_passes e _ (List.mem_map.2 ⟨y.1, y.2, rfl⟩)
      exact disjoint_sound hW hN a y.1 hy v ha hyp
    rw [if_neg b1] at hd
    by_cases a2 : a.op = 2
    · rw [if_pos a2] at hd
      obtain ⟨sl, cs, c, s, e⟩ := ha
      rw [sem_or a2] at e
      obtain ⟨t, ht, hp⟩ := orT_passes e
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 ht
      exact disjoint_sound hW hN x b (List.all_eq_true.1 hd ⟨x, hx⟩ (by simp)) v hp hb
    rw [if_neg a2] at hd
    by_cases b2 : b.op = 2
    · rw [if_pos b2] at hd
      obtain ⟨sl, cs, c, s, e⟩ := hb
      rw [sem_or b2] at e
      obtain ⟨t, ht, hp⟩ := orT_passes e
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 ht
      exact disjoint_sound hW hN a y (List.all_eq_true.1 hd ⟨y, hy⟩ (by simp)) v ha hp
    rw [if_neg b2] at hd
    by_cases m : a.op = 5 ∧ b.op = 5
    · rw [if_pos m] at hd
      simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hd
      obtain ⟨⟨⟨⟨⟨he, hee⟩, hcv⟩, htw⟩, -⟩, hany⟩ := hd
      obtain ⟨⟨p, hp⟩, hpd⟩ := List.any_eq_true.1 hany
      obtain ⟨i, h1, h2, rfl⟩ := mem_zip_get hp
      rw [sem_matches m.1 he] at ha
      rw [sem_matches m.2 (hee ▸ he)] at hb
      obtain ⟨-, ka⟩ := matchesT_passes ha
      obtain ⟨-, kb⟩ := matchesT_passes hb
      have hf : W.fields b.enc b.cv b.ch v = W.fields a.enc a.cv a.ch v := by
        rw [← hee, ← hcv]; exact ((hN.twin a.enc a.cv a.ch b.ch htw v).1).symm
      have pa := ka _ (mem_assign_struct W.dflt v a.ch (W.fields a.enc a.cv a.ch v) i h1)
      have pb := kb _ (mem_assign_struct W.dflt v b.ch (W.fields b.enc b.cv b.ch v) i h2)
      rw [hf] at pb
      exact disjoint_sound hW hN _ _ hpd.2 _ pa pb
    rw [if_neg m] at hd
    split at hd
    · rename_i x y hx hy
      have hne : x ≠ y := by simpa using hd
      have oa := pinned_op hx
      have ob := pinned_op hy
      rw [sem_ext (by omega) (by omega) (by omega) (by omega)] at ha hb
      obtain ⟨sl, cs, c, s, ea⟩ := ha
      obtain ⟨sl', cs', c', s', eb⟩ := hb
      rcases hW.eqWord a b _ _ v x y hx hy hne sl cs sl' cs' with h | h
      · rw [ea] at h; simp at h
      · rw [eb] at h; simp at h
    · simp at hd
termination_by a b => sizeOf a + sizeOf b
decreasing_by
  all_goals first
    | (have := sizeOf_lt_of_mem x.2; omega)
    | (have := sizeOf_lt_of_mem y.2; omega)
    | (have := sizeOf_lt_of_mem hx; omega)
    | (have := sizeOf_lt_of_mem hy; omega)
    | (have e1 := sizeOf_lt_of_mem (List.mem_filter.1 (List.getElem_mem h1)).1
       have e2 := sizeOf_lt_of_mem (List.mem_filter.1 (List.getElem_mem h2)).1
       omega)

/-! ## Reordering an `Or` -/

theorem orT_swap_pure {a b : Thunk S C} (ha : PureT a) (hb : PureT b) (l : List (Thunk S C)) :
    orT (a :: b :: l) = orT (b :: a :: l) := by
  obtain ⟨p, hp⟩ := ha
  obtain ⟨q, hq⟩ := hb
  funext sl cs
  simp only [orT, hp, hq]
  by_cases h1 : p sl <;> by_cases h2 : q sl <;> simp [h1, h2]

/-- Two branches that keep the slots and never both pass may change places. -/
theorem orT_swap_excl {a b : Thunk S C} (ha : KeepsT a) (hb : KeepsT b)
    (hx : ∀ sl cs, (a sl cs).1 = none ∨ (b sl cs).1 = none) (l : List (Thunk S C)) :
    orT (a :: b :: l) = orT (b :: a :: l) := by
  funext sl cs
  obtain ⟨ra, ea⟩ := keeps_eq ha sl cs
  obtain ⟨rb, eb⟩ := keeps_eq hb sl cs
  have h := hx sl cs
  rw [ea, eb] at h
  simp only [orT, ea, eb]
  rcases ra with _ | ca <;> rcases rb with _ | cb <;> simp_all [orT]

theorem pairOk_comm (a b : Cond) : pairOk a b = pairOk b a := by
  unfold pairOk; exact Bool.and_comm _ _

theorem pairwiseOk_iff : ∀ l : List Cond, pairwiseOk l = true ↔ l.Pairwise fun x y => pairOk x y = true
  | [] => by simp [pairwiseOk]
  | x :: xs => by
    simp only [pairwiseOk, Bool.and_eq_true, List.all_eq_true, List.pairwise_cons, pairwiseOk_iff xs]

theorem pairwiseOk_perm {l l' : List Cond} (h : l.Perm l') : pairwiseOk l = pairwiseOk l' := by
  rw [Bool.eq_iff_iff, pairwiseOk_iff, pairwiseOk_iff]
  exact h.pairwise_iff fun {x y} hxy => by rwa [pairOk_comm]

/-- **The rule does not depend on the order of the children.** -/
theorem canReorderOr_perm {l l' : List Cond} (h : l.Perm l') : canReorderOr l = canReorderOr l' := by
  simp only [canReorderOr, any_perm h, pairwiseOk_perm h]

theorem canReorderOr_tail {x : Cond} {l : List Cond} (h : canReorderOr (x :: l) = true) :
    canReorderOr l = true := by
  simp only [canReorderOr, List.any_cons, pairwiseOk, Bool.and_eq_true, Bool.not_eq_true',
    Bool.or_eq_false_iff, Bool.or_eq_true] at h ⊢
  refine ⟨h.1.2, ?_⟩
  rcases h.2 with h2 | h2
  · exact Or.inl h2.2
  · exact Or.inr h2.2

/-- Excluding branches never both pass on one value. -/
theorem excl_thunk (hW : W.Ok step) {inv : Cond → Prop} (hN : W.NormOk inv) {a b : Cond}
    (h : excludes a b = true) (v : V) :
    ∀ sl cs, (sem W a v sl cs).1 = none ∨ (sem W b v sl cs).1 = none := by
  intro sl cs
  unfold excludes at h
  simp only [Bool.and_eq_true] at h
  rcases ea : sem W a v sl cs with ⟨_ | ca, sa⟩
  · exact Or.inl rfl
  rcases eb : sem W b v sl cs with ⟨_ | cb, sb⟩
  · exact Or.inr rfl
  exact (disjoint_sound hW hN a b h.2 v ⟨sl, cs, ca, sa, ea⟩ ⟨sl, cs, cb, sb, eb⟩).elim

/-- **An `Or` the SDK may reorder means the same in every order.** -/
theorem orT_perm (hW : W.Ok step) {inv : Cond → Prop} (hN : W.NormOk inv) {l l' : List Cond}
    (hp : l.Perm l') (h : canReorderOr l = true) (v : V) :
    orT (l.map fun c => sem W c v) = orT (l'.map fun c => sem W c v) := by
  induction hp with
  | nil => rfl
  | cons x _ ih =>
    funext sl cs
    simp only [List.map_cons, orT]
    rw [ih (canReorderOr_tail h)]
  | swap x y l =>
    simp only [List.map_cons]
    simp only [canReorderOr, List.any_cons, pairwiseOk, List.all_cons, Bool.and_eq_true,
      Bool.not_eq_true', Bool.or_eq_false_iff, Bool.or_eq_true] at h
    obtain ⟨⟨hwy, hwx, -⟩, hc⟩ := h
    have ky := keeps_sem hW y hwy v
    have kx := keeps_sem hW x hwx v
    rcases hc with ⟨hcy, hcx, -⟩ | ⟨⟨hyx, -⟩, -⟩
    · exact orT_swap_pure (pure_sem hW y hwy hcy v) (pure_sem hW x hwx hcx v) _
    · unfold pairOk at hyx
      simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hyx
      rcases hyx with ⟨hy | hy, hx | hx⟩
      · exact orT_swap_pure (pure_sem hW y hwy hy v) (pure_sem hW x hwx hx v) _
      · exact orT_swap_excl ky kx (fun sl cs => (excl_thunk hW hN hx v sl cs).symm) _
      · exact orT_swap_excl ky kx (excl_thunk hW hN hy v) _
      · exact orT_swap_excl ky kx (excl_thunk hW hN hy v) _
  | trans h1 h2 ih1 ih2 =>
    rw [ih1 h, ih2 (by rwa [← canReorderOr_perm h1])]

end
end Normalize
