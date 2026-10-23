import Bridge.NormalizeFits

/-!
# Node-local properties survive normalization

Every node of `normalize k c` is a node of `c` (with other children) or a
fresh `Or`/`Pass` node. So a property of single nodes that ignores their
children holds everywhere in the normalized tree if it does in the input and
for fresh nodes (`allN_normalize`); `CvOk` is one (`cvOk_normalize`).
-/

namespace Bridge
open Normalize

section
variable (P : Cond → Prop) (hloc : ∀ c l, P { c with ch := l } ↔ P c)
  (hOr : P ⟨0, 2, [], []⟩) (hPass : ∀ e, P ⟨e, 0, [], []⟩)

/-- `P` holds of every node. -/
inductive AllN : Cond → Prop
  | mk {c : Cond} : P c → (∀ x ∈ c.ch, AllN x) → AllN c

theorem AllN.self {c : Cond} (h : AllN P c) : P c := by cases h; assumption
theorem AllN.ch {c : Cond} (h : AllN P c) : ∀ x ∈ c.ch, AllN P x := by cases h; assumption

include hloc in
theorem AllN.withCh {c : Cond} (h : P c) {l : List Cond} (hl : ∀ x ∈ l, AllN P x) :
    AllN P { c with ch := l } := .mk ((hloc c l).2 h) hl

theorem mem_pruneCh {c x : Cond} (h : x ∈ pruneCh c) : x ∈ c.ch := by
  unfold pruneCh pruneList at h
  have hre : ∀ y, y ∈ reorderGA c.ch → y ∈ c.ch := by
    intro y hy; unfold reorderGA at hy; split at hy
    · simp only [List.mem_append, List.mem_filter] at hy; rcases hy with h | h <;> exact h.1
    · exact hy
  simp only [List.mem_append, List.mem_filter] at h
  rcases h with h | h
  · exact hre x (List.mem_of_mem_take h)
  · exact hre x (List.mem_of_mem_drop h.1)

include hloc hPass in
theorem allN_get! (hP0 : AllN P (default : Cond)) {o : Cond} (h : AllN P o) (i : Nat) : AllN P o.ch[i]! := by
  by_cases hi : i < o.ch.length
  · exact AllN.ch P h _ (getElem!_mem hi)
  · rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; exact hP0

include hloc hOr in
theorem allN_orNode {hs : List Cond} (h : ∀ x ∈ hs, AllN P x) : AllN P (orNode hs) :=
  AllN.withCh P hloc (c := ⟨0, 2, [], []⟩) hOr h

include hloc hOr hPass in
theorem allN_pushStep (hP0 : AllN P (default : Cond)) {c n : Cond} (h : AllN P c)
    (hp : pushStep c = some n) : AllN P n := by
  unfold pushStep at hp
  split at hp
  · rename_i hcond
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
    have hhead : c.ch.head! ∈ c.ch := by
      obtain ⟨x, xs, hc⟩ : ∃ x xs, c.ch = x :: xs := by
        cases hc : c.ch with
        | nil => rw [hc] at hcond; simp at hcond
        | cons x xs => exact ⟨x, xs, rfl⟩
      rw [hc]; exact List.mem_cons.2 (Or.inl rfl)
    have hH := AllN.ch P h _ hhead
    have hall : ∀ (f : Cond → Nat), ∀ y ∈ c.ch.map (fun o => o.ch[f o]!), AllN P y := by
      intro f y hy
      obtain ⟨o, ho, rfl⟩ := List.mem_map.1 hy
      exact allN_get! P hloc hPass hP0 (AllN.ch P h o ho) _
    split at hp
    · obtain ⟨nch, hm, rfl⟩ := Option.map_eq_some_iff.1 hp
      unfold mergeMatches at hm
      repeat (split at hm; · simp at hm)
      simp only [Option.some.injEq] at hm; subst hm
      refine AllN.withCh P hloc (AllN.self P hH) fun y hy => ?_
      rcases mem_replaceAt hy with hy | rfl
      · exact AllN.ch P hH y hy
      · exact allN_orNode P hloc hOr fun y hy => by
          obtain ⟨o, ho, rfl⟩ := List.mem_map.1 hy
          exact allN_get! P hloc hPass hP0 (AllN.ch P h o ho) _
    · split at hp
      · obtain ⟨nch, hm, rfl⟩ := Option.map_eq_some_iff.1 hp
        unfold mergeAnd at hm
        repeat (split at hm; · simp at hm)
        simp only [Option.some.injEq] at hm; subst hm
        refine AllN.withCh P hloc (AllN.self P hH) fun y hy => ?_
        rcases mem_replaceAt hy with hy | rfl
        · exact AllN.ch P hH y hy
        · exact allN_orNode P hloc hOr (hall (hingeOf c.ch))
      · simp at hp
  · simp at hp

include hloc hOr hPass in
theorem allN_normalize (hP0 : AllN P (default : Cond)) :
    ∀ (k : Nat) (c : Cond), AllN P c → AllN P (normalize k c)
  | 0, _, h => h
  | k + 1, c, h => by
    rw [normalize]
    split
    · exact h
    dsimp only
    have IH := allN_normalize hP0 k
    have h1 : AllN P { c with ch := c.ch.map (normalize k) } :=
      AllN.withCh P hloc (AllN.self P h) fun y hy => by
        obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy; exact IH x (AllN.ch P h x hx)
    have hpr : ∀ x, AllN P x → AllN P (prune x) := fun x hx => by
      unfold prune; split
      · exact AllN.withCh P hloc (AllN.self P hx) fun y hy => AllN.ch P hx y (mem_pruneCh hy)
      · exact hx
    have hfl : ∀ x, AllN P x → AllN P (flatten x) := fun x hx => by
      unfold flatten; split
      · refine AllN.withCh P hloc (AllN.self P hx) fun y hy => ?_
        unfold flattenCh at hy
        obtain ⟨z, hz, hyz⟩ := List.mem_flatMap.1 hy
        split at hyz
        · exact AllN.ch P (AllN.ch P hx z hz) y hyz
        · simp at hyz; subst hyz; exact AllN.ch P hx _ hz
      · exact hx
    have hde : ∀ x, AllN P x → AllN P (dedupe x) := fun x hx => by
      unfold dedupe; split
      · exact AllN.withCh P hloc (AllN.self P hx) fun y hy => AllN.ch P hx y (mem_dedupeL hy)
      · exact hx
    have hun : ∀ x, AllN P x → AllN P (unwrap x) := fun x hx => by
      unfold unwrap; split
      · split
        · rename_i z hz; exact AllN.ch P hx z (by rw [hz]; simp)
        · exact hx
      · exact hx
    have hpu : ∀ x, AllN P x → AllN P (pushDownOr (normalize k) x) := fun x hx => by
      unfold pushDownOr; split
      · rename_i n hn; exact IH n (allN_pushStep P hloc hOr hPass hP0 hx hn)
      · exact hx
    have hso : ∀ x, AllN P x → AllN P (sortB x) := fun x hx => by
      unfold sortB; split
      · exact AllN.withCh P hloc (AllN.self P hx) fun y hy =>
          AllN.ch P hx y ((sortCh_perm x.ch).mem_iff.1 hy)
      · exact hx
    exact hso _ (hpu _ (hun _ (hde _ (hfl _ (hpr _ h1)))))

end
end Bridge
