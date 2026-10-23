import Bridge.Lemmas

/-!
# Correspondence of results and loops

`Rel r x`: the contract's result `r` and the world's `x` agree. The loops of
`evaluate` (`_and`/`_matches`, `_or`, the array iterators) relate to
`seqT`/`orT` child by child (`Corr`).
-/

namespace Bridge
open DecoderFaithfulness DecoderFaithfulness.Roles Normalize Evaluate

/-- What is assumed of the outside: the external calls never report `Ok`
    as a failure, nor a status that reads as a revert. -/
structure EnvOk (env : Env) : Prop where
  scale : ∀ cv n, (env.scale cv n).1 ≠ revert
  custom : ∀ cv l sz vals s, env.customCall cv l sz vals = .inl s → s ≠ sOk ∧ s ≠ revert
  ratio : ∀ cv vals, env.ratio cv vals ≠ revert

theorem sOk_ne_revert : sOk ≠ revert := by decide

theorem Rel.ok (cons : List Consumption) (sl : Slots) :
    Rel (Evaluate.ok cons sl) (some (toMap cons), sl) := by
  refine ⟨rfl, ?_⟩
  simp [Evaluate.ok]

theorem Rel.violation {s : Nat} (h1 : s ≠ sOk) (h2 : s ≠ revert) (sl : Slots) :
    Rel (violation s sl) (none, sl) := by
  simp [Rel, Evaluate.violation, h1, h2]

theorem Rel.result {s : Nat} (h : s ≠ revert) (cons : List Consumption) (sl : Slots) :
    Rel (result s cons sl) (if s = sOk then some (toMap cons) else none, sl) := by
  unfold Evaluate.result
  by_cases hs : s = sOk
  · simp only [hs, ite_true]; exact Rel.ok cons sl
  · simp only [hs, ite_false]; exact Rel.violation hs h sl

theorem Rel.status_ne {r : Res} {x : Option CM × Slots} (h : Rel r x) : r.status ≠ revert := by
  obtain ⟨-, h2⟩ := h
  split at h2
  · rename_i hs; rw [hs]; exact sOk_ne_revert
  · exact h2.1

/-- A result that passes or fails like `x`, as a world result. -/
theorem Rel.eq {r : Res} {x : Option CM × Slots} (h : Rel r x) :
    x = (if r.status = sOk then some (toMap r.cons) else none, r.slots) := by
  obtain ⟨h1, h2⟩ := h
  rcases x with ⟨x1, x2⟩
  simp only at h1 h2
  subst h1
  split at h2
  · rename_i hs; simp [hs, h2]
  · rename_i hs; simp [hs, h2.2]

section
variable (env : Env) (data : Calldata)

/-- Child by child: each contract run corresponds to the world thunk (with
    `n` slots). -/
inductive Corr (n fuel : Nat) : List (Condition × Nat) → List T → Prop
  | nil : Corr n fuel [] []
  | cons {p : Condition × Nat} {t : T} {ps ts} :
      (∀ cons sl, Rel (evalC env data n fuel p.2 p.1 cons sl) (t sl (toMap cons))) →
      Corr n fuel ps ts → Corr n fuel (p :: ps) (t :: ts)

theorem seqLoop_rel {n fuel : Nat} : ∀ (ps : List (Condition × Nat)) (ts : List T),
    Corr env data n fuel ps ts → ∀ cons sl,
    Rel (seqLoop env data n fuel ps cons sl) (seqT ts sl (toMap cons))
  | [], [], _, cons, sl => by rw [seqLoop]; exact Rel.ok cons sl
  | [], _ :: _, h, _, _ => by cases h
  | _ :: _, [], h, _, _ => by cases h
  | (d, l) :: ps, t :: ts, h, cons, sl => by
    cases h with
    | cons hp hrest =>
      rw [seqLoop, seqT_cons]
      have h1 := hp cons sl
      have hne := h1.status_ne
      rw [h1.eq]
      by_cases hs : (evalC env data n fuel l d cons sl).status = sOk
      · simp only [hs, ite_true, ne_eq, not_true_eq_false, ite_false, bindR_some]
        exact seqLoop_rel ps ts hrest _ _
      · simp only [hs, ite_false, ne_eq, not_false_eq_true, ite_true, bindR_none]
        simp only [Rel, if_neg hs]
        simp [hne]

theorem orLoop_rel {n fuel : Nat} (loc : Nat) : ∀ {cs : List Condition} {ts},
    Corr env data n fuel (cs.map (·, loc)) ts → ∀ cons sl,
    Rel (orLoop env data n fuel cs loc cons sl) (orT ts sl (toMap cons))
  | [], [], _, cons, sl => by
    rw [orLoop]; exact Rel.violation (by decide) (by decide) sl
  | [], _ :: _, h, _, _ => by cases h
  | c :: cs, ts, h, cons, sl => by
    cases h with
    | cons hp hrest =>
      rename_i t ts'
      rw [orLoop]
      simp only [orT]
      have h1 := hp cons sl
      have hne := h1.status_ne
      rw [h1.eq]
      by_cases hs : (evalC env data n fuel loc c cons sl).status = sOk
      · simp only [hs, true_or, ite_true]
        simp [Rel, hs]
      · simp only [hs, false_or, hne, ite_false]
        exact orLoop_rel loc hrest _ _

theorem everyLoop_rel {n fuel : Nat} (c : Condition) : ∀ {locs : List Nat} {ts},
    Corr env data n fuel (locs.map (c, ·)) ts → ∀ cons sl,
    Rel (everyLoop env data n fuel c locs cons sl) (seqT ts sl (toMap cons))
  | [], [], _, cons, sl => by rw [everyLoop]; exact Rel.ok cons sl
  | [], _ :: _, h, _, _ => by cases h
  | l :: locs, ts, h, cons, sl => by
    cases h with
    | cons hp hrest =>
      rw [everyLoop, seqT_cons]
      have h1 := hp cons sl
      have hne := h1.status_ne
      rw [h1.eq]
      by_cases hs : (evalC env data n fuel l c cons sl).status = sOk
      · simp only [hs, ite_true, ne_eq, not_true_eq_false, ite_false, bindR_some, hne]
        exact everyLoop_rel c hrest _ _
      · simp only [hs, ite_false, hne, ne_eq, not_false_eq_true, ite_true, bindR_none]
        simp [Rel, sNotEveryArrayElementPasses, sOk, revert]

theorem someLoop_rel {n fuel : Nat} (c : Condition) : ∀ {locs : List Nat} {ts},
    Corr env data n fuel (locs.map (c, ·)) ts → ∀ cons sl,
    Rel (someLoop env data n fuel c locs cons sl) (orT ts sl (toMap cons))
  | [], [], _, cons, sl => by
    rw [someLoop]; exact Rel.violation (by decide) (by decide) sl
  | [], _ :: _, h, _, _ => by cases h
  | l :: locs, ts, h, cons, sl => by
    cases h with
    | cons hp hrest =>
      rw [someLoop]
      simp only [orT]
      have h1 := hp cons sl
      have hne := h1.status_ne
      rw [h1.eq]
      by_cases hs : (evalC env data n fuel l c cons sl).status = sOk
      · simp only [hs, true_or, ite_true]
        simp [Rel, hs]
      · simp only [hs, false_or, hne, ite_false]
        exact someLoop_rel c hrest _ _

end
end Bridge
