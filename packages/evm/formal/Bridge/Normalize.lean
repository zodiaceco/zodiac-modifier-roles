import Bridge.Main

/-!
# Normalization keeps the contract's verdict

The contract's evaluation of a tree and of its normalized form agree when both
fit the layout of the calldata (`normalize_calldata`): adequacy for each, and
`normalize_sound` for the contract world (whose assumptions are
`contractWorld_ok`).
-/

namespace Bridge
open DecoderFaithfulness DecoderFaithfulness.Roles Normalize Evaluate

/-- Two contract results agree: same slots, both pass with the same
    consumptions (as maps) or both fail, neither reverts. -/
def Agree (r r' : Res) : Prop :=
  r.slots = r'.slots ∧ (r.status = sOk ↔ r'.status = sOk) ∧
    (r.status = sOk → toMap r.cons = toMap r'.cons) ∧ r.status ≠ revert ∧ r'.status ≠ revert

theorem Rel.agree {r r' : Res} {x : Option CM × Slots} (h : Rel r x) (h' : Rel r' x) : Agree r r' := by
  have e := h.eq
  have e' := h'.eq
  rw [e] at e'
  simp only [Prod.mk.injEq] at e'
  obtain ⟨e1, e2⟩ := e'
  refine ⟨e2, ?_, ?_, h.status_ne, h'.status_ne⟩
  · by_cases hs : r.status = sOk <;> by_cases hs' : r'.status = sOk <;> simp_all
  · intro hs
    have hs' : r'.status = sOk := by
      by_cases hs' : r'.status = sOk
      · exact hs'
      · simp [hs, hs'] at e1
    simp only [hs, hs', ite_true, Option.some.injEq] at e1
    exact e1

section
variable (avatar : Bytes) (env : Env) (henv : EnvOk env) (data : Calldata) (n : Nat)

include henv in
/-- **Normalization keeps the contract's verdict** on every calldata that
    decodes as the layout both trees fit. -/
theorem normalize_calldata (k : Nat) {c : Cond} {m : Condition}
    (hc : Fits avatar c (D avatar c) m) (hc' : Fits avatar (normalize k c) (D avatar (normalize k c)) m)
    (hcv : CvOk n c) (hcv' : CvOk n (normalize k c)) (l : Nat) (hdec : Decodable data m l)
    (fuel fuel' : Nat) (hf : height c < fuel) (hf' : height (normalize k c) < fuel')
    (cons : List Consumption) (sl : Slots) :
    Agree (evalC env data n fuel l (D avatar c) cons sl)
      (evalC env data n fuel' l (D avatar (normalize k c)) cons sl) := by
  have h1 := adequacy avatar env henv data n hc fuel l cons sl hf hcv hdec
  have h2 := adequacy avatar env henv data n hc' fuel' l cons sl hf' hcv' hdec
  rw [normalize_sound (contractWorld_ok avatar env data n) k c] at h2
  exact h1.agree h2

end
end Bridge
