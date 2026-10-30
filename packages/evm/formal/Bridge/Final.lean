import Bridge.ReadNorm

/-!
# Normalization keeps the contract's verdict, on calldata

For every well-typed tree `c` (`inv`, which the SDK check is tested to
imply) and
every calldata, the contract's evaluation of `normalize k c` computes the
contract's own reading of `c` (`normalize_meaning`): whenever it does not
revert, it passes exactly when that reading passes, with the same allowance
consumptions and Pluck slots. Evaluating `c` as written gives the same
(`normalize_calldata`), whenever neither reverts. A revert denies the call,
so the stored tree never allows more than the tree as written means.

Nothing is assumed of the calldata or of how the tree relates to an ABI
type: the reading is the contract's (`readWorld`), and normalization keeps
the layout of every node (`norm_inv`).
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

theorem AllN.imp {P Q : Cond → Prop} (h : ∀ c, P c → Q c) : ∀ {c : Cond}, AllN P c → AllN Q c
  | _, .mk hp hch => .mk (h _ hp) fun x hx => AllN.imp h (hch x hx)

section
variable (avatar : Bytes) (env : Env) (henv : EnvOk env) (data : Calldata) (n : Nat)

include henv in
/-- The contract's evaluation of a well-typed tree computes its reading. -/
theorem eval_reading {c : Cond} (hc : inv avatar c) (l fuel : Nat) (hf : height c < fuel)
    (cons : List Consumption) (sl : Slots)
    (hne : (evalC env data n fuel l (D avatar c) cons sl).status ≠ revert) :
    Rel (evalC env data n fuel l (D avatar c) cons sl)
      (sem (readWorld avatar env data n) c (.pos l) sl (toMap cons)) :=
  adequacy_gen avatar env henv data n fuel c (.pos l) hf (AllN.imp (fun _ h => h.1) hc)
    (fun _ _ h => by cases h) (fun _ h => by cases h) cons sl hne

include henv in
/-- **The normalized tree computes the meaning of the tree as written.**
    For a well-typed tree `c`, on every calldata, whenever the contract's
    evaluation of `normalize k c` does not revert, it passes exactly when the
    contract's reading of `c` does, with the same consumptions and slots. -/
theorem normalize_meaning (k : Nat) {c : Cond} (hc : inv avatar c) (l fuel : Nat)
    (hf : height (normalize k c) < fuel) (cons : List Consumption) (sl : Slots)
    (hne : (evalC env data n fuel l (D avatar (normalize k c)) cons sl).status ≠ revert) :
    Rel (evalC env data n fuel l (D avatar (normalize k c)) cons sl)
      (sem (readWorld avatar env data n) c (.pos l) sl (toMap cons)) := by
  have h := eval_reading avatar env henv data n (norm_inv avatar k c hc).1 l fuel hf cons sl hne
  rwa [normalize_sound (readWorld_ok avatar env data n) (readWorld_normOk avatar env data n) k c hc] at h

include henv in
/-- **Normalization keeps the contract's verdict.** For a well-typed tree
    `c`, on every calldata, the contract's evaluations of `c` and of
    `normalize k c` agree whenever neither reverts: both pass with the same
    consumptions, or both fail; and they leave the same Pluck slots. -/
theorem normalize_calldata (k : Nat) {c : Cond} (hc : inv avatar c) (l fuel fuel' : Nat)
    (hf : height c < fuel) (hf' : height (normalize k c) < fuel') (cons : List Consumption) (sl : Slots)
    (hne : (evalC env data n fuel l (D avatar c) cons sl).status ≠ revert)
    (hne' : (evalC env data n fuel' l (D avatar (normalize k c)) cons sl).status ≠ revert) :
    Agree (evalC env data n fuel l (D avatar c) cons sl)
      (evalC env data n fuel' l (D avatar (normalize k c)) cons sl) :=
  (eval_reading avatar env henv data n hc l fuel hf cons sl hne).agree
    (normalize_meaning avatar env henv data n k hc l fuel' hf' cons sl hne')

end
end Bridge
