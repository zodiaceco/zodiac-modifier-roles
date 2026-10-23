import Bridge.CvOkPres

/-!
# Normalization keeps the contract's verdict, on calldata

`normalize_calldata'`: for every tree that fits the layout of the calldata
(`Fits`), with compValues the evaluator does not revert on (`CvOk`), the
contract's evaluation of the normalized tree agrees with its evaluation of
the tree as written, on every calldata that decodes as that layout: same
verdict, same allowance consumptions, same Pluck slots.
-/

namespace Bridge
open DecoderFaithfulness DecoderFaithfulness.Roles Normalize Evaluate

/-- `CvOk` of one node. -/
def cvOk1 (n : Nat) (c : Cond) : Prop :=
  (c.op = 5 → (prefixOf c.enc c.cv).length ≤ 32) ∧ (c.op = 13 → 3 ≤ c.cv.length) ∧
    (c.op = 14 → ∃ k ∈ c.cv.head?, k % 256 < n)

theorem cvOk_iff (n : Nat) (c : Cond) : CvOk n c ↔ AllN (cvOk1 n) c := by
  rw [cvOk_eq]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    exact .mk ⟨h1, h2, h3⟩ fun x hx => (cvOk_iff n x).1 (h4 x hx)
  · intro h
    obtain ⟨h1, h2, h3⟩ := AllN.self _ h
    exact ⟨h1, h2, h3, fun x hx => (cvOk_iff n x).2 (AllN.ch _ h x hx)⟩
termination_by sizeOf c
decreasing_by all_goals exact sizeOf_lt_of_mem hx

theorem cvOk1_triv (n e o : Nat) (h5 : o ≠ 5) (h13 : o ≠ 13) (h14 : o ≠ 14) :
    cvOk1 n ⟨e, o, [], []⟩ :=
  ⟨fun h => absurd h h5, fun h => absurd h h13, fun h => absurd h h14⟩

theorem cvOk_normalize (n k : Nat) (c : Cond) (h : CvOk n c) : CvOk n (normalize k c) := by
  rw [cvOk_iff] at h ⊢
  apply allN_normalize (cvOk1 n) (fun _ _ => Iff.rfl) (cvOk1_triv n 0 2 (by decide) (by decide) (by decide))
    (fun e => cvOk1_triv n e 0 (by decide) (by decide) (by decide)) ?_ k c h
  exact .mk (cvOk1_triv n 0 0 (by decide) (by decide) (by decide)) (fun x hx => nomatch hx)

section
variable (avatar : Bytes) (env : Env) (henv : EnvOk env) (data : Calldata) (n : Nat)

include henv in
/-- **Normalization keeps the contract's verdict.** For a tree `c` that fits
    the calldata layout `m` and has well-formed compValues, on every calldata
    that decodes as `m`, the contract's evaluation of `normalize k c` agrees
    with its evaluation of `c`: both pass with the same consumptions, or both
    fail; and they leave the same Pluck slots. -/
theorem normalize_calldata' (k : Nat) {c : Cond} {m : Condition}
    (hc : Fits avatar c (D avatar c) m) (hcv : CvOk n c) (l : Nat) (hdec : Decodable data m l)
    (fuel fuel' : Nat) (hf : height c < fuel) (hf' : height (normalize k c) < fuel')
    (cons : List Consumption) (sl : Slots) :
    Agree (evalC env data n fuel l (D avatar c) cons sl)
      (evalC env data n fuel' l (D avatar (normalize k c)) cons sl) :=
  normalize_calldata avatar env henv data n k hc (normalize_fits avatar k c m hc) hcv
    (cvOk_normalize n k c hcv) l hdec fuel fuel' hf hf' cons sl

end
end Bridge
