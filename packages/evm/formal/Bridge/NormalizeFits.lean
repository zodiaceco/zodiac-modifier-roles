import Bridge.Preserve

/-!
# Normalization keeps a tree fitting its layout

`normalize_fits`: every step of `normalize` (pruning, flattening, dedupe,
unwrap, pushing an `Or` down, sorting) keeps a tree that fits layout `m`
fitting `m`. The `PDesc` lemmas are about `Pass` type descriptions.
-/

namespace Bridge
open DecoderFaithfulness DecoderFaithfulness.Roles Normalize Evaluate

section
variable (avatar : Bytes) (P : Nat → Option Condition)

local notation "F" => fun (c : Cond) (m : Condition) => Fits avatar P c (D avatar c) m

/-- The layout metadata depend on the encoding and the children only. -/
theorem raw_same {c c' : Cond} (he : c.enc = c'.enc) (hc : c.ch = c'.ch) :
    isInl c = isInl c' ∧ rawSz avatar c = rawSz avatar c' := by
  constructor
  · rw [isInl_eq, isInl_eq, he, hc]
  · rw [rawSz_eq, rawSz_eq, he, hc]

theorem D_meta_same {c c' : Cond} (he : c.enc = c'.enc) (hc : c.ch = c'.ch) :
    (D avatar c).inlined = (D avatar c').inlined ∧ (D avatar c).size = (D avatar c').size := by
  have := raw_same avatar he hc
  rw [D_inlined, D_inlined, D_size, D_size, this.1, this.2]; exact ⟨rfl, rfl⟩

theorem isStruct_pass {c : Cond} (h0 : c.op = 0) (he : c.enc = 1 ∨ c.enc = 2 ∨ c.enc = 3 ∨ c.enc = 4 ∨ c.enc = 5) :
    isStruct c = true := by
  rw [isStruct_eq, h0]; simp; omega

theorem PDesc.op {c : Cond} {m : Condition} (h : PDesc avatar c m) : c.op = 0 := by
  cases h <;> assumption

theorem PDesc.enc {c : Cond} {m : Condition} (h : PDesc avatar c m) :
    c.enc = 1 ∨ c.enc = 2 ∨ c.enc = 3 ∨ c.enc = 4 ∨ c.enc = 5 := by
  cases h with
  | leaf _ he => omega
  | tup _ he => omega
  | arr _ he => omega

theorem PDesc.lay_sane {c : Cond} {m : Condition} (h : PDesc avatar c m) :
    LayEq (D avatar c) m ∧ isInl c = (D avatar c).inlined := by
  cases h with
  | leaf _ _ _ hl hs => exact ⟨hl, hs⟩
  | tup _ _ _ _ _ hl hs => exact ⟨hl, hs⟩
  | arr _ _ _ _ _ hl hs => exact ⟨hl, hs⟩

theorem PDesc.plain : ∀ {c : Cond} {m : Condition}, PDesc avatar c m → Plain c := by
  intro c m h
  induction h with
  | leaf h0 he hch =>
    exact .mk (by omega) (by omega) (by omega) (by omega) (by rw [hch]; simp)
  | tup h0 he _ _ _ _ _ ih =>
    refine .mk (by omega) (by omega) (by omega) (by omega) ?_
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    exact ih i hi
  | arr h0 he hch _ _ _ _ ih =>
    refine .mk (by omega) (by omega) (by omega) (by rw [hch]; simp) ?_
    intro x hx; rw [hch] at hx; simp at hx; subst hx; exact ih

theorem PDesc.fits {c : Cond} {m : Condition} (h : PDesc avatar c m) : F c m := by
  have hl := h.lay_sane avatar
  exact .pass (h.op avatar) (Node.refl avatar c) (isStruct_pass (h.op avatar) (h.enc avatar)) hl.1
    (h.plain avatar) hl.2 (fun _ => h)

theorem PDesc.raw {c : Cond} {m : Condition} (h : PDesc avatar c m) :
    isInl c = m.inlined ∧ (isInl c = true → rawSz avatar c = m.size) ∧
      (m.inlined = true → 0 < m.size) ∧ (m.inlined = false → m.size = 0) :=
  (h.fits avatar fun _ => none).raw avatar (fun _ => none) (isStruct_pass (h.op avatar) (h.enc avatar))

theorem D_encoding_same {c c' : Cond} (he : c.enc = c'.enc) : (D avatar c).encoding = (D avatar c').encoding := by
  rw [D_encoding, D_encoding, he]

theorem tmpl_eq (m : Condition) : tmpl m = m.children.getD 0 default := by
  unfold tmpl; cases m.children <;> rfl

theorem TyEq.children_length {c : Cond} {m : Condition} (h : TyEq (D avatar c) m) :
    c.ch.length = m.children.length := by
  cases h with
  | mk _ _ hl => have := hl.length; rw [D_children] at this; simpa using this

/-! ## Extending -/

theorem any_congr_mem {α} {f g : α → Bool} : ∀ {l : List α}, (∀ x ∈ l, f x = g x) → l.any f = l.any g
  | [], _ => rfl
  | x :: xs, h => by
    have ih : xs.any f = xs.any g := any_congr_mem (l := xs) (fun y hy => h y (List.mem_cons_of_mem _ hy))
    simp only [List.any_cons, h x (by simp), ih]

theorem TyEqL.get : ∀ {as bs : List Condition}, TyEqL as bs →
    ∀ i (h1 : i < as.length) (h2 : i < bs.length), TyEq as[i] bs[i]
  | _, _, .nil, _, h1, _ => by simp at h1
  | _, _, .cons h _, 0, _, _ => h
  | _, _, .cons _ hs, i + 1, h1, h2 => TyEqL.get hs i (by simpa using h1) (by simpa using h2)

theorem TyEq.child {c : Cond} {m : Condition} (h : TyEq (D avatar c) m) (i : Nat) (h1 : i < c.ch.length) :
    TyEq (D avatar c.ch[i]) (m.children.getD i default) := by
  have hl := TyEq.children_length avatar h
  cases h with
  | mk _ _ hcs =>
    have hcs' : TyEqL (c.ch.map (D avatar)) m.children := by rw [← D_children]; exact hcs
    have := hcs'.get i (by simpa using h1) (by omega)
    simp only [List.getElem_map] at this
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
    exact this

/-- A tuple that is not inlined stays so when its children keep their
    `isInl` at the positions it had. -/
theorem notInl_of_child {c c' : Cond} (he : c.enc = c'.enc) (hl : c.ch.length ≤ c'.ch.length)
    (hc : isInl c = false)
    (hk : ∀ k (h1 : k < c.ch.length) (h2 : k < c'.ch.length), isInl c'.ch[k] = isInl c.ch[k]) :
    isInl c' = false := by
  rw [isInl_eq] at hc ⊢
  rw [← he]
  cases hd : (c.enc == 2 || c.enc == 4 || c.enc == 5)
  · rw [hd] at hc
    simp only [Bool.not_false, Bool.true_and] at hc ⊢
    rw [List.all_eq_false] at hc ⊢
    obtain ⟨x, hx, hxi⟩ := hc
    obtain ⟨k, hk1, rfl⟩ := List.getElem_of_mem hx
    exact ⟨c'.ch[k]'(by omega), List.getElem_mem _, by rw [hk k hk1 (by omega)]; exact hxi⟩
  · simp

/-! ## The padding loop -/

theorem getElem!_mem {l : List Cond} {i : Nat} (h : i < l.length) : l[i]! ∈ l := by
  rw [getElem!_eq h]; exact List.getElem_mem h

/-! ## Normalization -/

/-- **Normalization keeps a tree fitting its layout.** -/
theorem normalize_fits : ∀ (k : Nat) (c : Cond) (m : Condition), F c m → F (normalize k c) m
  | 0, _, _, h => h
  | k + 1, c, m, h => by
    rw [normalize]
    split
    · exact h
    rename_i hkw
    dsimp only
    have IH : ∀ x m', F x m' → F (normalize k x) m' := fun x m' => normalize_fits k x m'
    exact sortB_fits avatar P (pushDownOr_fits avatar P _ (fun n hn => IH n m hn)
      (unwrap_fits avatar P (dedupe_fits avatar P (flatten_fits avatar P
        (prune_fits avatar P (fits_children avatar P k IH h (by simpa using hkw)))))))

end
end Bridge
