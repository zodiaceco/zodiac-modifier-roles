import Bridge.Preserve

/-!
# Normalization keeps a tree fitting its layout

`normalize_fits`: every step of `normalize` (pruning, flattening, dedupe,
unwrap, pushing an `Or` down, sorting) keeps a tree that fits layout `m`
fitting `m`.
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

theorem D_encoding_same {c c' : Cond} (he : c.enc = c'.enc) : (D avatar c).encoding = (D avatar c').encoding := by
  rw [D_encoding, D_encoding, he]

theorem tmpl_eq (m : Condition) : tmpl m = m.children.getD 0 default := by
  unfold tmpl; cases m.children <;> rfl

/-! ## Extending -/

theorem any_congr_mem {α} {f g : α → Bool} : ∀ {l : List α}, (∀ x ∈ l, f x = g x) → l.any f = l.any g
  | [], _ => rfl
  | x :: xs, h => by
    have ih : xs.any f = xs.any g := any_congr_mem (l := xs) (fun y hy => h y (List.mem_cons_of_mem _ hy))
    simp only [List.any_cons, h x (by simp), ih]

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
