import Bridge.Fits
import DecoderFaithfulness.Decode

/-!
# Lemmas for adequacy

`AbiLocation` reads a child only through its `inlined` and `size`, so two
layouts that agree on those decode the same locations (`childrenLoop_congr`),
and decoding the first `k` children gives the first `k` locations
(`childrenLoop_prefix`). `size` and `__input` read the whole type
(`size_tyEq`, `input_tyEq`). The contract's consumption list and the
world's map stay in step (`consume_toMap`, `applyCharges_toMap`).
-/

namespace Bridge
open DecoderFaithfulness DecoderFaithfulness.Roles Normalize Evaluate

/-! ## Decoding -/

theorem childrenLoop_congr (data : Calldata) (loc : Nat) (f g : Nat → Condition) :
    ∀ (n i h : Nat), (∀ j, i ≤ j → j < i + n → LayEq (f j) (g j)) →
      childrenLoop data loc f n i h = childrenLoop data loc g n i h
  | 0, _, _, _ => rfl
  | n + 1, i, h, hfg => by
    have ⟨hin, hsz⟩ := hfg i (Nat.le_refl _) (by omega)
    simp only [childrenLoop, hin, hsz]
    rw [childrenLoop_congr data loc f g n (i + 1) _ (fun j h1 h2 => hfg j (by omega) (by omega))]

theorem childrenLoop_prefix (data : Calldata) (loc : Nat) (f : Nat → Condition) :
    ∀ (k K i h : Nat) (locs : List Nat), k ≤ K → childrenLoop data loc f K i h = some locs →
      childrenLoop data loc f k i h = some (locs.take k)
  | 0, _, _, _, _, _, _ => by simp [childrenLoop]
  | k + 1, 0, _, _, _, hk, _ => absurd hk (by omega)
  | k + 1, K + 1, i, h, locs, hk, hK => by
    simp only [childrenLoop] at hK ⊢
    cases hfi : (f i).inlined <;> simp only [hfi, Bool.false_eq_true, ite_false, ite_true] at hK ⊢ <;>
    · split at hK
      · exact absurd hK (by simp)
      · rename_i hr
        rw [if_neg hr]
        obtain ⟨rest, hrest, rfl⟩ := Option.map_eq_some_iff.1 hK
        rw [childrenLoop_prefix data loc f k K _ _ rest (by omega) hrest]
        simp

/-! ## `size` and `__input` read the type -/

theorem LayEq.refl (d : Condition) : LayEq d d := ⟨rfl, rfl⟩

theorem TyEq.layEq {d m : Condition} (h : TyEq d m) : LayEq d m := by cases h; assumption
theorem TyEq.encoding {d m : Condition} (h : TyEq d m) : d.encoding = m.encoding := by
  cases h; assumption

theorem TyEqL.length : ∀ {as bs : List Condition}, TyEqL as bs → as.length = bs.length
  | _, _, .nil => rfl
  | _, _, .cons _ h => by simp [TyEqL.length h]

theorem TyEqL.headD {as bs : List Condition} (h : TyEqL as bs) :
    TyEq (as.headD default) (bs.headD default) ∨ (as = [] ∧ bs = []) := by
  cases h with
  | nil => exact Or.inr ⟨rfl, rfl⟩
  | cons h1 _ => exact Or.inl h1

theorem sizeArrayLoop_congr (data : Calldata) (loc : Nat) (a b : Condition) (fa fb : Nat → Nat)
    (hab : LayEq a b) (hf : ∀ l, fa l = fb l) :
    ∀ n h, sizeArrayLoop data loc a fa n h = sizeArrayLoop data loc b fb n h
  | 0, _ => rfl
  | n + 1, h => by
    simp only [sizeArrayLoop, hab.1, hab.2, hf]
    rw [sizeArrayLoop_congr data loc a b fa fb hab hf n]
    rw [sizeArrayLoop_congr data loc a b fa fb hab hf n]

mutual
  theorem size_tyEq (data : Calldata) : ∀ {d m : Condition}, TyEq d m → ∀ l, size data l d = size data l m
    | ⟨de, dop, dcs, di, ds, dlb, dcv⟩, ⟨me, mop, mcs, mi, ms, mlb, mcv⟩, .mk he hl hcs, l => by
      simp only at he hl hcs
      subst he
      rw [size_eq, size_eq]
      simp only
      split
      · rfl
      split
      · rfl
      rename_i hS
      split
      · rfl
      rename_i hD
      have hcs := hcs hS (fun h => hD (.inl h)) (fun h => hD (.inr h))
      split
      · exact sizeNone_tyEq data hcs l
      split
      · cases hcs with
        | nil => rfl
        | cons h0 hrest =>
          simp only
          rw [sizeArrayLoop_congr data (l + 32) _ _ _ _ h0.layEq (fun l' => size_tyEq data h0 l')]
      · exact sizeTuple_tyEq data hcs l 0

  theorem sizeNone_tyEq (data : Calldata) : ∀ {as bs : List Condition}, TyEqL as bs →
      ∀ l, sizeNone data l as = sizeNone data l bs
    | _, _, .nil, _ => rfl
    | _, _, .cons h1 h2, l => by
      simp only [sizeNone]
      rw [size_tyEq data h1 l, sizeNone_tyEq data h2 l]

  theorem sizeTuple_tyEq (data : Calldata) : ∀ {as bs : List Condition}, TyEqL as bs →
      ∀ l h, sizeTuple data l as h = sizeTuple data l bs h
    | _, _, .nil, _, _ => rfl
    | _, _, .cons h1 h2, l, h => by
      simp only [sizeTuple, h1.layEq.1, h1.layEq.2]
      rw [size_tyEq data h1, sizeTuple_tyEq data h2, sizeTuple_tyEq data h2]
end

theorem input_tyEq (data : Calldata) {d m : Condition} (h : TyEq d m) (l : Nat) :
    input data l d = input data l m := by
  unfold input
  rw [h.encoding, h.layEq.2, size_tyEq data h l]

/-! ## Consumptions -/

theorem toMap_nil : toMap [] = fun _ => none := rfl

theorem toMap_cons (e : Consumption) (es : List Consumption) (k : Bytes) :
    toMap (e :: es) k = if e.key = k then some (e.balance, e.consumed) else toMap es k := by
  unfold toMap
  by_cases h : e.key = k <;> simp [List.find?, h]

theorem consume_keeps (env : Env) : ∀ (cons : List Consumption) (k : Bytes) (a : Nat),
    (Evaluate.consume env cons k a).1 ≠ sOk → (Evaluate.consume env cons k a).2 = cons ∧
      (Evaluate.consume env cons k a).1 = sAllowanceExceeded
  | [], k, a, h => by
    unfold Evaluate.consume at h ⊢
    by_cases ha : a > env.balance k <;> simp_all [sOk, sAllowanceExceeded]
  | e :: es, k, a, h => by
    unfold Evaluate.consume at h ⊢
    by_cases hk : e.key = k
    · by_cases ha : a > e.balance - e.consumed <;> simp_all [sOk, sAllowanceExceeded]
    · simp only [hk, if_false] at h ⊢
      have := consume_keeps env es k a h
      exact ⟨by rw [this.1], this.2⟩

/-- The contract's `consume` and the map's agree. -/
theorem consume_toMap (env : Env) : ∀ (cons : List Consumption) (k : Bytes) (a : Nat),
    consumeM env.balance (toMap cons) (k, a) =
      if (Evaluate.consume env cons k a).1 = sOk then some (toMap (Evaluate.consume env cons k a).2) else none
  | [], k, a => by
    unfold Evaluate.consume consumeM ent
    simp only [toMap_nil, Option.getD_none]
    by_cases ha : a > env.balance k
    · simp [ha, sOk, sAllowanceExceeded]
    · simp only [ha, if_false, ite_true, Nat.sub_zero, Nat.zero_add]
      congr 1
      funext k'
      rw [toMap_cons, toMap_nil]
      by_cases hk : k = k' <;> simp [CM.set, hk, eq_comm]
  | e :: es, k, a => by
    by_cases hk : e.key = k
    · unfold Evaluate.consume consumeM ent
      simp only [toMap_cons, hk, if_true, Option.getD_some]
      by_cases ha : a > e.balance - e.consumed
      · simp [ha, sOk, sAllowanceExceeded]
      · simp only [ha, if_false, ite_true]
        congr 1
        funext k'
        rw [toMap_cons]
        by_cases hk' : k' = k
        · subst hk'; simp [CM.set]
        · simp [CM.set, hk', hk, toMap_cons, Ne.symm hk']
    · have ih := consume_toMap env es k a
      have hent : ent env.balance (toMap (e :: es)) k = ent env.balance (toMap es) k := by
        simp [ent, toMap_cons, hk]
      unfold consumeM at ih ⊢
      rw [hent]
      unfold Evaluate.consume
      simp only [hk, if_false]
      split at ih
      · rename_i hgt
        rw [if_pos hgt]
        have : (Evaluate.consume env es k a).1 ≠ sOk := by
          intro h; rw [if_pos h] at ih; exact absurd ih (by simp)
        rw [if_neg this]
      · rename_i hgt
        rw [if_neg hgt]
        have hok : (Evaluate.consume env es k a).1 = sOk := by
          by_cases h : (Evaluate.consume env es k a).1 = sOk
          · exact h
          · rw [if_neg h] at ih; exact absurd ih (by simp)
        rw [if_pos hok] at ih ⊢
        simp only [Option.some.injEq] at ih ⊢
        funext k'
        rw [toMap_cons, ← ih]
        simp only [CM.set, toMap_cons]
        by_cases h1 : k' = k
        · subst h1; simp [hk]
        · simp [h1]

end Bridge
