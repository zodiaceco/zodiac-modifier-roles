import Bridge.Base

/-!
# Metadata of SDK trees, and what the evaluator reads of it

`isInl c` and `rawSz c`: the packer's `isInlined` and `inlinedSize` of the tree,
which give `D c`'s `inlineSize`. `region_tyEq`, `input_tyEq`:
`AbiLocation.sliceRegion` and `_read` read a node only through `TyEq`.
-/

namespace Bridge
open DecoderFaithfulness DecoderFaithfulness.Roles Normalize Evaluate

section
variable (avatar : Bytes)

/-! ## The node the evaluator runs -/

theorem toRoles_eq (c : Cond) :
    toRoles avatar c =
      ⟨encN c.enc, opN c.op, c.ch.map (toRoles avatar), 0, lbOf c, cvOf avatar c⟩ := by
  rcases c with ⟨e, o, cv, ch⟩
  rw [toRoles, toRolesL_eq]

theorem opOf_avatar {o : Nat} (h : ConditionPacking.opOf? o = some .EqualToAvatar) : o = 15 := by
  unfold ConditionPacking.opOf? at h
  split at h <;> simp_all

theorem opN_ne_avatar (o : Nat) : opN o ≠ .EqualToAvatar := by
  unfold opN
  split
  · simp
  · rename_i h15
    rcases hh : ConditionPacking.opOf? o with _ | op
    · simp
    · simp only [Option.getD_some]
      intro he
      subst he
      exact h15 (opOf_avatar hh)

theorem D_operator (c : Cond) : (D avatar c).operator = opN c.op := by
  unfold D
  rw [annotate_operator, toRoles_eq]
  simp [opN_ne_avatar]

theorem D_encoding (c : Cond) :
    (D avatar c).encoding = if encN c.enc = .EtherValue then .None else encN c.enc := by
  unfold D; rw [annotate_encoding, toRoles_eq]

theorem D_children (c : Cond) : (D avatar c).children = c.ch.map (D avatar) := by
  unfold D; rw [annotate_children, toRoles_eq]; simp

theorem D_compValue (c : Cond) : (D avatar c).compValue = cvOf avatar c := by
  unfold D; rw [annotate_compValue, toRoles_eq]

theorem D_leadingBytes (c : Cond) :
    (D avatar c).leadingBytes = if encN c.enc = .AbiEncoded then lbOf c else 0 := by
  unfold D; rw [annotate_leadingBytes, toRoles_eq]

end

/-! ## Height (the recursion depth `evaluate` needs) -/

mutual
  def height : Cond → Nat
    | ⟨_, _, _, ch⟩ => heightL ch + 1
  def heightL : List Cond → Nat
    | [] => 0
    | x :: xs => max (height x) (heightL xs)
end

theorem heightL_mem : ∀ {l : List Cond} {x : Cond}, x ∈ l → height x ≤ heightL l
  | _ :: _, _, .head _ => by simp only [heightL]; omega
  | _ :: _, _, .tail _ h => by simp only [heightL]; have := heightL_mem h; omega

theorem height_mem {c x : Cond} (h : x ∈ c.ch) : height x < height c := by
  rcases c with ⟨e, o, cv, ch⟩
  have := heightL_mem (l := ch) h
  simp only [height]; omega



section
variable (avatar : Bytes)

theorem isInlL_eq (l : List Cond) : isInlL l = l.all isInl := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp [isInlL, ih]

theorem isInl_eq (c : Cond) : isInl c = (!(c.enc == 2 || c.enc == 4 || c.enc == 5) && c.ch.all isInl) := by
  rcases c with ⟨e, o, cv, ch⟩; rw [isInl, isInlL_eq]

theorem encN_dyn (e : Nat) :
    (encN e = .Dynamic ∨ encN e = .Array ∨ encN e = .AbiEncoded) ↔ (e = 2 ∨ e = 4 ∨ e = 5) := by
  unfold encN
  constructor
  · intro h
    unfold ConditionPacking.encOf? at h
    split at h <;> simp_all
  · rintro (rfl | rfl | rfl) <;> simp [ConditionPacking.encOf?]

theorem all_congr_mem {α} {f g : α → Bool} : ∀ {l : List α}, (∀ x ∈ l, f x = g x) → l.all f = l.all g
  | [], _ => rfl
  | x :: xs, h => by
    have ih : xs.all f = xs.all g := all_congr_mem (l := xs) (fun y hy => h y (List.mem_cons_of_mem _ hy))
    simp only [List.all_cons, h x (by simp), ih]

theorem isInlined_toRoles (c : Cond) : isInlined (toRoles avatar c) = isInl c := by
  rw [isInlined_eq, toRoles_eq, isInl_eq, isInlinedAll_eq]
  simp only
  by_cases h : c.enc = 2 ∨ c.enc = 4 ∨ c.enc = 5
  · rw [ite_pos' ((encN_dyn c.enc).2 h)]
    have : (c.enc == 2 || c.enc == 4 || c.enc == 5) = true := by
      rcases h with h | h | h <;> simp [h]
    rw [this]; rfl
  · rw [ite_neg' (fun h' => h ((encN_dyn c.enc).1 h'))]
    have : (c.enc == 2 || c.enc == 4 || c.enc == 5) = false := by
      simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne]; omega
    rw [this, List.all_map]
    simp only [Bool.not_false, Bool.true_and]
    exact all_congr_mem fun x hx => isInlined_toRoles x
termination_by sizeOf c
decreasing_by exact sizeOf_lt_of_mem hx

/-- `inlinedSize` of the tree. -/
def rawSz (c : Cond) : Nat := inlinedSize (toRoles avatar c)

theorem D_inlineSize (c : Cond) :
    (D avatar c).inlineSize = if isInl c then rawSz avatar c else 0 := by
  unfold D rawSz; rw [annotate_inlineSize, isInlined_toRoles]

theorem encN_static (e : Nat) : encN e = .Static ↔ e = 1 := by
  unfold encN
  constructor
  · intro h; unfold ConditionPacking.encOf? at h; split at h <;> simp_all
  · rintro rfl; rfl

theorem encN_none (e : Nat) : encN e = .None ↔ (e = 0 ∨ ConditionPacking.encOf? e = none) := by
  unfold encN
  constructor
  · intro h
    rcases hh : ConditionPacking.encOf? e with _ | x
    · exact Or.inr rfl
    · rw [hh] at h; simp only [Option.getD_some] at h; subst h
      unfold ConditionPacking.encOf? at hh; split at hh <;> simp_all
  · rintro (rfl | h)
    · rfl
    · rw [h]; rfl

theorem rawSz_eq (c : Cond) :
    rawSz avatar c = if c.enc = 1 then 32
      else inlinedSizeLoop (decide (encN c.enc = .None)) (c.ch.map (toRoles avatar)) := by
  unfold rawSz
  rw [inlinedSize_eq, toRoles_eq]
  simp only
  by_cases h : c.enc = 1
  · rw [ite_pos' ((encN_static _).2 h), ite_pos' h]
  · rw [ite_neg' (fun h' => h ((encN_static _).1 h')), ite_neg' h]

/-! ## Non-structural subtrees -/

theorem NsOk.meta : ∀ {c : Cond}, NsOk c → isInl c = true ∧ rawSz avatar c = 0 := by
  intro c h
  induction h with
  | @leaf c he hch _ =>
    rw [isInl_eq, rawSz_eq, hch]
    rcases he with h | h <;> simp [h, inlinedSizeLoop]
  | @logical c hop he hall ih =>
    rw [isInl_eq, rawSz_eq, he]
    refine ⟨?_, ?_⟩
    · simp only [List.all_eq_true, Bool.and_eq_true]
      refine ⟨by decide, fun x hx => (ih x hx).1⟩
    · apply inlinedSizeLoop_zero
      intro ch hch
      simp only [List.mem_map] at hch
      obtain ⟨x, hx, rfl⟩ := hch
      exact (ih x hx).2

theorem inlinedSizeLoop_congr (b : Bool) :
    ∀ (as bs : List Condition), List.length as = bs.length →
      (∀ i (h1 : i < as.length) (h2 : i < bs.length), inlinedSize as[i] = inlinedSize bs[i]) →
      inlinedSizeLoop b as = inlinedSizeLoop b bs
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | a :: as, b' :: bs, hl, h => by
    simp only [inlinedSizeLoop]
    have h0 : inlinedSize a = inlinedSize b' := h 0 (by simp) (by simp)
    rw [h0, inlinedSizeLoop_congr b as bs (by simpa using hl)
      (fun i h1 h2 => h (i + 1) (by simpa using h1) (by simpa using h2))]

end


/-! ## Decoding -/

theorem childrenLoop_congr (data : Calldata) (body : Slice) (f g : Nat → Nat) :
    ∀ (n i h : Nat), (∀ j, i ≤ j → j < i + n → f j = g j) →
      childrenLoop data body f n i h = childrenLoop data body g n i h
  | 0, _, _, _ => rfl
  | n + 1, i, h, hfg => by
    simp only [childrenLoop, hfg i (Nat.le_refl _) (by omega)]
    split
    · rfl
    · rw [childrenLoop_congr data body f g n (i + 1) _ (fun j h1 h2 => hfg j (by omega) (by omega))]

theorem childrenLoop_prefix (data : Calldata) (body : Slice) (f : Nat → Nat) :
    ∀ (k K i h : Nat) (spans : List Slice), k ≤ K →
      childrenLoop data body f K i h = some spans →
      childrenLoop data body f k i h = some (spans.take k)
  | 0, _, _, _, _, _, _ => by simp [childrenLoop]
  | k + 1, 0, _, _, _, hk, _ => absurd hk (by omega)
  | k + 1, K + 1, i, h, spans, hk, hK => by
    simp only [childrenLoop] at hK ⊢
    split at hK
    · exact absurd hK (by simp)
    · obtain ⟨rest, hrest, rfl⟩ := Option.map_eq_some_iff.1 hK
      rw [childrenLoop_prefix data body f k K _ _ rest (by omega) hrest]
      simp

/-! ## `sliceRegion` and `_read` read the type -/

theorem LayEq.refl (d : Condition) : LayEq d d := rfl

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

theorem regionArrayLoop_congr (data : Calldata) (body : Slice) (fa fb : Slice → Option Nat)
    (hf : ∀ l, fa l = fb l) :
    ∀ n h cur, regionArrayLoop data body fa n h cur = regionArrayLoop data body fb n h cur
  | 0, _, _ => rfl
  | n + 1, h, cur => by
    simp only [regionArrayLoop, hf]
    split
    · rfl
    · split
      · rfl
      · exact regionArrayLoop_congr data body fa fb hf n _ _

theorem headSize_tyEq : ∀ {as bs : List Condition}, TyEqL as bs → headSize as = headSize bs
  | _, _, .nil => rfl
  | _, _, .cons h1 h2 => by
    simp only [headSize]
    rw [h1.layEq, headSize_tyEq h2]

mutual
  theorem region_tyEq (data : Calldata) : ∀ {d m : Condition}, TyEq d m →
      ∀ l, region data l d = region data l m
    | ⟨de, dop, dcs, ds, dlb, dcv⟩, ⟨me, mop, mcs, ms, mlb, mcv⟩, .mk he hl hcs, l => by
      simp only [LayEq] at he hl hcs
      subst he; subst hl
      rw [region_eq, region_eq]
      simp only
      split
      · rfl
      split
      · rfl
      rename_i hD
      by_cases hS : de = .Static
      · subst hS; rfl
      have hcs := hcs hS (fun h => hD (.inl h)) (fun h => hD (.inr h))
      split
      · exact regionNone_tyEq data hcs l
      split
      · cases hcs with
        | nil => rfl
        | cons h0 hrest =>
          have hl0 : _ = _ := h0.layEq
          simp only
          rw [hl0]
          split
          · rfl
          · rw [regionArrayLoop_congr data _ _ _ (fun l' => region_tyEq data h0 l')]
      split
      · rw [headSize_tyEq hcs]
        split
        · rfl
        · exact regionTuple_tyEq data hcs l 0 _
      · rfl

  theorem regionNone_tyEq (data : Calldata) : ∀ {as bs : List Condition}, TyEqL as bs →
      ∀ l, regionNone data l as = regionNone data l bs
    | _, _, .nil, _ => rfl
    | _, _, .cons h1 h2, l => by
      simp only [regionNone]
      rw [region_tyEq data h1 l, regionNone_tyEq data h2 l]

  theorem regionTuple_tyEq (data : Calldata) : ∀ {as bs : List Condition}, TyEqL as bs →
      ∀ l h cur, regionTuple data l as h cur = regionTuple data l bs h cur
    | _, _, .nil, _, _, _ => rfl
    | _, _, .cons h1 h2, l, h, cur => by
      have hl : _ = _ := h1.layEq
      simp only [regionTuple, hl]
      split
      · exact regionTuple_tyEq data h2 l _ _
      · split
        · rfl
        · rw [region_tyEq data h1]
          split
          · rfl
          · exact regionTuple_tyEq data h2 l _ _
end

theorem operand_tyEq (data : Calldata) {d m : Condition} (h : TyEq d m) (l : Slice) (z : Nat) :
    operand data l z d = operand data l z m := by
  unfold operand sliceRegion
  rw [region_tyEq data h l]

theorem input_tyEq (data : Calldata) {d m : Condition} (h : TyEq d m) (l : Slice) (z : Nat) :
    input data l z d = input data l z m := by
  unfold input
  rw [h.encoding, operand_tyEq data h l z]

theorem inputLength_tyEq (data : Calldata) {d m : Condition} (h : TyEq d m) (l : Slice)
    (z : Nat) : inputLength data l z d = inputLength data l z m := by
  unfold inputLength
  rw [h.encoding, operand_tyEq data h l z]

theorem pluckSpan_tyEq (data : Calldata) {d m : Condition} (h : TyEq d m) (l : Slice)
    (z : Nat) : pluckSpan data l z d = pluckSpan data l z m := by
  unfold pluckSpan
  rw [h.encoding, operand_tyEq data h l z]

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
