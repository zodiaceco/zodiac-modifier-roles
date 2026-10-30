import Bridge.Base

/-!
# Metadata of SDK trees, and what the evaluator reads of it

`isInl c` and `rawSz c`: `Topology.isInlined` and `inlinedSize` of the tree,
which give `D c`'s `inlined` and `size`. `size_tyEq`, `input_tyEq`:
`AbiLocation.size` and `__input` read a node only through `TyEq`.
-/

namespace Bridge
open DecoderFaithfulness DecoderFaithfulness.Roles Normalize Evaluate

section
variable (avatar : Bytes)

/-! ## The node the evaluator runs -/

theorem toRoles_eq (c : Cond) :
    toRoles avatar c =
      ⟨encN c.enc, opN c.op, c.ch.map (toRoles avatar), false, 0, lbOf c, cvOf avatar c⟩ := by
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

theorem Node.operator {c : Cond} {d : Condition} (h : Node avatar c d) : d.operator = opN c.op := by
  rw [h]; exact D_operator avatar c
theorem Node.encoding {c : Cond} {d : Condition} (h : Node avatar c d) :
    d.encoding = (D avatar c).encoding := by rw [h]
theorem Node.compValue {c : Cond} {d : Condition} (h : Node avatar c d) :
    d.compValue = cvOf avatar c := by rw [h]; exact D_compValue avatar c
theorem Node.children {c : Cond} {d : Condition} (h : Node avatar c d) :
    d.children = c.ch.map (D avatar) := by rw [h]; exact D_children avatar c
theorem Node.inlined {c : Cond} {d : Condition} (h : Node avatar c d) :
    d.inlined = (D avatar c).inlined := by rw [h]
theorem Node.refl (c : Cond) : Node avatar c (D avatar c) := by
  unfold Node; cases D avatar c; rfl

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

theorem D_inlined (c : Cond) :
    (D avatar c).inlined = decide ((if isInl c then rawSz avatar c else 0) > 0) := by
  unfold D rawSz; rw [annotate_inlined, isInlined_toRoles]

theorem D_size (c : Cond) : (D avatar c).size = if isInl c then rawSz avatar c else 0 := by
  unfold D rawSz; rw [annotate_size, isInlined_toRoles]

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

/-- `isInl c = (D c).inlined`: an inlined node has a positive size. -/
def Sane (c : Cond) : Prop := isInl c = (D avatar c).inlined

theorem Sane.pos {c : Cond} (h : Sane avatar c) (hi : isInl c = true) : 0 < rawSz avatar c := by
  unfold Sane at h; rw [D_inlined, hi] at h; simp at h; omega

theorem LayEq.of_sane {c : Cond} {m : Condition} (hs : Sane avatar c) (hl : LayEq (D avatar c) m) :
    isInl c = m.inlined ∧ (isInl c = true → rawSz avatar c = m.size) := by
  refine ⟨hs.trans hl.1, fun hi => ?_⟩
  rw [← hl.2, D_size, ite_pos' hi]

theorem LayEq.of_raw {c : Cond} {m : Condition} (h1 : isInl c = m.inlined)
    (h2 : isInl c = true → rawSz avatar c = m.size) (hpos : m.inlined = true → 0 < m.size)
    (hz : m.inlined = false → m.size = 0) :
    LayEq (D avatar c) m ∧ Sane avatar c := by
  unfold Sane LayEq
  rw [D_inlined, D_size]
  by_cases hi : isInl c = true
  · have := h2 hi
    have hp := hpos (h1 ▸ hi)
    simp [hi, this, hp, ← h1]
  · have hf : isInl c = false := by simpa using hi
    have hm : m.inlined = false := h1 ▸ hf
    simp [hf, hm, hz hm]

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
