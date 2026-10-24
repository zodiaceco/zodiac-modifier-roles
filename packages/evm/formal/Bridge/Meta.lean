import Bridge.Plain

/-!
# Layout metadata of SDK trees

The evaluator's `inlined` and `size` of `D c` come from `Topology.isInlined`
(`isInl c`) and `inlinedSize` of the tree. They are determined by the
encoding and the children's: a logical node has the layout of its
structural children (its non-structural children are inline with size 0), a
container with children of the same layouts has the same layout.
-/

namespace Bridge
open DecoderFaithfulness DecoderFaithfulness.Roles Normalize Evaluate

section
variable (avatar : Bytes) (P : Nat → Option Condition)

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

/-! ## What `Fits` says about metadata -/

theorem Fits.sane {c : Cond} {d m : Condition} (h : Fits avatar P c d m) :
    isStruct c = true → Sane avatar c := by
  induction h with
  | pass _ _ _ _ _ hsn _ => exact fun _ => hsn
  | ns hns => intro hs; rw [hns] at hs; exact absurd hs (by simp)
  | logical _ _ _ _ _ _ hsn => exact fun _ => hsn
  | tup _ _ _ _ _ _ _ _ _ hsn => exact fun _ => hsn
  | arr _ _ _ _ _ _ _ _ hsn => exact fun _ => hsn
  | slice _ _ _ _ _ _ _ hsn _ => exact fun _ => hsn
  | leaf _ _ _ _ _ _ _ hsn _ _ _ _ => exact fun _ => hsn
  | varAbi _ _ _ _ _ _ _ _ _ _ ih => exact ih
  | varDyn _ _ _ _ ih => exact ih
  | @zip c d m t h he _ _ _ _ _ _ _ _ _ _ _ =>
    intro hs; rw [isStruct_eq] at hs
    have : (c.op == 1 || c.op == 2) = false := by rcases h with h | h <;> simp [h]
    rw [this] at hs; simp_all
  | zipLogical _ _ hns => intro hs; rw [hns] at hs; cases hs

theorem Fits.sane_lay {c : Cond} {m : Condition} (h : Fits avatar P c (D avatar c) m)
    (hs : isStruct c = true) : Sane avatar c ∧ LayEq (D avatar c) m := by
  refine ⟨h.sane avatar P hs, ?_⟩
  cases h with
  | pass _ _ _ hl _ _ _ => exact hl
  | ns hns => rw [hns] at hs; exact absurd hs (by simp)
  | logical _ _ _ _ hl _ _ => exact hl
  | tup _ _ _ _ hl _ _ _ _ _ => exact hl
  | arr _ _ _ _ hl _ _ _ _ => exact hl
  | slice _ _ _ hl _ _ _ _ _ => exact hl
  | leaf _ _ _ ht _ _ _ _ _ _ _ _ _ => exact ht.layEq
  | varAbi _ _ _ _ hl _ _ _ _ _ => exact hl
  | varDyn _ _ hl _ => exact hl
  | zip h he _ _ _ _ _ _ _ _ _ _ =>
    rw [isStruct_eq] at hs
    have : (c.op == 1 || c.op == 2) = false := by rcases h with h | h <;> simp [h]
    rw [this] at hs; simp_all
  | zipLogical _ _ hns => rw [hns] at hs; cases hs

theorem hasZip_eq (c : Cond) : hasZip c = (c.op == 10 || c.op == 11 || c.ch.any hasZip) := by
  rcases c with ⟨e, o, cv, ch⟩
  rw [hasZip]
  simp only
  congr 1
  conv => rhs; rw [← List.attach_map_subtype_val ch]
  rw [List.any_map]; rfl

/-- A non-structural node that fits: a subtree reading no calldata (and
    plucking into no slot with a layout), or one with a Zip at a value that
    is not inlined. -/
theorem Fits.nsOk {c : Cond} {d m : Condition} (h : Fits avatar P c d m) :
    isStruct c = false → (NsOk c ∧ ∀ k ∈ plucks c, P k = none) ∨ (hasZip c = true ∧ m.inlined = false) := by
  induction h with
  | ns _ hns _ hpl => exact fun _ => .inl ⟨hns, hpl⟩
  | @zip c d m t h _ _ _ hm _ _ _ _ _ _ _ _ =>
    exact fun _ => .inr ⟨by rw [hasZip_eq]; rcases h with h | h <;> simp [h], hm⟩
  | zipLogical _ _ _ hz _ hm _ _ => exact fun _ => .inr ⟨hz, hm⟩
  | pass _ _ h _ _ _ _ => intro hs; rw [h] at hs; exact absurd hs (by simp)
  | logical _ _ h _ _ _ _ => intro hs; rw [h] at hs; exact absurd hs (by simp)
  | tup h5 he _ _ _ _ _ _ _ _ =>
    intro hs; rw [isStruct_eq] at hs; rcases he with h | h <;> simp_all
  | arr hop he _ _ _ _ _ _ _ =>
    intro hs; rw [isStruct_eq] at hs; rcases hop with h | h | h | h <;> simp_all
  | slice h13 he _ _ _ _ _ _ =>
    intro hs; rw [isStruct_eq] at hs; rcases he with h | h <;> simp_all
  | leaf _ h _ _ _ _ _ _ _ _ _ _ _ => intro hs; rw [h] at hs; exact absurd hs (by simp)
  | varAbi h5 he _ _ _ _ _ _ _ _ _ => intro hs; rw [isStruct_eq] at hs; simp_all
  | @varDyn c d m _ he _ hf _ =>
    intro hs
    have hops := Fits.dyn_op avatar P hf he
    rw [isStruct_eq] at hs
    have : (c.op == 1 || c.op == 2) = false := by simp [hops.1, hops.2]
    rw [this] at hs; simp [he] at hs

/-- Layout of a node fitting `m`, in terms of the tree. -/
theorem Fits.raw {c : Cond} {m : Condition} (h : Fits avatar P c (D avatar c) m)
    (hs : isStruct c = true) :
    isInl c = m.inlined ∧ (isInl c = true → rawSz avatar c = m.size) ∧
      (m.inlined = true → 0 < m.size) ∧ (m.inlined = false → m.size = 0) := by
  obtain ⟨hsn, hl⟩ := h.sane_lay avatar P hs
  obtain ⟨h1, h2⟩ := hl.of_sane avatar hsn
  refine ⟨h1, h2, fun hi => ?_, fun hi => ?_⟩
  · have := hsn.pos avatar (h1 ▸ hi); rw [← h2 (h1 ▸ hi)]; exact this
  · rw [← hl.2, D_size, if_neg (by rw [h1, hi]; simp)]

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

/-- A logical node whose children fit `m` has `m`'s layout. -/
theorem logical_lay {c : Cond} {m : Condition} (hop : c.op = 1 ∨ c.op = 2) (he : c.enc = 0)
    (hs : isStruct c = true) (hch : ∀ x ∈ c.ch, Fits avatar P x (D avatar x) m) :
    LayEq (D avatar c) m ∧ Sane avatar c := by
  have hs' : c.ch.any isStruct = true := by
    rw [isStruct_eq] at hs; rcases hop with h | h <;> simp_all
  obtain ⟨x0, hx0, hsx0⟩ := List.any_eq_true.1 hs'
  have hraw0 := (hch x0 hx0).raw avatar P hsx0
  have hchild : ∀ x ∈ c.ch, (isInl x = m.inlined ∧ (isInl x = true → rawSz avatar x = m.size)) ∨
      (isInl x = true ∧ rawSz avatar x = 0) ∨ m.inlined = false := by
    intro x hx
    by_cases hsx : isStruct x = true
    · have := (hch x hx).raw avatar P hsx; exact Or.inl ⟨this.1, this.2.1⟩
    · rcases (hch x hx).nsOk avatar P (by simpa using hsx) with ⟨hn, -⟩ | ⟨-, hm⟩
      · exact Or.inr (Or.inl (hn.meta avatar))
      · exact Or.inr (Or.inr hm)
  apply LayEq.of_raw avatar _ _ hraw0.2.2.1 hraw0.2.2.2
  · rw [isInl_eq, he]
    by_cases hm : m.inlined = true
    · rw [hm, Bool.and_eq_true, List.all_eq_true]
      refine ⟨by decide, fun x hx => ?_⟩
      rcases hchild x hx with h | h | h
      · rw [h.1, hm]
      · exact h.1
      · rw [hm] at h; cases h
    · have hmf : m.inlined = false := by simpa using hm
      rw [hmf]
      simp only [Bool.and_eq_false_iff]
      right
      rw [List.all_eq_false]
      exact ⟨x0, hx0, by rw [hraw0.1, hmf]; simp⟩
  · intro hi
    have hm : m.inlined = true := by
      have : isInl x0 = true := by
        rw [isInl_eq] at hi; simp only [Bool.and_eq_true, List.all_eq_true] at hi
        exact hi.2 x0 hx0
      rw [← hraw0.1]; exact this
    rw [rawSz_eq, he]
    simp only [Nat.zero_ne_one, ite_false]
    have hnone : decide (encN 0 = .None) = true := by decide
    rw [hnone]
    apply inlinedSizeLoop_first _ m.size (hraw0.2.2.1 hm)
    · intro ch hch'
      simp only [List.mem_map] at hch'
      obtain ⟨x, hx, rfl⟩ := hch'
      rcases hchild x hx with h | h | h
      · right; exact h.2 (h.1.trans hm)
      · left; exact h.2
      · rw [hm] at h; cases h
    · exact ⟨toRoles avatar x0, List.mem_map_of_mem hx0, hraw0.2.1 (hraw0.1.trans hm)⟩

end
end Bridge
