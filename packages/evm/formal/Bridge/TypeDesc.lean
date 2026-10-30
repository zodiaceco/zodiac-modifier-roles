import Bridge.AllN

/-!
# Normalization keeps type descriptions

The children of a check that reads its whole value (`EqualTo` on a tuple,
`Pass`, ...) only describe the value's type: `AbiLocation.size` and
`__input` read their encodings and sizes, and nothing below a word, `bytes`
or nested calldata (`TyEq`). `TD` lists the descriptions the SDK check
accepts there (`exactTy`). Normalization rewrites inside them (it sorts a
nested call's `Or`, say), but keeps their type: `td_normalize`, with
`RTy`, the same type on the SDK trees (`RTy.D`).
-/

namespace Bridge
open DecoderFaithfulness DecoderFaithfulness.Roles Normalize Evaluate

mutual
  theorem TyEq.trans : ∀ {a b c : Condition}, TyEq a b → TyEq b c → TyEq a c
    | _, _, _, .mk he1 hl1 hc1, .mk he2 hl2 hc2 =>
      .mk (he1.trans he2) ⟨hl1.1.trans hl2.1, hl1.2.trans hl2.2⟩ fun h1 h2 h3 =>
        TyEqL.trans (hc1 h1 h2 h3)
          (hc2 (fun h => h1 (he1.trans h)) (fun h => h2 (he1.trans h)) (fun h => h3 (he1.trans h)))
  theorem TyEqL.trans : ∀ {as bs cs : List Condition}, TyEqL as bs → TyEqL bs cs → TyEqL as cs
    | _, _, _, .nil, .nil => .nil
    | _, _, _, .cons h1 t1, .cons h2 t2 => .cons (TyEq.trans h1 h2) (TyEqL.trans t1 t2)
end

theorem allN_winEnc_inl {w : Cond} (h : AllN winEnc w) : isInl w = true := by
  induction h with
  | @mk c hc _ ih =>
    rw [isInl_eq]
    have : (c.enc == 2 || c.enc == 4 || c.enc == 5) = false := by
      unfold winEnc at hc; rcases hc with h | h | h <;> simp [h]
    rw [this, Bool.not_false, Bool.true_and, List.all_eq_true]
    exact ih

theorem isInl_abi {c : Cond} (he : c.enc = 5) : isInl c = false := by rw [isInl_eq, he]; rfl

theorem isInl_dyn {c : Cond} (he : c.enc = 2) : isInl c = false := by rw [isInl_eq, he]; rfl

section
variable (avatar : Bytes)

/-- Same type, on the SDK trees: what `D` makes of a node for
    `AbiLocation.size` and `__input`. -/
inductive RTy : Cond → Cond → Prop
  | mk {a b : Cond} : a.enc = b.enc → isInl a = isInl b →
      (isInl a = true → rawSz avatar a = rawSz avatar b) →
      (a.enc ≠ 1 → a.enc ≠ 2 → a.enc ≠ 5 → a.ch.length = b.ch.length) →
      (∀ i (h1 : i < a.ch.length) (h2 : i < b.ch.length), a.enc ≠ 1 → a.enc ≠ 2 → a.enc ≠ 5 →
        RTy a.ch[i] b.ch[i]) → RTy a b

theorem RTy.inl {a b : Cond} (h : RTy avatar a b) : isInl a = isInl b := by cases h; assumption
theorem RTy.raw {a b : Cond} (h : RTy avatar a b) : isInl a = true → rawSz avatar a = rawSz avatar b := by
  cases h; assumption

theorem RTy.refl : ∀ c : Cond, RTy avatar c c
  | ⟨e, o, cv, ch⟩ => .mk rfl rfl (fun _ => rfl) (fun _ _ _ => rfl) fun i h1 _ _ _ _ => RTy.refl ch[i]
termination_by c => sizeOf c
decreasing_by
  simp_wf
  have := List.sizeOf_lt_of_mem (List.getElem_mem (l := ch) h1)
  omega

theorem tyEqL_map : ∀ (as bs : List Cond), as.length = bs.length →
    (∀ i (h1 : i < as.length) (h2 : i < bs.length), TyEq (D avatar as[i]) (D avatar bs[i])) →
    TyEqL (as.map (D avatar)) (bs.map (D avatar))
  | [], [], _, _ => .nil
  | a :: as, b :: bs, hl, h =>
    .cons (h 0 (by simp) (by simp)) (tyEqL_map as bs (by simpa using hl)
      fun i h1 h2 => h (i + 1) (by simp; omega) (by simp; omega))
  | [], _ :: _, hl, _ => by simp at hl
  | _ :: _, [], hl, _ => by simp at hl

/-- Trees of the same type give nodes of the same type. -/
theorem RTy.D {a b : Cond} (h : RTy avatar a b) : TyEq (D avatar a) (D avatar b) := by
  induction h with
  | @mk a b he hi hs hlen _ ih =>
    refine .mk (by rw [D_encoding, D_encoding, he]) ⟨?_, ?_⟩ ?_
    · rw [D_inlined, D_inlined, ← hi]; by_cases h : isInl a = true <;> simp [h, hs]
    · rw [D_size, D_size, ← hi]; by_cases h : isInl a = true <;> simp [h, hs]
    · intro h1 h2 h3
      have e1 : a.enc ≠ 1 := fun h => h1 (by rw [D_encoding, h]; rfl)
      have e2 : a.enc ≠ 2 := fun h => h2 (by rw [D_encoding, h]; rfl)
      have e5 : a.enc ≠ 5 := fun h => h3 (by rw [D_encoding, h]; rfl)
      rw [D_children, D_children]
      exact tyEqL_map avatar _ _ (hlen e1 e2 e5) fun i h1 h2 => ih i h1 h2 e1 e2 e5

theorem container_raw {c c' : Cond} (he : c.enc = c'.enc) (hl : c.ch.length = c'.ch.length)
    (hp : ∀ i (h1 : i < c.ch.length) (h2 : i < c'.ch.length),
      isInl c.ch[i] = isInl c'.ch[i] ∧ (isInl c.ch[i] = true → rawSz avatar c.ch[i] = rawSz avatar c'.ch[i])) :
    isInl c = isInl c' ∧ (isInl c = true → rawSz avatar c = rawSz avatar c') := by
  have hall : c.ch.all isInl = c'.ch.all isInl := by
    rw [Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
    constructor
    · intro h x hx
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
      rw [← (hp i (by omega) hi).1]; exact h _ (List.getElem_mem _)
    · intro h x hx
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
      rw [(hp i hi (by omega)).1]; exact h _ (List.getElem_mem _)
  have hinl : isInl c = isInl c' := by rw [isInl_eq, isInl_eq, he, hall]
  refine ⟨hinl, fun hi => ?_⟩
  rw [rawSz_eq, rawSz_eq, he]
  split
  · rfl
  · apply inlinedSizeLoop_congr _ _ _ (by simp [hl])
    intro i h1 h2
    have h1' : i < c.ch.length := by simpa using h1
    have h2' : i < c'.ch.length := by simpa using h2
    simp only [List.getElem_map]
    have hci : isInl c.ch[i] = true := by
      rw [isInl_eq] at hi; simp only [Bool.and_eq_true, List.all_eq_true] at hi
      exact hi.2 _ (List.getElem_mem _)
    exact (hp i h1' h2').2 hci

/-- A node whose children have the types of `c`'s has `c`'s type. -/
theorem rty_withCh {c : Cond} {l : List Cond} (hlen : l.length = c.ch.length)
    (h : ∀ i (h1 : i < l.length) (h2 : i < c.ch.length), RTy avatar l[i] c.ch[i]) :
    RTy avatar { c with ch := l } c := by
  have r := container_raw avatar (c := { c with ch := l }) (c' := c) rfl hlen
    fun i h1 h2 => ⟨(h i h1 h2).inl avatar, (h i h1 h2).raw avatar⟩
  exact .mk rfl r.1 r.2 (fun _ _ _ => hlen) fun i h1 h2 _ _ _ => h i h1 h2

/-! ## Normalization inside a description -/

/-- A node other than `And`/`Or` stays itself, with its children normalized. -/
theorem normalize_nonlog (k : Nat) {c : Cond} (h1 : c.op ≠ 1) (h2 : c.op ≠ 2)
    (hkw : keepsAsWritten c = false) :
    normalize (k + 1) c = { c with ch := c.ch.map (normalize k) } := by
  rw [normalize]
  split
  · rename_i h; rw [hkw] at h; cases h
  dsimp only
  have hop : ({ c with ch := c.ch.map (normalize k) } : Cond).op = c.op := rfl
  generalize ({ c with ch := c.ch.map (normalize k) } : Cond) = x at hop ⊢
  have hl : isLogical x = false := by unfold isLogical; simp [hop, h1, h2]
  have hf : flatten x = x := by unfold flatten; simp [hl]
  have hd : dedupe x = x := by unfold dedupe; simp [hl]
  have hu : unwrap x = x := by unfold unwrap; simp [hl]
  have hp : pushDownOr (normalize k) x = x := by unfold pushDownOr pushStep; simp [hop, h2]
  have hs : sortB x = x := by unfold sortB; simp [hl]
  rw [hf, hd, hu, hp, hs]

theorem navOp_false {o : Nat} (h : navOp o = false) : o ≠ 1 ∧ o ≠ 2 ∧ o ≠ 5 := by
  unfold navOp at h; simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne] at h; omega

/-- **Normalization keeps a type description's type.** -/
theorem td_normalize : ∀ (k : Nat) (x : Cond), TD x → TD (normalize k x) ∧ RTy avatar (normalize k x) x
  | 0, x, h => ⟨h, RTy.refl avatar x⟩
  | k + 1, x, h => by
    by_cases hkw : keepsAsWritten x = true
    · rw [normalize, if_pos hkw]; exact ⟨h, RTy.refl avatar x⟩
    have hkw' : keepsAsWritten x = false := by simpa using hkw
    have IH := td_normalize k
    cases h with
    | abi he h1 h2 =>
      rw [normalize_nonlog k h1 h2 hkw']
      have he' : ({ x with ch := x.ch.map (normalize k) } : Cond).enc = 5 := he
      have hop : ({ x with ch := x.ch.map (normalize k) } : Cond).op = x.op := rfl
      generalize ({ x with ch := x.ch.map (normalize k) } : Cond) = y at he' hop ⊢
      refine ⟨.abi he' (by rw [hop]; exact h1) (by rw [hop]; exact h2), .mk (by rw [he', he])
        (by rw [isInl_abi he', isInl_abi he]) (fun hi => by rw [isInl_abi he'] at hi; cases hi)
        (fun _ _ h5 => absurd he' h5) (fun _ _ _ _ _ h5 => absurd he' h5)⟩
    | @slice _ w h13 he hch hw =>
      rw [normalize_nonlog k (by omega) (by omega) hkw']
      have hch' : ({ x with ch := x.ch.map (normalize k) } : Cond).ch = [normalize k w] := by
        simp [hch]
      have hw' : x.enc = 1 → AllN winEnc (normalize k w) := fun h1 =>
        allN_normalize winEnc (fun _ _ => Iff.rfl) (Or.inl rfl) (.mk (Or.inl rfl) fun _ h => nomatch h)
          k w (hw h1)
      refine ⟨.slice h13 he hch' hw', .mk rfl ?_ ?_ (fun h1 h2 _ => by simp at h1 h2; omega)
        (fun _ _ _ h1 h2 _ => by simp at h1 h2; omega)⟩
      · rcases he with e | e
        · rw [isInl_eq, isInl_eq, hch', hch]
          simp [allN_winEnc_inl (hw' e), allN_winEnc_inl (hw e)]
        · rw [isInl_dyn (c := { x with ch := _ }) e, isInl_dyn e]
      · intro hi
        rcases he with e | e
        · rw [rawSz_eq, rawSz_eq]; simp [e]
        · rw [isInl_dyn (c := { x with ch := _ }) e] at hi; cases hi
    | node hnav henc hch =>
      obtain ⟨h1, h2, h5⟩ := navOp_false hnav
      rw [normalize_nonlog k h1 h2 hkw']
      refine ⟨.node hnav henc fun y hy => ?_, rty_withCh avatar (by simp) fun i h1 _ => ?_⟩
      · obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hy; exact (IH z (hch z hz)).1
      · simp only [List.getElem_map]; exact (IH _ (hch _ (List.getElem_mem _))).2

theorem td_map (k : Nat) {c : Cond} (h : ∀ x ∈ c.ch, TD x) :
    (∀ x ∈ ({ c with ch := c.ch.map (normalize k) } : Cond).ch, TD x) ∧
      RTy avatar { c with ch := c.ch.map (normalize k) } c := by
  refine ⟨fun y hy => ?_, rty_withCh avatar (by simp) fun i h1 _ => ?_⟩
  · obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hy; exact (td_normalize avatar k z (h z hz)).1
  · simp only [List.getElem_map]; exact (td_normalize avatar k _ (h _ (List.getElem_mem _))).2

end

mutual
  theorem tyEq_self : ∀ d : Condition, TyEq d d
    | ⟨_, _, cs, _, _, _, _⟩ => .mk rfl ⟨rfl, rfl⟩ fun _ _ _ => tyEqL_self cs
  theorem tyEqL_self : ∀ cs : List Condition, TyEqL cs cs
    | [] => .nil
    | c :: cs => .cons (tyEq_self c) (tyEqL_self cs)
end

end Bridge
