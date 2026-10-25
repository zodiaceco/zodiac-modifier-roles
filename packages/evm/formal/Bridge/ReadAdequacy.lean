import Bridge.ReadLoops

/-!
# The evaluator computes the contract's reading

`adequacy`: on every calldata, for every tree `c` whose nodes are
well-formed (`AllN adOk`), the evaluator transcription (`Evaluate.evalC`)
and the reading (`sem (readWorld ..) c`) agree, whenever the evaluator does
not revert: both pass with the same consumptions (as a map) and slots, or
both fail with the same slots. A revert (an array length above `2^64 - 1`,
a compValue the evaluator cannot read) denies the call anyway.
-/

namespace Bridge
open DecoderFaithfulness DecoderFaithfulness.Roles Normalize Evaluate

/-- What adequacy needs of a node (the SDK check enforces each): a known
    operator; the children of a `Matches` on a tuple or calldata all read a
    parameter (`AbiLocation` gives every child a field); a `Slice`'s child
    is a leaf; a Zip's first child is a `Matches` on a tuple whose children
    all read a field. -/
def adOk (c : Cond) : Prop :=
  (ConditionPacking.opOf? c.op).isSome = true ∧
  (c.op = 5 → (c.enc = 3 ∨ c.enc = 5) → ∀ x ∈ c.ch, isStruct x = true) ∧
  (c.op = 13 → ∀ x ∈ c.ch, x.ch = [] ∧ navOp x.op = false) ∧
  (c.op = 10 ∨ c.op = 11 → ∃ t rest, c.ch = t :: rest ∧ t.op = 5 ∧ t.enc = 3 ∧
    ∀ y ∈ t.ch, isStruct y = true)

theorem opKnown_cases {o : Nat} (h : (ConditionPacking.opOf? o).isSome = true) :
    o = 0 ∨ o = 1 ∨ o = 2 ∨ o = 4 ∨ o = 5 ∨ o = 6 ∨ o = 7 ∨ o = 8 ∨ o = 10 ∨ o = 11 ∨ o = 13 ∨
      o = 14 ∨ (15 ≤ o ∧ o ≤ 20) ∨ o = 21 ∨ o = 22 ∨ o = 23 ∨ o = 28 ∨ o = 30 := by
  unfold ConditionPacking.opOf? at h
  split at h <;> first | omega | simp at h

theorem leadingCheck_ne_ok {data : Calldata} {loc : Nat} {cv : Bytes} {s : Nat}
    (h : leadingCheck data loc cv = some s) : s ≠ sOk := by
  unfold leadingCheck at h
  repeat' split at h
  all_goals first | (subst h; decide) | (simp only [Option.some.injEq] at h; subst h; decide) | simp at h

theorem childrenE_inl {data : Calldata} {loc : Nat} {d : Condition} {s : Nat}
    (h : childrenE data loc d = .inl s) : s = revert := by
  unfold childrenE at h
  split at h
  · simp only [Sum.inl.injEq] at h; exact h.symm
  · simp at h

theorem zipLocsGo_spec (data : Calldata) (n : Nat) (cv : Bytes) :
    ∀ (fields : List Condition) (sl : Slots) (f : Nat) (len : Option Nat) (acc : List (List Nat)),
    (∀ s, zipLocsGo data n cv fields sl f len acc = .inl s → s ≠ sOk) ∧
    (∀ locss m, zipLocsGo data n cv fields sl f len acc = .inr (locss, m) →
      locss.length = acc.length + fields.length)
  | [], sl, f, len, acc => by simp [zipLocsGo]
  | fd :: rest, sl, f, len, acc => by
    have ih := fun len' acc' => zipLocsGo_spec data n cv rest sl (f + 1) len' acc'
    constructor
    · intro s h
      unfold zipLocsGo at h
      repeat' split at h
      all_goals first
        | (simp only [Sum.inl.injEq] at h; subst h; decide)
        | exact (ih _ _).1 s h
        | (rename_i hc; have := childrenE_inl hc; simp only [Sum.inl.injEq] at h; subst h; rw [this]; decide)
        | simp at h
    · intro locss m h
      unfold zipLocsGo at h
      repeat' split at h
      all_goals first
        | simp at h
        | (have := (ih _ _).2 locss m h; simp at this ⊢; omega)

section
variable (avatar : Bytes) (env : Env) (henv : EnvOk env) (data : Calldata) (n : Nat)

local notation "RW" => readWorld avatar env data n

theorem Corr.of_zip {f : Nat}
    {cs0 : List Cond} (hx : ∀ x ∈ cs0, ∀ l cons sl, (evalC env data n f l (D avatar x) cons sl).status ≠ revert →
      Rel (evalC env data n f l (D avatar x) cons sl) (sem RW x (.pos l) sl (toMap cons))) :
    ∀ (cs : List Cond), (∀ x ∈ cs, x ∈ cs0) → ∀ (locs : List Nat),
    Corr env data n f ((cs.map (D avatar)).zip locs) ((cs.zip (locs.map RV.pos)).map fun p => sem RW p.1 p.2)
  | [], _, _ => by simp; exact .nil
  | _ :: _, _, [] => by simp; exact .nil
  | x :: xs, hm, l :: ls => by
    simp only [List.map_cons, List.zip_cons_cons]
    exact .cons (fun cons sl h => hx x (hm x (by simp)) l cons sl h)
      (Corr.of_zip hx xs (fun y hy => hm y (by simp [hy])) ls)

theorem Corr.of_zipWith {f : Nat}
    {cs0 : List Cond} (hx : ∀ x ∈ cs0, ∀ l cons sl, (evalC env data n f l (D avatar x) cons sl).status ≠ revert →
      Rel (evalC env data n f l (D avatar x) cons sl) (sem RW x (.pos l) sl (toMap cons))) :
    ∀ (cs : List Cond), (∀ x ∈ cs, x ∈ cs0) → ∀ (locs : List Nat),
    Corr env data n f ((cs.map (D avatar)).zip locs)
      (List.zipWith (fun s l => s (RV.pos l)) (cs.map (sem RW)) locs)
  | [], _, _ => by simp; exact .nil
  | _ :: _, _, [] => by simp; exact .nil
  | x :: xs, hm, l :: ls => by
    simp only [List.map_cons, List.zip_cons_cons, List.zipWith_cons_cons]
    exact .cons (fun cons sl h => hx x (hm x (by simp)) l cons sl h)
      (Corr.of_zipWith hx xs (fun y hy => hm y (by simp [hy])) ls)

theorem nodeAt_at (c : Cond) (l : Nat) : nodeAt avatar c (.pos l) = D avatar c := rfl

theorem D_enc_abi (c : Cond) : (D avatar c).encoding = .AbiEncoded ↔ c.enc = 5 := by
  rw [D_encoding]
  constructor
  · intro h
    split at h
    · simp at h
    · unfold encN ConditionPacking.encOf? at h; split at h <;> simp_all
  · intro h; simp [h, encN, ConditionPacking.encOf?]

theorem adjust_eq (c : Cond) (l : Nat) :
    (if l > 0 ∧ (D avatar c).encoding = .AbiEncoded then l + 32 else l) = adjust c.enc l := by
  unfold adjust; simp only [D_enc_abi]

theorem sem_matchesT_el (t : Cond) (ht5 : t.op = 5) (ht3 : t.enc = 3) (hs : ∀ y ∈ t.ch, isStruct y = true)
    (ls : List Nat) (hl : t.ch.length ≤ ls.length) :
    sem RW t (.el ls) = seqT ((t.ch.zip (ls.map RV.pos)).map fun p => sem RW p.1 p.2) := by
  funext sl cs
  rw [sem_eq, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos ⟨ht5, Or.inl ht3⟩]
  simp only [matchesT, readWorld, matchLocs, Option.isSome_some, ite_true, Option.getD_some]
  rw [assign_struct _ _ _ _ hs (by simpa using hl)]

end
section
variable (avatar : Bytes) (env : Env) (henv : EnvOk env) (data : Calldata) (n : Nat)

local notation "RW" => readWorld avatar env data n

include henv in
/-- **Adequacy**, at a location or a `Slice` window (where only a leaf is
    evaluated). -/
theorem adequacy_gen : ∀ (f : Nat) (c : Cond) (v : RV), height c < f → AllN adOk c →
    (∀ l sz, v = .win l sz → c.ch = [] ∧ navOp c.op = false) → (∀ ls, v ≠ .el ls) →
    ∀ cons sl, (evalC env data n f v.loc (nodeAt avatar c v) cons sl).status ≠ revert →
    Rel (evalC env data n f v.loc (nodeAt avatar c v) cons sl) (sem RW c v sl (toMap cons))
  | 0, c, _, h, _, _, _, _, _, _ => absurd h (by omega)
  | f + 1, c, v, hh, hinv, hv, hel, cons, sl, hne => by
    have hok : adOk c := AllN.self _ hinv
    have hchI : ∀ x ∈ c.ch, AllN adOk x := AllN.ch _ hinv
    have hhx : ∀ x ∈ c.ch, height x < f := fun x hx => by have := height_mem hx; omega
    have IH := adequacy_gen f
    -- a child at a location
    have IHat : ∀ x ∈ c.ch, ∀ l cons sl, (evalC env data n f l (D avatar x) cons sl).status ≠ revert →
        Rel (evalC env data n f l (D avatar x) cons sl) (sem RW x (.pos l) sl (toMap cons)) :=
      fun x hx l cons sl h => IH x (.pos l) (hhx x hx) (hchI x hx) (fun _ _ h => by cases h)
        (fun _ h => by cases h) cons sl h
    have hop := nodeAt_operator avatar c v
    -- navigating operators run at a location
    have hat : navOp c.op = true → ∃ l, v = .pos l := by
      intro hn
      cases v with
      | pos l => exact ⟨l, rfl⟩
      | win l sz => have := (hv l sz rfl).2; rw [hn] at this; cases this
      | el ls => exact absurd rfl (hel ls)
    rw [sem_eq]
    by_cases h0 : c.op = 0
    · rw [if_pos h0]
      have hd : (nodeAt avatar c v).operator = .Pass := by rw [hop, h0]; rfl
      rw [evalC_pass env data n f _ _ cons sl hd]
      exact Rel.ok cons sl
    rw [if_neg h0]
    by_cases h1 : c.op = 1
    · rw [if_pos h1]
      obtain ⟨l, rfl⟩ := hat (by simp [navOp, h1])
      have hd : (D avatar c).operator = .And := by rw [D_operator, h1]; rfl
      change (evalC env data n (f + 1) l (D avatar c) cons sl).status ≠ revert at hne
      change Rel (evalC env data n (f + 1) l (D avatar c) cons sl) _
      rw [evalC_and env data n f l _ cons sl hd, D_children, List.map_map] at hne ⊢
      exact seqLoop_rel env data n (Corr.of_map env data n (fun x => (D avatar x, l))
        (fun x => sem RW x (.pos l)) fun x hx cons sl h => IHat x hx l cons sl h) cons sl hne
    rw [if_neg h1]
    by_cases h2 : c.op = 2
    · rw [if_pos h2]
      obtain ⟨l, rfl⟩ := hat (by simp [navOp, h2])
      have hd : (D avatar c).operator = .Or := by rw [D_operator, h2]; rfl
      change (evalC env data n (f + 1) l (D avatar c) cons sl).status ≠ revert at hne
      change Rel (evalC env data n (f + 1) l (D avatar c) cons sl) _
      rw [evalC_or env data n f l _ cons sl hd, D_children] at hne ⊢
      refine orLoop_rel env data n l ?_ cons sl hne
      rw [List.map_map]
      exact Corr.of_map env data n (fun x => (D avatar x, l))
        (fun x => sem RW x (.pos l)) fun x hx cons sl h => IHat x hx l cons sl h
    rw [if_neg h2]
    by_cases h5 : c.op = 5 ∧ (c.enc = 3 ∨ c.enc = 5)
    · rw [if_pos h5]
      obtain ⟨l, rfl⟩ := hat (by simp [navOp, h5.1])
      have hd : (D avatar c).operator = .Matches := by rw [D_operator, h5.1]; rfl
      have hcm : (⟨c.enc, 5, c.cv, c.ch⟩ : Cond) = c := by
        rcases c with ⟨e, o, cv, ch⟩; simp only at h5 ⊢; rw [h5.1]
      have hs := hok.2.1 h5.1 h5.2
      change (evalC env data n (f + 1) l (D avatar c) cons sl).status ≠ revert at hne
      change Rel (evalC env data n (f + 1) l (D avatar c) cons sl)
        (matchesT RW c.enc c.cv c.ch (.pos l) sl (toMap cons))
      rw [evalC_matches env data n f l _ cons sl hd, adjust_eq] at hne ⊢
      simp only [matchesT, readWorld, matchLocs, RV.loc, hcm]
      rcases hlc : leadingCheck data (adjust c.enc l) (D avatar c).compValue with _ | s
      · simp only [hlc] at hne ⊢
        rcases hce : childrenE data (adjust c.enc l + (D avatar c).leadingBytes) (D avatar c) with s | _ | locs
        · simp only [hce, Evaluate.violation] at hne
          exact absurd (childrenE_inl hce) hne
        · simp only [hce]
          exact Rel.violation (by decide) (by decide) sl
        · simp only [hce] at hne ⊢
          rw [D_children, List.length_map] at hne ⊢
          by_cases hlen : c.ch.length = locs.length
          · simp only [hlen, ne_eq, not_true_eq_false, ite_false, ite_true, Option.isSome_some,
              Option.getD_some] at hne ⊢
            rw [assign_struct _ _ _ _ hs (by simp [hlen])]
            exact seqLoop_rel env data n (Corr.of_zip avatar env data n (cs0 := c.ch)
              (fun x hx l cons sl h => IHat x hx l cons sl h) c.ch (fun _ h => h) locs) cons sl hne
          · simp only [hlen, ne_eq, not_false_eq_true, ite_true, ite_false, Option.isSome_none]
            exact Rel.violation (by decide) (by decide) sl
      · simp only [hlc, Evaluate.violation] at hne ⊢
        exact Rel.violation (leadingCheck_ne_ok hlc) hne sl
    rw [if_neg h5]
    show Rel _ (readExt avatar env data n c (c.ch.map (sem RW)) v sl (toMap cons))
    rcases opKnown_cases hok.1 with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact absurd h h0
    · exact absurd h h1
    · exact absurd h h2
    · exact empty_rel avatar env data n f c _ v cons sl h
    · -- `Matches` on an array (or another encoding)
      obtain ⟨l, rfl⟩ := hat (by simp [navOp, h])
      have hd : (D avatar c).operator = .Matches := by rw [D_operator, h]; rfl
      change (evalC env data n (f + 1) l (D avatar c) cons sl).status ≠ revert at hne
      change Rel (evalC env data n (f + 1) l (D avatar c) cons sl) _
      unfold readExt; simp only [h]
      unfold marrT arrLocs
      simp only [RV.loc, nodeAt_at]
      rw [evalC_matches env data n f l _ cons sl hd, adjust_eq] at hne ⊢
      rcases hlc : leadingCheck data (adjust c.enc l) (D avatar c).compValue with _ | s
      · simp only [hlc] at hne ⊢
        rcases hce : childrenE data (adjust c.enc l + (D avatar c).leadingBytes) (D avatar c) with s | _ | locs
        · simp only [hce, Evaluate.violation] at hne
          exact absurd (childrenE_inl hce) hne
        · simp only [hce]
          exact Rel.violation (by decide) (by decide) sl
        · simp only [hce] at hne ⊢
          rw [D_children, List.length_map] at hne ⊢
          by_cases hlen : c.ch.length = locs.length
          · simp only [hlen, List.length_map, ne_eq, not_true_eq_false, ite_false] at hne ⊢
            exact seqLoop_rel env data n (Corr.of_zipWith avatar env data n (cs0 := c.ch)
              (fun x hx l cons sl h => IHat x hx l cons sl h) c.ch (fun _ h => h) locs) cons sl hne
          · simp only [hlen, List.length_map, ne_eq, not_false_eq_true, ite_true]
            exact Rel.violation (by decide) (by decide) sl
      · simp only [hlc, Evaluate.violation] at hne ⊢
        exact Rel.violation (leadingCheck_ne_ok hlc) hne sl
    · -- `ArraySome` / `ArrayEvery`
      obtain ⟨l, rfl⟩ := hat (by simp [navOp, h])
      have hd : (D avatar c).operator = if false then .ArrayEvery else .ArraySome := by
        rw [D_operator, h]; rfl
      change (evalC env data n (f + 1) l (D avatar c) cons sl).status ≠ revert at hne
      change Rel (evalC env data n (f + 1) l (D avatar c) cons sl) _
      unfold readExt; simp only [h]
      unfold iterT arrLocs
      simp only [RV.loc, nodeAt_at]
      rw [evalC_iter env data n f l _ cons sl false hd] at hne ⊢
      rcases hce : childrenE data l (D avatar c) with s | _ | locs
      · simp only [hce, Evaluate.violation] at hne
        exact absurd (childrenE_inl hce) hne
      · simp only [hce]
        exact Rel.violation (by decide) (by decide) sl
      · simp only [hce] at hne ⊢
        rw [D_children] at hne ⊢
        rcases hch : c.ch with _ | ⟨x, rest⟩
        · simp only [hch, List.map_nil, hd] at hne ⊢
          by_cases hl : locs = []
          · subst hl
            simp [Evaluate.ok, Evaluate.violation] at hne ⊢
            first
              | exact Rel.ok cons sl
              | exact Rel.violation (by decide) (by decide) sl
          · simp [hl, Evaluate.violation, revert] at hne
        · have hx : x ∈ c.ch := by rw [hch]; simp
          simp only [hch, List.map_cons, hd, reduceCtorEq, List.headD_cons, ite_true, ite_false,
            Bool.false_eq_true, ↓reduceIte] at hne ⊢
          first
            | exact everyLoop_rel env data n (D avatar x) (Corr.of_map env data n (fun l => (D avatar x, l))
                (fun l => sem RW x (.pos l)) fun l _ cons sl h => IHat x hx l cons sl h) cons sl hne
            | exact someLoop_rel env data n (D avatar x) (Corr.of_map env data n (fun l => (D avatar x, l))
                (fun l => sem RW x (.pos l)) fun l _ cons sl h => IHat x hx l cons sl h) cons sl hne
    · -- `ArraySome` / `ArrayEvery`
      obtain ⟨l, rfl⟩ := hat (by simp [navOp, h])
      have hd : (D avatar c).operator = if true then .ArrayEvery else .ArraySome := by
        rw [D_operator, h]; rfl
      change (evalC env data n (f + 1) l (D avatar c) cons sl).status ≠ revert at hne
      change Rel (evalC env data n (f + 1) l (D avatar c) cons sl) _
      unfold readExt; simp only [h]
      unfold iterT arrLocs
      simp only [RV.loc, nodeAt_at]
      rw [evalC_iter env data n f l _ cons sl true hd] at hne ⊢
      rcases hce : childrenE data l (D avatar c) with s | _ | locs
      · simp only [hce, Evaluate.violation] at hne
        exact absurd (childrenE_inl hce) hne
      · simp only [hce]
        exact Rel.violation (by decide) (by decide) sl
      · simp only [hce] at hne ⊢
        rw [D_children] at hne ⊢
        rcases hch : c.ch with _ | ⟨x, rest⟩
        · simp only [hch, List.map_nil, hd] at hne ⊢
          by_cases hl : locs = []
          · subst hl
            simp [Evaluate.ok, Evaluate.violation] at hne ⊢
            first
              | exact Rel.ok cons sl
              | exact Rel.violation (by decide) (by decide) sl
          · simp [hl, Evaluate.violation, revert] at hne
        · have hx : x ∈ c.ch := by rw [hch]; simp
          simp only [hch, List.map_cons, hd, reduceCtorEq, List.headD_cons, ite_true, ite_false,
            Bool.false_eq_true, ↓reduceIte] at hne ⊢
          first
            | exact everyLoop_rel env data n (D avatar x) (Corr.of_map env data n (fun l => (D avatar x, l))
                (fun l => sem RW x (.pos l)) fun l _ cons sl h => IHat x hx l cons sl h) cons sl hne
            | exact someLoop_rel env data n (D avatar x) (Corr.of_map env data n (fun l => (D avatar x, l))
                (fun l => sem RW x (.pos l)) fun l _ cons sl h => IHat x hx l cons sl h) cons sl hne
    · -- `ArrayTailMatches`
      obtain ⟨l, rfl⟩ := hat (by simp [navOp, h])
      have hd : (D avatar c).operator = .ArrayTailMatches := by rw [D_operator, h]; rfl
      change (evalC env data n (f + 1) l (D avatar c) cons sl).status ≠ revert at hne
      change Rel (evalC env data n (f + 1) l (D avatar c) cons sl) _
      unfold readExt; simp only [h]
      unfold tailT arrLocs
      simp only [RV.loc, nodeAt_at]
      rw [evalC_tail env data n f l _ cons sl hd] at hne ⊢
      rcases hce : childrenE data l (D avatar c) with s | _ | locs
      · simp only [hce, Evaluate.violation] at hne
        exact absurd (childrenE_inl hce) hne
      · simp only [hce]
        exact Rel.violation (by decide) (by decide) sl
      · simp only [hce] at hne ⊢
        rw [D_children, List.length_map] at hne ⊢
        simp only [List.length_map]
        by_cases hlen : locs.length < c.ch.length
        · simp only [hlen, ite_true]
          exact Rel.violation (by decide) (by decide) sl
        · simp only [hlen, ite_false] at hne ⊢
          exact seqLoop_rel env data n (Corr.of_zipWith avatar env data n (cs0 := c.ch)
            (fun x hx l cons sl h => IHat x hx l cons sl h) c.ch (fun _ h => h) _) cons sl hne
    · -- Zip: each element is the tuple child at its fields' locations
      obtain ⟨l, rfl⟩ := hat (by simp [navOp, h])
      obtain ⟨t, rest, hch, ht5, ht3, hts⟩ := hok.2.2.2 (by omega)
      have ht : t ∈ c.ch := by rw [hch]; simp
      have hd : (D avatar c).operator = if false then .ZipEvery else .ZipSome := by
        rw [D_operator, h]; rfl
      change (evalC env data n (f + 1) l (D avatar c) cons sl).status ≠ revert at hne
      change Rel (evalC env data n (f + 1) l (D avatar c) cons sl) _
      unfold readExt; simp only [h]
      rw [show nodeAt avatar c (RV.pos l) = D avatar c from rfl]
      unfold zipT
      rw [evalC_zip env data n f l _ cons sl false hd] at hne ⊢
      rw [D_children, hch] at hne ⊢
      simp only [List.map_cons, List.headD_cons] at hne ⊢
      unfold zipF
      rcases hz : zipLocs data n (D avatar c).compValue (D avatar t).children sl with s | ⟨locss, len⟩
      · simp only [hz, Evaluate.violation] at hne ⊢
        have := (zipLocsGo_spec data n _ _ sl 0 none []).1 s (by unfold zipLocs at hz; exact hz)
        exact Rel.violation this hne sl
      · simp only [hz] at hne ⊢
        have hlen := (zipLocsGo_spec data n _ _ sl 0 none []).2 locss len (by unfold zipLocs at hz; exact hz)
        have hyI : ∀ y ∈ t.ch, ∀ l cons sl, (evalC env data n f l (D avatar y) cons sl).status ≠ revert →
            Rel (evalC env data n f l (D avatar y) cons sl) (sem RW y (.pos l) sl (toMap cons)) := by
          intro y hy l cons sl h'
          have h1 := height_mem hy
          have h2 := hhx t ht
          exact IH y (.pos l) (by omega) (AllN.ch _ (hchI t ht) y hy) (fun _ _ h => by cases h)
            (fun _ h => by cases h) cons sl h'
        have hel : ElemCorr env data n f (D avatar t).children locss
            (fun i => sem RW t (.el (locss.map fun ls => ls.getD i 0))) := by
          intro i cons sl hne'
          show Rel _ (sem RW t (RV.el (locss.map fun ls => ls.getD i 0)) sl (toMap cons))
          rw [sem_matchesT_el avatar env data n t ht5 ht3 hts _
            (by rw [List.length_map, hlen, D_children, List.length_map]; simp)]
          rw [D_children] at hne' ⊢
          exact seqLoop_rel env data n (Corr.of_zip avatar env data n (cs0 := t.ch) hyI t.ch
            (fun _ h => h) _) cons sl hne'
        rw [List.range_eq_range']
        exact zipLoop_some_rel env data n _ _ _ hel len 0 cons sl hne
    · -- Zip: each element is the tuple child at its fields' locations
      obtain ⟨l, rfl⟩ := hat (by simp [navOp, h])
      obtain ⟨t, rest, hch, ht5, ht3, hts⟩ := hok.2.2.2 (by omega)
      have ht : t ∈ c.ch := by rw [hch]; simp
      have hd : (D avatar c).operator = if true then .ZipEvery else .ZipSome := by
        rw [D_operator, h]; rfl
      change (evalC env data n (f + 1) l (D avatar c) cons sl).status ≠ revert at hne
      change Rel (evalC env data n (f + 1) l (D avatar c) cons sl) _
      unfold readExt; simp only [h]
      rw [show nodeAt avatar c (RV.pos l) = D avatar c from rfl]
      unfold zipT
      rw [evalC_zip env data n f l _ cons sl true hd] at hne ⊢
      rw [D_children, hch] at hne ⊢
      simp only [List.map_cons, List.headD_cons] at hne ⊢
      unfold zipF
      rcases hz : zipLocs data n (D avatar c).compValue (D avatar t).children sl with s | ⟨locss, len⟩
      · simp only [hz, Evaluate.violation] at hne ⊢
        have := (zipLocsGo_spec data n _ _ sl 0 none []).1 s (by unfold zipLocs at hz; exact hz)
        exact Rel.violation this hne sl
      · simp only [hz] at hne ⊢
        have hlen := (zipLocsGo_spec data n _ _ sl 0 none []).2 locss len (by unfold zipLocs at hz; exact hz)
        have hyI : ∀ y ∈ t.ch, ∀ l cons sl, (evalC env data n f l (D avatar y) cons sl).status ≠ revert →
            Rel (evalC env data n f l (D avatar y) cons sl) (sem RW y (.pos l) sl (toMap cons)) := by
          intro y hy l cons sl h'
          have h1 := height_mem hy
          have h2 := hhx t ht
          exact IH y (.pos l) (by omega) (AllN.ch _ (hchI t ht) y hy) (fun _ _ h => by cases h)
            (fun _ h => by cases h) cons sl h'
        have hel : ElemCorr env data n f (D avatar t).children locss
            (fun i => sem RW t (.el (locss.map fun ls => ls.getD i 0))) := by
          intro i cons sl hne'
          show Rel _ (sem RW t (RV.el (locss.map fun ls => ls.getD i 0)) sl (toMap cons))
          rw [sem_matchesT_el avatar env data n t ht5 ht3 hts _
            (by rw [List.length_map, hlen, D_children, List.length_map]; simp)]
          rw [D_children] at hne' ⊢
          exact seqLoop_rel env data n (Corr.of_zip avatar env data n (cs0 := t.ch) hyI t.ch
            (fun _ h => h) _) cons sl hne'
        rw [List.range_eq_range']
        exact zipLoop_every_rel env data n _ _ _ cons hel len 0 cons sl hne
    · -- `Slice`: the leaf child at the window
      obtain ⟨l, rfl⟩ := hat (by simp [navOp, h])
      have hd : (D avatar c).operator = .Slice := by rw [D_operator, h]; rfl
      change (evalC env data n (f + 1) l (D avatar c) cons sl).status ≠ revert at hne
      change Rel (evalC env data n (f + 1) l (D avatar c) cons sl) _
      unfold readExt; simp only [h]
      rw [show nodeAt avatar c (RV.pos l) = D avatar c from rfl, show (RV.pos l).loc = l from rfl]
      unfold sliceT
      rw [evalC_slice env data n f l _ cons sl hd] at hne ⊢
      rcases hsz : cvAt (D avatar c).compValue 2 with _ | sz
      · simp [hsz, Evaluate.violation] at hne
      · simp only [hsz] at hne ⊢
        by_cases h1' : (D avatar c).inlined = false ∧ l + 32 > data.length
        · simp only [h1', and_self, ↓reduceIte]
          exact Rel.violation (s := sCalldataOverflow) (by decide) (by decide) sl
        · simp only [h1', ↓reduceIte] at hne ⊢
          by_cases h2' : shiftOf (D avatar c).compValue + sz >
              (if (D avatar c).inlined = true then (D avatar c).size else load data l)
          · simp only [h2', ↓reduceIte]
            exact Rel.violation (s := sCalldataOverflow) (by decide) (by decide) sl
          · simp only [h2', ↓reduceIte] at hne ⊢
            rw [D_children] at hne ⊢
            rcases hch : c.ch with _ | ⟨x, rest⟩
            · simp [hch, Evaluate.violation] at hne
            · have hx : x ∈ c.ch := by rw [hch]; simp
              simp only [hch, List.map_cons, List.headD_cons] at hne ⊢
              have hw := hok.2.2.1 h x hx
              exact IH x (.win _ sz) (hhx x hx) (hchI x hx)
                (fun l' sz' he => by cases he; exact hw) (fun _ h => by cases h) cons sl hne
    · exact pluck_rel avatar env data n f c _ v cons sl h hne
    · exact cmp_rel avatar env data n f c _ v cons sl h
    · exact bitmask_rel avatar env data n f c _ v cons sl h
    · exact custom_rel avatar env henv data n f c _ v cons sl h hne
    · exact ratio_rel avatar env data n f c _ v cons sl h hne
    · exact wa_rel avatar env data n f c _ v cons sl h hne
    · exact cwa_rel avatar env data n f c _ v cons sl h hne


end
end Bridge
