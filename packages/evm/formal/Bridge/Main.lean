import Bridge.Leaves

/-!
# Adequacy

`adequacy`: for a tree that fits layout `m`, on calldata that decodes as
`m`, the evaluator transcription and the contract world agree.
-/

namespace Bridge
open DecoderFaithfulness DecoderFaithfulness.Roles Normalize Evaluate

/-! ## Helpers -/

theorem childrenLoop_length (data : Calldata) (loc : Nat) (f : Nat → Condition) :
    ∀ (k i h : Nat) (locs : List Nat), childrenLoop data loc f k i h = some locs → locs.length = k
  | 0, _, _, locs, h => by simp [childrenLoop] at h; simp [← h]
  | k + 1, i, h, locs, hk => by
    simp only [childrenLoop] at hk
    cases hfi : (f i).inlined <;> simp only [hfi, Bool.false_eq_true, ite_false, ite_true] at hk <;>
    · split at hk
      · simp at hk
      · obtain ⟨rest, hrest, rfl⟩ := Option.map_eq_some_iff.1 hk
        simp [childrenLoop_length data loc f k _ _ rest hrest]

theorem assign_struct {V : Type} (d : V) : ∀ (cs : List Cond) (fs : List V) (v : V),
    (∀ x ∈ cs, isStruct x = true) → cs.length ≤ fs.length → assign d cs fs v = cs.zip fs
  | [], _, _, _, _ => by simp [assign]
  | _ :: _, [], _, _, h => by simp at h
  | c :: cs, f :: fs, v, hs, hl => by
    simp only [assign, hs c (by simp), if_true, List.headD_cons, List.tail_cons, List.zip_cons_cons]
    rw [assign_struct d cs fs v (fun x hx => hs x (by simp [hx])) (by simp at hl; omega)]

section
variable (avatar : Bytes) (env : Env) (henv : EnvOk env) (data : Calldata) (n : Nat)
  (P : Nat → Option Condition)

abbrev W := contractWorld avatar env data n P

theorem Corr.of_map {α : Type} (f : Nat) (g : α → Condition × Nat) (h : α → T) (a : α → AF) :
    ∀ (xs : List α), (∀ x ∈ xs, ∀ A B, a x A = some B → ∀ cons sl, Inv data P A sl →
      Good data P (evalC env data n f (g x).2 (g x).1 cons sl) (h x sl (toMap cons)) sl B) →
      Corr env data P n f (xs.map g) (xs.map h) (xs.map a)
  | [], _ => .nil
  | x :: xs, hx => .cons (hx x (by simp)) (Corr.of_map f g h a xs fun y hy => hx y (by simp [hy]))

/-- What a Pluck does to the slots in the world. -/
theorem pluckT_slots (cv : List Nat) (e : Nat) (v : Val') (sl : Slots) (cs : CM) {k0 : Nat}
    (hk : cv.head? = some k0) :
    (∀ j, j ≠ k0 % 256 → (pluckT env data n e cv v sl cs).2.locations j = sl.locations j) ∧
    ((pluckT env data n e cv v sl cs).1.isSome → (pluckT env data n e cv v sl cs).2.locations (k0 % 256) = v.2) ∧
    ((pluckT env data n e cv v sl cs).1 = none → (pluckT env data n e cv v sl cs).2 = sl) := by
  obtain ⟨rest, rfl⟩ : ∃ rest, cv = k0 :: rest := by
    cases cv with
    | nil => simp at hk
    | cons a as => simp at hk; exact ⟨as, by rw [hk]⟩
  have hc : cvAt (toBytes (k0 :: rest)) 0 = some (k0 % 256) := by simp [cvAt, toBytes]
  unfold pluckT
  rw [hc]
  split
  · simp
  · simp at *
  · simp only [Option.some.injEq] at *
    subst_vars
    split
    · simp
    · refine ⟨fun j hj => by simp [writeSlot, hj], fun _ => by simp [writeSlot], fun h => by simp at h⟩

/-- A Pluck run: the slot it writes holds its own location, which decodes as
    the slot's layout. -/
theorem pluck_good {r : Res} {x : Option CM × Slots} {sl : Slots} {A : Nat → Bool} {e : Nat}
    {cv : List Nat} {m : Condition} {l : Nat} {cs : CM} {k0 : Nat}
    (hx : x = pluckT env data n e cv (m, l) sl cs) (hrel : Rel r x) (hk : cv.head? = some k0)
    (hA : Inv data P A sl) (hP : ∀ ma, P (k0 % 256) = some ma → Decodable data ma l) :
    Good data P r x sl (fun j => j == cv.headD 0 % 256 || A j) := by
  obtain ⟨h1, h2, h3⟩ := pluckT_slots env data n cv e (m, l) sl cs hk
  rw [← hx] at h1 h2 h3
  have hhead : cv.headD 0 = k0 := by
    cases cv with
    | nil => simp at hk
    | cons a as => simp at hk; simp [hk]
  rw [hhead]
  have hsl : r.slots = x.2 := hrel.1
  refine ⟨hrel, fun j ma hp hne => ?_, fun hok => ?_⟩
  · rw [hsl] at hne ⊢
    by_cases hj : j = k0 % 256
    · subst hj
      cases hx1 : x.1 with
      | none => rw [h3 hx1] at hne; exact absurd rfl hne
      | some _ => rw [h2 (by rw [hx1]; rfl)]; exact hP ma hp
    · exact absurd (h1 j hj) hne
  · have hsome : x.1.isSome := by
      have := hrel.2; rw [if_pos hok] at this; rw [this]; rfl
    intro j ma hB hp
    rw [hsl]
    by_cases hj : j = k0 % 256
    · subst hj; rw [h2 hsome]; exact hP ma hp
    · rw [h1 j hj]
      simp only [Bool.or_eq_true, beq_iff_eq, hj, false_or] at hB
      exact hA j ma hB hp

/-- The leaf operators other than `Pluck` leave the slots. -/
theorem extW_leaf_slots (e o : Nat) (cv : List Nat) (ss : List (Val' → T)) (v : Val') (sl : Slots)
    (cs : CM) (hops : o = 4 ∨ leafOp o = true) (h14 : o ≠ 14) :
    (extW avatar env data n P e o cv ss v sl cs).2 = sl := by
  unfold leafOp at hops
  simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq] at hops
  have : o = 4 ∨ o = 15 ∨ o = 16 ∨ o = 17 ∨ o = 18 ∨ o = 19 ∨ o = 20 ∨ o = 21 ∨ o = 22 ∨ o = 23 ∨
      o = 28 ∨ o = 30 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- A run that changes no slots and whose node writes none. -/
theorem Good.of_rel_keeps {r : Res} {x : Option CM × Slots} {sl : Slots} {A : Nat → Bool}
    (h : Rel r x) (hk : x.2 = sl) (hA : Inv data P A sl) : Good data P r x sl A :=
  Good.of_keeps h (by rw [h.1, hk]) hA

/-- A failing run that changes no slots. -/
theorem Good.of_fail {r : Res} {x : Option CM × Slots} {sl : Slots} {B : Nat → Bool}
    (h : Rel r x) (hk : x.2 = sl) (hn : x.1 = none) : Good data P r x sl B := by
  refine ⟨h, by rw [h.1, hk]; exact WV.refl data P sl, fun hok => ?_⟩
  have := h.2; rw [if_pos hok, hn] at this; cases this

theorem Fits.layEq {x : Cond} {d m : Condition} (h : Fits avatar P x d m) (hs : isStruct x = true) :
    LayEq d m := by
  cases h with
  | pass _ _ _ hl _ _ _ => exact hl
  | ns hns _ _ => rw [hns] at hs; exact absurd hs (by simp)
  | logical _ _ _ _ hl _ _ => exact hl
  | tup _ _ _ _ hl _ _ _ _ _ => exact hl
  | arr _ _ _ _ hl _ _ _ _ => exact hl
  | slice _ _ _ hl _ _ _ _ _ => exact hl
  | leaf _ _ _ ht _ _ _ _ _ _ _ _ _ => exact ht.layEq
  | varAbi _ _ _ _ hl _ _ _ _ _ => exact hl
  | varDyn _ _ hl _ => exact hl
  | zip h _ _ _ _ _ _ _ _ _ _ _ =>
    rw [isStruct_eq] at hs
    have : (x.op == 1 || x.op == 2) = false := by rcases h with h | h <;> simp [h]
    rw [this] at hs; simp_all
  | zipLogical _ _ hns => rw [hns] at hs; cases hs

theorem cvOf_plain {c : Cond} (h15 : c.op ≠ 15) (h16 : c.op ≠ 16) (h5 : c.enc ≠ 5) :
    cvOf avatar c = toBytes c.cv := by
  unfold cvOf; simp [h15, h16, h5]

theorem sem_ext {c : Cond} (h0 : c.op ≠ 0) (h1 : c.op ≠ 1) (h2 : c.op ≠ 2) (h5 : c.op ≠ 5)
    (v : Val') :
    sem (W avatar env data n P) c v = extW avatar env data n P c.enc c.op c.cv (c.ch.map (sem (W avatar env data n P))) v := by
  rw [sem_eq]
  simp only [h0, h1, h2, ite_false]
  rw [ite_neg' (by omega)]
  rfl

include henv in
/-- The operators that read one value, given how the node and the layout
    agree. -/
theorem ext_rel (c : Cond) (d m : Condition) (f l : Nat) (cons : List Consumption) (sl : Slots)
    (ss : List (Val' → T))
    (hop : d.operator = opN c.op) (hops : c.op = 4 ∨ leafOp c.op = true) (henc : c.enc ≠ 5)
    (hin : input data l d = inputAt data c.enc m l)
    (hlay : c.op = 21 → d.inlined = m.inlined ∧ d.size = m.size)
    (hcs : c.op = 22 → (if d.size ≠ 0 then d.size else size data l d) = customSize data c.enc m l)
    (hcv : d.compValue = cvOf avatar c)
    (hinl : c.op = 16 → (if c.enc = 0 ∨ c.enc = 6 then true else m.inlined) = isInl c)
    (hk : c.op = 14 → ∃ k ∈ c.cv.head?, k % 256 < n) :
    Rel (evalC env data n (f + 1) l d cons sl)
      (extW avatar env data n P c.enc c.op c.cv ss (m, l) sl (toMap cons)) := by
  rcases c with ⟨e, o, cv, ch⟩
  simp only at hop hops henc hin hlay hcs hcv hinl hk ⊢
  rcases hops with rfl | hops
  · exact empty_rel avatar env data n P f l d m e cv ss cons sl (by rw [hop]; rfl)
  unfold leafOp at hops
  simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq] at hops
  have hplain : o ≠ 15 → o ≠ 16 → d.compValue = toBytes cv := fun a b => by
    rw [hcv]; exact cvOf_plain avatar a b henc
  rcases hops with ((rfl | ⟨h1, h2⟩) | rfl) | rfl
  · exact pluck_rel avatar env data n P f l d m e cv ss cons sl (by rw [hop]; rfl)
      (hplain (by decide) (by decide)) hin (hk rfl)
  · have : o = 15 ∨ o = 16 ∨ o = 17 ∨ o = 18 ∨ o = 19 ∨ o = 20 ∨ o = 21 ∨ o = 22 ∨ o = 23 := by
      omega
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact cmp_rel avatar env data n P f l d m e 15 cv ss cons sl (by decide) hop hin
        (by rw [hcv]; unfold cvOf cmpValue; simp)
    · refine cmp_rel avatar env data n P f l d m e 16 cv ss cons sl (by decide) hop hin ?_
      rw [hcv]
      have hi := hinl rfl
      unfold cvOf cmpValue
      simp only [henc, ite_false]
      by_cases he : e = 0 ∨ e = 6
      · simp only [he, ite_true] at hi
        simp [he, ← hi]
      · simp only [he, ite_false] at hi
        simp [he, hi]
    all_goals first
      | exact cmp_rel avatar env data n P f l d m e _ cv ss cons sl (by decide) hop hin
          (by rw [hplain (by decide) (by decide)]; unfold cmpValue; simp)
      | exact bitmask_rel avatar env data n P f l d m e cv ss cons sl (by rw [hop]; rfl)
          (hplain (by decide) (by decide)) (hlay rfl)
      | exact custom_rel avatar env henv data n P f l d m e cv ss cons sl (by rw [hop]; rfl)
          (hplain (by decide) (by decide)) (hcs rfl)
      | exact ratio_rel avatar env henv data n P f l d m e cv ss cons sl (by rw [hop]; rfl)
          (hplain (by decide) (by decide))
  · exact wa_rel avatar env henv data n P f l d m e cv ss cons sl (by rw [hop]; rfl)
      (hplain (by decide) (by decide)) hin
  · exact cwa_rel avatar env henv data n P f l d m e cv ss cons sl (by rw [hop]; rfl)
      (hplain (by decide) (by decide))

theorem fuel_succ {c : Cond} {fuel : Nat} (h : height c < fuel) : ∃ f, fuel = f + 1 ∧ height c ≤ f :=
  ⟨fuel - 1, by omega, by omega⟩

theorem height_pos (c : Cond) : 0 < height c := by rcases c; simp [height]

theorem evalC_pass (f l : Nat) (d : Condition) (cons : List Consumption) (sl : Slots)
    (hd : d.operator = .Pass) : evalC env data n (f + 1) l d cons sl = Evaluate.ok cons sl := by
  rw [evalC, hd]

theorem evalC_and (f l : Nat) (d : Condition) (cons : List Consumption) (sl : Slots)
    (hd : d.operator = .And) :
    evalC env data n (f + 1) l d cons sl = seqLoop env data n f (d.children.map (·, l)) cons sl := by
  rw [evalC, hd]

theorem evalC_or (f l : Nat) (d : Condition) (cons : List Consumption) (sl : Slots)
    (hd : d.operator = .Or) :
    evalC env data n (f + 1) l d cons sl = orLoop env data n f d.children l cons sl := by
  rw [evalC, hd]

theorem D_encoding_ns {c : Cond} (he : c.enc = 0 ∨ c.enc = 6) : (D avatar c).encoding = .None := by
  rw [D_encoding]; rcases he with h | h <;> simp [h, encN, ConditionPacking.encOf?]

theorem isInl_leaf {c : Cond} (he : c.enc = 0 ∨ c.enc = 6) (hch : c.ch = []) : isInl c = true := by
  rcases c with ⟨e, o, cv, ch⟩
  simp only at he hch; subst hch
  rcases he with rfl | rfl <;> rfl

theorem D_size_leaf {c : Cond} (he : c.enc = 0 ∨ c.enc = 6) (hch : c.ch = []) : (D avatar c).size = 0 := by
  unfold D
  rw [annotate_size, toRoles_eq, hch]
  rcases he with h | h <;> simp [h, encN, ConditionPacking.encOf?, isInlined, isInlinedAll,
    inlinedSize, inlinedSizeLoop]

include henv in
/-- Non-structural subtrees read no calldata location: any layout fits. -/
theorem ns_adequacy : ∀ {c : Cond}, NsOk c → ∀ (m : Condition) (fuel l : Nat) (cons : List Consumption)
    (sl : Slots) (A B : Nat → Bool), (∀ k ∈ plucks c, P k = none) → height c < fuel → CvOk n c →
    za c A = some B → Inv data P A sl →
    Good data P (evalC env data n fuel l (D avatar c) cons sl)
      (sem (W avatar env data n P) c (m, l) sl (toMap cons)) sl B := by
  intro c hns
  induction hns with
  | @leaf c he hch hop =>
    intro m fuel l cons sl A B hpl hh hcv hza hA
    obtain ⟨f, rfl, -⟩ := fuel_succ hh
    unfold nsOp at hop
    simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq] at hop
    by_cases h0 : c.op = 0
    · rw [za_plain (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega)] at hza
      cases hza
      rw [evalC_pass env data n f l _ cons sl (by rw [D_operator, h0]; rfl), sem_eq, ite_pos' h0]
      exact Good.ok data P cons hA
    have hops : c.op = 4 ∨ leafOp c.op = true := by
      unfold leafOp; simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq]
      omega
    rw [sem_ext avatar env data n P h0 (by omega) (by omega) (by omega)]
    have hcv' := hcv
    rw [cvOk_eq] at hcv
    have hDenc := D_encoding_ns avatar he
    have hrel := ext_rel avatar env henv data n P c (D avatar c) m f l cons sl
      (c.ch.map (sem (W avatar env data n P))) (D_operator avatar c) hops
      (by rcases he with h | h <;> omega) (by unfold input inputAt; simp [hDenc, he]) (by intro h21; omega)
      (by
        intro _
        rw [D_size_leaf avatar he hch, size_eq, hDenc, D_children, hch]
        unfold customSize
        simp [he, sizeNone])
      (D_compValue avatar c) (by intro _; simp [he, isInl_leaf he hch]) hcv.2.2.1
    by_cases h14 : c.op = 14
    · obtain ⟨k0, hk0, -⟩ := hcv.2.2.1 h14
      rw [za_eq, if_pos h14] at hza
      cases hza
      have hhd : c.cv.headD 0 = k0 := by
        cases h : c.cv with
        | nil => simp [h] at hk0
        | cons a as => simp [h] at hk0; simp [hk0]
      have hpk : P (k0 % 256) = none := hpl _ (by rw [plucks_eq, if_pos h14, hhd]; simp)
      have hx : extW avatar env data n P c.enc c.op c.cv (c.ch.map (sem (W avatar env data n P))) (m, l) =
          pluckT env data n c.enc c.cv (m, l) := by rw [h14]; rfl
      rw [hx] at hrel ⊢
      exact pluck_good env data n P rfl hrel hk0 hA fun ma h => by rw [hpk] at h; cases h
    · rw [za_plain h14 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega)] at hza
      cases hza
      exact Good.of_rel_keeps data P hrel
        (extW_leaf_slots avatar env data n P _ _ _ _ _ _ _ hops h14) hA
  | @logical c hop _ hall ih =>
    intro m fuel l cons sl A B hpl hh hcv hza hA
    obtain ⟨f, rfl, hf⟩ := fuel_succ hh
    have hcorr : Corr env data P n f (c.ch.map fun x => (D avatar x, l))
        (c.ch.map fun x => sem (W avatar env data n P) x (m, l)) (c.ch.map za) :=
      Corr.of_map env data n P f _ _ _ c.ch fun x hx A B hB cons sl hA =>
        ih x hx m f l cons sl A B (fun k hk => hpl k (plucks_child hx hk))
          (by have := height_mem hx; omega) (hcv.child hx) hB hA
    rcases hop with h1 | h2
    · rw [evalC_and env data n f l _ cons sl (by rw [D_operator, h1]; rfl), sem_eq,
        ite_neg' (by omega), ite_pos' h1, D_children, List.map_map]
      rw [za_eq, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
        if_pos (by omega), zaSeq_eq] at hza
      exact seqLoop_rel env data P _ _ _ hcorr A B hza cons sl hA
    · rw [evalC_or env data n f l _ cons sl (by rw [D_operator, h2]; rfl), sem_eq,
        ite_neg' (by omega), ite_neg' (by omega), ite_pos' h2, D_children]
      rw [za_eq, if_neg (by omega), if_neg (by omega), if_pos h2, zaOr_eq] at hza
      refine orLoop_rel env data P l ?_ A B hza cons sl hA
      rw [List.map_map]; exact hcorr

theorem evalC_matches (f l : Nat) (d : Condition) (cons : List Consumption) (sl : Slots)
    (hd : d.operator = .Matches) :
    evalC env data n (f + 1) l d cons sl =
      match leadingCheck data (if l > 0 ∧ d.encoding = .AbiEncoded then l + 32 else l) d.compValue with
      | some s => violation s sl
      | none =>
        match childrenE data ((if l > 0 ∧ d.encoding = .AbiEncoded then l + 32 else l) + d.leadingBytes) d with
        | .inl s => violation s sl
        | .inr none => violation sCalldataOverflow sl
        | .inr (some locs) =>
          if d.children.length ≠ locs.length then violation sParameterNotAMatch sl
          else seqLoop env data n f (d.children.zip locs) cons sl := by
  rw [evalC, hd]; rfl

theorem Corr.of_idx (f : Nat) : ∀ (ps : List (Condition × Nat)) (ts : List T) (αs : List AF),
    ps.length = ts.length → ps.length = αs.length →
    (∀ i (h1 : i < ps.length) (h2 : i < ts.length) (h3 : i < αs.length), ∀ A B, αs[i] A = some B →
      ∀ cons sl, Inv data P A sl →
      Good data P (evalC env data n f ps[i].2 ps[i].1 cons sl) (ts[i] sl (toMap cons)) sl B) →
    Corr env data P n f ps ts αs
  | [], [], [], _, _, _ => .nil
  | [], _ :: _, _, h, _, _ => by simp at h
  | _ :: _, [], _, h, _, _ => by simp at h
  | [], [], _ :: _, _, h, _ => by simp at h
  | _ :: _, _ :: _, [], _, h, _ => by simp at h
  | p :: ps, t :: ts, α :: αs, h, h', hi => .cons (hi 0 (by simp) (by simp) (by simp))
      (Corr.of_idx f ps ts αs (by simpa using h) (by simpa using h')
        fun i h1 h2 h3 => hi (i + 1) (by simpa using h1) (by simpa using h2) (by simpa using h3))

theorem leadingCheck_cases (data : Calldata) (loc : Nat) (cv : Bytes) (h : cv.length ≤ 32) :
    leadingCheck data loc cv = none ∨ leadingCheck data loc cv = some sCalldataOverflow ∨
      leadingCheck data loc cv = some sLeadingBytesNotAMatch := by
  unfold leadingCheck
  repeat' split
  all_goals first | (left; rfl) | (right; left; rfl) | (right; right; rfl) | omega

theorem encN_ne_ether {e : Nat} (h : e = 3 ∨ e = 4 ∨ e = 5 ∨ e = 1 ∨ e = 2) : encN e ≠ .EtherValue := by
  rcases h with rfl | rfl | rfl | rfl | rfl <;> decide

theorem D_encoding_of {c : Cond} (h : c.enc = 3 ∨ c.enc = 4 ∨ c.enc = 5 ∨ c.enc = 1 ∨ c.enc = 2) :
    (D avatar c).encoding = encN c.enc := by
  rw [D_encoding, if_neg (encN_ne_ether h)]

theorem prefixOf_cvOf {c : Cond} (h5 : c.op = 5) (he : c.enc = 3 ∨ c.enc = 5) :
    cvOf avatar c = prefixOf c.enc c.cv := by
  unfold cvOf prefixOf
  rcases he with h | h
  · simp [h, h5]
  · simp only [h5, h, ite_true]
    simp
    split
    · rename_i hc; simp [hc, toBytes]
    · rfl

theorem childrenE_plain (data : Calldata) (L : Nat) (d : Condition) (h : d.encoding ≠ .Array) :
    childrenE data L d = .inr (children data L d) := by
  unfold childrenE allocPanics; simp [h]

theorem children_plain (data : Calldata) (L : Nat) (d : Condition) (h : d.encoding ≠ .Array) :
    children data L d = childrenLoop data L (fun i => d.children.getD i default) d.children.length 0 0 := by
  unfold children; simp [h]

theorem decodeAt_some {data : Calldata} {e : Nat} {m : Condition} {l : Nat} {locs : List Nat}
    (hm : m.encoding ≠ .Array) (h : decodeAt data e m l = some locs) :
    children data (adjust e l + m.leadingBytes) m = some locs := by
  unfold decodeAt at h
  rw [childrenE_plain data _ m hm] at h
  split at h
  · rename_i heq; simp only [Sum.inr.injEq] at heq; rw [heq]; simpa using h
  · simp at h

include henv in
theorem tup_rel {c : Cond} {m : Condition} (f l : Nat) (cons : List Consumption) (sl : Slots)
    (h5 : c.op = 5) (he : c.enc = 3 ∨ c.enc = 5) (hm : (D avatar c).encoding = m.encoding)
    (hlb : (D avatar c).leadingBytes = m.leadingBytes)
    (hs : ∀ x ∈ c.ch, isStruct x = true) (hk : c.ch.length ≤ m.children.length)
    (hlay : ∀ i (h : i < c.ch.length), LayEq (D avatar c.ch[i]) (m.children.getD i default))
    (ih : ∀ i (h : i < c.ch.length) (l' : Nat), Decodable data (m.children.getD i default) l' →
      ∀ A B, za c.ch[i] A = some B → ∀ cons sl, Inv data P A sl →
      Good data P (evalC env data n f l' (D avatar c.ch[i]) cons sl)
        (sem (W avatar env data n P) c.ch[i] (m.children.getD i default, l') sl (toMap cons)) sl B)
    (hcv : (prefixOf c.enc c.cv).length ≤ 32) (hdec : Decodable data m l)
    {A B : Nat → Bool} (hza : zaSeq c.ch A = some B) (hA : Inv data P A sl) :
    Good data P (evalC env data n (f + 1) l (D avatar c) cons sl)
      (sem (W avatar env data n P) c (m, l) sl (toMap cons)) sl B := by
  have hDe := D_encoding_of avatar (c := c) (by omega)
  have hsem : sem (W avatar env data n P) c (m, l) = matchesT (W avatar env data n P) c.enc c.cv c.ch (m, l) := by
    have h0 : ¬ c.op = 0 := by omega
    have h1 : ¬ c.op = 1 := by omega
    have h2 : ¬ c.op = 2 := by omega
    rw [sem_eq, ite_neg' h0, ite_neg' h1, ite_neg' h2, ite_pos' ⟨h5, he⟩]
  rw [evalC_matches env data n f l _ cons sl (by rw [D_operator, h5]; rfl), hsem]
  unfold matchesT
  have hadj : (if l > 0 ∧ (D avatar c).encoding = .AbiEncoded then l + 32 else l) = adjust c.enc l := by
    rw [hDe]; unfold adjust
    rcases he with h | h <;> simp [h, encN, ConditionPacking.encOf?]
  have hnarr : m.encoding ≠ .Array := by
    rw [← hm, hDe]; rcases he with h | h <;> simp [h, encN, ConditionPacking.encOf?]
  have hnarrD : (D avatar c).encoding ≠ .Array := by rw [hm]; exact hnarr
  have hndyn : m.encoding ≠ .Dynamic := by
    rw [← hm, hDe]; rcases he with h | h <;> simp [h, encN, ConditionPacking.encOf?]
  have hlayAt : layAt data c.enc (m, l) = m := layAt_of_ne c.enc l hndyn
  have hz : isZipEl m = false := isZipEl_of_ne (by
    rw [← hm, hDe]; rcases he with h | h <;> simp [h, encN, ConditionPacking.encOf?])
  rw [hadj, D_compValue, prefixOf_cvOf avatar h5 he]
  show Good data P _ (if (isZipEl m || ((leadingCheck data (adjust c.enc l) (prefixOf c.enc c.cv)).isNone &&
      (decodeAt data c.enc (layAt data c.enc (m, l)) l).isSome)) = true then _ else _) sl B
  rw [hlayAt, hz, Bool.false_or]
  rcases leadingCheck_cases data (adjust c.enc l) (prefixOf c.enc c.cv) hcv with h | h | h
  · rw [h]
    simp only [Option.isNone_none, Bool.true_and]
    cases hdec with
    | leaf h1 h2 _ =>
      exfalso; rw [← hm, hDe] at h1 h2; rcases he with h | h <;> simp_all [encN, ConditionPacking.encOf?]
    | arr _ h1 _ _ => exact absurd h1 hnarr
    | var hv _ =>
      exfalso; unfold isVarLay at hv; simp at hv; exact hndyn hv.2
    | tup locsM _ hdl hdch =>
      have hde : decodeAt data c.enc m l = some locsM := by
        have : (if m.encoding = .AbiEncoded then 5 else 3) = c.enc := by
          rw [← hm, hDe]; rcases he with h | h <;> simp [h, encN, ConditionPacking.encOf?]
        unfold decodeL at hdl; rw [this] at hdl; exact hdl
      have hcm := decodeAt_some hnarr hde
      rw [children_plain data _ m hnarr] at hcm
      have hK := childrenLoop_length data _ _ _ _ _ _ hcm
      have hpre := childrenLoop_prefix data _ _ c.ch.length m.children.length 0 0 locsM hk hcm
      have hDch := D_children avatar c
      have hcd : children data (adjust c.enc l + m.leadingBytes) (D avatar c) =
          some (locsM.take c.ch.length) := by
        rw [children_plain data _ _ hnarrD, hDch, List.length_map, ← hpre]
        apply childrenLoop_congr
        intro j _ hj
        simp only [Nat.zero_add] at hj
        have := hlay j hj
        simpa [List.getElem?_map, List.getElem?_eq_getElem hj, List.getD_eq_getElem?_getD] using this
      rw [hlb, childrenE_plain data _ _ hnarrD, hcd, hde]
      simp only [Option.isSome_some, ite_true]
      have hlen : (D avatar c).children.length = (locsM.take c.ch.length).length := by
        rw [hDch]; simp; omega
      rw [if_neg (by rw [hlen]; exact fun h => h rfl)]
      have hfields : (W avatar env data n P).fields c.enc (m, l) = m.children.zip locsM := by
        show (if isZipEl m then zipElFields m else match decodeAt data c.enc (layAt data c.enc (m, l)) l with
          | some locs => (layAt data c.enc (m, l)).children.zip locs
          | none => []) = _
        rw [hz, if_neg (by decide), hlayAt, hde]
      rw [hfields, assign_struct _ c.ch _ _ hs (by simp; omega)]
      rw [zaSeq_eq] at hza
      refine seqLoop_rel env data P _ _ (c.ch.map za)
        (Corr.of_idx env data n P f _ _ _ (by simp [hDch]; omega) (by simp [hDch]; omega) ?_) A B hza cons sl hA
      intro i h1 h2 h3 A' B' hB' cons' sl' hA'
      have hi : i < c.ch.length := by simp at h1; omega
      have hiK : i < locsM.length := by omega
      have hgm : m.children.getD i default = m.children[i]'(by omega) := by
        simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show i < m.children.length by omega)]
      have := ih i hi locsM[i] (hdch i hiK) A' B' (by simpa using hB') cons' sl' hA'
      rw [hgm] at this
      simpa [hDch] using this
  · rw [h]; exact Good.violation data P (by decide) (by decide) sl B
  · rw [h]; exact Good.violation data P (by decide) (by decide) sl B

theorem childrenE_arr (data : Calldata) (l : Nat) (d m : Condition) (hd : d.encoding = .Array)
    (hm : m.encoding = .Array) (ht : LayEq (d.children.headD default) (m.children.headD default)) :
    childrenE data l d = childrenE data l m := by
  unfold childrenE allocPanics children
  simp only [hd, hm, ite_true]
  split
  · rfl
  · congr 2
    exact childrenLoop_congr data _ _ _ _ 0 0 fun _ _ _ => ht

theorem evalC_iter (f l : Nat) (d : Condition) (cons : List Consumption) (sl : Slots)
    (every : Bool) (hd : d.operator = if every then .ArrayEvery else .ArraySome) :
    evalC env data n (f + 1) l d cons sl =
      match childrenE data l d with
      | .inl s => violation s sl
      | .inr none => violation sCalldataOverflow sl
      | .inr (some locs) =>
        match d.children with
        | [] => if locs = [] then
                  (if d.operator = .ArrayEvery then Evaluate.ok cons sl
                   else violation sNoArrayElementPasses sl)
                else violation revert sl
        | ch :: _ =>
          if d.operator = .ArrayEvery then everyLoop env data n f ch locs cons sl
          else someLoop env data n f ch locs cons sl := by
  rw [evalC]
  cases every <;> simp only [hd, Bool.false_eq_true, ite_false, ite_true] <;> rfl

theorem evalC_tail (f l : Nat) (d : Condition) (cons : List Consumption) (sl : Slots)
    (hd : d.operator = .ArrayTailMatches) :
    evalC env data n (f + 1) l d cons sl =
      match childrenE data l d with
      | .inl s => violation s sl
      | .inr none => violation sCalldataOverflow sl
      | .inr (some locs) =>
        if locs.length < d.children.length then violation sParameterNotAMatch sl
        else seqLoop env data n f (d.children.zip (locs.drop (locs.length - d.children.length)))
          cons sl := by
  rw [evalC, hd]; rfl

theorem evalC_slice (f l : Nat) (d : Condition) (cons : List Consumption) (sl : Slots)
    (hd : d.operator = .Slice) :
    evalC env data n (f + 1) l d cons sl =
      match cvAt d.compValue 2 with
      | none => violation revert sl
      | some sz =>
        if d.inlined = false ∧ l + 32 > data.length then violation sCalldataOverflow sl
        else
          if shiftOf d.compValue + sz > (if d.inlined then d.size else load data l) then
            violation sCalldataOverflow sl
          else
            match d.children with
            | [] => violation revert sl
            | ch :: _ =>
              evalC env data n f (l + (if d.inlined then 0 else 32) + shiftOf d.compValue)
                (ch.withSize sz) cons sl := by
  rw [evalC, hd]; rfl

theorem sem_ext' {c : Cond} (h0 : c.op ≠ 0) (h1 : c.op ≠ 1) (h2 : c.op ≠ 2)
    (h5 : ¬(c.op = 5 ∧ (c.enc = 3 ∨ c.enc = 5))) (v : Val') :
    sem (W avatar env data n P) c v =
      extW avatar env data n P c.enc c.op c.cv (c.ch.map (sem (W avatar env data n P))) v := by
  rw [sem_eq]
  simp only [h0, h1, h2, ite_false]
  rw [ite_neg' h5]
  rfl

theorem D_enc_arr {c : Cond} (he : c.enc = 4) : (D avatar c).encoding = .Array := by
  rw [D_encoding_of avatar (by omega), he]; rfl

theorem Decodable.arr_locs {data : Calldata} {m : Condition} {l : Nat} (hm : m.encoding = .Array)
    (h : Decodable data m l) :
    ∃ locs, childrenE data l m = .inr (some locs) ∧ ∀ l' ∈ locs, Decodable data (tmpl m) l' := by
  cases h with
  | leaf _ _ h3 => exact absurd hm h3
  | tup _ h1 _ _ => rcases h1 with h1 | h1 <;> rw [hm] at h1 <;> exact absurd h1 (by decide)
  | arr locs _ h2 h3 => exact ⟨locs, h2, h3⟩
  | var hv _ => unfold isVarLay at hv; simp [hm] at hv

include henv in
theorem iter_rel {c : Cond} {m : Condition} (f l : Nat) (cons : List Consumption) (sl : Slots)
    (every : Bool) (hop : c.op = if every then 7 else 6) (he : c.enc = 4) (hm : m.encoding = .Array)
    {x : Cond} {xs : List Cond} (hch : c.ch = x :: xs) (hlx : LayEq (D avatar x) (tmpl m))
    (ih : ∀ l', Decodable data (tmpl m) l' → ∀ A B, za x A = some B → ∀ cons sl, Inv data P A sl →
      Good data P (evalC env data n f l' (D avatar x) cons sl)
        (sem (W avatar env data n P) x (tmpl m, l') sl (toMap cons)) sl B)
    (hdec : Decodable data m l) {A B : Nat → Bool} (hzx : za x A = some B) (hA : Inv data P A sl) :
    Good data P (evalC env data n (f + 1) l (D avatar c) cons sl)
      (sem (W avatar env data n P) c (m, l) sl (toMap cons)) sl (if every then A else B) := by
  have hDop : (D avatar c).operator = if every then .ArrayEvery else .ArraySome := by
    rw [D_operator, hop]; cases every <;> rfl
  have hDch : (D avatar c).children = D avatar x :: xs.map (D avatar) := by
    rw [D_children, hch]; rfl
  rw [evalC_iter env data n f l _ cons sl every hDop]
  rw [sem_ext' avatar env data n P (by cases every <;> simp_all) (by cases every <;> simp_all)
    (by cases every <;> simp_all) (by cases every <;> simp_all)]
  obtain ⟨locs, hlocs, hdl⟩ := hdec.arr_locs hm
  have hce : childrenE data l (D avatar c) = .inr (some locs) := by
    rw [childrenE_arr data l _ m (D_enc_arr avatar he) hm (by rw [hDch]; exact hlx), hlocs]
  rw [hce, hDch]
  simp only
  have hcorr : Corr env data P n f (locs.map (D avatar x, ·))
      (locs.map fun l' => sem (W avatar env data n P) x (tmpl m, l')) (locs.map fun _ => za x) :=
    Corr.of_map env data n P f _ _ _ locs fun l' hl' A B hB cons sl hA =>
      ih l' (hdl l' hl') A B hB cons sl hA
  have hhead : (c.ch.map (sem (W avatar env data n P))).headD passK = sem (W avatar env data n P) x := by
    rw [hch]; rfl
  cases every
  · simp only [hop, ite_false] at hDop ⊢
    rw [hDop]
    show Good data P _ (iterT data false c.enc _ (m, l) sl (toMap cons)) sl _
    unfold iterT
    rw [he, hhead, hlocs]
    simp only [ne_eq, not_true_eq_false, ite_false, Bool.false_eq_true]
    exact someLoop_rel env data P (D avatar x) (za x) hcorr A B hzx cons sl hA
  · simp only [hop, ite_true] at hDop ⊢
    rw [hDop]
    show Good data P _ (iterT data true c.enc _ (m, l) sl (toMap cons)) sl _
    unfold iterT
    rw [he, hhead, hlocs]
    simp only [ne_eq, not_true_eq_false, ite_false, ite_true]
    exact everyLoop_rel env data P (D avatar x) (za x) hcorr A B hzx cons sl hA

include henv in
theorem tail_rel {c : Cond} {m : Condition} (f l : Nat) (cons : List Consumption) (sl : Slots)
    (hop : c.op = 8) (he : c.enc = 4) (hm : m.encoding = .Array) (hne : c.ch ≠ [])
    (hlx : ∀ x ∈ c.ch, LayEq (D avatar x) (tmpl m))
    (ih : ∀ x ∈ c.ch, ∀ l', Decodable data (tmpl m) l' → ∀ A B, za x A = some B → ∀ cons sl,
      Inv data P A sl → Good data P (evalC env data n f l' (D avatar x) cons sl)
        (sem (W avatar env data n P) x (tmpl m, l') sl (toMap cons)) sl B)
    (hdec : Decodable data m l)
    {A B : Nat → Bool} (hza : zaSeq c.ch A = some B) (hA : Inv data P A sl) :
    Good data P (evalC env data n (f + 1) l (D avatar c) cons sl)
      (sem (W avatar env data n P) c (m, l) sl (toMap cons)) sl B := by
  obtain ⟨x, xs, hch⟩ : ∃ x xs, c.ch = x :: xs := by
    cases h : c.ch with
    | nil => exact absurd h hne
    | cons x xs => exact ⟨x, xs, rfl⟩
  have hDch := D_children avatar c
  rw [evalC_tail env data n f l _ cons sl (by rw [D_operator, hop]; rfl)]
  rw [sem_ext' avatar env data n P (by omega) (by omega) (by omega) (by omega)]
  obtain ⟨locs, hlocs, hdl⟩ := hdec.arr_locs hm
  have hce : childrenE data l (D avatar c) = .inr (some locs) := by
    rw [childrenE_arr data l _ m (D_enc_arr avatar he) hm
      (by rw [hDch, hch]; exact hlx x (by rw [hch]; simp)), hlocs]
  rw [hce, hop]
  show Good data P _ (tailT data c.enc _ (m, l) sl (toMap cons)) sl B
  unfold tailT
  rw [he, hlocs]
  simp only [ne_eq, not_true_eq_false, ite_false, List.length_map, hDch]
  split
  · exact Good.violation data P (by decide) (by decide) sl B
  · rename_i hlt
    rw [zaSeq_eq] at hza
    refine seqLoop_rel env data P _ _ (c.ch.map za)
      (Corr.of_idx env data n P f _ _ _ (by simp) (by simp; omega) ?_) A B hza cons sl hA
    intro i h1 h2 h3 A' B' hB' cons' sl' hA'
    have hi : i < c.ch.length := by simp at h1; omega
    have hmem : c.ch[i] ∈ c.ch := List.getElem_mem hi
    have hj : locs.length - c.ch.length + i < locs.length := by omega
    have hd := hdl (locs[locs.length - c.ch.length + i]) (List.getElem_mem hj)
    have := ih c.ch[i] hmem _ hd A' B' (by simpa using hB') cons' sl' hA'
    simpa [List.getElem_zip, List.getElem_drop, List.getElem_zipWith, List.getElem_map] using this

include henv in
theorem marr_rel {c : Cond} {m : Condition} (f l : Nat) (cons : List Consumption) (sl : Slots)
    (hop : c.op = 5) (he : c.enc = 4) (hm : m.encoding = .Array) (hne : c.ch ≠ [])
    (hlx : ∀ x ∈ c.ch, LayEq (D avatar x) (tmpl m))
    (ih : ∀ x ∈ c.ch, ∀ l', Decodable data (tmpl m) l' → ∀ A B, za x A = some B → ∀ cons sl,
      Inv data P A sl → Good data P (evalC env data n f l' (D avatar x) cons sl)
        (sem (W avatar env data n P) x (tmpl m, l') sl (toMap cons)) sl B)
    (hcv : (prefixOf c.enc c.cv).length ≤ 32) (hdec : Decodable data m l)
    {A B : Nat → Bool} (hza : zaSeq c.ch A = some B) (hA : Inv data P A sl) :
    Good data P (evalC env data n (f + 1) l (D avatar c) cons sl)
      (sem (W avatar env data n P) c (m, l) sl (toMap cons)) sl B := by
  obtain ⟨x, xs, hch⟩ : ∃ x xs, c.ch = x :: xs := by
    cases h : c.ch with
    | nil => exact absurd h hne
    | cons x xs => exact ⟨x, xs, rfl⟩
  have hDch := D_children avatar c
  have hDe := D_enc_arr avatar he
  rw [evalC_matches env data n f l _ cons sl (by rw [D_operator, hop]; rfl)]
  rw [sem_ext' avatar env data n P (by omega) (by omega) (by omega) (by omega)]
  obtain ⟨locs, hlocs, hdl⟩ := hdec.arr_locs hm
  have hlb : (D avatar c).leadingBytes = 0 := by
    rw [D_leadingBytes, he]; rfl
  have hce : childrenE data l (D avatar c) = .inr (some locs) := by
    rw [childrenE_arr data l _ m hDe hm
      (by rw [hDch, hch]; exact hlx x (by rw [hch]; simp)), hlocs]
  have hcvD : (D avatar c).compValue = toBytes c.cv := by
    rw [D_compValue]; exact cvOf_plain avatar (by omega) (by omega) (by omega)
  have hloc : (if l > 0 ∧ (D avatar c).encoding = .AbiEncoded then l + 32 else l) = l := by
    rw [hDe]; simp
  rw [hloc, hlb, Nat.add_zero, hce, hcvD, hop]
  show Good data P _ (matchesArrT data c.enc c.cv _ (m, l) sl (toMap cons)) sl B
  unfold matchesArrT
  rw [he, hlocs]
  simp only [ne_eq, not_true_eq_false, ite_false]
  have hp : prefixOf c.enc c.cv = toBytes c.cv := by unfold prefixOf; simp [he]
  rw [hp] at hcv
  rcases leadingCheck_cases data l (toBytes c.cv) hcv with h | h | h
  · rw [h]
    simp only [List.length_map, hDch]
    split
    · exact Good.violation data P (by decide) (by decide) sl B
    · rename_i hlen
      rw [zaSeq_eq] at hza
      refine seqLoop_rel env data P _ _ (c.ch.map za)
        (Corr.of_idx env data n P f _ _ _ (by simp) (by simp; omega) ?_) A B hza cons sl hA
      intro i h1 h2 h3 A' B' hB' cons' sl' hA'
      have hi : i < c.ch.length := by simp at h1; omega
      have hmem : c.ch[i] ∈ c.ch := List.getElem_mem hi
      have hil : i < locs.length := by simp at h1; omega
      have := ih c.ch[i] hmem _ (hdl _ (List.getElem_mem hil)) A' B' (by simpa using hB') cons' sl' hA'
      simpa [List.getElem_zip, List.getElem_zipWith, List.getElem_map] using this
  · rw [h]; exact Good.violation data P (by decide) (by decide) sl B
  · rw [h]; exact Good.violation data P (by decide) (by decide) sl B

theorem slice_rel {c x : Cond} {d m : Condition} (f l : Nat) (cons : List Consumption) (sl : Slots)
    (hop : c.op = 13) (he : c.enc = 1 ∨ c.enc = 2) (hnode : Node avatar c d) (hlay : LayEq d m)
    (hch : c.ch = [x])
    {A B : Nat → Bool}
    (ih : ∀ sz l', ∀ cons sl, Inv data P A sl →
      Good data P (evalC env data n f l' { D avatar x with size := sz } cons sl)
        (sem (W avatar env data n P) x (winMeta sz, l') sl (toMap cons)) sl B)
    (hcv : 3 ≤ c.cv.length) (hA : Inv data P A sl) :
    Good data P (evalC env data n (f + 1) l d cons sl)
      (sem (W avatar env data n P) c (m, l) sl (toMap cons)) sl B := by
  rw [evalC_slice env data n f l d cons sl (by rw [hnode.operator, hop]; rfl)]
  rw [sem_ext' avatar env data n P (by omega) (by omega) (by omega) (by omega)]
  have hcvD : d.compValue = toBytes c.cv := by
    rw [hnode.compValue]; exact cvOf_plain avatar (by omega) (by omega) (by omega)
  rw [hcvD, hnode.children, hch, hop]
  show Good data P _ (sliceT data c.enc c.cv _ (m, l) sl (toMap cons)) sl B
  unfold sliceT
  simp only [he, not_true_eq_false, ite_false, List.map_cons, List.map_nil, List.headD_cons]
  obtain ⟨b, bs, hb⟩ : ∃ b bs, c.cv = b :: bs := by
    cases h : c.cv with
    | nil => rw [h] at hcv; simp at hcv
    | cons b bs => exact ⟨b, bs, rfl⟩
  have hsz : ∃ sz, cvAt (toBytes c.cv) 2 = some sz := by
    unfold cvAt toBytes
    have : 2 < (c.cv.map fun n => (⟨n % 256, Nat.mod_lt _ (by decide)⟩ : Fin 256)).length := by
      simp; omega
    exact ⟨_, by rw [List.getElem?_eq_getElem this]; rfl⟩
  obtain ⟨sz, hsz⟩ := hsz
  rw [hsz]
  simp only
  rw [hlay.1, hlay.2]
  repeat' split
  all_goals first
    | exact Good.violation data P (s := sCalldataOverflow) (by decide) (by decide) sl B
    | exact ih sz _ cons sl hA
    | (exfalso; simp_all)

theorem leafOp_ne {o : Nat} (h : leafOp o = true) : o ≠ 0 ∧ o ≠ 1 ∧ o ≠ 2 ∧ o ≠ 5 ∧ o ≠ 4 := by
  unfold leafOp at h
  simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq] at h
  omega

theorem struct_enc {c : Cond} (hs : isStruct c = true) (h1 : c.op ≠ 1) (h2 : c.op ≠ 2) :
    c.enc ≠ 0 ∧ c.enc ≠ 6 := by
  rw [isStruct_eq] at hs
  have : (c.op == 1 || c.op == 2) = false := by simp [h1, h2]
  rw [this] at hs
  simp only [Bool.false_eq_true, ite_false, Bool.not_eq_true', Bool.or_eq_false_iff, beq_eq_false_iff_ne] at hs
  exact hs

/-! ## Variants -/

theorem prefix_of_leading_none {data : Calldata} {loc : Nat} {a : Bytes}
    (h : (leadingCheck data loc a).isNone = true) : a <+: data.drop loc := by
  unfold leadingCheck at h
  split at h
  · rename_i h0; rw [List.eq_nil_of_length_eq_zero h0]; exact List.nil_prefix
  · split at h
    · simp at h
    · split at h
      · simp at h
      · split at h
        · rename_i heq; rw [← heq]; exact List.take_prefix _ _
        · simp at h

/-- The candidate whose key the calldata starts with is the one `pick`
    chooses: no other key is comparable with it. -/
theorem pick_eq {data : Calldata} {m k : Condition} {l : Nat} (hv : isVarLay m = true)
    (hm : k ∈ m.children) (hu : KeyUnique m k)
    (hk : (leadingCheck data (adjust 5 l) k.compValue).isNone = true) : pick data m l = k := by
  unfold pick; rw [if_pos hv]
  cases hf : m.children.find? (fun k => (leadingCheck data (adjust 5 l) k.compValue).isNone) with
  | none =>
    rw [List.find?_eq_none] at hf
    exact absurd hk (hf k hm)
  | some k' =>
    simp only [Option.getD_some]
    by_cases hne : k' = k
    · exact hne
    exfalso
    have hk' := List.find?_some hf
    have hm' := List.mem_of_find?_eq_some hf
    have p1 := prefix_of_leading_none hk
    have p2 := prefix_of_leading_none hk'
    obtain ⟨n1, n2⟩ := hu k' hm' hne
    rcases Nat.le_total k'.compValue.length k.compValue.length with hl | hl
    · exact n1 (List.prefix_of_prefix_length_le p2 p1 hl)
    · exact n2 (List.prefix_of_prefix_length_le p1 p2 hl)

theorem assign_indep {V : Type} (dd : V) : ∀ (cs : List Cond) (fs : List V) (v v' : V),
    (∀ x ∈ cs, isStruct x = true) → assign dd cs fs v = assign dd cs fs v'
  | [], _, _, _, _ => rfl
  | c :: cs, fs, v, v', hs => by
    simp only [assign, hs c (by simp), ite_true]
    rw [assign_indep dd cs fs.tail v v' (fun x hx => hs x (by simp [hx]))]

theorem gate_plain {e : Nat} {cv : List Nat} {v : Condition} (l : Nat) (hv : isZipEl v = false) :
    (W avatar env data n P).gate e cv (v, l) =
      ((leadingCheck data (adjust e l) (prefixOf e cv)).isNone &&
        (decodeAt data e (layAt data e (v, l)) l).isSome) := by
  show (isZipEl v || _) = _; rw [hv, Bool.false_or]

theorem fields_plain {e : Nat} {v : Condition} (l : Nat) (hv : isZipEl v = false) :
    (W avatar env data n P).fields e (v, l) =
      match decodeAt data e (layAt data e (v, l)) l with
      | some locs => (layAt data e (v, l)).children.zip locs
      | none => [] := by
  show (if isZipEl v then _ else _) = _; rw [hv]; rfl

/-- A `Matches` with structural children depends on the value only through
    the layout it decodes with (when its leading bytes match). -/
theorem matchesT_layAt (e : Nat) (cv : List Nat) (ch : List Cond) (v1 v2 : Condition) (l : Nat)
    (hs : ∀ x ∈ ch, isStruct x = true) (hz1 : isZipEl v1 = false) (hz2 : isZipEl v2 = false)
    (h : (leadingCheck data (adjust e l) (prefixOf e cv)).isNone = true →
      layAt data e (v1, l) = layAt data e (v2, l)) :
    matchesT (W avatar env data n P) e cv ch (v1, l) = matchesT (W avatar env data n P) e cv ch (v2, l) := by
  funext sl cs
  unfold matchesT
  rw [gate_plain avatar env data n P l hz1, gate_plain avatar env data n P l hz2,
    fields_plain avatar env data n P l hz1, fields_plain avatar env data n P l hz2]
  by_cases hL : (leadingCheck data (adjust e l) (prefixOf e cv)).isNone = true
  · have hla := h hL
    rw [hla]
    split
    · congr 1
      rw [assign_indep _ ch _ (v1, l) (v2, l) hs]
    · rfl
  · simp only [Bool.not_eq_true] at hL
    simp [hL]

theorem sem_matches_eq {c : Cond} (h5 : c.op = 5) (he : c.enc = 3 ∨ c.enc = 5) (v : Val') :
    sem (W avatar env data n P) c v = matchesT (W avatar env data n P) c.enc c.cv c.ch v := by
  have h0 : ¬ c.op = 0 := by omega
  have h1 : ¬ c.op = 1 := by omega
  have h2 : ¬ c.op = 2 := by omega
  rw [sem_eq, ite_neg' h0, ite_neg' h1, ite_neg' h2, ite_pos' ⟨h5, he⟩]

/-- A call interpretation whose leading bytes the calldata does not have:
    both sides fail at the leading-bytes check. -/
theorem lead_fail_rel {c : Cond} (f l : Nat) (cons : List Consumption) (sl : Slots) (v : Val')
    (h5 : c.op = 5) (he : c.enc = 5) (hl : v.2 = l) (hz : isZipEl v.1 = false)
    (hL : (leadingCheck data (adjust 5 l) (prefixOf 5 c.cv)).isNone = false)
    (hcv : (prefixOf c.enc c.cv).length ≤ 32) (B : Nat → Bool) :
    Good data P (evalC env data n (f + 1) l (D avatar c) cons sl)
      (sem (W avatar env data n P) c v sl (toMap cons)) sl B := by
  have hDe := D_encoding_of avatar (c := c) (by omega)
  rw [evalC_matches env data n f l _ cons sl (by rw [D_operator, h5]; rfl),
    sem_matches_eq avatar env data n P h5 (.inr he)]
  have hadj : (if l > 0 ∧ (D avatar c).encoding = .AbiEncoded then l + 32 else l) = adjust 5 l := by
    rw [hDe]; unfold adjust; simp [he, encN, ConditionPacking.encOf?]
  rw [hadj, D_compValue, prefixOf_cvOf avatar h5 (.inr he)]
  rw [he] at hcv
  unfold matchesT
  rcases v with ⟨v1, v2⟩
  simp only at hl hz; subst hl
  rw [he, gate_plain avatar env data n P v2 hz]
  rcases leadingCheck_cases data (adjust 5 v2) (prefixOf 5 c.cv) hcv with h | h | h
  · rw [h] at hL; simp at hL
  · rw [h]; simpa using Good.violation data P (by decide) (by decide) sl B
  · rw [h]; simpa using Good.violation data P (by decide) (by decide) sl B

/-- What the operators read of a plain `bytes` layout: the encoding,
    `inlined` and `size`. -/
theorem input_dyn {m m' : Condition} (l : Nat) (he : m.encoding = .Dynamic) (he' : m'.encoding = .Dynamic)
    (hs : m.size = m'.size) : input data l m = input data l m' := by
  have hsz : Roles.size data l m = Roles.size data l m' := by
    rw [DecoderFaithfulness.size_eq, DecoderFaithfulness.size_eq, he, he']; simp
  unfold input
  rw [he, he', hs, hsz]

theorem extW_dyn {m m' : Condition} (o : Nat) (cv : List Nat) (ss : List (Val' → T)) (l : Nat)
    (he : m.encoding = .Dynamic) (he' : m'.encoding = .Dynamic)
    (hi : m.inlined = m'.inlined) (hs : m.size = m'.size) :
    extW avatar env data n P 2 o cv ss (m, l) = extW avatar env data n P 2 o cv ss (m', l) := by
  have hin : inputAt data 2 m l = inputAt data 2 m' l := by
    unfold inputAt; simp only [show ¬ ((2 : Nat) = 0 ∨ (2 : Nat) = 6) by omega, ite_false]
    exact input_dyn data l he he' hs
  have hcs : customSize data 2 m l = customSize data 2 m' l := by
    unfold customSize
    simp only [show ¬ ((2 : Nat) = 0 ∨ (2 : Nat) = 6) by omega, ite_false]
    rw [hs, show Roles.size data l m = Roles.size data l m' by
      rw [DecoderFaithfulness.size_eq, DecoderFaithfulness.size_eq, he, he']; simp]
  unfold extW
  split
  all_goals first
    | rfl
    | (simp only [iterT, tailT, matchesArrT, sliceT, cmpOk, bitmaskOk,
        allowanceCharge, cmpValue, hin, hi, hs]; done)
    | (unfold pluckT; simp only [hin]; done)
    | (unfold customCharges; simp only [hcs]; done)


theorem sem_dyn {c : Cond} (henc : c.enc = 2) (h1 : c.op ≠ 1) (h2 : c.op ≠ 2) {m m' : Condition} (l : Nat)
    (he : m.encoding = .Dynamic) (he' : m'.encoding = .Dynamic)
    (hi : m.inlined = m'.inlined) (hs : m.size = m'.size) :
    sem (W avatar env data n P) c (m, l) = sem (W avatar env data n P) c (m', l) := by
  rw [sem_eq, sem_eq]
  by_cases h0 : c.op = 0
  · simp [h0]
  simp only [h0, h1, h2, ite_false]
  rw [ite_neg' (by omega), ite_neg' (by omega)]
  show extW avatar env data n P c.enc c.op c.cv _ (m, l) = extW avatar env data n P c.enc c.op c.cv _ (m', l)
  rw [henc]
  exact extW_dyn avatar env data n P c.op c.cv _ l he he' hi hs

/-- A `Matches` on calldata that fits a call layout has structural
    children. -/
theorem Fits.matches_struct {c : Cond} {d k : Condition} (h : Fits avatar P c d k)
    (h5 : c.op = 5) (he : c.enc = 5) (hk : k.encoding = .AbiEncoded) :
    ∀ x ∈ c.ch, isStruct x = true := by
  cases h with
  | tup _ _ _ _ _ _ hs _ _ _ => exact hs
  | pass hop _ _ _ _ _ _ => omega
  | ns hs _ _ => rw [isStruct_eq] at hs; simp [h5, he] at hs
  | logical hop _ _ _ _ _ _ => omega
  | arr _ h _ _ _ _ _ _ _ => omega
  | slice hop _ _ _ _ _ _ _ _ => omega
  | leaf hop _ _ _ _ _ _ _ _ _ _ _ =>
    unfold leafOp at hop; simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true,
      decide_eq_true_eq] at hop; omega
  | varAbi _ _ _ hv _ _ _ _ _ _ => unfold isVarLay at hv; simp [hk] at hv
  | varDyn _ h _ _ => omega
  | zip h _ _ _ _ _ _ _ _ _ _ _ => omega
  | zipLogical h => omega

/-! ## Zips -/

theorem zipLoop_every_good {fuel : Nat} (fields : List Condition) (locss : List (List Nat))
    (kid : Nat → T) (A A' : Nat → Bool) (L : Nat)
    (hel : ∀ j, j < L → ∀ cons sl, Inv data P A sl →
      Good data P (seqLoop env data n fuel (fields.zip (locss.map fun ls => ls.getD j 0)) cons sl)
        (kid j sl (toMap cons)) sl A') :
    ∀ k i base cons sl, i + k ≤ L → Inv data P A sl →
      Good data P (zipLoop env data n fuel true fields locss k i base cons sl)
        (seqT ((List.range' i k).map kid) sl (toMap cons)) sl A
  | 0, i, base, cons, sl, _, hA => by rw [zipLoop]; exact Good.ok data P cons hA
  | k + 1, i, base, cons, sl, hL, hA => by
    rw [zipLoop]
    simp only [List.range'_succ, List.map_cons, seqT_cons, ite_true]
    have h1 := hel i (by omega) cons sl hA
    have hne := h1.1.status_ne
    rw [h1.1.eq]
    simp only [hne, ite_false]
    by_cases hs : (seqLoop env data n fuel (fields.zip (locss.map fun ls => ls.getD i 0)) cons sl).status = sOk
    · simp only [hs, ite_true, ne_eq, not_true_eq_false, ite_false, bindR_some]
      have h2 := zipLoop_every_good fields locss kid A A' L hel k (i + 1) base
        (seqLoop env data n fuel (fields.zip (locss.map fun ls => ls.getD i 0)) cons sl).cons _
        (by omega) (hA.wv h1.2.1)
      exact ⟨h2.1, h1.2.1.trans h2.2.1, h2.2.2⟩
    · simp only [hs, ite_false, ne_eq, not_false_eq_true, ite_true, bindR_none]
      refine ⟨by simp [Rel, sNotEveryZippedElementPasses, sOk, revert], h1.2.1, fun h => ?_⟩
      simp [sNotEveryZippedElementPasses, sOk] at h

theorem zipLoop_some_good {fuel : Nat} (fields : List Condition) (locss : List (List Nat))
    (kid : Nat → T) (A A' : Nat → Bool) (L : Nat)
    (hel : ∀ j, j < L → ∀ cons sl, Inv data P A sl →
      Good data P (seqLoop env data n fuel (fields.zip (locss.map fun ls => ls.getD j 0)) cons sl)
        (kid j sl (toMap cons)) sl A') :
    ∀ k i base cons sl, i + k ≤ L → Inv data P A sl →
      Good data P (zipLoop env data n fuel false fields locss k i base cons sl)
        (orT ((List.range' i k).map kid) sl (toMap base)) sl A'
  | 0, i, base, cons, sl, _, _ => by
    rw [zipLoop]; exact Good.violation data P (by decide) (by decide) sl A'
  | k + 1, i, base, cons, sl, hL, hA => by
    rw [zipLoop]
    simp only [List.range'_succ, List.map_cons, orT, Bool.false_eq_true, ite_false]
    have h1 := hel i (by omega) base sl hA
    have hne := h1.1.status_ne
    rw [h1.1.eq]
    simp only [hne, ite_false]
    by_cases hs : (seqLoop env data n fuel (fields.zip (locss.map fun ls => ls.getD i 0)) base sl).status = sOk
    · simp only [hs, ite_true]
      exact ⟨⟨rfl, by rw [if_pos hs]⟩, h1.2.1, fun _ => h1.2.2 hs⟩
    · simp only [hs, ite_false]
      have h2 := zipLoop_some_good fields locss kid A A' L hel k (i + 1) base cons _ (by omega) (hA.wv h1.2.1)
      exact ⟨h2.1, h1.2.1.trans h2.2.1, h2.2.2⟩

/-- The world decodes the plucked arrays when each slot has a layout the
    location decodes as an array with. -/
theorem zipLocsW_some (sl : Slots) : ∀ (ks : List Nat),
    (∀ k ∈ ks, ∃ ma ls, P k = some ma ∧ childrenE data (sl.locations k) ma = .inr (some ls)) →
    ∃ fl, zipLocsW data P sl ks = some fl ∧ fl.length = ks.length ∧
      ∀ i (h : i < fl.length) (h' : i < ks.length), ∃ ma, P ks[i] = some ma ∧ fl[i].1 = tmpl ma ∧
        childrenE data (sl.locations ks[i]) ma = .inr (some fl[i].2)
  | [], _ => ⟨[], rfl, rfl, fun i h => by simp at h⟩
  | k :: ks, h => by
    obtain ⟨ma, ls, hp, hc⟩ := h k (by simp)
    obtain ⟨fl, hfl, hlen, hi⟩ := zipLocsW_some sl ks fun k' hk' => h k' (by simp [hk'])
    refine ⟨(tmpl ma, ls) :: fl, ?_, by simp [hlen], fun i h h' => ?_⟩
    · simp only [zipLocsW, hp, hc, hfl, Option.map_some]
    · cases i with
      | zero => exact ⟨ma, hp, rfl, hc⟩
      | succ i => exact hi i (by simpa using h) (by simpa using h')

/-- The contract decodes the same arrays: the same element locations, and a
    length mismatch exactly when the world sees one. -/
theorem zipLocsGo_eq (cv : Bytes) (sl : Slots) : ∀ (fds : List Condition) (fl : List (Condition × List Nat))
    (ks : List Nat) (f : Nat) (len : Option Nat) (acc : List (List Nat)),
    fds.length = fl.length → fds.length = ks.length →
    (∀ j (h : j < ks.length), cvAt cv (f + j) = some ks[j] ∧ ks[j] < n) →
    (∀ j (h : j < fds.length) (h' : j < fl.length) (h'' : j < ks.length),
      childrenE data (sl.locations ks[j]) (zipStub fds[j]) = .inr (some fl[j].2)) →
    zipLocsGo data n cv fds sl f len acc =
      if fl.all (fun p => p.2.length == len.getD (fl.headD (default, [])).2.length) then
        .inr (acc ++ fl.map (·.2), len.getD (fl.headD (default, [])).2.length)
      else .inl sZippedArrayLengthMismatch
  | [], [], [], f, len, acc, _, _, _, _ => by simp [zipLocsGo]
  | [], _ :: _, _, _, _, _, h, _, _, _ => by simp at h
  | _ :: _, [], _, _, _, _, h, _, _, _ => by simp at h
  | [], [], _ :: _, _, _, _, _, h, _, _ => by simp at h
  | _ :: _, _ :: _, [], _, _, _, _, h, _, _ => by simp at h
  | fd :: fds, (lay, ls) :: fl, k :: ks, f, len, acc, h1, h2, hk, hc => by
    obtain ⟨hcv, hkn⟩ := hk 0 (by simp)
    have hc0 := hc 0 (by simp) (by simp) (by simp)
    simp only [List.getElem_cons_zero, Nat.add_zero] at hcv hkn hc0
    rw [zipLocsGo, hcv]
    simp only [show ¬ k ≥ n by omega, ite_false, hc0]
    have ih := fun len' acc' => zipLocsGo_eq cv sl fds fl ks (f + 1) len' acc'
      (by simpa using h1) (by simpa using h2)
      (fun j h => by have := hk (j + 1) (by simpa using h); simpa [Nat.add_assoc, Nat.add_comm 1] using this)
      (fun j h h' h'' => by
        have := hc (j + 1) (by simpa using h) (by simpa using h') (by simpa using h'')
        simpa only [List.getElem_cons_succ] using this)
    cases len with
    | some m =>
      simp only [Option.getD_some]
      by_cases hm : m = ls.length
      · rw [if_neg (by omega), ih (some m) (acc ++ [ls])]
        simp only [Option.getD_some, List.all_cons, hm, beq_self_eq_true, Bool.true_and, List.map_cons,
          List.append_assoc, List.singleton_append]
      · rw [if_pos (by omega)]
        have : (ls.length == m) = false := by simp; omega
        simp [this]
    | none =>
      rw [ih (some ls.length) (acc ++ [ls])]
      simp only [Option.getD_some, Option.getD_none, List.headD_cons, List.all_cons, beq_self_eq_true,
        Bool.true_and, List.map_cons, List.append_assoc, List.singleton_append]

theorem evalC_zip (f l : Nat) (d : Condition) (cons : List Consumption) (sl : Slots) (every : Bool)
    (hd : d.operator = if every then .ZipEvery else .ZipSome) :
    evalC env data n (f + 1) l d cons sl =
      match d.children with
      | [] => violation revert sl
      | t :: _ =>
        match zipLocs data n d.compValue t.children sl with
        | .inl s => violation s sl
        | .inr (locss, len) => zipLoop env data n f every t.children locss len 0 cons cons sl := by
  rw [evalC]
  cases every <;> simp only [hd, Bool.false_eq_true, ite_false, ite_true] <;> rfl

theorem cvAt_toBytes_at (cv : List Nat) (j : Nat) (h : j < cv.length) :
    cvAt (toBytes cv) j = some (cv[j] % 256) := by
  simp [cvAt, toBytes, List.getElem?_eq_getElem h]

/-- A Zip whose slots hold sound locations: the contract and the world decode
    the same arrays and run the fields on the same elements. -/
theorem zip_rel {c t : Cond} {m : Condition} (f l : Nat) (cons : List Consumption) (sl : Slots)
    (hop : c.op = 10 ∨ c.op = 11) (he : c.enc = 0) (hch : c.ch = [t]) (ht5 : t.op = 5)
    (ht3 : t.enc = 3) (hlen : t.ch.length = c.cv.length) (hs : ∀ x ∈ t.ch, isStruct x = true)
    (hPs : ∀ k ∈ c.cv, (P (k % 256)).isSome)
    (hParr : ∀ f ma, P (c.cv.getD f 0 % 256) = some ma → ma.encoding = .Array)
    (hlay : ∀ i (h : i < t.ch.length) ma, P (c.cv.getD i 0 % 256) = some ma →
      LayEq (D avatar t.ch[i]) (tmpl ma))
    (ih : ∀ i (h : i < t.ch.length) ma, P (c.cv.getD i 0 % 256) = some ma → ∀ l',
      Decodable data (tmpl ma) l' → ∀ A B, za t.ch[i] A = some B → ∀ cons sl, Inv data P A sl →
      Good data P (evalC env data n f l' (D avatar t.ch[i]) cons sl)
        (sem (W avatar env data n P) t.ch[i] (tmpl ma, l') sl (toMap cons)) sl B)
    (hcvn : ∀ k ∈ c.cv, k % 256 < n) {A B : Nat → Bool} (hza : za c A = some B)
    (hA : Inv data P A sl) :
    Good data P (evalC env data n (f + 1) l (D avatar c) cons sl)
      (sem (W avatar env data n P) c (m, l) sl (toMap cons)) sl B := by
  have every_def : (c.op = 11) ∨ (c.op = 10) := by omega
  -- the node the contract runs
  have hDop : (D avatar c).operator = if decide (c.op = 11) then .ZipEvery else .ZipSome := by
    rw [D_operator]
    rcases hop with h | h <;> simp [h, opN, ConditionPacking.opOf?]
  have hDch : (D avatar c).children = [D avatar t] := by rw [D_children, hch]; rfl
  have hDcv : (D avatar c).compValue = toBytes c.cv := by
    rw [D_compValue]; exact cvOf_plain avatar (by omega) (by omega) (by omega)
  have hDtch : (D avatar t).children = t.ch.map (D avatar) := D_children avatar t
  -- the world's meaning
  have hsem : sem (W avatar env data n P) c (m, l) =
      zipT data P (decide (c.op = 11)) (zipKeys c.cv) (sem (W avatar env data n P) t) := by
    rw [sem_ext' avatar env data n P (by omega) (by omega) (by omega) (by omega), hch]
    rcases hop with h | h <;> rw [h] <;> rfl
  -- the slots it reads
  rw [za_eq, if_neg (by omega), if_pos hop] at hza
  split at hza
  case isFalse => cases hza
  rename_i hall
  obtain ⟨A', hA', hB⟩ := Option.map_eq_some_iff.1 hza
  rw [hch, zaFields_cons] at hA'
  have hkA : ∀ k ∈ zipKeys c.cv, A k = true := fun k hk => by simpa using List.all_eq_true.1 hall k hk
  have hdecs : ∀ k ∈ zipKeys c.cv, ∃ ma, P k = some ma ∧ Decodable data ma (sl.locations k) ∧
      ma.encoding = .Array := by
    intro k hk
    obtain ⟨k', hk', rfl⟩ := List.mem_map.1 hk
    obtain ⟨ma, hma⟩ := Option.isSome_iff_exists.1 (hPs k' hk')
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hk'
    have hg : c.cv.getD j 0 = c.cv[j] := by simp [List.getD_eq_getElem?_getD, hj]
    refine ⟨ma, hma, hA _ ma (hkA _ hk) hma, hParr j ma (by rw [hg]; exact hma)⟩
  obtain ⟨fl, hfl, hflen, hfli⟩ := zipLocsW_some data P sl (zipKeys c.cv) fun k hk => by
    obtain ⟨ma, hp, hd, harr⟩ := hdecs k hk
    obtain ⟨ls, hls, -⟩ := hd.arr_locs harr
    exact ⟨ma, ls, hp, hls⟩
  have hkl : (zipKeys c.cv).length = t.ch.length := by simp [zipKeys, hlen]
  -- field `i`: its key, layout and elements
  have hfield : ∀ i (hi : i < t.ch.length), ∃ ma, P (c.cv.getD i 0 % 256) = some ma ∧
      fl[i]'(by omega) = (tmpl ma, (fl[i]'(by omega)).2) ∧
      childrenE data (sl.locations (c.cv.getD i 0 % 256)) ma = .inr (some (fl[i]'(by omega)).2) ∧
      ∀ l' ∈ (fl[i]'(by omega)).2, Decodable data (tmpl ma) l' := by
    intro i hi
    obtain ⟨ma, hp, h1, h2⟩ := hfli i (by omega) (by omega)
    have hki : (zipKeys c.cv)[i]'(by omega) = c.cv.getD i 0 % 256 := by
      simp [zipKeys, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show i < c.cv.length by omega)]
    obtain ⟨ma', hp', hd, harr⟩ := hdecs _ (List.getElem_mem (show i < (zipKeys c.cv).length by omega))
    rw [hki] at hp h2 hp' hd
    rw [hp] at hp'
    cases hp'
    obtain ⟨ls, hls, hdl⟩ := hd.arr_locs harr
    rw [h2] at hls
    simp only [Sum.inr.injEq, Option.some.injEq] at hls
    refine ⟨ma, hp, Prod.ext h1 rfl, h2, fun l' hl' => hdl l' (hls ▸ hl')⟩
  -- the contract decodes the same arrays
  have hgo : zipLocs data n (toBytes c.cv) (t.ch.map (D avatar)) sl =
      if fl.all (fun p => p.2.length == (fl.headD (default, [])).2.length) then
        .inr (fl.map (·.2), (fl.headD (default, [])).2.length)
      else .inl sZippedArrayLengthMismatch := by
    unfold zipLocs
    rw [zipLocsGo_eq data n (toBytes c.cv) sl (t.ch.map (D avatar)) fl (zipKeys c.cv) 0 none []
      (by simp; omega) (by simp [hkl])]
    · simp
    · intro j hj
      have hj' : j < c.cv.length := by simp [zipKeys] at hj; exact hj
      refine ⟨by rw [Nat.zero_add, cvAt_toBytes_at c.cv j hj']; simp [zipKeys], ?_⟩
      simpa [zipKeys] using hcvn _ (List.getElem_mem hj')
    · intro j h h' h''
      have hj : j < t.ch.length := by simpa using h
      obtain ⟨ma, hp, -, hc, -⟩ := hfield j hj
      have hki : (zipKeys c.cv)[j] = c.cv.getD j 0 % 256 := by
        simp [zipKeys, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show j < c.cv.length by omega)]
      rw [hki, childrenE_arr data _ (zipStub _) ma rfl (hParr j ma hp)
        (by simpa [zipStub, tmpl] using hlay j hj ma hp)]
      exact hc
  rw [evalC_zip env data n f l _ cons sl (decide (c.op = 11)) hDop, hDch]
  simp only
  rw [hDcv, hDtch, hgo, hsem]
  show Good data P _ (zipF data P (decide (c.op = 11)) (zipKeys c.cv) (sem (W avatar env data n P) t) sl sl
    (toMap cons)) sl B
  unfold zipF
  rw [hfl]
  simp only
  by_cases hall2 : (fl.all fun p => p.2.length == (fl.headD (default, [])).2.length) = true
  · rw [if_pos hall2, if_pos hall2]
    simp only
    have hel : ∀ j, j < (fl.headD (default, [])).2.length → ∀ cs sl', Inv data P A sl' →
        Good data P (seqLoop env data n f ((t.ch.map (D avatar)).zip ((fl.map (·.2)).map fun ls => ls.getD j 0))
          cs sl') (sem (W avatar env data n P) t (zipAt fl j) sl' (toMap cs)) sl' A' := by
      intro j hj cs sl' hAs
      rw [sem_matches_eq avatar env data n P ht5 (.inl ht3)]
      unfold matchesT
      have hg : (W avatar env data n P).gate t.enc t.cv (zipAt fl j) = true := by
        simp only [W, contractWorld, zipAt, isZipEl_zipEl, Bool.true_or]
      have hf : (W avatar env data n P).fields t.enc (zipAt fl j) = fl.map fun p => (p.1, p.2.getD j 0) := by
        simp only [W, contractWorld, zipAt, isZipEl_zipEl, ite_true, zipElFields_zipEl]
      rw [if_pos hg, hf, assign_struct _ t.ch _ _ hs (by simp <;> omega)]
      rw [zaSeq_eq] at hA'
      refine seqLoop_rel env data P _ _ (t.ch.map za)
        (Corr.of_idx env data n P f _ _ _ (by simp <;> omega) (by simp <;> omega) ?_) A A' hA' cs sl' hAs
      intro i h1 h2 h3 A1 B1 hB1 cs' sl'' hA1
      have hi : i < t.ch.length := by simp at h1; omega
      have hif : i < fl.length := by omega
      obtain ⟨ma, hp, hfi, -, hdl⟩ := hfield i hi
      have hjl : j < (fl[i]).2.length := by
        have := List.all_eq_true.1 hall2 fl[i] (List.getElem_mem hif)
        simp only [beq_iff_eq] at this; omega
      have hmem : (fl[i]).2.getD j 0 ∈ (fl[i]).2 := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hjl]; exact List.getElem_mem hjl
      have h1' := ih i hi ma hp _ (hdl _ hmem) A1 B1 (by simpa using hB1) cs' sl'' hA1
      have e1 : (fl[i]).1 = tmpl ma := congrArg Prod.fst hfi
      simp only [List.getElem_zip, List.getElem_map, e1]
      exact h1'
    rcases hop with h10 | h11
    · have hd : decide (c.op = 11) = false := by simp [h10]
      rw [hd]
      simp only [Bool.false_eq_true, ite_false]
      rw [show B = A' by rw [← hB, h10]; rfl, List.range_eq_range']
      exact zipLoop_some_good env data n P (t.ch.map (D avatar)) (fl.map (·.2))
        (fun j => sem (W avatar env data n P) t (zipAt fl j)) A A' (fl.headD (default, [])).2.length hel
        (fl.headD (default, [])).2.length 0 cons cons sl (by omega) hA
    · have hd : decide (c.op = 11) = true := by simp [h11]
      rw [hd]
      simp only [ite_true]
      rw [show B = A by rw [← hB, h11]; rfl, List.range_eq_range']
      exact zipLoop_every_good env data n P (t.ch.map (D avatar)) (fl.map (·.2))
        (fun j => sem (W avatar env data n P) t (zipAt fl j)) A A' (fl.headD (default, [])).2.length hel
        (fl.headD (default, [])).2.length 0 cons cons sl (by omega) hA
  · rw [if_neg hall2, if_neg hall2]
    exact Good.violation data P (by decide) (by decide) sl B

include henv in
/-- **Adequacy.** The evaluator transcription computes the contract world's
    meaning, for every tree whose layout fits `m`, on calldata that decodes
    as `m`, from slots whose locations the tree's Zips may read (`Inv` for
    the slots `za` needs). It also keeps the slots sound for later Zips. -/
theorem adequacy {c : Cond} {d m : Condition} (hfit : Fits avatar P c d m) :
    ∀ (fuel l : Nat) (cons : List Consumption) (sl : Slots) (A B : Nat → Bool), height c < fuel →
      CvOk n c → Decodable data m l → za c A = some B → Inv data P A sl →
      Good data P (evalC env data n fuel l d cons sl)
        (sem (W avatar env data n P) c (m, l) sl (toMap cons)) sl B := by
  induction hfit with
  | @pass c d m hop hnode _ _ _ _ _ =>
    intro fuel l cons sl A B hh _ _ hza hA
    obtain ⟨f, rfl, -⟩ := fuel_succ hh
    rw [za_plain (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega)] at hza
    cases hza
    rw [evalC_pass env data n f l d cons sl (by rw [hnode.operator, hop]; rfl), sem_eq, ite_pos' hop]
    exact Good.ok data P cons hA
  | @ns c d m _ hns hd hpl =>
    intro fuel l cons sl A B hh hcv _ hza hA
    subst hd
    exact ns_adequacy avatar env henv data n P hns m fuel l cons sl A B hpl hh hcv hza hA
  | @logical c d m hop _ _ hd _ _ _ ih =>
    intro fuel l cons sl A B hh hcv hdec hza hA
    obtain ⟨f, rfl, hf⟩ := fuel_succ hh
    subst hd
    have hcorr : Corr env data P n f (c.ch.map fun x => (D avatar x, l))
        (c.ch.map fun x => sem (W avatar env data n P) x (m, l)) (c.ch.map za) :=
      Corr.of_map env data n P f _ _ _ c.ch fun x hx A B hB cons sl hA =>
        ih x hx f l cons sl A B (by have := height_mem hx; omega) (hcv.child hx) hdec hB hA
    rcases hop with h1 | h2
    · rw [evalC_and env data n f l _ cons sl (by rw [D_operator, h1]; rfl), sem_eq,
        ite_neg' (by omega), ite_pos' h1, D_children, List.map_map]
      rw [za_eq, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
        if_pos (by omega), zaSeq_eq] at hza
      exact seqLoop_rel env data P _ _ _ hcorr A B hza cons sl hA
    · rw [evalC_or env data n f l _ cons sl (by rw [D_operator, h2]; rfl), sem_eq,
        ite_neg' (by omega), ite_neg' (by omega), ite_pos' h2, D_children]
      rw [za_eq, if_neg (by omega), if_neg (by omega), if_pos h2, zaOr_eq] at hza
      refine orLoop_rel env data P l ?_ A B hza cons sl hA
      rw [List.map_map]; exact hcorr
  | @zipLogical c d m hop _ _ _ hd _ _ ih =>
    intro fuel l cons sl A B hh hcv hdec hza hA
    obtain ⟨f, rfl, hf⟩ := fuel_succ hh
    subst hd
    have hcorr : Corr env data P n f (c.ch.map fun x => (D avatar x, l))
        (c.ch.map fun x => sem (W avatar env data n P) x (m, l)) (c.ch.map za) :=
      Corr.of_map env data n P f _ _ _ c.ch fun x hx A B hB cons sl hA =>
        ih x hx f l cons sl A B (by have := height_mem hx; omega) (hcv.child hx) hdec hB hA
    rcases hop with h1 | h2
    · rw [evalC_and env data n f l _ cons sl (by rw [D_operator, h1]; rfl), sem_eq,
        ite_neg' (by omega), ite_pos' h1, D_children, List.map_map]
      rw [za_eq, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
        if_pos (by omega), zaSeq_eq] at hza
      exact seqLoop_rel env data P _ _ _ hcorr A B hza cons sl hA
    · rw [evalC_or env data n f l _ cons sl (by rw [D_operator, h2]; rfl), sem_eq,
        ite_neg' (by omega), ite_neg' (by omega), ite_pos' h2, D_children]
      rw [za_eq, if_neg (by omega), if_neg (by omega), if_pos h2, zaOr_eq] at hza
      refine orLoop_rel env data P l ?_ A B hza cons sl hA
      rw [List.map_map]; exact hcorr
  | @tup c d m h5 he hd hm hlay hlb hs hk hch _ ih =>
    intro fuel l cons sl A B hh hcv hdec hza hA
    obtain ⟨f, rfl, hf⟩ := fuel_succ hh
    subst hd
    have hcv' := hcv
    rw [cvOk_eq] at hcv'
    rw [za_eq, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_pos (by omega)] at hza
    exact tup_rel avatar env henv data n P f l cons sl h5 he hm hlb hs hk
      (fun i h => Fits.layEq avatar P (hch i h) (hs _ (List.getElem_mem h)))
      (fun i h l' hd' A B hB cons sl hA => ih i h f l' cons sl A B
        (by have := height_mem (List.getElem_mem h); omega)
        (hcv.child (List.getElem_mem h)) hd' hB hA)
      (hcv'.1 h5) hdec hza hA
  | @arr c d m hop he hd hm _ hne hs hch _ ih =>
    intro fuel l cons sl A B hh hcv hdec hza hA
    obtain ⟨f, rfl, hf⟩ := fuel_succ hh
    subst hd
    have hlx : ∀ x ∈ c.ch, LayEq (D avatar x) (tmpl m) := fun x hx =>
      Fits.layEq avatar P (hch x hx) (hs x hx)
    have ih' : ∀ x ∈ c.ch, ∀ l', Decodable data (tmpl m) l' → ∀ A B, za x A = some B → ∀ cons sl,
        Inv data P A sl → Good data P (evalC env data n f l' (D avatar x) cons sl)
          (sem (W avatar env data n P) x (tmpl m, l') sl (toMap cons)) sl B :=
      fun x hx l' hd' A B hB cons sl hA => ih x hx f l' cons sl A B
        (by have := height_mem hx; omega) (hcv.child hx) hd' hB hA
    have hcv' := hcv
    rw [cvOk_eq] at hcv'
    rcases hop with h | h | h | h
    · rw [za_eq, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
        if_pos (by omega)] at hza
      exact marr_rel avatar env henv data n P f l cons sl h he hm hne hlx ih' (hcv'.1 h) hdec hza hA
    · obtain ⟨x, xs, hx⟩ : ∃ x xs, c.ch = x :: xs := by
        cases h' : c.ch with
        | nil => exact absurd h' hne
        | cons x xs => exact ⟨x, xs, rfl⟩
      rw [za_eq, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega), hx,
        zaFirst_cons] at hza
      obtain ⟨B', hB', hBB⟩ := Option.map_eq_some_iff.1 hza
      have := iter_rel avatar env henv data n P f l cons sl false (by simp [h]) he hm hx
        (hlx x (by rw [hx]; simp)) (ih' x (by rw [hx]; simp)) hdec hB' hA
      rw [← hBB, if_pos h]; exact this
    · obtain ⟨x, xs, hx⟩ : ∃ x xs, c.ch = x :: xs := by
        cases h' : c.ch with
        | nil => exact absurd h' hne
        | cons x xs => exact ⟨x, xs, rfl⟩
      rw [za_eq, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega), hx,
        zaFirst_cons] at hza
      obtain ⟨B', hB', hBB⟩ := Option.map_eq_some_iff.1 hza
      have := iter_rel avatar env henv data n P f l cons sl true (by simp [h]) he hm hx
        (hlx x (by rw [hx]; simp)) (ih' x (by rw [hx]; simp)) hdec hB' hA
      rw [← hBB, if_neg (by omega)]; exact this
    · rw [za_eq, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
        if_pos (by omega)] at hza
      exact tail_rel avatar env henv data n P f l cons sl h he hm hne hlx ih' hdec hza hA
  | @slice c d m x hop he hnode hlay hch _ _ _ _ ih =>
    intro fuel l cons sl A B hh hcv _ hza hA
    obtain ⟨f, rfl, hf⟩ := fuel_succ hh
    have hx : x ∈ c.ch := by rw [hch]; simp
    have hcv' := hcv
    rw [cvOk_eq] at hcv'
    rw [za_eq, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_neg (by omega), if_pos hop, hch, zaFirst_cons] at hza
    exact slice_rel avatar env data n P f l cons sl hop he hnode hlay hch
      (fun sz l' cons sl hA => ih sz f l' cons sl A B (by have := height_mem hx; omega) (hcv.child hx)
        (.leaf (by simp [winMeta]) (by simp [winMeta]) (by simp [winMeta])
          (by simp [winMeta, isVarLay])) hza hA)
      (hcv'.2.1 hop) hA
  | @varAbi c d m k h5 he hd hv _ hmem hkenc hkey hu hf ih =>
    intro fuel l cons sl A B hh hcv hdec hza hA
    obtain ⟨f, rfl, -⟩ := fuel_succ hh
    subst hd
    have hcv' := hcv
    rw [cvOk_eq] at hcv'
    have hlen : (prefixOf c.enc c.cv).length ≤ 32 := hcv'.1 h5
    have hs := Fits.matches_struct avatar P hf h5 he hkenc
    have hkd : k.encoding ≠ .Dynamic := by rw [hkenc]; decide
    have hmz : isZipEl m = false := isZipEl_of_ne (by
      unfold isVarLay at hv; simp at hv; rw [hv.2]; decide)
    have hkz : isZipEl k = false := isZipEl_of_ne (by rw [hkenc]; decide)
    -- the variant decodes as the candidate whenever its leading bytes match
    have hsem : sem (W avatar env data n P) c (m, l) = sem (W avatar env data n P) c (k, l) := by
      rw [sem_matches_eq avatar env data n P h5 (.inr he), sem_matches_eq avatar env data n P h5 (.inr he), he]
      refine matchesT_layAt avatar env data n P 5 c.cv c.ch m k l hs hmz hkz fun hL => ?_
      unfold layAt
      simp only [ite_true]
      rw [pick_eq hv hmem hu (by rw [hkey]; exact hL), pick_of_ne l hkd]
    cases hL : (leadingCheck data (adjust 5 l) (prefixOf 5 c.cv)).isNone
    · exact lead_fail_rel avatar env data n P f l cons sl (m, l) h5 he rfl hmz hL hlen B
    · have hdk : Decodable data k l := by
        cases hdec with
        | var _ h => exact h k hmem (by rw [hkey]; exact hL)
        | leaf _ _ _ hnv => rw [hv] at hnv; cases hnv
        | tup _ h1 _ _ =>
          unfold isVarLay at hv; simp at hv; rcases h1 with h1 | h1 <;> rw [hv.2] at h1 <;> cases h1
        | arr _ h1 _ _ => unfold isVarLay at hv; simp at hv; rw [hv.2] at h1; cases h1
      rw [hsem]; exact ih (f + 1) l cons sl A B hh hcv hdk hza hA
  | @varDyn c d m hv he2 hl hf ih =>
    intro fuel l cons sl A B hh hcv _ hza hA
    have hops := Fits.dyn_op avatar P hf he2
    have hst : isStruct c = true := by
      rw [isStruct_eq]
      have : (c.op == 1 || c.op == 2) = false := by simp [hops.1, hops.2]
      rw [this]; simp [he2]
    have hld := Fits.layEq avatar P hf hst
    have hme : m.encoding = .Dynamic := by unfold isVarLay at hv; simp at hv; exact hv.2
    have hsem : sem (W avatar env data n P) c (m, l) = sem (W avatar env data n P) c (dynLay, l) :=
      sem_dyn avatar env data n P he2 hops.1 hops.2 l hme rfl
        (by rw [← hl.1, hld.1]) (by rw [← hl.2, hld.2])
    rw [hsem]
    exact ih fuel l cons sl A B hh hcv
      (.leaf (by simp [dynLay]) (by simp [dynLay]) (by simp [dynLay]) (by simp [dynLay, isVarLay])) hza hA
  | @leaf c d m hop hs hnode hty henc hinl _ _ _ _ _ _ hpk =>
    intro fuel l cons sl A B hh hcv hdec hza hA
    obtain ⟨f, rfl, -⟩ := fuel_succ hh
    have hne := leafOp_ne hop
    have hse := struct_enc hs hne.2.1 hne.2.2.1
    have hether : ¬(c.enc = 0 ∨ c.enc = 6) := by omega
    rw [sem_ext avatar env data n P hne.1 hne.2.1 hne.2.2.1 hne.2.2.2.1]
    have hcv' := hcv
    rw [cvOk_eq] at hcv'
    have hrel := ext_rel avatar env henv data n P c d m f l cons sl (c.ch.map (sem (W avatar env data n P)))
      hnode.operator (Or.inr hop) henc
      (by unfold inputAt; rw [ite_neg' hether]; exact input_tyEq data hty l)
      (fun _ => ⟨hty.layEq.1, hty.layEq.2⟩)
      (by intro _; unfold customSize; rw [ite_neg' hether, hty.layEq.2, size_tyEq data hty l])
      hnode.compValue (by intro h16; rw [ite_neg' hether]; exact (hinl h16).symm) hcv'.2.2.1
    by_cases h14 : c.op = 14
    · obtain ⟨k0, hk0, -⟩ := hcv'.2.2.1 h14
      rw [za_eq, if_pos h14] at hza
      cases hza
      have hhd : c.cv.headD 0 = k0 := by
        cases h : c.cv with
        | nil => simp [h] at hk0
        | cons a as => simp [h] at hk0; simp [hk0]
      have hx : extW avatar env data n P c.enc c.op c.cv (c.ch.map (sem (W avatar env data n P))) (m, l) =
          pluckT env data n c.enc c.cv (m, l) := by rw [h14]; rfl
      rw [hx] at hrel ⊢
      exact pluck_good env data n P rfl hrel hk0 hA fun ma h => by
        rw [hpk h14 ma (by rw [hhd]; exact h)]; exact hdec
    · have hops : c.op = 4 ∨ leafOp c.op = true := .inr hop
      have hl := hop
      unfold leafOp at hl
      simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq] at hl
      rw [za_plain h14 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega)] at hza
      cases hza
      exact Good.of_rel_keeps data P hrel
        (extW_leaf_slots avatar env data n P _ _ _ _ _ _ _ hops h14) hA
  | @zip c d m t hop he hd hch _ ht5 ht3 hlen hs hPs hParr hflds ih =>
    intro fuel l cons sl A B hh hcv _ hza hA
    obtain ⟨f, rfl, hf⟩ := fuel_succ hh
    subst hd
    have ht : t ∈ c.ch := by rw [hch]; simp
    have hcv' := hcv
    rw [cvOk_eq] at hcv'
    have hcvt := hcv.child ht
    exact zip_rel avatar env data n P f l cons sl hop he hch ht5 ht3 hlen hs hPs hParr
      (fun i h ma hp => Fits.layEq avatar P (hflds i h ma hp) (hs _ (List.getElem_mem h)))
      (fun i h ma hp l' hd' A B hB cons sl hA => ih i h ma hp f l' cons sl A B
        (by have := height_mem (List.getElem_mem h); have := height_mem ht; omega)
        (hcvt.child (List.getElem_mem h)) hd' hB hA)
      (hcv'.2.2.2.1 hop) hza hA

end
end Bridge
