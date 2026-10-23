import Bridge.Preserve

/-!
# Padding keeps a tree fitting its layout

The type tree of a node that fits `m` (`createTT`), rendered as `Pass` nodes
(`passFor`), describes a prefix of `m` (`createTT_fits`). Extending a node
that fits `m` with such a description appends `Pass` children only to
containers that are not inlined, at positions `m` has, with `m`'s types
(`extendC_fits`); a check on a whole value already lists all of `m`'s
fields, and stays as it is.
-/

namespace Bridge
open DecoderFaithfulness DecoderFaithfulness.Roles Normalize Evaluate

section
variable (avatar : Bytes)

local notation "F" => fun (c : Cond) (m : Condition) => Fits avatar c (D avatar c) m

theorem passFor_mk (e : Nat) (ch : List TT) :
    passFor (.mk e ch) = ⟨e, 0, [], if e == 3 || e == 4 || e == 5 then ch.map passFor else []⟩ := by
  rw [passFor, passForL_eq]

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
  (h.fits avatar).raw avatar (isStruct_pass (h.op avatar) (h.enc avatar))

theorem filterMap_some {f : Cond → Option TT} : ∀ (l : List Cond), (∀ x ∈ l, (f x).isSome = true) →
    ∃ ts, l.filterMap f = ts ∧ ts.length = l.length ∧
      ∀ i (h1 : i < l.length) (h2 : i < ts.length), f l[i] = some ts[i]
  | [], _ => ⟨[], rfl, rfl, fun _ h => by simp at h⟩
  | x :: xs, h => by
    obtain ⟨t, ht⟩ := Option.isSome_iff_exists.1 (h x (by simp))
    obtain ⟨ts, h1, h2, h3⟩ := filterMap_some xs fun y hy => h y (by simp [hy])
    refine ⟨t :: ts, by simp [List.filterMap_cons, ht, h1], by simp [h2], ?_⟩
    intro i hi1 hi2
    cases i with
    | zero => simpa using ht
    | succ i => simpa using h3 i (by simpa using hi1) (by simpa using hi2)

theorem D_encoding_same {c c' : Cond} (he : c.enc = c'.enc) : (D avatar c).encoding = (D avatar c').encoding := by
  rw [D_encoding, D_encoding, he]

theorem pdesc_tt : ∀ {c : Cond} {m : Condition}, PDesc avatar c m →
    ∃ t, createTT c = some t ∧ PDesc avatar (passFor t) m := by
  intro c m h
  induction h with
  | @leaf c m h0 he hch hl hs =>
    refine ⟨.mk c.enc [], ?_, ?_⟩
    · rcases c with ⟨e, o, cv, ch⟩; simp only at h0 he hch; subst h0 hch
      rw [createTT_mk]; rcases he with rfl | rfl <;> rfl
    · rw [passFor_mk]
      have hpe : (if (c.enc == 3 || c.enc == 4 || c.enc == 5) = true then ([] : List TT).map passFor else []) = [] := by
        split <;> rfl
      rw [hpe]
      have hm := D_meta_same avatar (c := ⟨c.enc, 0, [], []⟩) (c' := c) rfl (by rw [hch])
      have hr := raw_same avatar (c := ⟨c.enc, 0, [], []⟩) (c' := c) rfl (by rw [hch])
      refine .leaf rfl he rfl ⟨hm.1.trans hl.1, hm.2.trans hl.2⟩ ?_
      rw [hr.1, hs, hm.1]
  | @tup c m h0 he hm hk hch hl hs ih =>
    have hsome : ∀ x ∈ c.ch, (createTT x).isSome = true := by
      intro x hx
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
      obtain ⟨t, ht, -⟩ := ih i hi
      simp [ht]
    obtain ⟨ts, hts, hlen, hget⟩ := filterMap_some c.ch hsome
    have hct : createTT c = some (.mk c.enc ts) := by
      rcases c with ⟨e, o, cv, ch⟩; simp only at h0 he hts ⊢; subst h0
      rw [createTT_mk, createTTL_eq, hts]
      rcases he with rfl | rfl <;> rfl
    refine ⟨.mk c.enc ts, hct, ?_⟩
    have hpf : passFor (.mk c.enc ts) = ⟨c.enc, 0, [], ts.map passFor⟩ := by
      rw [passFor_mk]; rcases he with h | h <;> simp [h]
    rw [hpf]
    have hchild : ∀ i (h1 : i < (ts.map passFor).length),
        PDesc avatar (ts.map passFor)[i] (m.children.getD i default) := by
      intro i h1
      have h1' : i < c.ch.length := by simp at h1; omega
      obtain ⟨t, ht, hp⟩ := ih i h1'
      rw [hget i h1' (by simp at h1; exact h1)] at ht
      simp only [Option.some.injEq] at ht
      simp only [List.getElem_map]; rw [ht]; exact hp
    have hraw := container_raw avatar (c := c) (c' := ⟨c.enc, 0, [], ts.map passFor⟩) rfl
      (by simp [hlen]) (fun i h1 h2 => by
        have r1 := (hch i h1).raw avatar
        have r2 := (hchild i h2).raw avatar
        exact ⟨r1.1.trans r2.1.symm,
          fun hi => (r1.2.1 hi).trans (r2.2.1 (r2.1.trans (r1.1.symm.trans hi))).symm⟩)
    obtain ⟨hsn', hl'⟩ := lay_transfer avatar hraw hs hl
    exact .tup rfl he ((D_encoding_same avatar (c := ⟨c.enc, 0, [], ts.map passFor⟩) (c' := c) rfl).trans hm)
      (by simp [hlen]; exact hk) hchild hl' hsn'
  | @arr c m x h0 he hch hm hx hl hs ih =>
    obtain ⟨t0, ht0, hp0⟩ := ih
    have hct : createTT c = some (.mk 4 [t0]) := by
      rcases c with ⟨e, o, cv, ch⟩; simp only at h0 he hch; subst h0 he hch
      rw [createTT_mk]; simp [ht0]
    refine ⟨.mk 4 [t0], hct, ?_⟩
    have hpf : passFor (.mk 4 [t0]) = ⟨4, 0, [], [passFor t0]⟩ := by rw [passFor_mk]; rfl
    rw [hpf]
    have hraw : isInl c = isInl ⟨4, 0, [], [passFor t0]⟩ ∧
        (isInl c = true → rawSz avatar c = rawSz avatar ⟨4, 0, [], [passFor t0]⟩) := by
      have h1 : isInl c = false := by rw [isInl_eq, he]; rfl
      have h2 : isInl (⟨4, 0, [], [passFor t0]⟩ : Cond) = false := by rw [isInl_eq]; rfl
      rw [h1, h2]; simp
    obtain ⟨hsn', hl'⟩ := lay_transfer avatar hraw hs hl
    exact .arr rfl rfl rfl hm hp0 hl' hsn'

theorem createTTFirst_none : ∀ {l : List Cond}, (∀ x ∈ l, isStruct x = false) → createTTFirst l = none
  | [], _ => rfl
  | x :: xs, h => by
    unfold createTTFirst; rw [if_neg (by simp [h x (by simp)])]
    exact createTTFirst_none fun y hy => h y (by simp [hy])

theorem createTTFirst_some : ∀ {l : List Cond}, (∀ x ∈ l, isStruct x = true → (createTT x).isSome = true) →
    (∃ x ∈ l, isStruct x = true) → (createTTFirst l).isSome = true
  | [], _, ⟨_, hx, _⟩ => by simp at hx
  | x :: xs, h, ⟨y, hy, hys⟩ => by
    unfold createTTFirst
    split
    · rename_i hxs; exact h x (by simp) hxs
    · rename_i hxs
      rcases List.mem_cons.1 hy with rfl | hy
      · exact absurd hys hxs
      · exact createTTFirst_some (fun z hz => h z (by simp [hz])) ⟨y, hy, hys⟩

theorem NsOk.createTT : ∀ {x : Cond}, NsOk x → Normalize.createTT x = none := by
  intro x h
  induction h with
  | @leaf c he hch hop =>
    rcases c with ⟨e, o, cv, ch⟩; simp only at he hch hop
    rw [createTT_mk]
    have : (o == 1 || o == 2) = false := by
      simp only [nsOp, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq] at hop
      simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne]; omega
    rw [this]
    rcases he with rfl | rfl <;> rfl
  | @logical c hop _ hall _ =>
    rcases c with ⟨e, o, cv, ch⟩; simp only at hop hall
    rw [createTT_mk]
    have : (o == 1 || o == 2) = true := by rcases hop with h | h <;> simp [h]
    rw [this]; simp only [ite_true]
    exact createTTFirst_none fun y hy => (hall y hy).isStruct

theorem tmpl_eq (m : Condition) : tmpl m = m.children.getD 0 default := by
  unfold tmpl; cases m.children <;> rfl

/-- A structural node that fits has a type tree. -/
theorem createTT_some {x : Cond} {d m : Condition} (h : Fits avatar x d m) :
    d = D avatar x → isStruct x = true → (Normalize.createTT x).isSome = true := by
  induction h with
  | @pass c d m _ _ _ _ _ _ hp =>
    intro hd _; obtain ⟨t, ht, -⟩ := pdesc_tt avatar (hp hd); simp [ht]
  | ns hs => intro _ h; rw [hs] at h; exact absurd h (by simp)
  | @logical c d m hop he hs _ _ _ _ ih =>
    intro _ _
    have ih' : ∀ y ∈ c.ch, isStruct y = true → (Normalize.createTT y).isSome = true :=
      fun y hy hys => ih y hy rfl hys
    have hany : ∃ y ∈ c.ch, isStruct y = true := by
      rw [isStruct_eq] at hs
      have : (c.op == 1 || c.op == 2) = true := by rcases hop with h | h <;> simp [h]
      rw [this] at hs; simpa using hs
    rcases c with ⟨e, o, cv, ch⟩; simp only at hop ih' hany ⊢
    rw [createTT_mk]
    have : (o == 1 || o == 2) = true := by rcases hop with h | h <;> simp [h]
    rw [this]; simp only [ite_true]
    exact createTTFirst_some ih' hany
  | @tup c d m h5 he =>
    intro _ _
    rcases c with ⟨e, o, cv, ch⟩; simp only at h5 he; subst h5
    rw [createTT_mk]; rcases he with rfl | rfl <;> rfl
  | @arr c d m hop he _ _ _ hne hs _ _ ih =>
    intro _ _
    obtain ⟨x0, xs, hch⟩ : ∃ x0 xs, c.ch = x0 :: xs := by
      cases h' : c.ch with
      | nil => exact absurd h' hne
      | cons x0 xs => exact ⟨x0, xs, rfl⟩
    have hx0 : x0 ∈ c.ch := by rw [hch]; simp
    have hx0s := ih x0 hx0 rfl (hs x0 hx0)
    rcases c with ⟨e, o, cv, ch⟩; simp only at hop he hch; subst he hch
    rw [createTT_mk]
    have h12 : (o == 1 || o == 2) = false := by simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne]; omega
    rw [h12]; simp only [Bool.false_eq_true, ite_false, ite_true]
    obtain ⟨t, ht⟩ := Option.isSome_iff_exists.1 hx0s
    simp [ht]
  | @slice c d m x hop he =>
    intro _ _
    rcases c with ⟨e, o, cv, ch⟩; simp only at hop he; subst hop
    rw [createTT_mk]; rcases he with rfl | rfl <;> rfl
  | @leaf c d m hop hs _ _ henc _ _ _ hpd hne4 hnl hle =>
    intro _ _
    have hne := leafOp_ne hop
    rcases c with ⟨e, o, cv, ch⟩; simp only at hop hs henc hpd hne4 hnl hne hle ⊢
    rw [createTT_mk]
    have h12 : (o == 1 || o == 2) = false := by simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne]; omega
    rw [h12]; simp only [Bool.false_eq_true, ite_false]
    have hse := struct_enc (c := ⟨e, o, cv, ch⟩) hs hne.2.1 hne.2.2.1
    simp only at hse
    by_cases h4 : e = 4
    · subst h4
      obtain ⟨x0, xs, hch⟩ : ∃ x0 xs, ch = x0 :: xs := by
        cases h' : ch with
        | nil => exact absurd h' (hne4 rfl)
        | cons x0 xs => exact ⟨x0, xs, rfl⟩
      subst hch
      obtain ⟨t, ht, -⟩ := pdesc_tt avatar (hpd 0 (by simp))
      simp only [beq_self_eq_true, ite_true]
      simp only [List.getElem_cons_zero] at ht
      simp [ht]
    · simp only [beq_iff_eq, h4, ite_false]
      split
      · rfl
      · split
        · rfl
        · rename_i h35 h12'
          exfalso
          simp only [Bool.or_eq_true, beq_iff_eq] at h35 h12'
          omega

/-- The `Pass` rendering of a container's type tree describes its layout. -/
theorem container_tt {c : Cond} {m : Condition} (he : c.enc = 3 ∨ c.enc = 5)
    (hm : (D avatar c).encoding = m.encoding) (hk : c.ch.length ≤ m.children.length)
    (hraw : ∀ i (h : i < c.ch.length), isInl c.ch[i] = (m.children.getD i default).inlined ∧
      (isInl c.ch[i] = true → rawSz avatar c.ch[i] = (m.children.getD i default).size))
    (hsome : ∀ x ∈ c.ch, (Normalize.createTT x).isSome = true)
    (hch : ∀ i (h : i < c.ch.length) t, Normalize.createTT c.ch[i] = some t →
      PDesc avatar (passFor t) (m.children.getD i default))
    (hl : LayEq (D avatar c) m) (hs : Sane avatar c) :
    PDesc avatar (passFor (.mk c.enc (createTTL c.ch))) m := by
  obtain ⟨ts, hts, hlen, hget⟩ := filterMap_some c.ch hsome
  rw [createTTL_eq, hts]
  have hpf : passFor (.mk c.enc ts) = ⟨c.enc, 0, [], ts.map passFor⟩ := by
    rw [passFor_mk]; rcases he with h | h <;> simp [h]
  rw [hpf]
  have hchild : ∀ i (h1 : i < (ts.map passFor).length),
      PDesc avatar (ts.map passFor)[i] (m.children.getD i default) := by
    intro i h1
    have h1' : i < c.ch.length := by simp at h1; omega
    simp only [List.getElem_map]
    exact hch i h1' _ (hget i h1' (by simp at h1; exact h1))
  have hr := container_raw avatar (c := c) (c' := ⟨c.enc, 0, [], ts.map passFor⟩) rfl
    (by simp [hlen]) (fun i h1 h2 => by
      have r1 := hraw i h1
      have r2 := (hchild i h2).raw avatar
      exact ⟨r1.1.trans r2.1.symm,
        fun hi => (r1.2 hi).trans (r2.2.1 (r2.1.trans (r1.1.symm.trans hi))).symm⟩)
  obtain ⟨hsn', hl'⟩ := lay_transfer avatar hr hs hl
  exact .tup rfl he ((D_encoding_same avatar (c := ⟨c.enc, 0, [], ts.map passFor⟩) (c' := c) rfl).trans hm)
    (by simp [hlen]; exact hk) hchild hl' hsn'

theorem TyEq.children_length {c : Cond} {m : Condition} (h : TyEq (D avatar c) m) :
    c.ch.length = m.children.length := by
  cases h with
  | mk _ _ hl => have := hl.length; rw [D_children] at this; simpa using this

/-- The type tree of a node that fits `m` describes `m` (a prefix of it). -/
theorem createTT_fits {x : Cond} {d m : Condition} (h : Fits avatar x d m) :
    d = D avatar x → ∀ t, Normalize.createTT x = some t → PDesc avatar (passFor t) m := by
  induction h with
  | @pass c d m _ _ _ _ _ _ hp =>
    intro hd t ht
    obtain ⟨t', ht', hp'⟩ := pdesc_tt avatar (hp hd)
    rw [ht'] at ht; simp only [Option.some.injEq] at ht; subst ht; exact hp'
  | @ns c d m _ hns _ =>
    intro _ t ht; rw [hns.createTT] at ht; exact absurd ht (by simp)
  | @logical c d m hop he hs _ _ _ _ ih =>
    intro _ t ht
    have hc : Normalize.createTT c = createTTFirst c.ch := by
      rcases c with ⟨e, o, cv, ch⟩; simp only at hop
      rw [createTT_mk]
      have : (o == 1 || o == 2) = true := by rcases hop with h | h <;> simp [h]
      simp [this]
    rw [hc] at ht
    obtain ⟨y, hy, -, hyt⟩ := createTTFirst_spec ht
    exact ih y hy rfl t hyt
  | @tup c d m h5 he hd' hm hl _ hs hk hch hsn ih =>
    intro hd t ht
    subst hd
    have hc : Normalize.createTT c = some (.mk c.enc (createTTL c.ch)) := by
      rcases c with ⟨e, o, cv, ch⟩; simp only at h5 he; subst h5
      rw [createTT_mk]; rcases he with rfl | rfl <;> rfl
    rw [hc] at ht; simp only [Option.some.injEq] at ht; subst ht
    exact container_tt avatar he hm hk
      (fun i h => by
        have r := (hch i h).raw avatar (hs _ (List.getElem_mem h)); exact ⟨r.1, r.2.1⟩)
      (fun x hx => by
        obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
        exact createTT_some avatar (hch i hi) rfl (hs _ (List.getElem_mem hi)))
      (fun i h t ht => ih i h rfl t ht) hl hsn
  | @arr c d m hop he hd' hm hl hne hs hch hsn ih =>
    intro hd t ht
    subst hd
    obtain ⟨x0, xs, hc0⟩ : ∃ x0 xs, c.ch = x0 :: xs := by
      cases h' : c.ch with
      | nil => exact absurd h' hne
      | cons x0 xs => exact ⟨x0, xs, rfl⟩
    have hx0 : x0 ∈ c.ch := by rw [hc0]; simp
    have hc : Normalize.createTT c = (Normalize.createTT x0).map fun t => .mk 4 [t] := by
      rcases c with ⟨e, o, cv, ch⟩; simp only at hop he hc0; subst he hc0
      rw [createTT_mk]
      have : (o == 1 || o == 2) = false := by simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne]; omega
      simp [this]
    rw [hc] at ht
    obtain ⟨t0, ht0, rfl⟩ := Option.map_eq_some_iff.1 ht
    have hp0 := ih x0 hx0 rfl t0 ht0
    have hpf : passFor (.mk 4 [t0]) = ⟨4, 0, [], [passFor t0]⟩ := by rw [passFor_mk]; rfl
    rw [hpf]
    have hraw : isInl c = isInl ⟨4, 0, [], [passFor t0]⟩ ∧
        (isInl c = true → rawSz avatar c = rawSz avatar ⟨4, 0, [], [passFor t0]⟩) := by
      have h1 : isInl c = false := by rw [isInl_eq, he]; rfl
      have h2 : isInl (⟨4, 0, [], [passFor t0]⟩ : Cond) = false := by rw [isInl_eq]; rfl
      rw [h1, h2]; simp
    obtain ⟨hsn', hl'⟩ := lay_transfer avatar hraw hsn hl
    exact .arr rfl rfl rfl hm hp0 hl' hsn'
  | @slice c d m x hop he hnode hl hch _ _ hsn hst _ =>
    intro hd t ht
    subst hd
    have hc : Normalize.createTT c = some (.mk c.enc []) := by
      rcases c with ⟨e, o, cv, ch⟩; simp only at hop he; subst hop
      rw [createTT_mk]; rcases he with rfl | rfl <;> rfl
    rw [hc] at ht; simp only [Option.some.injEq] at ht; subst ht
    have hpf : passFor (.mk c.enc []) = ⟨c.enc, 0, [], []⟩ := by
      rw [passFor_mk]; rcases he with h | h <;> simp [h]
    rw [hpf]
    have hraw : isInl c = isInl ⟨c.enc, 0, [], []⟩ ∧
        (isInl c = true → rawSz avatar c = rawSz avatar ⟨c.enc, 0, [], []⟩) := by
      rcases he with h | h
      · have h1 := hst h
        have h2 : isInl (⟨c.enc, 0, [], []⟩ : Cond) = true := by rw [isInl_eq]; simp [h]
        rw [h1, h2]
        refine ⟨rfl, fun _ => ?_⟩
        rw [rawSz_eq, rawSz_eq]; simp [h]
      · have h1 : isInl c = false := by rw [isInl_eq]; simp [h]
        have h2 : isInl (⟨c.enc, 0, [], []⟩ : Cond) = false := by rw [isInl_eq]; simp [h]
        rw [h1, h2]; simp
    obtain ⟨hsn', hl'⟩ := lay_transfer avatar hraw hsn hl
    exact .leaf rfl he rfl hl' hsn'
  | @leaf c d m hop hs hnode hty henc _ _ hsn hpd hne4 hnl hle =>
    intro hd t ht
    subst hd
    have hne := leafOp_ne hop
    have hse := struct_enc hs hne.2.1 hne.2.2.1
    have h12 : (c.op == 1 || c.op == 2) = false := by
      simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne]; omega
    have hl := hty.layEq
    by_cases h12e : c.enc = 1 ∨ c.enc = 2
    · have hch := hnl h12e
      have hc : Normalize.createTT c = some (.mk c.enc []) := by
        rcases c with ⟨e, o, cv, ch⟩; simp only at h12e h12 ⊢
        rw [createTT_mk, h12]; rcases h12e with rfl | rfl <;> rfl
      rw [hc] at ht; simp only [Option.some.injEq] at ht; subst ht
      have hpf : passFor (.mk c.enc []) = ⟨c.enc, 0, [], []⟩ := by
        rw [passFor_mk]; rcases h12e with h | h <;> simp [h]
      rw [hpf]
      have hm := D_meta_same avatar (c := ⟨c.enc, 0, [], []⟩) (c' := c) rfl (by rw [hch])
      have hr := raw_same avatar (c := ⟨c.enc, 0, [], []⟩) (c' := c) rfl (by rw [hch])
      refine .leaf rfl h12e rfl ⟨hm.1.trans hl.1, hm.2.trans hl.2⟩ ?_
      rw [hr.1, hsn, hm.1]
    by_cases h4 : c.enc = 4
    · obtain ⟨x0, xs, hc0⟩ : ∃ x0 xs, c.ch = x0 :: xs := by
        cases h' : c.ch with
        | nil => exact absurd h' (hne4 h4)
        | cons x0 xs => exact ⟨x0, xs, rfl⟩
      have hp0 : PDesc avatar x0 (tmpl m) := by
        have := hpd 0 (by rw [hc0]; simp)
        simp only [hc0, List.getElem_cons_zero] at this
        rw [tmpl_eq]; exact this
      obtain ⟨t0, ht0, hpt0⟩ := pdesc_tt avatar hp0
      have hc : Normalize.createTT c = some (.mk 4 [t0]) := by
        rcases c with ⟨e, o, cv, ch⟩; simp only at h4 hc0 h12; subst h4 hc0
        rw [createTT_mk, h12]; simp [ht0]
      rw [hc] at ht; simp only [Option.some.injEq] at ht; subst ht
      have hpf : passFor (.mk 4 [t0]) = ⟨4, 0, [], [passFor t0]⟩ := by rw [passFor_mk]; rfl
      rw [hpf]
      have hm : m.encoding = .Array := by rw [← hty.encoding, D_encoding_of avatar (by omega), h4]; rfl
      have hraw : isInl c = isInl ⟨4, 0, [], [passFor t0]⟩ ∧
          (isInl c = true → rawSz avatar c = rawSz avatar ⟨4, 0, [], [passFor t0]⟩) := by
        have h1 : isInl c = false := by rw [isInl_eq, h4]; rfl
        have h2 : isInl (⟨4, 0, [], [passFor t0]⟩ : Cond) = false := by rw [isInl_eq]; rfl
        rw [h1, h2]; simp
      obtain ⟨hsn', hl'⟩ := lay_transfer avatar hraw hsn hl
      exact .arr rfl rfl rfl hm hpt0 hl' hsn'
    · have h3 : c.enc = 3 := by omega
      have hc : Normalize.createTT c = some (.mk c.enc (createTTL c.ch)) := by
        rcases c with ⟨e, o, cv, ch⟩; simp only at h3 h12; subst h3
        rw [createTT_mk, h12]; rfl
      rw [hc] at ht; simp only [Option.some.injEq] at ht; subst ht
      have hk := TyEq.children_length avatar hty
      exact container_tt avatar (Or.inl h3) hty.encoding (by omega)
        (fun i h => by have r := (hpd i h).raw avatar; exact ⟨r.1, r.2.1⟩)
        (fun x hx => by
          obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
          obtain ⟨t, ht, -⟩ := pdesc_tt avatar (hpd i hi); simp [ht])
        (fun i h t ht => by
          obtain ⟨t', ht', hp'⟩ := pdesc_tt avatar (hpd i h)
          rw [ht'] at ht; simp only [Option.some.injEq] at ht; subst ht; exact hp')
        hl hsn

/-! ## Extending -/

theorem extendS_struct : ∀ (xs : List Cond) (ts : List TT), (∀ x ∈ xs, isStruct x = true) →
    extendS xs ts = List.zipWith (fun x t => extendC x t false) xs ts ++ xs.drop ts.length ++
      (ts.drop xs.length).map passFor
  | [], ts, _ => by rw [extendS, passForL_eq]; simp
  | x :: xs, [], h => by
    rw [extendS, extendS_struct xs [] (fun y hy => h y (by simp [hy]))]
    simp
  | x :: xs, t :: ts, h => by
    rw [extendS, ite_pos' (h x (by simp)), extendS_struct xs ts (fun y hy => h y (by simp [hy]))]
    simp

theorem extendS_length (xs : List Cond) (ts : List TT) (h : ∀ x ∈ xs, isStruct x = true) :
    (extendS xs ts).length = max xs.length ts.length := by
  rw [extendS_struct xs ts h]
  simp; omega

theorem extendS_get? : ∀ (xs : List Cond) (ts : List TT) (i : Nat), (∀ x ∈ xs, isStruct x = true) →
    (extendS xs ts)[i]? =
      if i < xs.length then (if i < ts.length then (xs[i]?).bind fun x => (ts[i]?).map (extendC x · false)
        else xs[i]?)
      else ts[i]?.map passFor
  | [], ts, i, _ => by rw [extendS, passForL_eq]; simp [List.getElem?_map]
  | x :: xs, [], i, h => by
    rw [extendS]
    cases i with
    | zero => simp
    | succ i =>
      simp only [List.getElem?_cons_succ, List.length_cons]
      rw [extendS_get? xs [] i (fun y hy => h y (by simp [hy]))]
      simp
  | x :: xs, t :: ts, i, h => by
    rw [extendS, ite_pos' (h x (by simp))]
    cases i with
    | zero => simp
    | succ i =>
      simp only [List.getElem?_cons_succ, List.length_cons]
      rw [extendS_get? xs ts i (fun y hy => h y (by simp [hy]))]
      simp only [Nat.add_lt_add_iff_right]

theorem any_congr_mem {α} {f g : α → Bool} : ∀ {l : List α}, (∀ x ∈ l, f x = g x) → l.any f = l.any g
  | [], _ => rfl
  | x :: xs, h => by
    have ih : xs.any f = xs.any g := any_congr_mem (l := xs) (fun y hy => h y (List.mem_cons_of_mem _ hy))
    simp only [List.any_cons, h x (by simp), ih]

theorem isStruct_extendC (x : Cond) (t : TT) (v : Bool) : isStruct (extendC x t v) = isStruct x := by
  rw [extendC]
  split
  · rename_i hlog
    have hop := logical_op hlog
    rw [isStruct_eq, isStruct_eq]
    simp only
    have : (x.op == 1 || x.op == 2) = true := by rcases hop with h | h <;> simp [h]
    rw [this]; simp only [ite_true]
    rw [extendAll_eq, List.any_map]
    exact any_congr_mem fun y hy => isStruct_extendC y t v
  · rename_i hlog
    have h12 : (x.op == 1 || x.op == 2) = false := by
      simp only [isLogical, Bool.not_eq_true] at hlog; exact hlog
    split
    · rfl
    · split
      · rw [isStruct_eq, isStruct_eq]; simp only [h12]; rfl
      · rfl
termination_by sizeOf x
decreasing_by exact sizeOf_lt_of_mem hy

theorem extendS_cases (xs : List Cond) (ts : List TT) (h : ∀ x ∈ xs, isStruct x = true) (i : Nat)
    (hi : i < (extendS xs ts).length) :
    (∃ (h1 : i < xs.length) (h2 : i < ts.length), (extendS xs ts)[i] = extendC xs[i] ts[i] false) ∨
    (∃ (h1 : i < xs.length), ts.length ≤ i ∧ (extendS xs ts)[i] = xs[i]) ∨
    (∃ (h2 : i < ts.length), xs.length ≤ i ∧ (extendS xs ts)[i] = passFor ts[i]) := by
  have e := extendS_get? xs ts i h
  rw [List.getElem?_eq_getElem hi] at e
  split at e
  · rename_i h1
    split at e
    · rename_i h2
      left
      refine ⟨h1, h2, ?_⟩
      rw [List.getElem?_eq_getElem h1, List.getElem?_eq_getElem h2] at e
      simpa using e
    · rename_i h2
      right; left
      refine ⟨h1, by omega, ?_⟩
      rw [List.getElem?_eq_getElem h1] at e
      simpa using e
  · rename_i h1
    right; right
    have h2 : i < ts.length := by
      have := extendS_length xs ts h; rw [this] at hi; omega
    refine ⟨h2, by omega, ?_⟩
    rw [List.getElem?_eq_getElem h2] at e
    simpa using e

theorem extendS_id (xs : List Cond) (ts : List TT) (h : ∀ x ∈ xs, isStruct x = true)
    (hl : ts.length ≤ xs.length)
    (hid : ∀ i (h1 : i < xs.length) (h2 : i < ts.length), extendC xs[i] ts[i] false = xs[i]) :
    extendS xs ts = xs := by
  apply List.ext_getElem?
  intro i
  rw [extendS_get? xs ts i h]
  split
  · rename_i h1
    split
    · rename_i h2
      rw [List.getElem?_eq_getElem h1, List.getElem?_eq_getElem h2]
      simp [hid i h1 h2]
    · rfl
  · rename_i h1
    rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]; rfl

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

theorem pdesc_passFor_tup {t : TT} {m : Condition} (h : PDesc avatar (passFor t) m) (he : t.enc = 3 ∨ t.enc = 5) :
    t.ch.length ≤ m.children.length ∧
      ∀ i (h1 : i < t.ch.length), PDesc avatar (passFor t.ch[i]) (m.children.getD i default) := by
  rcases t with ⟨e, ts⟩
  simp only [TT.enc, TT.ch] at he ⊢
  rw [passFor_mk] at h
  have hif : (if (e == 3 || e == 4 || e == 5) = true then ts.map passFor else []) = ts.map passFor := by
    rcases he with rfl | rfl <;> rfl
  rw [hif] at h
  cases h with
  | leaf _ he' => exfalso; simp at he'; omega
  | arr _ he' => exfalso; simp at he'; omega
  | tup _ _ _ hk hch _ _ =>
    simp only [List.length_map] at hk hch
    refine ⟨hk, fun i h1 => ?_⟩
    have := hch i (by simpa using h1)
    simpa using this

theorem pdesc_passFor_arr {t : TT} {m : Condition} (h : PDesc avatar (passFor t) m) (he : t.enc = 4) :
    ∃ t0, t.ch = [t0] ∧ PDesc avatar (passFor t0) (tmpl m) ∧ m.encoding = .Array := by
  rcases t with ⟨e, ts⟩
  simp only [TT.enc, TT.ch] at he ⊢
  subst he
  rw [passFor_mk] at h
  simp only [beq_self_eq_true, Bool.or_true, Bool.true_or, ite_true] at h
  cases h with
  | leaf _ he' => exfalso; simp at he'
  | tup _ he' => exfalso; simp at he'
  | arr _ _ hch hm hx _ _ =>
    simp only at hch
    cases ts with
    | nil => simp at hch
    | cons t0 rest =>
      cases rest with
      | nil =>
        simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hch
        subst hch; exact ⟨t0, rfl, hx, hm⟩
      | cons _ _ => simp at hch

theorem extendC_ns : ∀ {x : Cond}, NsOk x → ∀ t v, NsOk (extendC x t v) := by
  intro x h
  induction h with
  | @leaf c he hch hop =>
    intro t v
    rw [extendC]
    have hlog : isLogical c = false := by
      simp only [nsOp, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq] at hop
      simp only [isLogical, Bool.or_eq_false_iff, beq_eq_false_iff_ne]; omega
    have hcx : isComplex c = false := by
      simp only [isComplex, Bool.or_eq_false_iff, beq_eq_false_iff_ne]; omega
    simp only [hlog, hcx, Bool.false_and, Bool.false_eq_true, ite_false]
    split
    · exact .leaf he hch hop
    · exact .leaf he hch hop
  | @logical c hop he hall ih =>
    intro t v
    rw [extendC]
    have hlog : isLogical c = true := by simp [isLogical]; omega
    rw [ite_pos' hlog, extendAll_eq]
    exact .logical hop he fun y hy => by
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy; exact ih x hx t v

/-- A node that already lists all of its layout's fields stays as it is. -/
theorem extendC_exact : ∀ {c : Cond} {mm : Condition}, PDesc avatar c mm → TyEq (D avatar c) mm →
    ∀ t v, PDesc avatar (passFor t) mm → extendC c t v = c := by
  intro c mm h
  induction h with
  | @leaf c m h0 he hch _ _ =>
    intro _ t v _
    rw [extendC]
    have hlog : isLogical c = false := by simp [isLogical, h0]
    have hcx : isComplex c = false := by simp [isComplex]; omega
    simp only [hlog, hcx, Bool.false_and, Bool.false_eq_true, ite_false]
    split <;> rfl
  | @tup c m h0 he hm hk hch hl hs ih =>
    intro hty t v ht
    rw [extendC]
    have hlog : isLogical c = false := by simp [isLogical, h0]
    rw [ite_neg' (by simp [hlog])]
    split
    · rfl
    split
    · rename_i _ hc
      simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hc
      obtain ⟨⟨_, het⟩, _⟩ := hc
      have hte : t.enc = 3 ∨ t.enc = 5 := by omega
      obtain ⟨htk, htch⟩ := pdesc_passFor_tup avatar ht hte
      have hcl := TyEq.children_length avatar hty
      have hst : ∀ x ∈ c.ch, isStruct x = true := by
        intro x hx
        obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
        exact isStruct_pass (hch i hi).op (hch i hi).enc
      rw [extendS_id c.ch t.ch hst (by omega) (fun i h1 h2 =>
        ih i h1 (hty.child avatar i h1) t.ch[i] false (htch i h2))]
      cases c; rfl
    · rfl
  | @arr c m x h0 he hch hm hx hl hs ih =>
    intro hty t v ht
    rw [extendC]
    have hlog : isLogical c = false := by simp [isLogical, h0]
    rw [ite_neg' (by simp [hlog])]
    split
    · rfl
    split
    · rename_i _ hc
      simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hc
      obtain ⟨⟨_, het⟩, _⟩ := hc
      obtain ⟨t0, ht0, hp0, _⟩ := pdesc_passFor_arr avatar ht (by omega)
      have hx0 : TyEq (D avatar x) (tmpl m) := by
        have := hty.child avatar 0 (by rw [hch]; simp)
        simp only [hch, List.getElem_cons_zero] at this
        rw [tmpl_eq]; exact this
      have hext : extendS c.ch t.ch = c.ch := by
        rw [hch, ht0, extendS, ite_pos' (isStruct_pass hx.op hx.enc), ih hx0 t0 false hp0, extendS,
          passForL_eq]
        rfl
      rw [hext]; cases c; rfl
    · rfl

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

theorem extendC_pdesc : ∀ {x : Cond} {m : Condition}, PDesc avatar x m →
    ∀ t v, PDesc avatar (passFor t) m → PDesc avatar (extendC x t v) m := by
  intro x m h
  induction h with
  | @leaf c m h0 he hch hl hs =>
    intro t v _
    rw [extendC]
    have hlog : isLogical c = false := by simp [isLogical, h0]
    have hcx : isComplex c = false := by simp [isComplex]; omega
    simp only [hlog, hcx, Bool.false_and, Bool.false_eq_true, ite_false]
    split <;> exact .leaf h0 he hch hl hs
  | @tup c m h0 he hm hk hch hl hs ih =>
    intro t v ht
    have h0' := PDesc.tup (avatar := avatar) h0 he hm hk hch hl hs
    rw [extendC]
    have hlog : isLogical c = false := by simp [isLogical, h0]
    rw [ite_neg' (by simp [hlog])]
    split
    · exact h0'
    split
    · rename_i _ hc
      simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hc
      obtain ⟨⟨_, het⟩, hni⟩ := hc
      have hte : t.enc = 3 ∨ t.enc = 5 := by omega
      obtain ⟨htk, htch⟩ := pdesc_passFor_tup avatar ht hte
      have hst : ∀ x ∈ c.ch, isStruct x = true := by
        intro x hx
        obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
        exact isStruct_pass (hch i hi).op (hch i hi).enc
      have hlen := extendS_length c.ch t.ch hst
      have hchild : ∀ i (h1 : i < (extendS c.ch t.ch).length),
          PDesc avatar (extendS c.ch t.ch)[i] (m.children.getD i default) := by
        intro i h1
        rcases extendS_cases c.ch t.ch hst i h1 with ⟨a, b, e⟩ | ⟨a, _, e⟩ | ⟨b, _, e⟩
        · rw [e]; exact ih i a t.ch[i] false (htch i b)
        · rw [e]; exact hch i a
        · rw [e]; exact htch i b
      have hni' : isInl { c with ch := extendS c.ch t.ch } = false := by
        apply notInl_of_child (c := c) (c' := { c with ch := extendS c.ch t.ch }) rfl
          (by show c.ch.length ≤ (extendS c.ch t.ch).length; omega) hni
        intro k h1 h2
        rw [((hchild k h2).raw avatar).1, ((hch k h1).raw avatar).1]
      obtain ⟨hsn', hl'⟩ := lay_transfer avatar (c := c) (c' := { c with ch := extendS c.ch t.ch })
        ⟨hni.trans hni'.symm, fun h => by rw [hni] at h; exact absurd h (by simp)⟩ hs hl
      exact .tup h0 he (by rw [D_encoding_withCh]; exact hm) (by simp only; omega) hchild hl' hsn'
    · exact h0'
  | @arr c m x h0 he hch hm hx hl hs ih =>
    intro t v ht
    have h0' := PDesc.arr (avatar := avatar) h0 he hch hm hx hl hs
    rw [extendC]
    have hlog : isLogical c = false := by simp [isLogical, h0]
    rw [ite_neg' (by simp [hlog])]
    split
    · exact h0'
    split
    · rename_i _ hc
      simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hc
      obtain ⟨⟨_, het⟩, _⟩ := hc
      obtain ⟨t0, ht0, hp0, _⟩ := pdesc_passFor_arr avatar ht (by omega)
      have hext : extendS c.ch t.ch = [extendC x t0 false] := by
        rw [hch, ht0, extendS, ite_pos' (isStruct_pass hx.op hx.enc), extendS, passForL_eq]; rfl
      rw [hext]
      have hraw : isInl c = isInl { c with ch := [extendC x t0 false] } ∧
          (isInl c = true → rawSz avatar c = rawSz avatar { c with ch := [extendC x t0 false] }) := by
        have h1 : isInl c = false := by rw [isInl_eq, he]; rfl
        have h2 : isInl ({ c with ch := [extendC x t0 false] } : Cond) = false := by
          rw [isInl_eq]; simp [he]
        rw [h1, h2]; simp
      obtain ⟨hsn', hl'⟩ := lay_transfer avatar hraw hs hl
      exact .arr h0 he rfl hm (ih t0 false hp0) hl' hsn'
    · exact h0'

/-- Extending a node that fits `m` with a description of `m` keeps it fitting. -/
theorem extendC_fits {x : Cond} {d m : Condition} (h : Fits avatar x d m) :
    d = D avatar x → ∀ t v, PDesc avatar (passFor t) m → F (extendC x t v) m := by
  have h0 := h
  induction h with
  | pass _ _ _ _ _ _ hp =>
    intro hd t v ht; exact (extendC_pdesc avatar (hp hd) t v ht).fits avatar
  | @ns c d m _ hns _ =>
    intro _ t v _
    have := extendC_ns hns t v
    exact .ns this.isStruct this rfl
  | @logical c d m hop he _ _ _ hch _ ih =>
    intro _ t v _
    rw [extendC]
    have hlog : isLogical c = true := by simp [isLogical]; omega
    rw [ite_pos' hlog, extendAll_eq]
    apply logical_withCh avatar (c := c) hop he
    intro y hy
    obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hy
    exact ih z hz (hch z hz) rfl t v ‹_›
  | @tup c d m h5 he hd hm hl hlb hs hk hch hsn ih =>
    intro hd' t v ht
    subst hd'
    rw [extendC]
    have hlog : isLogical c = false := by simp [isLogical]; omega
    rw [ite_neg' (by simp [hlog])]
    split
    · exact h0
    split
    · rename_i _ hc
      simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hc
      obtain ⟨⟨_, het⟩, hni⟩ := hc
      have hte : t.enc = 3 ∨ t.enc = 5 := by omega
      obtain ⟨htk, htch⟩ := pdesc_passFor_tup avatar ht hte
      have hlen := extendS_length c.ch t.ch hs
      have hchild : ∀ i (h1 : i < (extendS c.ch t.ch).length),
          F (extendS c.ch t.ch)[i] (m.children.getD i default) := by
        intro i h1
        rcases extendS_cases c.ch t.ch hs i h1 with ⟨a, b, e⟩ | ⟨a, _, e⟩ | ⟨b, _, e⟩
        · rw [e]; exact ih i a (hch i a) rfl t.ch[i] false (htch i b)
        · rw [e]; exact hch i a
        · rw [e]; exact (htch i b).fits avatar
      have hst : ∀ y ∈ extendS c.ch t.ch, isStruct y = true := by
        intro y hy
        obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hy
        rcases extendS_cases c.ch t.ch hs i hi with ⟨a, b, e⟩ | ⟨a, _, e⟩ | ⟨b, _, e⟩
        · rw [e, isStruct_extendC]; exact hs _ (List.getElem_mem a)
        · rw [e]; exact hs _ (List.getElem_mem a)
        · rw [e]; exact isStruct_pass (htch i b).op (htch i b).enc
      have hni' : isInl { c with ch := extendS c.ch t.ch } = false := by
        apply notInl_of_child (c := c) (c' := { c with ch := extendS c.ch t.ch }) rfl
          (by show c.ch.length ≤ (extendS c.ch t.ch).length; omega) hni
        intro k h1 h2
        rw [((hchild k h2).raw avatar (hst _ (List.getElem_mem h2))).1,
          ((hch k h1).raw avatar (hs _ (List.getElem_mem h1))).1]
      obtain ⟨hsn', hl'⟩ := lay_transfer avatar (c := c) (c' := { c with ch := extendS c.ch t.ch })
        ⟨hni.trans hni'.symm, fun h => by rw [hni] at h; exact absurd h (by simp)⟩ hsn hl
      exact .tup h5 he rfl (by rw [D_encoding_withCh]; exact hm) hl' (by rw [D_leadingBytes_withCh]; exact hlb)
        hst (by simp only; omega) hchild hsn'
    · exact h0
  | @arr c d m hop he hd hm hl hne hs hch hsn ih =>
    intro hd' t v ht
    subst hd'
    rw [extendC]
    have hlog : isLogical c = false := by simp [isLogical]; omega
    rw [ite_neg' (by simp [hlog])]
    split
    · exact h0
    split
    · rename_i _ hc
      simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hc
      obtain ⟨⟨_, het⟩, _⟩ := hc
      obtain ⟨t0, ht0, hp0, _⟩ := pdesc_passFor_arr avatar ht (by omega)
      obtain ⟨x0, xs, hc0⟩ : ∃ x0 xs, c.ch = x0 :: xs := by
        cases h' : c.ch with
        | nil => exact absurd h' hne
        | cons x0 xs => exact ⟨x0, xs, rfl⟩
      have hx0 : x0 ∈ c.ch := by rw [hc0]; simp
      have hxs : ∀ y ∈ xs, isStruct y = true := fun y hy => hs y (by rw [hc0]; simp [hy])
      have hext : extendS c.ch t.ch = extendC x0 t0 false :: xs := by
        rw [hc0, ht0, extendS, ite_pos' (hs x0 hx0), extendS_struct xs [] hxs]; simp
      rw [hext]
      have hraw : isInl c = isInl { c with ch := extendC x0 t0 false :: xs } ∧
          (isInl c = true → rawSz avatar c = rawSz avatar { c with ch := extendC x0 t0 false :: xs }) := by
        have h1 : isInl c = false := by rw [isInl_eq, he]; rfl
        have h2 : isInl ({ c with ch := extendC x0 t0 false :: xs } : Cond) = false := by
          rw [isInl_eq]; simp [he]
        rw [h1, h2]; simp
      obtain ⟨hsn', hl'⟩ := lay_transfer avatar hraw hsn hl
      refine .arr hop he rfl hm hl' (by simp) ?_ ?_ hsn'
      · intro y hy
        rcases List.mem_cons.1 hy with rfl | hy
        · rw [isStruct_extendC]; exact hs x0 hx0
        · exact hxs y hy
      · intro y hy
        rcases List.mem_cons.1 hy with rfl | hy
        · exact ih x0 hx0 (hch x0 hx0) rfl t0 false hp0
        · exact hch y (by rw [hc0]; simp [hy])
    · exact h0
  | @slice c d m x hop he =>
    intro hd t v _
    subst hd
    rw [extendC]
    have hlog : isLogical c = false := by simp [isLogical]; omega
    have hcx : isComplex c = false := by simp [isComplex]; omega
    simp only [hlog, hcx, Bool.false_and, Bool.false_eq_true, ite_false]
    split <;> exact h0
  | @leaf c d m hop hs hnode hty henc _ _ _ hpd hne4 hnl hle =>
    intro hd t v ht
    subst hd
    rw [extendC]
    have hne := leafOp_ne hop
    have hlog : isLogical c = false := by simp [isLogical]; omega
    rw [ite_neg' (by simp [hlog])]
    split
    · exact h0
    split
    · rename_i _ hc
      simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', isComplex, Bool.or_eq_true] at hc
      obtain ⟨⟨hcx, het⟩, _⟩ := hc
      have hcl := TyEq.children_length avatar hty
      have hst : ∀ y ∈ c.ch, isStruct y = true := by
        intro y hy
        obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hy
        exact isStruct_pass (hpd i hi).op (hpd i hi).enc
      have hid : extendS c.ch t.ch = c.ch := by
        by_cases h4 : c.enc = 4
        · obtain ⟨t0, ht0, hp0, _⟩ := pdesc_passFor_arr avatar ht (by omega)
          apply extendS_id c.ch t.ch hst (by
            rw [ht0]; have := hne4 h4
            cases hcc : c.ch with
            | nil => exact absurd hcc this
            | cons _ _ => simp)
          intro i h1 h2
          rw [ht0] at h2; simp at h2; subst h2
          have hp := hpd 0 h1
          have := extendC_exact avatar hp (hty.child avatar 0 h1) t0 false (by
            rw [← tmpl_eq]; exact hp0)
          simpa [ht0] using this
        · have hte : t.enc = 3 ∨ t.enc = 5 := by omega
          obtain ⟨htk, htch⟩ := pdesc_passFor_tup avatar ht hte
          exact extendS_id c.ch t.ch hst (by omega) fun i h1 h2 =>
            extendC_exact avatar (hpd i h1) (hty.child avatar i h1) t.ch[i] false (htch i h2)
      rw [hid]; cases c; exact h0
    · exact h0

/-! ## The padding loop -/

theorem getElem!_mem {l : List Cond} {i : Nat} (h : i < l.length) : l[i]! ∈ l := by
  rw [getElem!_eq h]; exact List.getElem_mem h

theorem createTT_default : Normalize.createTT (default : Cond) = none := by decide

/-- What the padding loop keeps. -/
def PadI (cs : List Cond) (m : Condition) (acc : List Cond) : Prop :=
  acc.length = cs.length ∧ (∀ x ∈ acc, F x m) ∧
    ((∀ x ∈ cs, isStruct x = true) → ∀ x ∈ acc, isStruct x = true)

theorem padI_step {cs : List Cond} {m : Condition} {acc : List Cond} (h : PadI avatar cs m acc)
    (i j : Nat) (t : TT) (ht : Normalize.createTT acc[j]! = some t) :
    PadI avatar cs m (acc.set i (extendC acc[i]! t true)) := by
  obtain ⟨hl, hf, hs⟩ := h
  have hj : j < acc.length := by
    by_cases hj : j < acc.length
    · exact hj
    · rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_none (by omega)] at ht
      simp only [Option.getD_none] at ht
      rw [createTT_default] at ht; exact absurd ht (by simp)
  have hpt := createTT_fits avatar (hf _ (getElem!_mem hj)) rfl t ht
  by_cases hi : i < acc.length
  · have hx := hf _ (getElem!_mem hi)
    have hext := extendC_fits avatar hx rfl t true hpt
    refine ⟨by simp [hl], fun y hy => ?_, fun hcs y hy => ?_⟩
    · rcases List.mem_or_eq_of_mem_set hy with hy | rfl
      · exact hf y hy
      · exact hext
    · rcases List.mem_or_eq_of_mem_set hy with hy | rfl
      · exact hs hcs y hy
      · rw [isStruct_extendC]; exact hs hcs _ (getElem!_mem hi)
  · rw [List.set_eq_of_length_le (by omega)]; exact ⟨hl, hf, hs⟩

theorem padLoop_fits (cs : List Cond) (m : Condition) (h : ∀ x ∈ cs, F x m) :
    PadI avatar cs m (padLoop cs) := by
  unfold padLoop
  refine foldl_inv _ (PadI avatar cs m) _ _ (fun acc i _ hacc => ?_) ⟨rfl, h, fun hs => hs⟩
  split
  · exact hacc
  · refine foldl_inv _ (PadI avatar cs m) _ _ (fun a j _ ha => ?_) hacc
    split
    · exact ha
    · split
      · exact ha
      · rename_i t ht
        exact padI_step avatar ha i j t ht

theorem pad_fits {c : Cond} {m : Condition} (h : F c m) : F (pad c) m := by
  unfold pad
  split
  · rename_i hc
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hc
    obtain ⟨hl4, hok⟩ := hc
    by_cases hlog : isLogical c = true
    · have hop := logical_op hlog
      obtain ⟨he, hch⟩ := h.logical_ch avatar hop
      exact logical_withCh avatar hop he _ (padLoop_fits avatar c.ch m hch).2.1
    · have h4 : c.enc = 4 := by simpa [hlog] using hl4
      have h0 := h
      cases h with
      | arr hop he _ hm hl hne hs hch hsn =>
        obtain ⟨hlen, hf, hst⟩ := padLoop_fits avatar c.ch (tmpl m) hch
        have hraw : isInl c = isInl { c with ch := padLoop c.ch } ∧
            (isInl c = true → rawSz avatar c = rawSz avatar { c with ch := padLoop c.ch }) := by
          have h1 : isInl c = false := by rw [isInl_eq, he]; rfl
          have h2 : isInl ({ c with ch := padLoop c.ch } : Cond) = false := by
            rw [isInl_eq]; simp [he]
          rw [h1, h2]; simp
        obtain ⟨hsn', hl'⟩ := lay_transfer avatar hraw hsn hl
        refine .arr hop he rfl hm hl' ?_ (hst hs) hf hsn'
        intro hnil; apply hne
        have h1 : (padLoop c.ch).length = 0 := by
          have : (padLoop c.ch) = [] := hnil
          rw [this]; rfl
        rw [hlen] at h1; exact List.eq_nil_of_length_eq_zero h1
      | ns _ hns =>
        exfalso
        cases hns with
        | leaf he => omega
        | logical hop => exact hlog (by simp [isLogical]; omega)
      | logical hop => exact absurd (by simp [isLogical]; omega) hlog
      | pass _ _ _ _ hp =>
        exfalso
        rcases hp with ⟨_, _, _, h41, _⟩
        have hle := h41 h4
        simp only [padOk, Bool.and_eq_true, Bool.not_eq_true'] at hok
        have := eraseDups_short ((c.ch.filter isPaddeable).map createTT)
          (by simpa using Nat.le_trans (List.length_filter_le _ _) hle)
        simp at hok; omega
      | leaf _ _ _ _ _ _ hp =>
        exfalso
        rcases hp with ⟨_, _, _, h41, _⟩
        have hle := h41 h4
        simp only [padOk, Bool.and_eq_true, Bool.not_eq_true'] at hok
        have := eraseDups_short ((c.ch.filter isPaddeable).map createTT)
          (by simpa using Nat.le_trans (List.length_filter_le _ _) hle)
        simp at hok; omega
      | tup _ he => omega
      | slice _ he => omega
  · exact h

/-! ## Normalization -/

/-- **Normalization keeps a tree fitting its layout.** -/
theorem normalize_fits : ∀ (k : Nat) (c : Cond) (m : Condition), F c m → F (normalize k c) m
  | 0, _, _, h => h
  | k + 1, c, m, h => by
    rw [normalize]
    split
    · exact h
    dsimp only
    have IH : ∀ x m', F x m' → F (normalize k x) m' := fun x m' => normalize_fits k x m'
    exact sortB_fits avatar (pushDownOr_fits avatar _ (fun n hn => IH n m hn)
      (unwrap_fits avatar (dedupe_fits avatar (flatten_fits avatar (pad_fits avatar
        (prune_fits avatar (fits_children avatar k IH h)))))))

end
end Bridge
