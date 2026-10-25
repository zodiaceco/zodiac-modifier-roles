import Bridge.TyLay

/-!
# Normalization keeps every node's layout

The contract reads a value through the tree's own metadata: where the fields
of a `Matches` are follows from its children's `inlined` and `size`. With
pruning gone, normalization keeps these for every node of a well-typed tree
(`inv`): a rewritten node is read where and as the original was.
`norm_inv` proves it; `readWorld_normOk` turns it into the assumptions of
the normalization proof (`World.NormOk`).

`inv` is what the SDK check enforces, node by node (`invP`): what adequacy
needs (`adOk`); the children of an `And`/`Or` that read a parameter share one
layout, and the others are inlined and empty unless a sibling that reads a
parameter is not inlined (so the node is not); the children of a check on a
whole value are type descriptions; the children of the other nodes
normalization rewrites read a parameter, and a tuple has one; an inlined node
that reads a parameter has a size.
-/

namespace Bridge
open DecoderFaithfulness DecoderFaithfulness.Roles Normalize Evaluate

section
variable (avatar : Bytes)

/-- Same layout: what a parent's `AbiLocation.children` reads of a child. -/
def LayR (a b : Cond) : Prop := isInl a = isInl b ∧ (isInl a = true → rawSz avatar a = rawSz avatar b)

theorem LayR.refl (a : Cond) : LayR avatar a a := ⟨rfl, fun _ => rfl⟩
theorem LayR.symm {a b : Cond} (h : LayR avatar a b) : LayR avatar b a :=
  ⟨h.1.symm, fun hb => (h.2 (h.1 ▸ hb)).symm⟩
theorem LayR.trans {a b c : Cond} (h1 : LayR avatar a b) (h2 : LayR avatar b c) : LayR avatar a c :=
  ⟨h1.1.trans h2.1, fun ha => (h1.2 ha).trans (h2.2 (h1.1 ▸ ha))⟩

/-- An empty, inlined node (reads no parameter and takes no room). -/
def Z (x : Cond) : Prop := isInl x = true ∧ rawSz avatar x = 0

/-- Operators that read their whole value, and `Pass`: their children only
    describe the type. -/
def descOp (o : Nat) : Bool := o == 0 || (15 ≤ o && o ≤ 22) || o == 28

def isLog (c : Cond) : Prop := c.op = 1 ∨ c.op = 2

/-- The local well-typedness the SDK check enforces. -/
def invP (c : Cond) : Prop :=
  adOk c ∧
  (isLog c → c.enc = 0) ∧
  (isLog c → (∀ x ∈ c.ch, ∀ y ∈ c.ch, isStruct x = true → isStruct y = true → LayR avatar x y) ∧
    (∀ x ∈ c.ch, isStruct x = false → Z avatar x ∨ ∃ y ∈ c.ch, isStruct y = true ∧ isInl y = false)) ∧
  (descOp c.op = true → ∀ x ∈ c.ch, TD x) ∧
  (¬isLog c → keepsAsWritten c = false → (∀ x ∈ c.ch, isStruct x = true) ∧ (c.enc = 3 → c.ch ≠ [])) ∧
  (isStruct c = true → isInl c = true → 0 < rawSz avatar c)

/-- **Well-typed trees.** -/
abbrev inv (c : Cond) : Prop := AllN (invP avatar) c

theorem rawSz_none {c : Cond} (h : c.enc = 0) :
    rawSz avatar c = inlinedSizeLoop true (c.ch.map (toRoles avatar)) := by
  rw [rawSz_eq, h]; simp [encN, ConditionPacking.encOf?]

theorem isInl_none {c : Cond} (h : c.enc = 0) : isInl c = c.ch.all isInl := by
  rw [isInl_eq, h]; simp

theorem loop_first (L : Nat) (hL : 0 < L) : ∀ (l : List Cond),
    (∀ x ∈ l, rawSz avatar x = 0 ∨ rawSz avatar x = L) → (∃ x ∈ l, rawSz avatar x = L) →
    inlinedSizeLoop true (l.map (toRoles avatar)) = L
  | [], _, ⟨x, hx, _⟩ => by simp at hx
  | x :: xs, h, hex => by
    simp only [List.map_cons, inlinedSizeLoop]
    have hx : inlinedSize (toRoles avatar x) = rawSz avatar x := rfl
    rw [hx]
    rcases h x (by simp) with h0 | h0
    · rw [h0]
      simp only [gt_iff_lt, Nat.lt_irrefl, and_false, ite_false, Nat.zero_add]
      obtain ⟨y, hy, hyL⟩ := hex
      rcases List.mem_cons.1 hy with rfl | hy
      · omega
      · exact loop_first L hL xs (fun z hz => h z (by simp [hz])) ⟨y, hy, hyL⟩
    · rw [h0]; simp [hL]

theorem loop_zero : ∀ (l : List Cond), (∀ x ∈ l, rawSz avatar x = 0) →
    inlinedSizeLoop true (l.map (toRoles avatar)) = 0
  | [], _ => rfl
  | x :: xs, h => by
    simp only [List.map_cons, inlinedSizeLoop]
    have hx : inlinedSize (toRoles avatar x) = 0 := h x (by simp)
    rw [hx]
    simp only [gt_iff_lt, Nat.lt_irrefl, and_false, ite_false, Nat.zero_add]
    exact loop_zero xs fun z hz => h z (by simp [hz])

/-- An `And`/`Or` has the layout of its children that read a parameter. -/
theorem logLay {c : Cond} (he : c.enc = 0)
    (hlay : ∀ x ∈ c.ch, ∀ y ∈ c.ch, isStruct x = true → isStruct y = true → LayR avatar x y)
    (hns : ∀ x ∈ c.ch, isStruct x = false → Z avatar x ∨ ∃ y ∈ c.ch, isStruct y = true ∧ isInl y = false)
    (hpos : ∀ x ∈ c.ch, isStruct x = true → isInl x = true → 0 < rawSz avatar x)
    {y0 : Cond} (hy0 : y0 ∈ c.ch) (hs0 : isStruct y0 = true) : LayR avatar c y0 := by
  by_cases hi : isInl y0 = true
  · have hall : ∀ x ∈ c.ch, (isInl x = true ∧ rawSz avatar x = rawSz avatar y0) ∨ Z avatar x := by
      intro x hx
      by_cases hsx : isStruct x = true
      · have := hlay x hx y0 hy0 hsx hs0
        left; exact ⟨this.1 ▸ hi, this.2 (this.1 ▸ hi)⟩
      · rcases hns x hx (by simpa using hsx) with hz | ⟨y, hy, hsy, hiy⟩
        · right; exact hz
        · have := hlay y hy y0 hy0 hsy hs0
          rw [this.1] at hiy; rw [hi] at hiy; cases hiy
    have hinl : isInl c = true := by
      rw [isInl_none he, List.all_eq_true]
      intro x hx; rcases hall x hx with h | h <;> exact h.1
    refine ⟨by rw [hinl, hi], fun _ => ?_⟩
    rw [rawSz_none avatar he]
    exact loop_first avatar _ (hpos y0 hy0 hs0 hi) c.ch
      (fun x hx => (hall x hx).elim (fun h => Or.inr h.2) (fun h => Or.inl h.2))
      ⟨y0, hy0, rfl⟩
  · simp only [Bool.not_eq_true] at hi
    have : isInl c = false := by
      rw [isInl_none he, List.all_eq_false]; exact ⟨y0, hy0, by simp [hi]⟩
    exact ⟨by rw [this, hi], fun h => by rw [this] at h; cases h⟩

/-- An `And`/`Or` of empty nodes is empty. -/
theorem logZ {c : Cond} (he : c.enc = 0) (hz : ∀ x ∈ c.ch, Z avatar x) : Z avatar c := by
  refine ⟨?_, ?_⟩
  · rw [isInl_none he, List.all_eq_true]; exact fun x hx => (hz x hx).1
  · rw [rawSz_none avatar he]; exact loop_zero avatar c.ch fun x hx => (hz x hx).2

/-! ## Normalization keeps whether a node reads a parameter -/

/-- A world that reads nothing: every assumption holds outright. -/
def trivW : World Unit Unit Unit where
  fields _ _ _ _ := []
  dflt := ()
  gate _ _ _ _ := true
  ext _ _ _ := fun sl _ => (none, sl)

theorem trivW_ok : trivW.Ok (fun c (_ : Unit) => some c) where
  comm := fun _ _ _ => rfl
  keeps := fun _ _ _ _ _ _ _ => rfl
  pure := fun _ _ _ _ _ _ _ _ => ⟨fun _ => false, fun _ _ => rfl⟩
  charger := fun _ _ _ _ _ _ _ _ => ⟨fun _ => none, fun _ _ => rfl⟩

theorem trivW_norm : trivW.NormOk fun _ => True where
  sub := fun _ _ _ _ => trivial
  pre := fun _ _ _ _ => trivial
  push := fun _ _ _ _ => trivial
  fields := fun _ _ _ _ _ _ => ⟨rfl, rfl⟩
  ext := fun _ _ _ _ => rfl
  hinge := fun _ _ _ _ _ _ _ _ _ _ => ⟨rfl, rfl⟩

theorem isStruct_normalize (n : Nat) (c : Cond) : isStruct (normalize n c) = isStruct c :=
  (normalize_same trivW_ok trivW_norm n c trivial).2

/-! ## And/Or nodes -/

theorem invP_default : invP avatar default := by
  show invP avatar ⟨0, 0, [], []⟩
  unfold invP adOk isLog
  simp [ConditionPacking.opOf?, isStruct_mk]

theorem inv_default : inv avatar default := .mk (invP_default avatar) fun x hx => by cases hx

theorem inv_get! {o : Cond} (h : inv avatar o) (i : Nat) : inv avatar o.ch[i]! := by
  by_cases hi : i < o.ch.length
  · exact AllN.ch _ h _ (getElem!_mem hi)
  · rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; exact inv_default avatar

theorem isStruct_log {c : Cond} (h : isLog c) : isStruct c = c.ch.any isStruct := by
  rw [isStruct_eq]; rcases h with h | h <;> simp [h]

theorem struct_log {c : Cond} (h : isLog c) :
    isStruct c = true ↔ ∃ x ∈ c.ch, isStruct x = true := by
  rw [isStruct_log h, List.any_eq_true]

/-- The layout clauses of an `And`/`Or`, with its children's sizes. -/
def LogC (c : Cond) : Prop :=
  c.enc = 0 ∧
  (∀ x ∈ c.ch, ∀ y ∈ c.ch, isStruct x = true → isStruct y = true → LayR avatar x y) ∧
  (∀ x ∈ c.ch, isStruct x = false → Z avatar x ∨ ∃ y ∈ c.ch, isStruct y = true ∧ isInl y = false) ∧
  (∀ x ∈ c.ch, isStruct x = true → isInl x = true → 0 < rawSz avatar x)

theorem LogC.of {c : Cond} (hl : isLog c) (h : inv avatar c) : LogC avatar c :=
  have p := AllN.self _ h
  ⟨p.2.1 hl, (p.2.2.1 hl).1, (p.2.2.1 hl).2, fun x hx => (AllN.self _ (AllN.ch _ h x hx)).2.2.2.2.2⟩

theorem LogC.lay {c : Cond} (h : LogC avatar c) {y : Cond} (hy : y ∈ c.ch) (hs : isStruct y = true) :
    LayR avatar c y := logLay avatar h.1 h.2.1 h.2.2.1 h.2.2.2 hy hs

theorem LogC.allZ {c : Cond} (h : LogC avatar c) (hn : ∀ x ∈ c.ch, isStruct x = false) :
    ∀ x ∈ c.ch, Z avatar x := fun x hx =>
  (h.2.2.1 x hx (hn x hx)).elim id fun ⟨y, hy, hs, _⟩ => by rw [hn y hy] at hs; cases hs

theorem Z.layR {a b : Cond} (ha : Z avatar a) (hb : Z avatar b) : LayR avatar a b :=
  ⟨ha.1.trans hb.1.symm, fun _ => ha.2.trans hb.2.symm⟩

theorem LayR.z {a b : Cond} (h : LayR avatar a b) (hb : Z avatar b) : Z avatar a :=
  ⟨h.1.trans hb.1, (h.2 (h.1.trans hb.1)).trans hb.2⟩

theorem LogC.pos {c : Cond} (hl : isLog c) (h : LogC avatar c) (hs : isStruct c = true)
    (hi : isInl c = true) : 0 < rawSz avatar c := by
  obtain ⟨y, hy, hys⟩ := (struct_log hl).1 hs
  have r := LogC.lay avatar h hy hys
  rw [r.2 hi]; exact h.2.2.2 y hy hys (r.1 ▸ hi)

/-- Two `And`/`Or` nodes whose children that read a parameter have the same
    layout, or that have none, have the same layout. -/
theorem logLayR {c d : Cond} (hc : LogC avatar c) (hd : LogC avatar d)
    (h : (∃ x ∈ c.ch, isStruct x = true ∧ ∃ y ∈ d.ch, isStruct y = true ∧ LayR avatar x y) ∨
      ((∀ x ∈ c.ch, isStruct x = false) ∧ ∀ y ∈ d.ch, isStruct y = false)) : LayR avatar c d := by
  rcases h with ⟨x, hx, hxs, y, hy, hys, r⟩ | ⟨h1, h2⟩
  · exact ((LogC.lay avatar hc hx hxs).trans avatar r).trans avatar (LogC.lay avatar hd hy hys).symm
  · exact Z.layR avatar (logZ avatar hc.1 (LogC.allZ avatar hc h1)) (logZ avatar hd.1 (LogC.allZ avatar hd h2))

/-- An `And`/`Or` rebuilt from other children that read a parameter where it
    did (with the same layout), or none if it did not. -/
theorem log_rebuild {c : Cond} (hl : isLog c) (hc : inv avatar c) (l : List Cond)
    (ha : ∀ y ∈ l, inv avatar y)
    (hb : ∀ y ∈ l, isStruct y = true → ∃ x ∈ c.ch, isStruct x = true ∧ LayR avatar y x)
    (hn : ∀ y ∈ l, isStruct y = false → Z avatar y ∨ ∃ z ∈ l, isStruct z = true ∧ isInl z = false)
    (hd : (∃ x ∈ c.ch, isStruct x = true) → ∃ y ∈ l, isStruct y = true) :
    inv avatar { c with ch := l } ∧ LayR avatar { c with ch := l } c := by
  have pc := AllN.self _ hc
  have Lc := LogC.of avatar hl hc
  have hl' : isLog ({ c with ch := l } : Cond) := hl
  have Ld : LogC avatar { c with ch := l } :=
    ⟨Lc.1,
     fun y1 h1 y2 h2 s1 s2 => by
       obtain ⟨x1, hx1, sx1, r1⟩ := hb y1 h1 s1
       obtain ⟨x2, hx2, sx2, r2⟩ := hb y2 h2 s2
       exact (r1.trans avatar (Lc.2.1 x1 hx1 x2 hx2 sx1 sx2)).trans avatar r2.symm,
     hn,
     fun y hy hs => (AllN.self _ (ha y hy)).2.2.2.2.2 hs⟩
  refine ⟨.mk ⟨⟨pc.1.1, fun h => by rcases hl with h' | h' <;> simp_all,
      fun h => by rcases hl with h' | h' <;> simp_all,
      fun h => by rcases hl with h' | h' <;> rcases h with h | h <;> simp_all⟩,
    fun _ => Lc.1, fun _ => ⟨Ld.2.1, Ld.2.2.1⟩,
    fun h => by rcases hl with h' | h' <;> simp_all [descOp],
    fun h => absurd hl' h,
    fun hs hi => LogC.pos avatar hl' Ld hs hi⟩ ha, ?_⟩
  by_cases hex : ∃ x ∈ c.ch, isStruct x = true
  · obtain ⟨y, hy, hys⟩ := hd hex
    obtain ⟨x, hx, hxs, r⟩ := hb y hy hys
    exact logLayR avatar Ld Lc (.inl ⟨y, hy, hys, x, hx, hxs, r⟩)
  · refine logLayR avatar Ld Lc (.inr ⟨fun y hy => ?_, fun x hx => ?_⟩)
    · cases hys : isStruct y
      · rfl
      · obtain ⟨x, hx, hxs, _⟩ := hb y hy hys; exact absurd ⟨x, hx, hxs⟩ hex
    · cases hxs : isStruct x
      · rfl
      · exact absurd ⟨x, hx, hxs⟩ hex

/-! ## The steps of `normalize` -/

theorem normalize_leaf : ∀ (k : Nat) {x : Cond}, x.ch = [] → x.op ≠ 1 → x.op ≠ 2 → normalize k x = x
  | 0, _, _, _, _ => rfl
  | k + 1, x, h, h1, h2 => by
    by_cases hkw : keepsAsWritten x = true
    · rw [normalize, if_pos hkw]
    · rw [normalize_nonlog k h1 h2 (by simpa using hkw), h]
      rcases x with ⟨e, o, v, ch⟩; simp only at h; subst h; rfl

theorem isStruct_withCh {c : Cond} {l : List Cond} (h : l.any isStruct = c.ch.any isStruct) :
    isStruct { c with ch := l } = isStruct c := by
  rw [isStruct_eq, isStruct_eq]; simp only [h]

/-- Normalizing the children keeps the tree well-typed and the layout. -/
theorem c1_inv (k : Nat) {c : Cond} (hc : inv avatar c) (hkw : keepsAsWritten c = false)
    (IH : ∀ x ∈ c.ch, inv avatar (normalize k x) ∧ LayR avatar (normalize k x) x) :
    inv avatar { c with ch := c.ch.map (normalize k) } ∧ LayR avatar { c with ch := c.ch.map (normalize k) } c := by
  have pc := AllN.self _ hc
  have hlay : LayR avatar { c with ch := c.ch.map (normalize k) } c := by
    have r := container_raw avatar (c := { c with ch := c.ch.map (normalize k) }) (c' := c) rfl (by simp)
      fun i h1 h2 => by
        simp only [List.getElem_map]
        exact IH _ (List.getElem_mem _) |>.2
    exact ⟨r.1, r.2⟩
  have hs : isStruct ({ c with ch := c.ch.map (normalize k) } : Cond) = isStruct c := by
    apply isStruct_withCh; rw [List.any_map]
    exact any_congr_mem fun x _ => isStruct_normalize k x
  have mem : ∀ {P : Cond → Prop}, (∀ x ∈ c.ch, P (normalize k x)) →
      ∀ y ∈ ({ c with ch := c.ch.map (normalize k) } : Cond).ch, P y := fun h y hy => by
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy; exact h x hx
  refine ⟨.mk ⟨⟨pc.1.1, fun h5 he => mem fun x hx => (isStruct_normalize k x).trans (pc.1.2.1 h5 he x hx),
      fun h13 => mem fun x hx => by
        obtain ⟨h0, hn⟩ := pc.1.2.2.1 h13 x hx
        obtain ⟨_, _, _⟩ := navOp_false hn
        rw [normalize_leaf k h0 (by omega) (by omega)]; exact ⟨h0, hn⟩,
      fun h => by
        unfold keepsAsWritten at hkw
        have h' : c.op = 10 ∨ c.op = 11 := h
        rcases h' with h' | h' <;> simp [h'] at hkw⟩,
    pc.2.1,
    fun hl => ⟨fun y1 h1 y2 h2 s1 s2 => by
        obtain ⟨x1, hx1, rfl⟩ := List.mem_map.1 h1
        obtain ⟨x2, hx2, rfl⟩ := List.mem_map.1 h2
        rw [isStruct_normalize] at s1 s2
        exact ((IH x1 hx1).2.trans avatar ((pc.2.2.1 hl).1 x1 hx1 x2 hx2 s1 s2)).trans avatar (IH x2 hx2).2.symm,
      fun y hy hn => by
        obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy
        rw [isStruct_normalize] at hn
        rcases (pc.2.2.1 hl).2 x hx hn with hz | ⟨z, hz, hzs, hzi⟩
        · exact .inl (LayR.z avatar (IH x hx).2 hz)
        · exact .inr ⟨normalize k z, List.mem_map_of_mem hz, (isStruct_normalize k z).trans hzs,
            ((IH z hz).2.1).trans hzi⟩⟩,
    fun hd => mem fun x hx => (td_normalize avatar k x (pc.2.2.2.1 hd x hx)).1,
    fun hl hk => ⟨mem fun x hx => (isStruct_normalize k x).trans ((pc.2.2.2.2.1 hl hk).1 x hx),
      fun he => by simpa using (pc.2.2.2.2.1 hl hk).2 he⟩,
    fun h1 h2 => by
      rw [hs] at h1; rw [hlay.2 h2]; exact pc.2.2.2.2.2 h1 (hlay.1 ▸ h2)⟩
    (mem fun x hx => (IH x hx).1), hlay⟩

theorem isLog_of {c : Cond} (h : isLogical c = true) : isLog c := by
  unfold isLogical at h; unfold isLog; simp only [Bool.or_eq_true, beq_iff_eq] at h; exact h

theorem mem_flattenCh {op : Nat} {cs : List Cond} {y : Cond} :
    y ∈ flattenCh op cs ↔ ∃ x ∈ cs, (x.op = op ∧ y ∈ x.ch) ∨ (x.op ≠ op ∧ y = x) := by
  unfold flattenCh
  rw [List.mem_flatMap]
  constructor
  · rintro ⟨x, hx, h⟩
    refine ⟨x, hx, ?_⟩
    split at h
    · rename_i he; exact .inl ⟨by simpa using he, h⟩
    · rename_i he; exact .inr ⟨by simpa using he, by simpa using h⟩
  · rintro ⟨x, hx, h | h⟩
    · exact ⟨x, hx, by rw [if_pos (by simp [h.1])]; exact h.2⟩
    · exact ⟨x, hx, by rw [if_neg (by simp [h.1])]; simp [h.2]⟩

/-- A child that reads a parameter has one among its children (if it is an
    `And`/`Or`), with its layout. -/
theorem struct_child {x : Cond} (hl : isLog x) (hx : inv avatar x) (hs : isStruct x = true) :
    ∃ g ∈ x.ch, isStruct g = true ∧ LayR avatar g x := by
  obtain ⟨g, hg, hgs⟩ := (struct_log hl).1 hs
  exact ⟨g, hg, hgs, (LogC.lay avatar (LogC.of avatar hl hx) hg hgs).symm⟩

theorem flatten_inv {c : Cond} (hc : inv avatar c) :
    inv avatar (flatten c) ∧ LayR avatar (flatten c) c := by
  unfold flatten
  split
  case isFalse => exact ⟨hc, LayR.refl avatar c⟩
  rename_i hL
  have hl := isLog_of hL
  have sub : ∀ x ∈ c.ch, x.op = c.op → isLog x := fun x _ h => by unfold isLog; rw [h]; exact hl
  apply log_rebuild avatar hl hc
  · intro y hy
    obtain ⟨x, hx, ⟨_, hyx⟩ | ⟨_, rfl⟩⟩ := mem_flattenCh.1 hy
    · exact AllN.ch _ (AllN.ch _ hc x hx) y hyx
    · exact AllN.ch _ hc _ hx
  · intro y hy hys
    obtain ⟨x, hx, ⟨hop, hyx⟩ | ⟨_, rfl⟩⟩ := mem_flattenCh.1 hy
    · have hxl := sub x hx hop
      have hxs : isStruct x = true := (struct_log hxl).2 ⟨y, hyx, hys⟩
      exact ⟨x, hx, hxs, (LogC.lay avatar (LogC.of avatar hxl (AllN.ch _ hc x hx)) hyx hys).symm⟩
    · exact ⟨_, hx, hys, LayR.refl avatar _⟩
  · -- a child of `c` that reads a parameter and is not inlined leaves one in the flattened list
    have wit : ∀ z ∈ c.ch, isStruct z = true → isInl z = false →
        ∃ z' ∈ flattenCh c.op c.ch, isStruct z' = true ∧ isInl z' = false := fun z hz hzs hzi => by
      by_cases hop : z.op = c.op
      · obtain ⟨g, hg, hgs, r⟩ := struct_child avatar (sub z hz hop) (AllN.ch _ hc z hz) hzs
        exact ⟨g, mem_flattenCh.2 ⟨z, hz, .inl ⟨hop, hg⟩⟩, hgs, r.1.trans hzi⟩
      · exact ⟨z, mem_flattenCh.2 ⟨z, hz, .inr ⟨hop, rfl⟩⟩, hzs, hzi⟩
    intro y hy hyn
    obtain ⟨x, hx, ⟨hop, hyx⟩ | ⟨_, rfl⟩⟩ := mem_flattenCh.1 hy
    · rcases (LogC.of avatar (sub x hx hop) (AllN.ch _ hc x hx)).2.2.1 y hyx hyn with hz | ⟨z, hz, hzs, hzi⟩
      · exact .inl hz
      · exact .inr ⟨z, mem_flattenCh.2 ⟨x, hx, .inl ⟨hop, hz⟩⟩, hzs, hzi⟩
    · rcases (LogC.of avatar hl hc).2.2.1 _ hx hyn with hz | ⟨z, hz, hzs, hzi⟩
      · exact .inl hz
      · exact .inr (wit z hz hzs hzi)
  · rintro ⟨x, hx, hxs⟩
    by_cases hop : x.op = c.op
    · obtain ⟨g, hg, hgs, _⟩ := struct_child avatar (sub x hx hop) (AllN.ch _ hc x hx) hxs
      exact ⟨g, mem_flattenCh.2 ⟨x, hx, .inl ⟨hop, hg⟩⟩, hgs⟩
    · exact ⟨x, mem_flattenCh.2 ⟨x, hx, .inr ⟨hop, rfl⟩⟩, hxs⟩

theorem mem_dedupeL' {b : Bool} : ∀ {seen l : List Cond} {x : Cond}, x ∈ l →
    x ∈ seen ∨ x ∈ dedupeL b seen l
  | _, [], _, h => by cases h
  | seen, y :: ys, x, h => by
    unfold dedupeL
    split
    · rename_i hy
      rcases List.mem_cons.1 h with rfl | h
      · exact .inl (by simpa using hy)
      · rcases mem_dedupeL' (b := b) (seen := seen) h with h | h
        · exact .inl h
        · split
          · exact .inr (List.mem_cons_of_mem _ h)
          · exact .inr h
    · rcases List.mem_cons.1 h with rfl | h
      · exact .inr (by simp)
      · rcases mem_dedupeL' (b := b) (seen := y :: seen) h with h | h
        · rcases List.mem_cons.1 h with rfl | h
          · exact .inr (by simp)
          · exact .inl h
        · exact .inr (List.mem_cons_of_mem _ h)

/-- An `And`/`Or` with the same children, as a set. -/
theorem log_sameMem {c : Cond} (hl : isLog c) (hc : inv avatar c) {l : List Cond}
    (h : ∀ x, x ∈ l ↔ x ∈ c.ch) : inv avatar { c with ch := l } ∧ LayR avatar { c with ch := l } c := by
  apply log_rebuild avatar hl hc l (fun y hy => AllN.ch _ hc y ((h y).1 hy))
    (fun y hy hys => ⟨y, (h y).1 hy, hys, LayR.refl avatar y⟩)
  · intro y hy hyn
    rcases (LogC.of avatar hl hc).2.2.1 y ((h y).1 hy) hyn with hz | ⟨z, hz, hzs, hzi⟩
    · exact .inl hz
    · exact .inr ⟨z, (h z).2 hz, hzs, hzi⟩
  · rintro ⟨x, hx, hxs⟩; exact ⟨x, (h x).2 hx, hxs⟩

theorem dedupe_inv {c : Cond} (hc : inv avatar c) :
    inv avatar (dedupe c) ∧ LayR avatar (dedupe c) c := by
  unfold dedupe
  split
  case isFalse => exact ⟨hc, LayR.refl avatar c⟩
  rename_i hL
  simp only [Bool.and_eq_true] at hL
  exact log_sameMem avatar (isLog_of hL.1) hc fun x =>
    ⟨mem_dedupeL, fun hx => (mem_dedupeL' (seen := []) hx).resolve_left (by simp)⟩

theorem sortB_inv {c : Cond} (hc : inv avatar c) :
    inv avatar (sortB c) ∧ LayR avatar (sortB c) c := by
  unfold sortB
  split
  case isFalse => exact ⟨hc, LayR.refl avatar c⟩
  rename_i hL
  simp only [Bool.and_eq_true] at hL
  exact log_sameMem avatar (isLog_of hL.1) hc fun x => (sortCh_perm c.ch).mem_iff

theorem unwrap_inv {c : Cond} (hc : inv avatar c) :
    inv avatar (unwrap c) ∧ LayR avatar (unwrap c) c := by
  unfold unwrap
  split
  case isFalse => exact ⟨hc, LayR.refl avatar c⟩
  rename_i hL
  split
  case h_2 => exact ⟨hc, LayR.refl avatar c⟩
  rename_i x hx
  have hl := isLog_of hL
  have Lc := LogC.of avatar hl hc
  have hm : x ∈ c.ch := by rw [hx]; simp
  refine ⟨AllN.ch _ hc x hm, ?_⟩
  cases hxs : isStruct x
  · rcases Lc.2.2.1 x hm hxs with hz | ⟨z, hz, hzs, _⟩
    · exact Z.layR avatar hz (logZ avatar Lc.1 fun y hy => by
        rw [hx] at hy; rcases List.mem_singleton.1 hy with rfl; exact hz)
    · rw [hx] at hz; rcases List.mem_singleton.1 hz with rfl; rw [hxs] at hzs; cases hzs
  · exact (LogC.lay avatar Lc hm hxs).symm

/-! ## `pushDownOr` -/

theorem invP_of_LogC {c : Cond} (hl : isLog c) (h : LogC avatar c) : invP avatar c := by
  have hop : c.op = 1 ∨ c.op = 2 := hl
  refine ⟨⟨by rcases hop with h' | h' <;> simp [h', ConditionPacking.opOf?],
      fun h5 => by omega, fun h13 => by omega, fun h => by omega⟩,
    fun _ => h.1, fun _ => ⟨h.2.1, h.2.2.1⟩,
    fun hd => by rcases hop with h' | h' <;> simp [h', descOp] at hd,
    fun h' => absurd hl h', fun hs hi => LogC.pos avatar hl h hs hi⟩

theorem orNode_logC {hs : List Cond} (hst : sameType hs = true) :
    LogC avatar (orNode hs) ∧ ∀ x ∈ hs, isStruct x = true := by
  obtain ⟨t, ht⟩ := sameType_lay avatar hst
  exact ⟨⟨rfl, fun x hx y hy _ _ => ⟨(ht x hx).2.1.trans (ht y hy).2.1.symm, fun hi =>
        ((ht x hx).2.2 ((ht x hx).2.1 ▸ hi)).1.trans ((ht y hy).2.2 ((ht x hx).2.1 ▸ hi)).1.symm⟩,
     fun x hx hn => (by rw [(ht x hx).1] at hn; cases hn),
     fun x hx _ hi => (by rw [((ht x hx).2.2 ((ht x hx).2.1 ▸ hi)).1]; exact ((ht x hx).2.2 ((ht x hx).2.1 ▸ hi)).2)⟩,
    fun x hx => (ht x hx).1⟩

/-- The `Or` a merge puts at the hinge has its branches' layout. -/
theorem orNode_lay {hs : List Cond} (hst : sameType hs = true) :
    ∀ x ∈ hs, isStruct x = true ∧ LayR avatar (orNode hs) x := fun x hx =>
  have L := orNode_logC avatar hst
  ⟨L.2 x hx, LogC.lay avatar L.1 hx (L.2 x hx)⟩

theorem orNode_inv {hs : List Cond} (hst : sameType hs = true) (hne : hs ≠ [])
    (ha : ∀ x ∈ hs, inv avatar x) :
    inv avatar (orNode hs) ∧ ∀ x ∈ hs, isStruct x = true ∧ LayR avatar (orNode hs) x :=
  ⟨.mk (invP_of_LogC avatar (Or.inr rfl) (orNode_logC avatar hst).1) ha, orNode_lay avatar hst⟩

theorem mem_set_or {l : List Cond} {i : Nat} (hi : i < l.length) {x y : Cond} (hx : x ∈ l) :
    x ∈ l.set i y ∨ x = l[i] := by
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
  by_cases hij : i = j
  · subst hij; exact .inr rfl
  · left
    have h : (l.set i y)[j]'(by simpa using hj) = l[j] := by rw [List.getElem_set]; simp [hij]
    rw [← h]; exact List.getElem_mem _

theorem mem_set_self {l : List Cond} {i : Nat} (hi : i < l.length) (y : Cond) : y ∈ l.set i y := by
  have h := List.getElem_mem (l := l.set i y) (by simpa using hi)
  rwa [List.getElem_set_self] at h

theorem set_lay {l : List Cond} {i : Nat} (hi : i < l.length) {y : Cond} (hy : LayR avatar y l[i]) :
    ∀ j (h1 : j < (l.set i y).length) (h2 : j < l.length), LayR avatar (l.set i y)[j] l[j] := by
  intro j h1 h2
  rw [List.getElem_set]
  split
  · rename_i h; subst h; exact hy
  · exact LayR.refl avatar _

theorem eta_ch (c : Cond) : ({ c with ch := c.ch } : Cond) = c := rfl

theorem pushStep_inv {u m : Cond} (hu : inv avatar u) (hp : pushStep u = some m) :
    inv avatar m ∧ LayR avatar m u := by
  unfold pushStep at hp
  split at hp
  case isFalse => simp at hp
  rename_i hcond
  have hop : u.op = 2 := by
    revert hcond; simp only [Bool.and_eq_true, beq_iff_eq]; intro h; exact h.1.1.1
  have hlen : 2 ≤ u.ch.length := by
    revert hcond; simp only [Bool.and_eq_true, decide_eq_true_eq]; intro h; exact h.1.1.2
  have hlu : isLog u := Or.inr hop
  have Lu := LogC.of avatar hlu hu
  have hhead : u.ch.head! ∈ u.ch := by
    obtain ⟨x, xs, hc⟩ : ∃ x xs, u.ch = x :: xs := by
      cases h : u.ch with
      | nil => rw [h] at hlen; simp at hlen
      | cons x xs => exact ⟨x, xs, rfl⟩
    rw [hc]; exact .head _
  have hH := AllN.ch _ hu _ hhead
  have pH := AllN.self _ hH
  have hsInv : ∀ (f : Cond → Nat), ∀ y ∈ u.ch.map (fun o => o.ch[f o]!), inv avatar y := by
    intro f y hy
    obtain ⟨o, ho, rfl⟩ := List.mem_map.1 hy
    exact inv_get! avatar (AllN.ch _ hu o ho) _
  have hne : ∀ (f : Cond → Nat), u.ch.map (fun o => o.ch[f o]!) ≠ [] := fun f h => by
    rw [List.map_eq_nil_iff] at h; rw [h] at hhead; cases hhead
  have hmemH : ∀ (f : Cond → Nat), u.ch.head!.ch[f u.ch.head!]! ∈ u.ch.map (fun o => o.ch[f o]!) :=
    fun f => List.mem_map_of_mem (f := fun o => o.ch[f o]!) hhead
  split at hp
  · -- `Matches` branches
    rename_i hall
    have hop5 : u.ch.head!.op = 5 := by
      have := List.all_eq_true.1 hall _ hhead; simpa using this
    obtain ⟨nch, hm, rfl⟩ := Option.map_eq_some_iff.1 hp
    unfold mergeMatches at hm
    split at hm; · simp at hm
    rename_i he35
    have he : u.ch.head!.enc = 3 ∨ u.ch.head!.enc = 5 := by simp at he35; omega
    split at hm; · simp at hm
    split at hm; · simp at hm
    split at hm; · simp at hm
    rename_i h _
    split at hm; · simp at hm
    split at hm; · simp at hm
    rename_i hst
    have hst' : sameType (u.ch.map (·.ch[h]!)) = true := by simpa using hst
    split at hm; · simp at hm
    simp only [Option.some.injEq] at hm; subst hm
    generalize hH0 : u.ch.head! = H at *
    have hHs : isStruct H = true := by
      rw [isStruct_eq, hop5]; rcases he with h' | h' <;> simp [h']
    have hHu : LayR avatar H u := (LogC.lay avatar Lu hhead hHs).symm
    obtain ⟨hOr, hOrL⟩ := orNode_inv avatar hst' (hne fun _ => h) (hsInv fun _ => h)
    rw [replaceAt_set]
    by_cases hh' : H.ch.length ≤ h
    · rw [List.set_eq_of_length_le hh']; rcases H with ⟨e, o, v, ch⟩; exact ⟨hH, hHu⟩
    have hh : h < H.ch.length := by omega
    have hmem : H.ch[h] ∈ u.ch.map (·.ch[h]!) := by
      rw [← getElem!_eq hh]; exact hmemH fun _ => h
    obtain ⟨hHs', hlay⟩ := hOrL _ hmem
    have hOrS : isStruct (orNode (u.ch.map (·.ch[h]!))) = true :=
      (struct_log (Or.inr rfl)).2 ⟨_, hmem, hHs'⟩
    have hchS : ∀ x ∈ H.ch.set h (orNode (u.ch.map (·.ch[h]!))), isStruct x = true := fun x hx => by
      rcases List.mem_or_eq_of_mem_set hx with hx | rfl
      · exact pH.1.2.1 hop5 he x hx
      · exact hOrS
    have r := container_raw avatar (c := { H with ch := H.ch.set h (orNode (u.ch.map (·.ch[h]!))) })
      (c' := H) rfl (by simp) (fun i h1 h2 => by
        have := set_lay avatar hh hlay i h1 h2; exact ⟨this.1, this.2⟩)
    have hmH : LayR avatar { H with ch := H.ch.set h (orNode (u.ch.map (·.ch[h]!))) } H := ⟨r.1, r.2⟩
    have hsm : isStruct ({ H with ch := H.ch.set h (orNode (u.ch.map (·.ch[h]!))) } : Cond) = true := by
      rw [isStruct_eq] at hHs ⊢; simp only [hop5] at hHs ⊢; exact hHs
    refine ⟨.mk ⟨⟨pH.1.1, fun _ _ => hchS, fun h13 => by simp [hop5] at h13,
        fun h1011 => by simp [hop5] at h1011⟩,
      fun hl => by rcases hl with h' | h' <;> simp [hop5] at h',
      fun hl => by rcases hl with h' | h' <;> simp [hop5] at h',
      fun hd => by simp [hop5, descOp] at hd,
      fun _ _ => ⟨hchS, fun _ h0 => by have := congrArg List.length h0; rw [List.length_set] at this; simp only [List.length_nil] at this; omega⟩,
      fun _ hi => by rw [hmH.2 hi]; exact pH.2.2.2.2.2 hHs (hmH.1 ▸ hi)⟩
      (fun x hx => by
        rcases List.mem_or_eq_of_mem_set hx with hx | rfl
        · exact AllN.ch _ hH x hx
        · exact hOr), hmH.trans avatar hHu⟩
  · split at hp
    case isFalse => simp at hp
    -- `And` branches
    rename_i _ hall
    have hop1 : u.ch.head!.op = 1 := by
      have := List.all_eq_true.1 hall _ hhead; simpa using this
    obtain ⟨nch, hm, rfl⟩ := Option.map_eq_some_iff.1 hp
    unfold mergeAnd at hm
    split at hm; · simp at hm
    split at hm; · simp at hm
    split at hm; · simp at hm
    split at hm; · simp at hm
    split at hm; · simp at hm
    rename_i hst
    have hst' : sameType (u.ch.map fun o => o.ch[hingeOf u.ch o]!) = true := by simpa using hst
    simp only [Option.some.injEq] at hm; subst hm
    obtain ⟨hOr, hOrL⟩ := orNode_inv avatar hst' (hne (hingeOf u.ch)) (hsInv (hingeOf u.ch))
    have hmemH' := hmemH (hingeOf u.ch)
    generalize hH0 : u.ch.head! = H at *
    generalize u.ch.map (fun o => o.ch[hingeOf u.ch o]!) = hs at *
    generalize hingeOf u.ch H = h at *
    have hlH : isLog H := Or.inl hop1
    rw [replaceAt_set]
    by_cases hh' : H.ch.length ≤ h
    · rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_none hh'] at hmemH'
      rw [Option.getD_none] at hmemH'
      have h1 := (hOrL _ hmemH').1
      have h2 : isStruct (default : Cond) = false := rfl
      rw [h2] at h1; cases h1
    have hh : h < H.ch.length := by omega
    rw [getElem!_eq hh] at hmemH'
    obtain ⟨hHs', hlay⟩ := hOrL _ hmemH'
    have hHs : isStruct H = true := (struct_log hlH).2 ⟨_, List.getElem_mem hh, hHs'⟩
    have hHu : LayR avatar H u := (LogC.lay avatar Lu hhead hHs).symm
    have hOrS : isStruct (orNode hs) = true := (struct_log (Or.inr rfl)).2 ⟨_, hmemH', hHs'⟩
    have LH := LogC.of avatar hlH hH
    have res := log_rebuild avatar hlH hH (H.ch.set h (orNode hs))
      (fun y hy => by
        rcases List.mem_or_eq_of_mem_set hy with hy | rfl
        · exact AllN.ch _ hH y hy
        · exact hOr)
      (fun y hy hys => by
        rcases List.mem_or_eq_of_mem_set hy with hy | rfl
        · exact ⟨y, hy, hys, LayR.refl avatar y⟩
        · exact ⟨_, List.getElem_mem hh, hHs', hlay⟩)
      (fun y hy hyn => by
        rcases List.mem_or_eq_of_mem_set hy with hy | rfl
        · rcases LH.2.2.1 y hy hyn with hz | ⟨z, hz, hzs, hzi⟩
          · exact .inl hz
          · rcases mem_set_or hh (y := orNode hs) hz with hz' | rfl
            · exact .inr ⟨z, hz', hzs, hzi⟩
            · exact .inr ⟨orNode hs, mem_set_self hh _, hOrS, hlay.1.trans hzi⟩
        · rw [hOrS] at hyn; cases hyn)
      (fun _ => ⟨orNode hs, mem_set_self hh _, hOrS⟩)
    exact ⟨res.1, res.2.trans avatar hHu⟩

/-! ## Normalization keeps the layout -/

/-- **Normalization keeps a well-typed tree well-typed, and its layout.** -/
theorem norm_inv : ∀ (k : Nat) (x : Cond), inv avatar x →
    inv avatar (normalize k x) ∧ LayR avatar (normalize k x) x
  | 0, x, h => ⟨h, LayR.refl avatar x⟩
  | k + 1, x, h => by
    rw [normalize]
    split
    · exact ⟨h, LayR.refl avatar x⟩
    rename_i hkw
    dsimp only
    have IH := norm_inv k
    have s1 := c1_inv avatar k h (by simpa using hkw) fun y hy => IH y (AllN.ch _ h y hy)
    have s2 := flatten_inv avatar s1.1
    have s3 := dedupe_inv avatar s2.1
    have s4 := unwrap_inv avatar s3.1
    have s5 : inv avatar (pushDownOr (normalize k) (unwrap (dedupe (flatten
        { x with ch := x.ch.map (normalize k) })))) ∧
        LayR avatar (pushDownOr (normalize k) (unwrap (dedupe (flatten
        { x with ch := x.ch.map (normalize k) })))) (unwrap (dedupe (flatten
        { x with ch := x.ch.map (normalize k) }))) := by
      unfold pushDownOr
      split
      · rename_i m hm
        have p := pushStep_inv avatar s4.1 hm
        have q := IH m p.1
        exact ⟨q.1, q.2.trans avatar p.2⟩
      · exact ⟨s4.1, LayR.refl avatar _⟩
    have s6 := sortB_inv avatar s5.1
    exact ⟨s6.1, s6.2.trans avatar (s5.2.trans avatar (s4.2.trans avatar (s3.2.trans avatar
      (s2.2.trans avatar s1.2))))⟩

/-! ## What the contract reads of a node -/

/-- What the evaluator reads of a node, apart from its type: the same in both. -/
structure NEq (d m : Condition) : Prop where
  enc : d.encoding = m.encoding
  op : d.operator = m.operator
  cv : d.compValue = m.compValue
  lb : d.leadingBytes = m.leadingBytes
  inl : d.inlined = m.inlined
  sz : d.size = m.size
  len : d.children.length = m.children.length
  ch : ∀ i (h1 : i < d.children.length) (h2 : i < m.children.length), LayEq d.children[i] m.children[i]

theorem D_lay {a b : Cond} (h : LayR avatar a b) : LayEq (D avatar a) (D avatar b) := by
  unfold LayEq; rw [D_inlined, D_inlined, D_size, D_size, h.1]
  by_cases hi : isInl b = true
  · rw [← h.1] at hi; simp [hi, h.2 hi]
  · simp at hi; simp [hi]

theorem childrenE_congr (data : Calldata) (loc : Nat) {d m : Condition} (h : NEq d m) :
    childrenE data loc d = childrenE data loc m := by
  unfold childrenE allocPanics children
  rw [h.enc]
  split
  · rfl
  · congr 1
    split
    · congr 1
      apply childrenLoop_congr
      intro j _ _
      cases hd : d.children with
      | nil =>
        have : m.children = [] := List.eq_nil_of_length_eq_zero (by rw [← h.len, hd]; rfl)
        rw [this]; exact LayEq.refl _
      | cons a as =>
        cases hm : m.children with
        | nil => have := h.len; rw [hd, hm] at this; simp at this
        | cons b bs =>
          have := h.ch 0 (by rw [hd]; simp) (by rw [hm]; simp)
          simp only [hd, hm, List.getElem_cons_zero] at this
          exact this
    · rw [h.len]
      apply childrenLoop_congr
      intro j _ hj
      simp only [Nat.zero_add] at hj
      have hl := h.len
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega),
        List.getElem?_eq_getElem hj]
      simp only [Option.getD_some]
      exact h.ch j (by omega) hj

theorem NEq.withSize {d m : Condition} (h : NEq d m) (s : Nat) : NEq (d.withSize s) (m.withSize s) :=
  ⟨h.enc, h.op, h.cv, h.lb, h.inl, rfl, h.len, h.ch⟩

theorem TyEq.withSize {d m : Condition} (h : TyEq d m) (s : Nat) : TyEq (d.withSize s) (m.withSize s) := by
  cases h with
  | mk he hl hc => exact .mk he ⟨hl.1, rfl⟩ hc

theorem nodeAt_neq {c c' : Cond} (h : NEq (D avatar c') (D avatar c)) :
    ∀ v, NEq (nodeAt avatar c' v) (nodeAt avatar c v)
  | .pos _ => h
  | .el _ => h
  | .win _ sz => h.withSize sz

theorem nodeAt_ty {c c' : Cond} (h : TyEq (D avatar c') (D avatar c)) :
    ∀ v, TyEq (nodeAt avatar c' v) (nodeAt avatar c v)
  | .pos _ => h
  | .el _ => h
  | .win _ sz => h.withSize sz

section
variable (env : Env) (data : Calldata) (n : Nat)

/-- `readExt`, from the operator, the encoding and the nodes the evaluator runs. -/
def readExtN (op e : Nat) (nd : RV → Condition) (ss : List (RV → T)) (v : RV) : T :=
  match op with
  | 4 => emptyT data
  | 5 => marrT data e (nd v) v.loc ss
  | 6 => iterT data false (nd v) v.loc ss
  | 7 => iterT data true (nd v) v.loc ss
  | 8 => tailT data (nd v) v.loc ss
  | 10 => zipT data n false (nd v) (ss.headD fun _ => passT)
  | 11 => zipT data n true (nd v) (ss.headD fun _ => passT)
  | 13 => sliceT data (nd v) v.loc (ss.headD fun _ => passT)
  | 14 => pluckT env data n (nd v) v.loc
  | 15 | 16 | 17 | 18 | 19 | 20 => checkT fun _ => cmpOk env data (nd v) v.loc
  | 21 => checkT fun _ =>
    bitmaskStatus (bitmaskCheck data v.loc (nd v).compValue (nd v).inlined (nd v).size []) = sOk
  | 22 => chargesT env.balance (customCharges env data (nd v) v.loc)
  | 23 => checkT fun sl => env.ratio (nd v).compValue sl.values = sOk
  | 28 => chargesT env.balance fun _ => allowanceCharge env data (nd v) v.loc
  | 30 => chargesT env.balance fun _ => (charge env (nd v).compValue 1).map ([·])
  | _ => failT

theorem readExt_eq (c : Cond) :
    readExt avatar env data n c = readExtN env data n c.op c.enc (nodeAt avatar c) := by
  funext ss v; unfold readExt readExtN; rfl

theorem arrLocs_congr {d m : Condition} (h : NEq d m) (l : Nat) : arrLocs data d l = arrLocs data m l := by
  unfold arrLocs; rw [childrenE_congr data l h]

theorem readExtN_congr {op e : Nat} {nd nd' : RV → Condition} (hkw : op ≠ 10 ∧ op ≠ 11 ∧ op ≠ 14)
    (hN : ∀ v, NEq (nd v) (nd' v)) (hT : descOp op = true → ∀ v, TyEq (nd v) (nd' v)) :
    readExtN env data n op e nd = readExtN env data n op e nd' := by
  funext ss v
  have N := hN v
  have T : descOp op = true → TyEq (nd v) (nd' v) := fun h => hT h v
  unfold readExtN
  generalize nd v = d at N T
  generalize nd' v = m at N T
  split
  · rfl
  · unfold marrT; rw [N.cv, N.lb, arrLocs_congr data N]
  · unfold iterT; rw [arrLocs_congr data N]
  · unfold iterT; rw [arrLocs_congr data N]
  · unfold tailT; rw [arrLocs_congr data N]
  · exact absurd rfl hkw.1
  · exact absurd rfl hkw.2.1
  · unfold sliceT; rw [N.cv, N.inl, N.sz]
  · exact absurd rfl hkw.2.2
  all_goals first
    | (unfold cmpOk; rw [input_tyEq data (T rfl), N.op, N.cv])
    | (rw [N.cv, N.inl, N.sz])
    | (unfold customCharges; rw [N.cv, N.sz, size_tyEq data (T rfl)])
    | (rw [N.cv])
    | (unfold allowanceCharge; rw [input_tyEq data (T rfl), N.cv])
    | rfl
end

/-- Nodes with the same operator, encoding and compValue whose children have
    the same layouts: the evaluator reads them alike (apart from types). -/
theorem D_neq {c c' : Cond} (he : c'.enc = c.enc) (hop : c'.op = c.op) (hcv : c'.cv = c.cv)
    (hl : c'.ch.length = c.ch.length)
    (h : ∀ i (h1 : i < c'.ch.length) (h2 : i < c.ch.length), LayR avatar c'.ch[i] c.ch[i]) :
    NEq (D avatar c') (D avatar c) ∧ LayR avatar c' c := by
  have r := container_raw avatar he hl fun i h1 h2 => ⟨(h i h1 h2).1, (h i h1 h2).2⟩
  have hr : LayR avatar c' c := ⟨r.1, r.2⟩
  have hd := D_lay avatar hr
  refine ⟨⟨by rw [D_encoding, D_encoding, he], by rw [D_operator, D_operator, hop],
    by rw [D_compValue, D_compValue]; unfold cvOf; rw [hop, he, hcv, hr.1],
    by rw [D_leadingBytes, D_leadingBytes]; unfold lbOf; rw [he, hcv], hd.1, hd.2,
    by rw [D_children, D_children, List.length_map, List.length_map, hl],
    fun i h1 h2 => ?_⟩, hr⟩
  simp only [D_children, List.getElem_map]
  exact D_lay avatar (h i (by simpa [D_children] using h1) (by simpa [D_children] using h2))

theorem matchLocs_congr (data : Calldata) (e : Nat) (cv : List Nat) {ch ch' : List Cond}
    (hl : ch'.length = ch.length)
    (h : ∀ i (h1 : i < ch'.length) (h2 : i < ch.length), LayR avatar ch'[i] ch[i]) (v : RV) :
    matchLocs avatar data e cv ch' v = matchLocs avatar data e cv ch v := by
  have N := (D_neq avatar (c' := ⟨e, 5, cv, ch'⟩) (c := ⟨e, 5, cv, ch⟩) rfl rfl rfl hl h).1
  cases v with
  | el => rfl
  | pos l =>
    unfold matchLocs; dsimp only
    rw [N.cv, N.lb, childrenE_congr data _ N, hl]
  | win l sz =>
    unfold matchLocs; dsimp only
    rw [N.cv, N.lb, childrenE_congr data _ N, hl]

theorem append_lay {a b : Cond} (hab : LayR avatar a b) (pre post : List Cond) :
    ∀ i (h1 : i < (pre ++ a :: post).length) (h2 : i < (pre ++ b :: post).length),
      LayR avatar (pre ++ a :: post)[i] (pre ++ b :: post)[i] := by
  intro i h1 h2
  rw [List.getElem_append, List.getElem_append]
  split
  · exact LayR.refl avatar _
  · rename_i hi
    simp only [List.length_append, List.length_cons] at h1
    rw [List.getElem_cons, List.getElem_cons]
    split
    · exact hab
    · exact LayR.refl avatar _

/-- **The contract's reading meets normalization's assumptions** on
    well-typed trees. -/
theorem readWorld_normOk (env : Env) (data : Calldata) (n : Nat) :
    (readWorld avatar env data n).NormOk (inv avatar) where
  sub := fun _ h => AllN.ch _ h
  pre := fun k c hc hkw => by
    have s1 := c1_inv avatar k hc hkw fun y hy => norm_inv avatar k y (AllN.ch _ hc y hy)
    exact (unwrap_inv avatar (dedupe_inv avatar (flatten_inv avatar s1.1).1).1).1
  push := fun _ _ hc hp => (pushStep_inv avatar hc hp).1
  fields := fun k e cv ch hch v => by
    have hm := matchLocs_congr avatar data e cv (ch := ch) (ch' := ch.map (normalize k)) (by simp)
      (fun i h1 h2 => by
        simp only [List.getElem_map]; exact (norm_inv avatar k _ (hch _ (List.getElem_mem _))).2) v
    exact ⟨by show ((matchLocs avatar data e cv _ v).getD []).map RV.pos = _; rw [hm]; rfl,
      by show (matchLocs avatar data e cv _ v).isSome = _; rw [hm]; rfl⟩
  ext := fun k c hc hkw => by
    have hch : ∀ x ∈ c.ch, LayR avatar (normalize k x) x := fun x hx =>
      (norm_inv avatar k x (AllN.ch _ hc x hx)).2
    have N := (D_neq avatar (c' := { c with ch := c.ch.map (normalize k) }) (c := c) rfl rfl rfl (by simp)
      fun i h1 h2 => by simp only [List.getElem_map]; exact hch _ (List.getElem_mem _)).1
    show readExt avatar env data n _ = readExt avatar env data n c
    rw [readExt_eq, readExt_eq]
    apply readExtN_congr env data n
    · unfold keepsAsWritten at hkw
      simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne] at hkw
      exact ⟨hkw.1.2, hkw.2, hkw.1.1⟩
    · exact nodeAt_neq avatar N
    · intro hd
      exact nodeAt_ty avatar (RTy.D avatar (td_map avatar k ((AllN.self _ hc).2.2.2.1 hd)).2)
  hinge := fun e cv pre post hs hst _ x hx v => by
    have hm := matchLocs_congr avatar data e cv (ch := pre ++ orNode hs :: post) (ch' := pre ++ x :: post)
      (by simp) (append_lay avatar ((orNode_lay avatar hst x hx).2.symm) pre post) v
    exact ⟨by show ((matchLocs avatar data e cv _ v).getD []).map RV.pos = _; rw [hm]; rfl,
      by show (matchLocs avatar data e cv _ v).isSome = _; rw [hm]; rfl⟩

end
end Bridge
