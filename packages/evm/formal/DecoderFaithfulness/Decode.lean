import DecoderFaithfulness.Meta

/-!
# `AbiLocation` against the spec encoding

Throughout, `hlen : data.length < 2 ^ 255` stands for "calldata is far
smaller than `2^256` bytes" (gas limits keep real calldata below `2^32`).
It makes every offset and length word the encoder writes fit in a `uint256`.
-/

namespace DecoderFaithfulness
open Roles

theorem Placed.of_Fits {data : Bytes} {sl : Slice} {u : Val} (h : Fits data sl (enc u))
    (hcall : ∀ pre args, u = .call pre args → 0 < sl.offset) : Placed data sl u := by
  cases u with
  | call pre args => exact Or.inr ⟨hcall pre args rfl, h⟩
  | word => exact h
  | bytes => exact h
  | tuple => exact h
  | array => exact h

theorem Placed.to_Fits {data : Bytes} {sl : Slice} {u : Val} (h : Placed data sl u)
    (hl : (∀ pre args, u = .call pre args → 0 < sl.offset)) : Fits data sl (enc u) := by
  cases u with
  | call pre args =>
    rcases h with ⟨h0, _⟩ | ⟨_, h⟩
    · have := hl pre args rfl; omega
    · exact h
  | word => exact h
  | bytes => exact h
  | tuple => exact h
  | array => exact h

theorem DescAll.length_eq {s : Bool} : ∀ {cs vs}, DescAll s cs vs → cs.length = vs.length
  | _, _, .nil => rfl
  | _, _, .cons _ hs => by simp [DescAll.length_eq hs]

theorem DescAll.get {s : Bool} : ∀ {cs vs} (h : DescAll s cs vs) (i : Nat) (hi : i < cs.length),
    DescS s cs[i] (vs[i]'(by rw [← DescAll.length_eq h]; exact hi))
  | _, _, .cons h _, 0, _ => h
  | _, _, .cons _ hs, i + 1, hi => DescAll.get hs i (by simp at hi; omega)

/-! ## Slices -/

theorem Fits.at {data : Bytes} {sl : Slice} {bs : Bytes} (h : Fits data sl bs) :
    At data sl.offset bs := h.1

theorem Fits.mk' {data : Bytes} {o n : Nat} {bs : Bytes} (h : At data o bs) (hn : bs.length ≤ n) :
    Fits data ⟨o, n⟩ bs := ⟨h, hn⟩

/-- The bytes of a slice that is exactly `bs`. -/
theorem bytes_of_At {data : Bytes} {o : Nat} {bs : Bytes} (h : At data o bs) :
    (⟨o, bs.length⟩ : Slice).bytes data = bs := h.1

/-! ## `_child` -/

theorem slotSize_pos (n : Nat) : 0 < slotSize n := by unfold slotSize; split <;> omega

theorem child_inline {data : Bytes} {body : Slice} {h n : Nat} (hn : 0 < n)
    (hfit : h + n ≤ body.length) :
    child data body h n = some (⟨body.offset + h, n⟩, h + n) := by
  unfold child slotSize
  simp only [hn, ite_true]
  rw [ite_eq_right (by omega)]

theorem child_tail {data : Bytes} {body : Slice} {h off : Nat} {rest tl : Bytes}
    (hlen : data.length < 2 ^ 255)
    (hH : At data (body.offset + h) (word off ++ rest)) (hlt : h + 32 ≤ off)
    (hT : At data (body.offset + off) tl) (htl : 32 ≤ tl.length)
    (hroom : off + tl.length ≤ body.length) :
    child data body h 0 = some (⟨body.offset + off, body.length - off⟩, h + 32) := by
  have hTb := hT.bound
  have hoff : off < 2 ^ 256 := by
    have : (2 : Nat) ^ 255 < 2 ^ 256 := by decide
    omega
  unfold child slotSize
  simp only [Nat.lt_irrefl, ite_false]
  rw [ite_eq_right (by omega), load_of_At_append hH hoff, ite_eq_right (by omega)]

/-! ## What a successful read says -/

theorem child_some {data : Bytes} {body : Slice} {h isz : Nat} {sp : Slice} {next : Nat}
    (hc : child data body h isz = some (sp, next)) :
    next = h + slotSize isz ∧ h + slotSize isz ≤ body.length ∧
    ((0 < isz ∧ sp = ⟨body.offset + h, isz⟩) ∨
     (isz = 0 ∧ h + 32 ≤ load data (body.offset + h) ∧
       load data (body.offset + h) + 32 ≤ body.length ∧
       sp = ⟨body.offset + load data (body.offset + h),
         body.length - load data (body.offset + h)⟩)) := by
  unfold child at hc
  simp only at hc
  by_cases h1 : h > body.length ∨ slotSize isz > body.length - h
  · rw [ite_eq_left h1] at hc; cases hc
  · rw [ite_eq_right h1] at hc
    by_cases h2 : isz > 0
    · have hs : slotSize isz = isz := by unfold slotSize; rw [ite_eq_left h2]
      rw [ite_eq_left h2] at hc
      simp only [Option.some.injEq, Prod.mk.injEq] at hc
      obtain ⟨rfl, rfl⟩ := hc
      exact ⟨rfl, by omega, .inl ⟨h2, by rw [hs]⟩⟩
    · have hs : slotSize isz = 32 := by unfold slotSize; rw [ite_eq_right h2]
      rw [ite_eq_right h2] at hc
      by_cases h3 : load data (body.offset + h) < h + slotSize isz ∨
          load data (body.offset + h) > body.length ∨
          body.length - load data (body.offset + h) < 32
      · rw [ite_eq_left h3] at hc; cases hc
      · rw [ite_eq_right h3] at hc
        simp only [Option.some.injEq, Prod.mk.injEq] at hc
        obtain ⟨rfl, rfl⟩ := hc
        exact ⟨rfl, by omega, .inr ⟨by omega, by omega, by omega, rfl⟩⟩

theorem slicePayload_some {data : Bytes} {s : Slice} {isz : Nat} {payload : Slice}
    (h : slicePayload data s isz = some payload) :
    (0 < isz ∧ isz ≤ s.length ∧ payload = ⟨s.offset, isz⟩) ∨
    (isz = 0 ∧ 32 ≤ s.length ∧ load data s.offset ≤ s.length - 32 ∧
      payload = ⟨s.offset + 32, load data s.offset⟩) := by
  unfold slicePayload at h
  simp only at h
  by_cases h1 : isz > 0
  · rw [ite_eq_left h1] at h
    by_cases h2 : isz > s.length
    · rw [ite_eq_left h2] at h; cases h
    · rw [ite_eq_right h2] at h
      simp only [Option.some.injEq] at h
      exact .inl ⟨h1, by omega, h.symm⟩
  · rw [ite_eq_right h1] at h
    by_cases h2 : s.length < 32
    · rw [ite_eq_left h2] at h; cases h
    · rw [ite_eq_right h2] at h
      by_cases h3 : load data s.offset > s.length - 32
      · rw [ite_eq_left h3] at h; cases h
      · rw [ite_eq_right h3] at h
        simp only [Option.some.injEq] at h
        exact .inr ⟨by omega, by omega, by omega, h.symm⟩

theorem array_some {data : Bytes} {s : Slice} {isz : Nat} {body : Slice} {count : Nat}
    (h : array data s isz = some (body, count)) :
    32 ≤ s.length ∧ body = ⟨s.offset + 32, s.length - 32⟩ ∧ count = load data s.offset ∧
      count ≤ (s.length - 32) / slotSize isz := by
  unfold array at h
  simp only at h
  by_cases h1 : s.length < 32
  · rw [ite_eq_left h1] at h; cases h
  · rw [ite_eq_right h1] at h
    by_cases h2 : load data s.offset ≤ (s.length - 32) / slotSize isz
    · rw [ite_eq_left h2] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨by omega, rfl, rfl, h2⟩
    · rw [ite_eq_right h2] at h; cases h

theorem elements_some {data : Bytes} {s : Slice} {isz : Nat} {spans : List Slice}
    (h : elements data s isz = some spans) :
    32 ≤ s.length ∧
      childrenLoop data ⟨s.offset + 32, s.length - 32⟩ (fun _ => isz) (load data s.offset) 0 0 =
        some spans := by
  unfold elements at h
  cases ha : array data s isz with
  | none => rw [ha] at h; cases h
  | some q =>
    obtain ⟨body, count⟩ := q
    rw [ha] at h
    obtain ⟨h32, rfl, rfl, -⟩ := array_some ha
    exact ⟨h32, h⟩

theorem matchesBody_some {data : Bytes} {s : Slice} {c : Condition} {body : Slice}
    (h : matchesBody data s c = some body) :
    (c.encoding ≠ .AbiEncoded ∧ body = s) ∨
    (c.encoding = .AbiEncoded ∧ ∃ payload,
      ((s.offset = 0 ∧ payload = s) ∨ (s.offset ≠ 0 ∧ slicePayload data s 0 = some payload)) ∧
      c.leadingBytes ≤ payload.length ∧
      body = ⟨payload.offset + c.leadingBytes, payload.length - c.leadingBytes⟩) := by
  unfold matchesBody at h
  by_cases he : c.encoding = .AbiEncoded
  · rw [ite_eq_left he] at h
    right
    refine ⟨he, ?_⟩
    by_cases h0 : s.offset ≠ 0
    · rw [ite_eq_left h0] at h
      cases hp : slicePayload data s 0 with
      | none => rw [hp] at h; cases h
      | some payload =>
        rw [hp] at h
        simp only at h
        by_cases hl : c.leadingBytes > payload.length
        · rw [ite_eq_left hl] at h; cases h
        · rw [ite_eq_right hl] at h
          simp only [Option.some.injEq] at h
          exact ⟨payload, .inr ⟨h0, rfl⟩, by omega, h.symm⟩
    · rw [ite_eq_right h0] at h
      simp only at h
      by_cases hl : c.leadingBytes > s.length
      · rw [ite_eq_left hl] at h; cases h
      · rw [ite_eq_right hl] at h
        simp only [Option.some.injEq] at h
        exact ⟨s, .inl ⟨by omega, rfl⟩, by omega, h.symm⟩
  · rw [ite_eq_right he] at h
    simp only [Option.some.injEq] at h
    exact .inl ⟨he, h.symm⟩

/-! ## `children` loop -/

theorem childrenLoop_eq {data : Bytes} (hlen : data.length < 2 ^ 255) {s : Bool} (body : Slice)
    (sizeAt : Nat → Nat) :
    ∀ (vs : List Val) (i h off : Nat),
    (∀ k (hk : k < vs.length), ∃ c, sizeAt (i + k) = (annotate c).inlineSize ∧ DescS s c vs[k]) →
    At data (body.offset + h) (encParts vs off).1 →
    At data (body.offset + off) (encParts vs off).2 →
    h + (encParts vs off).1.length ≤ off →
    off + (encParts vs off).2.length ≤ body.length →
    ∃ spans, childrenLoop data body sizeAt vs.length i h = some spans ∧
      spans.length = vs.length ∧
      ∀ k (hk : k < spans.length) (hk' : k < vs.length),
        Fits data spans[k] (enc vs[k]) ∧ (vs[k].isStatic = false → 0 < spans[k].offset)
  | [], _, _, _, _, _, _, _, _ => ⟨[], by simp [childrenLoop], rfl, by simp⟩
  | v :: vs, i, h, off, hch, hH, hT, hinv, hroom => by
    obtain ⟨c, hc, hD⟩ := hch 0 (by simp)
    simp only [Nat.add_zero, List.getElem_cons_zero] at hc hD
    have hmeta := hD.annotate_meta
    have hge := hD.enc_ge
    have hrest : ∀ k (hk : k < vs.length), ∃ c, sizeAt (i + 1 + k) = (annotate c).inlineSize ∧
        DescS s c vs[k] := by
      intro k hk
      obtain ⟨c', h1, h2⟩ := hch (k + 1) (by simp; omega)
      exact ⟨c', by rw [← h1]; congr 1; omega, by simpa using h2⟩
    simp only [List.length_cons, childrenLoop]
    rw [hc, hmeta]
    by_cases hs : v.isStatic
    · -- static component: inline in HEAD
      simp only [encParts, hs, ite_true] at hH hT hinv hroom
      obtain ⟨hv, hH'⟩ := At_append.mp hH
      simp only [List.length_append] at hinv
      obtain ⟨spans, hl, hlen', hplaced⟩ := childrenLoop_eq hlen body sizeAt vs (i + 1)
        (h + (enc v).length) off hrest (by rw [← Nat.add_assoc]; exact hH') hT (by omega) hroom
      refine ⟨⟨body.offset + h, (enc v).length⟩ :: spans, ?_, by simp [hlen'], ?_⟩
      · simp only [hs, ite_true]
        rw [child_inline (by omega) (by omega)]
        simp [hl]
      · intro k hk hk'
        cases k with
        | zero =>
          simp
          exact ⟨Fits.mk' hv (Nat.le_refl _), by simp [hs]⟩
        | succ k => simpa using hplaced k (by simp at hk; omega) (by simp at hk'; omega)
    · -- dynamic component: offset word in HEAD, encoding in TAIL
      simp only [encParts, hs, ite_false, Bool.false_eq_true] at hH hT hinv hroom
      obtain ⟨hw, hH'⟩ := At_append.mp hH
      obtain ⟨hv, hT'⟩ := At_append.mp hT
      simp only [List.length_append, length_word] at hinv hroom
      obtain ⟨spans, hl, hlen', hplaced⟩ := childrenLoop_eq hlen body sizeAt vs (i + 1)
        (h + 32) (off + (enc v).length) hrest
        (by simp only [length_word] at hH'; rw [← Nat.add_assoc]; exact hH')
        (by rw [← Nat.add_assoc]; exact hT') (by omega) (by omega)
      refine ⟨⟨body.offset + off, body.length - off⟩ :: spans, ?_, by simp [hlen'], ?_⟩
      · simp only [hs, Bool.false_eq_true, ite_false]
        rw [child_tail hlen hH (by omega) hv hge (by omega)]
        simp [hl]
      · intro k hk hk'
        cases k with
        | zero => simp; exact ⟨Fits.mk' hv (by omega), fun _ => by omega⟩
        | succ k => simpa using hplaced k (by simp at hk; omega) (by simp at hk'; omega)

/-- A tuple's encoding, split into HEAD and TAIL as the loop expects. -/
theorem At_encTuple {data : Bytes} {loc : Nat} {vs : List Val} (h : At data loc (encTuple vs)) :
    At data (loc + 0) (encParts vs (headLen vs)).1 ∧
    At data (loc + headLen vs) (encParts vs (headLen vs)).2 ∧
    0 + (encParts vs (headLen vs)).1.length ≤ headLen vs := by
  unfold encTuple at h
  obtain ⟨h1, h2⟩ := At_append.mp h
  rw [encParts_fst_length] at h2
  exact ⟨by simpa using h1, h2, by simp [encParts_fst_length]⟩

theorem headLen_ge_count (vs : List Val) (h : ∀ v, v ∈ vs → 32 ≤ (enc v).length) :
    32 * vs.length ≤ headLen vs := by
  induction vs with
  | nil => simp [headLen]
  | cons v vs ih =>
    simp only [headLen, List.length_cons]
    have := h v (by simp)
    have := ih (fun w hw => h w (by simp [hw]))
    split <;> omega

/-! ## `AbiLocation.children` for each container -/

theorem encParts_take : ∀ (vs : List Val) (k off : Nat),
    ∃ r1 r2, (encParts vs off).1 = (encParts (vs.take k) off).1 ++ r1 ∧
      (encParts vs off).2 = (encParts (vs.take k) off).2 ++ r2
  | [], k, off => ⟨[], [], by cases k <;> simp [encParts]⟩
  | v :: vs, 0, off => ⟨(encParts (v :: vs) off).1, (encParts (v :: vs) off).2,
      by simp [encParts], by simp [encParts]⟩
  | v :: vs, k + 1, off => by
    by_cases hs : v.isStatic
    · obtain ⟨r1, r2, h1, h2⟩ := encParts_take vs k off
      exact ⟨r1, r2, by simp [encParts, hs, h1], by simp [encParts, hs, h2]⟩
    · obtain ⟨r1, r2, h1, h2⟩ := encParts_take vs k (off + (enc v).length)
      exact ⟨r1, r2, by simp [encParts, hs, h1], by simp [encParts, hs, h2]⟩

theorem encParts_snd_length_take : ∀ (vs : List Val) (k off : Nat),
    (encParts (vs.take k) off).2.length ≤ (encParts vs off).2.length := by
  intro vs k off
  obtain ⟨_, r2, _, e2⟩ := encParts_take vs k off
  rw [e2]; simp

/-- The children of a tuple (or calldata) node that describe the first
    fields of `vs`: the first spans of the spec encoding. -/
theorem children_tuple {data : Bytes} (hlen : data.length < 2 ^ 255) {s : Bool} {c : Condition}
    {vs : List Val} {body : Slice}
    (hne : (annotate c).encoding ≠ .Array) (hk : c.children.length ≤ vs.length)
    (hall : DescAll s c.children (vs.take c.children.length))
    (hfit : Fits data body (encTuple vs)) :
    ∃ spans, children data body (annotate c) = some spans ∧
      spans.length = c.children.length ∧
      ∀ k (hk : k < spans.length) (hk' : k < vs.length),
        Fits data spans[k] (enc vs[k]) ∧ (vs[k].isStatic = false → 0 < spans[k].offset) := by
  obtain ⟨hat, hroom⟩ := hfit
  unfold children
  rw [ite_eq_right hne, annotate_children]
  have hl : (c.children.map annotate).length = (vs.take c.children.length).length := by
    rw [List.length_map]; exact DescAll.length_eq hall
  rw [hl]
  obtain ⟨h1, h2, h3⟩ := At_encTuple hat
  obtain ⟨r1, r2, e1, e2⟩ := encParts_take vs c.children.length (headLen vs)
  rw [e1] at h1; rw [e2] at h2
  have h1' := (At_append.mp h1).1
  have h2' := (At_append.mp h2).1
  have h3' : 0 + (encParts (vs.take c.children.length) (headLen vs)).1.length ≤ headLen vs := by
    rw [encParts_fst_length]; have := headLen_take_le vs c.children.length; omega
  have h4' : headLen vs + (encParts (vs.take c.children.length) (headLen vs)).2.length
      ≤ body.length := by
    have := encParts_snd_length_take vs c.children.length (headLen vs)
    simp only [encTuple, List.length_append, encParts_fst_length] at hroom
    omega
  obtain ⟨spans, hloop, hlen', hpl⟩ := childrenLoop_eq hlen (s := s) body
    (fun i => ((c.children.map annotate).getD i default).inlineSize)
    (vs.take c.children.length) 0 0 (headLen vs) (by
      intro k hk
      have hkc : k < c.children.length := by rw [DescAll.length_eq hall]; exact hk
      exact ⟨c.children[k], by simp [hkc], DescAll.get hall k hkc⟩) h1' h2' h3' h4'
  refine ⟨spans, hloop, by rw [hlen', ← DescAll.length_eq hall], ?_⟩
  intro k hk hk'
  have hkt : k < (vs.take c.children.length).length := by omega
  have := hpl k hk hkt
  rw [List.getElem_take] at this
  exact this

/-- The head of an array whose elements one node describes: one slot each. -/
theorem headLen_eq_count {s : Bool} {c0 : Condition} : ∀ (vs : List Val),
    (∀ v, v ∈ vs → DescS s c0 v) →
    headLen vs = vs.length * slotSize (annotate c0).inlineSize
  | [], _ => by simp [headLen]
  | v :: vs, h => by
    have hm := (h v (by simp)).annotate_meta
    have hge := (h v (by simp)).enc_ge
    have ih := headLen_eq_count vs (fun w hw => h w (by simp [hw]))
    simp only [headLen, List.length_cons, ih, Nat.succ_mul]
    rw [hm]; unfold slotSize
    cases v.isStatic
    · simp; omega
    · simp only [ite_true]; rw [ite_eq_left (by omega)]; omega

/-- Elements read in place are static. -/
theorem allStatic_of_inline {s : Bool} {c0 : Condition} : ∀ (vs : List Val),
    (∀ v, v ∈ vs → DescS s c0 v) → (annotate c0).inlineSize > 0 → Val.allStatic vs = true
  | [], _, _ => rfl
  | v :: vs, h, hi => by
    have hmv := (h v (by simp)).annotate_meta
    simp only [Val.allStatic, Bool.and_eq_true]
    refine ⟨?_, allStatic_of_inline vs (fun w hw => h w (by simp [hw])) hi⟩
    cases hsv : v.isStatic
    · rw [hsv] at hmv; simp at hmv; omega
    · rfl

theorem array_eq {data : Bytes} (hlen : data.length < 2 ^ 255) {s : Bool} {c0 : Condition}
    {vs : List Val} {sl : Slice} (h0 : ∀ v, v ∈ vs → DescS s c0 v)
    (hfit : Fits data sl (enc (.array vs))) :
    array data sl (annotate c0).inlineSize = some (⟨sl.offset + 32, sl.length - 32⟩, vs.length) := by
  obtain ⟨hat, hroom⟩ := hfit
  rw [enc_array] at hat hroom
  obtain ⟨hw, ht⟩ := At_append.mp hat
  have hb := ht.bound
  simp only [List.length_append, length_word] at hroom hb
  have hhead := headLen_eq_count vs h0
  have hge := encTuple_length_ge vs
  have hpos := slotSize_pos (annotate c0).inlineSize
  have hcount : vs.length < 2 ^ 256 := by
    have : vs.length ≤ vs.length * slotSize (annotate c0).inlineSize :=
      Nat.le_mul_of_pos_right _ hpos
    have : (2 : Nat) ^ 255 < 2 ^ 256 := by decide
    omega
  unfold array
  rw [ite_eq_right (by omega), load_of_At hw hcount]
  simp only
  rw [ite_eq_left ((Nat.le_div_iff_mul_le hpos).mpr (by omega))]

/-- The elements of an array, with the node that describes them as size. -/
theorem elements_array {data : Bytes} (hlen : data.length < 2 ^ 255) {s : Bool} {c0 : Condition}
    {vs : List Val} {sl : Slice} (h0 : ∀ v, v ∈ vs → DescS s c0 v)
    (hfit : Fits data sl (enc (.array vs))) :
    ∃ spans, elements data sl (annotate c0).inlineSize = some spans ∧
      spans.length = vs.length ∧
      ∀ k (hk : k < spans.length) (hk' : k < vs.length),
        Fits data spans[k] (enc vs[k]) ∧ (vs[k].isStatic = false → 0 < spans[k].offset) := by
  unfold elements
  rw [array_eq hlen h0 hfit]
  obtain ⟨hat, hroom⟩ := hfit
  rw [enc_array] at hat hroom
  obtain ⟨hw, ht⟩ := At_append.mp hat
  simp only [List.length_append, length_word] at hroom ht
  obtain ⟨h1, h2, h3⟩ := At_encTuple ht
  apply childrenLoop_eq hlen (s := s) ⟨sl.offset + 32, sl.length - 32⟩ _ vs 0 0 (headLen vs) _
    h1 h2 h3
  · simp only [encTuple, List.length_append, encParts_fst_length] at hroom
    show headLen vs + _ ≤ sl.length - 32
    omega
  · intro k hk
    exact ⟨c0, rfl, h0 _ (List.getElem_mem hk)⟩

theorem children_array {data : Bytes} (hlen : data.length < 2 ^ 255) {s : Bool}
    {c c0 : Condition} {cs : List Condition} {vs : List Val} {sl : Slice}
    (he : (annotate c).encoding = .Array) (hch : c.children = c0 :: cs)
    (h0 : ∀ v, v ∈ vs → DescS s c0 v) (hfit : Fits data sl (enc (.array vs))) :
    ∃ spans, children data sl (annotate c) = some spans ∧ spans.length = vs.length ∧
      ∀ k (hk : k < spans.length) (hk' : k < vs.length),
        Fits data spans[k] (enc vs[k]) ∧ (vs[k].isStatic = false → 0 < spans[k].offset) := by
  unfold children
  rw [ite_eq_left he, annotate_children, hch]
  exact elements_array hlen h0 hfit

/-! ## `AbiLocation.slicePayload` -/

theorem slicePayload_inline {data : Bytes} {sl : Slice} {n : Nat} (hn : 0 < n)
    (hfit : n ≤ sl.length) : slicePayload data sl n = some ⟨sl.offset, n⟩ := by
  unfold slicePayload
  rw [ite_eq_left hn, ite_eq_right (by omega)]

theorem bytes_length_lt {data : Bytes} (hlen : data.length < 2 ^ 255) {l : Nat} {b : Bytes}
    (hat : At data l (encBytes b)) : b.length + 31 < 2 ^ 256 := by
  have hb := hat.bound
  rw [length_encBytes] at hb
  have : (2 : Nat) ^ 255 + 2 ^ 255 = 2 ^ 256 := by decide
  have := ceil32_ge b.length
  omega

/-- The payload of an encoded bytes value: its content. -/
theorem slicePayload_bytes {data : Bytes} (hlen : data.length < 2 ^ 255) {sl : Slice} {b : Bytes}
    (hfit : Fits data sl (encBytes b)) :
    slicePayload data sl 0 = some ⟨sl.offset + 32, b.length⟩ := by
  obtain ⟨hat, hroom⟩ := hfit
  have hw := bytes_length_lt hlen hat
  rw [length_encBytes] at hroom
  have := ceil32_ge b.length
  unfold encBytes at hat
  rw [List.append_assoc] at hat
  unfold slicePayload
  simp only [Nat.lt_irrefl, ite_false]
  rw [ite_eq_right (by omega), load_of_At_append hat (by omega), ite_eq_right (by omega)]

/-! ## `AbiLocation.sliceRegion` -/

theorem region_eq (data : Bytes) (sl : Slice) (c : Condition) :
    region data sl c =
      if c.inlineSize > 0 then
        if c.inlineSize > sl.length then none else some c.inlineSize
      else if c.encoding = .Dynamic ∨ c.encoding = .AbiEncoded then
        match slicePayload data sl 0 with
        | none => none
        | some payload =>
          if (payload.length + 31) &&& notU31 > sl.length - 32 then none
          else if payload.length % 32 ≠ 0 ∧
              (loadBytes data (sl.offset + ((payload.length + 31) &&& notU31))).drop
                (payload.length % 32) ≠ zeros (32 - payload.length % 32)
          then none
          else some (32 + ((payload.length + 31) &&& notU31))
      else if c.encoding = .None then regionNone data sl c.children
      else if c.encoding = .Array then
        match c.children with
        | [] => none
        | c0 :: _ =>
          match array data sl c0.inlineSize with
          | none => none
          | some (body, count) =>
            if c0.inlineSize > 0 then some (32 + count * c0.inlineSize)
            else
              (regionArrayLoop data body (fun sl' => region data sl' c0) count 0 (count * 32)).map
                (32 + ·)
      else if c.encoding = .Tuple then
        if headSize c.children > sl.length then none
        else regionTuple data sl c.children 0 (headSize c.children)
      else none := by
  rcases c with ⟨e, o, cs, i, lb, cv⟩
  rw [region.eq_def]
  rfl

/-- A `Dynamic` or `AbiEncoded` node that is not inlined: its region is the
    length word and the padded payload. -/
theorem region_bytes_some {data : Bytes} {sl : Slice} {c : Condition} {n : Nat}
    (hi : c.inlineSize = 0) (he : c.encoding = .Dynamic ∨ c.encoding = .AbiEncoded)
    (h : region data sl c = some n) :
    32 ≤ sl.length ∧ load data sl.offset ≤ sl.length - 32 ∧
      n = 32 + ((load data sl.offset + 31) &&& notU31) ∧
      ((load data sl.offset + 31) &&& notU31) ≤ sl.length - 32 := by
  rw [region_eq, hi, ite_eq_right (by omega), ite_eq_left he] at h
  cases hp : slicePayload data sl 0 with
  | none => rw [hp] at h; cases h
  | some payload =>
    rw [hp] at h
    simp only at h
    rcases slicePayload_some hp with ⟨h0, -⟩ | ⟨-, h32, hle, rfl⟩
    · omega
    · simp only at h
      by_cases h1 : (load data sl.offset + 31) &&& notU31 > sl.length - 32
      · rw [ite_eq_left h1] at h; cases h
      · rw [ite_eq_right h1] at h
        split at h
        · cases h
        · simp only [Option.some.injEq] at h
          exact ⟨h32, hle, h.symm, by omega⟩

theorem regionNone_all_none (data : Bytes) (sl : Slice) (cs : List Condition)
    (h : ∀ ch, ch ∈ cs → region data sl ch = none) : regionNone data sl cs = none := by
  induction cs with
  | nil => simp [regionNone]
  | cons c cs ih =>
    simp only [regionNone]
    rw [h c (by simp), ih (fun ch hm => h ch (by simp [hm]))]

theorem regionNone_first (data : Bytes) (sl : Slice) (n : Nat) (cs : List Condition)
    (h : ∀ ch, ch ∈ cs → region data sl ch = some n ∨ region data sl ch = none)
    (hex : ∃ ch, ch ∈ cs ∧ region data sl ch = some n) : regionNone data sl cs = some n := by
  induction cs with
  | nil => obtain ⟨_, hm, _⟩ := hex; simp at hm
  | cons c cs ih =>
    simp only [regionNone]
    rcases h c (by simp) with h1 | h1
    · rw [h1]
    · rw [h1]
      apply ih (fun ch hm => h ch (by simp [hm]))
      obtain ⟨ch, hm, hch⟩ := hex
      simp at hm
      rcases hm with rfl | hm
      · rw [h1] at hch; cases hch
      · exact ⟨ch, hm, hch⟩

/-- `regionNone` returns `n` if the described child comes after children
    that each give `n` or no region. -/
theorem regionNone_prefix (data : Bytes) (sl : Slice) (n : Nat) (ch0 : Condition)
    (post : List Condition) (h0 : region data sl ch0 = some n) :
    ∀ pre : List Condition,
    (∀ ch, ch ∈ pre → region data sl ch = some n ∨ region data sl ch = none) →
    regionNone data sl (pre ++ ch0 :: post) = some n
  | [], _ => by simp only [List.nil_append, regionNone]; rw [h0]
  | c :: pre, h => by
    simp only [List.cons_append, regionNone]
    rcases h c (by simp) with h1 | h1
    · rw [h1]
    · rw [h1]
      exact regionNone_prefix data sl n ch0 post h0 pre (fun ch hm => h ch (by simp [hm]))

theorem NonStruct.region_none {data : Bytes} (sl : Slice) :
    ∀ {c}, NonStruct c → region data sl (annotate c) = none
  | c, .leaf he hch hnav => by
    have hm := (NonStruct.leaf he hch hnav).meta
    rw [region_eq, annotate_inlineSize, hm.1, hm.2, annotate_encoding, annotate_children, hch]
    rcases he with he | he <;> simp [he, regionNone]
  | c, .logical he hop hall => by
    have hm := (NonStruct.logical he hop hall).meta
    rw [region_eq, annotate_inlineSize, hm.1, hm.2, annotate_encoding, annotate_children, he]
    simp
    apply regionNone_all_none
    intro ch hmem
    simp at hmem
    obtain ⟨ch', hm', rfl⟩ := hmem
    exact NonStruct.region_none sl (hall ch' hm')

theorem ceil32_rest {n : Nat} (h : n % 32 ≠ 0) : ceil32 n = n + (32 - n % 32) := by
  unfold ceil32; omega

/-- The padding of an encoded bytes value is zero, as `sliceRegion` checks. -/
theorem padding_zero {data : Bytes} {l : Nat} {b : Bytes} (hat : At data l (encBytes b))
    (hr : b.length % 32 ≠ 0) :
    (loadBytes data (l + ceil32 b.length)).drop (b.length % 32) =
      zeros (32 - b.length % 32) := by
  have hb := hat.bound
  rw [length_encBytes] at hb
  have hc := ceil32_rest hr
  have hmod := Nat.mod_lt b.length (show 32 > 0 by decide)
  unfold encBytes at hat
  obtain ⟨_, hz⟩ := At_append.mp hat
  simp only [List.length_append, length_word] at hz
  obtain ⟨hz1, hz2⟩ := hz
  simp only [length_zeros] at hz1 hz2
  unfold loadBytes
  rw [List.drop_take, List.drop_append_of_le_length (by simp; omega), List.drop_drop,
    List.take_append_of_le_length (by simp; omega)]
  have e1 : l + ceil32 b.length + b.length % 32 = l + (32 + b.length) := by omega
  have e2 : 32 - b.length % 32 = ceil32 b.length - b.length := by omega
  rw [e1, e2]; exact hz1

theorem region_dynamic {data : Bytes} (hlen : data.length < 2 ^ 255) {sl : Slice} {b : Bytes}
    {c : Condition} (hi : c.inlineSize = 0) (he : c.encoding = .Dynamic ∨ c.encoding = .AbiEncoded)
    (hfit : Fits data sl (encBytes b)) : region data sl c = some (encBytes b).length := by
  have hw := bytes_length_lt hlen hfit.at
  have hroom := hfit.2
  rw [length_encBytes] at hroom ⊢
  rw [region_eq, hi, ite_eq_right (by omega), ite_eq_left he, slicePayload_bytes hlen hfit]
  simp only
  rw [roundUp_eq _ hw, ite_eq_right (by omega), ite_eq_right]
  rintro ⟨hr, hne⟩
  exact hne (padding_zero hfit.at hr)

/-- `region` of a `Dynamic` or `AbiEncoded` node reads the length word and
    the padding. -/
theorem region_dynamicNode {data : Bytes} (hlen : data.length < 2 ^ 255) {sl : Slice} {u : Val}
    {c : Condition} (he : c.encoding = .Dynamic ∨ c.encoding = .AbiEncoded) (hu : IsBytesLike u)
    (hfit : Fits data sl (enc u)) : region data sl (annotate c) = some (enc u).length := by
  rw [enc_bytesLike hu] at hfit ⊢
  apply region_dynamic hlen _ _ hfit
  · rw [annotate_inlineSize, isInlined_eq]; rcases he with he | he <;> simp [he]
  · rw [annotate_encoding]; rcases he with he | he <;> simp [he]

mutual
  /-- Any bytes-like node, whatever interpretation it encodes, gets the region
      of a bytes value right: it reads the length word and the padding. -/
  theorem BytesLike.region_eq {data : Bytes} (hlen : data.length < 2 ^ 255) :
      ∀ {c u sl}, BytesLike c → IsBytesLike u → Fits data sl (enc u) →
      region data sl (annotate c) = some (enc u).length
    | _, _, _, .dyn he, hu, hfit => region_dynamicNode hlen (.inl he) hu hfit
    | _, _, _, .abi he, hu, hfit => region_dynamicNode hlen (.inr he) hu hfit
    | c, u, sl, .logical ch0 he hop hm0 h0 hall, hu, hfit => by
      have hi := (BytesLike.logical ch0 he hop hm0 h0 hall).meta
      rw [DecoderFaithfulness.region_eq, annotate_inlineSize, hi, annotate_encoding, he,
        annotate_children]
      simp
      apply regionNone_first data sl
      · intro ch hm
        simp at hm
        obtain ⟨ch', hm', rfl⟩ := hm
        exact BytesLikeN.region_cases hlen (hall ch' hm') hu hfit
      · exact ⟨annotate ch0, List.mem_map_of_mem hm0, BytesLike.region_eq hlen h0 hu hfit⟩

  theorem BytesLikeN.region_cases {data : Bytes} (hlen : data.length < 2 ^ 255) :
      ∀ {c u sl}, BytesLikeN c → IsBytesLike u → Fits data sl (enc u) →
      region data sl (annotate c) = some (enc u).length ∨ region data sl (annotate c) = none
    | _, _, _, .bl h, hu, hfit => Or.inl (BytesLike.region_eq hlen h hu hfit)
    | _, _, sl, .ns h, _, _ => Or.inr (NonStruct.region_none sl h)
end

/-! ## Slices stay within the calldata -/

/-- The slice lies within the calldata. -/
def Within (data : Bytes) (l : Slice) : Prop := l.offset + l.length ≤ data.length

theorem child_within {body : Slice} {data : Bytes} {h isz : Nat} {sp : Slice} {next : Nat}
    (hc : child data body h isz = some (sp, next)) :
    body.offset ≤ sp.offset ∧ sp.offset + sp.length ≤ body.offset + body.length := by
  obtain ⟨-, hroom, hsp⟩ := child_some hc
  rcases hsp with ⟨hpos, rfl⟩ | ⟨-, h1, h2, rfl⟩
  · have hs : slotSize isz = isz := by unfold slotSize; rw [ite_eq_left hpos]
    simp only; omega
  · simp only; omega

theorem childrenLoop_within {data : Bytes} {body : Slice} {f : Nat → Nat} :
    ∀ (n i h : Nat) (spans : List Slice), childrenLoop data body f n i h = some spans →
      ∀ sp ∈ spans, sp.offset + sp.length ≤ body.offset + body.length
  | 0, _, _, spans, e => by simp [childrenLoop] at e; subst e; simp
  | n + 1, i, h, spans, e => by
    simp only [childrenLoop] at e
    split at e
    · simp at e
    · rename_i sp next hc
      obtain ⟨rest, hrest, rfl⟩ := Option.map_eq_some_iff.1 e
      intro x hx
      simp at hx
      rcases hx with rfl | hx
      · exact (child_within hc).2
      · exact childrenLoop_within n _ _ rest hrest x hx

theorem elements_within {data : Bytes} {s : Slice} {isz : Nat} {spans : List Slice}
    (h : elements data s isz = some spans) :
    ∀ sp ∈ spans, sp.offset + sp.length ≤ s.offset + s.length := by
  obtain ⟨h32, h⟩ := elements_some h
  intro sp hsp
  have := childrenLoop_within _ _ _ _ h sp hsp
  simp only at this
  omega

theorem children_within {data : Bytes} {s : Slice} {c : Condition} {spans : List Slice}
    (h : children data s c = some spans) :
    ∀ sp ∈ spans, sp.offset + sp.length ≤ s.offset + s.length := by
  unfold children at h
  split at h
  · split at h
    · simp at h
    · exact elements_within h
  · exact childrenLoop_within _ _ _ _ h

theorem slicePayload_within {data : Bytes} {s : Slice} {isz : Nat} {payload : Slice}
    (h : slicePayload data s isz = some payload) :
    s.offset ≤ payload.offset ∧ payload.offset + payload.length ≤ s.offset + s.length := by
  rcases slicePayload_some h with ⟨-, h1, rfl⟩ | ⟨-, h1, h2, rfl⟩ <;> (simp only; omega)

theorem matchesBody_within {data : Bytes} {s : Slice} {c : Condition} {body : Slice}
    (h : matchesBody data s c = some body) :
    body.offset + body.length ≤ s.offset + s.length := by
  rcases matchesBody_some h with ⟨-, rfl⟩ | ⟨-, payload, hp, hlb, rfl⟩
  · exact Nat.le_refl _
  · rcases hp with ⟨-, rfl⟩ | ⟨-, hp⟩
    · simp only; omega
    · have := (slicePayload_within hp).2
      simp only; omega

theorem regionArrayLoop_le {data : Bytes} {body : Slice} {f : Slice → Option Nat}
    (hf : ∀ sl k, f sl = some k → k ≤ sl.length) :
    ∀ n h cur r, regionArrayLoop data body f n h cur = some r → cur ≤ body.length →
      cur ≤ r ∧ r ≤ body.length
  | 0, _, cur, r, e, hc => by
    simp [regionArrayLoop] at e; subst e; exact ⟨Nat.le_refl _, hc⟩
  | n + 1, h, cur, r, e, hc => by
    simp only [regionArrayLoop] at e
    split at e
    · cases e
    · split at e
      · cases e
      · rename_i len hlen
        have := hf _ _ hlen
        simp only at this
        have ih := regionArrayLoop_le hf n _ _ r e (by omega)
        exact ⟨by omega, ih.2⟩

mutual
  /-- A region fits its slice. -/
  theorem region_le (data : Bytes) : ∀ (c : Condition) (s : Slice) (n : Nat),
      region data s c = some n → n ≤ s.length
    | ⟨e, o, cs, isz, lb, cv⟩, s, n, h => by
      rw [region_eq] at h
      simp only at h
      split at h
      · split at h
        · cases h
        · simp only [Option.some.injEq] at h; omega
      split at h
      · cases hp : slicePayload data s 0 with
        | none => rw [hp] at h; cases h
        | some payload =>
          rw [hp] at h
          simp only at h
          rcases slicePayload_some hp with ⟨h0, -⟩ | ⟨-, h32, hle, rfl⟩
          · omega
          · simp only at h
            split at h
            · cases h
            · rename_i hpad
              split at h
              · cases h
              · simp only [Option.some.injEq] at h; omega
      split at h
      · exact regionNone_le data cs s n h
      split at h
      · cases cs with
        | nil => simp at h
        | cons c0 rest =>
          simp only at h
          cases ha : array data s c0.inlineSize with
          | none => rw [ha] at h; cases h
          | some q =>
            obtain ⟨body, count⟩ := q
            rw [ha] at h
            simp only at h
            obtain ⟨h32, rfl, rfl, hcount⟩ := array_some ha
            split at h
            · rename_i hpos
              simp only [Option.some.injEq] at h
              have hs : slotSize c0.inlineSize = c0.inlineSize := by
                unfold slotSize; rw [ite_eq_left hpos]
              rw [hs] at hcount
              have h1 := Nat.div_mul_le_self (s.length - 32) c0.inlineSize
              have h2 := Nat.mul_le_mul_right c0.inlineSize hcount
              omega
            · rename_i hpos
              have hs : slotSize c0.inlineSize = 32 := by
                unfold slotSize; rw [ite_eq_right hpos]
              rw [hs] at hcount
              cases hl : regionArrayLoop data ⟨s.offset + 32, s.length - 32⟩
                  (fun sl' => region data sl' c0) (load data s.offset) 0
                  (load data s.offset * 32) with
              | none => rw [hl] at h; cases h
              | some r =>
                rw [hl] at h
                simp only [Option.map_some, Option.some.injEq] at h
                have h1 := Nat.div_mul_le_self (s.length - 32) 32
                have h2 := Nat.mul_le_mul_right 32 hcount
                have := (regionArrayLoop_le (fun sl k hk => region_le data c0 sl k hk) _ _ _ _ hl
                  (by simp only; omega)).2
                simp only at this
                omega
      split at h
      · split at h
        · cases h
        · exact (regionTuple_le data cs s 0 _ n h (by omega)).2
      · cases h

  theorem regionNone_le (data : Bytes) : ∀ (cs : List Condition) (s : Slice) (n : Nat),
      regionNone data s cs = some n → n ≤ s.length
    | [], _, _, h => by simp [regionNone] at h
    | c :: cs, s, n, h => by
      simp only [regionNone] at h
      cases hr : region data s c with
      | some k =>
        rw [hr] at h
        simp only [Option.some.injEq] at h
        subst h
        exact region_le data c s k hr
      | none => rw [hr] at h; exact regionNone_le data cs s n h

  theorem regionTuple_le (data : Bytes) : ∀ (cs : List Condition) (body : Slice) (h cur n : Nat),
      regionTuple data body cs h cur = some n → cur ≤ body.length → cur ≤ n ∧ n ≤ body.length
    | [], _, _, cur, n, e, hc => by
      simp [regionTuple] at e; subst e; exact ⟨Nat.le_refl _, hc⟩
    | c :: cs, body, h, cur, n, e, hc => by
      simp only [regionTuple] at e
      split at e
      · exact regionTuple_le data cs body _ cur n e hc
      · split at e
        · cases e
        · cases hr : region data ⟨body.offset + cur, body.length - cur⟩ c with
          | none => rw [hr] at e; cases e
          | some len =>
            rw [hr] at e
            simp only at e
            have := region_le data c _ len hr
            simp only at this
            have ih := regionTuple_le data cs body _ _ n e (by omega)
            exact ⟨by omega, ih.2⟩
end

/-- An operand starts where its slice does, and fits it. -/
theorem operand_some {data : Bytes} {s : Slice} {z : Nat} {c : Condition} {op : Slice}
    (h : operand data s z c = some op) : op.offset = s.offset ∧ op.length ≤ s.length := by
  unfold operand at h
  split at h
  · rcases slicePayload_some h with ⟨-, hle, rfl⟩ | ⟨h0, -⟩
    · exact ⟨rfl, hle⟩
    · omega
  · unfold sliceRegion at h
    cases hr : region data s c with
    | none => rw [hr] at h; cases h
    | some n =>
      rw [hr] at h
      simp only [Option.map_some, Option.some.injEq] at h
      rw [← h]
      exact ⟨rfl, region_le data c s n hr⟩

/-- The span a `Pluck` stored, when a Zip decodes an array in it, starts
    where the `Pluck` was evaluated, and fits its slice. -/
theorem pluckSpan_some {data : Bytes} {L : Slice} {yk : Nat} {pk : Condition} {op : Slice}
    {isz : Nat} {spans : List Slice} (h : pluckSpan data L yk pk = some op)
    (he : elements data op isz = some spans) : op.offset = L.offset ∧ op.length ≤ L.length := by
  unfold pluckSpan at h
  split at h
  · simp only [Option.some.injEq] at h
    subst h
    have := (elements_some he).1
    simp at this
  · exact operand_some h

/-- Every slice `evaluate` visits from a slice within the calldata lies
    within the calldata. -/
theorem Visit.within {data : Bytes} {c : Condition} {loc : Slice} {z : Nat} {p : List Nat}
    {d : Condition} {l : Slice} {y : Nat} (hv : Visit data c loc z p d l y) :
    Within data loc → Within data l := by
  unfold Within
  induction hv with
  | here => exact id
  | logical _ _ _ _ ih => exact ih
  | matchesChild body spans i hi _ hbody hch _ _ ih =>
    intro h
    have h1 := matchesBody_within hbody
    have h2 := children_within hch _ (List.getElem_mem hi)
    exact ih (by omega)
  | arrayIter spans i hi _ hch _ ih =>
    intro h
    have h2 := children_within hch _ (List.getElem_mem hi)
    exact ih (by omega)
  | arrayTail spans j hj _ hch _ _ _ ih =>
    intro h
    have h2 := children_within hch _ (List.getElem_mem hj)
    exact ih (by omega)
  | slice payload _ hpay hle _ ih =>
    intro h
    have h1 := slicePayload_within hpay
    exact ih (by simp only; omega)

/-- ... Zip jumps included. -/
theorem Eval.within {data : Bytes} {root : Condition} {p : List Nat} {d : Condition}
    {l : Slice} {y : Nat} (he : Eval data root p d l y) : Within data l := by
  induction he with
  | visit hv => exact Visit.within hv (by unfold Within; simp)
  | zip f op spans i hi _ _ _ _ _ _ hop hch hvis _ ihpk =>
    apply Visit.within hvis
    have h1 := pluckSpan_some hop hch
    have h2 := elements_within hch _ (List.getElem_mem hi)
    unfold Within at ihpk ⊢
    omega

/-- The head of a tuple node, given its children's metadata. -/
theorem headSize_eq {s : Bool} : ∀ {cs : List Condition} {vs : List Val}, DescAll s cs vs →
    headSize (cs.map annotate) = headLen vs
  | _, _, .nil => rfl
  | _, _, .cons (v := v) h hs => by
    have hm := h.annotate_meta
    have hge := h.enc_ge
    simp only [List.map_cons, headSize, headLen, headSize_eq hs, hm]
    unfold slotSize
    cases v.isStatic
    · simp
    · simp only [ite_true]; rw [ite_eq_left (by omega)]

/-- Tuple loop of `region`, given correct regions for each component. -/
theorem regionTuple_eq {data : Bytes} (hlen : data.length < 2 ^ 255) {s : Bool} (body : Slice) :
    ∀ (cs : List Condition) (vs : List Val) (h off : Nat) (hl : cs.length = vs.length),
    (∀ k (hk : k < cs.length), ∃ c, cs[k] = annotate c ∧ DescS s c (vs[k]'(by omega)) ∧
      ∀ sl, Fits data sl (enc (vs[k]'(by omega))) →
        region data sl cs[k] = some (enc (vs[k]'(by omega))).length) →
    At data (body.offset + h) (encParts vs off).1 →
    At data (body.offset + off) (encParts vs off).2 →
    off + (encParts vs off).2.length ≤ body.length →
    regionTuple data body cs h off = some (off + (encParts vs off).2.length)
  | [], [], _, _, _, _, _, _, _ => by simp [regionTuple, encParts]
  | [], _ :: _, _, _, hl, _, _, _, _ => by simp at hl
  | _ :: _, [], _, _, hl, _, _, _, _ => by simp at hl
  | ch :: cs, v :: vs, h, off, hl, hch, hH, hT, hroom => by
    obtain ⟨c, hc, hD, hsz⟩ := hch 0 (by simp)
    simp only [List.getElem_cons_zero] at hc hD hsz
    have hmeta := hD.annotate_meta
    have hge := hD.enc_ge
    have hrest : ∀ k (hk : k < cs.length), ∃ c, cs[k] = annotate c ∧
        DescS s c (vs[k]'(by simp at hl; omega)) ∧
        ∀ sl, Fits data sl (enc (vs[k]'(by simp at hl; omega))) →
          region data sl cs[k] = some (enc (vs[k]'(by simp at hl; omega))).length := by
      intro k hk
      obtain ⟨c', h1, h2, h4⟩ := hch (k + 1) (by simp; omega)
      exact ⟨c', by simpa using h1, by simpa using h2,
        fun sl hsl => by simpa using h4 sl (by simpa using hsl)⟩
    have hl' : cs.length = vs.length := by simpa using hl
    simp only [regionTuple]
    rw [hc, hmeta]
    by_cases hs : v.isStatic
    · simp only [encParts, hs, ite_true] at hH hT hroom ⊢
      obtain ⟨hv, hH'⟩ := At_append.mp hH
      rw [ite_eq_left (by omega)]
      exact regionTuple_eq hlen body cs vs (h + (enc v).length) off hl' hrest
        (by rw [← Nat.add_assoc]; exact hH') hT hroom
    · simp only [encParts, hs, ite_false, Bool.false_eq_true] at hH hT hroom ⊢
      obtain ⟨hw, hH'⟩ := At_append.mp hH
      obtain ⟨hv, hT'⟩ := At_append.mp hT
      simp only [List.length_append] at hroom ⊢
      have hTb := hv.bound
      have hoff : off < 2 ^ 256 := by
        have : (2 : Nat) ^ 255 < 2 ^ 256 := by decide
        omega
      simp only [Nat.lt_irrefl, ite_false]
      rw [load_of_At_append hH hoff]
      simp only [ne_eq, not_true_eq_false, ite_false]
      rw [← hc, hsz _ (Fits.mk' hv (by omega))]
      simp only
      rw [regionTuple_eq hlen body cs vs (h + 32) (off + (enc v).length) hl' hrest
        (by simp only [length_word] at hH'; rw [← Nat.add_assoc]; exact hH')
        (by rw [← Nat.add_assoc]; exact hT') (by omega)]
      congr 1; omega

/-- Array loop of `region`, for referenced elements with correct regions. -/
theorem regionArrayLoop_eq {data : Bytes} (hlen : data.length < 2 ^ 255) (body : Slice)
    (regionOf : Slice → Option Nat) :
    ∀ (vs : List Val) (h off : Nat), (∀ v, v ∈ vs → v.isStatic = false) →
    (∀ sl v, v ∈ vs → Fits data sl (enc v) → regionOf sl = some (enc v).length) →
    At data (body.offset + h) (encParts vs off).1 →
    At data (body.offset + off) (encParts vs off).2 →
    off + (encParts vs off).2.length ≤ body.length →
    regionArrayLoop data body regionOf vs.length h off = some (off + (encParts vs off).2.length)
  | [], _, _, _, _, _, _, _ => by simp [regionArrayLoop, encParts]
  | v :: vs, h, off, hdyn, hsz, hH, hT, hroom => by
    have hs := hdyn v (by simp)
    simp only [encParts, hs, ite_false, Bool.false_eq_true] at hH hT hroom ⊢
    obtain ⟨hw, hH'⟩ := At_append.mp hH
    obtain ⟨hv, hT'⟩ := At_append.mp hT
    simp only [List.length_append] at hroom ⊢
    have hTb := hv.bound
    have hoff : off < 2 ^ 256 := by
      have : (2 : Nat) ^ 255 < 2 ^ 256 := by decide
      omega
    simp only [List.length_cons, regionArrayLoop]
    rw [load_of_At_append hH hoff]
    simp only [ne_eq, not_true_eq_false, ite_false]
    rw [hsz _ v (by simp) (Fits.mk' hv (by omega))]
    simp only
    rw [regionArrayLoop_eq hlen body regionOf vs (h + 32) (off + (enc v).length)
      (fun w hw => hdyn w (by simp [hw])) (fun sl w hw => hsz sl w (by simp [hw]))
      (by simp only [length_word] at hH'; rw [← Nat.add_assoc]; exact hH')
      (by rw [← Nat.add_assoc]; exact hT') (by omega)]
    congr 1; omega

theorem region_inline {data : Bytes} {sl : Slice} {c : Condition} (hi : 0 < c.inlineSize)
    (hfit : c.inlineSize ≤ sl.length) : region data sl c = some c.inlineSize := by
  rw [region_eq, ite_eq_left hi, ite_eq_right (by omega)]

/-- A static value is read in place. -/
theorem region_static {data : Bytes} {s : Bool} {sl : Slice} {c : Condition} {u : Val}
    (hD : DescS s c u) (hs : u.isStatic = true) (hfit : Fits data sl (enc u)) :
    region data sl (annotate c) = some (enc u).length := by
  have hm := hD.annotate_meta
  have hge := hD.enc_ge
  rw [hs] at hm; simp only [ite_true] at hm
  rw [region_inline (by omega) (by rw [hm]; exact hfit.2), hm]

theorem exactTy_eq (c : Condition) : exactTy c =
    (c.encoding == .AbiEncoded || c.operator == .Slice || (!isNavOp c.operator && exactTyAll c.children)) := by
  rcases c with ⟨e, op, cs, sz, lb, cv⟩; rfl

theorem exactTyAll_get : ∀ {cs : List Condition}, exactTyAll cs = true →
    ∀ k (hk : k < cs.length), exactTy cs[k] = true
  | c :: cs, h, 0, _ => by simp only [exactTyAll, Bool.and_eq_true] at h; exact h.1
  | c :: cs, h, k + 1, hk => by
    simp only [exactTyAll, Bool.and_eq_true] at h
    exact exactTyAll_get h.2 k (by simp at hk; omega)

theorem exactTy_parts {c : Condition} (h : exactTy c = true) (he : c.encoding ≠ .AbiEncoded)
    (ho : c.operator ≠ .Slice) : isNavOp c.operator = false ∧ exactTyAll c.children = true := by
  rw [exactTy_eq] at h; simpa [he, ho] using h

theorem ne_slice_of {op : Operator} (h : (isNavOp op = false ∧ True) ∨ op ≠ .Slice) : op ≠ .Slice := by
  rcases h with ⟨h, -⟩ | h
  · intro e; rw [e] at h; simp [isNavOp] at h
  · exact h

mutual
  /-- `AbiLocation.sliceRegion` returns the length of the spec encoding, for a
      node whose subtree does not navigate (what `_read` reads the region
      of). -/
  theorem Desc.region_eq {data : Bytes} (hlen : data.length < 2 ^ 255) {s : Bool} :
      ∀ {c u sl}, Desc s c u → exactTy c = true → Fits data sl (enc u) →
      region data sl (annotate c) = some (enc u).length
    | _, _, _, .word he hch hnav hw, _, hfit =>
      region_static (s := s) (.desc (.word he hch hnav hw)) rfl hfit
    | _, _, _, .sliceWord he hop hch h1 h32 hwin hw, _, hfit =>
      region_static (s := s) (.desc (.sliceWord he hop hch h1 h32 hwin hw)) rfl hfit
    | _, _, _, .bytes he _ _ hu, _, hfit => region_dynamicNode hlen (.inl he) hu hfit
    | _, _, _, .sliceBytes he _ _ _ _ _ hu, _, hfit => region_dynamicNode hlen (.inl he) hu hfit
    | _, _, _, .call he _ _ _ _ _, _, hfit => region_dynamicNode hlen (.inr he) trivial hfit
    | c, _, sl, .tuple (vs := vs) he hne hk hall0 hpre hop, hnn, hfit => by
      have hD : Desc s c (.tuple vs) := .tuple he hne hk hall0 hpre hop
      by_cases hst : (Val.tuple vs).isStatic = true
      · exact region_static (.desc hD) hst hfit
      have hp := exactTy_parts hnn (by rw [he]; decide) (ne_slice_of (by
        rcases hop with ⟨h, -⟩ | h
        · exact .inl ⟨h, trivial⟩
        · rw [h]; exact .inr (by decide)))
      have hkeq : c.children.length = vs.length := by
        by_cases hlt : c.children.length < vs.length
        · have := (hpre hlt).2
          rw [this] at hp; simp [isNavOp] at hp
        · omega
      have htake : vs.take c.children.length = vs := List.take_of_length_le (by omega)
      have hall : DescAll s c.children vs := htake ▸ hall0
      have hm := hD.annotate_meta
      rw [ite_eq_right hst] at hm
      obtain ⟨hat, hroom⟩ := hfit
      rw [enc_tuple] at hat hroom ⊢
      have hge := encTuple_length_ge vs
      rw [DecoderFaithfulness.region_eq, hm, ite_eq_right (by omega), annotate_encoding, he,
        annotate_children, headSize_eq hall]
      simp only [reduceCtorEq, ite_false, false_or, ite_true]
      rw [ite_eq_right (by omega)]
      obtain ⟨h1, h2, h3⟩ := At_encTuple hat
      rw [regionTuple_eq hlen (s := s) sl _ vs 0 (headLen vs)
        (by simp [DescAll.length_eq hall]) ?_ h1 h2
        (by simpa [encTuple, encParts_fst_length] using hroom)]
      · simp [encTuple, encParts_fst_length]
      · intro k hk
        have hkc : k < c.children.length := by simpa using hk
        have hkv : k < vs.length := by rw [← DescAll.length_eq hall]; exact hkc
        refine ⟨c.children[k], by simp, DescAll.get hall k hkc, ?_⟩
        intro sl' hsl'
        simp only [List.getElem_map]
        exact DescAll.regions hlen hall hp.2 k hkc hkv sl' hsl'
    | c, _, sl, .array (vs := vs) c0 cs he hch h0 h1' h2' hop, hnn, hfit => by
      have hD : Desc s c (.array vs) := .array c0 cs he hch h0 h1' h2' hop
      have hp := exactTy_parts hnn (by rw [he]; decide) (ne_slice_of (by
        rcases hop with ⟨h, -⟩ | h | h | h | h
        · exact .inl ⟨h, trivial⟩
        all_goals (rw [h]; exact .inr (by decide))))
      have hn0 : exactTy c0 = true := by
        have := exactTyAll_get hp.2 0 (by rw [hch]; simp)
        simpa [hch] using this
      have hm := hD.annotate_meta
      simp only [Val.isStatic, Bool.false_eq_true, ite_false] at hm
      have harr := array_eq hlen h0 hfit
      obtain ⟨hat, hroom⟩ := hfit
      rw [enc_array] at hat hroom ⊢
      obtain ⟨hw, ht⟩ := At_append.mp hat
      simp only [List.length_append, length_word] at hroom ht ⊢
      rw [DecoderFaithfulness.region_eq, hm, ite_eq_right (by omega), annotate_encoding, he,
        annotate_children, hch]
      simp only [reduceCtorEq, ite_false, false_or, ite_true, List.map_cons]
      rw [harr]
      simp only
      obtain ⟨h1, h2, h3⟩ := At_encTuple ht
      have hhead := headLen_eq_count vs h0
      by_cases hi : (annotate c0).inlineSize > 0
      · -- static elements: no tails
        rw [ite_eq_left hi]
        have hall := allStatic_of_inline vs h0 hi
        rw [encTuple_length_static vs hall, hhead]
        unfold slotSize; rw [ite_eq_left hi]
      · rw [ite_eq_right hi]
        have hi0 : (annotate c0).inlineSize = 0 := by omega
        have hdyn : ∀ v, v ∈ vs → v.isStatic = false := by
          intro v hv
          have hmv := (h0 v hv).annotate_meta
          have hgev := (h0 v hv).enc_ge
          cases hsv : v.isStatic
          · rfl
          · rw [hsv, hi0] at hmv; simp at hmv; omega
        have h32 : vs.length * 32 = headLen vs := by
          rw [hhead, hi0]; rfl
        rw [h32, regionArrayLoop_eq hlen ⟨sl.offset + 32, sl.length - 32⟩ _ vs 0 (headLen vs) hdyn
          (fun sl' v hv hsl' => DescS.region_eq hlen (h0 v hv) hn0 hsl') h1 h2
          (by
            simp only [encTuple, List.length_append, encParts_fst_length] at hroom
            show headLen vs + _ ≤ sl.length - 32
            omega)]
        simp [encTuple, encParts_fst_length]
    | _, _, _, .logical _ he hop _ _ _ _, hnn, _ => by
      have hp := exactTy_parts hnn (by rw [he]; decide) (by rcases hop with h | h <;> rw [h] <;> decide)
      rcases hop with h | h <;> (rw [h] at hp; simp [isNavOp] at hp)

  theorem DescS.region_eq {data : Bytes} (hlen : data.length < 2 ^ 255) {s : Bool} :
      ∀ {c u sl}, DescS s c u → exactTy c = true → Fits data sl (enc u) →
      region data sl (annotate c) = some (enc u).length
    | _, _, _, .desc h, hnn, hfit => Desc.region_eq hlen h hnn hfit
    | _, _, _, .stray _ hb hu, _, hfit => BytesLike.region_eq hlen hb hu hfit

  theorem DescAll.regions {data : Bytes} (hlen : data.length < 2 ^ 255) {s : Bool} :
      ∀ {cs vs}, DescAll s cs vs → exactTyAll cs = true →
      ∀ k (hk : k < cs.length) (hkv : k < vs.length) sl, Fits data sl (enc vs[k]) →
      region data sl (annotate cs[k]) = some (enc vs[k]).length
    | _, _, .cons h _, hnn, 0, _, _, _, hfit => by
      simp only [exactTyAll, Bool.and_eq_true] at hnn
      exact DescS.region_eq hlen h hnn.1 hfit
    | _, _, .cons _ hs, hnn, k + 1, hk, hkv, sl, hfit => by
      simp only [exactTyAll, Bool.and_eq_true] at hnn
      simp only [List.getElem_cons_succ] at hfit ⊢
      exact DescAll.regions hlen hs hnn.2 k (by simp at hk; omega) (by simp at hkv; omega) sl hfit
end

end DecoderFaithfulness
