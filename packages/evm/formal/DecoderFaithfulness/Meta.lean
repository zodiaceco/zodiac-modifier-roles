import DecoderFaithfulness.Basic

/-!
# Metadata: `Topology` + pack/unpack agree with the ABI spec

For a tree that describes value `u`, the evaluator's `inlined` flag is
"`u` is static" and `size` is the length of `u`'s encoding (0 for dynamic
values).
-/

namespace DecoderFaithfulness
open Roles

/-! ## Equation lemmas for the transcription -/

theorem isInlined_eq (c : Condition) :
    isInlined c = if c.encoding = .Dynamic ∨ c.encoding = .Array ∨ c.encoding = .AbiEncoded
      then false else isInlinedAll c.children := by
  cases c; simp [isInlined]

theorem inlinedSize_eq (c : Condition) :
    inlinedSize c = if c.encoding = .Static then 32
      else inlinedSizeLoop (decide (c.encoding = .None)) c.children := by
  cases c; simp [inlinedSize]

theorem isInlinedAll_eq (cs : List Condition) : isInlinedAll cs = cs.all isInlined := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp [isInlinedAll, ih]

theorem annotate_eq (c : Condition) :
    annotate c =
      { encoding := if c.encoding = .EtherValue then .None else c.encoding
        operator := if c.operator = .EqualToAvatar then .EqualTo else c.operator
        children := c.children.map annotate
        inlined := decide ((if isInlined c then inlinedSize c else 0) > 0)
        size := if isInlined c then inlinedSize c else 0
        leadingBytes := if c.encoding = .AbiEncoded then c.leadingBytes else 0
        compValue := c.compValue } := by
  rcases c with ⟨e, o, cs, i, s, lb, cv⟩
  rw [annotate]
  simp

theorem annotate_children (c : Condition) : (annotate c).children = c.children.map annotate := by
  rw [annotate_eq]

theorem annotate_operator (c : Condition) :
    (annotate c).operator = if c.operator = .EqualToAvatar then .EqualTo else c.operator := by
  rw [annotate_eq]

theorem annotate_encoding (c : Condition) :
    (annotate c).encoding = if c.encoding = .EtherValue then .None else c.encoding := by
  rw [annotate_eq]

theorem annotate_leadingBytes (c : Condition) :
    (annotate c).leadingBytes = if c.encoding = .AbiEncoded then c.leadingBytes else 0 := by
  rw [annotate_eq]

theorem annotate_size (c : Condition) :
    (annotate c).size = if isInlined c then inlinedSize c else 0 := by
  rw [annotate_eq]

theorem annotate_inlined (c : Condition) :
    (annotate c).inlined = decide ((if isInlined c then inlinedSize c else 0) > 0) := by
  rw [annotate_eq]

theorem annotate_compValue (c : Condition) : (annotate c).compValue = c.compValue := by
  rw [annotate_eq]

/-! ## Loop helpers -/

theorem inlinedSizeLoop_zero (b : Bool) (cs : List Condition)
    (h : ∀ ch, ch ∈ cs → inlinedSize ch = 0) : inlinedSizeLoop b cs = 0 := by
  induction cs with
  | nil => simp [inlinedSizeLoop]
  | cons c cs ih =>
    simp only [inlinedSizeLoop]
    rw [h c (by simp), ih (fun ch hm => h ch (by simp [hm]))]
    simp

theorem inlinedSizeLoop_first (cs : List Condition) (s : Nat) (hs : 0 < s)
    (h : ∀ ch, ch ∈ cs → inlinedSize ch = 0 ∨ inlinedSize ch = s)
    (hex : ∃ ch, ch ∈ cs ∧ inlinedSize ch = s) : inlinedSizeLoop true cs = s := by
  induction cs with
  | nil => obtain ⟨_, hm, _⟩ := hex; simp at hm
  | cons c cs ih =>
    simp only [inlinedSizeLoop]
    rcases h c (by simp) with h0 | h1
    · rw [h0]
      have hex' : ∃ ch, ch ∈ cs ∧ inlinedSize ch = s := by
        obtain ⟨ch, hm, hch⟩ := hex
        simp at hm
        rcases hm with rfl | hm
        · omega
        · exact ⟨ch, hm, hch⟩
      simp [ih (fun ch hm => h ch (by simp [hm])) hex']
    · rw [h1]; simp [hs]

/-! ## Non-structural, bytes-like and slice-child nodes -/

theorem NonStruct.meta : ∀ {c}, NonStruct c → isInlined c = true ∧ inlinedSize c = 0
  | c, .leaf he hch _ => by
    rw [isInlined_eq, inlinedSize_eq, hch]
    rcases he with he | he <;> simp [he, isInlinedAll, inlinedSizeLoop]
  | c, .logical he _ hall => by
    rw [isInlined_eq, inlinedSize_eq, he, isInlinedAll_eq]
    have hm := fun ch (hm : ch ∈ c.children) => NonStruct.meta (hall ch hm)
    refine ⟨?_, ?_⟩
    · simp
      intro ch hch
      exact (hm ch hch).1
    · simp
      exact inlinedSizeLoop_zero _ _ (fun ch hch => (hm ch hch).2)

theorem BytesLike.meta : ∀ {c}, BytesLike c → isInlined c = false
  | c, .dyn he => by rw [isInlined_eq, he]; simp
  | c, .abi he => by rw [isInlined_eq, he]; simp
  | c, .logical ch0 he _ hm0 h0 _ => by
    rw [isInlined_eq, he, isInlinedAll_eq]
    simp
    exact ⟨ch0, hm0, BytesLike.meta h0⟩

theorem Win.meta : ∀ {c}, Win c → isInlined c = true ∧ inlinedSize c = 32
  | c, .leaf he hch _ => by
    rw [isInlined_eq, inlinedSize_eq, hch, he]; simp [isInlinedAll]
  | c, .slice he _ hch _ _ hw => by
    rw [isInlined_eq, inlinedSize_eq, hch, he]
    simp [isInlinedAll, (Win.meta hw).1]

/-! ## Structural nodes -/

mutual
  theorem Desc.meta {s : Bool} : ∀ {c u}, Desc s c u →
      isInlined c = u.isStatic ∧ (u.isStatic = true → inlinedSize c = (enc u).length)
    | c, _, .word he hch _ hw => by
      rw [isInlined_eq, inlinedSize_eq, hch, he]
      simp [isInlinedAll, Val.isStatic, enc, hw]
    | c, _, .bytes he _ _ hu => by
      rw [isInlined_eq, he, isStatic_bytesLike hu]; simp
    | c, _, .sliceWord he _ hch _ _ hw hlen => by
      rw [isInlined_eq, inlinedSize_eq, hch, he]
      simp [isInlinedAll, (Win.meta hw).1, Val.isStatic, enc, hlen]
    | c, _, .sliceBytes he _ _ _ _ _ hu => by
      rw [isInlined_eq, he, isStatic_bytesLike hu]; simp
    | c, _, .tuple (vs := vs) he _ hall _ => by
      rw [isInlined_eq, inlinedSize_eq, he]
      have := DescAll.meta hall
      simp [Val.isStatic, this.1]
      intro hst
      rw [this.2 hst, enc_tuple, encTuple_length_static vs hst]
    | c, _, .array _ _ he _ _ _ _ _ => by
      rw [isInlined_eq, he]; simp [Val.isStatic]
    | c, _, .call he _ _ _ _ => by
      rw [isInlined_eq, he]; simp [Val.isStatic]
    | c, u, .logical ch0 he _ hm0 h0 hall => by
      have hns : ∀ ch, ch ∈ c.children →
          (isInlined ch = u.isStatic ∧ (u.isStatic = true → inlinedSize ch = (enc u).length)) ∨
          (isInlined ch = true ∧ inlinedSize ch = 0) :=
        fun ch hm => DescSN.meta (hall ch hm)
      have m0 := DescS.meta h0
      rw [isInlined_eq, inlinedSize_eq, he, isInlinedAll_eq]
      refine ⟨?_, ?_⟩
      · simp
        cases hst : u.isStatic
        · rw [hst] at m0
          apply Bool.eq_false_iff.mpr
          intro hall'
          simp [List.all_eq_true] at hall'
          have := hall' ch0 hm0
          rw [m0.1] at this; exact Bool.false_ne_true this
        · simp [List.all_eq_true]
          intro ch hm
          rcases hns ch hm with h | h
          · rw [h.1, hst]
          · exact h.1
      · intro hst
        simp
        have hpos : 0 < (enc u).length := by have := DescS.enc_ge h0; omega
        apply inlinedSizeLoop_first _ _ hpos
        · intro ch hm
          rcases hns ch hm with h | h
          · exact Or.inr (h.2 hst)
          · exact Or.inl h.2
        · exact ⟨ch0, hm0, (m0.2 hst)⟩

  theorem DescAll.meta {s : Bool} : ∀ {cs vs}, DescAll s cs vs →
      isInlinedAll cs = Val.allStatic vs ∧
      (Val.allStatic vs = true → inlinedSizeLoop false cs = headLen vs)
    | _, _, .nil => by simp [isInlinedAll, Val.allStatic, inlinedSizeLoop, headLen]
    | _, _, .cons h hs => by
      have m := DescS.meta h
      have ms := DescAll.meta hs
      refine ⟨by simp [isInlinedAll, Val.allStatic, m.1, ms.1], ?_⟩
      intro hst
      simp [Val.allStatic] at hst
      simp [inlinedSizeLoop, headLen, m.2 hst.1, ms.2 hst.2, hst.1]

  theorem DescS.meta {s : Bool} : ∀ {c u}, DescS s c u →
      isInlined c = u.isStatic ∧ (u.isStatic = true → inlinedSize c = (enc u).length)
    | _, _, .desc h => Desc.meta h
    | _, _, .stray _ hb hu => by
      rw [BytesLike.meta hb, isStatic_bytesLike hu]; simp

  theorem DescSN.meta {s : Bool} : ∀ {c u}, DescSN s c u →
      (isInlined c = u.isStatic ∧ (u.isStatic = true → inlinedSize c = (enc u).length)) ∨
      (isInlined c = true ∧ inlinedSize c = 0)
    | _, _, .ds h => Or.inl (DescS.meta h)
    | _, _, .ns h => Or.inr (NonStruct.meta h)

  /-- Every described value is at least one word. -/
  theorem DescS.enc_ge {s : Bool} : ∀ {c u}, DescS s c u → 32 ≤ (enc u).length
    | _, _, .desc h => Desc.enc_ge h
    | _, _, .stray _ _ hu => by rw [enc_bytesLike hu, length_encBytes]; omega

  theorem Desc.enc_ge {s : Bool} : ∀ {c u}, Desc s c u → 32 ≤ (enc u).length
    | _, _, .word _ _ _ hw => by simp [enc, hw]
    | _, _, .bytes _ _ _ hu => by rw [enc_bytesLike hu, length_encBytes]; omega
    | _, _, .sliceWord _ _ _ _ _ _ hw => by simp [enc, hw]
    | _, _, .sliceBytes _ _ _ _ _ _ hu => by rw [enc_bytesLike hu, length_encBytes]; omega
    | _, _, .tuple _ hne hall _ => by
      rw [enc_tuple]
      exact Nat.le_trans (DescAll.headLen_ge hall hne) (encTuple_length_ge _)
    | _, _, .array _ _ _ _ _ _ _ _ => by simp [enc_array]
    | _, _, .call _ _ _ _ _ => by simp [enc_call, length_encBytes]
    | _, _, .logical _ _ _ _ h0 _ => DescS.enc_ge h0

  theorem DescAll.headLen_ge {s : Bool} : ∀ {cs vs}, DescAll s cs vs → vs ≠ [] →
      32 ≤ headLen vs
    | _, _, .nil, hne => absurd rfl hne
    | _, _, .cons h _, _ => by
      simp only [headLen]
      split
      · have := DescS.enc_ge h; omega
      · omega
end

/-- The metadata the evaluator reads for a structural node. -/
theorem DescS.annotate_meta {s : Bool} {c : Condition} {u : Val} (h : DescS s c u) :
    (annotate c).inlined = u.isStatic ∧
    (annotate c).size = if u.isStatic then (enc u).length else 0 := by
  have m := DescS.meta h
  have hge := DescS.enc_ge h
  rw [annotate_inlined, annotate_size, m.1]
  cases hst : u.isStatic
  · simp
  · simp [m.2 hst]; omega

theorem Desc.annotate_meta {s : Bool} {c : Condition} {u : Val} (h : Desc s c u) :
    (annotate c).inlined = u.isStatic ∧
    (annotate c).size = if u.isStatic then (enc u).length else 0 :=
  DescS.annotate_meta (.desc h)

theorem Win.annotate_meta {c : Condition} (h : Win c) :
    (annotate c).inlined = true ∧ (annotate c).size = 32 := by
  rw [annotate_inlined, annotate_size, (Win.meta h).1, (Win.meta h).2]; simp

end DecoderFaithfulness
