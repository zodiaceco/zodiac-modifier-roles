import DecoderFaithfulness.Meta

/-!
# `AbiLocation` against the spec encoding

Throughout, `hlen : data.length < 2 ^ 255` stands for "calldata is far
smaller than `2^256` bytes" (gas limits keep real calldata below `2^32`).
It makes every offset and length word the encoder writes fit in a `uint256`.
-/

namespace DecoderFaithfulness
open Roles

theorem Placed.of_At {data : Bytes} {l : Nat} {u : Val} (h : At data l (enc u))
    (hcall : ∀ pre args, u = .call pre args → 0 < l) : Placed data l u := by
  cases u with
  | call pre args => exact Or.inr ⟨hcall pre args rfl, h⟩
  | word => exact h
  | bytes => exact h
  | tuple => exact h
  | array => exact h

theorem Placed.to_At {data : Bytes} {l : Nat} {u : Val} (h : Placed data l u)
    (hl : (∀ pre args, u = .call pre args → 0 < l)) : At data l (enc u) := by
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

/-! ## `_tailLocation` -/

theorem tailLocation_eq {data : Bytes} {loc h off : Nat} {rest tl : Bytes}
    (hlen : data.length < 2 ^ 255)
    (hH : At data (loc + h) (word off ++ rest)) (hlt : h < off)
    (hT : At data (loc + off) tl) (htl : 32 ≤ tl.length) :
    tailLocation data loc h = loc + off := by
  have hHb := hH.bound
  have hTb := hT.bound
  simp only [List.length_append, length_word] at hHb
  have hoff : off < 2 ^ 256 := by
    have : (2 : Nat) ^ 255 < 2 ^ 256 := by decide
    omega
  unfold tailLocation
  rw [load_of_At_append hH hoff]
  dsimp only
  split
  · omega
  · split
    · omega
    · split
      · omega
      · rfl

/-! ## `children` loop -/

theorem childrenLoop_eq {data : Bytes} (hlen : data.length < 2 ^ 255) {s : Bool} (loc : Nat)
    (childAt : Nat → Condition) :
    ∀ (vs : List Val) (i h off : Nat),
    (∀ k (hk : k < vs.length), ∃ c, childAt (i + k) = annotate c ∧ DescS s c vs[k]) →
    At data (loc + h) (encParts vs off).1 →
    At data (loc + off) (encParts vs off).2 →
    h + (encParts vs off).1.length ≤ off →
    ∃ locs, childrenLoop data loc childAt vs.length i h = some locs ∧
      locs.length = vs.length ∧
      ∀ k (hk : k < locs.length) (hk' : k < vs.length),
        At data locs[k] (enc vs[k]) ∧ (vs[k].isStatic = false → 0 < locs[k])
  | [], _, _, _, _, _, _, _ => ⟨[], by simp [childrenLoop], rfl, by simp⟩
  | v :: vs, i, h, off, hch, hH, hT, hinv => by
    obtain ⟨c, hc, hD⟩ := hch 0 (by simp)
    simp only [Nat.add_zero, List.getElem_cons_zero] at hc hD
    have hmeta := hD.annotate_meta
    have hrest : ∀ k (hk : k < vs.length), ∃ c, childAt (i + 1 + k) = annotate c ∧
        DescS s c vs[k] := by
      intro k hk
      obtain ⟨c', h1, h2⟩ := hch (k + 1) (by simp; omega)
      exact ⟨c', by rw [← h1]; congr 1; omega, by simpa using h2⟩
    simp only [List.length_cons, childrenLoop]
    rw [hc, hmeta.1, hmeta.2]
    by_cases hs : v.isStatic
    · -- static component: inline in HEAD
      simp only [encParts, hs, ite_true] at hH hT hinv
      obtain ⟨hv, hH'⟩ := At_append.mp hH
      simp only [List.length_append] at hinv
      obtain ⟨locs, hl, hlen', hplaced⟩ := childrenLoop_eq hlen loc childAt vs (i + 1)
        (h + (enc v).length) off hrest (by rw [← Nat.add_assoc]; exact hH') hT (by omega)
      have hb := hv.bound
      refine ⟨(loc + h) :: locs, ?_, by simp [hlen'], ?_⟩
      · simp [hs, hl]; omega
      · intro k hk hk'
        cases k with
        | zero =>
          simp
          exact ⟨hv, by simp [hs]⟩
        | succ k => simpa using hplaced k (by simp at hk; omega) (by simp at hk'; omega)
    · -- dynamic component: offset word in HEAD, encoding in TAIL
      simp only [encParts, hs, ite_false, Bool.false_eq_true] at hH hT hinv
      obtain ⟨hw, hH'⟩ := At_append.mp hH
      obtain ⟨hv, hT'⟩ := At_append.mp hT
      simp only [List.length_append, length_word] at hinv
      have hge := hD.enc_ge
      have htail := tailLocation_eq hlen hH (by omega) hv hge
      obtain ⟨locs, hl, hlen', hplaced⟩ := childrenLoop_eq hlen loc childAt vs (i + 1)
        (h + 32) (off + (enc v).length) hrest
        (by simp only [length_word] at hH'; rw [← Nat.add_assoc]; exact hH')
        (by rw [← Nat.add_assoc]; exact hT') (by omega)
      have hb := hv.bound
      refine ⟨(loc + off) :: locs, ?_, by simp [hlen'], ?_⟩
      · simp [hs, htail, hl]; omega
      · intro k hk hk'
        cases k with
        | zero => simp; exact ⟨hv, fun _ => by omega⟩
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

theorem children_tuple {data : Bytes} (hlen : data.length < 2 ^ 255) {s : Bool} {c : Condition}
    {vs : List Val} {loc : Nat}
    (hne : (annotate c).encoding ≠ .Array) (hall : DescAll s c.children vs)
    (hat : At data loc (encTuple vs)) :
    ∃ locs, children data loc (annotate c) = some locs ∧ locs.length = vs.length ∧
      ∀ k (hk : k < locs.length) (hk' : k < vs.length),
        At data locs[k] (enc vs[k]) ∧ (vs[k].isStatic = false → 0 < locs[k]) := by
  unfold children
  rw [ite_eq_right hne, annotate_children]
  have hl : (c.children.map annotate).length = vs.length := by
    simp [DescAll.length_eq hall]
  rw [hl]
  obtain ⟨h1, h2, h3⟩ := At_encTuple hat
  apply childrenLoop_eq hlen (s := s) loc _ vs 0 0 (headLen vs) _ h1 h2 h3
  intro k hk
  have hkc : k < c.children.length := by rw [DescAll.length_eq hall]; exact hk
  refine ⟨c.children[k], ?_, DescAll.get hall k hkc⟩
  simp [hkc]

theorem children_array {data : Bytes} (hlen : data.length < 2 ^ 255) {s : Bool}
    {c c0 : Condition} {cs : List Condition} {vs : List Val} {loc : Nat}
    (he : (annotate c).encoding = .Array) (hch : c.children = c0 :: cs)
    (h0 : ∀ v, v ∈ vs → DescS s c0 v) (hat : At data loc (enc (.array vs))) :
    ∃ locs, children data loc (annotate c) = some locs ∧ locs.length = vs.length ∧
      ∀ k (hk : k < locs.length) (hk' : k < vs.length),
        At data locs[k] (enc vs[k]) ∧ (vs[k].isStatic = false → 0 < locs[k]) := by
  rw [enc_array] at hat
  obtain ⟨hw, ht⟩ := At_append.mp hat
  have hb := ht.bound
  have hcount : vs.length < 2 ^ 256 := by
    have := headLen_ge_count vs (fun v hv => (h0 v hv).enc_ge)
    have := encTuple_length_ge vs
    have : (2 : Nat) ^ 255 < 2 ^ 256 := by decide
    omega
  unfold children
  rw [ite_eq_left he, load_of_At hw hcount, annotate_children, hch]
  simp only [length_word] at hb ht
  have hwb := hw.bound
  simp only [length_word] at hwb
  rw [ite_eq_right (by omega)]
  obtain ⟨h1, h2, h3⟩ := At_encTuple ht
  apply childrenLoop_eq hlen (s := s) (loc + 32) _ vs 0 0 (headLen vs) _ h1 h2 h3
  intro k hk
  exact ⟨c0, by simp, h0 _ (List.getElem_mem hk)⟩

/-! ## `AbiLocation.size` -/

theorem size_eq (data : Bytes) (l : Nat) (c : Condition) :
    size data l c =
      if l + 32 > data.length then data.length + 1
      else if c.encoding = .Static then 32
      else if c.encoding = .Dynamic ∨ c.encoding = .AbiEncoded then
        32 + ((load data l + 31) &&& notU31)
      else if c.encoding = .None then sizeNone data l c.children
      else if c.encoding = .Array then
        match c.children with
        | [] => 32
        | c0 :: _ =>
          32 + sizeArrayLoop data (l + 32) c0 (fun l' => size data l' c0) (load data l) 0
      else sizeTuple data l c.children 0 := by
  rcases c with ⟨e, o, cs, i, s, lb, cv⟩
  rw [size.eq_def]
  rfl

theorem sizeNone_all_gt (data : Bytes) (l : Nat) (cs : List Condition)
    (h : ∀ ch, ch ∈ cs → data.length < size data l ch) :
    sizeNone data l cs = data.length + 1 := by
  induction cs with
  | nil => simp [sizeNone]
  | cons c cs ih =>
    simp only [sizeNone]
    have := h c (by simp)
    rw [ite_eq_right (by omega), ih (fun ch hm => h ch (by simp [hm]))]

theorem sizeNone_first (data : Bytes) (l s : Nat) (cs : List Condition)
    (hs : 0 < s ∧ s ≤ data.length)
    (h : ∀ ch, ch ∈ cs → size data l ch = s ∨ data.length < size data l ch)
    (hex : ∃ ch, ch ∈ cs ∧ size data l ch = s) : sizeNone data l cs = s := by
  induction cs with
  | nil => obtain ⟨_, hm, _⟩ := hex; simp at hm
  | cons c cs ih =>
    simp only [sizeNone]
    rcases h c (by simp) with h1 | h1
    · rw [h1, ite_eq_left hs]
    · rw [ite_eq_right (by omega)]
      apply ih (fun ch hm => h ch (by simp [hm]))
      obtain ⟨ch, hm, hch⟩ := hex
      simp at hm
      rcases hm with rfl | hm
      · omega
      · exact ⟨ch, hm, hch⟩

/-- `sizeNone` returns `s` if the described child comes after children that
    each give `s` or an implausible size. -/
theorem sizeNone_prefix (data : Bytes) (l s : Nat) (ch0 : Condition) (post : List Condition)
    (hs : 0 < s ∧ s ≤ data.length) (h0 : size data l ch0 = s) :
    ∀ pre : List Condition, (∀ ch, ch ∈ pre → size data l ch = s ∨ data.length < size data l ch) →
    sizeNone data l (pre ++ ch0 :: post) = s
  | [], _ => by simp only [List.nil_append, sizeNone]; rw [h0, ite_eq_left hs]
  | c :: pre, h => by
    simp only [List.cons_append, sizeNone]
    rcases h c (by simp) with h1 | h1
    · rw [h1, ite_eq_left hs]
    · rw [ite_eq_right (by omega)]
      exact sizeNone_prefix data l s ch0 post hs h0 pre (fun ch hm => h ch (by simp [hm]))

theorem NonStruct.size_gt {data : Bytes} (l : Nat) :
    ∀ {c}, NonStruct c → data.length < size data l (annotate c)
  | c, .leaf he hch _ => by
    rw [size_eq, annotate_encoding, annotate_children, hch]
    rcases he with he | he <;> simp [he, sizeNone] <;> split <;> omega
  | c, .logical he _ hall => by
    rw [size_eq, annotate_encoding, annotate_children, he]
    simp
    split
    · omega
    · rw [sizeNone_all_gt]
      · omega
      · intro ch hm
        simp at hm
        obtain ⟨ch', hm', rfl⟩ := hm
        exact NonStruct.size_gt l (hall ch' hm')

theorem size_dynamic {data : Bytes} (hlen : data.length < 2 ^ 255) {l : Nat} {b : Bytes}
    (hat : At data l (encBytes b)) :
    32 + ((load data l + 31) &&& notU31) = (encBytes b).length := by
  have hb := hat.bound
  rw [length_encBytes] at hb ⊢
  unfold encBytes at hat
  rw [List.append_assoc] at hat
  have hw : b.length < 2 ^ 256 := by
    have : (2 : Nat) ^ 255 < 2 ^ 256 := by decide
    have := ceil32_ge b.length
    omega
  rw [load_of_At_append hat hw, roundUp_eq]
  have : (2 : Nat) ^ 255 + 2 ^ 255 = 2 ^ 256 := by decide
  have := ceil32_ge b.length
  omega

/-- `size` of a `Dynamic` or `AbiEncoded` node only reads the length word. -/
theorem size_dynamicNode {data : Bytes} (hlen : data.length < 2 ^ 255) {l : Nat} {u : Val}
    {c : Condition} (he : c.encoding = .Dynamic ∨ c.encoding = .AbiEncoded) (hu : IsBytesLike u)
    (hat : At data l (enc u)) : size data l (annotate c) = (enc u).length := by
  have hb := hat.bound
  have hge : 32 ≤ (enc u).length := by rw [enc_bytesLike hu, length_encBytes]; omega
  rw [enc_bytesLike hu] at hat hb hge ⊢
  rw [size_eq, annotate_encoding]
  rcases he with he | he <;>
  · rw [he]
    simp only [reduceCtorEq, ite_false]
    rw [ite_eq_right (by omega)]
    simp
    exact size_dynamic hlen hat

mutual
  /-- Any bytes-like node, whatever interpretation it encodes, gets the size
      of a bytes value right: it only reads the length word. -/
  theorem BytesLike.size_eq {data : Bytes} (hlen : data.length < 2 ^ 255) :
      ∀ {c u l}, BytesLike c → IsBytesLike u → At data l (enc u) →
      size data l (annotate c) = (enc u).length
    | _, _, _, .dyn he, hu, hat => size_dynamicNode hlen (.inl he) hu hat
    | _, _, _, .abi he, hu, hat => size_dynamicNode hlen (.inr he) hu hat
    | c, u, l, .logical ch0 he _ hm0 h0 hall, hu, hat => by
      have hge : 32 ≤ (enc u).length := by rw [enc_bytesLike hu, length_encBytes]; omega
      have hb := hat.bound
      rw [DecoderFaithfulness.size_eq, annotate_encoding, he, annotate_children]
      rw [ite_eq_right (by omega)]
      simp
      apply sizeNone_first data l _ _ ⟨by omega, by omega⟩
      · intro ch hm
        simp at hm
        obtain ⟨ch', hm', rfl⟩ := hm
        exact BytesLikeN.size_cases hlen (hall ch' hm') hu hat
      · exact ⟨annotate ch0, List.mem_map_of_mem hm0, BytesLike.size_eq hlen h0 hu hat⟩

  theorem BytesLikeN.size_cases {data : Bytes} (hlen : data.length < 2 ^ 255) :
      ∀ {c u l}, BytesLikeN c → IsBytesLike u → At data l (enc u) →
      size data l (annotate c) = (enc u).length ∨ data.length < size data l (annotate c)
    | _, _, _, .bl h, hu, hat => Or.inl (BytesLike.size_eq hlen h hu hat)
    | _, _, l, .ns h, _, _ => Or.inr (NonStruct.size_gt l h)
end

/-- Tuple loop of `size`, given correct sizes for each component. -/
theorem sizeTuple_eq {data : Bytes} (hlen : data.length < 2 ^ 255) {s : Bool} (loc : Nat) :
    ∀ (cs : List Condition) (vs : List Val) (h off : Nat) (hl : cs.length = vs.length),
    (∀ k (hk : k < cs.length), ∃ c, cs[k] = annotate c ∧ DescS s c (vs[k]'(by omega)) ∧
      ∀ l, At data l (enc (vs[k]'(by omega))) → size data l cs[k] = (enc (vs[k]'(by omega))).length) →
    At data (loc + h) (encParts vs off).1 →
    At data (loc + off) (encParts vs off).2 →
    h + (encParts vs off).1.length ≤ off →
    sizeTuple data loc cs h = (encParts vs off).1.length + (encParts vs off).2.length
  | [], [], _, _, _, _, _, _, _ => by simp [sizeTuple, encParts]
  | [], _ :: _, _, _, hl, _, _, _, _ => by simp at hl
  | _ :: _, [], _, _, hl, _, _, _, _ => by simp at hl
  | ch :: cs, v :: vs, h, off, hl, hch, hH, hT, hinv => by
    obtain ⟨c, hc, hD, hsz⟩ := hch 0 (by simp)
    simp only [List.getElem_cons_zero] at hc hD hsz
    have hmeta := hD.annotate_meta
    have hrest : ∀ k (hk : k < cs.length), ∃ c, cs[k] = annotate c ∧
        DescS s c (vs[k]'(by simp at hl; omega)) ∧
        ∀ l, At data l (enc (vs[k]'(by simp at hl; omega))) →
          size data l cs[k] = (enc (vs[k]'(by simp at hl; omega))).length := by
      intro k hk
      obtain ⟨c', h1, h2, h4⟩ := hch (k + 1) (by simp; omega)
      exact ⟨c', by simpa using h1, by simpa using h2,
        fun l hl => by simpa using h4 l (by simpa using hl)⟩
    have hl' : cs.length = vs.length := by simpa using hl
    simp only [sizeTuple]
    rw [hc, hmeta.1, hmeta.2]
    by_cases hs : v.isStatic
    · simp only [encParts, hs, ite_true] at hH hT hinv ⊢
      obtain ⟨hv, hH'⟩ := At_append.mp hH
      simp only [List.length_append] at hinv ⊢
      rw [sizeTuple_eq hlen loc cs vs (h + (enc v).length) off hl' hrest
        (by rw [← Nat.add_assoc]; exact hH') hT (by omega)]
      omega
    · simp only [encParts, hs, ite_false, Bool.false_eq_true] at hH hT hinv ⊢
      obtain ⟨hw, hH'⟩ := At_append.mp hH
      obtain ⟨hv, hT'⟩ := At_append.mp hT
      simp only [List.length_append, length_word] at hinv ⊢
      have hge := hD.enc_ge
      rw [tailLocation_eq hlen hH (by omega) hv hge, ← hc, hsz _ hv]
      rw [sizeTuple_eq hlen loc cs vs (h + 32) (off + (enc v).length) hl' hrest
        (by simp only [length_word] at hH'; rw [← Nat.add_assoc]; exact hH')
        (by rw [← Nat.add_assoc]; exact hT') (by omega)]
      omega

/-- Array loop of `size`, given correct sizes for the element template. -/
theorem sizeArrayLoop_eq {data : Bytes} (hlen : data.length < 2 ^ 255) {s : Bool} (loc : Nat)
    (c : Condition) {c0 : Condition} (hc : c = annotate c0) :
    ∀ (vs : List Val) (h off : Nat), (∀ v, v ∈ vs → DescS s c0 v) →
    (∀ l v, v ∈ vs → At data l (enc v) → size data l c = (enc v).length) →
    At data (loc + h) (encParts vs off).1 →
    At data (loc + off) (encParts vs off).2 →
    h + (encParts vs off).1.length ≤ off →
    sizeArrayLoop data loc c (fun l => size data l c) vs.length h =
      (encParts vs off).1.length + (encParts vs off).2.length
  | [], _, _, _, _, _, _, _ => by simp [sizeArrayLoop, encParts]
  | v :: vs, h, off, hD, hsz, hH, hT, hinv => by
    have hv0 := hD v (by simp)
    have hmeta := hv0.annotate_meta
    have hrest : ∀ w, w ∈ vs → DescS s c0 w := fun w hw => hD w (by simp [hw])
    have hszr : ∀ l w, w ∈ vs → At data l (enc w) → size data l c = (enc w).length :=
      fun l w hw => hsz l w (by simp [hw])
    simp only [List.length_cons, sizeArrayLoop]
    rw [hc, hmeta.1, hmeta.2, ← hc]
    by_cases hs : v.isStatic
    · simp only [encParts, hs, ite_true] at hH hT hinv ⊢
      obtain ⟨hv, hH'⟩ := At_append.mp hH
      simp only [List.length_append] at hinv ⊢
      rw [sizeArrayLoop_eq hlen loc c hc vs (h + (enc v).length) off hrest hszr
        (by rw [← Nat.add_assoc]; exact hH') hT (by omega)]
      omega
    · simp only [encParts, hs, ite_false, Bool.false_eq_true] at hH hT hinv ⊢
      obtain ⟨hw, hH'⟩ := At_append.mp hH
      obtain ⟨hv, hT'⟩ := At_append.mp hT
      simp only [List.length_append, length_word] at hinv ⊢
      have hge := hv0.enc_ge
      rw [tailLocation_eq hlen hH (by omega) hv hge, hsz _ _ (by simp) hv]
      rw [sizeArrayLoop_eq hlen loc c hc vs (h + 32) (off + (enc v).length) hrest hszr
        (by simp only [length_word] at hH'; rw [← Nat.add_assoc]; exact hH')
        (by rw [← Nat.add_assoc]; exact hT') (by omega)]
      omega

theorem size_static {data : Bytes} {l : Nat} {c : Condition} {w : Bytes}
    (he : c.encoding = .Static) (hw : w.length = 32) (hat : At data l w) :
    size data l (annotate c) = 32 := by
  have := hat.bound
  rw [size_eq, annotate_encoding, he]
  rw [hw] at this
  rw [ite_eq_right (by omega)]
  simp

mutual
  /-- `AbiLocation.size` returns the length of the spec encoding. -/
  theorem Desc.size_eq {data : Bytes} (hlen : data.length < 2 ^ 255) {s : Bool} :
      ∀ {c u l}, Desc s c u → At data l (enc u) →
      size data l (annotate c) = (enc u).length
    | _, _, _, .word he _ _ hw, hat => by
      simp only [enc] at hat ⊢; rw [hw]; exact size_static he hw hat
    | _, _, _, .sliceWord he _ _ _ _ _ hw, hat => by
      simp only [enc] at hat ⊢; rw [hw]; exact size_static he hw hat
    | _, _, _, .bytes he _ _ hu, hat => size_dynamicNode hlen (.inl he) hu hat
    | _, _, _, .sliceBytes he _ _ _ _ _ hu, hat => size_dynamicNode hlen (.inl he) hu hat
    | _, _, _, .call he _ _ _ _, hat => size_dynamicNode hlen (.inr he) trivial hat
    | c, _, l, .tuple (vs := vs) he hne hall hop, hat => by
      have hge := (Desc.tuple he hne hall hop (s := s)).enc_ge
      have hb := hat.bound
      rw [enc_tuple] at hat hb hge ⊢
      rw [DecoderFaithfulness.size_eq, annotate_encoding, he, annotate_children]
      rw [ite_eq_right (by omega)]
      simp
      obtain ⟨h1, h2, h3⟩ := At_encTuple hat
      rw [sizeTuple_eq hlen (s := s) l _ vs 0 (headLen vs)
        (by simp [DescAll.length_eq hall]) ?_ h1 h2 h3]
      · simp [encTuple]
      · intro k hk
        have hkc : k < c.children.length := by simpa using hk
        have hkv : k < vs.length := by rw [← DescAll.length_eq hall]; exact hkc
        refine ⟨c.children[k], by simp, DescAll.get hall k hkc, ?_⟩
        intro l' hl'
        simp only [List.getElem_map]
        exact DescAll.sizes hlen hall k hkc hkv l' hl'
    | c, _, l, .array (vs := vs) c0 cs he hch h0 _ _ _, hat => by
      have hb := hat.bound
      rw [enc_array] at hat hb ⊢
      obtain ⟨hw, ht⟩ := At_append.mp hat
      have hcount : vs.length < 2 ^ 256 := by
        have := headLen_ge_count vs (fun v hv => (h0 v hv).enc_ge)
        have := encTuple_length_ge vs
        have := ht.bound
        have : (2 : Nat) ^ 255 < 2 ^ 256 := by decide
        omega
      rw [DecoderFaithfulness.size_eq, annotate_encoding, he, annotate_children, hch]
      simp only [List.length_append, length_word] at hb
      rw [ite_eq_right (by omega)]
      simp only [List.map_cons]
      simp
      rw [load_of_At hw hcount]
      simp only [length_word] at ht
      obtain ⟨h1, h2, h3⟩ := At_encTuple ht
      rw [sizeArrayLoop_eq hlen (l + 32) (annotate c0) rfl vs 0 (headLen vs) h0
        (fun l' v hv hat' => DescS.size_eq hlen (h0 v hv) hat') h1 h2 h3]
      simp [encTuple]
    | c, u, l, .logical ch0 he _ _ h0 hall ⟨pre, post, hcs, hnz⟩, hat => by
      have hge := h0.enc_ge
      have hb := hat.bound
      rw [DecoderFaithfulness.size_eq, annotate_encoding, he, annotate_children, hcs]
      rw [ite_eq_right (by omega)]
      simp only [reduceCtorEq, ite_false, ite_true, List.map_append, List.map_cons]
      apply sizeNone_prefix data l _ _ _ ⟨by omega, by omega⟩ (DescS.size_eq hlen h0 hat)
      intro ch hm
      obtain ⟨ch', hm', rfl⟩ := List.mem_map.mp hm
      exact DescSN.size_cases hlen (hall ch' (by rw [hcs]; simp [hm'])) (hnz ch' hm') hat

  theorem DescS.size_eq {data : Bytes} (hlen : data.length < 2 ^ 255) {s : Bool} :
      ∀ {c u l}, DescS s c u → At data l (enc u) →
      size data l (annotate c) = (enc u).length
    | _, _, _, .desc h, hat => Desc.size_eq hlen h hat
    | _, _, _, .stray _ hb hu, hat => BytesLike.size_eq hlen hb hu hat

  theorem DescSN.size_cases {data : Bytes} (hlen : data.length < 2 ^ 255) {s : Bool} :
      ∀ {c u l}, DescSN s c u → ¬ ZipNode c → At data l (enc u) →
      size data l (annotate c) = (enc u).length ∨ data.length < size data l (annotate c)
    | _, _, _, .ds h, _, hat => Or.inl (DescS.size_eq hlen h hat)
    | _, _, l, .ns h, _, _ => Or.inr (NonStruct.size_gt l h)
    | _, _, _, .zip hz _, hnz, _ => absurd hz hnz

  theorem DescAll.sizes {data : Bytes} (hlen : data.length < 2 ^ 255) {s : Bool} :
      ∀ {cs vs}, DescAll s cs vs →
      ∀ k (hk : k < cs.length) (hkv : k < vs.length) l, At data l (enc vs[k]) →
      size data l (annotate cs[k]) = (enc vs[k]).length
    | _, _, .cons h _, 0, _, _, _, hat => DescS.size_eq hlen h hat
    | _, _, .cons _ hs, k + 1, hk, hkv, l, hat => by
      simp only [List.getElem_cons_succ] at hat ⊢
      exact DescAll.sizes hlen hs k (by simp at hk; omega) (by simp at hkv; omega) l hat
end

end DecoderFaithfulness
