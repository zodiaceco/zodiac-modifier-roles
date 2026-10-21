import ConditionCheck.Check

/-!
# Soundness of `checkCondition`

`checkCondition_sound`: if `checkCondition s root = some t`, then `root`
satisfies `RootOK` and `ZipOK s`, and `Desc s root (.call pre args)` holds for
every calldata `pre ++ enc(args)` of type `t`. These are the hypotheses of
the decoder theorems (`DecoderFaithfulness/Main.lean`), so for such trees
`evaluate` reads every node at the spec location of the value it describes.
-/

namespace ConditionCheck
open DecoderFaithfulness DecoderFaithfulness.Roles

/-! ## Basics -/

theorem sizeOf_child {ch c : Condition} (h : ch ∈ c.children) : sizeOf ch < sizeOf c := by
  rcases c with ⟨e, op, cs, i, sz, lb, cv⟩
  have := List.sizeOf_lt_of_mem h
  simp only [Condition.mk.sizeOf_spec]
  simp only at this
  omega

theorem classify_eq (s : Bool) (c : Condition) :
    classify s c = (classifyAll s c.children).bind
      (classifyNode s c.encoding c.operator c.children c.leadingBytes c.compValue) := by
  rcases c with ⟨e, op, cs, i, sz, lb, cv⟩
  simp [classify]

theorem classifyAll_get (s : Bool) :
    ∀ {cs : List Condition} {ks : List K}, classifyAll s cs = some ks →
      ks.length = cs.length ∧ ∀ i (h1 : i < cs.length) (h2 : i < ks.length),
        classify s cs[i] = some ks[i]
  | [], ks, h => by
    simp [classifyAll] at h; subst h; simp
  | c :: cs, ks, h => by
    simp only [classifyAll, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨k, hk, ks', hks', rfl⟩ := h
    obtain ⟨hl, hg⟩ := classifyAll_get s hks'
    refine ⟨by simp [hl], ?_⟩
    intro i h1 h2
    cases i with
    | zero => simpa using hk
    | succ i => simpa using hg i (by simp at h1; omega) (by simp at h2; omega)

/-- Every child has a kind, and it is among `ks`. -/
theorem classifyAll_mem (s : Bool) {cs : List Condition} {ks : List K}
    (h : classifyAll s cs = some ks) {ch : Condition} (hm : ch ∈ cs) :
    ∃ k, k ∈ ks ∧ classify s ch = some k := by
  obtain ⟨hl, hg⟩ := classifyAll_get s h
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hm
  exact ⟨ks[i]'(by omega), List.getElem_mem _, hg i hi (by omega)⟩

theorem allTy_eq : ∀ {ks : List K} {ts : List Ty}, allTy ks = some ts → ks = ts.map .ty
  | [], ts, h => by simp [allTy] at h; subst h; rfl
  | .ty t :: ks, ts, h => by
    simp only [allTy, Option.map_eq_some_iff] at h
    obtain ⟨ts', h', rfl⟩ := h
    simp [allTy_eq h']
  | .ns :: _, _, h => by simp [allTy] at h
  | .zip :: _, _, h => by simp [allTy] at h

/-! ## Typing lemmas -/

theorem hasTAll_get (s : Bool) :
    ∀ {vs : List Val} {ts : List Ty}, HasTAll s vs ts →
      vs.length = ts.length ∧ ∀ i (h1 : i < vs.length) (h2 : i < ts.length), HasT s vs[i] ts[i]
  | [], [], _ => by simp
  | v :: vs, t :: ts, h => by
    simp only [HasTAll] at h
    obtain ⟨hl, hg⟩ := hasTAll_get s h.2
    refine ⟨by simp [hl], ?_⟩
    intro i h1 h2
    cases i with
    | zero => simpa using h.1
    | succ i => simpa using hg i (by simp at h1; omega) (by simp at h2; omega)
  | [], _ :: _, h | _ :: _, [], h => by simp [HasTAll] at h

theorem hasTAll_of_get (s : Bool) :
    ∀ {vs : List Val} {ts : List Ty}, vs.length = ts.length →
      (∀ i (h1 : i < vs.length) (h2 : i < ts.length), HasT s vs[i] ts[i]) → HasTAll s vs ts
  | [], [], _, _ => by simp [HasTAll]
  | v :: vs, t :: ts, hl, hg => by
    simp only [HasTAll]
    exact ⟨hg 0 (by simp) (by simp),
      hasTAll_of_get s (by simpa using hl) fun i h1 h2 =>
        hg (i + 1) (by simp; omega) (by simp; omega)⟩
  | [], _ :: _, hl, _ | _ :: _, [], hl, _ => by simp at hl

theorem hasTEach_iff (s : Bool) (t : Ty) :
    ∀ {vs : List Val}, HasTEach s vs t ↔ ∀ v, v ∈ vs → HasT s v t
  | [] => by simp [HasTEach]
  | v :: vs => by simp [HasTEach, hasTEach_iff s t (vs := vs)]

mutual
  theorem hasT_isStatic (s : Bool) : ∀ {u : Val} {t : Ty}, HasT s u t → u.isStatic = t.isStatic
    | .word _, t, h => by simp only [HasT] at h; rw [h.1]; rfl
    | .bytes _, t, h => by
      simp only [HasT] at h
      rcases h with rfl | ⟨_, lb, ts, rfl⟩ <;> rfl
    | .tuple vs, t, h => by
      simp only [HasT] at h
      obtain ⟨ts, rfl, h⟩ := h
      simp only [Val.isStatic, Ty.isStatic]
      exact hasTAll_allStatic s h
    | .array _, t, h => by
      simp only [HasT] at h
      obtain ⟨t', rfl, _⟩ := h
      rfl
    | .call _ _, t, h => by
      simp only [HasT] at h
      rcases h with rfl | ⟨lb, ts, rfl, _⟩ <;> rfl

  theorem hasTAll_allStatic (s : Bool) :
      ∀ {vs : List Val} {ts : List Ty}, HasTAll s vs ts → Val.allStatic vs = Ty.allStatic ts
    | [], [], _ => rfl
    | v :: vs, t :: ts, h => by
      simp only [HasTAll] at h
      simp only [Val.allStatic, Ty.allStatic, hasT_isStatic s h.1, hasTAll_allStatic s h.2]
    | [], _ :: _, h | _ :: _, [], h => by simp [HasTAll] at h
end

theorem isBytesLike_of_hasT {s : Bool} {u : Val} {t : Ty} (h : HasT s u t)
    (ht : t.isBytesLike = true) : IsBytesLike u := by
  cases u with
  | word w => simp only [HasT] at h; rw [h.1] at ht; simp [Ty.isBytesLike] at ht
  | bytes _ => trivial
  | tuple vs =>
    simp only [HasT] at h; obtain ⟨ts, rfl, _⟩ := h; simp [Ty.isBytesLike] at ht
  | array vs =>
    simp only [HasT] at h; obtain ⟨t', rfl, _⟩ := h; simp [Ty.isBytesLike] at ht
  | call _ _ => trivial

/-- With `s = true` a bytes value has every bytes-like type. -/
theorem hasT_of_bytesLike {s : Bool} {u : Val} {t : Ty} (hs : s = true) (hu : IsBytesLike u)
    (ht : t.isBytesLike = true) : HasT s u t := by
  cases t with
  | dynamic =>
    cases u with
    | bytes _ => simp [HasT]
    | call _ _ => simp [HasT]
    | _ => cases hu
  | call lb ts =>
    cases u with
    | bytes _ => simp [HasT, hs]
    | call _ _ => simp [HasT, hs]
    | _ => cases hu
  | _ => simp [Ty.isBytesLike] at ht

theorem hasT_dynamic {s : Bool} {u : Val} (hu : IsBytesLike u) : HasT s u .dynamic := by
  cases u with
  | bytes _ => simp [HasT]
  | call _ _ => simp [HasT]
  | _ => cases hu

/-! ## Inverting `classifyNode` -/

theorem leafOk_iff {cs : List Condition} {op : Operator} :
    leafOk cs op = true ↔ cs = [] ∧ isNavOp op = false := by
  cases cs <;> simp [leafOk]

theorem sliceOk_iff {op : Operator} {cs : List Condition} {cv : Bytes} {ks : List K} :
    sliceOk op cs cv ks = true ↔ op = .Slice ∧ 1 ≤ sliceSize cv ∧ sliceSize cv ≤ 32 ∧
      ∃ ch, cs = [ch] ∧ ch.encoding = .Static ∧ ks = [.ty .static] := by
  unfold sliceOk
  rcases cs with _ | ⟨ch, _ | ⟨_, _⟩⟩ <;> simp [and_assoc]

theorem node_word {s : Bool} {e : Encoding} {op : Operator} {cs : List Condition} {lb : Nat}
    {cv : Bytes} {ks : List K} {k : K} (he : e = .Static ∨ e = .Dynamic)
    (h : classifyNode s e op cs lb cv ks = some k) :
    k = .ty (if e = .Static then .static else .dynamic) ∧
      (leafOk cs op = true ∨ sliceOk op cs cv ks = true) := by
  rcases he with rfl | rfl <;>
  · simp only [classifyNode] at h
    split at h
    · rename_i hc; simp only [Option.some.injEq] at h; subst h
      simpa [Bool.or_eq_true] using hc
    · cases h

theorem node_tuple {s : Bool} {op : Operator} {cs : List Condition} {lb : Nat}
    {cv : Bytes} {ks : List K} {k : K} (h : classifyNode s .Tuple op cs lb cv ks = some k) :
    ∃ ts, k = .ty (.tuple ts) ∧ cs ≠ [] ∧ (isNavOp op = false ∨ op = .Matches) ∧
      allTy ks = some ts := by
  simp only [classifyNode] at h
  split at h
  · rename_i hc
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨ts, hts, rfl⟩ := h
    simp only [Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff, Bool.or_eq_true,
      beq_iff_eq] at hc
    exact ⟨ts, rfl, hc.1, by simpa using hc.2, hts⟩
  · cases h

theorem node_array {s : Bool} {op : Operator} {cs : List Condition} {lb : Nat}
    {cv : Bytes} {ks : List K} {k : K} (h : classifyNode s .Array op cs lb cv ks = some k) :
    ∃ t0, k = .ty (.array t0) ∧ (isNavOp op = false ∨ isArrayOp op = true) ∧
      ks ≠ [] ∧ ∀ k', k' ∈ ks → k' = .ty t0 := by
  simp only [classifyNode] at h
  split at h
  · rename_i hc
    split at h
    · rename_i t rest
      split at h
      · rename_i hr
        simp only [Option.some.injEq] at h; subst h
        refine ⟨t, rfl, by simpa [Bool.or_eq_true] using hc, by simp, ?_⟩
        intro k' hk'
        simp only [List.mem_cons] at hk'
        rcases hk' with rfl | hk'
        · rfl
        · simpa using List.all_eq_true.mp hr k' hk'
      · cases h
    · cases h
  · cases h

theorem node_abi {s : Bool} {op : Operator} {cs : List Condition} {lb : Nat}
    {cv : Bytes} {ks : List K} {k : K} (h : classifyNode s .AbiEncoded op cs lb cv ks = some k) :
    ∃ ts, k = .ty (.call lb ts) ∧ cs ≠ [] ∧ (op = .Matches ∨ op = .Pass) ∧
      allTy ks = some ts := by
  simp only [classifyNode] at h
  split at h
  · rename_i hc
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨ts, hts, rfl⟩ := h
    simp only [Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff, Bool.or_eq_true,
      beq_iff_eq] at hc
    exact ⟨ts, rfl, hc.1, hc.2, hts⟩
  · cases h

theorem node_ether {s : Bool} {op : Operator} {cs : List Condition} {lb : Nat}
    {cv : Bytes} {ks : List K} {k : K} (h : classifyNode s .EtherValue op cs lb cv ks = some k) :
    k = .ns ∧ cs = [] ∧ isNavOp op = false := by
  simp only [classifyNode] at h
  split at h
  · rename_i hc; simp only [Option.some.injEq] at h; exact ⟨h.symm, leafOk_iff.mp hc⟩
  · cases h

theorem node_none {s : Bool} {op : Operator} {cs : List Condition} {lb : Nat}
    {cv : Bytes} {ks : List K} {k : K} (h : classifyNode s .None op cs lb cv ks = some k) :
    ((op = .ZipSome ∨ op = .ZipEvery) ∧ k = .zip ∧ ∃ ts, ks = [.ty (.tuple ts)]) ∨
    (k = .ns ∧ cs = [] ∧ isNavOp op = false) ∨
    ((op = .And ∨ op = .Or) ∧ logicalKind s ks = some k) := by
  simp only [classifyNode] at h
  split at h
  · rename_i hz
    split at h
    · rename_i ts
      simp only [Option.some.injEq] at h
      exact .inl ⟨by simpa [Bool.or_eq_true] using hz, h.symm, ts, rfl⟩
    · cases h
  · split at h
    · rename_i hl; simp only [Option.some.injEq] at h
      exact .inr (.inl ⟨h.symm, leafOk_iff.mp hl⟩)
    · split at h
      · rename_i ho
        exact .inr (.inr ⟨by simpa [Bool.or_eq_true] using ho, h⟩)
      · cases h

/-! ## `And` / `Or` -/

theorem firstTy_spec : ∀ {ks : List K} {t0 : Ty}, firstTy ks = some t0 →
    ∃ i, ∃ h : i < ks.length, ks[i] = .ty t0 ∧ ∀ j (hj : j < i), ks[j]'(by omega) = .ns
  | [], _, h => by simp [firstTy] at h
  | .ty t :: _, t0, h => by
    simp only [firstTy, Option.some.injEq] at h; subst h
    exact ⟨0, by simp, rfl, fun j hj => absurd hj (by omega)⟩
  | .ns :: ks, t0, h => by
    simp only [firstTy] at h
    obtain ⟨i, hi, hk, hb⟩ := firstTy_spec h
    refine ⟨i + 1, by simp; omega, by simpa using hk, ?_⟩
    intro j hj
    cases j with
    | zero => rfl
    | succ j => simpa using hb j (by omega)
  | .zip :: _, _, h => by simp [firstTy] at h

theorem logicalKind_ns {s : Bool} {ks : List K} (h : logicalKind s ks = some .ns) :
    ∀ k, k ∈ ks → k = .ns := by
  unfold logicalKind at h
  split at h
  · cases h
  · split at h
    · rename_i ha; intro k hk; simpa using List.all_eq_true.mp ha k hk
    · split at h
      · cases h
      · split at h
        · cases h
        · simp at h

theorem logicalKind_not_zip {s : Bool} {ks : List K} : logicalKind s ks ≠ some .zip := by
  unfold logicalKind
  split
  · simp
  · split
    · simp
    · split
      · simp
      · split <;> simp

/-- What `logicalKind = ty t` guarantees: a first structural child with only
    non-structural children before it, and every child non-structural, a Zip
    (then `t` is dynamic), or structural with type `t` or (variant) a
    bytes-like type. -/
theorem logicalKind_ty {s : Bool} {ks : List K} {t : Ty} (h : logicalKind s ks = some (.ty t)) :
    (∃ i, ∃ hi : i < ks.length, (∃ t0, ks[i] = .ty t0) ∧ ∀ j (hj : j < i), ks[j]'(by omega) = .ns) ∧
    ∀ k, k ∈ ks → k = .ns ∨ (k = .zip ∧ t.isStatic = false) ∨
      ∃ t', k = .ty t' ∧ (t' = t ∨ (s = true ∧ t = .dynamic ∧ t'.isBytesLike = true)) := by
  unfold logicalKind at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · rename_i t1 hlt
        split at h
        · cases h
        · rename_i hz
          simp only [Option.some.injEq, K.ty.injEq] at h; subst h
          unfold logicalTy at hlt
          split at hlt
          · cases hlt
          · rename_i t0 hf
            obtain ⟨i, hi, hk, hb⟩ := firstTy_spec hf
            refine ⟨⟨i, hi, ⟨t0, hk⟩, hb⟩, ?_⟩
            intro k hk
            rcases k with t' | _ | _
            · refine .inr (.inr ⟨t', rfl, ?_⟩)
              split at hlt
              · rename_i hall
                simp only [Option.some.injEq] at hlt; subst hlt
                have := List.all_eq_true.mp hall _ hk
                simp [K.fits] at this
                exact .inl this
              · split at hlt
                · rename_i hall
                  simp only [Option.some.injEq] at hlt; subst hlt
                  simp only [Bool.and_eq_true] at hall
                  have := List.all_eq_true.mp hall.2 _ hk
                  exact .inr ⟨hall.1, rfl, by simpa [K.bytesLikeOk] using this⟩
                · cases hlt
            · exact .inl rfl
            · refine .inr (.inl ⟨rfl, ?_⟩)
              simp at hz
              exact hz hk

/-! ## Inverting `Desc` and `BytesLike` by encoding -/

theorem Desc.static_inv {s : Bool} {c : Condition} {u : Val} (hD : Desc s c u)
    (he : c.encoding = .Static) : ∃ w, u = .word w ∧ w.length = 32 := by
  cases hD <;> simp_all

theorem Desc.dynamic_inv {s : Bool} {c : Condition} {u : Val} (hD : Desc s c u)
    (he : c.encoding = .Dynamic) : IsBytesLike u := by
  cases hD <;> simp_all

theorem Desc.tuple_inv {s : Bool} {c : Condition} {u : Val} (hD : Desc s c u)
    (he : c.encoding = .Tuple) : ∃ vs, u = .tuple vs ∧ DescAll s c.children vs := by
  cases hD <;> simp_all

theorem Desc.array_inv {s : Bool} {c : Condition} {u : Val} (hD : Desc s c u)
    (he : c.encoding = .Array) :
    ∃ vs c0 cs, u = .array vs ∧ c.children = c0 :: cs ∧ ∀ v, v ∈ vs → DescS s c0 v := by
  cases hD with
  | array c0 cs _ hch h0 _ _ _ => exact ⟨_, c0, cs, rfl, hch, h0⟩
  | _ => simp_all

theorem Desc.call_inv {s : Bool} {c : Condition} {u : Val} (hD : Desc s c u)
    (he : c.encoding = .AbiEncoded) :
    ∃ pre args, u = .call pre args ∧ c.leadingBytes = pre.length ∧ DescAll s c.children args := by
  cases hD with
  | call _ hlb _ hall _ => exact ⟨_, _, rfl, hlb, hall⟩
  | _ => simp_all

theorem Desc.none_inv {s : Bool} {c : Condition} {u : Val} (hD : Desc s c u)
    (he : c.encoding = .None ∨ c.encoding = .EtherValue) :
    (c.operator = .And ∨ c.operator = .Or) ∧ ∃ ch0, ch0 ∈ c.children ∧ DescS s ch0 u := by
  cases hD with
  | logical ch0 _ hop hm h0 _ _ => exact ⟨hop, ch0, hm, h0⟩
  | _ => rcases he with he | he <;> simp_all

theorem BytesLike.inv {c : Condition} (h : BytesLike c) :
    c.encoding = .Dynamic ∨ c.encoding = .AbiEncoded ∨
      (c.encoding = .None ∧ (c.operator = .And ∨ c.operator = .Or) ∧
        ∃ ch0, ch0 ∈ c.children ∧ BytesLike ch0) := by
  cases h with
  | dyn he => exact .inl he
  | abi he => exact .inr (.inl he)
  | logical ch0 he hop hm hb _ => exact .inr (.inr ⟨he, hop, ch0, hm, hb⟩)

/-! ## Non-structural nodes and Zips describe nothing -/

theorem NonStruct.not_zip {c : Condition} (h : NonStruct c) : ¬ ZipNode c := by
  intro hz
  cases hz with
  | mk t _ hop _ =>
    cases h with
    | leaf _ _ hnav => rcases hop with hop | hop <;> rw [hop] at hnav <;> simp [isNavOp] at hnav
    | logical _ hop' _ => rcases hop with hop | hop <;> rcases hop' with hop' | hop' <;> simp_all

theorem ZipNode.not_bytesLike {c : Condition} (h : ZipNode c) : ¬ BytesLike c := by
  intro hb
  cases h with
  | mk t he hop _ =>
    rcases BytesLike.inv hb with h | h | ⟨_, hop', _⟩
    · simp_all
    · simp_all
    · rcases hop with hop | hop <;> rcases hop' with hop' | hop' <;> simp_all

/-! ## Non-structural kinds -/

theorem ns_sound (s : Bool) (c : Condition) (h : classify s c = some .ns) : NonStruct c := by
  rw [classify_eq] at h
  obtain ⟨ks, hks, hn⟩ := Option.bind_eq_some_iff.mp h
  cases he : c.encoding <;> rw [he] at hn
  case None =>
    rcases node_none hn with ⟨_, hk, _⟩ | ⟨_, hcs, hnav⟩ | ⟨hop, hl⟩
    · cases hk
    · exact .leaf (.inl he) hcs hnav
    · refine .logical he hop fun ch hm => ?_
      obtain ⟨k, hk, hck⟩ := classifyAll_mem s hks hm
      rw [logicalKind_ns hl k hk] at hck
      exact ns_sound s ch hck
  case Static => cases (node_word (.inl rfl) hn).1
  case Dynamic => cases (node_word (.inr rfl) hn).1
  case Tuple => obtain ⟨_, hk, _⟩ := node_tuple hn; cases hk
  case Array => obtain ⟨_, hk, _⟩ := node_array hn; cases hk
  case AbiEncoded => obtain ⟨_, hk, _⟩ := node_abi hn; cases hk
  case EtherValue =>
    obtain ⟨_, hcs, hnav⟩ := node_ether hn
    exact .leaf (.inr he) hcs hnav
termination_by sizeOf c
decreasing_by exact sizeOf_child hm

theorem zip_sound (s : Bool) (c : Condition) (h : classify s c = some .zip) : ZipNode c := by
  rw [classify_eq] at h
  obtain ⟨ks, hks, hn⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨hlen, _⟩ := classifyAll_get s hks
  cases he : c.encoding <;> rw [he] at hn
  case None =>
    rcases node_none hn with ⟨hop, _, ts, rfl⟩ | ⟨hk, _⟩ | ⟨_, hl⟩
    · match hc : c.children, hlen with
      | [t], _ => exact .mk t he hop hc
    · cases hk
    · exact absurd hl logicalKind_not_zip
  case Static => cases (node_word (.inl rfl) hn).1
  case Dynamic => cases (node_word (.inr rfl) hn).1
  case Tuple => obtain ⟨_, hk, _⟩ := node_tuple hn; cases hk
  case Array => obtain ⟨_, hk, _⟩ := node_array hn; cases hk
  case AbiEncoded => obtain ⟨_, hk, _⟩ := node_abi hn; cases hk
  case EtherValue => cases (node_ether hn).1

/-! ## Slices -/

theorem win_of (s : Bool) (c : Condition) (h : classify s c = some (.ty .static))
    (he : c.encoding = .Static) : Win c := by
  rw [classify_eq] at h
  obtain ⟨ks, hks, hn⟩ := Option.bind_eq_some_iff.mp h
  rw [he] at hn
  rcases (node_word (.inl rfl) hn).2 with hl | hsl
  · obtain ⟨hcs, hnav⟩ := leafOk_iff.mp hl
    exact .leaf he hcs hnav
  · obtain ⟨hop, h1, h32, ch, hcs, hche, hks'⟩ := sliceOk_iff.mp hsl
    have hm : ch ∈ c.children := by rw [hcs]; simp
    obtain ⟨k, hk, hck⟩ := classifyAll_mem s hks hm
    rw [hks'] at hk
    simp only [List.mem_singleton] at hk
    subst hk
    exact .slice he hop hcs h1 h32 (win_of s ch hck hche)
termination_by sizeOf c
decreasing_by exact sizeOf_child hm

/-! ## Bytes-like nodes have bytes-like types -/

theorem bytesLike_ty (s : Bool) (c : Condition) {t : Ty} (h : classify s c = some (.ty t))
    (hb : BytesLike c) : t.isBytesLike = true := by
  rw [classify_eq] at h
  obtain ⟨ks, hks, hn⟩ := Option.bind_eq_some_iff.mp h
  rcases BytesLike.inv hb with he | he | ⟨he, _, ch0, hm, hb0⟩
  · rw [he] at hn
    have := (node_word (.inr rfl) hn).1
    simp only [K.ty.injEq] at this; subst this; rfl
  · rw [he] at hn
    obtain ⟨ts, hk, _⟩ := node_abi hn
    simp only [K.ty.injEq] at hk; subst hk; rfl
  · rw [he] at hn
    rcases node_none hn with ⟨_, hk, _⟩ | ⟨hk, _⟩ | ⟨_, hl⟩
    · cases hk
    · cases hk
    · obtain ⟨_, hall⟩ := logicalKind_ty hl
      obtain ⟨k, hk, hck⟩ := classifyAll_mem s hks hm
      rcases hall k hk with rfl | ⟨rfl, _⟩ | ⟨t', rfl, ht'⟩
      · exact (NonStruct.not_bytesLike (ns_sound s ch0 hck) hb0).elim
      · exact (ZipNode.not_bytesLike (zip_sound s ch0 hck) hb0).elim
      · have := bytesLike_ty s ch0 hck hb0
        rcases ht' with rfl | ⟨_, rfl, _⟩
        · exact this
        · rfl
termination_by sizeOf c
decreasing_by exact sizeOf_child hm

/-! ## Typed values are described -/

theorem descAll_of_get {s : Bool} : ∀ {cs : List Condition} {vs : List Val},
    cs.length = vs.length →
    (∀ i (h1 : i < cs.length) (h2 : i < vs.length), DescS s cs[i] vs[i]) → DescAll s cs vs
  | [], [], _, _ => .nil
  | _ :: _, _ :: _, hl, hg =>
    .cons (hg 0 (by simp) (by simp)) (descAll_of_get (by simpa using hl) fun i h1 h2 =>
      hg (i + 1) (by simp; omega) (by simp; omega))
  | [], _ :: _, hl, _ | _ :: _, [], hl, _ => by simp at hl

/-- **Typed values are described.** A node of type `t` describes every value
    of type `t` (`DescS`: possibly as an interpretation that does not hold,
    for nested calldata with `s = true`), and describes it outright when the
    value parses as the node's own `call` type (`Strict`). -/
theorem desc_of_ty (s : Bool) (c : Condition) : ∀ {t : Ty} {u : Val},
    classify s c = some (.ty t) → HasT s u t → DescS s c u ∧ (Strict s u t → Desc s c u) := by
  intro t u h hu
  have ih : ∀ ch, ch ∈ c.children → ∀ {t : Ty} {u : Val},
      classify s ch = some (.ty t) → HasT s u t → DescS s ch u ∧ (Strict s u t → Desc s ch u) :=
    fun ch hm => desc_of_ty s ch
  rw [classify_eq] at h
  obtain ⟨ks, hks, hn⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨hlen, hget⟩ := classifyAll_get s hks
  cases he : c.encoding <;> rw [he] at hn
  case None =>
    rcases node_none hn with ⟨_, hk, _⟩ | ⟨hk, _⟩ | ⟨hop, hl⟩
    · cases hk
    · cases hk
    obtain ⟨⟨i, hi, ⟨t0, hk0⟩, hpre⟩, hall⟩ := logicalKind_ty hl
    have hi' : i < c.children.length := by omega
    have hstruct : ∀ ch, ch ∈ c.children → ∀ t', classify s ch = some (.ty t') →
        (t' = t ∨ (s = true ∧ t = .dynamic ∧ t'.isBytesLike = true)) → DescS s ch u := by
      intro ch hm t' hck ht'
      have hu' : HasT s u t' := by
        rcases ht' with rfl | ⟨hs, rfl, hb⟩
        · exact hu
        · exact hasT_of_bytesLike hs (isBytesLike_of_hasT hu rfl) hb
      exact (ih ch hm hck hu').1
    have hch : ∀ ch, ch ∈ c.children → DescSN s ch u := by
      intro ch hm
      obtain ⟨k, hk, hck⟩ := classifyAll_mem s hks hm
      rcases hall k hk with rfl | ⟨rfl, hst⟩ | ⟨t', rfl, ht'⟩
      · exact .ns (ns_sound s ch hck)
      · exact .zip (zip_sound s ch hck) (by rw [hasT_isStatic s hu]; exact hst)
      · exact .ds (hstruct ch hm t' hck ht')
    have hm0 : c.children[i] ∈ c.children := List.getElem_mem hi'
    have hc0 := hget i hi' hi
    rw [hk0] at hc0
    have h0 : DescS s c.children[i] u := by
      refine hstruct _ hm0 t0 hc0 ?_
      rcases hall _ (List.getElem_mem hi) with h | ⟨h, _⟩ | ⟨t', h, ht'⟩
      · rw [hk0] at h; cases h
      · rw [hk0] at h; cases h
      · rw [hk0] at h; cases h; exact ht'
    have hza : ZipsAfter c.children c.children[i] := by
      refine ⟨c.children.take i, c.children.drop (i + 1), ?_, ?_⟩
      · conv => lhs; rw [← List.take_append_drop i c.children, List.drop_eq_getElem_cons hi']
      · intro ch hm hz
        obtain ⟨j, hj, rfl⟩ := List.mem_take_iff_getElem.mp hm
        have hjk := hget j (by omega) (by omega)
        rw [hpre j (by omega)] at hjk
        exact NonStruct.not_zip (ns_sound s _ hjk) hz
    have D : Desc s c u := .logical c.children[i] he hop hm0 h0 hch hza
    exact ⟨.desc D, fun _ => D⟩
  case Static =>
    obtain ⟨hk, hw'⟩ := node_word (.inl rfl) hn
    simp only [K.ty.injEq] at hk; subst hk
    obtain ⟨w, rfl, hw⟩ : ∃ w, u = .word w ∧ w.length = 32 := by
      cases u with
      | word w => simp only [HasT] at hu; exact ⟨w, rfl, hu.2⟩
      | _ => simp [HasT] at hu
    have D : Desc s c (.word w) := by
      rcases hw' with hl | hsl
      · obtain ⟨hcs, hnav⟩ := leafOk_iff.mp hl; exact .word he hcs hnav hw
      · obtain ⟨hop, h1, h32, ch, hcs, hche, hks'⟩ := sliceOk_iff.mp hsl
        have hm : ch ∈ c.children := by rw [hcs]; simp
        obtain ⟨k, hk, hck⟩ := classifyAll_mem s hks hm
        rw [hks'] at hk; simp only [List.mem_singleton] at hk; subst hk
        exact .sliceWord he hop hcs h1 h32 (win_of s ch hck hche) hw
    exact ⟨.desc D, fun _ => D⟩
  case Dynamic =>
    obtain ⟨hk, hw'⟩ := node_word (.inr rfl) hn
    simp only [K.ty.injEq] at hk; subst hk
    have hu' := isBytesLike_of_hasT hu rfl
    have D : Desc s c u := by
      rcases hw' with hl | hsl
      · obtain ⟨hcs, hnav⟩ := leafOk_iff.mp hl; exact .bytes he hcs hnav hu'
      · obtain ⟨hop, h1, h32, ch, hcs, hche, hks'⟩ := sliceOk_iff.mp hsl
        have hm : ch ∈ c.children := by rw [hcs]; simp
        obtain ⟨k, hk, hck⟩ := classifyAll_mem s hks hm
        rw [hks'] at hk; simp only [List.mem_singleton] at hk; subst hk
        exact .sliceBytes he hop hcs h1 h32 (win_of s ch hck hche) hu'
    exact ⟨.desc D, fun _ => D⟩
  case Tuple =>
    obtain ⟨ts, hk, hne, hop, hts⟩ := node_tuple hn
    simp only [K.ty.injEq] at hk; subst hk
    have hks' := allTy_eq hts; subst hks'
    obtain ⟨vs, rfl, hvs⟩ : ∃ vs, u = .tuple vs ∧ HasTAll s vs ts := by
      cases u with
      | tuple vs =>
        simp only [HasT] at hu
        obtain ⟨ts', h', hall⟩ := hu
        cases h'; exact ⟨vs, rfl, hall⟩
      | _ => simp [HasT] at hu
    obtain ⟨hl2, hg2⟩ := hasTAll_get s hvs
    simp only [List.length_map] at hlen
    have hall : DescAll s c.children vs := descAll_of_get (by omega) fun i h1 h2 => by
      have hc := hget i h1 (by simp; omega)
      simp only [List.getElem_map] at hc
      exact (ih _ (List.getElem_mem h1) hc (hg2 i h2 (by omega))).1
    have hvne : vs ≠ [] := by
      intro h; subst h
      exact hne (List.eq_nil_of_length_eq_zero (by simp at hl2; omega))
    have D : Desc s c (.tuple vs) := .tuple he hvne hall hop
    exact ⟨.desc D, fun _ => D⟩
  case Array =>
    obtain ⟨t0, hk, hop, hne, hallk⟩ := node_array hn
    simp only [K.ty.injEq] at hk; subst hk
    obtain ⟨vs, rfl, hvs⟩ : ∃ vs, u = .array vs ∧ HasTEach s vs t0 := by
      cases u with
      | array vs =>
        simp only [HasT] at hu
        obtain ⟨t', h', h⟩ := hu
        cases h'; exact ⟨vs, rfl, h⟩
      | _ => simp [HasT] at hu
    have hev := (hasTEach_iff s t0).mp hvs
    have hchild : ∀ ch, ch ∈ c.children → ∀ v, v ∈ vs → DescS s ch v := by
      intro ch hm v hv
      obtain ⟨k, hk, hck⟩ := classifyAll_mem s hks hm
      rw [hallk k hk] at hck
      exact (ih ch hm hck (hev v hv)).1
    obtain ⟨c0, cs, hcs⟩ : ∃ c0 cs, c.children = c0 :: cs := by
      cases hc : c.children with
      | nil => rw [hc] at hlen; exact absurd (List.eq_nil_of_length_eq_zero hlen) hne
      | cons c0 cs => exact ⟨c0, cs, rfl⟩
    have hm0 : c0 ∈ c.children := by rw [hcs]; simp
    have hop' : isNavOp c.operator = false ∨ c.operator = .Matches ∨ c.operator = .ArraySome ∨
        c.operator = .ArrayEvery ∨ c.operator = .ArrayTailMatches := by
      rcases hop with h | h
      · exact .inl h
      · simp only [isArrayOp, Bool.or_eq_true, beq_iff_eq] at h
        rcases h with ((h | h) | h) | h
        · exact .inr (.inl h)
        · exact .inr (.inr (.inl h))
        · exact .inr (.inr (.inr (.inl h)))
        · exact .inr (.inr (.inr (.inr h)))
    have D : Desc s c (.array vs) := .array c0 cs he hcs (hchild c0 hm0)
      (fun i hi hv => hchild _ (List.getElem_mem hi) _ (List.getElem_mem hv))
      (fun j hj _ => hchild _ (List.getElem_mem hj) _ (List.getElem_mem _)) hop'
    exact ⟨.desc D, fun _ => D⟩
  case AbiEncoded =>
    obtain ⟨ts, hk, hne, hop, hts⟩ := node_abi hn
    simp only [K.ty.injEq] at hk; subst hk
    have hks' := allTy_eq hts; subst hks'
    simp only [List.length_map] at hlen
    have strict : Strict s u (.call c.leadingBytes ts) → Desc s c u := by
      intro hS
      simp only [Strict] at hS
      obtain ⟨pre, args, rfl, hpre, hargs⟩ := hS
      obtain ⟨hl2, hg2⟩ := hasTAll_get s hargs
      have hall : DescAll s c.children args := descAll_of_get (by omega) fun i h1 h2 => by
        have hc := hget i h1 (by simp; omega)
        simp only [List.getElem_map] at hc
        exact (ih _ (List.getElem_mem h1) hc (hg2 i h2 (by omega))).1
      have hane : args ≠ [] := by
        intro h; subst h
        exact hne (List.eq_nil_of_length_eq_zero (by simp at hl2; omega))
      exact .call he hpre.symm hane hall hop
    refine ⟨?_, strict⟩
    by_cases hS : Strict s u (.call c.leadingBytes ts)
    · exact .desc (strict hS)
    · have hs : s = true := by
        cases u with
        | bytes _ =>
          simp only [HasT] at hu
          rcases hu with h | ⟨hs, _⟩
          · cases h
          · exact hs
        | call pre args =>
          simp only [HasT] at hu
          rcases hu with h | ⟨lb, ts', h, h2 | hs⟩
          · cases h
          · cases h; exact absurd ⟨pre, args, rfl, h2.1, h2.2⟩ hS
          · exact hs
        | _ => simp [HasT] at hu
      exact .stray hs (.abi he) (isBytesLike_of_hasT hu rfl)
  case EtherValue => cases (node_ether hn).1
termination_by sizeOf c
decreasing_by exact sizeOf_child hm

/-! ## Described values are typed -/

/-- The converse: a value a checked node describes has the node's type. Used
    for Zips, whose fields must describe whatever the Pluck node's elements
    are. -/
theorem hasT_of_descS (s : Bool) (c : Condition) : ∀ {t : Ty} {u : Val},
    classify s c = some (.ty t) → DescS s c u → HasT s u t := by
  intro t u h hD
  have ih : ∀ ch, ch ∈ c.children → ∀ {t : Ty} {u : Val},
      classify s ch = some (.ty t) → DescS s ch u → HasT s u t :=
    fun ch hm => hasT_of_descS s ch
  have hc := h
  rw [classify_eq] at h
  obtain ⟨ks, hks, hn⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨hlen, hget⟩ := classifyAll_get s hks
  cases hD with
  | stray hs hb hu => exact hasT_of_bytesLike hs hu (bytesLike_ty s c hc hb)
  | desc hD =>
  cases he : c.encoding <;> rw [he] at hn
  case None =>
    rcases node_none hn with ⟨_, hk, _⟩ | ⟨hk, _⟩ | ⟨_, hl⟩
    · cases hk
    · cases hk
    obtain ⟨_, hall⟩ := logicalKind_ty hl
    obtain ⟨_, ch0, hm, h0⟩ := Desc.none_inv hD (.inl he)
    obtain ⟨k, hk, hck⟩ := classifyAll_mem s hks hm
    rcases hall k hk with rfl | ⟨rfl, _⟩ | ⟨t', rfl, ht'⟩
    · exact (NonStruct.not_descS (ns_sound s ch0 hck) h0).elim
    · exact (ZipNode.not_descS (zip_sound s ch0 hck) h0).elim
    · have := ih ch0 hm hck h0
      rcases ht' with rfl | ⟨_, rfl, hb⟩
      · exact this
      · exact hasT_dynamic (isBytesLike_of_hasT this hb)
  case Static =>
    have := (node_word (.inl rfl) hn).1
    simp only [K.ty.injEq] at this; subst this
    obtain ⟨w, rfl, hw⟩ := Desc.static_inv hD he
    simp [HasT, hw]
  case Dynamic =>
    have := (node_word (.inr rfl) hn).1
    simp only [K.ty.injEq] at this; subst this
    exact hasT_dynamic (Desc.dynamic_inv hD he)
  case Tuple =>
    obtain ⟨ts, hk, _, _, hts⟩ := node_tuple hn
    simp only [K.ty.injEq] at hk; subst hk
    have hks' := allTy_eq hts; subst hks'
    simp only [List.length_map] at hlen
    obtain ⟨vs, rfl, hall⟩ := Desc.tuple_inv hD he
    have hl := DescAll.length_eq hall
    simp only [HasT]
    refine ⟨ts, rfl, hasTAll_of_get s (by omega) fun i h1 h2 => ?_⟩
    have hc := hget i (by omega) (by simp; omega)
    simp only [List.getElem_map] at hc
    exact ih _ (List.getElem_mem _) hc (DescAll.get hall i (by omega))
  case Array =>
    obtain ⟨t0, hk, _, _, hallk⟩ := node_array hn
    simp only [K.ty.injEq] at hk; subst hk
    obtain ⟨vs, c0, cs, rfl, hcs, h0⟩ := Desc.array_inv hD he
    have hm0 : c0 ∈ c.children := by rw [hcs]; simp
    obtain ⟨k, hk, hck⟩ := classifyAll_mem s hks hm0
    rw [hallk k hk] at hck
    simp only [HasT]
    exact ⟨t0, rfl, (hasTEach_iff s t0).mpr fun v hv => ih c0 hm0 hck (h0 v hv)⟩
  case AbiEncoded =>
    obtain ⟨ts, hk, _, _, hts⟩ := node_abi hn
    simp only [K.ty.injEq] at hk; subst hk
    have hks' := allTy_eq hts; subst hks'
    simp only [List.length_map] at hlen
    obtain ⟨pre, args, rfl, hlb, hall⟩ := Desc.call_inv hD he
    have hl := DescAll.length_eq hall
    simp only [HasT]
    refine .inr ⟨c.leadingBytes, ts, rfl, .inl ⟨hlb.symm, hasTAll_of_get s (by omega) fun i h1 h2 => ?_⟩⟩
    have hc := hget i (by omega) (by simp; omega)
    simp only [List.getElem_map] at hc
    exact ih _ (List.getElem_mem _) hc (DescAll.get hall i (by omega))
  case EtherValue => cases (node_ether hn).1
termination_by sizeOf c
decreasing_by exact sizeOf_child hm

/-! ## Zips -/

theorem zipOK_of (s : Bool) (root : Condition) (hz : zipCheck s root = true) : ZipOK s root := by
  intro z pk f hzs hpks hzop hf hpk hcv
  have hz1 := List.all_eq_true.mp hz z (Example.mem_nodes hzs)
  have hzop' : (z.operator == .ZipSome || z.operator == .ZipEvery) = true := by
    rcases hzop with h | h <;> simp [h]
  rw [hzop'] at hz1
  simp only [Bool.not_true, Bool.false_or] at hz1
  have hf1 := List.all_eq_true.mp hz1 f (List.mem_range.mpr hf)
  unfold zipFieldOk at hf1
  have hp := List.all_eq_true.mp hf1 pk (Example.mem_nodes hpks)
  have hpc : (pk.operator == .Pluck && cvByte pk.compValue 0 == cvByte z.compValue f) = true := by
    simp [hpk, hcv]
  rw [hpc] at hp
  simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true, beq_iff_eq] at hp
  obtain ⟨henc, hm⟩ := hp
  refine ⟨henc, fun vs hD v hv => ?_⟩
  split at hm
  · rename_i t1 t2 h1 h2
    simp only [beq_iff_eq] at hm; subst hm
    obtain ⟨vs', c0, cs, hvs, hch, h0⟩ := Desc.array_inv hD henc
    cases hvs
    rw [hch] at h1
    exact (desc_of_ty s _ h2 (hasT_of_descS s c0 h1 (h0 v hv))).1
  · cases hm

/-! ## The root -/

theorem rootOk_eq (s : Bool) (c : Condition) :
    rootOk s c = (c.encoding == .AbiEncoded ||
      (c.encoding == .None && (c.operator == .And || c.operator == .Or) &&
        rootOkAll s c.children)) := by
  rcases c with ⟨e, op, cs, i, sz, lb, cv⟩
  simp [rootOk]

theorem rootOkAll_mem (s : Bool) : ∀ {cs : List Condition}, rootOkAll s cs = true →
    ∀ ch, ch ∈ cs → rootOk s ch = true ∨ classify s ch = some .ns ∨ classify s ch = some .zip
  | [], _, _, hm => by cases hm
  | c :: cs, h, ch, hm => by
    simp only [rootOkAll, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
    rcases List.mem_cons.mp hm with rfl | hm
    · rcases h.1 with (h | h) | h
      · exact .inl h
      · exact .inr (.inl h)
      · exact .inr (.inr h)
    · exact rootOkAll_mem s h.2 ch hm

theorem rootOK_of (s : Bool) (c : Condition) (h : rootOk s c = true) : RootOK c := by
  rw [rootOk_eq] at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
  rcases h with he | ⟨⟨he, hop⟩, hall⟩
  · exact .abi he
  · refine .logical he hop fun ch hm => ?_
    rcases rootOkAll_mem s hall ch hm with h | h | h
    · exact .ok (rootOK_of s ch h)
    · exact .ns (ns_sound s ch h)
    · exact .zip (zip_sound s ch h)
termination_by sizeOf c
decreasing_by exact sizeOf_child hm

/-! ## The check -/

/-- **Soundness of `checkCondition`.** If the check accepts `root` with type
    `t`, then `root` satisfies the hypotheses of the decoder theorems for
    every calldata `pre ++ enc(args)` of type `t`: `RootOK root`,
    `ZipOK s root` and `Desc s root (.call pre args)`. -/
theorem checkCondition_sound {s : Bool} {root : Condition} {t : Ty}
    (h : checkCondition s root = some t) :
    RootOK root ∧ ZipOK s root ∧
      ∀ pre args, HasT s (.call pre args) t → Strict s (.call pre args) t →
        Desc s root (.call pre args) := by
  unfold checkCondition at h
  split at h
  · rename_i t' hc
    split at h
    · rename_i hok
      simp only [Option.some.injEq] at h; subst h
      simp only [Bool.and_eq_true] at hok
      exact ⟨rootOK_of s root hok.1, zipOK_of s root hok.2,
        fun pre args hu hS => (desc_of_ty s root hc hu).2 hS⟩
    · cases h
  · cases h

/-- The same for a root of type `call lb ts` (an `AbiEncoded` root, or an
    `And`/`Or` of such with one type): every calldata with `lb` leading bytes
    and arguments of types `ts`. -/
theorem checkCondition_call {s : Bool} {root : Condition} {lb : Nat} {ts : List Ty}
    (h : checkCondition s root = some (.call lb ts)) {pre : Bytes} {args : List Val}
    (hpre : pre.length = lb) (hargs : HasTAll s args ts) :
    RootOK root ∧ ZipOK s root ∧ Desc s root (.call pre args) := by
  obtain ⟨hr, hz, hd⟩ := checkCondition_sound h
  exact ⟨hr, hz, hd pre args (.inr ⟨lb, ts, rfl, .inl ⟨hpre, hargs⟩⟩) ⟨pre, args, rfl, hpre, hargs⟩⟩

/-- **End to end**, for the comparison operands (`decoder_input`): on a tree
    the check accepts, for every well-typed calldata, every visited node that
    reads `__input` reads the spec encoding of its value (or a window of it,
    below a `Slice`, or the ether value), unless it sits in an interpretation
    that does not hold (only with `s = true`). -/
theorem checked_input {s : Bool} {root : Condition} {lb : Nat} {ts : List Ty}
    (h : checkCondition s root = some (.call lb ts)) {pre : Bytes} {args : List Val}
    (hpre : pre.length = lb) (hargs : HasTAll s args ts) (suffix : Bytes)
    (hlen : (calldata pre args suffix).length < 2 ^ 255)
    {p : List Nat} {d : Condition} {l : Nat}
    (hv : Eval (calldata pre args suffix) (annotate root) p d l)
    (hop : readsInput d.operator = true) :
    (∃ u, (Val.call pre args).sub p = some u ∧
      input (calldata pre args suffix) l d = expectInput (enc u)) ∨
    (∃ u bs, (Val.call pre args).sub p = some u ∧ IsWindow bs (content u) ∧
      input (calldata pre args suffix) l d = .word (wordVal bs)) ∨
    input (calldata pre args suffix) l d = .etherValue ∨
    InStray s (calldata pre args suffix) (.call pre args) p d l := by
  obtain ⟨hr, hz, hd⟩ := checkCondition_call h hpre hargs
  exact decoder_input root pre args suffix hd hr hz hlen hv hop

end ConditionCheck
