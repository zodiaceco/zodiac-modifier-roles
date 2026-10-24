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

theorem hasTPre_get (s : Bool) :
    ∀ {vs : List Val} {ts : List Ty}, HasTPre s vs ts →
      ts.length ≤ vs.length ∧ ∀ i (h1 : i < vs.length) (h2 : i < ts.length), HasT s vs[i] ts[i]
  | _, [], _ => by simp
  | v :: vs, t :: ts, h => by
    simp only [HasTPre] at h
    obtain ⟨hl, hg⟩ := hasTPre_get s h.2
    refine ⟨by simp; omega, ?_⟩
    intro i h1 h2
    cases i with
    | zero => simpa using h.1
    | succ i => simpa using hg i (by simp at h1; omega) (by simp at h2; omega)
  | [], _ :: _, h => by simp [HasTPre] at h

theorem hasTPre_of_get (s : Bool) :
    ∀ {vs : List Val} {ts : List Ty}, ts.length ≤ vs.length →
      (∀ i (h1 : i < vs.length) (h2 : i < ts.length), HasT s vs[i] ts[i]) → HasTPre s vs ts
  | _, [], _, _ => by simp [HasTPre]
  | v :: vs, t :: ts, hl, hg => by
    simp only [HasTPre]
    exact ⟨hg 0 (by simp) (by simp),
      hasTPre_of_get s (by simp at hl; omega) fun i h1 h2 =>
        hg (i + 1) (by simp; omega) (by simp; omega)⟩
  | [], _ :: _, hl, _ => by simp at hl

theorem hasTPre_of_all {s : Bool} {vs : List Val} {ts : List Ty} (h : HasTAll s vs ts) :
    HasTPre s vs ts := by
  obtain ⟨hl, hg⟩ := hasTAll_get s h
  exact hasTPre_of_get s (by omega) hg

theorem hasTAll_of_pre {s : Bool} {vs : List Val} {ts : List Ty} (h : HasTPre s vs ts)
    (hl : vs.length = ts.length) : HasTAll s vs ts := by
  obtain ⟨_, hg⟩ := hasTPre_get s h
  exact hasTAll_of_get s hl hg

/-- An open type's fields, as the exact types of the first values. -/
theorem hasTPre_take {s : Bool} {vs : List Val} {ts : List Ty} (h : HasTPre s vs ts) :
    HasTAll s (vs.take ts.length) ts := by
  obtain ⟨hl, hg⟩ := hasTPre_get s h
  exact hasTAll_of_get s (by simp; omega) fun i h1 h2 => by
    simp only [List.getElem_take]; exact hg i (by simp at h1; omega) h2

theorem allStatic_take_drop' : ∀ (vs : List Val) (k : Nat),
    Val.allStatic vs = (Val.allStatic (vs.take k) && Val.allStatic (vs.drop k)) :=
  DecoderFaithfulness.allStatic_take_drop

mutual
  theorem hasT_isStatic (s : Bool) : ∀ {u : Val} {t : Ty}, HasT s u t → u.isStatic = t.isStatic
    | .word _, t, h => by simp only [HasT] at h; rw [h.1]; rfl
    | .bytes _, t, h => by
      simp only [HasT] at h
      rcases h with rfl | ⟨_, lb, ts, o, rfl⟩ <;> rfl
    | .tuple vs, t, h => by
      simp only [HasT] at h
      obtain ⟨ts, o, rfl, h⟩ := h
      simp only [Val.isStatic, Ty.isStatic]
      cases o
      · exact hasTAll_allStatic s h
      · simp only [ite_true] at h
        have ht := hasTAll_allStatic s (hasTPre_take h.1)
        by_cases hlt : ts.length < vs.length
        · rw [h.2 hlt, allStatic_take_drop' vs ts.length, ht, h.2 hlt]; rfl
        · rw [List.take_of_length_le (by omega)] at ht; exact ht
    | .array _, t, h => by
      simp only [HasT] at h
      obtain ⟨t', rfl, _⟩ := h
      rfl
    | .call _ _, t, h => by
      simp only [HasT] at h
      rcases h with rfl | ⟨lb, ts, o, rfl, _⟩ <;> rfl

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
    simp only [HasT] at h; obtain ⟨ts, o, rfl, _⟩ := h; simp [Ty.isBytesLike] at ht
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
  | call lb ts o =>
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

/-! ## Subtypes -/

theorem le_refl (s : Bool) (t : Ty) : Ty.le s t t = true := by simp [Ty.le]

theorem subPre_length {s : Bool} : ∀ {ts1 ts2 : List Ty}, Ty.subPre s ts1 ts2 = true →
    ts2.length ≤ ts1.length
  | _, [], _ => by simp
  | _ :: _, _ :: _, h => by
    simp only [Ty.subPre, Bool.and_eq_true] at h
    have := subPre_length h.2; simp; omega
  | [], _ :: _, h => by simp [Ty.subPre] at h

theorem subPre_get {s : Bool} : ∀ {ts1 ts2 : List Ty}, Ty.subPre s ts1 ts2 = true →
    ∀ i (h1 : i < ts1.length) (h2 : i < ts2.length), Ty.le s ts1[i] ts2[i] = true
  | _, [], _, _, _, h2 => by simp at h2
  | _ :: _, _ :: _, h, i, h1, h2 => by
    simp only [Ty.subPre, Bool.and_eq_true] at h
    cases i with
    | zero => simpa [Ty.le] using h.1
    | succ i => simpa using subPre_get h.2 i (by simp at h1; omega) (by simp at h2; omega)
  | [], _ :: _, h, _, _, _ => by simp [Ty.subPre] at h

mutual
  /-- **Subtypes.** Every value of type `t1` has every supertype `t2`. -/
  theorem hasT_sub (s : Bool) : ∀ {u : Val} {t1 t2 : Ty}, Ty.sub s t1 t2 = true →
      HasT s u t1 → HasT s u t2
    | .word _, t1, t2, hs, h => by
      simp only [HasT] at h ⊢
      obtain ⟨rfl, hw⟩ := h
      cases t2 <;> simp_all [Ty.sub]
    | .bytes _, t1, t2, hs, h => by
      simp only [HasT] at h ⊢
      rcases h with rfl | ⟨hs', lb, ts, o, rfl⟩
      · cases t2 <;> simp_all [Ty.sub]
      · cases t2 <;> simp_all [Ty.sub]
    | .tuple vs, t1, t2, hs, h => by
      simp only [HasT] at h ⊢
      obtain ⟨ts1, o1, rfl, h⟩ := h
      cases t2 with
      | tuple ts2 o2 =>
        refine ⟨ts2, o2, rfl, ?_⟩
        have hpre1 : HasTPre s vs ts1 := by
          cases o1
          · exact hasTPre_of_all (by simpa using h)
          · simp only [ite_true] at h; exact h.1
        have hsp : Ty.subPre s ts1 ts2 = true := by
          cases o2
          · simp only [Ty.sub, ite_false, Bool.false_eq_true, Bool.and_eq_true] at hs; exact hs.2
          · simp only [Ty.sub, ite_true, Bool.and_eq_true] at hs; exact hs.1.2
        have hpre2 : HasTPre s vs ts2 := hasTPre_subPre s hpre1 hsp
        cases o2
        · simp only [Ty.sub, ite_false, Bool.false_eq_true, Bool.and_eq_true, Bool.not_eq_true',
            decide_eq_true_eq] at hs
          obtain ⟨⟨ho1, hl⟩, _⟩ := hs
          subst ho1
          simp only [ite_false, Bool.false_eq_true] at h ⊢
          exact hasTAll_of_pre hpre2 (by have := (hasTAll_get s h).1; omega)
        · have h3 : (!(decide (ts2.length < ts1.length) || o1) || !Ty.allStatic ts2) = true := by
            simp only [Ty.sub, ite_true, Bool.and_eq_true] at hs; exact hs.2
          simp only [ite_true]
          refine ⟨hpre2, fun hlt => ?_⟩
          cases hst : Ty.allStatic ts2
          · rfl
          · exfalso
            rw [hst] at h3
            have ho1 : o1 = false := by cases o1 <;> simp_all
            have hge : ts1.length ≤ ts2.length := by
              rcases Nat.lt_or_ge ts2.length ts1.length with hl | hl
              · simp [hl] at h3
              · exact hl
            subst ho1
            simp only [ite_false, Bool.false_eq_true] at h
            have := (hasTAll_get s h).1; omega
      | _ => cases o1 <;> simp [Ty.sub] at hs
    | .array vs, t1, t2, hs, h => by
      simp only [HasT] at h ⊢
      obtain ⟨a, rfl, h⟩ := h
      cases t2 with
      | array b =>
        simp only [Ty.sub] at hs
        refine ⟨b, rfl, (hasTEach_iff s b).mpr fun v hv => ?_⟩
        have hv' := (hasTEach_iff s a).mp h v hv
        simp only [Bool.or_eq_true, decide_eq_true_eq] at hs
        rcases hs with rfl | hs
        · exact hv'
        · exact hasT_sub s hs hv'
      | _ => simp [Ty.sub] at hs
    | .call pre args, t1, t2, hs, h => by
      simp only [HasT] at h ⊢
      rcases h with rfl | ⟨lb1, ts1, o1, rfl, h⟩
      · cases t2 <;> simp_all [Ty.sub]
      · cases t2 with
        | dynamic => exact .inl rfl
        | call lb2 ts2 o2 =>
          refine .inr ⟨lb2, ts2, o2, rfl, ?_⟩
          by_cases hsv : s = true
          · exact .inr hsv
          · simp only [Ty.sub, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hs
            rcases hs with ⟨hlb, hs⟩ | hs
            · subst hlb
              rcases h with ⟨hpre, h⟩ | h
              · refine .inl ⟨hpre, ?_⟩
                have hpre1 : HasTPre s args ts1 := by
                  cases o1
                  · exact hasTPre_of_all (by simpa using h)
                  · simpa using h
                cases o2
                · simp only [ite_false, Bool.false_eq_true, Bool.and_eq_true, Bool.not_eq_true',
                    decide_eq_true_eq] at hs
                  obtain ⟨⟨ho1, hl⟩, hsp⟩ := hs
                  subst ho1
                  simp only [ite_false, Bool.false_eq_true] at h ⊢
                  exact hasTAll_of_pre (hasTPre_subPre s hpre1 hsp)
                    (by have := (hasTAll_get s h).1; omega)
                · simp only [ite_true, Bool.and_eq_true, decide_eq_true_eq] at hs ⊢
                  exact hasTPre_subPre s hpre1 hs.2
              · exact absurd h hsv
            · exact absurd hs hsv
        | _ => simp [Ty.sub] at hs

  theorem hasTPre_subPre (s : Bool) : ∀ {vs : List Val} {ts1 ts2 : List Ty},
      HasTPre s vs ts1 → Ty.subPre s ts1 ts2 = true → HasTPre s vs ts2
    | _, _, [], _, _ => by simp [HasTPre]
    | v :: vs, t1 :: ts1, t2 :: ts2, h, hs => by
      simp only [HasTPre] at h ⊢
      simp only [Ty.subPre, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hs
      refine ⟨?_, hasTPre_subPre s h.2 hs.2⟩
      rcases hs.1 with rfl | h1
      · exact h.1
      · exact hasT_sub s h1 h.1
    | [], _ :: _, _, h, _ => by simp [HasTPre] at h
    | _ :: _, [], _ :: _, _, hs => by simp [Ty.subPre] at hs
end

theorem hasT_le {s : Bool} {u : Val} {t1 t2 : Ty} (h : Ty.le s t1 t2 = true) (hu : HasT s u t1) :
    HasT s u t2 := by
  simp only [Ty.le, Bool.or_eq_true, decide_eq_true_eq] at h
  rcases h with rfl | h
  · exact hu
  · exact hasT_sub s h hu

/-- The bytes-like interpretations of a variant node: `dynamic` is below each. -/
theorem le_dynamic_of_bytesLike {s : Bool} {t : Ty} (hs : s = true) (hb : t.isBytesLike = true) :
    Ty.le s .dynamic t = true := by
  cases t <;> simp_all [Ty.isBytesLike, Ty.le, Ty.sub]

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
    ∃ ts, k = .ty (.tuple ts (op == .Matches)) ∧ cs ≠ [] ∧
      ((isNavOp op = false ∧ exactTyAll cs = true) ∨ op = .Matches) ∧ allTy ks = some ts := by
  simp only [classifyNode] at h
  split at h
  · rename_i hc
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨ts, hts, rfl⟩ := h
    simp only [Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff, Bool.or_eq_true,
      beq_iff_eq] at hc
    exact ⟨ts, rfl, hc.1, hc.2, hts⟩
  · cases h

theorem mem_tysOf : ∀ {ks : List K} {t : Ty}, t ∈ tysOf ks → K.ty t ∈ ks
  | [], _, h => by simp [tysOf] at h
  | .ty t' :: ks, t, h => by
    simp only [tysOf, List.mem_cons] at h
    rcases h with rfl | h
    · simp
    · exact List.mem_cons_of_mem _ (mem_tysOf h)
  | .ns :: ks, t, h => List.mem_cons_of_mem _ (mem_tysOf (by simpa [tysOf] using h))
  | .zip :: ks, t, h => List.mem_cons_of_mem _ (mem_tysOf (by simpa [tysOf] using h))

theorem meetOf_spec {s : Bool} {ks : List K} {t : Ty} (h : meetOf s ks = some t) :
    K.ty t ∈ ks ∧ ∀ k, k ∈ ks → K.fits s t k = true := by
  unfold meetOf at h
  obtain ⟨hp, hm⟩ := List.find?_some h, List.mem_of_find?_eq_some h
  exact ⟨mem_tysOf hm, fun k hk => List.all_eq_true.mp hp k hk⟩

theorem node_array {s : Bool} {op : Operator} {cs : List Condition} {lb : Nat}
    {cv : Bytes} {ks : List K} {k : K} (h : classifyNode s .Array op cs lb cv ks = some k) :
    ∃ t0, k = .ty (.array t0) ∧
      ((isNavOp op = false ∧ exactTyAll cs = true) ∨ isArrayOp op = true) ∧
      ks ≠ [] ∧ (∀ k', k' ∈ ks → ∃ t', k' = .ty t' ∧ Ty.le s t0 t' = true) ∧
      ((∃ rest, ks = .ty t0 :: rest) ∨ (s = true ∧ t0 = .dynamic ∧ ∀ k', k' ∈ ks → K.bytesLikeTy k' = true)) := by
  simp only [classifyNode] at h
  split at h
  · rename_i hc
    have hc' : (isNavOp op = false ∧ exactTyAll cs = true) ∨ isArrayOp op = true := by
      simpa [Bool.or_eq_true, Bool.and_eq_true] using hc
    split at h
    · rename_i t rest
      split at h
      · rename_i hr
        simp only [Option.some.injEq] at h; subst h
        refine ⟨t, rfl, hc', by simp, ?_, .inl ⟨rest, rfl⟩⟩
        intro k' hk'
        simp only [List.mem_cons] at hk'
        rcases hk' with rfl | hk'
        · exact ⟨t, rfl, le_refl s t⟩
        · have := List.all_eq_true.mp hr k' hk'
          rcases k' with t' | _ | _ <;> simp [K.fits] at this
          exact ⟨t', rfl, this⟩
      · split at h
        · rename_i hv
          simp only [Option.some.injEq] at h; subst h
          simp only [Bool.and_eq_true] at hv
          refine ⟨.dynamic, rfl, hc', by simp, ?_, .inr ⟨hv.1, rfl, fun k' hk' => List.all_eq_true.mp hv.2 k' hk'⟩⟩
          intro k' hk'
          have := List.all_eq_true.mp hv.2 k' hk'
          rcases k' with t' | _ | _ <;> simp [K.bytesLikeTy] at this
          exact ⟨t', rfl, le_dynamic_of_bytesLike hv.1 this⟩
        · cases h
    · cases h
  · cases h

theorem node_abi {s : Bool} {op : Operator} {cs : List Condition} {lb : Nat}
    {cv : Bytes} {ks : List K} {k : K} (h : classifyNode s .AbiEncoded op cs lb cv ks = some k) :
    ∃ ts, k = .ty (.call lb ts (op == .Matches)) ∧ cs ≠ [] ∧
      (op = .Matches ∨ (op = .Pass ∧ exactTyAll cs = true)) ∧ allTy ks = some ts := by
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
    ((op = .ZipSome ∨ op = .ZipEvery) ∧ k = .zip ∧ ∃ ts o, ks = [.ty (.tuple ts o)]) ∨
    (k = .ns ∧ cs = [] ∧ isNavOp op = false) ∨
    ((op = .And ∨ op = .Or) ∧ logicalKind s ks = some k) := by
  simp only [classifyNode] at h
  split at h
  · rename_i hz
    split at h
    · rename_i ts o
      simp only [Option.some.injEq] at h
      exact .inl ⟨by simpa [Bool.or_eq_true] using hz, h.symm, ts, o, rfl⟩
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
    (then `t` is dynamic), or structural with a type of which `t` is a
    subtype. -/
theorem logicalKind_ty {s : Bool} {ks : List K} {t : Ty} (h : logicalKind s ks = some (.ty t)) :
    (∃ i, ∃ hi : i < ks.length, (∃ t0, ks[i] = .ty t0) ∧ ∀ j (hj : j < i), ks[j]'(by omega) = .ns) ∧
    (∀ k, k ∈ ks → k = .ns ∨ (k = .zip ∧ t.isStatic = false) ∨
      ∃ t', k = .ty t' ∧ Ty.le s t t' = true) ∧
    (K.ty t ∈ ks ∨ (s = true ∧ t = .dynamic ∧ ∀ k, k ∈ ks → K.bytesLikeOk k = true)) := by
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
            have hmem : K.ty t1 ∈ ks ∨ (s = true ∧ t1 = .dynamic ∧ ∀ k, k ∈ ks → K.bytesLikeOk k = true) := by
              split at hlt
              · rename_i tm hm
                simp only [Option.some.injEq] at hlt; subst hlt
                exact .inl (meetOf_spec hm).1
              · split at hlt
                · rename_i hall
                  simp only [Option.some.injEq] at hlt; subst hlt
                  simp only [Bool.and_eq_true] at hall
                  exact .inr ⟨hall.1, rfl, fun k hk => List.all_eq_true.mp hall.2 k hk⟩
                · cases hlt
            refine ⟨⟨i, hi, ⟨t0, hk⟩, hb⟩, ?_, hmem⟩
            intro k hk
            rcases k with t' | _ | _
            · refine .inr (.inr ⟨t', rfl, ?_⟩)
              split at hlt
              · rename_i tm hm
                simp only [Option.some.injEq] at hlt; subst hlt
                simpa [K.fits] using (meetOf_spec hm).2 _ hk
              · split at hlt
                · rename_i hall
                  simp only [Option.some.injEq] at hlt; subst hlt
                  simp only [Bool.and_eq_true] at hall
                  have := List.all_eq_true.mp hall.2 _ hk
                  exact le_dynamic_of_bytesLike hall.1 (by simpa [K.bytesLikeOk] using this)
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
    (he : c.encoding = .Tuple) : ∃ vs, u = .tuple vs ∧ c.children.length ≤ vs.length ∧
      DescAll s c.children (vs.take c.children.length) ∧
      (c.children.length < vs.length → isInlined c = false ∧ c.operator = .Matches) := by
  cases hD with
  | tuple _ _ hk hall hpre _ => exact ⟨_, rfl, hk, hall, hpre⟩
  | _ => simp_all

theorem Desc.array_inv {s : Bool} {c : Condition} {u : Val} (hD : Desc s c u)
    (he : c.encoding = .Array) :
    ∃ vs c0 cs, u = .array vs ∧ c.children = c0 :: cs ∧ ∀ v, v ∈ vs → DescS s c0 v := by
  cases hD with
  | array c0 cs _ hch h0 _ _ _ => exact ⟨_, c0, cs, rfl, hch, h0⟩
  | _ => simp_all

theorem Desc.call_inv {s : Bool} {c : Condition} {u : Val} (hD : Desc s c u)
    (he : c.encoding = .AbiEncoded) :
    ∃ pre args, u = .call pre args ∧ c.leadingBytes = pre.length ∧
      c.children.length ≤ args.length ∧ DescAll s c.children (args.take c.children.length) ∧
      (c.operator = .Matches ∨
        (c.operator = .Pass ∧ c.children.length = args.length ∧ exactTyAll c.children = true)) := by
  cases hD with
  | call _ hlb _ hk hall hop => exact ⟨_, _, rfl, hlb, hk, hall, hop⟩
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
    rcases node_none hn with ⟨hop, _, ts, o, rfl⟩ | ⟨hk, _⟩ | ⟨_, hl⟩
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
    · obtain ⟨_, hall, _⟩ := logicalKind_ty hl
      obtain ⟨k, hk, hck⟩ := classifyAll_mem s hks hm
      rcases hall k hk with rfl | ⟨rfl, _⟩ | ⟨t', rfl, ht'⟩
      · exact (NonStruct.not_bytesLike (ns_sound s ch0 hck) hb0).elim
      · exact (ZipNode.not_bytesLike (zip_sound s ch0 hck) hb0).elim
      · have := bytesLike_ty s ch0 hck hb0
        simp only [Ty.le, Bool.or_eq_true, decide_eq_true_eq] at ht'
        rcases ht' with rfl | ht'
        · exact this
        · cases t <;> cases t' <;> simp_all [Ty.sub, Ty.isBytesLike]
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
    obtain ⟨⟨i, hi, ⟨t0, hk0⟩, hpre⟩, hall, _⟩ := logicalKind_ty hl
    have hi' : i < c.children.length := by omega
    have hstruct : ∀ ch, ch ∈ c.children → ∀ t', classify s ch = some (.ty t') →
        Ty.le s t t' = true → DescS s ch u :=
      fun ch hm t' hck ht' => (ih ch hm hck (hasT_le ht' hu)).1
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
    simp only [List.length_map] at hlen
    obtain ⟨vs, rfl, hvs⟩ : ∃ vs, u = .tuple vs ∧
        (if (c.operator == .Matches) = true then
          HasTPre s vs ts ∧ (ts.length < vs.length → Ty.allStatic ts = false)
         else HasTAll s vs ts) := by
      cases u with
      | tuple vs =>
        simp only [HasT] at hu
        obtain ⟨ts', o', h', hall⟩ := hu
        cases h'; exact ⟨vs, rfl, hall⟩
      | _ => simp [HasT] at hu
    have hpre : HasTPre s vs ts := by
      split at hvs
      · exact hvs.1
      · exact hasTPre_of_all hvs
    obtain ⟨hl2, hg2⟩ := hasTPre_get s hpre
    have hk : c.children.length ≤ vs.length := by omega
    have hall : DescAll s c.children (vs.take c.children.length) :=
      descAll_of_get (by simp; omega) fun i h1 h2 => by
        have hc := hget i h1 (by simp; omega)
        simp only [List.getElem_map] at hc
        simp only [List.getElem_take]
        exact (ih _ (List.getElem_mem h1) hc (hg2 i (by simp at h2; omega) (by omega))).1
    have hlong : c.children.length < vs.length →
        isInlined c = false ∧ c.operator = .Matches := by
      intro hlt
      split at hvs
      · rename_i hm
        refine ⟨?_, by simpa using hm⟩
        have hst := hvs.2 (by omega)
        have hm' := (DescAll.meta hall).1
        rw [isInlined_eq, he]
        simp only [reduceCtorEq, or_self, ite_false]
        rw [hm', ← hlen, hasTAll_allStatic s (hasTPre_take hpre), hst]
      · have := (hasTAll_get s hvs).1; omega
    have D : Desc s c (.tuple vs) := .tuple he hne hk hall hlong hop
    exact ⟨.desc D, fun _ => D⟩
  case Array =>
    obtain ⟨t0, hk, hop, hne, hallk, _⟩ := node_array hn
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
      obtain ⟨t', rfl, ht'⟩ := hallk k hk
      exact (ih ch hm hck (hasT_le ht' (hev v hv))).1
    obtain ⟨c0, cs, hcs⟩ : ∃ c0 cs, c.children = c0 :: cs := by
      cases hc : c.children with
      | nil => rw [hc] at hlen; exact absurd (List.eq_nil_of_length_eq_zero hlen) hne
      | cons c0 cs => exact ⟨c0, cs, rfl⟩
    have hm0 : c0 ∈ c.children := by rw [hcs]; simp
    have hop' : (isNavOp c.operator = false ∧ exactTyAll c.children = true) ∨
        c.operator = .Matches ∨ c.operator = .ArraySome ∨
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
    have strict : Strict s u (.call c.leadingBytes ts (c.operator == .Matches)) → Desc s c u := by
      intro hS
      simp only [Strict] at hS
      obtain ⟨pre, args, rfl, hpre, hargs⟩ := hS
      have hp : HasTPre s args ts := by
        split at hargs
        · exact hargs
        · exact hasTPre_of_all hargs
      obtain ⟨hl2, hg2⟩ := hasTPre_get s hp
      have hall : DescAll s c.children (args.take c.children.length) :=
        descAll_of_get (by simp; omega) fun i h1 h2 => by
          have hc := hget i h1 (by simp; omega)
          simp only [List.getElem_map] at hc
          simp only [List.getElem_take]
          exact (ih _ (List.getElem_mem h1) hc (hg2 i (by simp at h2; omega) (by omega))).1
      have hop' : c.operator = .Matches ∨
          (c.operator = .Pass ∧ c.children.length = args.length ∧ exactTyAll c.children = true) := by
        rcases hop with h | ⟨h, hn'⟩
        · exact .inl h
        · refine .inr ⟨h, ?_, hn'⟩
          rw [h] at hargs
          simp only [beq_iff_eq, reduceCtorEq, decide_false, Bool.false_eq_true, ite_false] at hargs
          have := (hasTAll_get s hargs).1; omega
      exact .call he hpre.symm hne (by omega) hall hop'
    refine ⟨?_, strict⟩
    by_cases hS : Strict s u (.call c.leadingBytes ts (c.operator == .Matches))
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
          rcases hu with h | ⟨lb, ts', o', h, h2 | hs⟩
          · cases h
          · cases h; exact absurd ⟨pre, args, rfl, h2.1, h2.2⟩ hS
          · exact hs
        | _ => simp [HasT] at hu
      exact .stray hs (.abi he) (isBytesLike_of_hasT hu rfl)
  case EtherValue => cases (node_ether hn).1
termination_by sizeOf c
decreasing_by exact sizeOf_child hm

/-! ## Described values are typed -/

theorem NonStruct.classify {s : Bool} : ∀ {c : Condition} {k : K}, NonStruct c →
    classify s c = some k → k = .ns
  | c, k, .leaf he hch hnav, h => by
    rw [classify_eq, hch] at h
    simp only [classifyAll, Option.bind_some] at h
    rcases he with he | he <;> rw [he] at h
    · rcases node_none h with ⟨hop, _, _, _, hks⟩ | ⟨hk, _⟩ | ⟨hop, hl⟩
      · cases hks
      · exact hk
      · unfold logicalKind at hl; simp at hl
    · exact (node_ether h).1
  | c, k, .logical he hop hall, h => by
    rw [classify_eq, he] at h
    obtain ⟨ks, hks, hn⟩ := Option.bind_eq_some_iff.mp h
    have hns : ∀ k', k' ∈ ks → k' = .ns := by
      intro k' hk'
      obtain ⟨hl, hg⟩ := classifyAll_get s hks
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hk'
      exact NonStruct.classify (hall _ (List.getElem_mem (by omega))) (hg i (by omega) hi)
    rcases node_none hn with ⟨hz, _⟩ | ⟨hk, _⟩ | ⟨_, hl⟩
    · rcases hop with h | h <;> rw [h] at hz <;> simp at hz
    · exact hk
    · unfold logicalKind at hl
      split at hl
      · cases hl
      · split at hl
        · simpa using hl.symm
        · rename_i hnot
          exact absurd (List.all_eq_true.mpr fun k' hk' => by simp [hns k' hk']) hnot
termination_by c => sizeOf c
decreasing_by
  all_goals first
    | (simp_wf; have := sizeOf_child (List.getElem_mem (by omega)); omega)
    | (exact sizeOf_child (List.getElem_mem _))

theorem ZipNode.classify {s : Bool} {c : Condition} {k : K} (hz : ZipNode c)
    (h : classify s c = some k) : k = .zip := by
  obtain ⟨t, he, hop, hch⟩ := hz
  rw [classify_eq, he] at h
  obtain ⟨ks, hks, hn⟩ := Option.bind_eq_some_iff.mp h
  rcases node_none hn with ⟨_, hk, _⟩ | ⟨_, hcs, _⟩ | ⟨hop', _⟩
  · exact hk
  · rw [hch] at hcs; cases hcs
  · rcases hop with h | h <;> rcases hop' with h' | h' <;> rw [h] at h' <;> cases h'

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
    obtain ⟨_, hall, hmem⟩ := logicalKind_ty hl
    obtain ⟨_, ch0, hm, h0⟩ := Desc.none_inv hD (.inl he)
    obtain ⟨hop, _, _, _, hchs, _⟩ : (c.operator = .And ∨ c.operator = .Or) ∧ ∃ ch0, ch0 ∈ c.children ∧
        DescS s ch0 u ∧ (∀ ch, ch ∈ c.children → DescSN s ch u) ∧ True := by
      cases hD with
      | logical ch0 _ hop hm h0 hall _ => exact ⟨hop, ch0, hm, h0, hall, trivial⟩
      | _ => simp_all
    rcases hmem with hmt | ⟨hs, rfl, hbl⟩
    · -- the branch of the most specific type describes the value too
      obtain ⟨i, hi, hki⟩ := List.getElem_of_mem hmt
      have hci := hget i (by omega) hi
      rw [hki] at hci
      have hmi : c.children[i]'(by omega) ∈ c.children := List.getElem_mem _
      cases hchs _ hmi with
      | ds h => exact ih _ hmi hci h
      | ns h => cases NonStruct.classify h hci
      | zip h _ => cases ZipNode.classify h hci
    · obtain ⟨k, hk, hck⟩ := classifyAll_mem s hks hm
      rcases hall k hk with rfl | ⟨rfl, _⟩ | ⟨t', rfl, ht'⟩
      · exact (NonStruct.not_descS (ns_sound s ch0 hck) h0).elim
      · exact (ZipNode.not_descS (zip_sound s ch0 hck) h0).elim
      · have := ih ch0 hm hck h0
        exact hasT_dynamic (isBytesLike_of_hasT this (by simpa [K.bytesLikeOk] using hbl _ hk))
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
    obtain ⟨vs, rfl, hkv, hall, hlong⟩ := Desc.tuple_inv hD he
    have hl := DescAll.length_eq hall
    simp only [List.length_take] at hl
    have htl : (vs.take c.children.length).length = c.children.length := by simp; omega
    have htake : HasTAll s (vs.take c.children.length) ts :=
      hasTAll_of_get s (by omega) fun i h1 h2 => by
        have hi : i < c.children.length := by omega
        have hc := hget i hi (by simp; omega)
        simp only [List.getElem_map] at hc
        exact ih _ (List.getElem_mem _) hc (DescAll.get hall i hi)
    have hpre : HasTPre s vs ts := hasTPre_of_get s (by omega) fun i h1 h2 => by
      have := (hasTAll_get s htake).2 i (by simp; omega) h2
      simpa [List.getElem_take] using this
    simp only [HasT]
    refine ⟨ts, _, rfl, ?_⟩
    split
    · refine ⟨hpre, fun hlt => ?_⟩
      have hi := (hlong (by omega)).1
      have hm' := (DescAll.meta hall).1
      rw [isInlined_eq, he] at hi
      simp only [reduceCtorEq, or_self, ite_false] at hi
      rw [← hasTAll_allStatic s htake, ← hm', hi]
    · rename_i hnm
      by_cases hlt : c.children.length < vs.length
      · exact absurd (by simpa using (hlong hlt).2) hnm
      · exact hasTAll_of_pre hpre (by omega)
  case Array =>
    obtain ⟨t0, hk, _, _, hallk, hfirst⟩ := node_array hn
    simp only [K.ty.injEq] at hk; subst hk
    obtain ⟨vs, c0, cs, rfl, hcs, h0⟩ := Desc.array_inv hD he
    have hm0 : c0 ∈ c.children := by rw [hcs]; simp
    obtain ⟨k, hk, hck⟩ := classifyAll_mem s hks hm0
    simp only [HasT]
    refine ⟨t0, rfl, (hasTEach_iff s t0).mpr fun v hv => ?_⟩
    rcases hfirst with ⟨rest, rfl⟩ | ⟨hs, rfl, hbl⟩
    · -- the template has the array's element type
      have hc0 := hget 0 (by rw [hcs]; simp) (by simp)
      simp only [List.getElem_cons_zero] at hc0
      have : c.children[0]'(by rw [hcs]; simp) = c0 := by simp [hcs]
      rw [this] at hc0
      exact ih c0 hm0 hc0 (h0 v hv)
    · obtain ⟨t', rfl, _⟩ := hallk k hk
      have := ih c0 hm0 hck (h0 v hv)
      exact hasT_dynamic (isBytesLike_of_hasT this (by simpa [K.bytesLikeTy] using hbl _ hk))
  case AbiEncoded =>
    obtain ⟨ts, hk, _, _, hts⟩ := node_abi hn
    simp only [K.ty.injEq] at hk; subst hk
    have hks' := allTy_eq hts; subst hks'
    simp only [List.length_map] at hlen
    obtain ⟨pre, args, rfl, hlb, hka, hall, hop⟩ := Desc.call_inv hD he
    have hl := DescAll.length_eq hall
    simp only [List.length_take] at hl
    have htl : (args.take c.children.length).length = c.children.length := by simp; omega
    have htake : HasTAll s (args.take c.children.length) ts :=
      hasTAll_of_get s (by omega) fun i h1 h2 => by
        have hi : i < c.children.length := by omega
        have hc := hget i hi (by simp; omega)
        simp only [List.getElem_map] at hc
        exact ih _ (List.getElem_mem _) hc (DescAll.get hall i hi)
    have hpre : HasTPre s args ts := hasTPre_of_get s (by omega) fun i h1 h2 => by
      have := (hasTAll_get s htake).2 i (by simp; omega) h2
      simpa [List.getElem_take] using this
    simp only [HasT]
    refine .inr ⟨c.leadingBytes, ts, _, rfl, .inl ⟨hlb.symm, ?_⟩⟩
    split
    · exact hpre
    · rename_i hnm
      rcases hop with h | ⟨_, hel, _⟩
      · exact absurd (by simp [h]) hnm
      · exact hasTAll_of_pre hpre (by omega)
  case EtherValue => cases (node_ether hn).1
termination_by sizeOf c
decreasing_by exact sizeOf_child hm

/-! ## Zips -/

theorem hasT_compat {s : Bool} {t1 t2 : Ty} {v : Val} (hc : tyCompat s t1 t2 = true)
    (h : HasT s v t1) : HasT s v t2 := hasT_le hc h

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
    obtain ⟨vs', c0, cs, hvs, hch, h0⟩ := Desc.array_inv hD henc
    cases hvs
    rw [hch] at h1
    exact (desc_of_ty s _ h2 (hasT_compat hm (hasT_of_descS s c0 h1 (h0 v hv)))).1
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

/-- The same for a root of type `call lb ts o` (an `AbiEncoded` root, or an
    `And`/`Or` of such): every calldata with `lb` leading bytes and arguments
    of types `ts`, followed by more arguments if the type is open (a
    `Matches` root, whose trailing `Pass` children were pruned). -/
theorem checkCondition_call {s : Bool} {root : Condition} {lb : Nat} {ts : List Ty} {o : Bool}
    (h : checkCondition s root = some (.call lb ts o)) {pre : Bytes} {args : List Val}
    (hpre : pre.length = lb) (hargs : if o then HasTPre s args ts else HasTAll s args ts) :
    RootOK root ∧ ZipOK s root ∧ Desc s root (.call pre args) := by
  obtain ⟨hr, hz, hd⟩ := checkCondition_sound h
  exact ⟨hr, hz, hd pre args (.inr ⟨lb, ts, o, rfl, .inl ⟨hpre, hargs⟩⟩) ⟨pre, args, rfl, hpre, hargs⟩⟩

/-- With exactly the arguments typed, for any root of type `call lb ts o`. -/
theorem checkCondition_call_all {s : Bool} {root : Condition} {lb : Nat} {ts : List Ty} {o : Bool}
    (h : checkCondition s root = some (.call lb ts o)) {pre : Bytes} {args : List Val}
    (hpre : pre.length = lb) (hargs : HasTAll s args ts) :
    RootOK root ∧ ZipOK s root ∧ Desc s root (.call pre args) :=
  checkCondition_call h hpre (by cases o <;> simp [hargs, hasTPre_of_all hargs])

/-- **End to end**, for the comparison operands (`decoder_input`): on a tree
    the check accepts, for every well-typed calldata, every visited node that
    reads `__input` reads the spec encoding of its value (or a window of it,
    below a `Slice`, or the ether value), unless it sits in an interpretation
    that does not hold (only with `s = true`). -/
theorem checked_input {s : Bool} {root : Condition} {lb : Nat} {ts : List Ty} {o : Bool}
    (h : checkCondition s root = some (.call lb ts o)) {pre : Bytes} {args : List Val}
    (hpre : pre.length = lb) (hargs : if o then HasTPre s args ts else HasTAll s args ts)
    (suffix : Bytes)
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
