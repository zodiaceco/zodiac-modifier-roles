import Bridge.ReadAdequacy
import ConditionCheck.Sound

/-!
# A node's layout follows from its SDK-check type

`classify_lay`: if the SDK check types node `r` as `t`, then `r` is inlined
exactly when `t` is static, and then its inline size is `layS t` (32 per
word). In particular nodes of one type have one layout: the merge rule of
`pushDownOr` (`sameType`) only puts children of one layout under the `Or` it
builds.
-/

namespace Bridge
open DecoderFaithfulness DecoderFaithfulness.Roles ConditionCheck

mutual
  /-- The inline size of a static type. -/
  def layS : Ty → Nat
    | .static => 32
    | .tuple ts _ => laySAll ts
    | _ => 0
  def laySAll : List Ty → Nat
    | [] => 0
    | t :: ts => layS t + laySAll ts
end

theorem allStatic_eq : ∀ ts : List Ty, Ty.allStatic ts = ts.all Ty.isStatic
  | [] => rfl
  | t :: ts => by simp [Ty.allStatic, allStatic_eq ts]

mutual
/-- A supertype of a static type is static, of the same size. -/
theorem le_static : ∀ (s : Bool) (a b : Ty), Ty.le s a b = true → a.isStatic = true →
    b.isStatic = true ∧ layS b = layS a
  | s, a, b, h, ha => by
    unfold Ty.le at h
    rcases Bool.or_eq_true _ _ ▸ h with h | h
    · simp only [decide_eq_true_eq] at h; subst h; exact ⟨ha, rfl⟩
    · exact sub_static s a b h ha
termination_by s a b => (sizeOf a + sizeOf b, 2)

theorem sub_static : ∀ (s : Bool) (a b : Ty), Ty.sub s a b = true → a.isStatic = true →
    b.isStatic = true ∧ layS b = layS a
  | s, .static, .static, _, _ => ⟨rfl, rfl⟩
  | s, .tuple ts1 o1, .tuple ts2 o2, h, ha => by
    simp only [Ty.isStatic] at ha
    unfold Ty.sub at h
    split at h
    · simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, Bool.not_eq_true',
        Bool.or_eq_false_iff, decide_eq_false_iff_not] at h
      obtain ⟨⟨hl, hsp⟩, hc⟩ := h
      have := subPre_static s ts1 ts2 hsp ha
      rcases hc with ⟨hlt, ho⟩ | hns
      · refine ⟨this.1, ?_⟩
        simp only [layS]; exact this.2 (by omega)
      · rw [this.1] at hns; cases hns
    · simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at h
      obtain ⟨⟨_, hl⟩, hsp⟩ := h
      have := subPre_static s ts1 ts2 hsp ha
      exact ⟨this.1, by simp only [layS]; exact this.2 hl⟩
  | s, .static, .dynamic, h, _ | s, .static, .tuple _ _, h, _ | s, .static, .array _, h, _
  | s, .static, .call _ _ _, h, _ => by simp [Ty.sub] at h
  | s, .tuple _ _, .static, h, _ | s, .tuple _ _, .dynamic, h, _ | s, .tuple _ _, .array _, h, _
  | s, .tuple _ _, .call _ _ _, h, _ => by simp [Ty.sub] at h
  | s, .dynamic, _, _, ha | s, .array _, _, _, ha | s, .call _ _ _, _, _, ha => by
    simp [Ty.isStatic] at ha
termination_by s a b => (sizeOf a + sizeOf b, 1)

theorem subPre_static : ∀ (s : Bool) (ts1 ts2 : List Ty), Ty.subPre s ts1 ts2 = true →
    Ty.allStatic ts1 = true →
    Ty.allStatic ts2 = true ∧ (ts1.length = ts2.length → laySAll ts2 = laySAll ts1)
  | _, _, [], _, _ => ⟨rfl, fun h => by
      cases ‹List Ty› with
      | nil => rfl
      | cons _ _ => simp at h⟩
  | s, t1 :: ts1, t2 :: ts2, h, ha => by
    simp only [Ty.subPre, Bool.and_eq_true] at h
    simp only [Ty.allStatic, Bool.and_eq_true] at ha
    have h1 := le_static s t1 t2 h.1 ha.1
    have h2 := subPre_static s ts1 ts2 h.2 ha.2
    refine ⟨by simp [Ty.allStatic, h1.1, h2.1], fun hl => ?_⟩
    simp only [laySAll, h1.2, h2.2 (by simpa using hl)]
  | _, [], _ :: _, h, _ => by simp [Ty.subPre] at h
termination_by s ts1 ts2 => (sizeOf ts1 + sizeOf ts2, 0)
end

/-! ## The layout of a classified node -/

/-- What a node's kind says of its layout: a typed node is inlined exactly
    when its type is static, then with the type's (positive) size; a node
    that reads no parameter is inlined with size 0. -/
def KLay (r : Condition) : K → Prop
  | .ty t => isInlined r = t.isStatic ∧ (t.isStatic = true → inlinedSize r = layS t ∧ 0 < layS t)
  | .ns => isInlined r = true ∧ inlinedSize r = 0
  | .zip => True

theorem loop_false_sum : ∀ (cs : List Condition) (ts : List Ty),
    cs.length = ts.length → (∀ i (h1 : i < cs.length) (h2 : i < ts.length), KLay cs[i] (.ty ts[i])) →
    Ty.allStatic ts = true → inlinedSizeLoop false cs = laySAll ts ∧ (cs ≠ [] → 0 < laySAll ts)
  | [], [], _, _, _ => ⟨rfl, fun h => absurd rfl h⟩
  | c :: cs, t :: ts, hl, hk, ha => by
    simp only [Ty.allStatic, Bool.and_eq_true] at ha
    have h0 := hk 0 (by simp) (by simp)
    simp only [List.getElem_cons_zero, KLay] at h0
    have ih := loop_false_sum cs ts (by simpa using hl)
      (fun i h1 h2 => by
        have := hk (i + 1) (by simp; omega) (by simp; omega)
        simp only [List.getElem_cons_succ] at this; exact this) ha.2
    have hs := (h0.2 ha.1)
    refine ⟨?_, fun _ => ?_⟩
    · simp only [inlinedSizeLoop, Bool.false_eq_true, false_and, ite_false, laySAll, hs.1, ih.1]
    · simp only [laySAll]; omega
  | [], _ :: _, hl, _, _ => by simp at hl
  | _ :: _, [], hl, _, _ => by simp at hl

/-- `None`: the first child with a size. Children of size 0 are skipped;
    if every sized child has size `L > 0`, the result is `L` (or 0 if none). -/
theorem loop_true_first (L : Nat) (hL : 0 < L) : ∀ (cs : List Condition),
    (∀ c ∈ cs, inlinedSize c = 0 ∨ inlinedSize c = L) →
    inlinedSizeLoop true cs = if cs.any (fun c => inlinedSize c == L) then L else 0
  | [], _ => by simp [inlinedSizeLoop]
  | c :: cs, h => by
    have ih := loop_true_first L hL cs fun x hx => h x (by simp [hx])
    simp only [inlinedSizeLoop, List.any_cons]
    rcases h c (by simp) with h0 | h0
    · simp only [h0, gt_iff_lt, Nat.lt_irrefl, and_false, ite_false, Nat.zero_add, ih]
      have : (0 == L) = false := by simp; omega
      simp [this]
    · simp [h0, hL]

theorem isInlinedAll_true : ∀ (cs : List Condition), (∀ c ∈ cs, isInlined c = true) →
    isInlinedAll cs = true
  | [], _ => rfl
  | c :: cs, h => by
    simp only [isInlinedAll, h c (by simp), Bool.true_and]
    exact isInlinedAll_true cs fun x hx => h x (by simp [hx])

theorem isInlinedAll_false {cs : List Condition} {c : Condition} (hc : c ∈ cs) (h : isInlined c = false) :
    isInlinedAll cs = false := by
  rw [isInlinedAll_eq, List.all_eq_false]; exact ⟨c, hc, by simp [h]⟩

theorem tysOf_mem : ∀ {ks : List K} {t : Ty}, t ∈ tysOf ks → K.ty t ∈ ks
  | [], _, h => by simp [tysOf] at h
  | .ty t' :: ks, t, h => by
    simp only [tysOf, List.mem_cons] at h
    rcases h with rfl | h
    · simp
    · exact List.mem_cons_of_mem _ (tysOf_mem h)
  | .ns :: ks, t, h => by simp only [tysOf] at h; exact List.mem_cons_of_mem _ (tysOf_mem h)
  | .zip :: ks, t, h => by simp only [tysOf] at h; exact List.mem_cons_of_mem _ (tysOf_mem h)

theorem firstTy_mem : ∀ {ks : List K} {t : Ty}, firstTy ks = some t → K.ty t ∈ ks
  | [], _, h => by simp [firstTy] at h
  | .ty t' :: ks, t, h => by simp only [firstTy, Option.some.injEq] at h; subst h; simp
  | .ns :: ks, t, h => by simp only [firstTy] at h; exact List.mem_cons_of_mem _ (firstTy_mem h)
  | .zip :: ks, t, h => by simp [firstTy] at h

/-- **The layout of a classified node.** -/
theorem classify_lay (s : Bool) : ∀ (r : Condition) (k : K), classify s r = some k → KLay r k
  | r, k, h => by
    rw [classify_eq] at h
    obtain ⟨ks, hks, hnode⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨hlen, hget⟩ := classifyAll_get s hks
    have hch : ∀ i (h1 : i < r.children.length) (h2 : i < ks.length), KLay r.children[i] ks[i] :=
      fun i h1 h2 => classify_lay s _ _ (hget i h1 h2)
    have hmem : ∀ c ∈ r.children, ∃ k ∈ ks, KLay c k := by
      intro c hc
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hc
      exact ⟨ks[i]'(by omega), List.getElem_mem _, hch i hi (by omega)⟩
    have hmem' : ∀ k ∈ ks, ∃ c ∈ r.children, KLay c k := by
      intro k hk
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hk
      exact ⟨r.children[i]'(by omega), List.getElem_mem _, hch i (by omega) hi⟩
    rcases r with ⟨e, op, cs, inl, sz, lb, cv⟩
    simp only at hch hmem hmem' hlen hks hnode ⊢
    unfold classifyNode at hnode
    cases e with
    | Static =>
      simp only [Option.ite_none_right_eq_some, Option.some.injEq] at hnode
      obtain ⟨hc, rfl⟩ := hnode
      unfold KLay; rw [isInlined_eq, inlinedSize_eq]
      simp only [Ty.isStatic, reduceCtorEq, false_or, or_self, ite_false, ite_true, layS, true_implies, and_true]
      refine ⟨?_, by decide⟩
      rcases Bool.or_eq_true _ _ ▸ hc with hc | hc
      · simp only [leafOk, Bool.and_eq_true, List.isEmpty_iff] at hc; rw [hc.1]; rfl
      · simp only [sliceOk, Bool.and_eq_true, beq_iff_eq] at hc
        obtain ⟨⟨⟨⟨_, _⟩, hen⟩, _⟩, hk⟩ := hc
        obtain ⟨w, rfl⟩ : ∃ w, cs = [w] := by
          cases cs with
          | nil => simp at hen
          | cons w ws => cases ws with
            | nil => exact ⟨w, rfl⟩
            | cons _ _ => simp at hen
        subst hk
        have := hch 0 (by simp) (by simp)
        simp only [List.getElem_cons_zero, KLay, Ty.isStatic] at this
        simp [isInlinedAll, this.1]
    | Dynamic =>
      simp only [Option.ite_none_right_eq_some, Option.some.injEq] at hnode
      obtain ⟨_, rfl⟩ := hnode
      unfold KLay; rw [isInlined_eq]; simp [Ty.isStatic]
    | Tuple =>
      simp only [Option.ite_none_right_eq_some, Option.map_eq_some_iff] at hnode
      obtain ⟨hc, ts, hts, rfl⟩ := hnode
      have hks' := allTy_eq hts
      subst hks'
      simp only [List.length_map] at hlen
      have hct : ∀ i (h1 : i < cs.length) (h2 : i < ts.length), KLay cs[i] (.ty ts[i]) :=
        fun i h1 h2 => by
          have := hch i h1 (by simpa using h2)
          rw [List.getElem_map] at this; exact this
      have hinl : isInlinedAll cs = Ty.allStatic ts := by
        rw [isInlinedAll_eq, allStatic_eq]
        apply Bool.eq_iff_iff.2
        simp only [List.all_eq_true]
        constructor
        · intro h t ht
          obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ht
          have := (hct i (by omega) hi).1
          rw [← this]; exact h _ (List.getElem_mem _)
        · intro h c hc
          obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hc
          have := (hct i hi (by omega)).1
          rw [this]; exact h _ (List.getElem_mem _)
      unfold KLay; rw [isInlined_eq, inlinedSize_eq]
      simp only [Ty.isStatic, reduceCtorEq, or_self, ite_false, hinl, layS, true_and]
      intro ha
      have := loop_false_sum cs ts hlen.symm hct ha
      refine ⟨this.1, this.2 ?_⟩
      simp only [Bool.not_eq_true', Bool.and_eq_true, List.isEmpty_eq_false_iff] at hc
      exact hc.1
    | Array =>
      dsimp only at hnode
      repeat' split at hnode
      all_goals first
        | (simp only [Option.some.injEq] at hnode; subst hnode; unfold KLay; rw [isInlined_eq]; simp [Ty.isStatic])
        | simp at hnode
    | AbiEncoded =>
      simp only [Option.ite_none_right_eq_some, Option.map_eq_some_iff] at hnode
      obtain ⟨_, ts, _, rfl⟩ := hnode
      unfold KLay; rw [isInlined_eq]; simp [Ty.isStatic]
    | None =>
      have hmk : ∀ k, KLay ⟨.None, op, cs, inl, sz, lb, cv⟩ k ↔ match k with
          | .ty t => isInlinedAll cs = t.isStatic ∧
              (t.isStatic = true → inlinedSizeLoop true cs = layS t ∧ 0 < layS t)
          | .ns => isInlinedAll cs = true ∧ inlinedSizeLoop true cs = 0
          | .zip => True := by
        intro k; cases k <;> simp [KLay, isInlined_eq, inlinedSize_eq]
      rw [hmk]
      dsimp only at hnode
      split at hnode
      · -- a Zip
        split at hnode <;> first | (simp only [Option.some.injEq] at hnode; subst hnode; trivial) | simp at hnode
      split at hnode
      · simp only [Option.some.injEq] at hnode; subst hnode
        rename_i hl
        simp only [leafOk, Bool.and_eq_true, List.isEmpty_iff] at hl
        simp only [hl.1]; exact ⟨rfl, rfl⟩
      split at hnode
      · rename_i hlog
        unfold logicalKind at hnode
        split at hnode
        · simp at hnode
        split at hnode
        · -- every child reads no parameter
          rename_i hns
          simp only [Option.some.injEq] at hnode; subst hnode
          have hall : ∀ c ∈ cs, isInlined c = true ∧ inlinedSize c = 0 := by
            intro c hc
            obtain ⟨k, hk, hkl⟩ := hmem c hc
            have : k = .ns := by
              have := List.all_eq_true.1 hns k hk; simpa using this
            subst this; exact hkl
          refine ⟨isInlinedAll_true cs fun c hc => (hall c hc).1, ?_⟩
          rw [loop_true_first 1 (by decide) cs (fun c hc => Or.inl (hall c hc).2)]
          simp [List.any_eq_true, (fun c hc => (hall c hc).2)]
          intro c hc; simp [(hall c hc).2]
        · split at hnode
          · simp at hnode
          rename_i t hlt
          split at hnode
          · simp at hnode
          rename_i hzs
          simp only [Option.some.injEq] at hnode; subst hnode
          simp only
          unfold logicalTy at hlt
          split at hlt
          · simp at hlt
          rename_i t0 hft
          split at hlt
          · -- the most specific type
            rename_i t1 hmeet
            simp only [Option.some.injEq] at hlt; subst hlt
            unfold meetOf at hmeet
            have ht1 := List.find?_some hmeet
            have hfits : ∀ k ∈ ks, K.fits s t1 k = true := by simpa using ht1
            have ht1m := tysOf_mem (List.mem_of_find?_eq_some hmeet)
            by_cases hst : t1.isStatic = true
            · have hnz : K.zip ∉ ks := by
                intro hz; apply hzs; simp [hst, List.contains_iff_mem]; exact hz
              have hcl : ∀ c ∈ cs, (isInlined c = true ∧ inlinedSize c = layS t1) ∨
                  (isInlined c = true ∧ inlinedSize c = 0) := by
                intro c hc
                obtain ⟨k, hk, hkl⟩ := hmem c hc
                cases k with
                | ty t' =>
                  have hle := hfits _ hk
                  simp only [K.fits] at hle
                  obtain ⟨hs', hsz⟩ := le_static s t1 t' hle hst
                  simp only [KLay] at hkl
                  left; exact ⟨by rw [hkl.1, hs'], by rw [(hkl.2 hs').1, hsz]⟩
                | ns => right; exact hkl
                | zip => exact absurd hk hnz
              obtain ⟨c1, hc1, hk1⟩ := hmem' _ ht1m
              simp only [KLay] at hk1
              have hpos := ((hk1.2 hst).2)
              refine ⟨?_, fun _ => ⟨?_, hpos⟩⟩
              · rw [hst]; exact isInlinedAll_true cs fun c hc => by rcases hcl c hc with h | h <;> exact h.1
              · rw [loop_true_first (layS t1) hpos cs (fun c hc => by
                  rcases hcl c hc with h | h
                  · exact Or.inr h.2
                  · exact Or.inl h.2)]
                have : cs.any (fun c => inlinedSize c == layS t1) = true := by
                  rw [List.any_eq_true]
                  refine ⟨c1, hc1, ?_⟩
                  rw [(hk1.2 hst).1]; simp
                simp [this]
            · simp only [Bool.not_eq_true] at hst
              obtain ⟨c1, hc1, hk1⟩ := hmem' _ ht1m
              simp only [KLay, hst] at hk1
              rw [hst]
              exact ⟨isInlinedAll_false hc1 hk1.1, fun h => by cases h⟩
          · -- interpretations of one `bytes` value
            split at hlt
            · rename_i hbl
              simp only [Option.some.injEq] at hlt; subst hlt
              simp only [Bool.and_eq_true] at hbl
              have h0 := firstTy_mem hft
              obtain ⟨c1, hc1, hk1⟩ := hmem' _ h0
              have hb := List.all_eq_true.1 hbl.2 _ h0
              have hs0 : t0.isStatic = false := by
                cases t0 <;> simp_all [K.bytesLikeOk, Ty.isBytesLike, Ty.isStatic]
              simp only [KLay, hs0] at hk1
              exact ⟨by simp [Ty.isStatic, isInlinedAll_false hc1 hk1.1], fun h => by cases h⟩
            · simp at hlt
      · simp at hnode
    | EtherValue =>
      simp only [Option.ite_none_right_eq_some, Option.some.injEq] at hnode
      obtain ⟨hl, rfl⟩ := hnode
      simp only [leafOk, Bool.and_eq_true, List.isEmpty_iff] at hl
      unfold KLay; rw [isInlined_eq, inlinedSize_eq, hl.1]; simp [isInlinedAll, inlinedSizeLoop]
termination_by r => sizeOf r
decreasing_by exact sizeOf_child (List.getElem_mem _)

/-! ## From the check's raw tree to the SDK tree -/

section
variable (avatar : Bytes)

theorem toCheckL_get : ∀ {l : List Normalize.Cond} {cs : List Condition}, Normalize.toCheckL l = some cs →
    cs.length = l.length ∧ ∀ i (h1 : i < l.length) (h2 : i < cs.length), Normalize.toCheck l[i] = some cs[i]
  | [], cs, h => by simp [Normalize.toCheckL] at h; subst h; simp
  | x :: xs, cs, h => by
    simp only [Normalize.toCheckL] at h
    split at h
    · rename_i c cs' hc hcs
      simp only [Option.some.injEq] at h; subst h
      obtain ⟨hl, hg⟩ := toCheckL_get hcs
      refine ⟨by simp [hl], fun i h1 h2 => ?_⟩
      cases i with
      | zero => simpa using hc
      | succ i => simpa using hg i (by simp at h1; omega) (by simp at h2; omega)
    · simp at h

theorem toCheck_eq {x : Normalize.Cond} {r : Condition} (h : Normalize.toCheck x = some r) :
    ∃ en op cs, ConditionPacking.encOf? x.enc = some en ∧ ConditionPacking.opOf? x.op = some op ∧
      Normalize.toCheckL x.ch = some cs ∧ r.encoding = en ∧ r.operator = op ∧ r.children = cs := by
  rcases x with ⟨e, o, cv, ch⟩
  simp only [Normalize.toCheck] at h
  split at h
  · rename_i en op cs he ho hc
    simp only [Option.some.injEq] at h; subst h
    exact ⟨en, op, cs, he, ho, hc, rfl, rfl, rfl⟩
  · simp at h

theorem encN_of {e : Nat} {en : Encoding} (h : ConditionPacking.encOf? e = some en) : encN e = en := by
  simp [encN, h]

/-- The check's raw tree has the evaluator's metadata. -/
theorem toCheck_meta : ∀ (x : Normalize.Cond) (r : Condition), Normalize.toCheck x = some r →
    isInlined r = isInlined (toRoles avatar x) ∧ inlinedSize r = inlinedSize (toRoles avatar x)
  | x, r, h => by
    obtain ⟨en, op, cs, he, _, hc, hre, _, hrc⟩ := toCheck_eq h
    obtain ⟨hl, hg⟩ := toCheckL_get hc
    have IH : ∀ i (h1 : i < x.ch.length) (h2 : i < cs.length),
        isInlined cs[i] = isInlined (toRoles avatar x.ch[i]) ∧
          inlinedSize cs[i] = inlinedSize (toRoles avatar x.ch[i]) :=
      fun i h1 h2 => toCheck_meta x.ch[i] cs[i] (hg i h1 h2)
    rw [isInlined_eq, isInlined_eq, inlinedSize_eq, inlinedSize_eq, toRoles_eq, hre, hrc]
    simp only [encN_of he]
    have hall : isInlinedAll cs = isInlinedAll (x.ch.map (toRoles avatar)) := by
      rw [isInlinedAll_eq, isInlinedAll_eq]
      apply Bool.eq_iff_iff.2
      simp only [List.all_eq_true, List.mem_map]
      constructor
      · rintro h' _ ⟨y, hy, rfl⟩
        obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hy
        rw [← (IH i hi (by omega)).1]; exact h' _ (List.getElem_mem _)
      · intro h' c hcm
        obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hcm
        rw [(IH i (by omega) hi).1]; exact h' _ ⟨_, List.getElem_mem _, rfl⟩
    refine ⟨by rw [hall], ?_⟩
    split
    · rfl
    · exact inlinedSizeLoop_congr _ _ _ (by simp [hl]) fun i h1 h2 => by
        simp only [List.getElem_map]; exact (IH i (by simpa using h2) h1).2
termination_by x => sizeOf x
decreasing_by exact Normalize.sizeOf_lt_of_mem (List.getElem_mem _)

/-- A node the check types reads a parameter. -/
theorem classify_struct (s : Bool) : ∀ (x : Normalize.Cond) (r : Condition) (t : Ty),
    Normalize.toCheck x = some r → classify s r = some (.ty t) → Normalize.isStruct x = true
  | x, r, t, h, hk => by
    obtain ⟨en, op, cs, he, ho, hc, hre, hro, hrc⟩ := toCheck_eq h
    obtain ⟨hl, hg⟩ := toCheckL_get hc
    rw [classify_eq, hre, hro, hrc] at hk
    obtain ⟨ks, hks, hnode⟩ := Option.bind_eq_some_iff.1 hk
    obtain ⟨hkl, hkg⟩ := classifyAll_get s hks
    rw [Normalize.isStruct_eq]
    by_cases hlog : (x.op == 1 || x.op == 2) = true
    · rw [if_pos hlog]
      have hop : op = .And ∨ op = .Or := by
        simp only [Bool.or_eq_true, beq_iff_eq] at hlog
        rcases hlog with h1 | h1 <;> rw [h1] at ho <;> simp [ConditionPacking.opOf?] at ho <;> simp [← ho]
      have hnav : isNavOp op = true := by rcases hop with rfl | rfl <;> rfl
      unfold classifyNode at hnode
      cases en with
      | None =>
        simp only at hnode
        have hz : (op == .ZipSome || op == .ZipEvery) = false := by rcases hop with rfl | rfl <;> rfl
        have hlf : leafOk cs op = false := by simp [leafOk, hnav]
        have hao : (op == .And || op == .Or) = true := by rcases hop with rfl | rfl <;> rfl
        rw [if_neg (by simp [hz]), if_neg (by simp [hlf]), if_pos hao] at hnode
        unfold logicalKind at hnode
        split at hnode; · simp at hnode
        split at hnode; · simp at hnode
        split at hnode; · simp at hnode
        rename_i t' hlt
        unfold logicalTy at hlt
        split at hlt; · simp at hlt
        rename_i t0 hft
        obtain ⟨i, hi, hki⟩ := List.getElem_of_mem (firstTy_mem hft)
        have hcls := hkg i (by omega) hi
        rw [hki] at hcls
        have := classify_struct s x.ch[i] cs[i] t0 (hg i (by omega) (by omega)) hcls
        rw [List.any_eq_true]; exact ⟨_, List.getElem_mem _, this⟩
      | Static | Dynamic =>
        simp only [leafOk, sliceOk, hnav, Bool.not_true, Bool.and_false, Bool.false_or] at hnode
        split at hnode
        · rename_i hsl
          simp only [Bool.and_eq_true, beq_iff_eq] at hsl
          rcases hop with rfl | rfl <;> simp at hsl
        · simp at hnode
      | Tuple =>
        simp only [hnav, Bool.not_true, Bool.false_and, Bool.false_or] at hnode
        split at hnode
        · rename_i hm; rcases hop with rfl | rfl <;> simp at hm
        · simp at hnode
      | Array =>
        simp only [hnav, Bool.not_true, Bool.false_and, Bool.false_or] at hnode
        split at hnode
        · rename_i hm; rcases hop with rfl | rfl <;> simp [isArrayOp] at hm
        · simp at hnode
      | AbiEncoded =>
        simp only at hnode
        split at hnode
        · rename_i hm; rcases hop with rfl | rfl <;> simp at hm
        · simp at hnode
      | EtherValue =>
        simp only [leafOk, hnav] at hnode
        simp at hnode
    · rw [if_neg hlog]
      have hop : op ≠ .And ∧ op ≠ .Or := by
        simp only [Bool.or_eq_true, beq_iff_eq, not_or] at hlog
        constructor <;> intro h' <;> subst h' <;> unfold ConditionPacking.opOf? at ho <;>
          split at ho <;> simp_all
      have hne : en ≠ .None ∧ en ≠ .EtherValue := by
        unfold classifyNode at hnode
        constructor <;> intro h' <;> subst h' <;> simp only at hnode
        · split at hnode
          · split at hnode <;> simp at hnode
          · split at hnode
            · simp at hnode
            · split at hnode
              · rename_i hao
                simp only [Bool.or_eq_true, beq_iff_eq] at hao
                exact (hao.elim hop.1 hop.2).elim
              · simp at hnode
        · split at hnode <;> simp at hnode
      have h0 : x.enc ≠ 0 := fun h0 => by
        rw [h0] at he; simp only [ConditionPacking.encOf?, Option.some.injEq] at he; exact hne.1 he.symm
      have h6 : x.enc ≠ 6 := fun h6 => by
        rw [h6] at he; simp only [ConditionPacking.encOf?, Option.some.injEq] at he; exact hne.2 he.symm
      simp [h0, h6]
termination_by x => sizeOf x
decreasing_by exact Normalize.sizeOf_lt_of_mem (List.getElem_mem _)


/-- **The children `pushDownOr` puts under one `Or` have one layout**: all
    read a parameter, all are inlined or none, with one size. -/
theorem sameType_lay {hs : List Normalize.Cond} (h : Normalize.sameType hs = true) :
    ∃ t : Ty, ∀ x ∈ hs, Normalize.isStruct x = true ∧ Normalize.isInl x = t.isStatic ∧
      (t.isStatic = true → rawSz avatar x = layS t ∧ 0 < layS t) := by
  unfold Normalize.sameType at h
  split at h
  · rename_i cs hc
    split at h
    · rename_i t ks hks
      obtain ⟨hl, hg⟩ := toCheckL_get hc
      obtain ⟨hkl, hkg⟩ := classifyAll_get true hks
      refine ⟨t, fun x hx => ?_⟩
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
      have hki : (K.ty t :: ks)[i]'(by simp at hkl ⊢; omega) = .ty t := by
        cases i with
        | zero => rfl
        | succ j =>
          simp only [List.getElem_cons_succ]
          have := List.all_eq_true.1 h (ks[j]'(by simp at hkl ⊢; omega)) (List.getElem_mem _)
          simpa using this
      have hcls := hkg i (by omega) (by simp at hkl ⊢; omega)
      rw [hki] at hcls
      have htc := hg i hi (by omega)
      have hlay := classify_lay true _ _ hcls
      have hm := toCheck_meta avatar _ _ htc
      simp only [KLay] at hlay
      refine ⟨classify_struct true _ _ t htc hcls, ?_, fun hs => ?_⟩
      · rw [← isInlined_toRoles, ← hm.1, hlay.1]
      · unfold rawSz; rw [← hm.2]; exact hlay.2 hs
    · simp at h
  · simp at h

end

end Bridge
