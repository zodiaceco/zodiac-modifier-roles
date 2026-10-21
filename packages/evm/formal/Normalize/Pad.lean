import Normalize.Steps

/-!
# `padToMatchTypeTree` keeps the meaning

Padding only appends `Pass` nodes, at the end of tuple and calldata children
(`World.Ok.pad`), and never to an array whose element is described: type
trees of arrays have exactly one child (`wfTT`), and `good` nodes are arrays
with children (guaranteed by `hasTT`, kept by padding).
-/

namespace Normalize

mutual
  def wfTT : TT → Bool
    | .mk e ch => (e != 4 || ch.length == 1) && wfTTL ch
  def wfTTL : List TT → Bool
    | [] => true
    | t :: ts => wfTT t && wfTTL ts
end

theorem wfTTL_eq (l : List TT) : wfTTL l = l.all wfTT := by
  induction l with
  | nil => rfl
  | cons t ts ih => simp [wfTTL, ih]

theorem wfTT_mk (e ch) : wfTT (.mk e ch) = ((e != 4 || ch.length == 1) && ch.all wfTT) := by
  rw [wfTT, wfTTL_eq]

theorem wfTT_eq (t : TT) : wfTT t = ((t.enc != 4 || t.ch.length == 1) && t.ch.all wfTT) := by
  rcases t; exact wfTT_mk ..

theorem TT.sizeOf_lt {t' t : TT} (h : t' ∈ t.ch) : sizeOf t' < sizeOf t := by
  rcases t with ⟨e, ch⟩
  simp only [TT.ch] at h
  have := List.sizeOf_lt_of_mem h
  simp only [TT.mk.sizeOf_spec]
  omega

mutual
  /-- Array nodes that check something have a structural child. -/
  def good : Cond → Bool
    | ⟨e, o, _, ch⟩ => (!(e == 4 && o != 0) || ch.any isStruct) && goodL ch
  def goodL : List Cond → Bool
    | [] => true
    | x :: xs => good x && goodL xs
end

theorem goodL_eq (l : List Cond) : goodL l = l.all good := by
  induction l with
  | nil => rfl
  | cons t ts ih => simp [goodL, ih]

theorem good_eq (c : Cond) :
    good c = ((!(c.enc == 4 && c.op != 0) || c.ch.any isStruct) && c.ch.all good) := by
  rcases c; rw [good, goodL_eq]

theorem createTTL_eq (l : List Cond) : createTTL l = l.filterMap createTT := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [createTTL, List.filterMap_cons, ih]
    split <;> simp_all

theorem createTT_mk (e o cv ch) : createTT ⟨e, o, cv, ch⟩ =
    if o == 1 || o == 2 then
      (match ch with
       | [] => none
       | x :: _ => createTT x)
    else if e == 4 then
      (match ch with
       | [] => none
       | x :: _ => (createTT x).map fun t => .mk 4 [t])
    else if e == 3 || e == 5 then some (.mk e (createTTL ch))
    else if e == 1 || e == 2 then some (.mk e [])
    else none := by
  cases ch <;> rw [createTT]

theorem createTT_wf : ∀ (c : Cond) (t : TT), createTT c = some t → wfTT t
  | ⟨e, o, cv, ch⟩, t, h => by
    rw [createTT_mk] at h
    split at h
    · split at h
      · simp at h
      · rename_i x xs
        exact createTT_wf x t h
    · split at h
      · split at h
        · simp at h
        · rename_i x xs
          cases hxe : createTT x with
          | none => simp [hxe] at h
          | some t' =>
            simp only [hxe, Option.map_some, Option.some.injEq] at h
            subst h
            simp [wfTT_mk, createTT_wf x t' hxe]
      · split at h
        · simp only [Option.some.injEq] at h
          subst h
          rw [wfTT_mk, createTTL_eq]
          rename_i hlog harr h35
          simp only [Bool.and_eq_true, List.all_eq_true, List.mem_filterMap]
          refine ⟨by first | (simp at harr; simp [harr]) | (simp at h35; simp; omega), ?_⟩
          rintro t ⟨x, hx, hxt⟩
          exact createTT_wf x t hxt
        · split at h
          · rename_i hlog harr h35 h12
            simp only [Option.some.injEq] at h
            subst h
            simp only [Bool.or_eq_true, beq_iff_eq] at h12
            simp [wfTT_mk]
            omega
          · simp at h
termination_by c => sizeOf c
decreasing_by
  all_goals simp_wf
  all_goals first
    | (subst_vars; simp only [List.cons.sizeOf_spec]; omega)
    | (have := List.sizeOf_lt_of_mem ‹_ ∈ _›; omega)

theorem createTT_struct : ∀ (c : Cond), (createTT c).isSome = true → isStruct c = true
  | ⟨e, o, cv, ch⟩, h => by
    rw [createTT_mk] at h
    rw [isStruct_mk]
    split at h
    · rename_i hl
      simp only [hl, ite_true]
      split at h
      · simp at h
      · rename_i x xs
        rw [List.any_eq_true]
        exact ⟨x, by simp, createTT_struct x h⟩
    · rename_i hl
      simp only [hl, Bool.false_eq_true, ite_false]
      split at h
      · rename_i h4; simp only [beq_iff_eq] at h4; simp [h4]
      · split at h
        · rename_i _ h35; simp only [Bool.or_eq_true, beq_iff_eq] at h35; simp; omega
        · split at h
          · rename_i _ _ h12; simp only [Bool.or_eq_true, beq_iff_eq] at h12; simp; omega
          · simp at h
termination_by c => sizeOf c
decreasing_by
  all_goals simp_wf
  all_goals first
    | (subst_vars; simp only [List.cons.sizeOf_spec]; omega)
    | (have := List.sizeOf_lt_of_mem ‹_ ∈ _›; omega)

theorem hasTT_good : ∀ c : Cond, hasTT c = true → good c = true
  | ⟨e, o, cv, ch⟩, h => by
    have hch : ∀ x ∈ ch, hasTT x = true := by
      simp only [hasTT, Bool.and_eq_true] at h
      have := h.2
      intro x hx
      clear h
      induction ch with
      | nil => simp at hx
      | cons y ys ih =>
        simp only [hasTTL, Bool.and_eq_true] at this
        rcases List.mem_cons.1 hx with rfl | hx
        · exact this.1
        · exact ih this.2 hx
    rw [good_eq]
    simp only [Bool.and_eq_true, List.all_eq_true]
    refine ⟨?_, fun x hx => hasTT_good x (hch x hx)⟩
    simp only [hasTT, Bool.and_eq_true] at h
    have h1 := h.1
    by_cases he : e = 4
    · subst he
      cases ch with
      | nil => simp at h1
      | cons x xs =>
        simp only [beq_self_eq_true, Bool.or_true, ite_true, Bool.true_and, List.isEmpty_cons,
          Bool.not_false] at h1
        simp [createTT_struct x h1]
    · simp [he]
termination_by c => sizeOf c
decreasing_by
  all_goals simp_wf
  have := List.sizeOf_lt_of_mem hx
  omega

theorem passForL_eq (l : List TT) : passForL l = l.map passFor := by
  induction l with
  | nil => rfl
  | cons t ts ih => simp [passForL, ih]

theorem passFor_op (t : TT) : (passFor t).op = 0 := by rcases t; rfl

theorem passFor_good : ∀ t : TT, good (passFor t) = true
  | .mk e ch => by
    rw [passFor, good_eq]
    simp only [Bool.and_eq_true, List.all_eq_true]
    refine ⟨by simp, ?_⟩
    intro x hx
    split at hx
    · rw [passForL_eq, List.mem_map] at hx
      obtain ⟨t, ht, rfl⟩ := hx
      exact passFor_good t
    · simp at hx
termination_by t => sizeOf t
decreasing_by
  simp_wf
  have := List.sizeOf_lt_of_mem ht
  omega

section
variable {V S C Ch : Type} {W : World V S C} {step : C → Ch → Option C}

theorem extendAll_eq (l : List Cond) (t : TT) : extendAll l t = l.map (extendC · t) := by
  induction l with
  | nil => rw [extendAll]; rfl
  | cons x xs ih => rw [extendAll, ih]; rfl

theorem extendC_op (c : Cond) (t : TT) : (extendC c t).op = c.op ∧ (extendC c t).enc = c.enc := by
  rw [extendC]; split
  · exact ⟨rfl, rfl⟩
  · split <;> exact ⟨rfl, rfl⟩

theorem ext_pad_rep (hW : W.Ok step) {e o : Nat} {cv : List Nat} (he : e = 3 ∨ e = 5)
    (h0 : o ≠ 0) (h1 : o ≠ 1) (h2 : o ≠ 2) (h5 : o ≠ 5) (ss : List (V → Thunk S C)) :
    ∀ n, W.ext e o cv (ss ++ List.replicate n (fun _ => passT)) = W.ext e o cv ss
  | 0 => by simp
  | n + 1 => by
    rw [List.replicate_succ', ← List.append_assoc, hW.pad _ _ _ _ he h0 h1 h2 h5]
    exact ext_pad_rep hW he h0 h1 h2 h5 ss n

theorem bindR_passT (r : Res S C) : bindR r passT = r := by
  rcases r with ⟨_ | c, s⟩ <;> rfl

theorem seqT_passes (d : V) (ps : List Cond) (hps : ∀ p ∈ ps, isPass p = true) (fs : List V) (v : V) :
    seqT ((assign d ps fs v).map fun p => sem W p.1 p.2) = passT := by
  induction ps generalizing fs with
  | nil => rfl
  | cons p ps ih =>
    have hp := hps p (by simp)
    have ih' := fun fs => ih (fun q hq => hps q (by simp [hq])) fs
    simp only [Normalize.assign]
    split <;> simp only [List.map_cons, sem_pass hp, seqT_pass_cons, ih']

theorem countP_pos {l : List Cond} (h : l.any isStruct = true) : 0 < l.countP isStruct := by
  rw [List.any_eq_true] at h
  obtain ⟨x, hx, hs⟩ := h
  exact List.countP_pos_iff.2 ⟨x, hx, hs⟩

theorem extendC_same (hW : W.Ok step) :
    ∀ (c : Cond) (t : TT), good c = true → wfTT t = true →
      Same W (extendC c t) c ∧ good (extendC c t) = true := by
  intro c t hc ht
  have hgood := hc
  rw [good_eq] at hgood
  simp only [Bool.and_eq_true, List.all_eq_true] at hgood
  obtain ⟨hne, hgch⟩ := hgood
  rw [extendC]
  split
  · -- logical: every child extended with the same tree
    rename_i hl
    have ih : ∀ x ∈ c.ch, Same W (extendC x t) x ∧ good (extendC x t) = true :=
      fun x hx => extendC_same hW x t (hgch x hx) ht
    rw [extendAll_eq]
    have hpw : Pw W (c.ch.map (extendC · t)) c.ch := Pw.of_map fun x hx => (ih x hx).1
    refine ⟨same_congr c hpw, ?_⟩
    rw [good_eq]
    simp only [Bool.and_eq_true, List.all_eq_true, List.mem_map]
    exact ⟨by rw [hpw.any_struct]; exact hne, by rintro _ ⟨x, hx, rfl⟩; exact (ih x hx).2⟩
  · split
    · rename_i hl hct
      simp only [Bool.and_eq_true, beq_iff_eq] at hct
      obtain ⟨hcx, hte⟩ := hct
      have htw := ht
      rw [wfTT_eq] at htw
      simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, List.all_eq_true] at htw
      -- the children: structural ones extended, then fresh `Pass` nodes
      have ihs : ∀ (xs : List Cond) (ts : List TT), (∀ x ∈ xs, good x = true) →
          (∀ t ∈ ts, wfTT t = true) → (∀ t' ∈ ts, sizeOf t' < sizeOf t) →
          ∃ cs' ps, extendS xs ts = cs' ++ ps ∧ Pw W cs' xs ∧ (∀ y ∈ cs', good y = true) ∧
            (∀ p ∈ ps, isPass p = true ∧ good p = true) ∧
            (ps ≠ [] → xs.countP isStruct < ts.length) := by
        intro xs ts hxs hts hsz
        induction xs generalizing ts with
        | nil =>
          refine ⟨[], passForL ts, by rw [extendS]; rfl, .nil, by simp, ?_, ?_⟩
          · intro p hp
            rw [passForL_eq, List.mem_map] at hp
            obtain ⟨t', -, rfl⟩ := hp
            exact ⟨by simp [isPass, passFor_op], passFor_good t'⟩
          · intro hps
            cases ts with
            | nil => simp [passForL] at hps
            | cons _ _ => simp
        | cons x xs ihx =>
          have hx := hxs x (by simp)
          have hxs' : ∀ y ∈ xs, good y = true := fun y hy => hxs y (List.mem_cons_of_mem _ hy)
          cases ts with
          | nil =>
            obtain ⟨cs', ps, he, hpw, hg, hp, hlen⟩ := ihx [] hxs' (by simp) (by simp)
            have hps : ps = [] := by
              cases ps with
              | nil => rfl
              | cons p ps => exact absurd (hlen (by simp)) (by simp)
            subst hps
            refine ⟨x :: cs', [], ?_, .cons (Same.refl x) hpw, ?_, by simp, by simp⟩
            · rw [extendS, he]; simp
            · intro y hy
              rcases List.mem_cons.1 hy with rfl | hy
              · exact hx
              · exact hg y hy
          | cons t' ts =>
            by_cases hsx : isStruct x = true
            · have hxe := extendC_same hW x t' hx (hts t' (by simp))
              obtain ⟨cs', ps, he, hpw, hg, hp, hlen⟩ := ihx ts hxs'
                (fun t hm => hts t (by simp [hm])) (fun t hm => hsz t (by simp [hm]))
              refine ⟨extendC x t' :: cs', ps, ?_, .cons hxe.1 hpw, ?_, hp, ?_⟩
              · rw [extendS, ite_pos' hsx, he]; rfl
              · intro y hy
                rcases List.mem_cons.1 hy with rfl | hy
                · exact hxe.2
                · exact hg y hy
              · intro hne
                have := hlen hne
                simp only [List.countP_cons, hsx, ite_true, List.length_cons]
                omega
            · obtain ⟨cs', ps, he, hpw, hg, hp, hlen⟩ := ihx (t' :: ts) hxs' hts hsz
              refine ⟨x :: cs', ps, ?_, .cons (Same.refl x) hpw, ?_, hp, ?_⟩
              · rw [extendS, ite_neg' hsx, he]; rfl
              · intro y hy
                rcases List.mem_cons.1 hy with rfl | hy
                · exact hx
                · exact hg y hy
              · intro hne
                have := hlen hne
                simp only [List.countP_cons, hsx, Bool.false_eq_true, ite_false]
                omega
      obtain ⟨cs', ps, hsplit, hpw, hg, hpsPass, hlen⟩ :=
        ihs c.ch t.ch hgch htw.2 (fun t' ht' => TT.sizeOf_lt ht')
      rw [hsplit]
      -- an array that checks something has a structural child, and its type tree one child:
      -- nothing is appended
      have harr : c.enc = 4 → c.op ≠ 0 → ps = [] := by
        intro h4 h0
        cases ps with
        | nil => rfl
        | cons p ps =>
          exfalso
          have h1 : t.ch.length = 1 := by
            rcases htw.1 with h | h
            · exact absurd (hte ▸ h4) (by simpa using h)
            · exact h
          have hany : c.ch.any isStruct = true := by
            simp only [Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_false_imp, beq_iff_eq] at hne
            rcases hne with h | h
            · exact absurd (by simpa using h h4) h0
            · exact h
          have := hlen (by simp)
          have := countP_pos hany
          omega
      have hop : c.op ≠ 1 ∧ c.op ≠ 2 := by
        simp only [isLogical, Bool.or_eq_true, beq_iff_eq, not_or] at hl; exact hl
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · funext v
        show sem W ⟨c.enc, c.op, c.cv, cs' ++ ps⟩ v = sem W c v
        rw [sem_eq, sem_eq]
        dsimp only
        by_cases h0 : c.op = 0
        · simp [h0]
        rw [ite_neg' h0, ite_neg' h0, ite_neg' hop.1, ite_neg' hop.1, ite_neg' hop.2,
          ite_neg' hop.2]
        by_cases h5 : c.op = 5 ∧ (c.enc = 3 ∨ c.enc = 5)
        · rw [ite_pos' h5, ite_pos' h5]
          funext sl cs
          simp only [matchesT]
          split
          · rw [assign_append, List.map_append, seqT_append,
              seqT_passes W.dflt ps (fun p hp => (hpsPass p hp).1), bindR_passT, hpw.assign]
          · rfl
        rw [ite_neg' h5, ite_neg' h5, List.map_append]
        by_cases h4 : c.enc = 4
        · rw [harr h4 h0, List.map_nil, List.append_nil, hpw.map_sem']
        · have hps' : ps.map (sem W) = List.replicate ps.length (fun _ => passT) := by
            apply List.eq_replicate_iff.2
            refine ⟨by simp, fun s hs => ?_⟩
            rw [List.mem_map] at hs
            obtain ⟨p, hp, rfl⟩ := hs
            funext w
            exact sem_pass (hpsPass p hp).1 w
          have he : c.enc = 3 ∨ c.enc = 5 := by
            simp only [isComplex, Bool.or_eq_true, beq_iff_eq] at hcx; omega
          have h5' : c.op ≠ 5 := fun h => h5 ⟨h, he⟩
          rw [hps', ext_pad_rep hW he h0 hop.1 hop.2 h5', hpw.map_sem']
      · show isStruct ⟨c.enc, c.op, c.cv, cs' ++ ps⟩ = isStruct c
        rw [struct_nonlog (c := ⟨c.enc, c.op, c.cv, cs' ++ ps⟩) hop.1 hop.2, struct_nonlog hop.1 hop.2]
      · show good ⟨c.enc, c.op, c.cv, cs' ++ ps⟩ = true
        rw [good_eq]
        simp only [Bool.and_eq_true, List.all_eq_true, List.mem_append]
        refine ⟨?_, ?_⟩
        · simp only [Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_false_imp, beq_iff_eq,
            List.any_append] at hne ⊢
          rcases hne with h | h
          · exact Or.inl h
          · right; rw [hpw.any_struct, h]; simp
        · rintro y (hy | hy)
          · exact hg y hy
          · exact (hpsPass y hy).2
    · exact ⟨Same.refl _, hc⟩
termination_by c t => (sizeOf t, sizeOf c)
decreasing_by
  · exact Prod.Lex.right _ (sizeOf_lt_of_mem hx)
  · exact Prod.Lex.left _ _ (hsz t' (by simp))

end

section
variable {V S C Ch : Type} {W : World V S C} {step : C → Ch → Option C}

theorem foldl_inv {α β} (f : α → β → α) (P : α → Prop) :
    ∀ (l : List β) (a : α), (∀ a b, b ∈ l → P a → P (f a b)) → P a → P (l.foldl f a)
  | [], _, _, h => h
  | b :: l, a, hf, h => foldl_inv f P l (f a b) (fun a' b' hb => hf a' b' (by simp [hb]))
      (hf a b (by simp) h)

theorem getElem!_set_eq {l : List Cond} {i k : Nat} {x : Cond} :
    (l.set i x)[k]! = if i = k ∧ i < l.length then x else l[k]! := by
  simp only [List.getElem!_eq_getElem?_getD, List.getElem?_set]
  by_cases h1 : i = k
  · subst h1
    by_cases h2 : i < l.length
    · simp [h2]
    · simp [h2]
  · simp [h1]

theorem isPaddeable_extendC (c : Cond) (t : TT) : isPaddeable (extendC c t) = isPaddeable c := by
  have := extendC_op c t
  rcases c with ⟨e, o, cv, ch⟩
  simp only [isPaddeable, isLogical, isComplex] at this ⊢
  rw [this.1, this.2]

/-- What the padding loop keeps: each node `Same` as before, paddeable nodes `good`. -/
def PadInv (W : World V S C) (cs acc : List Cond) : Prop :=
  acc.length = cs.length ∧ ∀ k < cs.length, Same W acc[k]! cs[k]! ∧
    isPaddeable acc[k]! = isPaddeable cs[k]! ∧ (isPaddeable cs[k]! = true → good acc[k]! = true)

theorem padInv_step (hW : W.Ok step) {cs acc : List Cond} {i : Nat} {t : TT}
    (h : PadInv W cs acc) (hi : isPaddeable acc[i]! = true) (ht : wfTT t = true) :
    PadInv W cs (acc.set i (extendC acc[i]! t)) := by
  obtain ⟨hlen, hk⟩ := h
  refine ⟨by simp [hlen], fun k hkl => ?_⟩
  rw [getElem!_set_eq]
  split
  · rename_i hik
    obtain ⟨rfl, hil⟩ := hik
    obtain ⟨hs, hp, hg⟩ := hk i (hlen ▸ hil)
    have hgi : good acc[i]! = true := hg (hp ▸ hi)
    have := extendC_same hW acc[i]! t hgi ht
    exact ⟨this.1.trans hs, by rw [isPaddeable_extendC, hp], fun _ => this.2⟩
  · exact hk k hkl

theorem padLoop_inv (hW : W.Ok step) (cs : List Cond)
    (hcs : ∀ x ∈ cs, isPaddeable x = true → hasTT x = true) : PadInv W cs (padLoop cs) := by
  have h0 : PadInv W cs cs := by
    refine ⟨rfl, fun k hk => ⟨Same.refl _, rfl, fun hp => hasTT_good _ (hcs _ ?_ hp)⟩⟩
    rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hk]
    exact List.getElem_mem hk
  unfold padLoop
  refine foldl_inv _ (PadInv W cs) _ _ (fun acc i _ hacc => ?_) h0
  split
  · exact hacc
  · rename_i hi
    have hi' : isPaddeable acc[i]! = true := by simpa using hi
    refine foldl_inv _ (fun a => PadInv W cs a ∧ isPaddeable a[i]! = true) _ _
      (fun a j _ ⟨ha, hai⟩ => ?_) ⟨hacc, hi'⟩ |>.1
    split
    · exact ⟨ha, hai⟩
    · split
      · exact ⟨ha, hai⟩
      · rename_i t ht
        refine ⟨padInv_step hW ha hai (createTT_wf _ _ ht), ?_⟩
        rw [getElem!_set_eq]
        split
        · rw [isPaddeable_extendC]; exact hai
        · exact hai

theorem Pw.of_getElem! {l l' : List Cond} (hlen : l.length = l'.length)
    (h : ∀ k < l'.length, Same W l[k]! l'[k]!) : Pw W l l' := by
  induction l generalizing l' with
  | nil => cases l' with
    | nil => exact .nil
    | cons _ _ => simp at hlen
  | cons x xs ih =>
    cases l' with
    | nil => simp at hlen
    | cons y ys =>
      refine .cons (by simpa using h 0 (by simp)) (ih (by simpa using hlen) fun k hk => ?_)
      simpa using h (k + 1) (by simpa using hk)

theorem pad_same (hW : W.Ok step) (c : Cond) : Same W (pad c) c := by
  unfold pad
  split
  · rename_i hc
    simp only [Bool.and_eq_true, padOk, List.all_eq_true, List.mem_filter] at hc
    have hcs : ∀ x ∈ c.ch, isPaddeable x = true → hasTT x = true :=
      fun x hx hp => hc.2.1 x ⟨hx, hp⟩
    obtain ⟨hlen, hk⟩ := padLoop_inv hW c.ch hcs
    exact same_congr c (Pw.of_getElem! hlen fun k hkl => (hk k hkl).1)
  · exact Same.refl _

end
end Normalize
