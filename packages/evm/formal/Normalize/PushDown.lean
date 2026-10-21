import Normalize.Steps

/-!
# `pushDownOr` keeps the meaning

`Or[M(pre, x₁, post), M(pre, x₂, post), …]` becomes `M(pre, Or[x₁, x₂, …], post)`
(`M` a `Matches` or an `And`). This is distributivity, which holds here
because nothing in the branches writes slots (so re-running `pre` in the next
branch gives the same result) and the hinge children charge nothing (so the
merged `Or` commits to a branch no later sibling would have rejected).
-/

namespace Normalize

section
variable {V S C Ch : Type} {W : World V S C} {step : C → Ch → Option C}

theorem orT_all_none {ts : List (Thunk S C)} {sl : S} {cs : C}
    (h : ∀ t ∈ ts, t sl cs = (none, sl)) : orT ts sl cs = (none, sl) := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    simp only [orT, h t (by simp)]
    exact ih fun t' ht' => h t' (by simp [ht'])

/-- Distributivity of `Or` over a sequence, for a pure hinge. -/
theorem orT_factor (pre post hs : List (Thunk S C)) (hpre : ∀ t ∈ pre, KeepsT t)
    (hpost : ∀ t ∈ post, KeepsT t) (hh : ∀ t ∈ hs, PureT t) :
    orT (hs.map fun h => seqT (pre ++ h :: post)) = seqT (pre ++ orT hs :: post) := by
  funext sl cs
  have split : ∀ h : Thunk S C, seqT (pre ++ h :: post) sl cs =
      bindR (seqT pre sl cs) fun s c => bindR (h s c) (seqT post) := by
    intro h; rw [seqT_append]; rfl
  rw [split]
  obtain ⟨r, hr⟩ := keeps_eq (seqT_keeps hpre) sl cs
  rw [hr]
  rcases r with _ | c1
  · exact orT_all_none fun t ht => by
      rw [List.mem_map] at ht
      obtain ⟨h, -, rfl⟩ := ht
      rw [split, hr]; rfl
  · simp only [bindR_some]
    obtain ⟨q, hq⟩ := keeps_eq (seqT_keeps hpost) sl c1
    induction hs with
    | nil => rfl
    | cons h hs ih =>
      obtain ⟨b, hb⟩ := hh h (by simp)
      have ih' := ih fun t ht => hh t (by simp [ht])
      simp only [List.map_cons, orT, split, hr, bindR_some, hb]
      by_cases hbs : b sl
      · simp only [hbs, ite_true, bindR_some, hq]
        rcases q with _ | c2
        · simp only
          refine (orT_all_none fun t ht => ?_).trans rfl
          rw [List.mem_map] at ht
          obtain ⟨h', hh', rfl⟩ := ht
          obtain ⟨b', hb'⟩ := hh h' (by simp [hh'])
          rw [split, hr, bindR_some, hb']
          by_cases hb's : b' sl <;> simp [hb's, hq]
        · rfl
      · simp only [hbs, Bool.false_eq_true, ite_false, bindR_none]
        exact ih'

/-! ## Unpacking the merge conditions -/

theorem replaceAt_eq {l : List Cond} {h : Nat} (hh : h < l.length) (x : Cond) :
    replaceAt l h x = l.take h ++ x :: l.drop (h + 1) := by
  simp [replaceAt, hh]

theorem list_split {l : List Cond} {h : Nat} (hh : h < l.length) :
    l = l.take h ++ l[h]! :: l.drop (h + 1) := by
  rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hh]
  simp

theorem hingeM_spec {first : Cond} {chs : List Cond} {h : Nat} (hm : hingeM first chs = some h) :
    h < first.ch.length ∧ ∀ o ∈ chs,
      o.ch = first.ch.take h ++ o.ch[h]! :: first.ch.drop (h + 1) := by
  unfold hingeM at hm
  split at hm
  · simp at hm
  split at hm
  · simp at hm
  rename_i _ hlen
  simp only [Bool.not_eq_true', Bool.not_eq_false, List.all_eq_true, beq_iff_eq] at hlen
  split at hm
  · rename_i i hfil
    simp only [Option.some.injEq] at hm
    subst hm
    have hmem : i ∈ (List.range first.ch.length).filter
        (fun i => chs.any fun o => o.ch[i]! != first.ch[i]!) := by rw [hfil]; simp
    have hi : i < first.ch.length := by simpa using (List.mem_filter.1 hmem).1
    refine ⟨hi, fun o ho => ?_⟩
    have hol := hlen o ho
    -- every other position agrees with the first branch
    have hsame : ∀ k < first.ch.length, k ≠ i → o.ch[k]! = first.ch[k]! := by
      intro k hk hki
      have : k ∉ (List.range first.ch.length).filter
          (fun i => chs.any fun o => o.ch[i]! != first.ch[i]!) := by
        rw [hfil]; simpa using hki
      simp only [List.mem_filter, List.mem_range, hk, true_and, List.any_eq_true, bne_iff_ne,
        ne_eq, not_exists, not_and, Decidable.not_not] at this
      exact this o ho
    conv => lhs; rw [list_split (hol ▸ hi : i < o.ch.length)]
    congr 1
    · apply List.ext_getElem (by simp [hol])
      intro k h1 h2
      simp only [List.getElem_take]
      have hk : k < i := by simp at h1; omega
      have := hsame k (by omega) (by omega)
      rwa [List.getElem!_eq_getElem?_getD, List.getElem!_eq_getElem?_getD,
        List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega)] at this
    · congr 1
      apply List.ext_getElem (by simp [hol])
      intro k h1 h2
      simp only [List.getElem_drop]
      have := hsame (i + 1 + k) (by simp at h2; omega) (by omega)
      rwa [List.getElem!_eq_getElem?_getD, List.getElem!_eq_getElem?_getD,
        List.getElem?_eq_getElem (by simp at h1; omega),
        List.getElem?_eq_getElem (by simp at h2; omega)] at this
  · simp at hm

theorem perm_getElem_eraseIdx {l : List Cond} {j : Nat} (hj : j < l.length) :
    l.Perm (l[j]! :: l.eraseIdx j) := by
  rw [List.eraseIdx_eq_take_drop_succ]
  conv => lhs; rw [list_split hj]
  exact List.perm_middle

theorem hingeOk_spec {chs : List Cond} (h : hingeOk chs = true) (o : Cond) (ho : o ∈ chs) :
    hingeOf chs o < o.ch.length ∧
      (o.ch.eraseIdx (hingeOf chs o)).Perm (chs.head!.ch.eraseIdx (hingeOf chs chs.head!)) := by
  simp only [hingeOk, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at h
  refine ⟨?_, List.isPerm_iff.1 (h.2 o ho)⟩
  have h1 := h.1 o ho
  unfold hingeOf
  apply List.idxOf_lt_length_of_mem
  have : (o.ch.filter fun x => !common chs x).head! ∈ o.ch.filter fun x => !common chs x := by
    match hf : o.ch.filter fun x => !common chs x, h1 with
    | [y], _ => exact List.mem_singleton.2 rfl
  exact (List.mem_filter.1 this).1

/-! ## The two merges -/

theorem struct_matches {o : Cond} (ho : o.op = 5) (he : o.enc = 3 ∨ o.enc = 5) : isStruct o = true := by
  rw [struct_nonlog (by omega) (by omega)]; rcases he with h | h <;> simp [h]

theorem assign_mid (d : V) (pre post : List Cond) (x : Cond) (s : Bool) (hx : isStruct x = s)
    (fs : List V) (v : V) :
    assign d (pre ++ x :: post) fs v = assign d pre fs v ++
      (x, if s then (fs.drop (pre.countP isStruct)).headD d else v) ::
        assign d post (if s then (fs.drop (pre.countP isStruct)).tail
          else fs.drop (pre.countP isStruct)) v := by
  rw [assign_append]
  congr 1
  simp only [Normalize.assign, hx]
  cases s <;> rfl

theorem orNode_struct {hs : List Cond} {s : Bool} (hne : hs ≠ []) (h : ∀ x ∈ hs, isStruct x = s) :
    isStruct (orNode hs) = s := by
  rw [struct_log (c := orNode hs) (Or.inr rfl)]
  show hs.any isStruct = s
  cases s
  · rw [List.any_eq_false]; intro y hy; simp [h y hy]
  · obtain ⟨y, hy⟩ := List.exists_mem_of_ne_nil hs hne
    rw [List.any_eq_true]; exact ⟨y, hy, h y hy⟩

/-- `Or` over `Matches` that differ in one position, with a pure hinge. -/
theorem matches_factor (hW : W.Ok step) (e : Nat) (cv : List Nat) (pre post hs : List Cond)
    (s : Bool) (hne : hs ≠ []) (hst : ∀ x ∈ hs, isStruct x = s)
    (hpre : ∀ x ∈ pre, writes x = false) (hpost : ∀ x ∈ post, writes x = false)
    (hpure : ∀ x ∈ hs, writes x = false ∧ charges x = false) (v : V) :
    orT (hs.map fun x => matchesT W e cv (pre ++ x :: post) v) =
      matchesT W e cv (pre ++ orNode hs :: post) v := by
  funext sl cs
  by_cases hg : W.gate e cv v = true
  · have hor := orNode_struct hne hst
    let fs := W.fields e v
    let w := if s then (fs.drop (pre.countP isStruct)).headD W.dflt else v
    let A := (assign W.dflt pre fs v).map (fun p => sem W p.1 p.2)
    let B := (assign W.dflt post (if s then (fs.drop (pre.countP isStruct)).tail
      else fs.drop (pre.countP isStruct)) v).map (fun p => sem W p.1 p.2)
    have hl : (hs.map fun x => matchesT W e cv (pre ++ x :: post) v) =
        (hs.map (fun x => sem W x w)).map fun h => seqT (A ++ h :: B) := by
      rw [List.map_map]
      apply List.map_congr_left
      intro x hx
      funext sl cs
      simp only [Function.comp, matchesT, hg, ite_true]
      rw [assign_mid W.dflt pre post x s (hst x hx), List.map_append, List.map_cons]
    have hA : ∀ t ∈ A, KeepsT t := by
      intro t ht
      simp only [A, List.mem_map] at ht
      obtain ⟨p, hp, rfl⟩ := ht
      exact keeps_sem hW p.1 (hpre p.1 (mem_assign hp)) p.2
    have hB : ∀ t ∈ B, KeepsT t := by
      intro t ht
      simp only [B, List.mem_map] at ht
      obtain ⟨p, hp, rfl⟩ := ht
      exact keeps_sem hW p.1 (hpost p.1 (mem_assign hp)) p.2
    have hP : ∀ t ∈ hs.map (fun x => sem W x w), PureT t := by
      intro t ht
      rw [List.mem_map] at ht
      obtain ⟨x, hx, rfl⟩ := ht
      exact pure_sem hW x (hpure x hx).1 (hpure x hx).2 w
    rw [hl, orT_factor A B _ hA hB hP]
    simp only [matchesT, hg, ite_true]
    rw [assign_mid W.dflt pre post _ s hor, List.map_append, List.map_cons, sem_or (c := orNode hs) rfl]
    rfl
  · simp only [matchesT, hg]
    exact orT_all_none fun t ht => by
      rw [List.mem_map] at ht
      obtain ⟨x, -, rfl⟩ := ht
      simp [matchesT, hg]

/-- `Or` over `And`s that differ in one position, with a pure hinge. -/
theorem and_factor (hW : W.Ok step) (pre post hs : List Cond) (v : V)
    (hpre : ∀ x ∈ pre, writes x = false) (hpost : ∀ x ∈ post, writes x = false)
    (hpure : ∀ x ∈ hs, writes x = false ∧ charges x = false) :
    orT (hs.map fun x => seqT ((pre ++ x :: post).map fun y => sem W y v)) =
      seqT ((pre ++ orNode hs :: post).map fun y => sem W y v) := by
  have := orT_factor (pre.map fun y => sem W y v) (post.map fun y => sem W y v)
    (hs.map fun x => sem W x v)
    (by simp only [List.mem_map]; rintro t ⟨x, hx, rfl⟩; exact keeps_sem hW x (hpre x hx) v)
    (by simp only [List.mem_map]; rintro t ⟨x, hx, rfl⟩; exact keeps_sem hW x (hpost x hx) v)
    (by simp only [List.mem_map]; rintro t ⟨x, hx, rfl⟩
        exact pure_sem hW x (hpure x hx).1 (hpure x hx).2 v)
  rw [List.map_map] at this
  simp only [List.map_append, List.map_cons, Function.comp_def] at this ⊢
  rw [this, sem_or (c := orNode hs) rfl]
  rfl

theorem mergeMatches_same (hW : W.Ok step) {c first : Cond} {rest nch : List Cond}
    (hc : c.op = 2) (hch : c.ch = first :: rest)
    (henc : ∀ o ∈ c.ch, o.enc = first.enc) (hop : ∀ o ∈ c.ch, o.op = 5)
    (hm : mergeMatches first c.ch = some nch) : Same W { first with ch := nch } c := by
  unfold mergeMatches at hm
  split at hm; · simp at hm
  rename_i he
  have he : first.enc = 3 ∨ first.enc = 5 := by revert he; simp; omega
  split at hm; · simp at hm
  rename_i hcv
  have hcv : ∀ o ∈ c.ch, o.cv = first.cv := by simpa using hcv
  split at hm; · simp at hm
  rename_i hw
  have hw : ∀ o ∈ c.ch, writes o = false := fun o ho => any_false (by simpa using hw) ho
  split at hm; · simp at hm
  rename_i h hhinge
  obtain ⟨hh, hsplit⟩ := hingeM_spec hhinge
  split at hm; · simp at hm
  rename_i hst
  split at hm; · simp at hm
  rename_i hchg
  simp only [Option.some.injEq] at hm
  subst hm
  have hfirst : first ∈ c.ch := by simp [hch]
  have hfw : ∀ x ∈ first.ch, writes x = false := by
    have := hw first hfirst
    rw [writes_eq, Bool.or_eq_false_iff] at this
    exact fun x hx => any_false this.2 hx
  let hs := c.ch.map (·.ch[h]!)
  have hs_ne : hs ≠ [] := by simp [hs, hch]
  have hall : ∀ y ∈ hs, isStruct y = isStruct hs.head! := by
    intro y hy
    simp only [Bool.not_eq_true', Bool.not_eq_false] at hst
    have := List.all_eq_true.1 hst y hy
    simpa only [beq_iff_eq] using this
  have hpure : ∀ x ∈ hs, writes x = false ∧ charges x = false := by
    intro x hx
    have hx' := hx
    simp only [hs, List.mem_map] at hx'
    obtain ⟨o, ho, rfl⟩ := hx'
    have hlo : h < o.ch.length := by
      have := congrArg List.length (hsplit o ho); simp at this; omega
    have hmem : o.ch[h]! ∈ o.ch := by
      rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hlo]; exact List.getElem_mem hlo
    have hwo := hw o ho
    rw [writes_eq, Bool.or_eq_false_iff] at hwo
    exact ⟨any_false hwo.2 hmem, any_false (by simpa [hs] using hchg) hx⟩
  constructor
  · funext v
    rw [sem_or hc, sem_matches (c := { first with ch := replaceAt first.ch h (orNode hs) })
      (hop first hfirst) he]
    dsimp only
    rw [replaceAt_eq hh]
    have hbranch : c.ch.map (fun o => sem W o v) =
        hs.map fun x => matchesT W first.enc first.cv (first.ch.take h ++ x :: first.ch.drop (h + 1)) v := by
      simp only [hs, List.map_map]
      apply List.map_congr_left
      intro o ho
      simp only [Function.comp]
      rw [sem_matches (hop o ho) (henc o ho ▸ he), henc o ho, hcv o ho, ← hsplit o ho]
    rw [hbranch]
    exact (matches_factor hW first.enc first.cv _ _ hs _ hs_ne hall
      (fun x hx => hfw x (List.mem_of_mem_take hx)) (fun x hx => hfw x (List.mem_of_mem_drop hx))
      hpure v).symm
  · rw [struct_log (Or.inr hc), struct_matches (o := { first with ch := _ }) (hop first hfirst) he]
    rw [eq_comm, List.any_eq_true]
    exact ⟨first, hfirst, struct_matches (hop first hfirst) he⟩

theorem any_congr_mem {l : List Cond} {f g : Cond → Bool} (h : ∀ x ∈ l, f x = g x) :
    l.any f = l.any g := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.any_cons, h x (by simp), ih fun y hy => h y (by simp [hy])]

theorem any_or_const {l : List Cond} (hne : l ≠ []) (P : Bool) (q : Cond → Bool) :
    l.any (fun o => P || q o) = (P || l.any q) := by
  induction l with
  | nil => exact absurd rfl hne
  | cons x xs ih =>
    cases xs with
    | nil => simp
    | cons y ys =>
      simp only [List.any_cons] at ih ⊢
      rw [ih (by simp)]
      cases P <;> simp

theorem mergeAnd_same (hW : W.Ok step) {c first : Cond} {rest nch : List Cond}
    (hc : c.op = 2) (hch : c.ch = first :: rest) (hop : ∀ o ∈ c.ch, o.op = 1)
    (hm : mergeAnd first c.ch = some nch) : Same W { first with ch := nch } c := by
  unfold mergeAnd at hm
  split at hm; · simp at hm
  rename_i hw
  have hw : ∀ o ∈ c.ch, writes o = false := fun o ho => any_false (by simpa using hw) ho
  split at hm; · simp at hm
  rename_i hr
  have hr : ∀ o ∈ c.ch, canReorderAnd o.ch = true := by
    simp only [Bool.not_eq_true', Bool.not_eq_false, List.all_eq_true] at hr; exact hr
  split at hm; · simp at hm
  rename_i hok
  have hok : hingeOk c.ch = true := by simpa using hok
  split at hm; · simp at hm
  rename_i hchg
  simp only [Option.some.injEq] at hm
  subst hm
  have hfirst : first ∈ c.ch := by simp [hch]
  have hhead : c.ch.head! = first := by rw [hch]; rfl
  let h0 := hingeOf c.ch first
  have hh0 : h0 < first.ch.length := (hingeOk_spec hok first hfirst).1
  let ys := c.ch.map fun o => o.ch[hingeOf c.ch o]!
  have hys_ne : ys ≠ [] := by simp [ys, hch]
  let pre := first.ch.take h0
  let post := first.ch.drop (h0 + 1)
  -- every branch is a permutation of `pre ++ y :: post`
  have hperm : ∀ o ∈ c.ch, o.ch.Perm (pre ++ o.ch[hingeOf c.ch o]! :: post) := by
    intro o ho
    obtain ⟨hj, hp⟩ := hingeOk_spec hok o ho
    rw [hhead] at hp
    refine (perm_getElem_eraseIdx hj).trans ?_
    refine (List.Perm.cons _ (hp.trans ?_)).trans List.perm_middle.symm
    rw [List.eraseIdx_eq_take_drop_succ]
  have hfw : ∀ x ∈ first.ch, writes x = false := by
    have := hw first hfirst
    rw [writes_eq, Bool.or_eq_false_iff] at this
    exact fun x hx => any_false this.2 hx
  have hpure : ∀ y ∈ ys, writes y = false ∧ charges y = false := by
    intro y hy
    have hy' := hy
    simp only [ys, List.mem_map] at hy'
    obtain ⟨o, ho, rfl⟩ := hy'
    obtain ⟨hj, -⟩ := hingeOk_spec hok o ho
    have hmem : o.ch[hingeOf c.ch o]! ∈ o.ch := by
      rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hj]; exact List.getElem_mem hj
    have hwo := hw o ho
    rw [writes_eq, Bool.or_eq_false_iff] at hwo
    exact ⟨any_false hwo.2 hmem, any_false (by simpa [ys] using hchg) hy⟩
  have hfop : first.op = 1 := hop first hfirst
  constructor
  · funext v
    rw [sem_or hc, sem_and (c := { first with ch := replaceAt first.ch h0 (orNode ys) }) hfop]
    dsimp only
    rw [replaceAt_eq hh0]
    have hbranch : c.ch.map (fun o => sem W o v) =
        ys.map fun y => seqT ((pre ++ y :: post).map fun x => sem W x v) := by
      simp only [ys, List.map_map]
      apply List.map_congr_left
      intro o ho
      simp only [Function.comp]
      rw [sem_and (hop o ho)]
      have := seqT_perm hW (W := W) (l := o.ch.map (·, v))
        (l' := (pre ++ o.ch[hingeOf c.ch o]! :: post).map (·, v)) ((hperm o ho).map _)
        (by simpa [List.map_map, Function.comp_def] using hr o ho)
      simpa [List.map_map, Function.comp_def] using this
    rw [hbranch]
    exact (and_factor hW pre post ys v (fun x hx => hfw x (List.mem_of_mem_take hx))
      (fun x hx => hfw x (List.mem_of_mem_drop hx)) hpure).symm
  · rw [struct_log (Or.inr hc), struct_log (c := { first with ch := _ }) (Or.inl hfop)]
    dsimp only
    rw [replaceAt_eq hh0]
    have hbr : c.ch.any isStruct = c.ch.any fun o => (pre ++ post).any isStruct ||
        isStruct o.ch[hingeOf c.ch o]! := by
      apply any_congr_mem
      intro o ho
      rw [struct_log (Or.inl (hop o ho)), any_perm (hperm o ho)]
      simp only [List.any_append, List.any_cons]
      cases (pre.any isStruct) <;> cases (post.any isStruct) <;> cases isStruct o.ch[hingeOf c.ch o]! <;> rfl
    rw [hbr, any_or_const (by simp [hch])]
    have hor : isStruct (orNode ys) = c.ch.any fun o => isStruct o.ch[hingeOf c.ch o]! := by
      rw [struct_log (c := orNode ys) (Or.inr rfl)]
      show ys.any isStruct = _
      simp only [ys, List.any_map, Function.comp_def]
    show (pre ++ orNode ys :: post).any isStruct = _
    simp only [List.any_append, List.any_cons, hor]
    cases (pre.any isStruct) <;> cases (post.any isStruct) <;>
      cases (c.ch.any fun o => isStruct o.ch[hingeOf c.ch o]!) <;> rfl

theorem pushStep_same (hW : W.Ok step) (c n : Cond) (h : pushStep c = some n) : Same W n c := by
  unfold pushStep at h
  split at h
  · rename_i hcond
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, Bool.not_eq_true',
      List.all_eq_true] at hcond
    obtain ⟨⟨⟨hc, hlen⟩, henc⟩, -⟩ := hcond
    obtain ⟨first, rest, hch⟩ : ∃ f r, c.ch = f :: r := by
      cases hc' : c.ch with
      | nil => rw [hc'] at hlen; simp at hlen
      | cons f r => exact ⟨f, r, rfl⟩
    have hhead : c.ch.head! = first := by rw [hch]; rfl
    rw [hhead] at h henc
    split at h
    · rename_i hop
      simp only [List.all_eq_true, beq_iff_eq] at hop
      cases hm : mergeMatches first c.ch with
      | none => rw [hm] at h; simp at h
      | some nch =>
        rw [hm] at h
        simp only [Option.map_some, Option.some.injEq] at h
        subst h
        exact mergeMatches_same hW hc hch henc hop hm
    · split at h
      · rename_i _ hop
        simp only [List.all_eq_true, beq_iff_eq] at hop
        cases hm : mergeAnd first c.ch with
        | none => rw [hm] at h; simp at h
        | some nch =>
          rw [hm] at h
          simp only [Option.map_some, Option.some.injEq] at h
          subst h
          exact mergeAnd_same hW hc hch hop hm
      · simp at h
  · simp at h

theorem pushDownOr_same (hW : W.Ok step) {f : Cond → Cond} (hf : ∀ x, Same W (f x) x) (c : Cond) :
    Same W (pushDownOr f c) c := by
  unfold pushDownOr
  split
  · rename_i n hn
    exact (hf n).trans (pushStep_same hW c n hn)
  · exact Same.refl _

end
end Normalize