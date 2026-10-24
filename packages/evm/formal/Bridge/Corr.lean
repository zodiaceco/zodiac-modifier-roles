import Bridge.Lemmas

/-!
# Correspondence of results and loops

`Rel r x`: the contract's result `r` and the world's `x` agree. The loops of
`evaluate` (`_and`/`_matches`, `_or`, the array iterators) relate to
`seqT`/`orT` child by child (`Corr`).
-/

namespace Bridge
open DecoderFaithfulness DecoderFaithfulness.Roles Normalize Evaluate

/-- What is assumed of the outside: the external calls never report `Ok`
    as a failure, nor a status that reads as a revert. -/
structure EnvOk (env : Env) : Prop where
  scale : ∀ cv n, (env.scale cv n).1 ≠ revert
  custom : ∀ cv l sz vals s, env.customCall cv l sz vals = .inl s → s ≠ sOk ∧ s ≠ revert
  ratio : ∀ cv vals, env.ratio cv vals ≠ revert

theorem sOk_ne_revert : sOk ≠ revert := by decide

theorem Rel.ok (cons : List Consumption) (sl : Slots) :
    Rel (Evaluate.ok cons sl) (some (toMap cons), sl) := by
  refine ⟨rfl, ?_⟩
  simp [Evaluate.ok]

theorem Rel.violation {s : Nat} (h1 : s ≠ sOk) (h2 : s ≠ revert) (sl : Slots) :
    Rel (violation s sl) (none, sl) := by
  simp [Rel, Evaluate.violation, h1, h2]

theorem Rel.result {s : Nat} (h : s ≠ revert) (cons : List Consumption) (sl : Slots) :
    Rel (result s cons sl) (if s = sOk then some (toMap cons) else none, sl) := by
  unfold Evaluate.result
  by_cases hs : s = sOk
  · simp only [hs, ite_true]; exact Rel.ok cons sl
  · simp only [hs, ite_false]; exact Rel.violation hs h sl

theorem Rel.status_ne {r : Res} {x : Option CM × Slots} (h : Rel r x) : r.status ≠ revert := by
  obtain ⟨-, h2⟩ := h
  split at h2
  · rename_i hs; rw [hs]; exact sOk_ne_revert
  · exact h2.1

/-- A result that passes or fails like `x`, as a world result. -/
theorem Rel.eq {r : Res} {x : Option CM × Slots} (h : Rel r x) :
    x = (if r.status = sOk then some (toMap r.cons) else none, r.slots) := by
  obtain ⟨h1, h2⟩ := h
  rcases x with ⟨x1, x2⟩
  simp only at h1 h2
  subst h1
  split at h2
  · rename_i hs; simp [hs, h2]
  · rename_i hs; simp [hs, h2.2]

/-! ## Slots

Besides `Rel`, each run keeps the Pluck slots sound for Zips: every slot
location it writes decodes as the slot's layout (`WV`), and once it passes,
the slots its `za` analysis promises are written (`Inv`). -/

/-- How a slot analysis of one node maps the written slots. -/
abbrev AF := (Nat → Bool) → Option (Nat → Bool)

/-- Children in order (`zaSeq`). -/
def seqA : List AF → AF
  | [] => some
  | α :: αs => fun A => (α A).bind (seqA αs)

/-- The slots every branch writes (`zaOr`). -/
def orA : List AF → AF
  | [] => fun _ => some fun _ => false
  | [α] => α
  | α :: α' :: αs => fun A => (α A).bind fun a => (orA (α' :: αs) A).map fun b j => a j && b j

/-- A run that agrees with the world (`Rel`), writes only sound slot
    locations, and, when it passes, leaves the slots `B` sound. -/
def Good (data : Calldata) (P : Nat → Option Condition) (r : Res) (x : Option CM × Slots) (sl : Slots)
    (B : Nat → Bool) : Prop :=
  Rel r x ∧ WV data P sl r.slots ∧ (r.status = sOk → Inv data P B r.slots)

theorem Good.rel {data : Calldata} {P : Nat → Option Condition} {r : Res} {x : Option CM × Slots}
    {sl : Slots} {B : Nat → Bool} (h : Good data P r x sl B) : Rel r x := h.1

theorem Good.ok (data : Calldata) (P : Nat → Option Condition) {A : Nat → Bool} (cons : List Consumption)
    {sl : Slots} (h : Inv data P A sl) : Good data P (Evaluate.ok cons sl) (some (toMap cons), sl) sl A :=
  ⟨Rel.ok cons sl, WV.refl data P sl, fun _ => h⟩

theorem Good.violation (data : Calldata) (P : Nat → Option Condition) {s : Nat} (h1 : s ≠ sOk)
    (h2 : s ≠ revert) (sl : Slots) (B : Nat → Bool) : Good data P (violation s sl) (none, sl) sl B :=
  ⟨Rel.violation h1 h2 sl, WV.refl data P sl, fun h => absurd h (by simpa [Evaluate.violation] using h1)⟩

/-- A run that changes no slot: `Rel` is all there is to show. -/
theorem Good.of_keeps {data : Calldata} {P : Nat → Option Condition} {r : Res} {x : Option CM × Slots}
    {sl : Slots} {A : Nat → Bool} (h : Rel r x) (hk : r.slots = sl) (hA : Inv data P A sl) :
    Good data P r x sl A := by
  refine ⟨h, ?_, fun _ => by rw [hk]; exact hA⟩
  rw [hk]; exact WV.refl data P sl

section
variable (env : Env) (data : Calldata) (P : Nat → Option Condition)

/-- Child by child: each contract run corresponds to the world thunk (with
    `n` slots), for its slot analysis. -/
inductive Corr (n fuel : Nat) : List (Condition × Nat) → List T → List AF → Prop
  | nil : Corr n fuel [] [] []
  | cons {p : Condition × Nat} {t : T} {α : AF} {ps ts αs} :
      (∀ A B, α A = some B → ∀ cons sl, Inv data P A sl →
        Good data P (evalC env data n fuel p.2 p.1 cons sl) (t sl (toMap cons)) sl B) →
      Corr n fuel ps ts αs → Corr n fuel (p :: ps) (t :: ts) (α :: αs)

theorem seqLoop_rel {n fuel : Nat} : ∀ (ps : List (Condition × Nat)) (ts : List T) (αs : List AF),
    Corr env data P n fuel ps ts αs → ∀ A B, seqA αs A = some B → ∀ cons sl, Inv data P A sl →
    Good data P (seqLoop env data n fuel ps cons sl) (seqT ts sl (toMap cons)) sl B
  | [], [], [], _, A, B, hB, cons, sl, hA => by
    rw [seqLoop]; simp only [seqA, Option.some.injEq] at hB; subst hB; exact Good.ok data P cons hA
  | [], _ :: _, _, h, _, _, _, _, _, _ => by cases h
  | _ :: _, [], _, h, _, _, _, _, _, _ => by cases h
  | [], [], _ :: _, h, _, _, _, _, _, _ => by cases h
  | _ :: _, _ :: _, [], h, _, _, _, _, _, _ => by cases h
  | (d, l) :: ps, t :: ts, α :: αs, h, A, B, hB, cons, sl, hA => by
    cases h with
    | cons hp hrest =>
      simp only [seqA] at hB
      obtain ⟨A1, hA1, hB1⟩ := Option.bind_eq_some_iff.1 hB
      rw [seqLoop, seqT_cons]
      have h1 := hp A A1 hA1 cons sl hA
      have hne := h1.1.status_ne
      rw [h1.1.eq]
      by_cases hs : (evalC env data n fuel l d cons sl).status = sOk
      · simp only [hs, ite_true, ne_eq, not_true_eq_false, ite_false, bindR_some]
        have h2 := seqLoop_rel ps ts αs hrest A1 B hB1 (evalC env data n fuel l d cons sl).cons _ (h1.2.2 hs)
        exact ⟨h2.1, h1.2.1.trans h2.2.1, h2.2.2⟩
      · simp only [hs, ite_false, ne_eq, not_false_eq_true, ite_true, bindR_none]
        refine ⟨?_, h1.2.1, fun h => absurd h hs⟩
        simp only [Rel, if_neg hs]
        simp [hne]

theorem orLoop_rel {n fuel : Nat} (loc : Nat) : ∀ {cs : List Condition} {ts αs},
    Corr env data P n fuel (cs.map (·, loc)) ts αs → ∀ A B, orA αs A = some B → ∀ cons sl,
    Inv data P A sl → Good data P (orLoop env data n fuel cs loc cons sl) (orT ts sl (toMap cons)) sl B
  | [], [], [], _, _, B, _, cons, sl, _ => by
    rw [orLoop]; exact Good.violation data P (by decide) (by decide) sl B
  | [], _ :: _, _, h, _, _, _, _, _, _ => by cases h
  | [], [], _ :: _, h, _, _, _, _, _, _ => by cases h
  | c :: cs, ts, αs, h, A, B, hB, cons, sl, hA => by
    cases h with
    | cons hp hrest =>
      rename_i t α ts' αs'
      rw [orLoop]
      simp only [orT]
      -- the branch's own analysis, and what it promises of the rest
      obtain ⟨a, ha, hsub, hrestB⟩ : ∃ a, α A = some a ∧ (∀ k, B k = true → a k = true) ∧
          (αs' ≠ [] → ∃ b, orA αs' A = some b ∧ ∀ k, B k = true → b k = true) := by
        cases αs' with
        | nil => exact ⟨B, hB, fun _ h => h, fun h => absurd rfl h⟩
        | cons α' αs'' =>
          simp only [orA] at hB
          obtain ⟨a, ha, hb⟩ := Option.bind_eq_some_iff.1 hB
          obtain ⟨b, hb2, rfl⟩ := Option.map_eq_some_iff.1 hb
          refine ⟨a, ha, fun k h => ?_, fun _ => ⟨b, hb2, fun k h => ?_⟩⟩
          · simp only [Bool.and_eq_true] at h; exact h.1
          · simp only [Bool.and_eq_true] at h; exact h.2
      have h1 := hp A a ha cons sl hA
      have hne := h1.1.status_ne
      rw [h1.1.eq]
      by_cases hs : (evalC env data n fuel loc c cons sl).status = sOk
      · simp only [hs, true_or, ite_true]
        refine ⟨by simp [Rel, hs], h1.2.1, fun _ => (h1.2.2 hs).mono hsub⟩
      · simp only [hs, false_or, hne, ite_false]
        have hA' := hA.wv h1.2.1
        cases cs with
        | nil =>
          cases hrest
          rw [orLoop]
          simp only [orT]
          exact ⟨Rel.violation (by decide) (by decide) _, h1.2.1, fun h => by
            simp [Evaluate.violation, sOrViolation, sOk] at h⟩
        | cons c' cs' =>
          cases hrest with
          | cons hp' hrest' =>
            obtain ⟨b, hb, hsub'⟩ := hrestB (by simp)
            have h2 := orLoop_rel loc (cs := c' :: cs') (.cons hp' hrest') A b hb cons _ hA'
            exact ⟨h2.1, h1.2.1.trans h2.2.1, fun h => (h2.2.2 h).mono hsub'⟩

theorem everyLoop_rel {n fuel : Nat} (c : Condition) (α : AF) : ∀ {locs : List Nat} {ts},
    Corr env data P n fuel (locs.map (c, ·)) ts (locs.map fun _ => α) → ∀ A B, α A = some B →
    ∀ cons sl, Inv data P A sl →
    Good data P (everyLoop env data n fuel c locs cons sl) (seqT ts sl (toMap cons)) sl A
  | [], [], _, A, _, _, cons, sl, hA => by rw [everyLoop]; exact Good.ok data P cons hA
  | [], _ :: _, h, _, _, _, _, _, _ => by cases h
  | l :: locs, ts, h, A, B, hB, cons, sl, hA => by
    cases h with
    | cons hp hrest =>
      rw [everyLoop, seqT_cons]
      have h1 := hp A B hB cons sl hA
      have hne := h1.1.status_ne
      rw [h1.1.eq]
      by_cases hs : (evalC env data n fuel l c cons sl).status = sOk
      · simp only [hs, ite_true, ne_eq, not_true_eq_false, ite_false, bindR_some, hne]
        have h2 := everyLoop_rel c α hrest A B hB (evalC env data n fuel l c cons sl).cons _ (hA.wv h1.2.1)
        exact ⟨h2.1, h1.2.1.trans h2.2.1, h2.2.2⟩
      · simp only [hs, ite_false, hne, ne_eq, not_false_eq_true, ite_true, bindR_none]
        refine ⟨by simp [Rel, sNotEveryArrayElementPasses, sOk, revert], h1.2.1, fun h => ?_⟩
        simp [sNotEveryArrayElementPasses, sOk] at h

theorem someLoop_rel {n fuel : Nat} (c : Condition) (α : AF) : ∀ {locs : List Nat} {ts},
    Corr env data P n fuel (locs.map (c, ·)) ts (locs.map fun _ => α) → ∀ A B, α A = some B →
    ∀ cons sl, Inv data P A sl →
    Good data P (someLoop env data n fuel c locs cons sl) (orT ts sl (toMap cons)) sl B
  | [], [], _, _, B, _, cons, sl, _ => by
    rw [someLoop]; exact Good.violation data P (by decide) (by decide) sl B
  | [], _ :: _, h, _, _, _, _, _, _ => by cases h
  | l :: locs, ts, h, A, B, hB, cons, sl, hA => by
    cases h with
    | cons hp hrest =>
      rw [someLoop]
      simp only [orT]
      have h1 := hp A B hB cons sl hA
      have hne := h1.1.status_ne
      rw [h1.1.eq]
      by_cases hs : (evalC env data n fuel l c cons sl).status = sOk
      · simp only [hs, true_or, ite_true]
        exact ⟨by simp [Rel, hs], h1.2.1, fun _ => h1.2.2 hs⟩
      · simp only [hs, false_or, hne, ite_false]
        have h2 := someLoop_rel c α hrest A B hB cons _ (hA.wv h1.2.1)
        exact ⟨h2.1, h1.2.1.trans h2.2.1, h2.2.2⟩

end

/-! ## The analysis `za` as list folds -/

theorem za_eq (c : Cond) (A : Nat → Bool) :
    za c A =
      if c.op = 14 then some fun j => j == c.cv.headD 0 % 256 || A j
      else if c.op = 10 ∨ c.op = 11 then
        if (zipKeys c.cv).all A then (zaFields c.ch A).map fun A' => if c.op = 10 then A' else A
        else none
      else if c.op = 2 then zaOr c.ch A
      else if c.op = 6 ∨ c.op = 7 then (zaFirst c.ch A).map fun A' => if c.op = 6 then A' else A
      else if c.op = 1 ∨ c.op = 5 ∨ c.op = 8 then zaSeq c.ch A
      else if c.op = 13 then zaFirst c.ch A
      else some A := by
  rcases c with ⟨e, o, cv, ch⟩; rw [za]

theorem zaSeq_eq : ∀ (cs : List Cond) (A : Nat → Bool), zaSeq cs A = seqA (cs.map za) A
  | [], A => by rw [zaSeq]; rfl
  | c :: cs, A => by
    rw [zaSeq]; simp only [List.map_cons, seqA]
    congr 1; funext B; exact zaSeq_eq cs B

theorem zaOr_eq : ∀ (cs : List Cond) (A : Nat → Bool), zaOr cs A = orA (cs.map za) A
  | [], A => by rw [zaOr]; rfl
  | [c], A => by rw [zaOr]; rfl
  | c :: c' :: cs, A => by
    rw [zaOr]; simp only [List.map_cons, orA]
    congr 1; funext a
    rw [zaOr_eq (c' :: cs) A]; rfl

theorem zaFirst_cons (x : Cond) (xs : List Cond) (A : Nat → Bool) : zaFirst (x :: xs) A = za x A := by
  rw [zaFirst]

theorem zaFields_cons (t : Cond) (xs : List Cond) (A : Nat → Bool) :
    zaFields (t :: xs) A = zaSeq t.ch A := by
  rcases t with ⟨e, o, cv, fs⟩; rw [zaFields]

/-- A node that is no Pluck, Zip or container leaves the slots it starts with. -/
theorem za_plain {c : Cond} (h14 : c.op ≠ 14) (h10 : c.op ≠ 10) (h11 : c.op ≠ 11) (h2 : c.op ≠ 2)
    (h6 : c.op ≠ 6) (h7 : c.op ≠ 7) (h1 : c.op ≠ 1) (h5 : c.op ≠ 5) (h8 : c.op ≠ 8) (h13 : c.op ≠ 13)
    (A : Nat → Bool) : za c A = some A := by
  rw [za_eq]; simp [h14, h10, h11, h2, h6, h7, h1, h5, h8, h13]

/-- The slots of a Pluck (`plucks`). -/
theorem plucks_eq (c : Cond) :
    plucks c = (if c.op = 14 then [c.cv.headD 0 % 256] else []) ++ c.ch.flatMap plucks := by
  rcases c with ⟨e, o, cv, ch⟩
  rw [plucks]
  congr 1
  simp only
  conv => rhs; rw [← List.attach_map_subtype_val ch]
  rw [List.flatMap_map]

theorem plucks_child {c x : Cond} (hx : x ∈ c.ch) {k : Nat} (hk : k ∈ plucks x) : k ∈ plucks c := by
  rw [plucks_eq c]
  exact List.mem_append_right _ (List.mem_flatMap.2 ⟨x, hx, hk⟩)

end Bridge
