import Bridge.ReadLeaves

/-!
# The evaluator's loops

`Corr f ps ts`: child by child, the evaluator (with fuel `f`) on node `p.1`
at location `p.2` agrees with thunk `t`, whenever it does not revert. Then
`_and`/`_matches` (`seqLoop`), `_or` (`orLoop`), the array iterators and the
Zip iterator agree with `seqT`/`orT` over the thunks, whenever they do not
revert.
-/

namespace Bridge
open DecoderFaithfulness DecoderFaithfulness.Roles Normalize Evaluate

section
variable (env : Env) (data : Calldata) (n : Nat)

theorem fuel_succ {c : Cond} {fuel : Nat} (h : height c < fuel) : ∃ f, fuel = f + 1 ∧ height c ≤ f :=
  ⟨fuel - 1, by omega, by omega⟩

theorem height_pos (c : Cond) : 0 < height c := by rcases c; simp [height]

theorem evalC_pass (f l : Nat) (d : Condition) (cons : List Consumption) (sl : Slots)
    (hd : d.operator = .Pass) : evalC env data n (f + 1) l d cons sl = Evaluate.ok cons sl := by
  rw [evalC, hd]

theorem evalC_and (f l : Nat) (d : Condition) (cons : List Consumption) (sl : Slots)
    (hd : d.operator = .And) :
    evalC env data n (f + 1) l d cons sl = seqLoop env data n f (d.children.map (·, l)) cons sl := by
  rw [evalC, hd]

theorem evalC_or (f l : Nat) (d : Condition) (cons : List Consumption) (sl : Slots)
    (hd : d.operator = .Or) :
    evalC env data n (f + 1) l d cons sl = orLoop env data n f d.children l cons sl := by
  rw [evalC, hd]

theorem evalC_matches (f l : Nat) (d : Condition) (cons : List Consumption) (sl : Slots)
    (hd : d.operator = .Matches) :
    evalC env data n (f + 1) l d cons sl =
      match leadingCheck data (if l > 0 ∧ d.encoding = .AbiEncoded then l + 32 else l) d.compValue with
      | some s => violation s sl
      | none =>
        match childrenE data ((if l > 0 ∧ d.encoding = .AbiEncoded then l + 32 else l) + d.leadingBytes) d with
        | .inl s => violation s sl
        | .inr none => violation sCalldataOverflow sl
        | .inr (some locs) =>
          if d.children.length ≠ locs.length then violation sParameterNotAMatch sl
          else seqLoop env data n f (d.children.zip locs) cons sl := by
  rw [evalC, hd]; rfl

theorem evalC_iter (f l : Nat) (d : Condition) (cons : List Consumption) (sl : Slots)
    (every : Bool) (hd : d.operator = if every then .ArrayEvery else .ArraySome) :
    evalC env data n (f + 1) l d cons sl =
      match childrenE data l d with
      | .inl s => violation s sl
      | .inr none => violation sCalldataOverflow sl
      | .inr (some locs) =>
        match d.children with
        | [] => if locs = [] then
                  (if d.operator = .ArrayEvery then Evaluate.ok cons sl
                   else violation sNoArrayElementPasses sl)
                else violation revert sl
        | ch :: _ =>
          if d.operator = .ArrayEvery then everyLoop env data n f ch locs cons sl
          else someLoop env data n f ch locs cons sl := by
  rw [evalC]
  cases every <;> simp only [hd, Bool.false_eq_true, ite_false, ite_true] <;> rfl

theorem evalC_tail (f l : Nat) (d : Condition) (cons : List Consumption) (sl : Slots)
    (hd : d.operator = .ArrayTailMatches) :
    evalC env data n (f + 1) l d cons sl =
      match childrenE data l d with
      | .inl s => violation s sl
      | .inr none => violation sCalldataOverflow sl
      | .inr (some locs) =>
        if locs.length < d.children.length then violation sParameterNotAMatch sl
        else seqLoop env data n f (d.children.zip (locs.drop (locs.length - d.children.length)))
          cons sl := by
  rw [evalC, hd]; rfl

theorem evalC_slice (f l : Nat) (d : Condition) (cons : List Consumption) (sl : Slots)
    (hd : d.operator = .Slice) :
    evalC env data n (f + 1) l d cons sl =
      match cvAt d.compValue 2 with
      | none => violation revert sl
      | some sz =>
        if d.inlined = false ∧ l + 32 > data.length then violation sCalldataOverflow sl
        else
          if shiftOf d.compValue + sz > (if d.inlined then d.size else load data l) then
            violation sCalldataOverflow sl
          else
            match d.children with
            | [] => violation revert sl
            | ch :: _ =>
              evalC env data n f (l + (if d.inlined then 0 else 32) + shiftOf d.compValue)
                (ch.withSize sz) cons sl := by
  rw [evalC, hd]; rfl

theorem evalC_zip (f l : Nat) (d : Condition) (cons : List Consumption) (sl : Slots) (every : Bool)
    (hd : d.operator = if every then .ZipEvery else .ZipSome) :
    evalC env data n (f + 1) l d cons sl =
      match d.children with
      | [] => violation revert sl
      | t :: _ =>
        match zipLocs data n d.compValue t.children sl with
        | .inl s => violation s sl
        | .inr (locss, len) => zipLoop env data n f every t.children locss len 0 cons cons sl := by
  rw [evalC]
  cases every <;> simp only [hd, Bool.false_eq_true, ite_false, ite_true] <;> rfl

theorem childrenLoop_length (data : Calldata) (loc : Nat) (f : Nat → Condition) :
    ∀ (k i h : Nat) (locs : List Nat), childrenLoop data loc f k i h = some locs → locs.length = k
  | 0, _, _, locs, h => by simp [childrenLoop] at h; simp [← h]
  | k + 1, i, h, locs, hk => by
    simp only [childrenLoop] at hk
    cases hfi : (f i).inlined <;> simp only [hfi, Bool.false_eq_true, ite_false, ite_true] at hk <;>
    · split at hk
      · simp at hk
      · obtain ⟨rest, hrest, rfl⟩ := Option.map_eq_some_iff.1 hk
        simp [childrenLoop_length data loc f k _ _ rest hrest]

theorem assign_struct {V : Type} (d : V) : ∀ (cs : List Cond) (fs : List V) (v : V),
    (∀ x ∈ cs, isStruct x = true) → cs.length ≤ fs.length → assign d cs fs v = cs.zip fs
  | [], _, _, _, _ => by simp [assign]
  | _ :: _, [], _, _, h => by simp at h
  | c :: cs, f :: fs, v, hs, hl => by
    simp only [assign, hs c (by simp), if_true, List.headD_cons, List.tail_cons, List.zip_cons_cons]
    rw [assign_struct d cs fs v (fun x hx => hs x (by simp [hx])) (by simp at hl; omega)]

inductive Corr (f : Nat) : List (Condition × Nat) → List T → Prop
  | nil : Corr f [] []
  | cons {p : Condition × Nat} {t : T} {ps ts} :
      (∀ cons sl, (evalC env data n f p.2 p.1 cons sl).status ≠ revert →
        Rel (evalC env data n f p.2 p.1 cons sl) (t sl (toMap cons))) →
      Corr f ps ts → Corr f (p :: ps) (t :: ts)

theorem Corr.of_map {α} {f : Nat} (g : α → Condition × Nat) (h : α → T) :
    ∀ {l : List α}, (∀ x ∈ l, ∀ cons sl, (evalC env data n f (g x).2 (g x).1 cons sl).status ≠ revert →
      Rel (evalC env data n f (g x).2 (g x).1 cons sl) (h x sl (toMap cons))) →
    Corr env data n f (l.map g) (l.map h)
  | [], _ => .nil
  | x :: xs, hx => .cons (hx x (by simp)) (Corr.of_map g h fun y hy => hx y (by simp [hy]))

theorem Rel.fail_of {r : Res} (h1 : r.status ≠ sOk) (h2 : r.status ≠ revert) : Rel r (none, r.slots) :=
  ⟨rfl, by simp [h1, h2]⟩

theorem seqLoop_rel {f : Nat} : ∀ {ps : List (Condition × Nat)} {ts : List T}, Corr env data n f ps ts →
    ∀ cons sl, (seqLoop env data n f ps cons sl).status ≠ revert →
    Rel (seqLoop env data n f ps cons sl) (seqT ts sl (toMap cons))
  | [], [], .nil, cons, sl, _ => by rw [seqLoop]; exact Rel.ok cons sl
  | (d, l) :: ps, t :: ts, .cons hp hr, cons, sl, hne => by
    rw [seqLoop] at hne ⊢
    rw [seqT_cons]
    by_cases hs : (evalC env data n f l d cons sl).status = sOk
    · have h1 := hp cons sl (by rw [hs]; exact sOk_ne_revert)
      simp only [hs, ne_eq, not_true_eq_false, ite_false] at hne ⊢
      rw [h1.eq, if_pos hs, bindR_some]
      exact seqLoop_rel hr _ _ hne
    · simp only [hs, ne_eq, not_false_eq_true, ite_true] at hne ⊢
      have h1 := hp cons sl hne
      rw [h1.eq, if_neg hs, bindR_none]
      exact Rel.fail_of hs hne

theorem orLoop_rel {f : Nat} (loc : Nat) : ∀ {cs : List Condition} {ts : List T},
    Corr env data n f (cs.map (·, loc)) ts → ∀ cons sl,
    (orLoop env data n f cs loc cons sl).status ≠ revert →
    Rel (orLoop env data n f cs loc cons sl) (orT ts sl (toMap cons))
  | [], [], .nil, cons, sl, _ => by
    rw [orLoop]; exact Rel.violation (by decide) (by decide) sl
  | c :: cs, t :: ts, .cons hp hr, cons, sl, hne => by
    rw [orLoop] at hne ⊢
    simp only [orT]
    by_cases hs : (evalC env data n f loc c cons sl).status = sOk
    · have h1 := hp cons sl (by rw [hs]; exact sOk_ne_revert)
      simp only [hs, true_or, ite_true] at hne ⊢
      rw [h1.eq, if_pos hs]
      exact ⟨rfl, by simp [hs]⟩
    · by_cases hr' : (evalC env data n f loc c cons sl).status = revert
      · simp only [hr', or_true, ite_true] at hne; exact absurd rfl hne
      · have h1 := hp cons sl hr'
        simp only [hs, hr', or_self, ite_false] at hne ⊢
        rw [h1.eq, if_neg hs]
        exact orLoop_rel loc hr _ _ hne

theorem everyLoop_rel {f : Nat} (c : Condition) : ∀ {locs : List Nat} {ts : List T},
    Corr env data n f (locs.map (c, ·)) ts → ∀ cons sl,
    (everyLoop env data n f c locs cons sl).status ≠ revert →
    Rel (everyLoop env data n f c locs cons sl) (seqT ts sl (toMap cons))
  | [], [], .nil, cons, sl, _ => by rw [everyLoop]; exact Rel.ok cons sl
  | l :: locs, t :: ts, .cons hp hr, cons, sl, hne => by
    rw [everyLoop] at hne ⊢
    rw [seqT_cons]
    by_cases hr' : (evalC env data n f l c cons sl).status = revert
    · simp only [hr', ite_true] at hne; exact absurd rfl hne
    · have h1 := hp cons sl hr'
      by_cases hs : (evalC env data n f l c cons sl).status = sOk
      · simp only [hr', hs, ite_false, ne_eq, not_true_eq_false] at hne ⊢
        rw [h1.eq, if_pos hs, bindR_some]
        exact everyLoop_rel c hr _ _ hne
      · simp only [hr', hs, ite_false, ne_eq, not_false_eq_true, ite_true]
        rw [h1.eq, if_neg hs, bindR_none]
        exact ⟨rfl, by simp [sNotEveryArrayElementPasses, sOk, revert]⟩

theorem someLoop_rel {f : Nat} (c : Condition) : ∀ {locs : List Nat} {ts : List T},
    Corr env data n f (locs.map (c, ·)) ts → ∀ cons sl,
    (someLoop env data n f c locs cons sl).status ≠ revert →
    Rel (someLoop env data n f c locs cons sl) (orT ts sl (toMap cons))
  | [], [], .nil, cons, sl, _ => by
    rw [someLoop]; exact Rel.violation (by decide) (by decide) sl
  | l :: locs, t :: ts, .cons hp hr, cons, sl, hne => by
    rw [someLoop] at hne ⊢
    simp only [orT]
    by_cases hs : (evalC env data n f l c cons sl).status = sOk
    · have h1 := hp cons sl (by rw [hs]; exact sOk_ne_revert)
      simp only [hs, true_or, ite_true] at hne ⊢
      rw [h1.eq, if_pos hs]
      exact ⟨rfl, by simp [hs]⟩
    · by_cases hr' : (evalC env data n f l c cons sl).status = revert
      · simp only [hr', or_true, ite_true] at hne; exact absurd rfl hne
      · have h1 := hp cons sl hr'
        simp only [hs, hr', or_self, ite_false] at hne ⊢
        rw [h1.eq, if_neg hs]
        exact someLoop_rel c hr _ _ hne

/-- A Zip's elements: element `i` of the run agrees with thunk `el i`. -/
def ElemCorr (f : Nat) (fields : List Condition) (locss : List (List Nat)) (el : Nat → T) : Prop :=
  ∀ i cons sl, (seqLoop env data n f (fields.zip (locss.map fun ls => ls.getD i 0)) cons sl).status ≠ revert →
    Rel (seqLoop env data n f (fields.zip (locss.map fun ls => ls.getD i 0)) cons sl) (el i sl (toMap cons))

theorem zipLoop_every_rel {f : Nat} (fields : List Condition) (locss : List (List Nat)) (el : Nat → T)
    (base : List Consumption) (h : ElemCorr env data n f fields locss el) :
    ∀ k i cons sl, (zipLoop env data n f true fields locss k i base cons sl).status ≠ revert →
    Rel (zipLoop env data n f true fields locss k i base cons sl)
      (seqT ((List.range' i k).map el) sl (toMap cons))
  | 0, i, cons, sl, _ => by
    rw [zipLoop]; simp only [ite_true, List.range'_zero, List.map_nil]; exact Rel.ok cons sl
  | k + 1, i, cons, sl, hne => by
    rw [zipLoop] at hne ⊢
    simp only [List.range'_succ, List.map_cons, seqT_cons, ite_true] at hne ⊢
    by_cases hr' : (seqLoop env data n f (fields.zip (locss.map fun ls => ls.getD i 0)) cons sl).status = revert
    · simp only [hr', ite_true] at hne; exact absurd rfl hne
    · have h1 := h i cons sl hr'
      by_cases hs : (seqLoop env data n f (fields.zip (locss.map fun ls => ls.getD i 0)) cons sl).status = sOk
      · simp only [hr', hs, ite_false, ne_eq, not_true_eq_false] at hne ⊢
        rw [h1.eq, if_pos hs, bindR_some]
        exact zipLoop_every_rel fields locss el base h k (i + 1) _ _ hne
      · simp only [hr', hs, ite_false, ne_eq, not_false_eq_true, ite_true]
        rw [h1.eq, if_neg hs, bindR_none]
        exact ⟨rfl, by simp [sNotEveryZippedElementPasses, sOk, revert]⟩

theorem zipLoop_some_rel {f : Nat} (fields : List Condition) (locss : List (List Nat)) (el : Nat → T)
    (h : ElemCorr env data n f fields locss el) :
    ∀ k i cons sl, (zipLoop env data n f false fields locss k i cons cons sl).status ≠ revert →
    Rel (zipLoop env data n f false fields locss k i cons cons sl)
      (orT ((List.range' i k).map el) sl (toMap cons))
  | 0, i, cons, sl, _ => by
    rw [zipLoop]; simpa [orT] using Rel.violation (s := sNoZippedElementPasses) (by decide) (by decide) sl
  | k + 1, i, cons, sl, hne => by
    rw [zipLoop] at hne ⊢
    simp only [List.range'_succ, List.map_cons, orT, Bool.false_eq_true, ite_false] at hne ⊢
    by_cases hr' : (seqLoop env data n f (fields.zip (locss.map fun ls => ls.getD i 0)) cons sl).status = revert
    · simp only [hr', ite_true] at hne; exact absurd rfl hne
    · have h1 := h i cons sl hr'
      by_cases hs : (seqLoop env data n f (fields.zip (locss.map fun ls => ls.getD i 0)) cons sl).status = sOk
      · have hsr : (sOk = revert) = False := by simp [sOk, revert]
        simp only [hs, hsr, ite_false, ite_true] at hne ⊢
        rw [h1.eq, if_pos hs]
        exact ⟨rfl, by simp only [ite_true, if_pos hs]⟩
      · simp only [hr', hs, ite_false] at hne ⊢
        rw [h1.eq, if_neg hs]
        exact zipLoop_some_rel fields locss el h k (i + 1) _ _ hne

end
end Bridge
