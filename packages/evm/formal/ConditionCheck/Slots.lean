import ConditionCheck.Flat

/-!
# Pluck slots

`ZipSome`/`ZipEvery` read array locations, and `WithinRatio` values, from the
slots `Pluck` nodes write (`context.pluckedLocations` / `pluckedValues`). An
unwritten slot reads as 0: a Zip would decode an array at calldata location 0.
Integrity rejects trees where that can happen (`_validatePluckAssignments`);
the `...Packed` setters don't.

* `assigned` transcribes `_validatePluckAssignments`: the slots guaranteed to
  be written once a subtree evaluates successfully, or `none` if a node may
  read an unwritten slot.
* `Run` models the control flow of `ConditionEvaluator.evaluate` with respect
  to slots: which children are evaluated in which order, where evaluation
  stops, and what `_pluck` writes. Leaf results (comparisons, overflows,
  array lengths) are left arbitrary, so `Run` covers every execution.
* `assigned_sound`: if the analysis passes at the root, no execution reads
  an unwritten slot.

The decoder model (`Roles.Eval`) assumes that a slot a Zip reads holds the
location at which a Pluck with that index was evaluated. With this theorem
that assumption reduces to: `Run` matches the evaluator's control flow, and
`_pluck` is the only writer, writing its own location. Unique Pluck indices
are not needed for it: `ZipOK` constrains every Pluck with the slot's index.
-/

namespace ConditionCheck
open DecoderFaithfulness DecoderFaithfulness.Roles

abbrev Slots := Nat → Bool

def SubS (A B : Slots) : Prop := ∀ k, A k = true → B k = true

theorem SubS.refl (A : Slots) : SubS A A := fun _ h => h
theorem SubS.trans {A B C : Slots} (h1 : SubS A B) (h2 : SubS B C) : SubS A C :=
  fun k h => h2 k (h1 k h)

def Slots.add (A : Slots) (k : Nat) : Slots := fun j => j == k || A j

/-- The slots a Zip reads: one per compValue byte. -/
def zipSlots (cv : Bytes) : List Nat := (List.range cv.length).map (cvByte cv)

/-- The slots `WithinRatio` reads (reference and relative). -/
def ratioOk (A : Slots) (cv : Bytes) : Bool := A (cvByte cv 0) && A (cvByte cv 2)

/-- Operators that neither write nor read slots, nor evaluate children. -/
def isPlain (op : Operator) : Bool :=
  !(op == .Pluck || op == .WithinRatio || op == .ZipSome || op == .ZipEvery || op == .Or ||
    op == .And || op == .Matches || op == .ArrayTailMatches || op == .ArraySome ||
    op == .ArrayEvery || op == .Slice)

/-! ## The analysis (`_validatePluckAssignments`) -/

mutual
  def assigned : Condition → Slots → Option Slots
    | ⟨_, op, cs, _, _, _, cv⟩, A =>
      if op = .Pluck then some (A.add (cvByte cv 0))
      else if op = .WithinRatio then (if ratioOk A cv then some A else none)
      else if op = .ZipSome ∨ op = .ZipEvery then
        if (zipSlots cv).all A then
          (assignedFields cs A).map fun A' => if op = .ZipSome then A' else A
        else none
      else if op = .Or then assignedOr cs A
      else if op = .ArraySome ∨ op = .ArrayEvery then
        (assignedFirst cs A).map fun A' => if op = .ArraySome then A' else A
      else if op = .And ∨ op = .Matches ∨ op = .ArrayTailMatches then assignedSeq cs A
      else if op = .Slice then assignedFirst cs A
      else some A

  /-- Children in order, each seeing the slots of its predecessors. -/
  def assignedSeq : List Condition → Slots → Option Slots
    | [], A => some A
    | c :: cs, A => (assigned c A).bind (assignedSeq cs)

  /-- Only slots every branch writes (none for no branches). -/
  def assignedOr : List Condition → Slots → Option Slots
    | [], _ => some fun _ => false
    | [c], A => assigned c A
    | c :: c' :: cs, A =>
      (assigned c A).bind fun a => (assignedOr (c' :: cs) A).map fun b j => a j && b j

  def assignedFirst : List Condition → Slots → Option Slots
    | [], A => some A
    | c :: _, A => assigned c A

  /-- The fields of a Zip (children of its tuple child), in order. -/
  def assignedFields : List Condition → Slots → Option Slots
    | [], A => some A
    | ⟨_, _, fs, _, _, _, _⟩ :: _, A => assignedSeq fs A
end

/-! ## The execution model -/

inductive Outcome where
  | ok | fail | bad
  deriving DecidableEq

mutual
  /-- `Run c A o A'`: evaluating `c` with slots `A` written can end with
      outcome `o` and slots `A'` written. `bad`: a read of an unwritten slot. -/
  inductive Run : Condition → Slots → Outcome → Slots → Prop
    /-- Leaves (comparisons, `Bitmask`, `Custom`, allowances, `Pass`, ...):
        any result, children never evaluated. -/
    | plain {c A o} : isPlain c.operator = true → o ≠ .bad → Run c A o A
    /-- `_pluck`: writes its slot, or fails on overflow first. -/
    | pluckOk {c A} : c.operator = .Pluck → Run c A .ok (A.add (cvByte c.compValue 0))
    | pluckFail {c A} : c.operator = .Pluck → Run c A .fail A
    | ratio {c A o} : c.operator = .WithinRatio → ratioOk A c.compValue = true → o ≠ .bad →
        Run c A o A
    | ratioBad {c A} : c.operator = .WithinRatio → ratioOk A c.compValue = false →
        Run c A .bad A
    /-- `_and`, `_matches`, `_arrayTailMatches`: children in order, stop at
        the first failure. -/
    | seq {c A o A'} : (c.operator = .And ∨ c.operator = .Matches ∨
        c.operator = .ArrayTailMatches) → RunSeq c.children A o A' → Run c A o A'
    /-- Failing before any child (overflow, leading bytes, count mismatch). -/
    | early {c A} : (c.operator = .Matches ∨ c.operator = .ArrayTailMatches ∨
        c.operator = .Slice ∨ c.operator = .ArraySome ∨ c.operator = .ArrayEvery) →
        Run c A .fail A
    /-- `_or`: children in order, stop at the first success. -/
    | or {c A o A'} : c.operator = .Or → RunOr c.children A o A' → Run c A o A'
    /-- `_slice`: the child. -/
    | slice {c A o A'} : c.operator = .Slice → Run (c.children.headD default) A o A' →
        Run c A o A'
    /-- `_arrayIterator`: `children[0]` per element. -/
    | iter {c A o A'} : (c.operator = .ArraySome ∨ c.operator = .ArrayEvery) →
        RunIter (c.operator == .ArraySome) (c.children.headD default) A o A' → Run c A o A'
    /-- `_zipLocations` reads every slot. -/
    | zipBad {c A} : (c.operator = .ZipSome ∨ c.operator = .ZipEvery) →
        (zipSlots c.compValue).all A = false → Run c A .bad A
    | zipEarly {c A} : (c.operator = .ZipSome ∨ c.operator = .ZipEvery) →
        (zipSlots c.compValue).all A = true → Run c A .fail A
    /-- `_zipIterator`: the fields in order per element. -/
    | zip {c A o A'} : (c.operator = .ZipSome ∨ c.operator = .ZipEvery) →
        (zipSlots c.compValue).all A = true →
        RunZip (c.operator == .ZipSome) (zipFields c) A o A' → Run c A o A'

  inductive RunSeq : List Condition → Slots → Outcome → Slots → Prop
    | nil {A} : RunSeq [] A .ok A
    | next {c cs A A1 o A2} : Run c A .ok A1 → RunSeq cs A1 o A2 → RunSeq (c :: cs) A o A2
    | stop {c cs A o A1} : Run c A o A1 → o ≠ .ok → RunSeq (c :: cs) A o A1

  inductive RunOr : List Condition → Slots → Outcome → Slots → Prop
    | nil {A} : RunOr [] A .fail A
    | stop {c cs A o A1} : Run c A o A1 → o ≠ .fail → RunOr (c :: cs) A o A1
    | next {c cs A A1 o A2} : Run c A .fail A1 → RunOr cs A1 o A2 → RunOr (c :: cs) A o A2

  /-- Elements of an array iterator; `sm`: `ArraySome` (stop at the first
      success) or `ArrayEvery` (stop at the first failure). -/
  inductive RunIter : Bool → Condition → Slots → Outcome → Slots → Prop
    | done {sm ch A} : RunIter sm ch A (if sm then .fail else .ok) A
    | stop {sm ch A o A1} : Run ch A o A1 →
        (o = .bad ∨ (sm = true ∧ o = .ok) ∨ (sm = false ∧ o = .fail)) → RunIter sm ch A o A1
    | next {sm ch A o A1 o' A2} : Run ch A o A1 →
        ((sm = true ∧ o = .fail) ∨ (sm = false ∧ o = .ok)) → RunIter sm ch A1 o' A2 →
        RunIter sm ch A o' A2

  /-- Elements of a Zip: each evaluates the fields in order. -/
  inductive RunZip : Bool → List Condition → Slots → Outcome → Slots → Prop
    | done {sm fs A} : RunZip sm fs A (if sm then .fail else .ok) A
    | stop {sm fs A o A1} : RunSeq fs A o A1 →
        (o = .bad ∨ (sm = true ∧ o = .ok) ∨ (sm = false ∧ o = .fail)) → RunZip sm fs A o A1
    | next {sm fs A o A1 o' A2} : RunSeq fs A o A1 →
        ((sm = true ∧ o = .fail) ∨ (sm = false ∧ o = .ok)) → RunZip sm fs A1 o' A2 →
        RunZip sm fs A o' A2
end

/-! ## Soundness -/

theorem assigned_eq (c : Condition) (A : Slots) :
    assigned c A =
      if c.operator = .Pluck then some (A.add (cvByte c.compValue 0))
      else if c.operator = .WithinRatio then (if ratioOk A c.compValue then some A else none)
      else if c.operator = .ZipSome ∨ c.operator = .ZipEvery then
        if (zipSlots c.compValue).all A then
          (assignedFields c.children A).map fun A' => if c.operator = .ZipSome then A' else A
        else none
      else if c.operator = .Or then assignedOr c.children A
      else if c.operator = .ArraySome ∨ c.operator = .ArrayEvery then
        (assignedFirst c.children A).map fun A' => if c.operator = .ArraySome then A' else A
      else if c.operator = .And ∨ c.operator = .Matches ∨ c.operator = .ArrayTailMatches then
        assignedSeq c.children A
      else if c.operator = .Slice then assignedFirst c.children A
      else some A := by
  rcases c with ⟨e, op, cs, i, sz, lb, cv⟩
  rw [assigned]

theorem assigned_plain {c : Condition} {A : Slots} (h : isPlain c.operator = true) :
    assigned c A = some A := by
  rw [assigned_eq]
  rcases c with ⟨e, op, cs, i, sz, lb, cv⟩
  cases op <;> simp_all [isPlain]

theorem assignedFirst_eq (cs : List Condition) (A : Slots) :
    assignedFirst cs A = assigned (cs.headD default) A := by
  cases cs with
  | nil => rfl
  | cons c _ => rfl

theorem assignedFields_eq (cs : List Condition) (A : Slots) :
    assignedFields cs A = assignedSeq (cs.headD default).children A := by
  cases cs with
  | nil => rfl
  | cons c _ => rcases c with ⟨e, op, fs, i, sz, lb, cv⟩; rfl

theorem assignedOr_cons {c : Condition} {cs : List Condition} {A0 R : Slots}
    (h : assignedOr (c :: cs) A0 = some R) :
    ∃ a, assigned c A0 = some a ∧ SubS R a ∧
      (cs ≠ [] → ∃ b, assignedOr cs A0 = some b ∧ SubS R b) := by
  cases cs with
  | nil => exact ⟨R, h, SubS.refl R, fun hne => absurd rfl hne⟩
  | cons c' cs =>
    simp only [assignedOr, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨a, ha, b, hb, rfl⟩ := h
    refine ⟨a, ha, fun k hk => by simp at hk; exact hk.1, fun _ => ⟨b, hb, fun k hk => ?_⟩⟩
    simp at hk; exact hk.2

theorem assignedOr_rest {c : Condition} {cs : List Condition} {A0 R : Slots}
    (h : assignedOr (c :: cs) A0 = some R) :
    ∃ b, assignedOr cs A0 = some b ∧ (cs ≠ [] → SubS R b) := by
  cases cs with
  | nil => exact ⟨_, rfl, fun hne => absurd rfl hne⟩
  | cons c' cs =>
    obtain ⟨_, _, _, hcs⟩ := assignedOr_cons h
    obtain ⟨b, hb, hRb⟩ := hcs (by simp)
    exact ⟨b, hb, fun _ => hRb⟩

mutual
  theorem run_sound : ∀ {c A o A'}, Run c A o A' → ∀ {A0 A1}, assigned c A0 = some A1 →
      SubS A0 A → o ≠ .bad ∧ SubS A A' ∧ (o = .ok → SubS A1 A')
    | c, A, o, _, .plain hp hb, A0, A1, h, hs => by
      rw [assigned_plain hp] at h; cases h
      exact ⟨hb, SubS.refl _, fun _ => hs⟩
    | c, A, _, _, .pluckOk hop, A0, A1, h, hs => by
      rw [assigned_eq] at h; simp only [hop, if_true, Option.some.injEq] at h; subst h
      refine ⟨by simp, fun k hk => by simp [Slots.add, hk], fun _ k hk => ?_⟩
      simp only [Slots.add, Bool.or_eq_true, beq_iff_eq] at hk ⊢
      rcases hk with hk | hk
      · exact .inl hk
      · exact .inr (hs k hk)
    | c, A, _, _, .pluckFail _, A0, A1, h, hs =>
      ⟨by simp, SubS.refl _, fun h => by cases h⟩
    | c, A, o, _, .ratio hop _ hb, A0, A1, h, hs => by
      rw [assigned_eq] at h
      simp only [hop, reduceCtorEq, if_false, if_true] at h
      split at h
      · cases h; exact ⟨hb, SubS.refl _, fun _ => hs⟩
      · cases h
    | c, A, _, _, .ratioBad hop hr, A0, A1, h, hs => by
      rw [assigned_eq] at h
      simp only [hop, reduceCtorEq, if_false, if_true] at h
      split at h
      · rename_i h0
        simp only [ratioOk, Bool.and_eq_true] at h0 hr
        have := hs _ h0.1; have := hs _ h0.2
        simp_all
      · cases h
    | c, A, o, A', .seq hop hrun, A0, A1, h, hs => by
      have h' : assignedSeq c.children A0 = some A1 := by
        rw [assigned_eq] at h
        rcases hop with hop | hop | hop <;> simpa [hop] using h
      exact runSeq_sound hrun h' hs
    | c, A, _, _, .early _, A0, A1, h, hs => ⟨by simp, SubS.refl _, fun h => by cases h⟩
    | c, A, o, A', .or hop hrun, A0, A1, h, hs => by
      have h' : assignedOr c.children A0 = some A1 := by
        rw [assigned_eq] at h; simpa [hop] using h
      have := runOr_sound hrun h' hs
      exact ⟨this.1, this.2.1, fun ho => (this.2.2 ho).2⟩
    | c, A, o, A', .slice hop hrun, A0, A1, h, hs => by
      have h' : assigned (c.children.headD default) A0 = some A1 := by
        rw [assigned_eq] at h; rw [← assignedFirst_eq]; simpa [hop] using h
      exact run_sound hrun h' hs
    | c, A, o, A', .iter hop hrun, A0, A1, h, hs => by
      rw [assigned_eq] at h
      have h1 : c.operator ≠ .Pluck ∧ c.operator ≠ .WithinRatio ∧
          ¬(c.operator = .ZipSome ∨ c.operator = .ZipEvery) ∧ c.operator ≠ .Or := by
        rcases hop with hop | hop <;> simp [hop]
      simp only [h1.1, h1.2.1, h1.2.2.1, h1.2.2.2, hop, if_false, if_true] at h
      rw [assignedFirst_eq] at h
      obtain ⟨B, hB, rfl⟩ := Option.map_eq_some_iff.mp h
      have := runIter_sound hrun hB hs
      refine ⟨this.1, this.2.1, fun ho => ?_⟩
      rcases hop with hop | hop
      · simp only [hop, if_true]; exact this.2.2 ho (by simp [hop])
      · simp only [hop, reduceCtorEq, if_false]; exact SubS.trans hs this.2.1
    | c, A, _, _, .zipBad hop hz, A0, A1, h, hs => by
      rw [assigned_eq] at h
      have h1 : c.operator ≠ .Pluck ∧ c.operator ≠ .WithinRatio := by
        rcases hop with hop | hop <;> simp [hop]
      simp only [h1.1, h1.2, hop, if_false, if_true] at h
      split at h
      · rename_i h0
        exfalso
        rw [List.all_eq_true] at h0
        rw [List.all_eq_false] at hz
        obtain ⟨k, hk, hk'⟩ := hz
        simp [hs k (h0 k hk)] at hk'
      · cases h
    | c, A, _, _, .zipEarly _ _, A0, A1, h, hs => ⟨by simp, SubS.refl _, fun h => by cases h⟩
    | c, A, o, A', .zip hop _ hrun, A0, A1, h, hs => by
      rw [assigned_eq] at h
      have h1 : c.operator ≠ .Pluck ∧ c.operator ≠ .WithinRatio := by
        rcases hop with hop | hop <;> simp [hop]
      simp only [h1.1, h1.2, hop, if_false, if_true] at h
      split at h
      · rw [assignedFields_eq] at h
        obtain ⟨B, hB, rfl⟩ := Option.map_eq_some_iff.mp h
        have := runZip_sound hrun hB hs
        refine ⟨this.1, this.2.1, fun ho => ?_⟩
        by_cases hzs : c.operator = .ZipSome
        · simp only [hzs, if_true]; exact this.2.2 ho (by simp [hzs])
        · simp only [hzs, if_false]; exact SubS.trans hs this.2.1
      · cases h

  theorem runSeq_sound : ∀ {cs A o A'}, RunSeq cs A o A' → ∀ {A0 A1},
      assignedSeq cs A0 = some A1 → SubS A0 A → o ≠ .bad ∧ SubS A A' ∧ (o = .ok → SubS A1 A')
    | _, A, _, _, .nil, A0, A1, h, hs => by
      simp only [assignedSeq, Option.some.injEq] at h; subst h
      exact ⟨by simp, SubS.refl _, fun _ => hs⟩
    | _, A, o, A2, .next (A1 := Am) hc hrest, A0, A1, h, hs => by
      simp only [assignedSeq, Option.bind_eq_some_iff] at h
      obtain ⟨B, hB, hrestA⟩ := h
      have r1 := run_sound hc hB hs
      have r2 := runSeq_sound hrest hrestA (r1.2.2 rfl)
      exact ⟨r2.1, SubS.trans r1.2.1 r2.2.1, r2.2.2⟩
    | _, A, o, A', .stop hc hne, A0, A1, h, hs => by
      simp only [assignedSeq, Option.bind_eq_some_iff] at h
      obtain ⟨B, hB, _⟩ := h
      have r1 := run_sound hc hB hs
      exact ⟨r1.1, r1.2.1, fun ho => absurd ho hne⟩

  theorem runOr_sound : ∀ {cs A o A'}, RunOr cs A o A' → ∀ {A0 A1},
      assignedOr cs A0 = some A1 → SubS A0 A →
      o ≠ .bad ∧ SubS A A' ∧ (o = .ok → cs ≠ [] ∧ SubS A1 A')
    | _, A, _, _, .nil, A0, A1, h, hs => ⟨by simp, SubS.refl _, fun h => by cases h⟩
    | _, A, o, A', .stop hc hne, A0, A1, h, hs => by
      obtain ⟨a, ha, hRa, _⟩ := assignedOr_cons h
      have r1 := run_sound hc ha hs
      exact ⟨r1.1, r1.2.1, fun ho => ⟨by simp, SubS.trans hRa (r1.2.2 ho)⟩⟩
    | _, A, o, A2, .next hc hrest, A0, A1, h, hs => by
      obtain ⟨a, ha, _, hcs⟩ := assignedOr_cons h
      have r1 := run_sound hc ha hs
      obtain ⟨b, hb, hRb⟩ := assignedOr_rest h
      have r2 := runOr_sound hrest hb (SubS.trans hs r1.2.1)
      exact ⟨r2.1, SubS.trans r1.2.1 r2.2.1, fun ho => by
        obtain ⟨hne, hsub⟩ := r2.2.2 ho
        exact ⟨by simp, SubS.trans (hRb hne) hsub⟩⟩

  theorem runIter_sound : ∀ {sm ch A o A'}, RunIter sm ch A o A' → ∀ {A0 B},
      assigned ch A0 = some B → SubS A0 A →
      o ≠ .bad ∧ SubS A A' ∧ (o = .ok → sm = true → SubS B A')
    | sm, _, A, _, _, .done, A0, B, h, hs => by
      refine ⟨by cases sm <;> simp, SubS.refl _, fun ho hsm => ?_⟩
      subst hsm; simp at ho
    | _, _, A, o, A', .stop hc hcase, A0, B, h, hs => by
      have r1 := run_sound hc h hs
      exact ⟨r1.1, r1.2.1, fun ho _ => r1.2.2 ho⟩
    | sm, _, A, o', A2, .next hc hcase hrest, A0, B, h, hs => by
      have r1 := run_sound hc h hs
      have r2 := runIter_sound hrest h (SubS.trans hs r1.2.1)
      exact ⟨r2.1, SubS.trans r1.2.1 r2.2.1, r2.2.2⟩

  theorem runZip_sound : ∀ {sm fs A o A'}, RunZip sm fs A o A' → ∀ {A0 B},
      assignedSeq fs A0 = some B → SubS A0 A →
      o ≠ .bad ∧ SubS A A' ∧ (o = .ok → sm = true → SubS B A')
    | sm, _, A, _, _, .done, A0, B, h, hs => by
      refine ⟨by cases sm <;> simp, SubS.refl _, fun ho hsm => ?_⟩
      subst hsm; simp at ho
    | _, _, A, o, A', .stop hc hcase, A0, B, h, hs => by
      have r1 := runSeq_sound hc h hs
      exact ⟨r1.1, r1.2.1, fun ho _ => r1.2.2 ho⟩
    | sm, _, A, o', A2, .next hc hcase hrest, A0, B, h, hs => by
      have r1 := runSeq_sound hc h hs
      have r2 := runZip_sound hrest h (SubS.trans hs r1.2.1)
      exact ⟨r2.1, SubS.trans r1.2.1 r2.2.1, r2.2.2⟩
end

/-- **No unwritten slot is read.** If the analysis accepts the tree from no
    written slots, no execution of it reads an unwritten slot. -/
theorem assigned_no_bad {c : Condition} {B : Slots} (h : assigned c (fun _ => false) = some B)
    {o : Outcome} {A' : Slots} (hrun : Run c (fun _ => false) o A') : o ≠ .bad :=
  (run_sound hrun h (fun _ h => h)).1

/-! ## Node-local rewrites don't change the analysis -/

def slotOp (op : Operator) : Prop :=
  op = .Pluck ∨ op = .WithinRatio ∨ op = .ZipSome ∨ op = .ZipEvery

section Map
variable (F : Condition → Condition)
  (hch : ∀ c, (F c).children = c.children.map F)
  (hop : ∀ c, (F c).operator = c.operator ∨
    (isPlain (F c).operator = true ∧ isPlain c.operator = true))
  (hcv : ∀ c, slotOp c.operator → (F c).compValue = c.compValue)

include hch hop hcv in
theorem assigned_map (c : Condition) : ∀ A, assigned (F c) A = assigned c A := by
  have ih : ∀ x, x ∈ c.children → ∀ A, assigned (F x) A = assigned x A :=
    fun x hm => assigned_map x
  have ih2 : ∀ x, x ∈ c.children → ∀ y, y ∈ x.children → ∀ A, assigned (F y) A = assigned y A :=
    fun x _ y _ => assigned_map y
  have seqL : ∀ cs : List Condition, (∀ x, x ∈ cs → ∀ A, assigned (F x) A = assigned x A) →
      ∀ A, assignedSeq (cs.map F) A = assignedSeq cs A := by
    intro cs
    induction cs with
    | nil => intro _ A; rfl
    | cons a cs ihl =>
      intro h A
      simp only [List.map_cons, assignedSeq, h a (by simp)]
      congr 1; funext B; exact ihl (fun x hx => h x (by simp [hx])) B
  have orL : ∀ cs : List Condition, (∀ x, x ∈ cs → ∀ A, assigned (F x) A = assigned x A) →
      ∀ A, assignedOr (cs.map F) A = assignedOr cs A := by
    intro cs
    induction cs with
    | nil => intro _ A; rfl
    | cons a cs ihl =>
      intro h A
      cases cs with
      | nil => simp only [List.map_cons, List.map_nil, assignedOr, h a (by simp)]
      | cons b cs =>
        have := ihl (fun x hx => h x (by simp [hx])) A
        simp only [List.map_cons] at this ⊢
        simp only [assignedOr, h a (by simp), this]
  have firstL : ∀ A, assignedFirst (c.children.map F) A = assignedFirst c.children A := by
    intro A
    cases hc : c.children with
    | nil => rfl
    | cons a _ => exact ih a (by rw [hc]; simp) A
  have fieldsL : ∀ A, assignedFields (c.children.map F) A = assignedFields c.children A := by
    intro A
    cases hc : c.children with
    | nil => rfl
    | cons a _ =>
      simp only [List.map_cons, assignedFields_eq, List.headD_cons, hch]
      exact seqL a.children (fun y hy => ih2 a (by rw [hc]; simp) y hy) A
  intro A
  rcases hop c with heq | ⟨hp1, hp2⟩
  · rw [assigned_eq, assigned_eq, heq, hch, seqL _ ih, orL _ ih, firstL, fieldsL]
    by_cases hs : slotOp c.operator
    · rw [hcv c hs]
    · cases hc : c.operator <;> simp [hc, slotOp] at hs ⊢
  · rw [assigned_plain hp1, assigned_plain hp2]
termination_by sizeOf c
decreasing_by
  · exact sizeOf_child hm
  · exact Nat.lt_trans (sizeOf_child (by assumption)) (sizeOf_child (by assumption))

end Map

theorem assigned_annotate (c : Condition) (A : Slots) : assigned (annotate c) A = assigned c A := by
  apply assigned_map annotate (fun c => annotate_children c)
  · intro c
    rw [annotate_operator]
    split
    · rename_i h; exact .inr ⟨by simp [isPlain], by simp [isPlain, h]⟩
    · exact .inl rfl
  · intro c _; exact annotate_compValue c

theorem assigned_skel (c : Condition) (A : Slots) : assigned (skel c) A = assigned c A := by
  apply assigned_map skel skel_children (fun c => .inl (skel_operator c))
  intro c hs
  rw [skel_compValue]
  rcases hs with h | h | h | h <;> simp [h, keepsCv]

theorem assigned_avatar (a b : Bytes) (fs : List ConditionPacking.Flat) (A : Slots) :
    assigned (ConditionPacking.rawTree a fs 0) A = assigned (ConditionPacking.rawTree b fs 0) A := by
  rw [← assigned_skel, skel_rawTree a b, assigned_skel]

end ConditionCheck
