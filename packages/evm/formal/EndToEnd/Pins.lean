import Evaluate.Model

/-!
# A pinned argument is pinned

The pin check a permission lint should make, on the condition
the evaluator runs (`Evaluate`): an argument of the calldata counts as
pinned when every way the condition passes reaches, through `Or` (every
branch), `And` (some child) and the root calldata `Matches` (4 leading
bytes, the argument at head offset `32 * i`), an `EqualTo` of the expected
shape at that argument.

`pin_sound`: when `evaluate` passes such a condition, the bytes Roles reads
at the argument's tail location equal the compValue of one of those
`EqualTo` nodes. (The evaluator model compares values longer than 32 bytes
by their preimages: keccak256 is taken to have no collision here.)
-/

namespace EndToEnd
open DecoderFaithfulness DecoderFaithfulness.Roles Evaluate

/-- An `EqualTo` the pin accepts: `leaf` checks its encoding and shape. -/
def pinnedLeaf (leaf : Condition → Bool) (c : Condition) : Bool :=
  c.operator = .EqualTo ∧ leaf c

/-- `isPinned`: an accepted `EqualTo`, an `Or` of pinned branches, or an `And`
    with a pinned child. -/
def isPinned (leaf : Condition → Bool) : Nat → Condition → Bool
  | 0, _ => false
  | f + 1, c =>
    pinnedLeaf leaf c ||
    (c.operator = .Or && c.children.all (isPinned leaf f)) ||
    (c.operator = .And && c.children.any (isPinned leaf f))

/-- The head of the calldata `Matches` up to argument `i` is one word per
    argument, so argument `i`'s head is at `32 * i`, and argument `i` itself
    is not inlined (it is read through its offset). -/
def headOk (c : Condition) (i : Nat) : Bool :=
  (List.range i).all (fun j =>
    let ch := c.children.getD j default
    !ch.inlined || ch.size = 32) &&
  !(c.children.getD i default).inlined

/-- The root calldata `Matches`: 4 leading bytes (the selector). -/
def decodesCalldata (c : Condition) : Bool :=
  c.operator = .Matches ∧ c.encoding = .AbiEncoded ∧ c.leadingBytes = 4

/-- Every way the root condition passes pins argument `i`. -/
def pinsArg (leaf : Condition → Bool) (i : Nat) : Nat → Condition → Bool
  | 0, _ => false
  | f + 1, c =>
    (c.operator = .Or && c.children.all (pinsArg leaf i f)) ||
    (c.operator = .And && c.children.any (pinsArg leaf i f)) ||
    (decodesCalldata c && headOk c i && i < c.children.length &&
      isPinned leaf f (c.children.getD i default))

/-! ## The evaluator's loops -/

variable {env : Env} {data : Calldata} {n : Nat}

/-- An `Or` that passes has a child that passes, from the same consumptions. -/
theorem orLoop_ok {F : Nat} : ∀ {cs : List Condition} {loc : Nat} {cons : List Consumption}
    {sl : Slots}, (orLoop env data n F cs loc cons sl).status = sOk →
    ∃ c ∈ cs, ∃ sl', (evalC env data n F loc c cons sl').status = sOk
  | [], _, _, _, h => by simp [orLoop, violation, sOk, sOrViolation] at h
  | c :: rest, loc, cons, sl, h => by
    unfold orLoop at h
    simp only at h
    split at h
    · rename_i hc
      rcases hc with hc | hc
      · exact ⟨c, by simp, sl, hc⟩
      · rw [hc] at h; simp [revert, sOk] at h
    · obtain ⟨c', hc', sl', h'⟩ := orLoop_ok h
      exact ⟨c', List.mem_cons_of_mem _ hc', sl', h'⟩

/-- A sequence that passes has every element pass, from some consumptions. -/
theorem seqLoop_ok {F : Nat} : ∀ {xs : List (Condition × Nat)} {cons : List Consumption}
    {sl : Slots}, (seqLoop env data n F xs cons sl).status = sOk →
    ∀ x ∈ xs, ∃ cons' sl', (evalC env data n F x.2 x.1 cons' sl').status = sOk
  | [], _, _, _, x, hx => by simp at hx
  | y :: rest, cons, sl, h, x, hx => by
    unfold seqLoop at h
    simp only at h
    split at h
    · rename_i hne; exact absurd h hne
    · rename_i hy
      rcases List.mem_cons.mp hx with rfl | hx
      · exact ⟨cons, sl, by simpa using hy⟩
      · exact seqLoop_ok h x hx

/-! ## Pinned leaves -/

/-- `e` is reached from `c` through `Or` branches and `And` children. -/
inductive Under : Condition → Condition → Prop
  | refl (c : Condition) : Under c c
  | child {c d e : Condition} (hop : c.operator = .Or ∨ c.operator = .And)
      (hd : d ∈ c.children) (h : Under d e) : Under c e

/-- **A pinned value passes only as one of the pinned compValues.** If
    `isPinned` holds and the evaluation passes at `loc`, an accepted `EqualTo`
    under the node compares equal to the value Roles reads at `loc`. -/
theorem isPinned_sound (leaf : Condition → Bool) :
    ∀ (F f : Nat) (loc : Nat) (c : Condition) (cons : List Consumption) (sl : Slots),
    isPinned leaf f c = true → (evalC env data n F loc c cons sl).status = sOk →
    ∃ e, Under c e ∧ pinnedLeaf leaf e = true ∧ input data loc e ≠ .overflow ∧
      inputB env (input data loc e) = cvB e.compValue
  | 0, _, _, _, _, _, _, h => by simp [evalC, violation, revert, sOk] at h
  | _, 0, _, _, _, _, hp, _ => by simp [isPinned] at hp
  | F + 1, f + 1, loc, c, cons, sl, hp, h => by
    unfold isPinned at hp
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
      List.any_eq_true] at hp
    rcases hp with (hleaf | ⟨hor, hall⟩) | ⟨hand, d, hd, hpd⟩
    · have hop : c.operator = .EqualTo := by
        unfold pinnedLeaf at hleaf; simp at hleaf; exact hleaf.1
      unfold evalC at h
      rw [hop] at h
      simp only at h
      split at h
      · simp [violation, sCalldataOverflow, sOk] at h
      · rename_i hnov
        refine ⟨c, .refl c, hleaf, hnov, ?_⟩
        unfold result at h
        by_cases hcmp : Evaluate.compare .EqualTo (inputB env (input data loc c)) c.compValue = sOk
        · simp only [Evaluate.compare] at hcmp
          by_cases hq : inputB env (input data loc c) = cvB c.compValue
          · exact hq
          · rw [if_neg hq] at hcmp
            simp [sParameterNotAllowed, sOk] at hcmp
        · rw [if_neg hcmp] at h; simp [violation, sOk] at h; exact absurd h hcmp
    · unfold evalC at h
      rw [hor] at h
      obtain ⟨d, hd, sl', hd'⟩ := orLoop_ok h
      obtain ⟨e, hu, hl, ho, hv⟩ := isPinned_sound leaf F f loc d cons sl' (hall d hd) hd'
      exact ⟨e, .child (.inl hor) hd hu, hl, ho, hv⟩
    · unfold evalC at h
      rw [hand] at h
      obtain ⟨cons', sl', hd'⟩ := seqLoop_ok h (d, loc) (by simp [hd])
      obtain ⟨e, hu, hl, ho, hv⟩ := isPinned_sound leaf F f loc d cons' sl' hpd hd'
      exact ⟨e, .child (.inr hand) hd hu, hl, ho, hv⟩

/-! ## The root calldata `Matches` -/

/-- Head bytes a child takes. -/
def step (ch : Condition) : Nat := if ch.inlined then ch.size else 32

/-- `AbiLocation.children`: when the children before `k` take one word of
    head each and child `k` is read through its offset, child `k` is at the
    tail location of head word `k`. -/
theorem childrenLoop_loc (loc : Nat) (childAt : Nat → Condition) :
    ∀ (cnt i0 h0 : Nat) (locs : List Nat), childrenLoop data loc childAt cnt i0 h0 = some locs →
    ∀ k, k < cnt → (∀ j, j < k → step (childAt (i0 + j)) = 32) →
      (childAt (i0 + k)).inlined = false →
      locs[k]? = some (tailLocation data loc (h0 + 32 * k))
  | 0, _, _, _, _, k, hk, _, _ => absurd hk (Nat.not_lt_zero k)
  | cnt + 1, i0, h0, locs, h, k, hk, hstep, hinl => by
    unfold childrenLoop at h
    simp only at h
    by_cases hin : (childAt i0).inlined = true
    · -- child `i0` inlined: then `k > 0` and its step is 32
      cases k with
      | zero => simp [hin] at hinl
      | succ k =>
        have h0s : step (childAt i0) = 32 := by simpa using hstep 0 (by omega)
        have hsz : (childAt i0).size = 32 := by simpa [step, hin] using h0s
        simp only [hin, ite_true, hsz] at h
        split at h
        · simp at h
        · obtain ⟨rest, hrest, rfl⟩ := Option.map_eq_some_iff.mp h
          have := childrenLoop_loc loc childAt cnt (i0 + 1) (h0 + 32) rest hrest k (by omega)
            (fun j hj => by
              have := hstep (j + 1) (by omega)
              rwa [show i0 + (j + 1) = i0 + 1 + j by omega] at this)
            (by rwa [show i0 + 1 + k = i0 + (k + 1) by omega])
          simp only [List.getElem?_cons_succ, this]
          congr 2; omega
    · simp only [hin, Bool.false_eq_true, ite_false] at h
      split at h
      · simp at h
      · obtain ⟨rest, hrest, rfl⟩ := Option.map_eq_some_iff.mp h
        cases k with
        | zero => simp
        | succ k =>
          have := childrenLoop_loc loc childAt cnt (i0 + 1) (h0 + 32) rest hrest k (by omega)
            (fun j hj => by
              have := hstep (j + 1) (by omega)
              rwa [show i0 + (j + 1) = i0 + 1 + j by omega] at this)
            (by rwa [show i0 + 1 + k = i0 + (k + 1) by omega])
          simp only [List.getElem?_cons_succ, this]
          congr 2; omega

/-- `e` is reached from the root: through `Or` branches and `And` children
    to a calldata `Matches`, then to its child `i`, then through `Or` and
    `And` again. -/
inductive PinUnder (i : Nat) : Condition → Condition → Prop
  | logical {c d e : Condition} (hop : c.operator = .Or ∨ c.operator = .And)
      (hd : d ∈ c.children) (h : PinUnder i d e) : PinUnder i c e
  | arg {m e : Condition} (hm : decodesCalldata m = true)
      (h : Under (m.children.getD i default) e) : PinUnder i m e

/-- **A pinned argument passes only as a pinned value** (`pinsArg`). When
    `evaluate` passes the root condition on `data`, some accepted `EqualTo`
    the pin reaches compares equal to what Roles reads at the tail location
    of head word `i`: `tailLocation data 4 (32 * i)`. -/
theorem pinsArg_sound (leaf : Condition → Bool) (i : Nat) :
    ∀ (F f : Nat) (c : Condition) (cons : List Consumption) (sl : Slots),
    pinsArg leaf i f c = true → (evalC env data n F 0 c cons sl).status = sOk →
    ∃ e, PinUnder i c e ∧ pinnedLeaf leaf e = true ∧
      input data (tailLocation data 4 (32 * i)) e ≠ .overflow ∧
      inputB env (input data (tailLocation data 4 (32 * i)) e) = cvB e.compValue
  | 0, _, _, _, _, _, h => by simp [evalC, violation, revert, sOk] at h
  | _, 0, _, _, _, hp, _ => by simp [pinsArg] at hp
  | F + 1, f + 1, c, cons, sl, hp, h => by
    unfold pinsArg at hp
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
      List.any_eq_true] at hp
    rcases hp with (⟨hor, hall⟩ | ⟨hand, d, hd, hpd⟩) | ⟨⟨⟨hm, hhead⟩, hi⟩, hpi⟩
    · unfold evalC at h
      rw [hor] at h
      obtain ⟨d, hd, sl', hd'⟩ := orLoop_ok h
      obtain ⟨e, hu, hl, ho, hv⟩ := pinsArg_sound leaf i F f d cons sl' (hall d hd) hd'
      exact ⟨e, .logical (.inl hor) hd hu, hl, ho, hv⟩
    · unfold evalC at h
      rw [hand] at h
      obtain ⟨cons', sl', hd'⟩ := seqLoop_ok h (d, 0) (by simp [hd])
      obtain ⟨e, hu, hl, ho, hv⟩ := pinsArg_sound leaf i F f d cons' sl' hpd hd'
      exact ⟨e, .logical (.inr hand) hd hu, hl, ho, hv⟩
    · have hm' := hm
      unfold decodesCalldata at hm'
      simp only [decide_eq_true_eq] at hm'
      obtain ⟨hop, henc, hlb⟩ := hm'
      unfold evalC at h
      rw [hop] at h
      simp only [show ¬(0 > 0 ∧ c.encoding = .AbiEncoded) by omega, ite_false, hlb,
        Nat.zero_add] at h
      split at h
      · rename_i s hs
        simp only [violation] at h
        unfold leadingCheck at hs
        split at hs; · simp at hs
        split at hs; · simp at hs; rw [← hs] at h; simp [sCalldataOverflow, sOk] at h
        split at hs; · simp at hs; rw [← hs] at h; simp [revert, sOk] at h
        split at hs; · simp at hs
        simp at hs; rw [← hs] at h; simp [sLeadingBytesNotAMatch, sOk] at h
      · unfold childrenE allocPanics at h
        simp only [henc, reduceCtorEq, false_and, decide_false, Bool.false_eq_true,
          ite_false] at h
        split at h
        · simp_all
        · simp [violation, sCalldataOverflow, sOk] at h
        · rename_i locs hlocs
          simp only [Sum.inr.injEq] at hlocs
          rw [children, if_neg (by rw [henc]; decide)] at hlocs
          split at h
          · simp [violation, sParameterNotAMatch, sOk] at h
          · rename_i hlen
            simp only [Decidable.not_not] at hlen
            have hheadAll := hhead
            unfold headOk at hheadAll
            simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.not_eq_true',
              Bool.or_eq_true, decide_eq_true_eq] at hheadAll
            obtain ⟨hbefore, hnotinl⟩ := hheadAll
            have hloc := childrenLoop_loc 4 (fun j => c.children.getD j default)
              c.children.length 0 0 locs hlocs i hi
              (fun j hj => by
                simp only [Nat.zero_add, step]
                rcases hbefore j hj with hb | hb
                · simp only [List.getD_eq_getElem?_getD] at hb; simp [hb]
                · simp only [List.getD_eq_getElem?_getD] at hb; split <;> simp_all)
              (by simpa using hnotinl)
            simp only [Nat.zero_add] at hloc
            have hil : i < locs.length := by rw [← hlen]; exact hi
            have hmem : (c.children.getD i default, tailLocation data 4 (32 * i)) ∈
                c.children.zip locs := by
              rw [List.mem_iff_getElem]
              refine ⟨i, by simp only [List.length_zip]; exact Nat.lt_min.mpr ⟨hi, hil⟩, ?_⟩
              simp only [List.getElem_zip]
              have := List.getElem?_eq_some_iff.mp hloc
              rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
              simp [this.2]
            obtain ⟨cons', sl', hd'⟩ := seqLoop_ok h _ hmem
            obtain ⟨e, hu, hl, ho, hv⟩ := isPinned_sound leaf F f _ _ cons' sl' hpi hd'
            exact ⟨e, .arg hm hu, hl, ho, hv⟩

end EndToEnd
