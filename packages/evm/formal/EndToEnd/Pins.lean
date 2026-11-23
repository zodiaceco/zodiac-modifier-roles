import Evaluate.Model
import DecoderFaithfulness.Decode

/-!
# A pinned argument is pinned

The pin check a permission lint should make, on the condition
the evaluator runs (`Evaluate`): an argument of the calldata counts as
pinned when every way the condition passes reaches, through `Or` (every
branch), `And` (some child) and the root calldata `Matches` (4 leading
bytes, the argument at head offset `32 * i`), an `EqualTo` of the expected
shape at that argument.

`pinsArg_sound`: when `evaluate` passes such a condition, one of those
`EqualTo` nodes passes on the slice Roles finds where the argument's head
word points: the bytes Roles reads there equal its compValue. (The evaluator model compares values longer than 32 bytes
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
  (List.range i).all (fun j => slotSize (c.children.getD j default).inlineSize = 32) &&
  (c.children.getD i default).inlineSize = 0

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
theorem orLoop_ok {F : Nat} : ∀ {cs : List Condition} {loc : Slice} {cons : List Consumption}
    {sl : Slots}, (orLoop env data n F cs loc cons sl).status = sOk →
    ∃ c ∈ cs, ∃ sl', (evalC env data n F loc c.inlineSize c cons sl').status = sOk
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
theorem seqLoop_ok {F : Nat} : ∀ {xs : List (Condition × Slice)} {cons : List Consumption}
    {sl : Slots}, (seqLoop env data n F xs cons sl).status = sOk →
    ∀ x ∈ xs, ∃ cons' sl', (evalC env data n F x.2 x.1.inlineSize x.1 cons' sl').status = sOk
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

/-- What a passing `EqualTo` says of its node at the slice `loc`: the
    operand was read, and `_compare` found it equal to the compValue. -/
def PassesAt (env : Env) (data : Calldata) (loc : Slice) (e : Condition) : Prop :=
  input data loc e.inlineSize e ≠ .overflow ∧
    Evaluate.compare .EqualTo (inputB env (input data loc e.inlineSize e))
      (inputLength data loc e.inlineSize e) e.compValue = sOk

/-- **A pinned value passes only as one of the pinned compValues.** If
    `isPinned` holds and the evaluation passes at `loc`, an accepted `EqualTo`
    under the node compares equal to the value Roles reads at `loc`. -/
theorem isPinned_sound (leaf : Condition → Bool) :
    ∀ (F f : Nat) (loc : Slice) (c : Condition) (cons : List Consumption) (sl : Slots),
    isPinned leaf f c = true → (evalC env data n F loc c.inlineSize c cons sl).status = sOk →
    ∃ e, Under c e ∧ pinnedLeaf leaf e = true ∧ PassesAt env data loc e
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
        split at h
        · assumption
        · rename_i hcmp
          simp [violation] at h; exact absurd h hcmp
    · unfold evalC at h
      rw [hor] at h
      obtain ⟨d, hd, sl', hd'⟩ := orLoop_ok h
      obtain ⟨e, hu, hl, hv⟩ := isPinned_sound leaf F f loc d cons sl' (hall d hd) hd'
      exact ⟨e, .child (.inl hor) hd hu, hl, hv⟩
    · unfold evalC at h
      rw [hand] at h
      obtain ⟨cons', sl', hd'⟩ := seqLoop_ok h (d, loc) (by simp [hd])
      obtain ⟨e, hu, hl, hv⟩ := isPinned_sound leaf F f loc d cons' sl' hpd hd'
      exact ⟨e, .child (.inr hand) hd hu, hl, hv⟩

/-! ## The root calldata `Matches` -/

/-- `AbiLocation.children`: when the children before `k` take one word of
    head each and child `k` is read through its offset, child `k` is the
    child `_child` finds at head word `k`. -/
theorem childrenLoop_loc (body : Slice) (sizeAt : Nat → Nat) :
    ∀ (cnt i0 h0 : Nat) (spans : List Slice),
    childrenLoop data body sizeAt cnt i0 h0 = some spans →
    ∀ k, k < cnt → (∀ j, j < k → slotSize (sizeAt (i0 + j)) = 32) → sizeAt (i0 + k) = 0 →
      ∃ sp next, spans[k]? = some sp ∧ child data body (h0 + 32 * k) 0 = some (sp, next)
  | 0, _, _, _, _, k, hk, _, _ => absurd hk (Nat.not_lt_zero k)
  | cnt + 1, i0, h0, spans, h, k, hk, hstep, hinl => by
    unfold childrenLoop at h
    cases hc : child data body h0 (sizeAt i0) with
    | none => rw [hc] at h; simp at h
    | some q =>
      obtain ⟨sp0, next⟩ := q
      rw [hc] at h
      simp only at h
      obtain ⟨rest, hrest, rfl⟩ := Option.map_eq_some_iff.mp h
      cases k with
      | zero =>
        simp only [Nat.add_zero] at hinl
        rw [hinl] at hc
        exact ⟨sp0, next, by simp, by simpa using hc⟩
      | succ k =>
        have h0s : slotSize (sizeAt i0) = 32 := by simpa using hstep 0 (by omega)
        obtain ⟨rfl, -, -⟩ := child_some hc
        rw [h0s] at hrest
        obtain ⟨sp, nx, hget, hch⟩ := childrenLoop_loc body sizeAt cnt (i0 + 1) (h0 + 32) rest hrest
          k (by omega)
          (fun j hj => by
            have := hstep (j + 1) (by omega)
            rwa [show i0 + (j + 1) = i0 + 1 + j by omega] at this)
          (by rwa [show i0 + 1 + k = i0 + (k + 1) by omega])
        refine ⟨sp, nx, by simpa using hget, ?_⟩
        rw [show h0 + 32 * (k + 1) = h0 + 32 + 32 * k by omega]
        exact hch

/-- `e` is reached from the root: through `Or` branches and `And` children
    to a calldata `Matches`, then to its child `i`, then through `Or` and
    `And` again. -/
inductive PinUnder (i : Nat) : Condition → Condition → Prop
  | logical {c d e : Condition} (hop : c.operator = .Or ∨ c.operator = .And)
      (hd : d ∈ c.children) (h : PinUnder i d e) : PinUnder i c e
  | arg {m e : Condition} (hm : decodesCalldata m = true)
      (h : Under (m.children.getD i default) e) : PinUnder i m e

private theorem leadingCheck_ne_ok' {loc : Slice} {cv : Bytes} {s : Nat}
    (h : leadingCheck data loc cv = some s) : s ≠ sOk := by
  unfold leadingCheck at h
  repeat' split at h
  all_goals (simp at h; try (subst h; decide))

/-- The root calldata `Matches` (4 leading bytes) that gets to its children
    finds them past the selector. -/
theorem matchesHead_root {c : Condition} {body : Slice} (henc : c.encoding = .AbiEncoded)
    (hlb : c.leadingBytes = 4) (h : matchesHead data ⟨0, data.length⟩ c = .inr body) :
    body = ⟨4, data.length - 4⟩ ∧ 4 ≤ data.length := by
  unfold matchesHead at h
  rw [ite_eq_left henc, hlb] at h
  simp only [ne_eq, not_true_eq_false, ite_false] at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · simp only [Sum.inr.injEq] at h
      exact ⟨by rw [← h], by omega⟩

private theorem matchesHead_ne_ok' {loc : Slice} {c : Condition} {s : Nat}
    (h : matchesHead data loc c = .inl s) : s ≠ sOk := by
  unfold matchesHead at h
  repeat' split at h
  all_goals first
    | (simp only [Sum.inl.injEq] at h; subst h; decide)
    | (rename_i hlc; simp only [Sum.inl.injEq] at h; subst h; exact leadingCheck_ne_ok' hlc)
    | simp at h

/-- **A pinned argument passes only as a pinned value** (`pinsArg`). When
    `evaluate` passes the root condition on `data`, some accepted `EqualTo`
    the pin reaches passes on the slice `L` Roles finds where head word `i`
    points, `calldataload(4 + 32 i) + 4`. -/
theorem pinsArg_sound (leaf : Condition → Bool) (i : Nat) :
    ∀ (F f : Nat) (c : Condition) (cons : List Consumption) (sl : Slots),
    pinsArg leaf i f c = true →
    (evalC env data n F ⟨0, data.length⟩ c.inlineSize c cons sl).status = sOk →
    ∃ e L, PinUnder i c e ∧ pinnedLeaf leaf e = true ∧
      L.offset = load data (4 + 32 * i) + 4 ∧ L.offset + L.length ≤ data.length ∧
      PassesAt env data L e
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
      obtain ⟨e, L, hu, hl, ho, hw, hv⟩ := pinsArg_sound leaf i F f d cons sl' (hall d hd) hd'
      exact ⟨e, L, .logical (.inl hor) hd hu, hl, ho, hw, hv⟩
    · unfold evalC at h
      rw [hand] at h
      obtain ⟨cons', sl', hd'⟩ := seqLoop_ok h (d, ⟨0, data.length⟩) (by simp [hd])
      obtain ⟨e, L, hu, hl, ho, hw, hv⟩ := pinsArg_sound leaf i F f d cons' sl' hpd hd'
      exact ⟨e, L, .logical (.inr hand) hd hu, hl, ho, hw, hv⟩
    · have hm' := hm
      unfold decodesCalldata at hm'
      simp only [decide_eq_true_eq] at hm'
      obtain ⟨hop, henc, hlb⟩ := hm'
      unfold evalC at h
      rw [hop] at h
      simp only at h
      rcases hmh : matchesHead data ⟨0, data.length⟩ c with s | body
      · rw [hmh] at h
        simp only [violation] at h
        exact absurd h (matchesHead_ne_ok' hmh)
      · rw [hmh] at h
        simp only at h
        obtain ⟨rfl, h4⟩ := matchesHead_root henc hlb hmh
        rcases hlocs : children data ⟨4, data.length - 4⟩ c with _ | spans
        · rw [hlocs] at h; simp [violation, sCalldataOverflow, sOk] at h
        · rw [hlocs] at h
          simp only at h
          rw [children, ite_eq_right (by rw [henc]; decide)] at hlocs
          split at h
          · simp [violation, sParameterNotAMatch, sOk] at h
          · rename_i hlen
            simp only [Decidable.not_not] at hlen
            have hheadAll := hhead
            unfold headOk at hheadAll
            simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range,
              decide_eq_true_eq] at hheadAll
            obtain ⟨hbefore, hnotinl⟩ := hheadAll
            obtain ⟨sp, next, hget, hch⟩ := childrenLoop_loc ⟨4, data.length - 4⟩
              (fun j => (c.children.getD j default).inlineSize)
              c.children.length 0 0 spans hlocs i hi
              (fun j hj => by simpa using hbefore j hj) (by simpa using hnotinl)
            simp only [Nat.zero_add] at hch
            have hil : i < spans.length := by rw [← hlen]; exact hi
            have hmem : (c.children.getD i default, sp) ∈ c.children.zip spans := by
              rw [List.mem_iff_getElem]
              refine ⟨i, by simp only [List.length_zip]; exact Nat.lt_min.mpr ⟨hi, hil⟩, ?_⟩
              simp only [List.getElem_zip]
              have := List.getElem?_eq_some_iff.mp hget
              rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
              simp [this.2]
            obtain ⟨cons', sl', hd'⟩ := seqLoop_ok h _ hmem
            obtain ⟨e, hu, hl, hv⟩ := isPinned_sound leaf F f _ _ cons' sl' hpi hd'
            obtain ⟨-, -, hsp⟩ := child_some hch
            rcases hsp with ⟨h0, -⟩ | ⟨-, hlo, hhi, rfl⟩
            · omega
            · simp only at hlo hhi
              exact ⟨e, _, .arg hm hu, hl, by simp only; omega, by simp only; omega, hv⟩

end EndToEnd
