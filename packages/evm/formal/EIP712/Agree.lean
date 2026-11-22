import EIP712.Decode
import DecoderFaithfulness.Decode

/-!
# Roles inspects what the encoder hashes

`SignTypedMessageLib`'s fallback hands `EIP712Encoder` the `message`
argument as calldata from `base` (the content of the `bytes` parameter, at
the offset the head word gives), of the length its length word gives. The
fallback reverts unless both lie within `msg.data`; the model leaves that
check out, so it covers every call the fallback accepts. In the model the
library reads `view data base m`: the calldata from `base`, zeros past its
end.

Roles reads the same calldata with `AbiLocation.children`
(`DecoderFaithfulness.Roles`), with bound checks against the slice it
narrowed to.

* `loop_agree` / `children_agree`: when the encoder's walk of a block
  succeeds and Roles' `children` succeeds on a condition node whose children
  have the encoder's inline sizes (`MetaFit`), Roles finds every child
  in a slice that starts exactly at `base +` the encoder's location.
* `visit_agree`: for a condition tree that follows the type tree (`FitT`),
  every node `evaluate` visits sits in a slice that starts at `base +` the
  location where the
  encoder reads the corresponding member, and that member was read. The
  member is one the encoder's walk of the argument's type tree `t0` reaches
  from offset 0 of the view (`Reach`), by its path from the argument root.
* `static_input` / `dynamic_input`: at such a node, the operand Roles
  compares is the word the encoder hashes, or a preimage that contains the
  bytes the encoder hashes.
-/

namespace EIP712
open DecoderFaithfulness DecoderFaithfulness.Roles

/-- What the library reads for a `bytes calldata` whose offset and length
    were set by hand: calldata from `base`, zeros past its end, `m` bytes. -/
def view (data : Bytes) (base m : Nat) : Bytes := (data.drop base ++ zeros m).take m

@[simp] theorem length_view (data : Bytes) (base m : Nat) : (view data base m).length = m := by
  simp [view]

theorem take_append_zeros (B : Bytes) (k : Nat) (hk : 32 ≤ k + B.length) :
    (B ++ zeros k).take 32 = (B ++ zeros 32).take 32 := by
  rw [List.take_append, List.take_append]
  congr 1
  simp only [zeros, List.take_replicate]
  congr 1
  omega

/-- A word of the view inside it is the calldata word (zeros past the end
    of calldata, as `calldataload`). -/
theorem load_view (data : Bytes) (base m x : Nat) (hx : x + 32 ≤ m) :
    load (view data base m) x = load data (base + x) := by
  unfold load view
  congr 1
  have h1 : ((data.drop base ++ zeros m).take m).drop x ++ zeros 32 =
      ((data.drop base ++ zeros m).drop x).take (m - x) ++ zeros 32 := by
    rw [List.drop_take]
  rw [h1, List.take_append_of_le_length (by simp; omega), List.take_take,
    show min 32 (m - x) = 32 by omega]
  rw [List.drop_append, List.drop_drop]
  simp only [zeros, List.drop_replicate]
  have := take_append_zeros (data.drop (base + x)) (m - (x - (data.drop base).length))
  simp only [zeros] at this
  rw [this (by simp; omega)]

/-- The bytes of the view inside it are the calldata's when they are inside
    the calldata. -/
theorem take_view (data : Bytes) (base m x n : Nat) (hx : x + n ≤ m)
    (hd : base + x + n ≤ data.length) :
    ((view data base m).drop x).take n = (data.drop (base + x)).take n := by
  unfold view
  rw [List.drop_take, List.take_take, show min n (m - x) = n by omega, List.drop_append,
    List.take_append_of_le_length (by simp; omega), List.drop_drop]

theorem wordAt_load {d : Bytes} {r : Nat} {w : Bytes} (h : wordAt d r = some w) :
    wordVal w = load d r ∧ r + 32 ≤ d.length := by
  unfold wordAt at h
  split at h
  · simp at h
  · rename_i hb
    simp at h
    subst h
    refine ⟨?_, by omega⟩
    unfold load
    rw [List.take_append_of_le_length (by simp; omega)]

/-! ## Child locations -/

/-- The condition node `ch` carries the inline size (`inlineSize`, as
    `annotate` computes it) of the encoder's type node `t`. -/
def MetaFit (ch : Condition) (t : TN) : Prop := inlineSize t = some ch.inlineSize

/-- A successful walk visits its children at locations: the same loop
    returning the locations. -/
theorem blockLoop_locs {α : Type} (d : Bytes) (rf : TN → Nat → Option α) (cs : List TN)
    (isArray : Bool) (bl : Nat) :
    ∀ n i h vs, blockLoop d rf cs isArray bl n i h = some vs →
    ∃ locs, blockLoop d (fun _ l => some l) cs isArray bl n i h = some locs ∧
      locs.length = n ∧ vs.length = n ∧
      ∀ k (h1 : k < locs.length) (h2 : k < vs.length),
        rf (cs.getD (if isArray then 0 else i + k) default) locs[k] = some vs[k]
  | 0, _, _, vs, e => by
    simp [blockLoop] at e; subst e
    exact ⟨[], by simp [blockLoop], rfl, rfl, fun k h1 => by simp at h1⟩
  | n + 1, i, h, vs, e => by
    simp only [blockLoop] at e ⊢
    cases hc : childLocation d bl h (cs.getD (if isArray = true then 0 else i) default) with
    | none => rw [hc] at e; simp at e
    | some p =>
      obtain ⟨loc, isz⟩ := p
      rw [hc] at e
      simp only at e ⊢
      cases hr : rf (cs.getD (if isArray = true then 0 else i) default) loc with
      | none => rw [hr] at e; simp at e
      | some r =>
        rw [hr] at e
        simp only at e
        cases hb : blockLoop d rf cs isArray bl n (i + 1) (h + if isz > 0 then isz else 32) with
        | none => rw [hb] at e; simp at e
        | some ws =>
          rw [hb] at e
          simp at e
          subst e
          obtain ⟨locs, hl, hll, hwl, hk⟩ := blockLoop_locs d rf cs isArray bl n (i + 1) _ ws hb
          refine ⟨loc :: locs, by rw [hl]; rfl, by simp [hll], by simp [hwl], ?_⟩
          intro k h1 h2
          cases k with
          | zero => simpa using hr
          | succ k =>
            have := hk k (by simp at h1; omega) (by simp at h2; omega)
            simp only [List.getElem_cons_succ]
            rw [show i + (k + 1) = i + 1 + k by omega]
            exact this

/-- Slices that start at `base +` the encoder's locations. -/
def StartAt (base : Nat) (spans : List Slice) (locs : List Nat) : Prop :=
  spans.map (·.offset) = locs.map (base + ·)

theorem StartAt.length {base : Nat} {spans : List Slice} {locs : List Nat}
    (h : StartAt base spans locs) : spans.length = locs.length := by
  have := congrArg List.length h; simpa using this

theorem StartAt.get {base : Nat} {spans : List Slice} {locs : List Nat}
    (h : StartAt base spans locs) (k : Nat) (h1 : k < spans.length) (h2 : k < locs.length) :
    spans[k].offset = base + locs[k] := by
  have := congrArg (fun l => l[k]?) h
  simpa [h1, h2] using this

/-- **Roles' `children` loop finds every child where the encoder does**,
    on any calldata: both use the head offset, reject an offset that points
    backwards, and add the offset to the start of the block; Roles only adds
    bound checks against its slice. -/
theorem loop_agree (data : Bytes) (base m : Nat) (cs : List TN) (isArray : Bool) (bl room : Nat)
    (sizeAt : Nat → Nat) :
    ∀ n i h locs, (∀ k, k < n →
      inlineSize (cs.getD (if isArray then 0 else i + k) default) = some (sizeAt (i + k))) →
    blockLoop (view data base m) (fun _ l => some l) cs isArray bl n i h = some locs →
    ∀ spans, childrenLoop data ⟨base + bl, room⟩ sizeAt n i h = some spans →
      StartAt base spans locs
  | 0, _, _, locs, _, e, spans, e' => by
    simp [blockLoop] at e; simp [childrenLoop] at e'; subst e; subst e'; rfl
  | n + 1, i, h, locs, hfit, e, spans, e' => by
    have hisz := hfit 0 (by omega)
    simp only [Nat.add_zero] at hisz
    simp only [blockLoop] at e
    simp only [childrenLoop] at e'
    cases hc : childLocation (view data base m) bl h (cs.getD (if isArray = true then 0 else i) default) with
    | none => rw [hc] at e; simp at e
    | some p =>
      obtain ⟨loc, isz'⟩ := p
      rw [hc] at e
      simp only at e
      cases hb : blockLoop (view data base m) (fun _ l => some l) cs isArray bl n (i + 1)
          (h + if isz' > 0 then isz' else 32) with
      | none => rw [hb] at e; simp at e
      | some ls =>
        rw [hb] at e
        simp at e
        subst e
        have hfit' : ∀ k, k < n → inlineSize (cs.getD (if isArray then 0 else i + 1 + k) default) =
            some (sizeAt (i + 1 + k)) := by
          intro k hk
          have := hfit (k + 1) (by omega)
          rw [show i + 1 + k = i + (k + 1) by omega]
          exact this
        simp only [childLocation, hisz] at hc
        cases hch : child data ⟨base + bl, room⟩ h (sizeAt i) with
        | none => rw [hch] at e'; simp at e'
        | some q =>
          obtain ⟨sp, next⟩ := q
          rw [hch] at e'
          simp only at e'
          cases hr : childrenLoop data ⟨base + bl, room⟩ sizeAt n (i + 1) next with
          | none => rw [hr] at e'; simp at e'
          | some rs =>
            rw [hr] at e'
            simp at e'
            subst e'
            obtain ⟨rfl, hroom, hsp⟩ := child_some hch
            by_cases hpos : 0 < sizeAt i
            · -- inline child
              rw [ite_eq_left (by omega)] at hc
              split at hc
              · simp at hc
              · simp at hc
                obtain ⟨rfl, rfl⟩ := hc
                rcases hsp with ⟨-, rfl⟩ | ⟨h0, -⟩
                · have hs : slotSize (sizeAt i) = sizeAt i := by
                    unfold slotSize; rw [ite_eq_left hpos]
                  rw [ite_eq_left (by omega)] at hb
                  rw [hs] at hr
                  have := loop_agree data base m cs isArray bl room sizeAt n (i + 1) (h + sizeAt i)
                    ls hfit' hb rs hr
                  unfold StartAt at this ⊢
                  simp [this]; omega
                · omega
            · -- offset child
              have hz : sizeAt i = 0 := by omega
              simp only [hz, gt_iff_lt, Nat.lt_irrefl, ite_false] at hc
              split at hc
              · simp at hc
              · rename_i hhead
                split at hc
                · simp at hc
                · rename_i hback
                  split at hc
                  · simp at hc
                  · simp at hc
                    obtain ⟨rfl, rfl⟩ := hc
                    have hlv := load_view data base m (bl + h) (by simp at hhead; omega)
                    rcases hsp with ⟨h0, -⟩ | ⟨-, -, -, rfl⟩
                    · omega
                    · have hs : slotSize (sizeAt i) = 32 := by rw [hz]; rfl
                      simp only [gt_iff_lt, Nat.lt_irrefl, ite_false] at hb
                      rw [hs] at hr
                      have := loop_agree data base m cs isArray bl room sizeAt n (i + 1) (h + 32)
                        ls hfit' hb rs hr
                      unfold StartAt at this ⊢
                      simp only [List.map_cons, this]
                      rw [show base + bl + h = base + (bl + h) by omega, ← hlv]
                      congr 1; omega

/-! ## The encoder's walk -/

/-- Where the encoder reads the children of `t` at `r`: a tuple's members,
    or an array's elements (after its length word). The location loop of
    `blockLoop`. -/
def childLocs (d : Bytes) (t : TN) (r : Nat) : Option (List Nat) :=
  if t.encoding = .Array then
    (wordAt d r).bind fun w => blockLoop d (fun _ l => some l) t.children true (r + 32) (wordVal w) 0 0
  else if t.encoding = .Tuple then
    blockLoop d (fun _ l => some l) t.children false r t.children.length 0 0
  else none

/-- `Reach d t0 t r`: the encoder's walk of the type tree `t0` (read at
    offset `0` of `d`) reads the subtree `t` at offset `r`. -/
inductive Reach (d : Bytes) (t0 : TN) : TN → Nat → Prop
  | root : Reach d t0 t0 0
  | child {t r locs k} : Reach d t0 t r → childLocs d t r = some locs → (hk : k < locs.length) →
      Reach d t0 (t.children.getD (if t.encoding = .Array then 0 else k) default) locs[k]

/-! ## Per node -/

/-- The children of a `Tuple` type node: where Roles' `children` finds them
    on a `Matches` node over it, the encoder read them. -/
theorem children_agree_tuple {data : Bytes} {base m fuel r : Nat} {t : TN} {v : V} {c : Condition}
    {body : Slice} (hbody : body.offset = base + r)
    (hread : readV (view data base m) (fuel + 1) t r = some v) (he : t.encoding = .Tuple)
    (hce : c.encoding ≠ .Array) (hlen : c.children.length = t.children.length)
    (hfit : ∀ k (h1 : k < c.children.length) (h2 : k < t.children.length),
      MetaFit c.children[k] t.children[k]) :
    ∀ spans, children data body c = some spans →
    ∃ (locs : List Nat) (vs : List V), StartAt base spans locs ∧ v = .list vs ∧
      childLocs (view data base m) t r = some locs ∧ locs.length = t.children.length ∧
      vs.length = t.children.length ∧
      ∀ k (h1 : k < locs.length) (h2 : k < vs.length) (h3 : k < t.children.length),
        readV (view data base m) fuel t.children[k] locs[k] = some vs[k] := by
  intro spans hc
  obtain ⟨bo, room⟩ := body
  simp only at hbody
  subst hbody
  simp only [readV, he, show (Encoding.Tuple = Encoding.Static) = False by simp,
    show (Encoding.Tuple = Encoding.Dynamic) = False by simp,
    show (Encoding.Tuple = Encoding.Array) = False by simp, ite_false, ite_true,
    Bool.false_eq_true, false_and] at hread
  cases hb : blockLoop (view data base m) (readV (view data base m) fuel) t.children false r
      t.children.length 0 0 with
  | none => rw [hb] at hread; simp at hread
  | some vs =>
    rw [hb] at hread
    simp at hread
    subst hread
    obtain ⟨locs, hl, hll, hvl, hk⟩ := blockLoop_locs _ _ _ _ _ _ _ _ vs hb
    unfold children at hc
    rw [ite_eq_right hce, hlen] at hc
    have := loop_agree data base m t.children false r room
      (fun i => (c.children.getD i default).inlineSize)
      t.children.length 0 0 locs (by
        intro k hk
        simp only [Bool.false_eq_true, ite_false, Nat.zero_add]
        have h1 : c.children.getD k default = c.children[k]'(by omega) := by
          simp [List.getD_eq_getElem?_getD, show k < c.children.length by omega]
        have h2 : t.children.getD k default = t.children[k]'hk := by
          simp [List.getD_eq_getElem?_getD, hk]
        rw [h1, h2]
        exact hfit k (by omega) hk) hl spans hc
    refine ⟨locs, vs, this, rfl, by simp [childLocs, he, hl], hll, hvl, fun k h1 h2 h3 => ?_⟩
    have := hk k h1 h2
    simp only [Bool.false_eq_true, ite_false, Nat.zero_add] at this
    have h4 : t.children.getD k default = t.children[k] := by
      simp [List.getD_eq_getElem?_getD, h3]
    rwa [h4] at this

/-- The elements of an `Array` type node, as `elements` finds them. -/
theorem elements_agree {data : Bytes} {base m fuel r : Nat} {l : TN} {th : Bytes} {v : V}
    {body : Slice} (hbody : body.offset = base + r) {isz : Nat}
    (hread : readV (view data base m) (fuel + 1) ⟨.Array, [l], th⟩ r = some v)
    (hfit : inlineSize l = some isz) :
    ∀ spans, elements data body isz = some spans →
    ∃ (locs : List Nat) (vs : List V), StartAt base spans locs ∧ v = .list vs ∧
      childLocs (view data base m) ⟨.Array, [l], th⟩ r = some locs ∧ locs.length = vs.length ∧
      ∀ k (h1 : k < locs.length) (h2 : k < vs.length),
        readV (view data base m) fuel l locs[k] = some vs[k] := by
  intro spans hc
  obtain ⟨bo, room⟩ := body
  simp only at hbody
  subst hbody
  simp only [readV, show (Encoding.Array = Encoding.Static) = False by simp,
    show (Encoding.Array = Encoding.Dynamic) = False by simp, ite_false, ite_true,
    List.length_singleton, ne_eq, not_true_eq_false, and_false] at hread
  cases hw : wordAt (view data base m) r with
  | none => rw [hw] at hread; simp at hread
  | some w =>
    rw [hw] at hread
    simp only at hread
    cases hb : blockLoop (view data base m) (readV (view data base m) fuel) [l] true (r + 32)
        (wordVal w) 0 0 with
    | none => rw [hb] at hread; simp at hread
    | some vs =>
      rw [hb] at hread
      simp at hread
      subst hread
      obtain ⟨hwv, hwb⟩ := wordAt_load hw
      simp only [length_view] at hwb
      obtain ⟨locs, hl, hll, hvl, hk⟩ := blockLoop_locs _ _ _ _ _ _ _ _ vs hb
      obtain ⟨-, hc⟩ := elements_some hc
      simp only at hc
      rw [← load_view data base m r hwb, ← hwv,
        show base + r + 32 = base + (r + 32) by omega] at hc
      have := loop_agree data base m [l] true (r + 32) (room - 32) (fun _ => isz)
        (wordVal w) 0 0 locs (by intro k _; simpa using hfit) hl spans hc
      refine ⟨locs, vs, this, rfl, by simp [childLocs, hw, hl], by omega, fun k h1 h2 => ?_⟩
      simpa using hk k h1 h2

/-- The elements of an `Array` type node, on a condition node over it. -/
theorem children_agree_array {data : Bytes} {base m fuel r : Nat} {l : TN} {th : Bytes} {v : V}
    {c : Condition} {body : Slice} (hbody : body.offset = base + r)
    (hread : readV (view data base m) (fuel + 1) ⟨.Array, [l], th⟩ r = some v)
    (hce : c.encoding = .Array) (hfit : MetaFit (c.children.headD default) l) :
    ∀ spans, children data body c = some spans →
    ∃ (locs : List Nat) (vs : List V), StartAt base spans locs ∧ v = .list vs ∧
      childLocs (view data base m) ⟨.Array, [l], th⟩ r = some locs ∧ locs.length = vs.length ∧
      ∀ k (h1 : k < locs.length) (h2 : k < vs.length),
        readV (view data base m) fuel l locs[k] = some vs[k] := by
  intro spans hc
  unfold children at hc
  rw [ite_eq_left hce] at hc
  cases hch : c.children with
  | nil => rw [hch] at hc; simp at hc
  | cons c0 rest =>
    rw [hch] at hc hfit
    exact elements_agree hbody hread hfit spans hc

/-! ## Every node `evaluate` visits -/

/-- For each pluck slot, the element type of the array that the `Pluck` node
    with that index reads (`none`: no Zip may read the slot). -/
abbrev Plucks := Nat → Option TN

/-- Operators `evaluate` does not descend through, and that store no
    span (`Pluck`) or jump (`Zip*`). -/
def NoDescend (op : Operator) : Prop :=
  op ≠ .And ∧ op ≠ .Or ∧ op ≠ .Matches ∧ op ≠ .ArraySome ∧ op ≠ .ArrayEvery ∧
    op ≠ .ArrayTailMatches ∧ op ≠ .Slice ∧ op ≠ .Pluck ∧ op ≠ .ZipSome ∧ op ≠ .ZipEvery

def IsZip (op : Operator) : Prop := op = .ZipSome ∨ op = .ZipEvery

/-- The node carries the member's inline size, or is a Zip (whose own
    slice and metadata `evaluate` does not use). -/
def MetaOk (c : Condition) (t : TN) : Prop := MetaFit c t ∨ IsZip c.operator

/-- `FitW c`: `c` may be evaluated on a window of a member (below a
    `Slice`): a leaf, a `Pluck` no Zip reads, or a further `Slice` (whose
    bound is the window). -/
inductive FitW (Γ : Plucks) : Condition → Prop
  | leaf {c} : NoDescend c.operator → FitW Γ c
  | pluck {c} : c.operator = .Pluck → Γ (cvByte c.compValue 0) = none → FitW Γ c
  | slice {c} : c.operator = .Slice → 0 < c.inlineSize → 0 < sliceSize c.compValue →
      sliceSize c.compValue ≤ 32 → FitW Γ (c.children.headD default) → FitW Γ c

/-- `FitT Γ c t`: the (annotated) condition tree `c` follows the type tree
    `t`: `Matches` over a struct has one child per member, with the
    member's inline size; array operators sit on arrays, every child with
    the element's inline size; `And` / `Or` children describe the same
    member; `Slice` sits on a word or `bytes` / `string` member and its
    child on the window; a `Pluck` whose slot a Zip reads sits on an array
    with the slot's element type; each field of a Zip follows the element
    type of the slot it reads. -/
inductive FitT (Γ : Plucks) : Condition → TN → Prop
  | leaf {c t} : NoDescend c.operator → FitT Γ c t
  | pluck {c t} : c.operator = .Pluck →
      (∀ l, Γ (cvByte c.compValue 0) = some l → ∃ th, t = ⟨.Array, [l], th⟩) → FitT Γ c t
  | zip {c t} : IsZip c.operator →
      (∀ f, f < (zipFields c).length → ∃ l, Γ (cvByte c.compValue f) = some l ∧
        MetaFit ((zipFields c).getD f default) l) →
      (∀ f l, f < (zipFields c).length → Γ (cvByte c.compValue f) = some l →
        FitT Γ ((zipFields c).getD f default) l) → FitT Γ c t
  | logical {c t} : (c.operator = .And ∨ c.operator = .Or) →
      (∀ ch ∈ c.children, MetaOk ch t) → (∀ ch ∈ c.children, FitT Γ ch t) → FitT Γ c t
  | tuple {c t} : c.operator = .Matches → t.encoding = .Tuple → c.encoding ≠ .Array →
      c.encoding ≠ .AbiEncoded → c.leadingBytes = 0 → c.children.length = t.children.length →
      (∀ k (h1 : k < c.children.length) (h2 : k < t.children.length),
        MetaFit c.children[k] t.children[k]) →
      (∀ k (h1 : k < c.children.length) (h2 : k < t.children.length),
        FitT Γ c.children[k] t.children[k]) → FitT Γ c t
  | array {c l th} : c.encoding = .Array → c.leadingBytes = 0 → c.children ≠ [] →
      (c.operator = .Matches ∨ c.operator = .ArraySome ∨ c.operator = .ArrayEvery ∨
        c.operator = .ArrayTailMatches) →
      (∀ ch ∈ c.children, MetaFit ch l) → (∀ ch ∈ c.children, FitT Γ ch l) →
      FitT Γ c ⟨.Array, [l], th⟩
  | slice {c t} : c.operator = .Slice →
      ((t.encoding = .Static ∧ c.inlineSize = 32) ∨ (t.encoding = .Dynamic ∧ c.inlineSize = 0)) →
      0 < sliceSize c.compValue → sliceSize c.compValue ≤ 32 →
      FitW Γ (c.children.headD default) → FitT Γ c t

/-- `d` in the slice `l` (with `inlineSize` `y`) is the member of type `t`
    that the encoder's walk of the argument's type tree `t0` reads at `r`
    (in the view from `base`). -/
def Member (Γ : Plucks) (data : Bytes) (base m : Nat) (t0 : TN) (d : Condition) (l : Slice)
    (y : Nat) : Prop :=
  ∃ t fuel r v, Reach (view data base m) t0 t r ∧ l.offset = base + r ∧ FitT Γ d t ∧
    readV (view data base m) fuel t r = some v ∧ MetaOk d t ∧ y = d.inlineSize

/-- `d` in the slice `l` reads `y` bytes, the whole slice, inside a member
    the encoder read: inside the word of a `Static` member (from byte `sh`),
    or inside the content of a `bytes` / `string` member (from byte `sh`). -/
def Window (Γ : Plucks) (data : Bytes) (base m : Nat) (t0 : TN) (d : Condition) (l : Slice)
    (y : Nat) : Prop :=
  FitW Γ d ∧ 0 < y ∧ y ≤ 32 ∧ l.length = y ∧ ∃ t fuel r v sh,
    Reach (view data base m) t0 t r ∧ readV (view data base m) fuel t r = some v ∧
    ((∃ w, t.encoding = .Static ∧ v = .atom w ∧ l.offset = base + r + sh ∧ sh + y ≤ 32) ∨
     (∃ b, t.encoding = .Dynamic ∧ v = .dyn b ∧ l.offset = base + r + 32 + sh ∧
       sh + y ≤ b.length))

def Site (Γ : Plucks) (data : Bytes) (base m : Nat) (t0 : TN) (d : Condition) (l : Slice)
    (y : Nat) : Prop :=
  Member Γ data base m t0 d l y ∨ Window Γ data base m t0 d l y

theorem readV_succ {t : TN} {fuel r : Nat} {d : Bytes} {v : V}
    (h : readV d fuel t r = some v) : ∃ f, fuel = f + 1 := by
  cases fuel with
  | zero => simp [readV] at h
  | succ f => exact ⟨f, rfl⟩

theorem headD_mem {c : Condition} (h : c.children ≠ []) : c.children.headD default ∈ c.children := by
  cases hc : c.children with
  | nil => exact absurd hc h
  | cons x xs => simp

/-- A `Static` member is the word at its location. -/
theorem readV_static {data : Bytes} {base m fuel r : Nat} {t : TN} {v : V}
    (h : readV (view data base m) fuel t r = some v) (he : t.encoding = .Static) :
    ∃ w, v = .atom w ∧ w = ((view data base m).drop r).take 32 ∧ r + 32 ≤ m := by
  obtain ⟨f, rfl⟩ := readV_succ h
  simp only [readV, he, ite_true] at h
  cases hw : wordAt (view data base m) r with
  | none => rw [hw] at h; simp at h
  | some w =>
    rw [hw] at h
    simp at h
    subst h
    unfold wordAt at hw
    split at hw
    · simp at hw
    · rename_i hb
      simp at hw hb
      exact ⟨w, rfl, hw.symm, by omega⟩

/-- A `bytes` / `string` member: its length word, as Roles loads it, and
    its content. -/
theorem readV_dynamic {data : Bytes} {base m fuel r : Nat} {t : TN} {v : V}
    (h : readV (view data base m) fuel t r = some v) (he : t.encoding = .Dynamic) :
    ∃ b, v = .dyn b ∧ r + 32 + b.length ≤ m ∧ load data (base + r) = b.length ∧
      b = ((view data base m).drop (r + 32)).take b.length := by
  obtain ⟨f, rfl⟩ := readV_succ h
  simp only [readV, he, show (Encoding.Dynamic = Encoding.Static) = False by simp, ite_false,
    ite_true] at h
  cases hw : wordAt (view data base m) r with
  | none => rw [hw] at h; simp at h
  | some w =>
    rw [hw] at h
    simp only at h
    split at h
    · simp at h
    · rename_i hright
      simp at h
      subst h
      obtain ⟨hwv, hwb⟩ := wordAt_load hw
      simp only [length_view] at hwb hright
      have hblen : ((List.drop (r + 32) (view data base m)).take (wordVal w)).length
          = wordVal w := by simp; omega
      refine ⟨_, rfl, by rw [hblen]; omega, ?_, by rw [hblen]⟩
      rw [hblen, ← load_view data base m r hwb, ← hwv]

theorem matchesBody_self {data : Bytes} {loc : Slice} {c : Condition}
    (h : c.encoding ≠ .AbiEncoded) : matchesBody data loc c = some loc := by
  unfold matchesBody; rw [ite_eq_right h]

/-- **Every node `evaluate` visits, on any calldata, sits where the encoder
    read the corresponding member, or reads a window inside it**, when the
    encoder's walk succeeded and the condition follows the type tree. -/
theorem visit_agree (Γ : Plucks) (data : Bytes) (base m : Nat) (t0 : TN) {c : Condition}
    {loc : Slice} {z : Nat} {p : List Nat} {d : Condition} {l : Slice} {y : Nat}
    (hv : Visit data c loc z p d l y) :
    Site Γ data base m t0 c loc z → Site Γ data base m t0 d l y := by
  induction hv with
  | here => exact id
  | @logical c loc z p d l y ch hop hmem _ ih =>
    rintro (⟨t, fuel, r, v, hR, hloc, hfit, hread, _⟩ | ⟨hw, _⟩)
    · cases hfit with
      | logical _ hm hf =>
        exact ih (Or.inl ⟨t, fuel, r, v, hR, hloc, hf ch hmem, hread, hm ch hmem, rfl⟩)
      | leaf hn => rcases hop with h | h <;> simp_all [NoDescend]
      | zip hz => rcases hop with h | h <;> rcases hz with h' | h' <;> simp_all
      | array _ _ _ hop' => rcases hop with h | h <;> rcases hop' with h' | h' | h' | h' <;> simp_all
      | _ => rcases hop with h | h <;> simp_all
    · cases hw <;> rcases hop with h | h <;> simp_all [NoDescend]
  | @matchesChild c loc z p d l y body spans i hi hop hbody hch hlen _ ih =>
    rintro (⟨t, fuel, r, v, hR, hloc, hfit, hread, _⟩ | ⟨hw, _⟩)
    · obtain ⟨f, rfl⟩ := readV_succ hread
      cases hfit with
      | tuple _ he hna hnabi hlb hl hm hf =>
        rw [matchesBody_self hnabi] at hbody; cases hbody
        obtain ⟨elocs, vs, hst, rfl, hcl, hel, hvl, hk⟩ :=
          children_agree_tuple hloc hread he hna hl hm spans hch
        have hi' : i < elocs.length := by rw [← hst.length]; exact hi
        have hic : i < c.children.length := by omega
        have hit : i < t.children.length := by omega
        have hg : c.children.getD i default = c.children[i] := by
          simp [List.getD_eq_getElem?_getD, hic]
        have hR' : Reach (view data base m) t0 t.children[i] elocs[i] := by
          have := Reach.child (k := i) hR hcl hi'
          simpa [he, List.getD_eq_getElem?_getD, hit] using this
        exact ih (Or.inl ⟨_, f, _, _, hR', hst.get i hi hi', by rw [hg]; exact hf i hic hit,
          hk i hi' (by omega) hit, Or.inl (by rw [hg]; exact hm i hic hit), rfl⟩)
      | @array _ l' th he hlb _ hop' hm hf =>
        rw [matchesBody_self (by rw [he]; decide)] at hbody; cases hbody
        have hic : i < c.children.length := by omega
        have hne : c.children ≠ [] := by intro h; rw [h] at hic; simp at hic
        obtain ⟨elocs, vs, hst, rfl, hcl, hel, hk⟩ :=
          children_agree_array hloc hread he (hm _ (headD_mem hne)) spans hch
        have hi' : i < elocs.length := by rw [← hst.length]; exact hi
        have hg : c.children.getD i default = c.children[i] := by
          simp [List.getD_eq_getElem?_getD, hic]
        have hR' : Reach (view data base m) t0 l' elocs[i] := by
          simpa using Reach.child (k := i) hR hcl hi'
        exact ih (Or.inl ⟨_, f, _, _, hR', hst.get i hi hi',
          by rw [hg]; exact hf _ (List.getElem_mem hic),
          hk i hi' (by omega), Or.inl (by rw [hg]; exact hm _ (List.getElem_mem hic)), rfl⟩)
      | leaf hn => simp_all [NoDescend]
      | zip hz => rcases hz with h | h <;> simp_all
      | logical hop' => rcases hop' with h | h <;> simp_all
      | _ => simp_all
    · cases hw <;> simp_all [NoDescend]
  | @arrayIter c loc z p d l y spans i hi hop hch _ ih =>
    rintro (⟨t, fuel, r, v, hR, hloc, hfit, hread, _⟩ | ⟨hw, _⟩)
    · obtain ⟨f, rfl⟩ := readV_succ hread
      cases hfit with
      | @array _ l' th he hlb hne hop' hm hf =>
        obtain ⟨elocs, vs, hst, rfl, hcl, hel, hk⟩ :=
          children_agree_array hloc hread he (hm _ (headD_mem hne)) spans hch
        have hi' : i < elocs.length := by rw [← hst.length]; exact hi
        have hR' : Reach (view data base m) t0 l' elocs[i] := by
          simpa using Reach.child (k := i) hR hcl hi'
        exact ih (Or.inl ⟨_, f, _, _, hR', hst.get i hi hi', hf _ (headD_mem hne),
          hk i hi' (by omega), Or.inl (hm _ (headD_mem hne)), rfl⟩)
      | leaf hn => rcases hop with h | h <;> simp_all [NoDescend]
      | zip hz => rcases hop with h | h <;> rcases hz with h' | h' <;> simp_all
      | logical hop' => rcases hop with h | h <;> rcases hop' with h' | h' <;> simp_all
      | _ => rcases hop with h | h <;> simp_all
    · cases hw <;> rcases hop with h | h <;> simp_all [NoDescend]
  | @arrayTail c loc z p d l y spans j hj hop hch hle hjc _ ih =>
    rintro (⟨t, fuel, r, v, hR, hloc, hfit, hread, _⟩ | ⟨hw, _⟩)
    · obtain ⟨f, rfl⟩ := readV_succ hread
      cases hfit with
      | @array _ l' th he hlb hne hop' hm hf =>
        obtain ⟨elocs, vs, hst, rfl, hcl, hel, hk⟩ :=
          children_agree_array hloc hread he (hm _ (headD_mem hne)) spans hch
        have hg : c.children.getD j default = c.children[j] := by
          simp [List.getD_eq_getElem?_getD, hjc]
        have hlen' := hst.length
        have hj' : spans.length - c.children.length + j < elocs.length := by omega
        have hR' : Reach (view data base m) t0 l' elocs[spans.length - c.children.length + j] := by
          simpa using Reach.child (k := spans.length - c.children.length + j) hR hcl hj'
        exact ih (Or.inl ⟨_, f, _, _, hR', hst.get _ hj hj',
          by rw [hg]; exact hf _ (List.getElem_mem hjc),
          hk _ hj' (by omega), Or.inl (by rw [hg]; exact hm _ (List.getElem_mem hjc)), rfl⟩)
      | leaf hn => simp_all [NoDescend]
      | zip hz => rcases hz with h | h <;> simp_all
      | logical hop' => rcases hop' with h | h <;> simp_all
      | _ => simp_all
    · cases hw <;> simp_all [NoDescend]
  | @slice c loc z p d l y payload hop hpay hle _ ih =>
    rintro (⟨t, fuel, r, v, hR, hloc, hfit, hread, _, hz⟩ |
      ⟨hw, hzpos, _, hlen, t, fuel, r, v, sh, hR, hread, hwin⟩)
    · cases hfit with
      | slice _ hkind hs1 hs2 hfw =>
        apply ih
        right
        refine ⟨hfw, hs1, hs2, rfl, t, fuel, r, v, sliceShift c.compValue, hR, hread, ?_⟩
        rcases hkind with ⟨hst, hsz⟩ | ⟨hdy, hsz⟩
        · left
          obtain ⟨w, rfl, _, _⟩ := readV_static hread hst
          rw [hz, hsz] at hpay
          rcases slicePayload_some hpay with ⟨-, -, rfl⟩ | ⟨h0, -⟩
          · exact ⟨w, hst, rfl, by simp only; rw [hloc], by simpa using hle⟩
          · omega
        · right
          obtain ⟨b, rfl, _, hld, _⟩ := readV_dynamic hread hdy
          rw [hz, hsz] at hpay
          rcases slicePayload_some hpay with ⟨h0, -⟩ | ⟨-, -, -, rfl⟩
          · omega
          · simp only at hle
            rw [hloc, hld] at hle
            exact ⟨b, hdy, rfl, by simp only; rw [hloc], hle⟩
      | leaf hn => exact absurd hop hn.2.2.2.2.2.2.1
      | zip hz => rcases hz with h | h <;> simp_all
      | logical hop' => rcases hop' with h | h <;> simp_all
      | array _ _ _ hop' => rcases hop' with h | h | h | h <;> simp_all
      | _ => simp_all
    · cases hw with
      | slice _ hin hs1 hs2 hfw =>
        apply ih
        right
        refine ⟨hfw, hs1, hs2, rfl, t, fuel, r, v, sh + sliceShift c.compValue, hR, hread, ?_⟩
        rcases slicePayload_some hpay with ⟨-, -, rfl⟩ | ⟨h0, -⟩
        · simp only at hle
          rcases hwin with ⟨w, h1, h2, h3, h4⟩ | ⟨b, h1, h2, h3, h4⟩
          · exact Or.inl ⟨w, h1, h2, by simp only; rw [h3]; omega, by omega⟩
          · exact Or.inr ⟨b, h1, h2, by simp only; rw [h3]; omega, by omega⟩
        · omega
      | leaf hn => exact absurd hop hn.2.2.2.2.2.2.1
      | pluck h => simp_all

/-! ## The operands -/

/-- **At a `Static` member, the word Roles compares is the word the encoder
    hashes** (unless Roles finds it out of bounds, which fails the node). -/
theorem static_input {data : Bytes} {base m fuel r : Nat} {t : TN} {w : Bytes} {d : Condition}
    {l : Slice} (hl : l.offset = base + r) (hin : Within data l)
    (he : t.encoding = .Static) (hread : readV (view data base m) fuel t r = some (.atom w))
    (hmeta : MetaFit d t) (hde : d.encoding ≠ .None) :
    input data l d.inlineSize d = .overflow ∨ input data l d.inlineSize d = .word (wordVal w) := by
  obtain ⟨w', hv, hw', hm⟩ := readV_static hread he
  injection hv with hv
  subst hv
  obtain ⟨e, cs, th⟩ := t
  simp only at he
  subst he
  have hsz : d.inlineSize = 32 := by
    unfold MetaFit at hmeta; simp [inlineSize] at hmeta; exact hmeta.symm
  unfold Within at hin
  unfold input operand
  rw [ite_eq_right hde, hsz, ite_eq_left (by decide)]
  by_cases h32 : 32 ≤ l.length
  · right
    rw [slicePayload_inline (by decide) h32]
    simp only [Nat.lt_irrefl, ite_false, Slice.bytes]
    rw [hw', hl, take_view data base m r 32 (by omega) (by omega)]
  · left
    unfold slicePayload
    rw [ite_eq_left (by decide), ite_eq_left (by omega)]

/-- **At a `Dynamic` member, the operand Roles compares is computed from
    the length word and the bytes the encoder hashes**: unless Roles finds
    the value out of bounds or not canonically padded (which fails the
    node), the calldata at the member holds `b.length`, then `b`, and Roles'
    operand is `_read` of exactly that encoding (`expectInput`). Assumes
    `b.length + 31 < 2^256` (the contract reverts on the overflow; the model
    does not). -/
theorem dynamic_input {data : Bytes} {base m fuel r : Nat} {t : TN} {b : Bytes} {d : Condition}
    {l : Slice} (hl : l.offset = base + r) (hwithin : Within data l)
    (he : t.encoding = .Dynamic) (hread : readV (view data base m) fuel t r = some (.dyn b))
    (hmeta : MetaFit d t) (hde : d.encoding = .Dynamic) (hb : b.length + 31 < 2 ^ 256)
    (hin : input data l d.inlineSize d ≠ .overflow) :
    load data (base + r) = b.length ∧ (data.drop (base + r + 32)).take b.length = b ∧
      input data l d.inlineSize d =
        expectInput ((data.drop (base + r)).take (32 + ceil32 b.length)) := by
  obtain ⟨b', hv, hbm, hld, hb'⟩ := readV_dynamic hread he
  injection hv with hv
  subst hv
  obtain ⟨e, cs, th⟩ := t
  simp only at he
  subst he
  have hsz : d.inlineSize = 0 := by
    unfold MetaFit at hmeta; simp [inlineSize] at hmeta; exact hmeta.symm
  have hne : d.encoding ≠ .None := by rw [hde]; decide
  unfold Within at hwithin
  have hc := ceil32_ge b.length
  unfold input at hin ⊢
  rw [ite_eq_right hne] at hin ⊢
  have hop : ∀ op, operand data l d.inlineSize d = some op →
      op = ⟨l.offset, 32 + ceil32 b.length⟩ ∧ 32 + ceil32 b.length ≤ l.length := by
    intro op hop
    unfold operand sliceRegion at hop
    rw [hsz, ite_eq_right (by omega)] at hop
    cases hr : region data l d with
    | none => rw [hr] at hop; cases hop
    | some n =>
      rw [hr] at hop
      simp only [Option.map_some, Option.some.injEq] at hop
      obtain ⟨h32, hle, rfl, hpad⟩ := region_bytes_some hsz (.inl hde) hr
      rw [hl, hld, roundUp_eq _ hb] at hpad
      subst hop
      rw [hl, hld, roundUp_eq _ hb]
      exact ⟨rfl, by omega⟩
  cases ho : operand data l d.inlineSize d with
  | none => rw [ho] at hin; exact absurd rfl hin
  | some op =>
    obtain ⟨rfl, hroom⟩ := hop op ho
    refine ⟨hld, ?_, ?_⟩
    · have htv := take_view data base m (r + 32) b.length (by omega) (by omega)
      rw [show base + r + 32 = base + (r + 32) by omega, ← htv]
      exact hb'.symm
    · simp only [Slice.bytes]
      rw [hl]
      have htl : ((data.drop (base + r)).take (32 + ceil32 b.length)).length =
          32 + ceil32 b.length := by simp; omega
      unfold expectInput
      rw [htl]
      by_cases h : 32 + ceil32 b.length = 32
      · rw [ite_eq_left h, ite_eq_right (by omega)]
      · rw [ite_eq_right h, ite_eq_left (by omega)]

/-! ## The `message` argument -/

/-- `SignTypedMessageLib`'s fallback reads argument `i` (`domain`,
    `message`, `types`) at `calldataload(4 + 32 i) + 4` (`+ 0x20` past the
    length word for `bytes`). Where Roles' root `Matches` (leading bytes 4)
    finds that argument as an offset slot, it is the same place. -/
theorem fallback_offset (data : Bytes) (room i : Nat) (sp : Slice) (next : Nat)
    (h : child data ⟨4, room⟩ (32 * i) 0 = some (sp, next)) :
    sp.offset = load data (4 + 32 * i) + 4 := by
  obtain ⟨-, -, hsp⟩ := child_some h
  rcases hsp with ⟨h0, -⟩ | ⟨-, -, -, rfl⟩
  · omega
  · simp only; omega

/-- The hypotheses on the condition node of the `message` (or `domain`)
    argument: a `Matches` on nested calldata (`AbiEncoded`, leading bytes 0)
    whose children follow the members of the struct's type tree `tm`. -/
structure MsgFit (Γ : Plucks) (c : Condition) (tm : TN) : Prop where
  op : c.operator = .Matches
  enc : c.encoding = .AbiEncoded
  lb : c.leadingBytes = 0
  tuple : tm.encoding = .Tuple
  len : c.children.length = tm.children.length
  metas : ∀ k (h1 : k < c.children.length) (h2 : k < tm.children.length),
    MetaFit c.children[k] tm.children[k]
  fits : ∀ k (h1 : k < c.children.length) (h2 : k < tm.children.length),
    FitT Γ c.children[k] tm.children[k]

/-- **On the `message` argument**: below a `Matches` on nested calldata in
    the slice `L` whose children follow the primary type's tree, every node
    `evaluate` visits sits where the encoder reads the corresponding member
    of the message, or reads a window inside it. The library sees the
    message at `L.offset + 32` (`fallback_offset` with `i = 1`; `m` is the
    length word there). -/
theorem message_agree (Γ : Plucks) (data : Bytes) (L : Slice) (m : Nat) {c : Condition} {tm : TN}
    {fuel : Nat} {v : V} (hmf : MsgFit Γ c tm) (hL : 0 < L.offset)
    (hread : readV (view data (L.offset + 32) m) fuel tm 0 = some v)
    {z : Nat} {p : List Nat} {d : Condition} {l : Slice} {y : Nat}
    (hv : Visit data c L z p d l y) :
    (p = [] ∧ d = c) ∨ (p ≠ [] ∧ Site Γ data (L.offset + 32) m tm d l y) := by
  obtain ⟨f, rfl⟩ := readV_succ hread
  have hop := hmf.op
  cases hv with
  | here => exact Or.inl ⟨rfl, rfl⟩
  | logical _ hop' => rcases hop' with h | h <;> simp_all
  | matchesChild body spans i hi _ hbody hch hl hv' =>
    right
    refine ⟨by simp, ?_⟩
    have hbo : body.offset = L.offset + 32 + 0 := by
      rcases matchesBody_some hbody with ⟨hne, -⟩ | ⟨-, payload, hp, -, rfl⟩
      · exact absurd hmf.enc hne
      · rcases hp with ⟨h0, -⟩ | ⟨-, hp⟩
        · omega
        · rcases slicePayload_some hp with ⟨h0, -⟩ | ⟨-, -, -, rfl⟩
          · omega
          · simp only [hmf.lb]
    obtain ⟨elocs, vs, hst, rfl, hcl, hel, hvl, hk⟩ :=
      children_agree_tuple hbo hread hmf.tuple (by rw [hmf.enc]; decide) hmf.len hmf.metas spans hch
    have hi' : i < elocs.length := by rw [← hst.length]; exact hi
    have hic : i < c.children.length := by omega
    have hit : i < tm.children.length := by rw [← hmf.len]; exact hic
    have hg : c.children.getD i default = c.children[i] := by
      simp [List.getD_eq_getElem?_getD, hic]
    rw [hg] at hv'
    have hR : Reach (view data (L.offset + 32) m) tm tm.children[i] elocs[i] := by
      have := Reach.child (k := i) (Reach.root (d := view data (L.offset + 32) m) (t0 := tm)) hcl hi'
      simpa [hmf.tuple, List.getD_eq_getElem?_getD, hit] using this
    exact visit_agree Γ data (L.offset + 32) m tm hv' (Or.inl ⟨_, f, _, _, hR, hst.get i hi hi',
      hmf.fits i hic hit, hk i hi' (by omega) hit, Or.inl (hmf.metas i hic hit), rfl⟩)
  | arrayIter _ _ _ hop' => rcases hop' with h | h <;> simp_all
  | arrayTail _ _ _ hop' => simp_all
  | slice _ hop' => simp_all

/-- **In a window, the word Roles compares is cut from what the encoder
    hashes**: bytes `[sh, sh + y)` of the member's word, or of the content of
    the `bytes` / `string` member. -/
theorem window_input {Γ : Plucks} {data : Bytes} {base m : Nat} {t0 : TN} {d : Condition}
    {l : Slice} {y : Nat} (hw : Window Γ data base m t0 d l y) (hwithin : Within data l)
    (hde : d.encoding ≠ .None) :
    ∃ t fuel r v sh, Reach (view data base m) t0 t r ∧
      readV (view data base m) fuel t r = some v ∧
      ((∃ w, v = .atom w ∧ input data l y d = .word (wordVal ((w.drop sh).take y))) ∨
       (∃ b, v = .dyn b ∧ input data l y d = .word (wordVal ((b.drop sh).take y)))) := by
  obtain ⟨_, hpos, h32, hlen, t, fuel, r, v, sh, hR, hread, hwin⟩ := hw
  unfold Within at hwithin
  have hin : input data l y d = .word (wordVal ((data.drop l.offset).take y)) := by
    unfold input operand slicePayload
    rw [ite_eq_right hde, ite_eq_left hpos, ite_eq_left hpos, ite_eq_right (by omega)]
    simp only [Slice.bytes]
    rw [ite_eq_right (by omega)]
  rw [hin]
  refine ⟨t, fuel, r, v, sh, hR, hread, ?_⟩
  rcases hwin with ⟨w, hst, rfl, hl, hle⟩ | ⟨b, hdy, rfl, hl, hle⟩
  · obtain ⟨w', hv, hw', hm⟩ := readV_static hread hst
    injection hv with hv
    subst hv
    left
    refine ⟨w, rfl, ?_⟩
    congr 2
    rw [hw', List.drop_take, List.take_take, show min y (32 - sh) = y by omega,
      List.drop_drop, hl, take_view data base m (r + sh) y (by omega) (by omega)]
    congr 2; omega
  · obtain ⟨b', hv, hbm, _, hb'⟩ := readV_dynamic hread hdy
    injection hv with hv
    subst hv
    right
    refine ⟨b, rfl, ?_⟩
    congr 2
    rw [hb', List.drop_take, List.take_take, show min y (b.length - sh) = y by omega,
      List.drop_drop, hl, take_view data base m (r + 32 + sh) y (by omega) (by omega)]
    congr 2; omega

end EIP712
