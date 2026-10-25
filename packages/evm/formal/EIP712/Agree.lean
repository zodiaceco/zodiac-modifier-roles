import EIP712.Decode
import DecoderFaithfulness.Decode

/-!
# Roles inspects what the encoder hashes

`SignTypedMessageLib`'s fallback hands `EIP712Encoder` the `message`
argument as calldata from `base` (the content of the `bytes` parameter, at
the offset the head word gives), of the length its length word gives,
without checking either against `msg.data`. So the library reads
`view data base m`: the calldata from `base`, zeros past its end.

Roles reads the same calldata with `AbiLocation.children`
(`DecoderFaithfulness.Roles`), with bound checks against `msg.data`.

* `loop_agree` / `children_agree`: when the encoder's walk of a block
  succeeds and Roles' `children` succeeds on a condition node whose children
  have the encoder's inline sizes (`MetaFit`), Roles finds every child
  exactly at `base +` the encoder's location.
* `visit_agree`: for a condition tree that follows the type tree (`FitT`),
  every node `evaluate` visits sits at `base +` the location where the
  encoder reads the corresponding member, and that member was read.
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

/-- The condition node `ch` carries the inline metadata (`inlined`, `size`,
    as `annotate` computes them) of the encoder's type node `t`. -/
def MetaFit (ch : Condition) (t : TN) : Prop :=
  ∃ isz, inlineSize t = some isz ∧ (ch.inlined = true ↔ 0 < isz) ∧ ch.size = isz

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

/-- **Roles' `children` loop finds every child where the encoder does**,
    on any calldata: both use the head offset, the same backwards-offset
    check and the same tail location; Roles only adds bound checks against
    `msg.data`. -/
theorem loop_agree (data : Bytes) (base m : Nat) (cs : List TN) (isArray : Bool) (bl : Nat)
    (childAt : Nat → Condition) :
    ∀ n i h locs, (∀ k, k < n →
      MetaFit (childAt (i + k)) (cs.getD (if isArray then 0 else i + k) default)) →
    blockLoop (view data base m) (fun _ l => some l) cs isArray bl n i h = some locs →
    ∀ locs', childrenLoop data (base + bl) childAt n i h = some locs' →
      locs' = locs.map (base + ·)
  | 0, _, _, locs, _, e, locs', e' => by
    simp [blockLoop] at e; simp [childrenLoop] at e'; subst e; subst e'; rfl
  | n + 1, i, h, locs, hfit, e, locs', e' => by
    obtain ⟨isz, hisz, hinl, hsize⟩ := hfit 0 (by omega)
    simp only [Nat.add_zero] at hisz hinl hsize
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
        have hfit' : ∀ k, k < n → MetaFit (childAt (i + 1 + k))
            (cs.getD (if isArray then 0 else i + 1 + k) default) := by
          intro k hk
          have := hfit (k + 1) (by omega)
          rw [show i + 1 + k = i + (k + 1) by omega]
          exact this
        simp only [childLocation, hisz] at hc
        by_cases hpos : 0 < isz
        · -- inline child
          have hin : (childAt i).inlined = true := hinl.mpr hpos
          rw [if_pos (by omega)] at hc
          split at hc
          · simp at hc
          · simp at hc
            obtain ⟨rfl, rfl⟩ := hc
            rw [hin] at e'
            simp only [ite_true, hsize] at e'
            split at e'
            · simp at e'
            · cases hr : childrenLoop data (base + bl) childAt n (i + 1) (h + isz) with
              | none => rw [hr] at e'; simp at e'
              | some rs =>
                rw [hr] at e'
                simp at e'
                subst e'
                rw [if_pos (by omega)] at hb
                have := loop_agree data base m cs isArray bl childAt n (i + 1) (h + isz) ls hfit' hb rs hr
                simp [this]; omega
        · -- offset child
          have hin : (childAt i).inlined = false := by
            cases hh : (childAt i).inlined
            · rfl
            · exact absurd (hinl.mp hh) hpos
          have hz : isz = 0 := by omega
          subst hz
          simp only [gt_iff_lt, Nat.lt_irrefl, ite_false] at hc
          split at hc
          · simp at hc
          · rename_i hhead
            split at hc
            · simp at hc
            · rename_i hback
              split at hc
              · simp at hc
              · rename_i htail
                simp at hc
                obtain ⟨rfl, rfl⟩ := hc
                rw [hin] at e'
                simp only [Bool.false_eq_true, ite_false] at e'
                have hlv := load_view data base m (bl + h) (by simp at hhead; omega)
                simp only [length_view] at hhead htail
                -- Roles' `_tailLocation`
                unfold tailLocation at e'
                split at e'
                · simp at e'
                · rename_i hh2
                  rw [show base + bl + h = base + (bl + h) by omega, ← hlv] at e'
                  rw [if_neg hback] at e'
                  split at e'
                  · simp at e'
                  · split at e'
                    · simp at e'
                    · cases hr : childrenLoop data (base + bl) childAt n (i + 1) (h + 32) with
                      | none => rw [hr] at e'; simp at e'
                      | some rs =>
                        rw [hr] at e'
                        simp at e'
                        subst e'
                        simp only [gt_iff_lt, Nat.lt_irrefl, ite_false] at hb
                        have := loop_agree data base m cs isArray bl childAt n (i + 1) (h + 32) ls
                          hfit' hb rs hr
                        simp [this]; omega

/-! ## Per node -/

/-- The children of a `Tuple` type node: where Roles' `children` finds them
    on a `Matches` node over it, the encoder read them. -/
theorem children_agree_tuple {data : Bytes} {base m fuel r : Nat} {t : TN} {v : V} {c : Condition}
    (hread : readV (view data base m) (fuel + 1) t r = some v) (he : t.encoding = .Tuple)
    (hce : c.encoding ≠ .Array) (hlen : c.children.length = t.children.length)
    (hfit : ∀ k (h1 : k < c.children.length) (h2 : k < t.children.length),
      MetaFit c.children[k] t.children[k]) :
    ∀ locs', children data (base + r) c = some locs' →
    ∃ (locs : List Nat) (vs : List V), locs' = locs.map (base + ·) ∧ v = .list vs ∧ locs.length = t.children.length ∧
      vs.length = t.children.length ∧
      ∀ k (h1 : k < locs.length) (h2 : k < vs.length) (h3 : k < t.children.length),
        readV (view data base m) fuel t.children[k] locs[k] = some vs[k] := by
  intro locs' hc
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
    rw [if_neg hce, hlen] at hc
    have := loop_agree data base m t.children false r (fun i => c.children.getD i default)
      t.children.length 0 0 locs (by
        intro k hk
        simp only [Bool.false_eq_true, ite_false, Nat.zero_add]
        have h1 : c.children.getD k default = c.children[k]'(by omega) := by
          simp [List.getD_eq_getElem?_getD, show k < c.children.length by omega]
        have h2 : t.children.getD k default = t.children[k]'hk := by
          simp [List.getD_eq_getElem?_getD, hk]
        rw [h1, h2]
        exact hfit k (by omega) hk) hl locs' hc
    refine ⟨locs, vs, this, rfl, hll, hvl, fun k h1 h2 h3 => ?_⟩
    have := hk k h1 h2
    simp only [Bool.false_eq_true, ite_false, Nat.zero_add] at this
    have h4 : t.children.getD k default = t.children[k] := by
      simp [List.getD_eq_getElem?_getD, h3]
    rwa [h4] at this

/-- The elements of an `Array` type node. -/
theorem children_agree_array {data : Bytes} {base m fuel r : Nat} {l : TN} {th : Bytes} {v : V}
    {c : Condition}
    (hread : readV (view data base m) (fuel + 1) ⟨.Array, [l], th⟩ r = some v)
    (hce : c.encoding = .Array) (hfit : MetaFit (c.children.headD default) l) :
    ∀ locs', children data (base + r) c = some locs' →
    ∃ (locs : List Nat) (vs : List V), locs' = locs.map (base + ·) ∧ v = .list vs ∧ locs.length = vs.length ∧
      ∀ k (h1 : k < locs.length) (h2 : k < vs.length),
        readV (view data base m) fuel l locs[k] = some vs[k] := by
  intro locs' hc
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
      unfold children at hc
      rw [if_pos hce] at hc
      split at hc
      · simp at hc
      · rw [show base + r + 32 = base + (r + 32) by omega, ← load_view data base m r hwb, ← hwv] at hc
        have := loop_agree data base m [l] true (r + 32) (fun _ => c.children.headD default)
          (wordVal w) 0 0 locs (by intro k _; simpa using hfit) hl locs' hc
        refine ⟨locs, vs, this, rfl, by omega, fun k h1 h2 => ?_⟩
        simpa using hk k h1 h2

/-! ## Every node `evaluate` visits -/

/-- Operators `evaluate` does not descend through. -/
def NoDescend (op : Operator) : Prop :=
  op ≠ .And ∧ op ≠ .Or ∧ op ≠ .Matches ∧ op ≠ .ArraySome ∧ op ≠ .ArrayEvery ∧
    op ≠ .ArrayTailMatches ∧ op ≠ .Slice

/-- `FitT c t`: the (annotated) condition tree `c` follows the type tree
    `t`: `Matches` over a struct has one child per member, with the
    member's inline metadata; array operators sit on arrays, every child
    with the element's metadata; `And` / `Or` children describe the same
    member. `Slice` is not covered. -/
inductive FitT : Condition → TN → Prop
  | leaf {c t} : NoDescend c.operator → FitT c t
  | logical {c t} : (c.operator = .And ∨ c.operator = .Or) →
      (∀ ch ∈ c.children, MetaFit ch t) → (∀ ch ∈ c.children, FitT ch t) → FitT c t
  | tuple {c t} : c.operator = .Matches → t.encoding = .Tuple → c.encoding ≠ .Array →
      c.encoding ≠ .AbiEncoded → c.leadingBytes = 0 → c.children.length = t.children.length →
      (∀ k (h1 : k < c.children.length) (h2 : k < t.children.length),
        MetaFit c.children[k] t.children[k]) →
      (∀ k (h1 : k < c.children.length) (h2 : k < t.children.length),
        FitT c.children[k] t.children[k]) → FitT c t
  | array {c l th} : c.encoding = .Array → c.leadingBytes = 0 → c.children ≠ [] →
      (c.operator = .Matches ∨ c.operator = .ArraySome ∨ c.operator = .ArrayEvery ∨
        c.operator = .ArrayTailMatches) →
      (∀ ch ∈ c.children, MetaFit ch l) → (∀ ch ∈ c.children, FitT ch l) →
      FitT c ⟨.Array, [l], th⟩

theorem readV_succ {t : TN} {fuel r : Nat} {d : Bytes} {v : V}
    (h : readV d fuel t r = some v) : ∃ f, fuel = f + 1 := by
  cases fuel with
  | zero => simp [readV] at h
  | succ f => exact ⟨f, rfl⟩

theorem headD_mem {c : Condition} (h : c.children ≠ []) : c.children.headD default ∈ c.children := by
  cases hc : c.children with
  | nil => exact absurd hc h
  | cons x xs => simp

/-- **Every node `evaluate` visits, on any calldata, sits where the encoder
    read the corresponding member** (`base +` its location in the view), when
    the encoder's walk succeeded and the condition follows the type tree. -/
theorem visit_agree (data : Bytes) (base m : Nat) {c : Condition} {loc : Nat} {p : List Nat}
    {d : Condition} {l : Nat} (hv : Visit data c loc p d l) :
    ∀ {t fuel r v}, loc = base + r → FitT c t → readV (view data base m) fuel t r = some v →
    ∃ t' fuel' r' v', l = base + r' ∧ FitT d t' ∧ readV (view data base m) fuel' t' r' = some v' ∧
      (MetaFit c t → MetaFit d t') := by
  induction hv with
  | here =>
    intro t fuel r v hloc hfit hread
    exact ⟨t, fuel, r, v, hloc, hfit, hread, id⟩
  | @logical c loc p d l ch hop hmem _ ih =>
    intro t fuel r v hloc hfit hread
    cases hfit with
    | leaf hn => rcases hop with h | h <;> simp_all [NoDescend]
    | logical _ hm hf =>
      obtain ⟨t', f', r', v', h1, h2, h3, h4⟩ := ih hloc (hf ch hmem) hread
      exact ⟨t', f', r', v', h1, h2, h3, fun _ => h4 (hm ch hmem)⟩
    | tuple hop' => rcases hop with h | h <;> simp_all
    | array _ _ _ hop' => rcases hop with h | h <;> rcases hop' with h' | h' | h' | h' <;> simp_all
  | @matchesChild c loc p d l locs i hi hop hch hlen _ ih =>
    intro t fuel r v hloc hfit hread
    obtain ⟨f, rfl⟩ := readV_succ hread
    cases hfit with
    | leaf hn => simp_all [NoDescend]
    | logical hop' => rcases hop' with h | h <;> simp_all
    | tuple _ he hna hnabi hlb hl hm hf =>
      rw [if_neg (by rintro ⟨_, h⟩; exact hnabi h), hlb, Nat.add_zero, hloc] at hch
      obtain ⟨elocs, vs, rfl, rfl, hel, hvl, hk⟩ := children_agree_tuple hread he hna hl hm locs hch
      have hi' : i < elocs.length := by simpa using hi
      have hic : i < c.children.length := by simp at hlen; omega
      have hit : i < t.children.length := by omega
      have hg : c.children.getD i default = c.children[i] := by
        simp [List.getD_eq_getElem?_getD, hic]
      obtain ⟨t', f', r', v', h1, h2, h3, h4⟩ := ih (by simp) (by rw [hg]; exact hf i hic hit)
        (hk i hi' (by omega) hit)
      exact ⟨t', f', r', v', h1, h2, h3, fun _ => h4 (by rw [hg]; exact hm i hic hit)⟩
    | @array _ l' th he hlb _ hop' hm hf =>
      rw [if_neg (by rintro ⟨_, h⟩; rw [he] at h; exact absurd h (by decide)), hlb, Nat.add_zero,
        hloc] at hch
      have hic : i < c.children.length := by omega
      have hne : c.children ≠ [] := by intro h; rw [h] at hic; simp at hic
      obtain ⟨elocs, vs, rfl, rfl, hel, hk⟩ :=
        children_agree_array hread he (hm _ (headD_mem hne)) locs hch
      have hi' : i < elocs.length := by simpa using hi
      have hg : c.children.getD i default = c.children[i] := by
        simp [List.getD_eq_getElem?_getD, hic]
      obtain ⟨t', f', r', v', h1, h2, h3, h4⟩ := ih (by simp)
        (by rw [hg]; exact hf _ (List.getElem_mem hic)) (hk i hi' (by omega))
      exact ⟨t', f', r', v', h1, h2, h3, fun _ => h4 (by rw [hg]; exact hm _ (List.getElem_mem hic))⟩
  | @arrayIter c loc p d l locs i hi hop hch _ ih =>
    intro t fuel r v hloc hfit hread
    obtain ⟨f, rfl⟩ := readV_succ hread
    cases hfit with
    | leaf hn => rcases hop with h | h <;> simp_all [NoDescend]
    | logical hop' => rcases hop with h | h <;> rcases hop' with h' | h' <;> simp_all
    | tuple hop' => rcases hop with h | h <;> simp_all
    | @array _ l' th he hlb hne hop' hm hf =>
      rw [hloc] at hch
      obtain ⟨elocs, vs, rfl, rfl, hel, hk⟩ :=
        children_agree_array hread he (hm _ (headD_mem hne)) locs hch
      have hi' : i < elocs.length := by simpa using hi
      obtain ⟨t', f', r', v', h1, h2, h3, h4⟩ := ih (by simp) (hf _ (headD_mem hne))
        (hk i hi' (by omega))
      exact ⟨t', f', r', v', h1, h2, h3, fun _ => h4 (hm _ (headD_mem hne))⟩
  | @arrayTail c loc p d l locs j hj hop hch hle hjc _ ih =>
    intro t fuel r v hloc hfit hread
    obtain ⟨f, rfl⟩ := readV_succ hread
    cases hfit with
    | leaf hn => simp_all [NoDescend]
    | logical hop' => rcases hop' with h' | h' <;> simp_all
    | tuple hop' => simp_all
    | @array _ l' th he hlb hne hop' hm hf =>
      rw [hloc] at hch
      obtain ⟨elocs, vs, rfl, rfl, hel, hk⟩ :=
        children_agree_array hread he (hm _ (headD_mem hne)) locs hch
      have hg : c.children.getD j default = c.children[j] := by
        simp [List.getD_eq_getElem?_getD, hjc]
      have hj' : elocs.length - c.children.length + j < elocs.length := by simpa using hj
      obtain ⟨t', f', r', v', h1, h2, h3, h4⟩ := ih (by simp)
        (by rw [hg]; exact hf _ (List.getElem_mem hjc)) (hk _ hj' (by omega))
      exact ⟨t', f', r', v', h1, h2, h3, fun _ => h4 (by rw [hg]; exact hm _ (List.getElem_mem hjc))⟩
  | @slice c loc p d l hop _ _ _ _ =>
    intro t fuel r v hloc hfit hread
    cases hfit with
    | leaf hn => exact absurd hop hn.2.2.2.2.2.2
    | logical hop' => rcases hop' with h | h <;> simp_all
    | tuple hop' => simp_all
    | array _ _ _ hop' => rcases hop' with h | h | h | h <;> simp_all

/-! ## The operands -/

theorem input_size0 (data : Bytes) (loc : Nat) (d : Condition) (hne : d.encoding ≠ .None)
    (hsz : d.size = 0) :
    input data loc d = (if loc + size data loc d > data.length then .overflow
      else if size data loc d = 32 then .word (load data loc)
      else if size data loc d < 32 then .word (wordVal ((data.drop loc).take (size data loc d)))
      else .hash ((data.drop loc).take (size data loc d))) := by
  unfold input
  rw [if_neg hne, hsz]
  rfl

theorem load_eq_take {data : Bytes} {loc : Nat} (h : loc + 32 ≤ data.length) :
    load data loc = wordVal ((data.drop loc).take 32) := by
  unfold load
  rw [List.take_append_of_le_length (by simp; omega)]

/-- **At a `Static` member, the word Roles compares is the word the encoder
    hashes** (unless Roles finds it out of bounds, which fails the node). -/
theorem static_input {data : Bytes} {base m fuel r : Nat} {t : TN} {w : Bytes} {d : Condition}
    (he : t.encoding = .Static) (hread : readV (view data base m) fuel t r = some (.atom w))
    (hmeta : MetaFit d t) (hde : d.encoding ≠ .None) :
    input data (base + r) d = .overflow ∨ input data (base + r) d = .word (wordVal w) := by
  obtain ⟨f, rfl⟩ := readV_succ hread
  simp only [readV, he, ite_true] at hread
  cases hw : wordAt (view data base m) r with
  | none => rw [hw] at hread; simp at hread
  | some w' =>
    rw [hw] at hread
    simp at hread
    subst hread
    obtain ⟨hwv, hwb⟩ := wordAt_load hw
    simp only [length_view] at hwb
    obtain ⟨isz, hisz, _, hsz⟩ := hmeta
    obtain ⟨e, cs, th⟩ := t
    simp only at he
    subst he
    simp [inlineSize] at hisz
    subst hisz
    unfold input
    rw [if_neg hde, hsz]
    simp only [ne_eq, show ¬(32 = 0) from by decide, not_false_eq_true, ite_true]
    split
    · exact Or.inl rfl
    · right
      rw [hwv, load_view data base m r hwb]

/-- **At a `Dynamic` member, the operand Roles compares is computed from
    the length word and the bytes the encoder hashes**: unless Roles finds
    the value out of bounds (which fails the node), the calldata at the
    member holds `b.length`, then `b`, and Roles' operand is `__input` of
    exactly that encoding (`expectInput`). Assumes `b.length + 31 < 2^256`
    (the contract reverts on the overflow; the model does not). -/
theorem dynamic_input {data : Bytes} {base m fuel r : Nat} {t : TN} {b : Bytes} {d : Condition}
    (he : t.encoding = .Dynamic) (hread : readV (view data base m) fuel t r = some (.dyn b))
    (hmeta : MetaFit d t) (hde : d.encoding = .Dynamic) (hb : b.length + 31 < 2 ^ 256)
    (hin : input data (base + r) d ≠ .overflow) :
    load data (base + r) = b.length ∧ (data.drop (base + r + 32)).take b.length = b ∧
      input data (base + r) d = expectInput ((data.drop (base + r)).take (32 + ceil32 b.length)) := by
  obtain ⟨f, rfl⟩ := readV_succ hread
  simp only [readV, he, show (Encoding.Dynamic = Encoding.Static) = False by simp, ite_false,
    ite_true] at hread
  cases hw : wordAt (view data base m) r with
  | none => rw [hw] at hread; simp at hread
  | some w =>
    rw [hw] at hread
    simp only at hread
    split at hread
    · simp at hread
    · rename_i hright
      simp at hread
      subst hread
      obtain ⟨hwv, hwb⟩ := wordAt_load hw
      simp only [length_view] at hwb hright
      have hlv := load_view data base m r hwb
      have hblen : ((List.drop (r + 32) (view data base m)).take (wordVal w)).length
          = wordVal w := by simp; omega
      rw [hblen] at hb ⊢
      obtain ⟨isz, hisz, _, hsz⟩ := hmeta
      obtain ⟨e, cs, th⟩ := t
      simp only at he
      subst he
      simp [inlineSize] at hisz
      subst hisz
      have hld : load data (base + r) = wordVal w := by rw [← hlv, ← hwv]
      have hne : d.encoding ≠ .None := by rw [hde]; decide
      rw [input_size0 data _ d hne hsz] at hin ⊢
      have hloc32 : base + r + 32 ≤ data.length := by
        apply Classical.byContradiction
        intro hc
        apply hin
        have : size data (base + r) d = data.length + 1 := by rw [size_eq, if_pos (by omega)]
        rw [this, if_pos (by omega)]
      have hS : size data (base + r) d = 32 + ceil32 (wordVal w) := by
        rw [size_eq, if_neg (by omega), if_neg (by rw [hde]; decide), if_pos (by rw [hde]; simp),
          hld, roundUp_eq _ hb]
      rw [hS] at hin ⊢
      have hfit : base + r + (32 + ceil32 (wordVal w)) ≤ data.length := by
        apply Classical.byContradiction
        intro hc
        apply hin
        rw [if_pos (by omega)]
      have hc := ceil32_ge (wordVal w)
      refine ⟨hld, ?_, ?_⟩
      · rw [take_view data base m (r + 32) (wordVal w) (by omega) (by omega)]
        congr 2
      · rw [if_neg (by omega)]
        have htl : ((data.drop (base + r)).take (32 + ceil32 (wordVal w))).length =
            32 + ceil32 (wordVal w) := by simp; omega
        unfold expectInput
        rw [htl]
        by_cases h : 32 + ceil32 (wordVal w) = 32
        · rw [if_pos h, if_pos h, h, load_eq_take hloc32]
        · rw [if_neg h, if_neg h, if_neg (by omega)]

/-! ## The `message` argument -/

/-- `SignTypedMessageLib`'s fallback reads argument `i` (`domain`,
    `message`, `types`) at `calldataload(4 + 32 i) + 4` (`+ 0x20` past the
    length word for `bytes`). Where Roles' root `Matches` (leading bytes 4)
    finds that argument as an offset slot, it is the same place. -/
theorem fallback_offset (data : Bytes) (i L : Nat) (h : tailLocation data 4 (32 * i) = L)
    (hL : L ≤ data.length) : L = load data (4 + 32 * i) + 4 := by
  unfold tailLocation at h
  split at h
  · omega
  · simp only at h
    split at h
    · omega
    · split at h
      · omega
      · omega

/-- **On the `message` argument**: below a `Matches` on nested calldata
    (`AbiEncoded`, leading bytes 0) at location `L`, whose children follow
    the primary type's tree, every node `evaluate` visits sits where the
    encoder reads the corresponding member of the message, which the
    library sees at `L + 32` (`fallback_offset` with `i = 1`; `m` is the
    length word there). -/
theorem message_agree (data : Bytes) (L m : Nat) {c : Condition} {tm : TN} {fuel : Nat} {v : V}
    (hop : c.operator = .Matches) (henc : c.encoding = .AbiEncoded) (hlb : c.leadingBytes = 0)
    (hL : 0 < L) (he : tm.encoding = .Tuple) (hlen : c.children.length = tm.children.length)
    (hm : ∀ k (h1 : k < c.children.length) (h2 : k < tm.children.length),
      MetaFit c.children[k] tm.children[k])
    (hf : ∀ k (h1 : k < c.children.length) (h2 : k < tm.children.length),
      FitT c.children[k] tm.children[k])
    (hread : readV (view data (L + 32) m) fuel tm 0 = some v)
    {p : List Nat} {d : Condition} {l : Nat} (hv : Visit data c L p d l) (hp : p ≠ []) :
    ∃ t' fuel' r' v', l = L + 32 + r' ∧ FitT d t' ∧
      readV (view data (L + 32) m) fuel' t' r' = some v' ∧ MetaFit d t' := by
  obtain ⟨f, rfl⟩ := readV_succ hread
  cases hv with
  | here => exact absurd rfl hp
  | logical _ hop' => rcases hop' with h | h <;> simp_all
  | matchesChild locs i hi _ hch hl hv' =>
    rw [if_pos ⟨hL, henc⟩, hlb, Nat.add_zero, show L + 32 = L + 32 + 0 by rfl] at hch
    obtain ⟨elocs, vs, rfl, rfl, hel, hvl, hk⟩ :=
      children_agree_tuple hread he (by rw [henc]; decide) hlen hm locs hch
    have hi' : i < elocs.length := by simpa using hi
    have hic : i < c.children.length := by simp at hl; omega
    have hit : i < tm.children.length := by omega
    have hg : c.children.getD i default = c.children[i] := by
      simp [List.getD_eq_getElem?_getD, hic]
    rw [hg] at hv'
    obtain ⟨t', f', r', v', h1, h2, h3, h4⟩ := visit_agree data (L + 32) m hv' (by simp)
      (hf i hic hit) (hk i hi' (by omega) hit)
    exact ⟨t', f', r', v', h1, h2, h3, h4 (hm i hic hit)⟩
  | arrayIter _ _ _ hop' => rcases hop' with h | h <;> simp_all
  | arrayTail _ _ _ hop' => simp_all
  | slice hop' => simp_all

end EIP712
