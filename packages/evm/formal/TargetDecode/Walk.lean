import TargetDecode.Canon
import TargetDecode.Decoder
import DecoderFaithfulness.Main
import DecoderFaithfulness.Bitmask

/-!
# Roles' walker on any layout the target accepts

Decoder faithfulness (`DecoderFaithfulness.visit_sound`) shows that on
calldata in spec encoding, every node Roles visits sits at the spec
encoding of the component it describes. Here the calldata is anything a
decoder that follows offsets accepts (`LP`, `LPCall`): tails in any
order, shared, with gaps, dirty padding. The statement is soundness only:
whenever Roles finds a slice (its `children` does not fail), it starts at
the location `LP` reads the component from. Roles may refuse layouts the target
accepts (a tail at or before its head slot); that only makes Roles
stricter.

This file: the shared step, `AbiLocation.children` on a block whose
components are loosely placed.
-/

namespace TargetDecode
open DecoderFaithfulness DecoderFaithfulness.Roles

/-! ## Bytes inside bytes -/

theorem At_take {c : Bytes} {x k : Nat} (h : x + k ≤ c.length) :
    At c x ((c.drop x).take k) := by
  refine ⟨?_, ?_⟩
  · rw [List.length_take, List.length_drop, Nat.min_eq_left (by omega)]
  · simp; omega

theorem At_trans {data c w : Bytes} {base x : Nat} (hw : At c x w) (hc : At data base c) :
    At data (base + x) w := by
  obtain ⟨h1, h2⟩ := hw
  obtain ⟨h3, h4⟩ := hc
  refine ⟨?_, by omega⟩
  conv => rhs; rw [← h1]
  conv => rhs; rw [← h3]
  rw [List.drop_take, List.take_take, List.drop_drop]
  congr 1
  omega

theorem load_in {c : Bytes} {x : Nat} (h : x + 32 ≤ c.length) :
    load c x = wordVal ((c.drop x).take 32) := by
  unfold load
  rw [List.take_append_of_le_length (by simp; omega)]

theorem load_shift {data c : Bytes} {base x : Nat} (hc : At data base c) (h : x + 32 ≤ c.length) :
    load c x = load data (base + x) := by
  have hw := At_trans (At_take h) hc
  have hb := hw.bound
  have hl : ((c.drop x).take 32).length = 32 := by simp; omega
  rw [hl] at hb
  rw [load_in h, load_in hb]
  congr 1
  have := hw.1
  rw [hl] at this
  exact this.symm

/-- **Loose placement survives embedding.** What a decoder reads inside
    `c` is read at the same relative position in any `data` that holds `c`. -/
theorem LP.shift {c : Bytes} {x : Nat} {v : Val} (h : LP c x v) :
    ∀ {data : Bytes} {base : Nat}, At data base c → LP data (base + x) v := by
  induction h with
  | word hat => intro data base hc; exact .word (At_trans hat hc)
  | @bytes c x b hb hload hat =>
    intro data base hc
    have := hc.bound
    refine .bytes (by omega) (by rw [← load_shift hc hb]; exact hload) ?_
    have := At_trans hat hc
    rwa [← Nat.add_assoc] at this
  | @tuple c x vs _ hb _ ihs ihd =>
    intro data base hc
    have := hc.bound
    refine .tuple (fun i h hst => ?_) (fun i h hst => ?_) (fun i h hst => ?_)
    · have := ihs i h hst hc; rwa [← Nat.add_assoc] at this
    · have := hb i h hst; omega
    · have h1 := ihd i h hst hc
      rw [load_shift hc (hb i h hst), show base + (x + headOff vs i) = base + x + headOff vs i by omega,
        ← Nat.add_assoc] at h1
      exact h1
  | @array c x vs hl hcount _ hb _ ihs ihd =>
    intro data base hc
    have := hc.bound
    refine .array (by omega) ?_ (fun i h hst => ?_) (fun i h hst => ?_) (fun i h hst => ?_)
    · rw [← load_shift hc hl]; exact hcount
    · have := ihs i h hst hc
      rwa [show base + (x + 32 + headOff vs i) = base + x + 32 + headOff vs i by omega] at this
    · have := hb i h hst; omega
    · have h1 := ihd i h hst hc
      rw [load_shift hc (hb i h hst),
        show base + (x + 32 + headOff vs i) = base + x + 32 + headOff vs i by omega,
        show base + (x + 32 + load data (base + x + 32 + headOff vs i)) =
          base + x + 32 + load data (base + x + 32 + headOff vs i) by omega] at h1
      exact h1
  | @call c x pre args cc hl hload hat hpl htake hs hb hd _ _ =>
    intro data base hc
    have := hc.bound
    refine .call (by omega) ?_ ?_ hpl htake hs hb hd
    · rw [← load_shift hc hl]; exact hload
    · have := At_trans hat hc; rwa [← Nat.add_assoc] at this

/-! ## Blocks -/

/-- The components of a block that starts at `base` (a tuple, the elements
    of an array after the count word, call arguments after the leading
    bytes), as a decoder reads them. -/
def LBlock (data : Bytes) (base : Nat) (vs : List Val) : Prop :=
  (∀ i (h : i < vs.length), vs[i].isStatic = true → LP data (base + headOff vs i) vs[i]) ∧
  (∀ i (h : i < vs.length), vs[i].isStatic = false →
    LP data (base + load data (base + headOff vs i)) vs[i])

theorem LP.tuple_block {data : Bytes} {l : Nat} {vs : List Val} (h : LP data l (.tuple vs)) :
    LBlock data l vs := by
  cases h with
  | tuple hs _ hd => exact ⟨hs, hd⟩

theorem LP.array_block {data : Bytes} {l : Nat} {vs : List Val} (h : LP data l (.array vs)) :
    load data l = vs.length ∧ LBlock data (l + 32) vs := by
  cases h with
  | array _ hc hs _ hd => exact ⟨hc, hs, hd⟩

theorem LPCall.block {data pre : Bytes} {args : List Val} (h : LPCall data pre args) :
    LBlock data pre.length args :=
  ⟨h.2.2.1, fun i hi hs => (h.2.2.2 i hi hs).2⟩

/-- Nested calldata at `l`: its arguments, read inside the `bytes` content,
    are read at the same places in `data`, after the length word and the
    leading bytes. -/
theorem LP.call_block {data pre : Bytes} {l : Nat} {args : List Val}
    (h : LP data l (.call pre args)) : LBlock data (l + 32 + pre.length) args := by
  cases h with
  | call _ _ hat _ _ hs hb hd =>
    refine ⟨fun i hi hst => ?_, fun i hi hst => ?_⟩
    · have := (hs i hi hst).shift hat
      rwa [← Nat.add_assoc] at this
    · have h1 := (hd i hi hst).shift hat
      rw [load_shift hat (hb i hi hst),
        show l + 32 + (pre.length + headOff args i) = l + 32 + pre.length + headOff args i by omega,
        show l + 32 + (pre.length + load data (l + 32 + pre.length + headOff args i)) =
          l + 32 + pre.length + load data (l + 32 + pre.length + headOff args i) by omega] at h1
      exact h1

/-- What `decodeCall` returns is the calldata of a call. -/
theorem BlockOK.call {data : Bytes} {ts : List STy} {n : Nat} {args : List Val}
    (hn : n ≤ data.length) (h : BlockOK data ts n 0 args) :
    LPCall data (data.take n) args := by
  have hl : (data.take n).length = n := by simp; omega
  have hts := h.1
  refine ⟨by omega, by rw [hl], fun i hi hs => ?_, fun i hi hs => ?_⟩
  · have := (h.2 i hi (by omega)).2.1 hs
    rw [hl]; simpa using this
  · have := (h.2 i hi (by omega)).2.2 hs
    rw [hl]; simpa using this

/-- What solc's parameter decoder accepts is the calldata of a call. -/
theorem decodeCall_LPCall {data : Bytes} {n : Nat} {ts : List STy} {args : List Val}
    (h : decodeCall data n ts = some args) : LPCall data (data.take n) args := by
  have hn : n ≤ data.length := by
    unfold decodeCall at h; split at h
    · simp at h
    · omega
  exact (decodeCall_LP h).call hn

/-! ## `_child` and the `children` loop -/

theorem headOff_take : ∀ (vs : List Val) (n k : Nat), k ≤ n → headOff (vs.take n) k = headOff vs k
  | [], _, _, _ => by simp [headOff]
  | _ :: _, 0, 0, _ => by simp [headOff]
  | _ :: _, _ + 1, 0, _ => by simp [headOff]
  | v :: vs, n + 1, k + 1, h => by
    simp only [List.take_succ_cons, headOff]
    rw [headOff_take vs n k (by omega)]
  | _ :: _, 0, _ + 1, h => by omega

/-- **The children loop is sound on any layout.** If the components are
    loosely placed in their slots, every slice the loop returns starts where
    a decoder reads the component. -/
theorem childrenLoop_LP {data : Bytes} {s : Bool} (body : Slice) (sizeAt : Nat → Nat) :
    ∀ (vs : List Val) (i h : Nat) (spans : List Slice),
    (∀ k (hk : k < vs.length), ∃ c, sizeAt (i + k) = (annotate c).inlineSize ∧ DescS s c vs[k]) →
    (∀ k (hk : k < vs.length), vs[k].isStatic = true →
      LP data (body.offset + h + headOff vs k) vs[k]) →
    (∀ k (hk : k < vs.length), vs[k].isStatic = false →
      LP data (body.offset + load data (body.offset + h + headOff vs k)) vs[k]) →
    childrenLoop data body sizeAt vs.length i h = some spans →
    spans.length = vs.length ∧ ∀ k (hk : k < spans.length) (hk' : k < vs.length),
      LP data spans[k].offset vs[k] ∧ (vs[k].isStatic = false → 0 < spans[k].offset)
  | [], _, _, spans, _, _, _, hl => by
    simp [childrenLoop] at hl; subst hl; simp
  | v :: vs, i, h, spans, hch, hst, hdy, hl => by
    obtain ⟨c, hc, hD⟩ := hch 0 (by simp)
    simp only [Nat.add_zero, List.getElem_cons_zero] at hc hD
    have hmeta := hD.annotate_meta
    have hge := hD.enc_ge
    have hrest : ∀ k (hk : k < vs.length), ∃ c, sizeAt (i + 1 + k) = (annotate c).inlineSize ∧
        DescS s c vs[k] := by
      intro k hk
      obtain ⟨c', h1, h2⟩ := hch (k + 1) (by simp; omega)
      exact ⟨c', by rw [← h1]; congr 1; omega, by simpa using h2⟩
    simp only [List.length_cons, childrenLoop] at hl
    rw [hc, hmeta] at hl
    cases hc0 : child data body h (if v.isStatic = true then (enc v).length else 0) with
    | none => rw [hc0] at hl; cases hl
    | some q =>
      obtain ⟨sp, next⟩ := q
      rw [hc0] at hl
      simp only at hl
      obtain ⟨spans', hl', rfl⟩ := Option.map_eq_some_iff.mp hl
      obtain ⟨rfl, -, hsp⟩ := child_some hc0
      by_cases hs : v.isStatic
      · simp only [hs, ite_true] at hsp hl'
        have hslot : slotSize (enc v).length = (enc v).length := by
          unfold slotSize; rw [ite_eq_left (by omega)]
        rw [hslot] at hl'
        rcases hsp with ⟨-, rfl⟩ | ⟨h0, -⟩
        · obtain ⟨hlen', hpl⟩ := childrenLoop_LP body sizeAt vs (i + 1) (h + (enc v).length) spans'
            hrest
            (fun k hk hk2 => by
              have := hst (k + 1) (by simp; omega) (by simpa using hk2)
              simp only [headOff, List.getElem_cons_succ, hs, ite_true] at this
              rwa [show body.offset + (h + (enc v).length) + headOff vs k =
                body.offset + h + ((enc v).length + headOff vs k) by omega])
            (fun k hk hk2 => by
              have := hdy (k + 1) (by simp; omega) (by simpa using hk2)
              simp only [headOff, List.getElem_cons_succ, hs, ite_true] at this
              rwa [show body.offset + (h + (enc v).length) + headOff vs k =
                body.offset + h + ((enc v).length + headOff vs k) by omega])
            hl'
          refine ⟨by simp [hlen'], fun k hk hk' => ?_⟩
          cases k with
          | zero =>
            have := hst 0 (by simp) (by simpa using hs)
            simp only [headOff, Nat.add_zero, List.getElem_cons_zero] at this
            simp [this, hs]
          | succ k => simpa using hpl k (by simp at hk; omega) (by simp at hk'; omega)
        · omega
      · simp only [hs, ite_false, Bool.false_eq_true] at hsp hl'
        have hslot : slotSize 0 = 32 := rfl
        rw [hslot] at hl'
        rcases hsp with ⟨h0, -⟩ | ⟨-, hlt, -, rfl⟩
        · omega
        · obtain ⟨hlen', hpl⟩ := childrenLoop_LP body sizeAt vs (i + 1) (h + 32) spans'
            hrest
            (fun k hk hk2 => by
              have := hst (k + 1) (by simp; omega) (by simpa using hk2)
              simp only [headOff, List.getElem_cons_succ, hs, ite_false, Bool.false_eq_true] at this
              rwa [show body.offset + (h + 32) + headOff vs k =
                body.offset + h + (32 + headOff vs k) by omega])
            (fun k hk hk2 => by
              have := hdy (k + 1) (by simp; omega) (by simpa using hk2)
              simp only [headOff, List.getElem_cons_succ, hs, ite_false, Bool.false_eq_true] at this
              rwa [show body.offset + (h + 32) + headOff vs k =
                body.offset + h + (32 + headOff vs k) by omega])
            hl'
          refine ⟨by simp [hlen'], fun k hk hk' => ?_⟩
          cases k with
          | zero =>
            have := hdy 0 (by simp) (by simpa using hs)
            simp only [headOff, Nat.add_zero, List.getElem_cons_zero] at this
            simp only [List.getElem_cons_zero]
            exact ⟨this, fun _ => by omega⟩
          | succ k => simpa using hpl k (by simp at hk; omega) (by simp at hk'; omega)

/-- `children` of a tuple (or calldata) node whose children describe the
    first fields of `vs`. -/
theorem children_tuple_LP {data : Bytes} {s : Bool} {c : Condition} {vs : List Val}
    {body : Slice} {spans : List Slice}
    (hne : (annotate c).encoding ≠ .Array) (hk : c.children.length ≤ vs.length)
    (hall : DescAll s c.children (vs.take c.children.length)) (hb : LBlock data body.offset vs)
    (hch : children data body (annotate c) = some spans) :
    spans.length = c.children.length ∧ ∀ k (hk : k < spans.length) (hk' : k < vs.length),
      LP data spans[k].offset vs[k] ∧ (vs[k].isStatic = false → 0 < spans[k].offset) := by
  unfold children at hch
  rw [ite_eq_right hne, annotate_children] at hch
  have hl : (c.children.map annotate).length = (vs.take c.children.length).length := by
    rw [List.length_map]; exact DescAll.length_eq hall
  rw [hl] at hch
  have htl : (vs.take c.children.length).length = c.children.length := by simp; omega
  obtain ⟨hlen', hpl⟩ := childrenLoop_LP (s := s) body
    (fun i => ((c.children.map annotate).getD i default).inlineSize)
    (vs.take c.children.length) 0 0 spans
    (by
      intro k hk
      have hkc : k < c.children.length := by rw [DescAll.length_eq hall]; exact hk
      exact ⟨c.children[k], by simp [hkc], DescAll.get hall k hkc⟩)
    (fun k hk hs => by
      rw [List.getElem_take] at hs ⊢
      rw [headOff_take vs _ k (by omega)]
      simpa using hb.1 k (by omega) hs)
    (fun k hk hs => by
      rw [List.getElem_take] at hs ⊢
      rw [headOff_take vs _ k (by omega)]
      simpa using hb.2 k (by omega) hs)
    hch
  refine ⟨by rw [hlen', htl], fun k hk hk' => ?_⟩
  have := hpl k hk (by omega)
  rw [List.getElem_take] at this
  exact this

/-- `elements` of an array whose elements one node describes. -/
theorem elements_LP {data : Bytes} {s : Bool} {c0 : Condition} {vs : List Val} {sl : Slice}
    {spans : List Slice} (h0 : ∀ v, v ∈ vs → DescS s c0 v)
    (hcount : load data sl.offset = vs.length) (hb : LBlock data (sl.offset + 32) vs)
    (hch : elements data sl (annotate c0).inlineSize = some spans) :
    spans.length = vs.length ∧ ∀ k (hk : k < spans.length) (hk' : k < vs.length),
      LP data spans[k].offset vs[k] ∧ (vs[k].isStatic = false → 0 < spans[k].offset) := by
  obtain ⟨-, hch⟩ := elements_some hch
  rw [hcount] at hch
  exact childrenLoop_LP (s := s) ⟨sl.offset + 32, sl.length - 32⟩ _ vs 0 0 spans
    (fun k hk => ⟨c0, rfl, h0 _ (List.getElem_mem hk)⟩)
    (fun k hk hs => by simpa using hb.1 k hk hs)
    (fun k hk hs => by simpa using hb.2 k hk hs) hch

/-- `children` of an array node whose template describes every element. -/
theorem children_array_LP {data : Bytes} {s : Bool} {c c0 : Condition} {cs : List Condition}
    {vs : List Val} {sl : Slice} {spans : List Slice}
    (he : (annotate c).encoding = .Array) (hcs : c.children = c0 :: cs)
    (h0 : ∀ v, v ∈ vs → DescS s c0 v) (hcount : load data sl.offset = vs.length)
    (hb : LBlock data (sl.offset + 32) vs)
    (hch : children data sl (annotate c) = some spans) :
    spans.length = vs.length ∧ ∀ k (hk : k < spans.length) (hk' : k < vs.length),
      LP data spans[k].offset vs[k] ∧ (vs[k].isStatic = false → 0 < spans[k].offset) := by
  unfold children at hch
  rw [ite_eq_left he, annotate_children, hcs] at hch
  exact elements_LP h0 hcount hb hch

/-! ## What a visited node is, on any layout -/

/-- Where Roles expects component `u` at `l`, read the way the target's
    decoder reads it. Nested calldata at `0` is the top-level calldata
    (no length word). -/
def LPl (data : Bytes) (l : Nat) : Val → Prop
  | .call pre args => (l = 0 ∧ LPCall data pre args) ∨ (0 < l ∧ LP data l (.call pre args))
  | u => LP data l u

/-- `cb` is the byte string a `Slice` indexes into for component `u` at
    `l`: the word, or the content of a `bytes` value as the target decodes
    it (for nested calldata: the raw `bytes` the target receives). -/
def ContentAt (data : Bytes) (l : Nat) : Val → Bytes → Prop
  | .word w, cb => cb = w
  | .bytes b, cb => cb = b
  | .call _ _, cb => l + 32 ≤ data.length ∧ load data l = cb.length ∧ At data (l + 32) cb
  | _, _ => False

theorem LP.bytesLike_content {data : Bytes} {l : Nat} {u : Val} (h : LP data l u)
    (hu : IsBytesLike u) :
    ∃ cb, l + 32 ≤ data.length ∧ load data l = cb.length ∧ At data (l + 32) cb ∧
      ContentAt data l u cb := by
  cases u with
  | bytes b => cases h with | bytes hb hl hat => exact ⟨b, hb, hl, hat, rfl⟩
  | call pre args => cases h with | call hb hl hat _ _ _ _ _ => exact ⟨_, hb, hl, hat, hb, hl, hat⟩
  | _ => simp [IsBytesLike] at hu

theorem LPl.of_LP {data : Bytes} {l : Nat} {u : Val} (h : LP data l u)
    (hcall : ∀ pre args, u = .call pre args → 0 < l) : LPl data l u := by
  cases u with
  | call pre args => exact Or.inr ⟨hcall pre args rfl, h⟩
  | _ => exact h

theorem LPl.to_LP {data : Bytes} {l : Nat} {u : Val} (h : LPl data l u)
    (hl : ∀ pre args, u = .call pre args → 0 < l) : LP data l u := by
  cases u with
  | call pre args =>
    rcases h with ⟨h0, _⟩ | ⟨_, h⟩
    · have := hl pre args rfl; omega
    · exact h
  | _ => exact h

theorem LPl.to_LP_of_root {data : Bytes} {l : Nat} {u : Val} {c : Condition}
    (hp : LPl data l u) (hr : l = 0 → IsCall u → RootOK c)
    (hne1 : c.encoding ≠ .AbiEncoded) (hne2 : c.encoding ≠ .None) : LP data l u := by
  apply LPl.to_LP hp
  intro pre args he
  rcases Nat.eq_zero_or_pos l with h0 | h0
  · exfalso
    cases hr h0 ⟨pre, args, he⟩ with
    | abi h => exact hne1 h
    | logical h _ _ => exact hne2 h
  · exact h0

theorem child_placedL {data : Bytes} {l : Slice} {v : Val} {c : Condition}
    (h : LP data l.offset v ∧ (v.isStatic = false → 0 < l.offset)) :
    LPl data l.offset v ∧ (l.offset = 0 → IsCall v → RootOK c) := by
  refine ⟨LPl.of_LP h.1 (fun pre args he => h.2 (by subst he; rfl)), ?_⟩
  rintro hl ⟨pre, args, rfl⟩
  have := h.2 rfl; omega

/-- Reached inside a bytes-like interpretation `ch` that does not describe
    the bytes value `us` it is evaluated on (a variant branch that does not
    fit). `ch` is a node of `top`; the walk from `top` (at `loc`) reaches it
    where the target reads `us` (`ls`, same index path), and `d` from there.
    Only with `s = true`. -/
def InStrayL (s : Bool) (data : Bytes) (top : Condition) (loc : Slice) (u : Val) (p : List Nat)
    (d : Condition) (l : Slice) (y : Nat) : Prop :=
  s = true ∧ ∃ p1 p2 ch us ls, p = p1 ++ p2 ∧ u.sub p1 = some us ∧ Sub ch top ∧ BytesLike ch ∧
    IsBytesLike us ∧ ¬ Desc s ch us ∧ LPl data ls.offset us ∧
    Below data (annotate top) loc (annotate top).inlineSize p1 (annotate ch) ls
      (annotate ch).inlineSize ∧
    Below data (annotate ch) ls (annotate ch).inlineSize p2 d l y

/-- The four outcomes of `DecoderFaithfulness.Reached`, with "sits at the
    spec encoding" replaced by "starts where the target's decoder reads
    it". -/
def ReachedL (s : Bool) (data : Bytes) (top : Condition) (loc : Slice) (u : Val) (p : List Nat)
    (d : Condition) (l : Slice) (y : Nat) : Prop :=
  -- a node of `top` that describes component `u'`, where the target reads it from
  (∃ d0 u', Sub d0 top ∧ d = annotate d0 ∧ y = d.inlineSize ∧ u.sub p = some u' ∧ Desc s d0 u' ∧
      LPl data l.offset u' ∧ (l.offset = 0 → IsCall u' → RootOK d0)) ∨
  -- non-structural (a Zip reads no calldata at its own slice)
  (∃ d0, d = annotate d0 ∧ (NonStruct d0 ∨ ZipNode d0)) ∨
  -- below a `Slice`: a window of the bytes the target decodes for component `u'`
  (∃ d0 bs u' lu cb, d = annotate d0 ∧ Win d0 ∧ Fits data l bs ∧ y = bs.length ∧
      1 ≤ bs.length ∧ bs.length ≤ 32 ∧ u.sub p = some u' ∧ LPl data lu u' ∧
      ContentAt data lu u' cb ∧ IsWindow bs cb) ∨
  -- inside an interpretation that does not fit (only with `s = true`)
  InStrayL s data top loc u p d l y

theorem ReachedL.lift {s : Bool} {data : Bytes} {u v : Val} {P : List Nat}
    (hsub : ∀ q, u.sub (P ++ q) = v.sub q) {top top' : Condition} (htop : Sub top top')
    {loc' lc : Slice}
    (hent : Below data (annotate top') loc' (annotate top').inlineSize P (annotate top) lc
      (annotate top).inlineSize)
    {p : List Nat} {d : Condition} {l : Slice} {y : Nat}
    (h : ReachedL s data top lc v p d l y) : ReachedL s data top' loc' u (P ++ p) d l y := by
  rcases h with ⟨d0, u', hst0, hd, hy, hs, hD, hp, hr⟩ | hns |
    ⟨d0, bs, u', lu, cb, hd, hw, hat, hy, h1, h32, hs, hpl, hct, hiw⟩ |
    ⟨hst, p1, p2, ch, us, ls, rfl, hs, hsc, hb, hu, hnd, hp, hb1, hv⟩
  · exact Or.inl ⟨d0, u', hst0.trans htop, hd, hy, by rw [hsub]; exact hs, hD, hp, hr⟩
  · exact Or.inr (Or.inl hns)
  · exact Or.inr (Or.inr (Or.inl ⟨d0, bs, u', lu, cb, hd, hw, hat, hy, h1, h32,
      by rw [hsub]; exact hs, hpl, hct, hiw⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨hst, P ++ p1, p2, ch, us, ls, by rw [List.append_assoc],
      by rw [hsub]; exact hs, hsc.trans htop, hb, hu, hnd, hp, hent.trans hb1, hv⟩))

theorem ReachedL.stepP {s : Bool} {data : Bytes} {u v : Val} {P : List Nat}
    (hsub : ∀ q, u.sub (P ++ q) = v.sub q) {ch top : Condition} (htop : Sub ch top)
    {ltop lc : Slice}
    (hent : Below data (annotate top) ltop (annotate top).inlineSize P (annotate ch) lc
      (annotate ch).inlineSize)
    {p : List Nat} {d : Condition} {l : Slice} {y : Nat} (hDS : DescS s ch v)
    (hp : LPl data lc.offset v)
    (hvis : Visit data (annotate ch) lc (annotate ch).inlineSize p d l y)
    (ih : Desc s ch v → ReachedL s data ch lc v p d l y) :
    ReachedL s data top ltop u (P ++ p) d l y := by
  by_cases hd : Desc s ch v
  · exact ReachedL.lift hsub htop hent (ih hd)
  · cases hDS with
    | desc hd' => exact absurd hd' hd
    | stray hst hb hu =>
      exact Or.inr (Or.inr (Or.inr ⟨hst, P, p, ch, v, lc, rfl,
        by rw [← List.append_nil P, hsub, Val.sub_nil], htop, hb, hu, hd, hp, hent, .visit hvis⟩))

theorem ReachedL.step {s : Bool} {data : Bytes} {u v : Val} {i : Nat}
    (hsub : ∀ q, u.sub (i :: q) = v.sub q) {ch top : Condition} (hmem : ch ∈ top.children)
    {ltop lc : Slice}
    (hent : Visit data (annotate top) ltop (annotate top).inlineSize [i] (annotate ch) lc
      (annotate ch).inlineSize) {p : List Nat}
    {d : Condition} {l : Slice} {y : Nat} (hDS : DescS s ch v) (hp : LPl data lc.offset v)
    (hvis : Visit data (annotate ch) lc (annotate ch).inlineSize p d l y)
    (ih : Desc s ch v → ReachedL s data ch lc v p d l y) :
    ReachedL s data top ltop u (i :: p) d l y :=
  ReachedL.stepP (P := [i]) hsub (Sub.mem hmem) (.visit hent) hDS hp hvis ih

/-- Nested calldata: the argument block, in the block `Matches` finds. -/
theorem call_args_block {data : Bytes} {c : Condition} {pre : Bytes} {args : List Val}
    {loc body : Slice} (he : c.encoding = .AbiEncoded) (hL : c.leadingBytes = pre.length)
    (hp : LPl data loc.offset (.call pre args))
    (hbody : matchesBody data loc (annotate c) = some body) :
    LBlock data body.offset args := by
  have henc : (annotate c).encoding = .AbiEncoded := by rw [annotate_encoding, he]; simp
  have hlb : (annotate c).leadingBytes = pre.length := by
    rw [annotate_leadingBytes, he, hL]; simp
  rcases matchesBody_some hbody with ⟨hne, -⟩ | ⟨-, payload, hpay, -, rfl⟩
  · exact absurd henc hne
  · simp only [hlb]
    rcases hpay with ⟨h0, rfl⟩ | ⟨hne0, hpay⟩
    · rcases hp with ⟨-, hc⟩ | ⟨hpos, -⟩
      · rw [h0]; simpa using hc.block
      · omega
    · rcases hp with ⟨h0, -⟩ | ⟨-, hc⟩
      · exact absurd h0 hne0
      · rcases slicePayload_some hpay with ⟨h0, -⟩ | ⟨-, -, -, rfl⟩
        · omega
        · exact hc.call_block

/-- **Soundness of Roles' navigation on any layout the target accepts.** -/
theorem visit_soundL {data : Bytes} {s : Bool} :
    ∀ {c' loc z p d l y}, Visit data c' loc z p d l y →
    ∀ {c u}, c' = annotate c → z = c'.inlineSize → Desc s c u → LPl data loc.offset u →
      (loc.offset = 0 → IsCall u → RootOK c) → ReachedL s data c loc u p d l y := by
  intro c' loc z p d l y hv
  induction hv with
  | here =>
    intro c u hc hz hD hp hr
    exact Or.inl ⟨c, u, .refl c, hc, hz, Val.sub_nil u, hD, hp, hr⟩
  | @logical _ loc _ p _ _ _ ch hop hmem hvis ih =>
    intro c u hc hz hD hp hr
    subst hc; subst hz
    have hent0 : Visit data (annotate c) loc (annotate c).inlineSize [] ch loc ch.inlineSize :=
      .logical ch hop hmem .here
    match hD with
    | .logical _ he _ _ _ hall _ =>
      rw [annotate_children] at hmem
      obtain ⟨ch0, hm0, rfl⟩ := List.mem_map.mp hmem
      cases hall ch0 hm0 with
      | ds hDS =>
        have hrch : loc.offset = 0 → IsCall u → RootOK ch0 := by
          intro h0 hcall
          cases hr h0 hcall with
          | abi h => rw [he] at h; cases h
          | logical _ _ hk =>
            cases hk ch0 hm0 with
            | ok h => exact h
            | ns hns => exact (hns.not_descS hDS).elim
            | zip hz => exact (hz.not_descS hDS).elim
        by_cases hd : Desc s ch0 u
        · exact ReachedL.lift (P := []) (fun _ => rfl) (Sub.mem hm0) (.visit hent0)
            (ih rfl rfl hd hp hrch)
        · cases hDS with
          | desc hd' => exact absurd hd' hd
          | stray hst hb hu =>
            exact Or.inr (Or.inr (Or.inr ⟨hst, [], p, ch0, u, loc, rfl, Val.sub_nil u,
              Sub.mem hm0, hb, hu, hd, hp, .visit hent0, .visit hvis⟩))
      | ns hns =>
        obtain ⟨rfl, d0, hd, hns'⟩ := NonStruct.visit hvis rfl hns
        exact Or.inr (Or.inl ⟨d0, hd, .inl hns'⟩)
      | zip hz _ =>
        obtain ⟨rfl, rfl⟩ := ZipNode.visit hz hvis rfl
        exact Or.inr (Or.inl ⟨ch0, rfl, .inr hz⟩)
    | .word _ _ hnav _ | .bytes _ _ hnav _ =>
      rcases hop with h | h <;> (rw [annotate_op_of h (by decide)] at hnav; simp [isNavOp] at hnav)
    | .sliceWord _ hop' _ _ _ _ _ | .sliceBytes _ hop' _ _ _ _ _ =>
      rcases hop with h | h <;> (rw [annotate_op_of h (by decide)] at hop'; cases hop')
    | .tuple _ _ _ _ _ hnav | .array _ _ _ _ _ _ _ hnav =>
      rcases hop with h | h <;> (rw [annotate_op_of h (by decide)] at hnav; simp [isNavOp] at hnav)
    | .call _ _ _ _ _ hop' =>
      rcases hop with h | h <;> (rw [annotate_op_of h (by decide)] at hop'; simp at hop')
  | @matchesChild _ loc _ _ _ _ _ body spans i hi hop hbody hch hcount hvis ih =>
    intro c u hc hz hD hp _
    subst hc; subst hz
    have hent0 := Visit.matchesChild (z := (annotate c).inlineSize) (p := []) body spans i hi hop
      hbody hch hcount .here
    have hop0 := annotate_op_of hop (by decide)
    match hD with
    | .tuple (vs := vs) he hne hk hall _ _ =>
      rw [matchesBody_plain (.inl he)] at hbody; cases hbody
      obtain ⟨hlen', hpl⟩ := children_tuple_LP (by rw [annotate_encoding, he]; simp) hk hall
        (show LP data loc.offset (.tuple vs) from hp).tuple_block hch
      have hiv : i < vs.length := by omega
      have hic : i < c.children.length := by omega
      have hall' : DescS s c.children[i] vs[i] := by
        have := DescAll.get hall i hic
        simpa [List.getElem_take] using this
      have hgetD : (annotate c).children.getD i default = annotate c.children[i] := by
        rw [annotate_children]; simp [hic]
      rw [hgetD] at ih hvis hent0
      have hpc := child_placedL (c := c.children[i]) (hpl i hi hiv)
      exact ReachedL.step (fun q => Val.sub_tuple vs i hiv q) (List.getElem_mem hic) hent0
        hall' hpc.1 hvis (fun hd => ih rfl rfl hd hpc.1 hpc.2)
    | .array (vs := vs) c0 cs he hcs h0 hpos _ _ =>
      rw [matchesBody_plain (.inr he)] at hbody; cases hbody
      obtain ⟨hcnt, hb⟩ := (show LP data loc.offset (.array vs) from hp).array_block
      obtain ⟨hlen', hpl⟩ :=
        children_array_LP (by rw [annotate_encoding, he]; simp) hcs h0 hcnt hb hch
      have hiv : i < vs.length := by omega
      have hic : i < c.children.length := by
        rw [annotate_children] at hcount; simp at hcount; omega
      have hgetD : (annotate c).children.getD i default = annotate c.children[i] := by
        rw [annotate_children]; simp [hic]
      rw [hgetD] at ih hvis hent0
      have hpc := child_placedL (c := c.children[i]) (hpl i hi hiv)
      exact ReachedL.step (fun q => Val.sub_array vs i hiv q) (List.getElem_mem hic) hent0
        (hpos i hic hiv) hpc.1 hvis (fun hd => ih rfl rfl hd hpc.1 hpc.2)
    | .call (pre := pre) (args := vs) he hL hne hk hall _ =>
      obtain ⟨hlen', hpl⟩ := children_tuple_LP (by rw [annotate_encoding, he]; simp) hk hall
        (call_args_block he hL hp hbody) hch
      have hiv : i < vs.length := by omega
      have hic : i < c.children.length := by omega
      have hall' : DescS s c.children[i] vs[i] := by
        have := DescAll.get hall i hic
        simpa [List.getElem_take] using this
      have hgetD : (annotate c).children.getD i default = annotate c.children[i] := by
        rw [annotate_children]; simp [hic]
      rw [hgetD] at ih hvis hent0
      have hpc := child_placedL (c := c.children[i]) (hpl i hi hiv)
      exact ReachedL.step (fun q => Val.sub_call pre vs i hiv q) (List.getElem_mem hic) hent0
        hall' hpc.1 hvis (fun hd => ih rfl rfl hd hpc.1 hpc.2)
    | .word _ _ hnav _ | .bytes _ _ hnav _ => rw [hop0] at hnav; simp [isNavOp] at hnav
    | .sliceWord _ hop' _ _ _ _ _ | .sliceBytes _ hop' _ _ _ _ _ => rw [hop0] at hop'; cases hop'
    | .logical _ _ hop' _ _ _ _ => rw [hop0] at hop'; simp at hop'
  | @arrayIter _ loc _ _ _ _ _ spans i hi hop hch hvis ih =>
    intro c u hc hz hD hp _
    subst hc; subst hz
    have hent0 := Visit.arrayIter (z := (annotate c).inlineSize) (p := []) spans i hi hop hch .here
    match hD with
    | .array (vs := vs) c0 cs he hcs h0 _ _ _ =>
      obtain ⟨hcnt, hb⟩ := (show LP data loc.offset (.array vs) from hp).array_block
      obtain ⟨hlen', hpl⟩ :=
        children_array_LP (by rw [annotate_encoding, he]; simp) hcs h0 hcnt hb hch
      have hiv : i < vs.length := by omega
      have hhead : (annotate c).children.headD default = annotate c0 := by
        rw [annotate_children, hcs]; rfl
      rw [hhead] at ih hvis hent0
      have hpc := child_placedL (c := c0) (hpl i hi hiv)
      exact ReachedL.step (fun q => Val.sub_array vs i hiv q) (by rw [hcs]; simp) hent0
        (h0 _ (List.getElem_mem hiv)) hpc.1 hvis (fun hd => ih rfl rfl hd hpc.1 hpc.2)
    | .word _ _ hnav _ | .bytes _ _ hnav _ | .tuple _ _ _ _ _ hnav =>
      rcases hop with h | h <;> (rw [annotate_op_of h (by decide)] at hnav; simp [isNavOp] at hnav)
    | .sliceWord _ hop' _ _ _ _ _ | .sliceBytes _ hop' _ _ _ _ _ =>
      rcases hop with h | h <;> (rw [annotate_op_of h (by decide)] at hop'; cases hop')
    | .call _ _ _ _ _ hop' =>
      rcases hop with h | h <;> (rw [annotate_op_of h (by decide)] at hop'; simp at hop')
    | .logical _ _ hop' _ _ _ _ =>
      rcases hop with h | h <;> (rw [annotate_op_of h (by decide)] at hop'; simp at hop')
  | @arrayTail _ loc _ _ _ _ _ spans j hj hop hch hle hjc hvis ih =>
    intro c u hc hz hD hp _
    subst hc; subst hz
    have hent0 := Visit.arrayTail (z := (annotate c).inlineSize) (p := []) spans j hj hop hch hle
      hjc .here
    have hop0 := annotate_op_of hop (by decide)
    match hD with
    | .array (vs := vs) c0 cs he hcs h0 _ htail _ =>
      obtain ⟨hcnt, hb⟩ := (show LP data loc.offset (.array vs) from hp).array_block
      obtain ⟨hlen', hpl⟩ :=
        children_array_LP (by rw [annotate_encoding, he]; simp) hcs h0 hcnt hb hch
      have hcl : (annotate c).children.length = c.children.length := by
        rw [annotate_children]; simp
      have hjv : spans.length - (annotate c).children.length + j < vs.length := by omega
      have hjc' : j < c.children.length := by omega
      have hk : c.children.length ≤ vs.length := by omega
      have hgetD : (annotate c).children.getD j default = annotate c.children[j] := by
        rw [annotate_children]; simp [hjc']
      rw [hgetD] at ih hvis hent0
      have hidx : vs.length - c.children.length + j =
          spans.length - (annotate c).children.length + j := by
        omega
      have hpc := child_placedL (c := c.children[j]) (hpl _ hj hjv)
      have hDS := htail j hjc' hk
      have hDS' : DescS s c.children[j] vs[spans.length - (annotate c).children.length + j] := by
        simpa only [hidx] using hDS
      exact ReachedL.step (fun q => Val.sub_array vs _ hjv q) (List.getElem_mem hjc') hent0 hDS'
        hpc.1 hvis (fun hd => ih rfl rfl hd hpc.1 hpc.2)
    | .word _ _ hnav _ | .bytes _ _ hnav _ => rw [hop0] at hnav; simp [isNavOp] at hnav
    | .sliceWord _ hop' _ _ _ _ _ | .sliceBytes _ hop' _ _ _ _ _ => rw [hop0] at hop'; cases hop'
    | .tuple _ _ _ _ _ hnav => rcases hnav with ⟨h, -⟩ | h <;> (rw [hop0] at h; simp [isNavOp] at h)
    | .call _ _ _ _ _ hop' => rw [hop0] at hop'; simp at hop'
    | .logical _ _ hop' _ _ _ _ => rw [hop0] at hop'; simp at hop'
  | @slice _ loc _ p _ _ _ payload hop hpay hbound hvis _ =>
    intro c u hc hz hD hp hr
    subst hc; subst hz
    have hop0 := annotate_op_of hop (by decide)
    match hD with
    | .sliceWord (w := w) he _ hch hs1 hs32 hw hw32 =>
      have hmeta := (Desc.sliceWord he hop0 hch hs1 hs32 hw hw32 (s := s)).annotate_meta
      have hat : At data loc.offset w := by
        have h' : LP data loc.offset (.word w) := hp
        cases h' with | word h => exact h
      simp only [Val.isStatic, ite_true, enc, hw32] at hmeta
      rw [hmeta] at hpay
      rcases slicePayload_some hpay with ⟨-, -, rfl⟩ | ⟨h0, -⟩
      · simp only [annotate_compValue] at hbound hvis
        rw [annotate_children, hch] at hvis
        simp only [List.map_cons, List.map_nil, List.headD_cons] at hvis
        have hbound' : sliceShift c.compValue + sliceSize c.compValue ≤ w.length := by omega
        have hwl := length_window hbound'
        have hfit : Fits data ⟨loc.offset, 32⟩ w := ⟨hat, by rw [hw32]; exact Nat.le_refl _⟩
        obtain ⟨rfl, d0, bs', hd, hw0, hat0, hy, h1', h32', hiw⟩ :=
          visit_win hvis (c := _) (bs := window w _ _) rfl hw (hfit.window hbound') (by rw [hwl])
            (by rw [hwl]; exact hs1) (by rw [hwl]; exact hs32)
        exact Or.inr (Or.inr (Or.inl ⟨d0, bs', _, loc.offset, w, hd, hw0, hat0, hy, h1', h32',
          Val.sub_nil _, hp, rfl, hiw.trans (IsWindow.window hbound')⟩))
      · omega
    | .sliceBytes (u := u) he _ hch hs1 hs32 hw hu =>
      have hmeta := (Desc.sliceBytes he hop0 hch hs1 hs32 hw hu (s := s)).annotate_meta
      have hLP := LPl.to_LP_of_root hp hr (by rw [he]; decide) (by rw [he]; decide)
      obtain ⟨cb, _, hload, hat, hct⟩ := hLP.bytesLike_content hu
      simp only [isStatic_bytesLike hu, Bool.false_eq_true, ite_false] at hmeta
      rw [hmeta] at hpay
      rcases slicePayload_some hpay with ⟨h0, -⟩ | ⟨-, -, -, rfl⟩
      · omega
      · simp only [annotate_compValue, hload] at hbound hvis
        rw [annotate_children, hch] at hvis
        simp only [List.map_cons, List.map_nil, List.headD_cons] at hvis
        have hwl := length_window hbound
        have hfit : Fits data ⟨loc.offset + 32, cb.length⟩ cb := ⟨hat, Nat.le_refl _⟩
        obtain ⟨rfl, d0, bs', hd, hw0, hat0, hy, h1', h32', hiw⟩ :=
          visit_win hvis (c := _) (bs := window cb _ _) rfl hw (hfit.window hbound) (by rw [hwl])
            (by rw [hwl]; exact hs1) (by rw [hwl]; exact hs32)
        exact Or.inr (Or.inr (Or.inl ⟨d0, bs', u, loc.offset, cb, hd, hw0, hat0, hy, h1', h32',
          Val.sub_nil u, hp, hct, hiw.trans (IsWindow.window hbound)⟩))
    | .word _ _ hnav _ | .bytes _ _ hnav _ => rw [hop0] at hnav; simp [isNavOp] at hnav
    | .tuple _ _ _ _ _ hnav => rcases hnav with ⟨h, -⟩ | h <;> (rw [hop0] at h; simp [isNavOp] at h)
    | .array _ _ _ _ _ _ _ hnav =>
      rcases hnav with ⟨h, -⟩ | h | h | h | h <;> (rw [hop0] at h; simp [isNavOp] at h)
    | .call _ _ _ _ _ hop' => rw [hop0] at hop'; simp at hop'
    | .logical _ _ hop' _ _ _ _ => rw [hop0] at hop'; simp at hop'

/-! ## Zip jumps -/

theorem zip_pluckL {s : Bool} {data : Bytes} {root : Condition} {V0 : Val} {pp : List Nat}
    {pk : Condition} {L : Slice} {yk : Nat} {z0 : Condition} {f : Nat} (hZ : ZipOK s root)
    (hz0 : Sub z0 root) (hzop : z0.operator = .ZipSome ∨ z0.operator = .ZipEvery)
    (hf : f < (zipFields z0).length) (hpkop : pk.operator = .Pluck)
    (hidx : cvByte pk.compValue 0 = cvByte z0.compValue f) (hraw : RawIn root pk)
    (hR : ReachedL s data root ⟨0, data.length⟩ V0 pp pk L yk) :
    (∃ vs, V0.sub pp = some (.array vs) ∧ LP data L.offset (.array vs) ∧
      ∀ v, v ∈ vs → DescS s (zipFields z0)[f] v) ∨
    InStrayL s data root ⟨0, data.length⟩ V0 pp pk L yk := by
  obtain ⟨pk1, hpk1, rfl⟩ := hraw
  have hop1' := annotate_op_of hpkop (by decide)
  have hpk1s : Sub pk1 root := by
    rcases hpk1 with h | rfl
    · exact h
    · cases hop1'
  have hcv1 : cvByte pk1.compValue 0 = cvByte z0.compValue f := by
    rw [← hidx, annotate_compValue]
  have henc1 := (hZ z0 pk1 f hz0 hpk1s hzop hf hop1' hcv1).1
  have hpkenc : (annotate pk1).encoding = .Array := by rw [annotate_encoding, henc1]; simp
  rcases hR with ⟨d0, V, hd0, hd, hy, hsub, hD, hp, _⟩ | ⟨d0, hd, hns⟩ |
    ⟨d0, bs, u', lu, cb, hd, hw, _⟩ | hst
  · rw [hd] at hpkop hidx
    have hop0 := annotate_op_of hpkop (by decide)
    have hcv0 : cvByte d0.compValue 0 = cvByte z0.compValue f := by
      rw [← hidx, annotate_compValue]
    obtain ⟨he0, hall⟩ := hZ z0 d0 f hz0 hd0 hzop hf hop0 hcv0
    obtain ⟨vs, rfl⟩ := hD.array_of he0
    refine Or.inl ⟨vs, hsub, hp, fun v hv => ?_⟩
    have := hall vs hD v hv
    have hg : (zipFields z0).getD f default = (zipFields z0)[f] := by simp [hf]
    rwa [hg] at this
  · exfalso
    rw [hd, annotate_encoding] at hpkenc
    rcases hns with hns | ⟨_, he, _, _⟩
    · cases hns with
      | leaf he _ _ => rcases he with he | he <;> simp [he] at hpkenc
      | logical he _ _ => simp [he] at hpkenc
    · simp [he] at hpkenc
  · exfalso
    have he : d0.encoding = .Static := by cases hw <;> assumption
    rw [hd, annotate_encoding, he] at hpkenc
    cases hpkenc
  · exact Or.inr hst

/-- Soundness of navigation from the root, including Zip jumps, on any
    layout the target accepts. -/
theorem eval_soundL {data : Bytes} {s : Bool} {root : Condition}
    {V0 : Val} (hD : Desc s root V0) (hR : RootOK root) (hp0 : LPl data 0 V0)
    (hZ : ZipOK s root) :
    ∀ {p d l y}, Eval data (annotate root) p d l y →
      ReachedL s data root ⟨0, data.length⟩ V0 p d l y := by
  intro p d l y he
  induction he with
  | visit hv => exact visit_soundL hv rfl rfl hD hp0 (fun _ _ => hR)
  | @zip pz z lz yz pp pk L yk p d l y f op spans i hi hzE hzop hf hpkE hpkop hidx hop hch hvis _
      ihpk =>
    have hent0 := Below.zip (p := []) hi (Eval.toBelow hpkE) hpkop hop hch .here
    obtain ⟨z0, hz0s, hzop0, hfields, hcv⟩ := Eval.zip_raw hzE hzop
    have hf0 : f < (zipFields z0).length := by rw [hfields] at hf; simpa using hf
    have hfield : (zipFields z).getD f default = annotate (zipFields z0)[f] := by
      rw [hfields]; simp [hf0]
    have hidx0 : cvByte pk.compValue 0 = cvByte z0.compValue f := by rw [hidx, hcv]
    rcases zip_pluckL hZ hz0s hzop0 hf0 hpkop hidx0 (Eval.rawIn hpkE) ihpk with
      ⟨vs, hsub, hlp, hall⟩ | ⟨hs, p1, p2, ch, us, ls, rfl, hsub, hsc, hb, hu, hnd, hp, hb1, hbel⟩
    · have hoff := (pluckSpan_some hop hch).1
      rw [hfield] at hch hvis hent0
      obtain ⟨hcnt, hblk⟩ := hlp.array_block
      rw [← hoff] at hcnt hblk
      obtain ⟨hlen', hpl⟩ := elements_LP hall hcnt hblk hch
      have hiv : i < vs.length := by omega
      have hpc := child_placedL (c := (zipFields z0)[f]) (hpl i hi hiv)
      have hsubF : Sub (zipFields z0)[f] root :=
        (Sub.zipField (List.getElem_mem hf0)).trans hz0s
      have key := ReachedL.stepP (P := pp ++ [i]) (u := V0) (v := vs[i])
        (fun q => by rw [List.append_assoc, Val.sub_append hsub]; exact Val.sub_array vs i hiv q)
        hsubF hent0 (hall _ (List.getElem_mem hiv)) hpc.1 hvis
        (fun hd => visit_soundL hvis rfl rfl hd hpc.1 hpc.2)
      simpa [List.append_assoc] using key
    · exact Or.inr (Or.inr (Or.inr ⟨hs, p1, p2 ++ i :: p, ch, us, ls, by simp, hsub, hsc, hb, hu,
        hnd, hp, hb1, .zip hi hbel hpkop hop hch hvis⟩))

/-! ## Operands -/

theorem natBE_wordVal : ∀ (n : Nat) (bs : Bytes), bs.length = n → natBE n (wordVal bs) = bs
  | 0, bs, h => by rw [List.length_eq_zero_iff.mp h]; rfl
  | n + 1, bs, h => by
    have hne : bs ≠ [] := by intro e; subst e; simp at h
    obtain ⟨init, b, rfl⟩ : ∃ init b, bs = init ++ [b] :=
      ⟨bs.dropLast, bs.getLast hne, (List.dropLast_concat_getLast hne).symm⟩
    simp only [List.length_append, List.length_singleton] at h
    rw [natBE, wordVal_append_single]
    have hb := b.isLt
    have h1 : (wordVal init * 256 + b.val) / 256 = wordVal init := by omega
    have h2 : (wordVal init * 256 + b.val) % 256 = b.val := by omega
    simp only [h1, h2, natBE_wordVal n init (by omega)]

/-- Equal operands come from equal bytes. -/
theorem expectInput_inj {R B : Bytes} (h : expectInput R = expectInput B) : R = B := by
  unfold expectInput at h
  by_cases hr : R.length = 32 <;> by_cases hb : B.length = 32 <;> simp [hr, hb] at h
  · rw [← natBE_wordVal 32 R hr, ← natBE_wordVal 32 B hb, h]
  · exact h

/-- `_read` of a node with an encoding, in a slice within the calldata: no
    operand, or the bytes of the operand at the start of the slice. -/
theorem input_region {data : Bytes} {l : Slice} {y : Nat} {c : Condition}
    (hne : c.encoding ≠ .None) (hin : Within data l) :
    input data l y c = .overflow ∨ ∃ R, At data l.offset R ∧
      operand data l y c = some ⟨l.offset, R.length⟩ ∧
      input data l y c = (if R.length ≤ 32 then .word (wordVal R) else .hash R) := by
  unfold Within at hin
  unfold input
  rw [ite_eq_right hne]
  cases ho : operand data l y c with
  | none => left; rfl
  | some op =>
    right
    obtain ⟨hoff, hle⟩ := operand_some ho
    obtain ⟨o, n⟩ := op
    simp only at hoff hle
    subst hoff
    have hl : ((data.drop l.offset).take n).length = n := by simp; omega
    refine ⟨(data.drop l.offset).take n, At_take (by omega), by rw [hl], ?_⟩
    simp only [Slice.bytes]
    rw [hl]
    by_cases h32 : n ≤ 32
    · rw [ite_eq_right (by omega), ite_eq_left h32]
    · rw [ite_eq_left (by omega), ite_eq_right h32]

theorem headSize_ge {s : Bool} {c : Condition} {v : Val} (cs : List Condition) (h : DescS s c v) :
    32 ≤ headSize (annotate c :: cs) := by
  have m := h.annotate_meta
  have hge := h.enc_ge
  simp only [headSize]
  have : 32 ≤ slotSize (annotate c).inlineSize := by
    rw [m]; unfold slotSize
    cases v.isStatic
    · simp
    · simp only [ite_true]; rw [ite_eq_left (by omega)]; exact hge
  omega

/-- A described dynamic value has a region of at least a word. -/
theorem region_ge_32 {data : Bytes} {l : Slice} {s : Bool} {c : Condition} {u : Val} {n : Nat}
    (hD : Desc s c u) (hne : c.encoding ≠ .None) (hs : u.isStatic = false)
    (h : region data l (annotate c) = some n) : 32 ≤ n := by
  have hm := hD.annotate_meta
  rw [hs] at hm
  simp only [Bool.false_eq_true, ite_false] at hm
  match hD with
  | .word _ _ _ _ | .sliceWord _ _ _ _ _ _ _ => simp [Val.isStatic] at hs
  | .bytes he _ _ _ | .sliceBytes he _ _ _ _ _ _ =>
    have := (region_bytes_some hm (.inl (by rw [annotate_encoding, he]; simp)) h).2.2.1
    omega
  | .call he _ _ _ _ _ =>
    have := (region_bytes_some hm (.inr (by rw [annotate_encoding, he]; simp)) h).2.2.1
    omega
  | .array c0 cs he hcs _ _ _ _ =>
    rw [region_eq, hm, ite_eq_right (by omega), annotate_encoding, he, annotate_children, hcs] at h
    simp only [reduceCtorEq, ite_false, false_or, ite_true, List.map_cons] at h
    split at h
    · cases h
    · split at h
      · simp only [Option.some.injEq] at h; omega
      · rw [Option.map_eq_some_iff] at h
        obtain ⟨r, -, rfl⟩ := h
        omega
  | .logical _ he _ _ _ _ _ => exact absurd he hne
  | .tuple he hcne _ hall _ _ =>
    rw [region_eq, hm, ite_eq_right (by omega), annotate_encoding, he, annotate_children] at h
    simp only [reduceCtorEq, ite_false, false_or, ite_true] at h
    obtain ⟨ch, chs, hcs⟩ := List.exists_cons_of_ne_nil hcne
    rw [hcs] at hall h
    have h0 := DescAll.get hall 0 (by simp)
    simp only [List.getElem_cons_zero] at h0
    simp only [List.map_cons] at h
    have hh := headSize_ge (chs.map annotate) h0
    split at h
    · cases h
    · have := (regionTuple_le data _ l 0 _ n h (by omega)).1
      omega

/-- The components of a static block, each in place, make up its head. -/
theorem block_static_At {data : Bytes} : ∀ (vs : List Val) (base off : Nat),
    Val.allStatic vs = true →
    (∀ i (h : i < vs.length), base + headOff vs i + (enc vs[i]).length ≤ data.length →
      At data (base + headOff vs i) (enc vs[i])) →
    base + headLen vs ≤ data.length → At data base (encParts vs off).1
  | [], base, _, _, _, hb => At_nil data base (by simp [headLen] at hb; omega)
  | v :: vs, base, off, hs, h, hb => by
    simp only [Val.allStatic, Bool.and_eq_true] at hs
    simp only [encParts, hs.1, ite_true]
    simp only [headLen, hs.1, ite_true] at hb
    have h0 := h 0 (by simp) (by simp [headOff]; omega)
    simp only [headOff, Nat.add_zero, List.getElem_cons_zero] at h0
    refine At_append.mpr ⟨h0, block_static_At vs (base + (enc v).length) off hs.2
      (fun i hi hbi => ?_) (by omega)⟩
    have := h (i + 1) (by simp; omega) (by
      simp only [headOff, hs.1, ite_true, List.getElem_cons_succ]; omega)
    simp only [headOff, hs.1, ite_true, List.getElem_cons_succ] at this
    rwa [Nat.add_assoc]

/-- A static value read by following offsets is contiguous: its spec
    encoding (static values have no offsets). -/
theorem LP.static_At {data : Bytes} {l : Nat} {u : Val} (h : LP data l u) :
    u.isStatic = true → l + (enc u).length ≤ data.length → At data l (enc u) := by
  induction h with
  | word hat => intro _ _; simpa [enc] using hat
  | bytes => intro h; simp [Val.isStatic] at h
  | @tuple data l vs _ _ _ ihs _ =>
    intro hst hb
    simp only [Val.isStatic] at hst
    rw [enc_tuple, encTuple, encParts_snd_nil vs _ hst, List.append_nil]
    rw [enc_tuple, encTuple_length_static vs hst] at hb
    exact block_static_At vs l _ hst
      (fun i hi hbi => ihs i hi ((allStatic_iff vs).mp hst i hi) ((allStatic_iff vs).mp hst i hi) hbi)
      hb
  | array => intro h; simp [Val.isStatic] at h
  | call => intro h; simp [Val.isStatic] at h

/-- The operand of a described comparison node in a slice that starts
    where the target reads its component from: no operand, or the bytes of
    a region at that location, at least a word long; for a static
    component exactly its encoding. -/
theorem desc_input_region {data : Bytes} (hlen : data.length < 2 ^ 255) {s : Bool}
    {c : Condition} {u : Val} {l : Slice} (hin : Within data l) (hD : Desc s c u)
    (hLP : LP data l.offset u)
    (henc : c.encoding ≠ .AbiEncoded ∧ c.encoding ≠ .None ∧ c.encoding ≠ .EtherValue)
    (hn : isNavOp c.operator = false) :
    input data l (annotate c).inlineSize (annotate c) = .overflow ∨ ∃ R, At data l.offset R ∧
      32 ≤ R.length ∧ input data l (annotate c).inlineSize (annotate c) = expectInput R ∧
      (u.isStatic = true → R = enc u) := by
  have hne' : (annotate c).encoding ≠ .None := by
    rw [annotate_encoding, ite_eq_right henc.2.2]; exact henc.2.1
  have hmeta := hD.annotate_meta
  have hge := hD.enc_ge
  cases hs : u.isStatic
  · rcases input_region (y := (annotate c).inlineSize) hne' hin with h | ⟨R, hat, hop, hinp⟩
    · exact Or.inl h
    · right
      have hsz : (annotate c).inlineSize = 0 := by rw [hmeta, hs]; simp
      have h32 : 32 ≤ R.length := by
        unfold operand sliceRegion at hop
        rw [hsz, ite_eq_right (by omega)] at hop
        cases hr : region data l (annotate c) with
        | none => rw [hr] at hop; cases hop
        | some n =>
          rw [hr] at hop
          simp only [Option.map_some, Option.some.injEq, Slice.mk.injEq, true_and] at hop
          rw [← hop]
          exact region_ge_32 hD henc.2.1 hs hr
      refine ⟨R, hat, h32, ?_, fun h => by simp at h⟩
      rw [hinp]
      unfold expectInput
      by_cases h' : R.length = 32
      · rw [ite_eq_left (by omega), ite_eq_left h']
      · rw [ite_eq_right (by omega), ite_eq_right h']
  · unfold Within at hin
    by_cases hb : (enc u).length ≤ l.length
    · have hat := hLP.static_At hs (by omega)
      exact Or.inr ⟨enc u, hat, hge, Desc.input_eq hlen hD ⟨hat, hb⟩ hne' hn, fun _ => rfl⟩
    · left
      unfold input operand slicePayload
      rw [ite_eq_right hne', hmeta, hs]
      simp only [ite_true]
      rw [ite_eq_left (by omega), ite_eq_left (by omega), ite_eq_left (by omega)]

/-- Bitmask on a `bytes` value the target reads at the start of the slice:
    Roles finds no payload, or checks the content the target decodes. -/
theorem bitmask_content {data : Bytes} {l : Slice} {cb : Bytes} (cv junk : Bytes)
    (hload : load data l.offset = cb.length) (hc : At data (l.offset + 32) cb) :
    bitmask data l 0 cv junk = .CalldataOverflow ∨ bitmask data l 0 cv junk = bitmaskSpec cb cv := by
  unfold bitmask
  cases hp : slicePayload data l 0 with
  | none => exact Or.inl rfl
  | some payload =>
    right
    rcases slicePayload_some hp with ⟨h0, -⟩ | ⟨-, -, -, rfl⟩
    · omega
    · simp only
      rw [hload]
      exact bitmaskCheck_eq cv junk hc

/-- Bitmask on a word the target reads at the start of the slice. -/
theorem bitmask_word {data : Bytes} {l : Slice} {w : Bytes} (cv junk : Bytes)
    (hw : w.length = 32) (hat : At data l.offset w) :
    bitmask data l 32 cv junk = .CalldataOverflow ∨ bitmask data l 32 cv junk = bitmaskSpec w cv := by
  unfold bitmask
  cases hp : slicePayload data l 32 with
  | none => exact Or.inl rfl
  | some payload =>
    right
    rcases slicePayload_some hp with ⟨-, -, rfl⟩ | ⟨h0, -⟩
    · simp only
      rw [← hw]
      exact bitmaskCheck_eq cv junk hat
    · omega

/-! ## Top-level statements

The calldata is anything a decoder that follows offsets reads as the call
`pre ++ args` (`LPCall`); `Decoder.lean` shows solc's decoder accepts
only such calldata (`BlockOK.call` turns its result into `LPCall`). -/

section Top

variable {root : Condition} {data pre : Bytes} {args : List Val}

/-- **Locations, on any layout the target accepts.** Every node Roles
    visits is in a slice that starts where the target reads the component
    it describes from (same index path), at a window of the bytes the
    target decodes for that component (below `Slice`), non-structural, or
    inside a variant branch that does not fit the bytes value it is
    evaluated on; the branch itself is reached where the target reads that
    value (`InStrayL`, only with `s = true`). -/
theorem target_locations {s : Bool}
    (hD : Desc s root (.call pre args)) (hR : RootOK root) (hZ : ZipOK s root)
    (hc : LPCall data pre args)
    {p : List Nat} {d : Condition} {l : Slice} {y : Nat}
    (hv : Eval data (annotate root) p d l y) :
    ReachedL s data root ⟨0, data.length⟩ (.call pre args) p d l y :=
  eval_soundL hD hR (Or.inl ⟨rfl, hc⟩) hZ hv

theorem InStrayL.strict {data : Bytes} {top : Condition} {loc : Slice} {u : Val} {p : List Nat}
    {d : Condition} {l : Slice} {y : Nat} : ¬ InStrayL false data top loc u p d l y :=
  fun h => Bool.false_ne_true h.1

/-- **Comparison operands, on any layout the target accepts.** For every
    visited node whose operator calls `_read`, one of:

    * it describes component `u` (which the target reads where the slice
      starts). For a static `u`, the operand is exactly `u`'s spec encoding
      (or Roles reports overflow). For any `u`: **if the operand equals the
      spec operand of a value `v` of `u`'s shape (`HasSh` of the same
      shape: `v` encoded with the parameter's type), then `u = v`.** So an
      `EqualTo` whose compValue is the spec encoding of `v` passes only if
      the target decoded `v`. (It may fail although the target decoded `v`:
      Roles reads one canonical region.) For a dynamic `u` the operand is a
      hash, represented by its preimage (`expectInput_inj`): this step
      trusts keccak256 collision resistance.
    * below a `Slice`: a window of the bytes the target decodes for `u`
      (which window is tested, not proven);
    * the ether value;
    * inside a variant branch that does not fit (`InStrayL`, only with
      `s = true`). -/
theorem target_input {s : Bool}
    (hD : Desc s root (.call pre args)) (hR : RootOK root) (hZ : ZipOK s root)
    (hc : LPCall data pre args) (hlen : data.length < 2 ^ 255)
    {p : List Nat} {d : Condition} {l : Slice} {y : Nat}
    (hv : Eval data (annotate root) p d l y)
    (hop : readsInput d.operator = true) :
    (∃ u, (Val.call pre args).sub p = some u ∧ LP data l.offset u ∧
      (u.isStatic = true →
        input data l y d = expectInput (enc u) ∨ input data l y d = .overflow) ∧
      ∀ v sh, small v = true → HasSh u sh → HasSh v sh →
        input data l y d = expectInput (enc v) → u = v) ∨
    (∃ u bs lu cb, (Val.call pre args).sub p = some u ∧ LPl data lu u ∧ ContentAt data lu u cb ∧
      IsWindow bs cb ∧ input data l y d = .word (wordVal bs)) ∨
    input data l y d = .etherValue ∨
    InStrayL s data root ⟨0, data.length⟩ (.call pre args) p d l y := by
  have hwithin := Eval.within hv
  rcases target_locations hD hR hZ hc hv with
    ⟨d0, u, _, rfl, rfl, hsub, hD0, hp, hr⟩ | ⟨d0, rfl, hns⟩ |
    ⟨d0, bs, u, lu, cb, rfl, hw, hat, rfl, h1, h32, hsub, hpl, hct, hiw⟩ | hst
  · left
    have henc := hD0.plain_encoding (by
      refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> intro h <;> rw [h] at hop <;> simp [readsInput] at hop)
    have hLP := LPl.to_LP_of_root hp hr henc.1 henc.2.1
    have hn : isNavOp d0.operator = false := by
      rw [← isNavOp_annotate]; cases h : (annotate d0).operator <;> simp_all [readsInput, isNavOp]
    refine ⟨u, hsub, hLP, ?_, ?_⟩
    · intro hs
      rcases desc_input_region hlen hwithin hD0 hLP henc hn with h | ⟨R, _, _, hin, hR'⟩
      · exact Or.inr h
      · exact Or.inl (by rw [hin, hR' hs])
    · intro v sh hsm hsu hsv hin
      rcases desc_input_region hlen hwithin hD0 hLP henc hn with h | ⟨R, hat, _, hin', _⟩
      · rw [h] at hin; unfold expectInput at hin; split at hin <;> cases hin
      · have hRv : R = enc v := expectInput_inj (by rw [← hin', hin])
        rw [hRv] at hat
        exact region_det hlen hLP hat hsm hsu hsv
  · right; right; left
    unfold input
    rw [annotate_encoding]
    rcases hns with hns | ⟨_, he, _, _⟩
    · cases hns with
      | leaf he _ _ => rcases he with he | he <;> simp [he]
      | logical he _ _ => simp [he]
    · simp [he]
  · right; left
    exact ⟨u, bs, lu, cb, hsub, hpl, hct, hiw, Win.input_eq hw hat h1 h32⟩
  · right; right; right; exact hst

/-- **Bitmask, on any layout the target accepts.** `_bitmask` finds no
    payload in its slice (`CalldataOverflow`), or returns `bitmaskSpec` of
    the bytes the target decodes for the component: its word, the content
    of a `bytes` value, or below a `Slice` a window of it. Or the node is
    inside a variant branch that does not fit (`InStrayL`, only with
    `s = true`). -/
theorem target_bitmask {s : Bool}
    (hD : Desc s root (.call pre args)) (hR : RootOK root) (hZ : ZipOK s root)
    (hc : LPCall data pre args)
    {p : List Nat} {d : Condition} {l : Slice} {y : Nat}
    (hv : Eval data (annotate root) p d l y)
    (hop : d.operator = .Bitmask) (henc : d.encoding = .Static ∨ d.encoding = .Dynamic)
    (junk : Bytes) :
    (∃ u cb, (Val.call pre args).sub p = some u ∧ ContentAt data l.offset u cb ∧
      (bitmask data l y d.compValue junk = .CalldataOverflow ∨
        bitmask data l y d.compValue junk = bitmaskSpec cb d.compValue)) ∨
    (∃ u bs lu cb, (Val.call pre args).sub p = some u ∧ LPl data lu u ∧ ContentAt data lu u cb ∧
      IsWindow bs cb ∧ bitmask data l y d.compValue junk = bitmaskSpec bs d.compValue) ∨
    InStrayL s data root ⟨0, data.length⟩ (.call pre args) p d l y := by
  rcases target_locations hD hR hZ hc hv with
    ⟨d0, u, _, rfl, rfl, hsub, hD0, hp, hr⟩ | ⟨d0, rfl, hns⟩ |
    ⟨d0, bs, u, lu, cb, rfl, hw, hat, rfl, h1, _, hsub, hpl, hct, hiw⟩ | hst
  · left
    have hop0 := annotate_op_of hop (by decide)
    have hmeta := hD0.annotate_meta
    rw [annotate_encoding] at henc
    match hD0 with
    | .word (w := w) he _ _ hw =>
      have hat : At data l.offset w := by
        have h' : LP data l.offset (.word w) := hp
        cases h' with | word h => exact h
      refine ⟨_, w, hsub, rfl, ?_⟩
      simp only [Val.isStatic, ite_true, enc, hw] at hmeta
      rw [hmeta, annotate_compValue]
      exact bitmask_word _ junk hw hat
    | .bytes he _ _ hu =>
      have hLP := LPl.to_LP_of_root hp hr (by rw [he]; decide) (by rw [he]; decide)
      obtain ⟨cb, hb, hload, hat, hct⟩ := hLP.bytesLike_content hu
      refine ⟨u, cb, hsub, hct, ?_⟩
      simp only [isStatic_bytesLike hu, Bool.false_eq_true, ite_false] at hmeta
      rw [hmeta, annotate_compValue]
      exact bitmask_content _ junk hload hat
    | .sliceWord _ h _ _ _ _ _ | .sliceBytes _ h _ _ _ _ _ => rw [hop0] at h; cases h
    | .tuple he _ _ _ _ _ | .array _ _ he _ _ _ _ _ | .call he _ _ _ _ _ | .logical _ he _ _ _ _ _ =>
      rw [he] at henc; simp at henc
  · exfalso
    rw [annotate_encoding] at henc
    rcases hns with hns | ⟨_, he, _, _⟩
    · cases hns with
      | leaf he _ _ => rcases he with he | he <;> simp [he] at henc
      | logical he _ _ => simp [he] at henc
    · simp [he] at henc
  · right; left
    refine ⟨u, bs, lu, cb, hsub, hpl, hct, hiw, ?_⟩
    rw [annotate_compValue]
    exact bitmask_inlined _ junk hat h1
  · right; right; exact hst

end Top

/-! ## Example: a layout that is not the spec encoding

`f(bytes a, bytes b)` with the tails in reverse order: `b`'s tail first.
`LPCall` holds, so `target_locations` and `target_input` apply, although
`DecoderFaithfulness` (spec encoding only) does not. (solc's decoder, and
the `decode` model, accept it too.) -/

section Example

def exSel : Bytes := zeros 4
def exData : Bytes :=
  exSel ++ word 0x80 ++ word 0x40 ++ word 1 ++ ([2] ++ zeros 31) ++ word 1 ++ ([1] ++ zeros 31)
def exArgs : List Val := [.bytes [1], .bytes [2]]

theorem ex_not_spec : exData ≠ exSel ++ encTuple exArgs := by decide +kernel

/-- The hypothesis of the theorems holds for this layout. -/
theorem ex_LPCall : LPCall exData exSel exArgs := by
  refine ⟨by decide +kernel, by decide +kernel, fun i hi hs => ?_, fun i hi hs => ?_⟩
  · match i, hi with
    | 0, _ | 1, _ => simp [exArgs, Val.isStatic] at hs
  · match i, hi with
    | 0, _ => exact ⟨by decide +kernel, .bytes (by decide +kernel) (by decide +kernel)
        ⟨by decide +kernel, by decide +kernel⟩⟩
    | 1, _ => exact ⟨by decide +kernel, .bytes (by decide +kernel) (by decide +kernel)
        ⟨by decide +kernel, by decide +kernel⟩⟩

end Example

end TargetDecode
