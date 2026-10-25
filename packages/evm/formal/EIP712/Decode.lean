import EIP712.Hash
import DecoderFaithfulness.Decode

/-!
# On the spec encoding, the encoder reads the value

`readV_enc`: if the bytes at `loc` are the Solidity ABI spec encoding
(`DecoderFaithfulness.enc`) of a typed EIP-712 value `v` (seen as an ABI
value, `abiOf`), the walk reads back exactly `v`. Together with
`hashField_spec`, the contract hashes `v` exactly as EIP-712 says.

Static / dynamic and the inline sizes come from `_inlineSize` on the type
tree (`inlineSize_lay`); they agree with the ABI's.
-/

namespace EIP712
open DecoderFaithfulness DecoderFaithfulness.Roles

/-- The ABI slot an encoded value takes in its parent's head: its encoding
    if static, else `0` (an offset word), as `_inlineSize` reports it. -/
def sz (u : Val) : Nat := if u.isStatic then (enc u).length else 0

theorem headLen_cons (u : Val) (us : List Val) :
    headLen (u :: us) = (if u.isStatic then (enc u).length else 32) + headLen us := by
  simp [headLen]

theorem allStatic_cons (u : Val) (us : List Val) :
    Val.allStatic (u :: us) = (u.isStatic && Val.allStatic us) := by
  simp [Val.allStatic]

/-- `inlineSizeL` on children whose inline sizes match their values. -/
theorem inlineSizeL_eq (ls : List TN) (us : List Val)
    (hlen : ls.length = us.length)
    (hk : ∀ k (h1 : k < ls.length) (h2 : k < us.length),
      inlineSize ls[k] = some (sz us[k]) ∧ 32 ≤ (enc us[k]).length) :
    ∀ acc, inlineSizeL ls acc =
      some (if Val.allStatic us then acc + headLen us else 0) := by
  induction ls generalizing us with
  | nil =>
    cases us with
    | nil => intro acc; simp [inlineSizeL, Val.allStatic, headLen]
    | cons => simp at hlen
  | cons l ls ih =>
    cases us with
    | nil => simp at hlen
    | cons u us =>
      intro acc
      obtain ⟨h0, h32⟩ := hk 0 (by simp) (by simp)
      simp only [List.getElem_cons_zero] at h0 h32
      have ih' := ih us (by simpa using hlen) (fun k h1 h2 => by
        have := hk (k + 1) (by simp; omega) (by simp; omega)
        rw [List.getElem_cons_succ, List.getElem_cons_succ] at this
        exact this)
      simp only [inlineSizeL, h0, sz]
      by_cases hs : u.isStatic
      · obtain ⟨m, hm⟩ : ∃ m, (enc u).length = m + 1 := ⟨(enc u).length - 1, by omega⟩
        simp only [hs, ite_true, hm]
        rw [ih' (acc + (m + 1)), allStatic_cons, headLen_cons]
        simp only [hs, Bool.true_and, ite_true, hm]
        split <;> simp [Nat.add_assoc]
      · simp [hs, allStatic_cons]

theorem HasTys.length {defs : Defs} : ∀ {tys vs}, HasTys defs tys vs → tys.length = vs.length
  | _, _, .nil => rfl
  | _, _, .cons _ h => by simp [HasTys.length h]

theorem HasTys.get {defs : Defs} : ∀ {tys vs}, HasTys defs tys vs → ∀ k (hk : k < vs.length),
    HasTy defs (tys.getD k default) vs[k]
  | _, _, .nil, _, hk => by simp at hk
  | _, _, .cons h _, 0, _ => by simpa using h
  | _, _, .cons _ hs, k + 1, hk => by simpa using HasTys.get hs k (by simp at hk; omega)

theorem HasSame.get {defs : Defs} {t : Ty} : ∀ {vs}, HasSame defs t vs → ∀ k (hk : k < vs.length),
    HasTy defs t vs[k]
  | _, .nil, _, hk => by simp at hk
  | _, .cons h _, 0, _ => by simpa using h
  | _, .cons _ hs, k + 1, hk => by simpa using HasSame.get hs k (by simp at hk; omega)

theorem abiFields_length (defs : Defs) : ∀ (tys : List Ty) (vs : List V),
    tys.length = vs.length → (abiFields defs tys vs).length = vs.length
  | [], [], _ => by simp [abiFields]
  | _ :: ts, _ :: vs, h => by simp [abiFields, abiFields_length defs ts vs (by simpa using h)]
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

theorem abiFields_get (defs : Defs) : ∀ (tys : List Ty) (vs : List V) (h : tys.length = vs.length)
    (k : Nat) (hk : k < (abiFields defs tys vs).length),
    (abiFields defs tys vs)[k] = abiOf defs (tys.getD k default) (vs[k]'(by
      rw [abiFields_length defs tys vs h] at hk; exact hk))
  | [], [], _, _, hk => by simp [abiFields] at hk
  | t :: ts, v :: vs, h, 0, _ => by simp [abiFields]
  | t :: ts, v :: vs, h, k + 1, hk => by
    simp only [abiFields, List.getElem_cons_succ, List.getD_cons_succ]
    exact abiFields_get defs ts vs (by simpa using h) k _
  | [], _ :: _, h, _, _ => by simp at h
  | _ :: _, [], h, _, _ => by simp at h

theorem abiSame_length (defs : Defs) (t : Ty) : ∀ (vs : List V), (abiSame defs t vs).length = vs.length
  | [] => by simp [abiSame]
  | _ :: vs => by simp [abiSame, abiSame_length defs t vs]

theorem abiSame_get (defs : Defs) (t : Ty) : ∀ (vs : List V) (k : Nat)
    (hk : k < (abiSame defs t vs).length),
    (abiSame defs t vs)[k] = abiOf defs t (vs[k]'(by rw [abiSame_length] at hk; exact hk))
  | [], _, hk => by simp [abiSame] at hk
  | v :: vs, 0, _ => by simp [abiSame]
  | v :: vs, k + 1, hk => by
    simp only [abiSame, List.getElem_cons_succ]
    exact abiSame_get defs t vs k _

theorem sizeOf_getElem_lt (vs : List V) (k : Nat) (hk : k < vs.length) :
    sizeOf vs[k] < sizeOf (V.list vs) := by
  have := List.sizeOf_lt_of_mem (List.getElem_mem hk)
  simp only [V.list.sizeOf_spec]
  omega

/-- A tuple of encodings of at least a word each: its slot and size. -/
theorem tuple_slot (us : List Val) (hne : us ≠ []) (h32 : ∀ u ∈ us, 32 ≤ (enc u).length) :
    sz (.tuple us) = (if Val.allStatic us then 0 + headLen us else 0) ∧
      32 ≤ (enc (.tuple us)).length := by
  have hc := headLen_ge_count us h32
  have hge := encTuple_length_ge us
  have hpos : 0 < us.length := by cases us <;> simp_all
  refine ⟨?_, by rw [enc_tuple]; omega⟩
  unfold sz
  simp only [Val.isStatic]
  by_cases hs : Val.allStatic us = true
  · simp only [hs, ite_true]; rw [enc_tuple, encTuple_length_static us hs]; omega
  · simp [hs]

/-- `_inlineSize` of a type tree, and that every encoding is at least a word. -/
theorem inlineSize_lay {K : Bytes → Bytes} {defs : Defs} :
    ∀ (n : Nat) {ty : Ty} {v : V} {t : TN}, sizeOf v < n → HasTy defs ty v → Lay K defs ty t →
    inlineSize t = some (sz (abiOf defs ty v)) ∧ 32 ≤ (enc (abiOf defs ty v)).length
  | 0, _, _, _, h, _, _ => by omega
  | n + 1, ty, v, t, hn, hv, hl => by
    cases hl with
    | @atom a th =>
      cases hv with
      | @atom _ w hc =>
        have h32 : w.length = 32 := by cases a <;> exact hc.1
        simp [inlineSize, sz, abiOf, enc, Val.isStatic, h32]
    | bytes =>
      cases hv with
      | bytes => simp [inlineSize, sz, abiOf, Val.isStatic, enc, encBytes]
    | string =>
      cases hv with
      | string => simp [inlineSize, sz, abiOf, Val.isStatic, enc, encBytes]
    | @array t' l hl' =>
      cases hv with
      | array _ =>
        simp [inlineSize, sz, abiOf, Val.isStatic, enc]
    | @struct s ls hdef hls hne hth =>
      cases hv with
      | @struct _ vs _ hts =>
        have hlen := HasTys.length hts
        have hlen' := LayL.length hls
        have hk : ∀ k (hk : k < vs.length),
            inlineSize (ls.getD k default) = some (sz (abiOf defs (((fieldsOf defs s).map (·.ty)).getD k default) vs[k])) ∧
            32 ≤ (enc (abiOf defs (((fieldsOf defs s).map (·.ty)).getD k default) vs[k])).length :=
          fun k hk => inlineSize_lay n (by have := sizeOf_getElem_lt vs k hk; omega)
            (HasTys.get hts k hk) (LayL.get hls k (by omega))
        have hus := abiFields_length defs _ vs hlen
        have hne' : abiFields defs ((fieldsOf defs s).map (·.ty)) vs ≠ [] := by
          intro h
          have h0 : vs.length = 0 := by rw [← hus, h]; rfl
          exact hne (List.eq_nil_of_length_eq_zero (by omega))
        have h32 : ∀ u ∈ abiFields defs ((fieldsOf defs s).map (·.ty)) vs, 32 ≤ (enc u).length := by
          intro u hu
          obtain ⟨k, hk', rfl⟩ := List.getElem_of_mem hu
          rw [abiFields_get defs _ vs hlen k hk']
          exact (hk k (by omega)).2
        have hsz := inlineSizeL_eq ls (abiFields defs ((fieldsOf defs s).map (·.ty)) vs)
          (by omega) (fun k h1 h2 => by
            have hg : ls.getD k default = ls[k] := by simp [List.getD_eq_getElem?_getD, h1]
            rw [abiFields_get defs _ vs hlen k h2, ← hg]
            exact hk k (by omega)) 0
        obtain ⟨hs1, hs2⟩ := tuple_slot _ hne' h32
        simp only [abiOf]
        refine ⟨?_, hs2⟩
        simp only [inlineSize, show (Encoding.Tuple = Encoding.Dynamic) = False by simp,
          show (Encoding.Tuple = Encoding.Array) = False by simp,
          show (Encoding.Tuple = Encoding.Static) = False by simp, or_self, ite_false,
          ne_eq, not_true_eq_false, hne, hsz, hs1]
    | @fixed t' m l hm hl' =>
      cases hv with
      | @fixed _ _ vs hlen hsame =>
        have hk : ∀ k (hk : k < vs.length),
            inlineSize l = some (sz (abiOf defs t' vs[k])) ∧ 32 ≤ (enc (abiOf defs t' vs[k])).length :=
          fun k hk => inlineSize_lay n (by have := sizeOf_getElem_lt vs k hk; omega)
            (HasSame.get hsame k hk) hl'
        have hus := abiSame_length defs t' vs
        have hne' : abiSame defs t' vs ≠ [] := by
          intro h; rw [h] at hus; simp at hus; omega
        have h32 : ∀ u ∈ abiSame defs t' vs, 32 ≤ (enc u).length := by
          intro u hu
          obtain ⟨k, hk', rfl⟩ := List.getElem_of_mem hu
          rw [abiSame_get defs t' vs k hk']
          exact (hk k (by omega)).2
        have hsz := inlineSizeL_eq (List.replicate m l) (abiSame defs t' vs)
          (by simp; omega) (fun k h1 h2 => by
            rw [abiSame_get defs t' vs k h2, List.getElem_replicate]
            exact hk k (by omega)) 0
        obtain ⟨hs1, hs2⟩ := tuple_slot _ hne' h32
        simp only [abiOf]
        refine ⟨?_, hs2⟩
        have hrep : List.replicate m l ≠ [] := by simp; omega
        simp only [inlineSize, show (Encoding.Tuple = Encoding.Dynamic) = False by simp,
          show (Encoding.Tuple = Encoding.Array) = False by simp,
          show (Encoding.Tuple = Encoding.Static) = False by simp, or_self, ite_false,
          ne_eq, not_true_eq_false, hrep, hsz, hs1]

/-! ## The walk on a spec encoding -/

theorem TN.height_mk (e : Encoding) (cs : List TN) (th : Bytes) :
    (TN.mk e cs th).height = TN.heightL cs + 1 := by simp [TN.height]

theorem TN.height_le_of_mem {c : TN} : ∀ {cs : List TN}, c ∈ cs → c.height ≤ TN.heightL cs
  | [], h => by simp at h
  | d :: ds, h => by
    simp only [TN.heightL]
    rcases List.mem_cons.mp h with rfl | h
    · omega
    · have := TN.height_le_of_mem h; omega

/-- The block loop on a spec-encoded tuple block reads every member. -/
theorem readLoop_eq (data : Bytes) (hlen : data.length < 2 ^ 255) (rf : TN → Nat → Option V)
    (cs : List TN) (isArray : Bool) (bl : Nat) :
    ∀ (us : List Val) (vs : List V) (i h off : Nat), us.length = vs.length →
    (∀ k (hk : k < us.length) (hk' : k < vs.length),
      inlineSize (cs.getD (if isArray then 0 else i + k) default) = some (sz us[k]) ∧
      32 ≤ (enc us[k]).length ∧
      ∀ l, At data l (enc us[k]) → rf (cs.getD (if isArray then 0 else i + k) default) l = some vs[k]) →
    At data (bl + h) (encParts us off).1 →
    At data (bl + off) (encParts us off).2 →
    h + (encParts us off).1.length ≤ off →
    blockLoop data rf cs isArray bl us.length i h = some vs
  | [], [], _, _, _, _, _, _, _, _ => by simp [blockLoop]
  | [], _ :: _, _, _, _, hl, _, _, _, _ => by simp at hl
  | _ :: _, [], _, _, _, hl, _, _, _, _ => by simp at hl
  | u :: us, v :: vs, i, h, off, hl, hch, hH, hT, hinv => by
    obtain ⟨hsz, h32, hrf⟩ := hch 0 (by simp) (by simp)
    simp only [Nat.add_zero, List.getElem_cons_zero] at hsz h32 hrf
    have hrest : ∀ k (hk : k < us.length) (hk' : k < vs.length),
        inlineSize (cs.getD (if isArray then 0 else i + 1 + k) default) = some (sz us[k]) ∧
        32 ≤ (enc us[k]).length ∧
        ∀ l, At data l (enc us[k]) → rf (cs.getD (if isArray then 0 else i + 1 + k) default) l = some vs[k] := by
      intro k hk hk'
      have := hch (k + 1) (by simp; omega) (by simp; omega)
      simp only [List.getElem_cons_succ] at this
      rw [show i + 1 + k = i + (k + 1) by omega]
      exact this
    simp only [List.length_cons, blockLoop]
    by_cases hs : u.isStatic
    · -- static member: inline in the head
      simp only [encParts, hs, ite_true] at hH hT hinv
      obtain ⟨hv, hH'⟩ := At_append.mp hH
      simp only [List.length_append] at hinv
      have hb := hv.bound
      have hcl : childLocation data bl h (cs.getD (if isArray = true then 0 else i) default) =
          some (bl + h, (enc u).length) := by
        simp only [childLocation, hsz, sz, hs, ite_true]
        rw [if_pos (by omega), if_neg (by omega)]
      rw [hcl]
      simp only
      rw [hrf _ hv]
      simp only
      rw [if_pos (by omega)]
      rw [readLoop_eq data hlen rf cs isArray bl us vs (i + 1) (h + (enc u).length) off
        (by simpa using hl) hrest (by rw [← Nat.add_assoc]; exact hH') hT (by omega)]
      rfl
    · -- dynamic member: an offset word in the head, the encoding in the tail
      simp only [encParts, hs, ite_false, Bool.false_eq_true] at hH hT hinv
      obtain ⟨hw, hH'⟩ := At_append.mp hH
      obtain ⟨hv, hT'⟩ := At_append.mp hT
      simp only [List.length_append, length_word] at hinv
      have hwb := hw.bound
      have hvb := hv.bound
      simp only [length_word] at hwb
      have hoff : off < 2 ^ 256 := by
        have : (2 : Nat) ^ 255 < 2 ^ 256 := by decide
        omega
      have hcl : childLocation data bl h (cs.getD (if isArray = true then 0 else i) default) =
          some (bl + off, 0) := by
        simp only [childLocation, hsz, sz, hs, Bool.false_eq_true, ite_false, gt_iff_lt,
          Nat.lt_irrefl]
        rw [if_neg (by omega), load_of_At_append hH hoff, if_neg (by omega), if_neg (by omega)]
      rw [hcl]
      simp only
      rw [hrf _ hv]
      simp only [gt_iff_lt, Nat.lt_irrefl, ite_false]
      rw [readLoop_eq data hlen rf cs isArray bl us vs (i + 1) (h + 32) (off + (enc u).length)
        (by simpa using hl) hrest
        (by simp only [length_word] at hH'; rw [← Nat.add_assoc]; exact hH')
        (by rw [← Nat.add_assoc]; exact hT') (by omega)]
      rfl

/-- **On the spec ABI encoding of a typed value, the encoder reads exactly
    that value.** -/
theorem readV_enc (K : Bytes → Bytes) (defs : Defs) (data : Bytes) (hlen : data.length < 2 ^ 255) :
    ∀ (fuel : Nat) {ty : Ty} {v : V} {t : TN} (loc : Nat), HasTy defs ty v → Lay K defs ty t →
    t.height ≤ fuel → At data loc (enc (abiOf defs ty v)) → readV data fuel t loc = some v
  | 0, _, _, t, _, _, _, hf, _ => by
    cases t; simp [TN.height] at hf
  | fuel + 1, ty, v, t, loc, hv, hl, hf, hat => by
    cases hl with
    | @atom a th =>
      cases hv with
      | @atom _ w hc =>
        have h32 : w.length = 32 := by cases a <;> exact hc.1
        simp only [abiOf, enc] at hat
        simp only [readV, ite_true, wordAt]
        have hb := hat.bound
        rw [if_neg (by omega)]
        have := take_of_At hat
        rw [h32] at this
        simp [this]
    | bytes =>
      cases hv with
      | @bytes b =>
        have hat' : At data loc (encBytes b) := by simpa only [abiOf, enc] using hat
        have hcb := At_content hat'
        unfold encBytes at hat'
        obtain ⟨hwb', -⟩ := At_append.mp hat'
        obtain ⟨hw, -⟩ := At_append.mp hwb'
        have hwb : loc + 32 ≤ data.length := by
          have := hw.bound; simp only [length_word] at this; exact this
        have hbb := hcb.bound
        have hbl : b.length < 2 ^ 256 := by
          have : (2 : Nat) ^ 255 < 2 ^ 256 := by decide
          omega
        have htw : (data.drop loc).take 32 = word b.length := by
          have := take_of_At hw; rwa [length_word] at this
        simp only [readV, show (Encoding.Dynamic = Encoding.Static) = False by simp, ite_false,
          ite_true, wordAt]
        rw [if_neg (by omega), htw]
        simp only
        rw [wordVal_word _ hbl, if_neg (by omega), show loc + 32 + b.length - (loc + 32) = b.length by omega,
          take_of_At hcb]
    | string =>
      cases hv with
      | @string b =>
        have hat' : At data loc (encBytes b) := by simpa only [abiOf, enc] using hat
        have hcb := At_content hat'
        unfold encBytes at hat'
        obtain ⟨hwb', -⟩ := At_append.mp hat'
        obtain ⟨hw, -⟩ := At_append.mp hwb'
        have hwb : loc + 32 ≤ data.length := by
          have := hw.bound; simp only [length_word] at this; exact this
        have hbb := hcb.bound
        have hbl : b.length < 2 ^ 256 := by
          have : (2 : Nat) ^ 255 < 2 ^ 256 := by decide
          omega
        have htw : (data.drop loc).take 32 = word b.length := by
          have := take_of_At hw; rwa [length_word] at this
        simp only [readV, show (Encoding.Dynamic = Encoding.Static) = False by simp, ite_false,
          ite_true, wordAt]
        rw [if_neg (by omega), htw]
        simp only
        rw [wordVal_word _ hbl, if_neg (by omega), show loc + 32 + b.length - (loc + 32) = b.length by omega,
          take_of_At hcb]
    | @array t' l hl' =>
      cases hv with
      | @array _ vs hsame =>
        have hat' : At data loc (word (abiSame defs t' vs).length ++ encTuple (abiSame defs t' vs)) := by
          have := hat; simp only [abiOf] at this; rwa [enc_array] at this
        obtain ⟨hw, ht⟩ := At_append.mp hat'
        rw [length_word] at ht
        have hus := abiSame_length defs t' vs
        have hk32 : ∀ k (hk : k < vs.length),
            inlineSize l = some (sz (abiOf defs t' vs[k])) ∧ 32 ≤ (enc (abiOf defs t' vs[k])).length :=
          fun k hk => inlineSize_lay (sizeOf vs[k] + 1) (by omega) (HasSame.get hsame k hk) hl'
        have hcount : (abiSame defs t' vs).length < 2 ^ 256 := by
          have hc := headLen_ge_count (abiSame defs t' vs) (by
            intro u hu
            obtain ⟨k, hk', rfl⟩ := List.getElem_of_mem hu
            rw [abiSame_get]; exact (hk32 k (by omega)).2)
          have := encTuple_length_ge (abiSame defs t' vs)
          have := ht.bound
          have : (2 : Nat) ^ 255 < 2 ^ 256 := by decide
          omega
        have hwb : loc + 32 ≤ data.length := by
          have := hw.bound; simp only [length_word] at this; exact this
        have htw : (data.drop loc).take 32 = word (abiSame defs t' vs).length := by
          have := take_of_At hw; rwa [length_word] at this
        have hfl : l.height ≤ fuel := by
          have := TN.height_le_of_mem (c := l) (cs := [l]) (by simp)
          rw [TN.height_mk] at hf; omega
        simp only [readV, show (Encoding.Array = Encoding.Static) = False by simp,
          show (Encoding.Array = Encoding.Dynamic) = False by simp, ite_false, ite_true, wordAt]
        rw [if_neg (by omega), htw]
        simp only [List.length_singleton, ne_eq, not_true_eq_false, and_false, ite_false]
        rw [wordVal_word _ hcount]
        obtain ⟨h1, h2, h3⟩ := At_encTuple ht
        rw [readLoop_eq data hlen (readV data fuel) [l] true (loc + 32) (abiSame defs t' vs) vs 0 0
          (headLen (abiSame defs t' vs)) hus (by
            intro k hk hk'
            simp only [ite_true, List.getD_cons_zero]
            rw [abiSame_get]
            refine ⟨(hk32 k hk').1, (hk32 k hk').2, fun l' hl'' => ?_⟩
            exact readV_enc K defs data hlen fuel l' (HasSame.get hsame k hk') hl' hfl hl'') h1 h2 h3]
        rfl
    | @struct s ls hdef hls hne hth =>
      cases hv with
      | @struct _ vs _ hts =>
        have hat' : At data loc (encTuple (abiFields defs ((fieldsOf defs s).map (·.ty)) vs)) := by
          have := hat; simp only [abiOf] at this; rwa [enc_tuple] at this
        have hlv := HasTys.length hts
        have hll := LayL.length hls
        have hus := abiFields_length defs _ vs hlv
        have hkey : ∀ k (hk : k < vs.length),
            ls.getD k default ∈ ls ∧ ls.getD k default = ls[k]'(by omega) := by
          intro k hk
          have : ls.getD k default = ls[k]'(by omega) := by
            simp [List.getD_eq_getElem?_getD, show k < ls.length by omega]
          exact ⟨by rw [this]; exact List.getElem_mem _, this⟩
        simp only [readV, show (Encoding.Tuple = Encoding.Static) = False by simp,
          show (Encoding.Tuple = Encoding.Dynamic) = False by simp,
          show (Encoding.Tuple = Encoding.Array) = False by simp, ite_false, ite_true,
          Bool.false_eq_true, false_and]
        obtain ⟨h1, h2, h3⟩ := At_encTuple hat'
        rw [show ls.length = (abiFields defs ((fieldsOf defs s).map (·.ty)) vs).length by omega]
        rw [readLoop_eq data hlen (readV data fuel) ls false loc _ vs 0 0 _ hus (by
            intro k hk hk'
            simp only [Bool.false_eq_true, ite_false, Nat.zero_add]
            rw [abiFields_get defs _ vs hlv k hk]
            have hlk := LayL.get hls k (by omega)
            have hvk := HasTys.get hts k hk'
            have hsz := inlineSize_lay (sizeOf vs[k] + 1) (by omega) hvk hlk
            refine ⟨hsz.1, hsz.2, fun l' hl'' => ?_⟩
            have hfl : (ls.getD k default).height ≤ fuel := by
              have := TN.height_le_of_mem (hkey k hk').1
              rw [TN.height_mk] at hf; omega
            exact readV_enc K defs data hlen fuel l' hvk hlk hfl hl'') h1 h2 h3]
        rfl
    | @fixed t' m l hm hl' =>
      cases hv with
      | @fixed _ _ vs hlv hsame =>
        have hat' : At data loc (encTuple (abiSame defs t' vs)) := by
          have := hat; simp only [abiOf] at this; rwa [enc_tuple] at this
        have hus := abiSame_length defs t' vs
        have hfl : l.height ≤ fuel := by
          have := TN.height_le_of_mem (c := l) (cs := List.replicate m l) (by simp; omega)
          rw [TN.height_mk] at hf; omega
        simp only [readV, show (Encoding.Tuple = Encoding.Static) = False by simp,
          show (Encoding.Tuple = Encoding.Dynamic) = False by simp,
          show (Encoding.Tuple = Encoding.Array) = False by simp, ite_false, ite_true,
          Bool.false_eq_true, false_and, List.length_replicate]
        obtain ⟨h1, h2, h3⟩ := At_encTuple hat'
        have hloop := readLoop_eq data hlen (readV data fuel) (List.replicate m l) false loc _ vs 0 0 _ hus (by
            intro k hk hk'
            simp only [Bool.false_eq_true, ite_false, Nat.zero_add]
            have hg : (List.replicate m l).getD k default = l := by
              simp [List.getD_eq_getElem?_getD, show k < m by omega]
            rw [hg, abiSame_get]
            have hvk := HasSame.get hsame k hk'
            have hsz := inlineSize_lay (sizeOf vs[k] + 1) (by omega) hvk hl'
            exact ⟨hsz.1, hsz.2, fun l' hl'' => readV_enc K defs data hlen fuel l' hvk hl' hfl hl''⟩)
          h1 h2 h3
        rw [hus, hlv] at hloop
        rw [hloop]
        rfl

end EIP712
