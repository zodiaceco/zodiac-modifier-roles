import AbiLayerA.Decode

/-!
# Layer A: on correctly encoded calldata, Roles reads exactly the spec bytes

Setting: a condition tree `root` that describes a call (`Desc s root (.call
pre args)`, `RootOK root`), and calldata that is the spec encoding of it:
`pre ++ encTuple args ++ suffix` (`pre` the leading bytes, normally the
4-byte selector; `suffix` arbitrary trailing bytes).

Main results, for every node `d` the evaluator visits at location `l`
(`Reached`):

* `layerA_locations`: `d` sits exactly where the spec puts the encoding of
  the component it describes, reached by the same index path; or `d` is
  below a `Slice` and sits exactly at a window of that component's content;
  or `d` is non-structural; or (only if `s = true`) `d` is inside a
  bytes-like interpretation that need not hold, which itself sits exactly at
  the right `bytes` value.
* `layerA_input`: every comparison operand `__input` produces is exactly the
  spec encoding of that component (one word as is, otherwise the bytes that
  are keccak-hashed), or the selected window (right-aligned) below a
  `Slice`.
* `layerA_custom_operand`: `Custom` conditions get exactly the spec region.
* `layerA_children`, `layerA_slice`: no false rejections. Containers decode
  without overflow, one location per component; `Slice` rejects exactly
  when the window exceeds the value's content.
-/

namespace AbiLayerA
open Roles

theorem Val.sub_nil (u : Val) : u.sub [] = some u := by cases u <;> rfl

theorem Val.sub_tuple (vs : List Val) (i : Nat) (hi : i < vs.length) (p : List Nat) :
    (Val.tuple vs).sub (i :: p) = vs[i].sub p := by
  simp [Val.sub, hi]

theorem Val.sub_array (vs : List Val) (i : Nat) (hi : i < vs.length) (p : List Nat) :
    (Val.array vs).sub (i :: p) = vs[i].sub p := by
  simp [Val.sub, hi]

theorem Val.sub_call (pre : Bytes) (vs : List Val) (i : Nat) (hi : i < vs.length) (p : List Nat) :
    (Val.call pre vs).sub (i :: p) = vs[i].sub p := by
  simp [Val.sub, hi]

theorem annotate_op_of {c : Condition} {o : Operator} (h : (annotate c).operator = o)
    (ho : o ≠ .EqualTo) : c.operator = o := by
  rw [annotate_operator] at h
  split at h
  · exact absurd h.symm ho
  · exact h

theorem annotate_op_eq {c : Condition} {o : Operator} (h : c.operator = o)
    (ho : o ≠ .EqualToAvatar) : (annotate c).operator = o := by
  rw [annotate_operator, h]; simp [ho]

def IsCall (u : Val) : Prop := ∃ pre args, u = .call pre args

/-- A described node that is not a `Slice`, a call or a logical node has a
    plain value encoding. -/
theorem Desc.plain_encoding {s : Bool} {c : Condition} {u : Val} (hD : Desc s c u)
    (hop : (annotate c).operator ≠ .Slice ∧ (annotate c).operator ≠ .Matches ∧
      (annotate c).operator ≠ .Pass ∧ (annotate c).operator ≠ .And ∧
      (annotate c).operator ≠ .Or) :
    c.encoding ≠ .AbiEncoded ∧ c.encoding ≠ .None ∧ c.encoding ≠ .EtherValue := by
  match hD with
  | .word he _ _ _ | .bytes he _ _ _ | .tuple he _ _ _ | .array _ _ he _ _ _ _ _ =>
    rw [he]; decide
  | .sliceWord _ h _ _ _ _ _ | .sliceBytes _ h _ _ _ _ _ =>
    exact absurd (annotate_op_eq h (by decide)) hop.1
  | .call _ _ _ _ h =>
    rcases h with h | h
    · exact absurd (annotate_op_eq h (by decide)) hop.2.1
    · exact absurd (annotate_op_eq h (by decide)) hop.2.2.1
  | .logical _ _ h _ _ _ =>
    rcases h with h | h
    · exact absurd (annotate_op_eq h (by decide)) hop.2.2.2.1
    · exact absurd (annotate_op_eq h (by decide)) hop.2.2.2.2

/-! ## Non-structural nodes describe nothing and stay put -/

theorem NonStruct.not_bytesLike : ∀ {c}, NonStruct c → BytesLike c → False
  | _, .leaf he _ _, .dyn h => by rcases he with he | he <;> rw [he] at h <;> cases h
  | _, .leaf he _ _, .abi h => by rcases he with he | he <;> rw [he] at h <;> cases h
  | _, .leaf _ hch _, .logical _ _ _ hm0 _ _ => by rw [hch] at hm0; simp at hm0
  | _, .logical he _ _, .dyn h => by rw [he] at h; cases h
  | _, .logical he _ _, .abi h => by rw [he] at h; cases h
  | _, .logical _ _ hall, .logical ch0 _ _ hm0 h0 _ => NonStruct.not_bytesLike (hall ch0 hm0) h0

theorem NonStruct.not_desc {s : Bool} : ∀ {c u}, NonStruct c → Desc s c u → False
  | _, _, .leaf he _ _, .word h _ _ _ | _, _, .leaf he _ _, .sliceWord h _ _ _ _ _ _
  | _, _, .leaf he _ _, .bytes h _ _ _ | _, _, .leaf he _ _, .sliceBytes h _ _ _ _ _ _
  | _, _, .leaf he _ _, .tuple h _ _ _ | _, _, .leaf he _ _, .array _ _ h _ _ _ _ _
  | _, _, .leaf he _ _, .call h _ _ _ _ => by
    rcases he with he | he <;> rw [he] at h <;> cases h
  | _, _, .leaf _ hch _, .logical _ _ _ hm0 _ _ => by rw [hch] at hm0; simp at hm0
  | _, _, .logical he _ _, .word h _ _ _ | _, _, .logical he _ _, .sliceWord h _ _ _ _ _ _
  | _, _, .logical he _ _, .bytes h _ _ _ | _, _, .logical he _ _, .sliceBytes h _ _ _ _ _ _
  | _, _, .logical he _ _, .tuple h _ _ _ | _, _, .logical he _ _, .array _ _ h _ _ _ _ _
  | _, _, .logical he _ _, .call h _ _ _ _ => by rw [he] at h; cases h
  | _, _, .logical _ _ hall, .logical ch0 _ _ hm0 h0 _ =>
    match h0 with
    | .desc d => NonStruct.not_desc (hall ch0 hm0) d
    | .stray _ hb _ => NonStruct.not_bytesLike (hall ch0 hm0) hb

theorem NonStruct.not_descS {s : Bool} {c : Condition} {u : Val} (h : NonStruct c)
    (hd : DescS s c u) : False := by
  cases hd with
  | desc d => exact h.not_desc d
  | stray _ hb _ => exact h.not_bytesLike hb

theorem NonStruct.visit {data : Bytes} :
    ∀ {c' loc p d l}, Visit data c' loc p d l → ∀ {c}, c' = annotate c → NonStruct c →
    p = [] ∧ ∃ d0, d = annotate d0 ∧ NonStruct d0 := by
  intro c' loc p d l hv
  induction hv with
  | here => intro c hc hns; exact ⟨rfl, c, hc, hns⟩
  | logical ch hop hmem _ ih =>
    intro c hc hns
    subst hc
    cases hns with
    | leaf _ _ hnav =>
      rcases hop with h | h <;> (rw [annotate_op_of h (by decide)] at hnav; simp [isNavOp] at hnav)
    | logical _ _ hall =>
      rw [annotate_children] at hmem
      obtain ⟨ch0, hm0, rfl⟩ := List.mem_map.mp hmem
      exact ih rfl (hall ch0 hm0)
  | matchesChild _ _ _ hop | arrayTail _ _ _ hop | slice hop =>
    intro c hc hns; subst hc
    have := annotate_op_of hop (by decide)
    cases hns with
    | leaf _ _ hnav => rw [this] at hnav; simp [isNavOp] at hnav
    | logical _ hop' _ => rw [this] at hop'; simp at hop'
  | arrayIter _ _ _ hop =>
    intro c hc hns; subst hc
    cases hns with
    | leaf _ _ hnav =>
      rcases hop with h | h <;> (rw [annotate_op_of h (by decide)] at hnav; simp [isNavOp] at hnav)
    | logical _ hop' _ =>
      rcases hop with h | h <;> (rw [annotate_op_of h (by decide)] at hop'; simp at hop')

/-! ## Below a `Slice`: windows -/

theorem visit_win {data : Bytes} :
    ∀ {c' loc p d l}, Visit data c' loc p d l →
    ∀ {c bs}, c' = (annotate c).withSize bs.length → Win c → At data loc bs →
    1 ≤ bs.length → bs.length ≤ 32 →
    p = [] ∧ ∃ d0 bs', d = (annotate d0).withSize bs'.length ∧ Win d0 ∧ At data l bs' ∧
      1 ≤ bs'.length ∧ bs'.length ≤ 32 ∧ IsWindow bs' bs := by
  intro c' loc p d l hv
  induction hv with
  | here =>
    intro c bs hc hw hat h1 h32
    exact ⟨rfl, c, bs, hc, hw, hat, h1, h32, IsWindow.refl bs⟩
  | logical _ hop _ _ _ | arrayIter _ _ _ hop =>
    intro c bs hc hw _ _ _; subst hc
    rcases hop with h | h <;>
    · have := annotate_op_of h (by decide)
      cases hw with
      | leaf _ _ hnav => rw [this] at hnav; simp [isNavOp] at hnav
      | slice _ hop' _ _ _ _ => rw [this] at hop'; cases hop'
  | matchesChild _ _ _ hop | arrayTail _ _ _ hop =>
    intro c bs hc hw _ _ _; subst hc
    have := annotate_op_of hop (by decide)
    cases hw with
    | leaf _ _ hnav => rw [this] at hnav; simp [isNavOp] at hnav
    | slice _ hop' _ _ _ _ => rw [this] at hop'; cases hop'
  | slice hop _ hbound hvis ih =>
    intro c bs hc hw hat h1 h32; subst hc
    have hop0 := annotate_op_of hop (by decide)
    cases hw with
    | leaf _ _ hnav => rw [hop0] at hnav; simp [isNavOp] at hnav
    | slice _ _ hch hs1 hs32 hw' =>
      have hin := (Win.annotate_meta (Win.slice ‹_› hop0 hch hs1 hs32 hw')).1
      simp only [Condition.withSize_inlined, Condition.withSize_size,
        Condition.withSize_compValue, Condition.withSize_children, hin, ite_true,
        annotate_compValue, annotate_children, hch, List.map_cons, List.map_nil,
        List.headD_cons, Nat.add_zero] at hbound hvis ih
      have hwl := length_window hbound
      have hat' := At_window hat hbound
      obtain ⟨rfl, d0, bs', hd, hw0, hat0, h1', h32', hiw⟩ :=
        ih (bs := window bs _ _) (by rw [hwl]) hw' hat'
          (by rw [hwl]; exact hs1) (by rw [hwl]; exact hs32)
      exact ⟨rfl, d0, bs', hd, hw0, hat0, h1', h32', hiw.trans (IsWindow.window hbound)⟩

/-! ## What a visited node is -/

/-- Visited inside a bytes-like interpretation `ch` of the bytes value `us`,
    which sits correctly at `ls` (the interpretation itself need not hold). -/
def InStray (s : Bool) (data : Bytes) (u : Val) (p : List Nat) (d : Condition) (l : Nat) : Prop :=
  s = true ∧ ∃ p1 p2 ch us ls, p = p1 ++ p2 ∧ u.sub p1 = some us ∧ BytesLike ch ∧
    IsBytesLike us ∧ Placed data ls us ∧ Visit data (annotate ch) ls p2 d l

/-- The four possible outcomes for a node `d` visited at `l` along path `p`
    from a node describing `u`. -/
def Reached (s : Bool) (data : Bytes) (u : Val) (p : List Nat) (d : Condition) (l : Nat) : Prop :=
  -- describes component `u'` and sits at its spec encoding
  (∃ d0 u', d = annotate d0 ∧ u.sub p = some u' ∧ Desc s d0 u' ∧ Placed data l u' ∧
      (l = 0 → IsCall u' → RootOK d0)) ∨
  -- non-structural
  (∃ d0, d = annotate d0 ∧ NonStruct d0) ∨
  -- below a `Slice`: sits at a window of component `u'`'s content
  (∃ d0 bs u', d = (annotate d0).withSize bs.length ∧ Win d0 ∧ At data l bs ∧
      1 ≤ bs.length ∧ bs.length ≤ 32 ∧ u.sub p = some u' ∧ IsWindow bs (content u')) ∨
  -- inside an interpretation that need not hold (only with `s = true`)
  InStray s data u p d l

theorem Reached.lift {s : Bool} {data : Bytes} {u v : Val} {i : Nat}
    (hsub : ∀ q, u.sub (i :: q) = v.sub q) {p : List Nat} {d : Condition} {l : Nat}
    (h : Reached s data v p d l) : Reached s data u (i :: p) d l := by
  rcases h with ⟨d0, u', hd, hs, hD, hp, hr⟩ | hns | ⟨d0, bs, u', hd, hw, hat, h1, h32, hs, hiw⟩ |
    ⟨hst, p1, p2, ch, us, ls, rfl, hs, hb, hu, hp, hv⟩
  · exact Or.inl ⟨d0, u', hd, by rw [hsub]; exact hs, hD, hp, hr⟩
  · exact Or.inr (Or.inl hns)
  · exact Or.inr (Or.inr (Or.inl ⟨d0, bs, u', hd, hw, hat, h1, h32, by rw [hsub]; exact hs, hiw⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨hst, i :: p1, p2, ch, us, ls, rfl, by rw [hsub]; exact hs,
      hb, hu, hp, hv⟩))

/-- One structural step into child `ch` (component `v` of `u`). -/
theorem Reached.step {s : Bool} {data : Bytes} {u v : Val} {i : Nat}
    (hsub : ∀ q, u.sub (i :: q) = v.sub q) {ch : Condition} {lc : Nat} {p : List Nat}
    {d : Condition} {l : Nat} (hDS : DescS s ch v) (hp : Placed data lc v)
    (hvis : Visit data (annotate ch) lc p d l)
    (ih : Desc s ch v → Reached s data v p d l) : Reached s data u (i :: p) d l := by
  cases hDS with
  | desc hd => exact Reached.lift hsub (ih hd)
  | stray hst hb hu =>
    exact Or.inr (Or.inr (Or.inr ⟨hst, [i], p, ch, v, lc, rfl,
      by rw [hsub, Val.sub_nil], hb, hu, hp, hvis⟩))

theorem child_placed {data : Bytes} {l : Nat} {v : Val} {c : Condition}
    (h : At data l (enc v) ∧ (v.isStatic = false → 0 < l)) :
    Placed data l v ∧ (l = 0 → IsCall v → RootOK c) := by
  refine ⟨Placed.of_At h.1 (fun pre args he => h.2 (by subst he; rfl)), ?_⟩
  rintro hl ⟨pre, args, rfl⟩
  have := h.2 rfl; omega

/-- A node that cannot be a root sits at its full encoding. -/
theorem Placed.to_At_of_root {data : Bytes} {l : Nat} {u : Val} {c : Condition}
    (hp : Placed data l u) (hr : l = 0 → IsCall u → RootOK c)
    (hne1 : c.encoding ≠ .AbiEncoded) (hne2 : c.encoding ≠ .None) : At data l (enc u) := by
  apply Placed.to_At hp
  intro pre args he
  rcases Nat.eq_zero_or_pos l with h0 | h0
  · exfalso
    cases hr h0 ⟨pre, args, he⟩ with
    | abi h => exact hne1 h
    | logical h _ _ => exact hne2 h
  · exact h0

/-! ## Container children: one shared step -/

theorem matchesLoc_plain {c : Condition} (he : c.encoding = .Tuple ∨ c.encoding = .Array)
    (loc : Nat) :
    ((if loc > 0 ∧ (annotate c).encoding = .AbiEncoded then loc + 32 else loc) +
      (annotate c).leadingBytes) = loc := by
  rw [annotate_encoding, annotate_leadingBytes]
  rcases he with he | he <;> (rw [he]; simp)

/-- Nested calldata: the argument tuple starts after the length word (if any)
    and the leading bytes. -/
theorem call_args_At {data : Bytes} {c : Condition} {pre : Bytes} {args : List Val}
    {loc : Nat} (he : c.encoding = .AbiEncoded) (hL : c.leadingBytes = pre.length)
    (hp : Placed data loc (.call pre args)) :
    At data ((if loc > 0 ∧ (annotate c).encoding = .AbiEncoded then loc + 32 else loc) +
      (annotate c).leadingBytes) (encTuple args) := by
  rw [annotate_encoding, annotate_leadingBytes, he, hL]
  simp only [reduceCtorEq, ite_false, and_true, ite_true]
  rcases hp with ⟨h0, hat⟩ | ⟨hpos, hat⟩
  · subst h0
    simp only [Nat.lt_irrefl, ite_false, Nat.zero_add]
    simpa using (At_append.mp hat).2
  · rw [ite_eq_left hpos]
    rw [enc_call] at hat
    have h1 := At_content hat
    have h2 := (At_append.mp h1).2
    simpa [Nat.add_assoc] using h2

/-! ## Soundness of navigation -/

theorem visit_sound {data : Bytes} (hlen : data.length < 2 ^ 255) {s : Bool} :
    ∀ {c' loc p d l}, Visit data c' loc p d l →
    ∀ {c u}, c' = annotate c → Desc s c u → Placed data loc u →
      (loc = 0 → IsCall u → RootOK c) → Reached s data u p d l := by
  intro c' loc p d l hv
  induction hv with
  | here =>
    intro c u hc hD hp hr
    exact Or.inl ⟨c, u, hc, Val.sub_nil u, hD, hp, hr⟩
  | @logical _ loc p _ _ ch hop hmem hvis ih =>
    intro c u hc hD hp hr
    subst hc
    match hD with
    | .logical _ he _ _ _ hall =>
      rw [annotate_children] at hmem
      obtain ⟨ch0, hm0, rfl⟩ := List.mem_map.mp hmem
      cases hall ch0 hm0 with
      | ds hDS =>
        have hrch : loc = 0 → IsCall u → RootOK ch0 := by
          intro h0 hcall
          cases hr h0 hcall with
          | abi h => rw [he] at h; cases h
          | logical _ _ hk =>
            cases hk ch0 hm0 with
            | ok h => exact h
            | ns hns => exact (hns.not_descS hDS).elim
        cases hDS with
        | desc hd => exact ih rfl hd hp hrch
        | stray hst hb hu =>
          exact Or.inr (Or.inr (Or.inr ⟨hst, [], p, ch0, u, loc, rfl, Val.sub_nil u,
            hb, hu, hp, hvis⟩))
      | ns hns =>
        obtain ⟨rfl, d0, hd, hns'⟩ := NonStruct.visit hvis rfl hns
        exact Or.inr (Or.inl ⟨d0, hd, hns'⟩)
    | .word _ _ hnav _ | .bytes _ _ hnav _ =>
      rcases hop with h | h <;> (rw [annotate_op_of h (by decide)] at hnav; simp [isNavOp] at hnav)
    | .sliceWord _ hop' _ _ _ _ _ | .sliceBytes _ hop' _ _ _ _ _ =>
      rcases hop with h | h <;> (rw [annotate_op_of h (by decide)] at hop'; cases hop')
    | .tuple _ _ _ hnav | .array _ _ _ _ _ _ _ hnav =>
      rcases hop with h | h <;> (rw [annotate_op_of h (by decide)] at hnav; simp [isNavOp] at hnav)
    | .call _ _ _ _ hop' =>
      rcases hop with h | h <;> (rw [annotate_op_of h (by decide)] at hop'; simp at hop')
  | matchesChild locs i hi hop hch hcount hvis ih =>
    intro c u hc hD hp _
    subst hc
    have hop0 := annotate_op_of hop (by decide)
    match hD with
    | .tuple (vs := vs) he hne hall _ =>
      rw [matchesLoc_plain (.inl he)] at hch
      obtain ⟨locs', hl, hlen', hpl⟩ :=
        children_tuple hlen (by rw [annotate_encoding, he]; simp) hall
          (by simpa [Placed, enc_tuple] using hp)
      rw [hl] at hch; cases hch
      have hiv : i < vs.length := by omega
      have hic : i < c.children.length := by rw [DescAll.length_eq hall]; exact hiv
      have hgetD : (annotate c).children.getD i default = annotate c.children[i] := by
        rw [annotate_children]; simp [hic]
      rw [hgetD] at ih hvis
      have hpc := child_placed (c := c.children[i]) (hpl i hi hiv)
      exact Reached.step (fun q => Val.sub_tuple vs i hiv q) (DescAll.get hall i hic) hpc.1
        hvis (fun hd => ih rfl hd hpc.1 hpc.2)
    | .array (vs := vs) c0 cs he hcs h0 hpos _ _ =>
      rw [matchesLoc_plain (.inr he)] at hch
      obtain ⟨locs', hl, hlen', hpl⟩ :=
        children_array hlen (by rw [annotate_encoding, he]; simp) hcs h0
          (by simpa [Placed] using hp)
      rw [hl] at hch; cases hch
      have hiv : i < vs.length := by omega
      have hic : i < c.children.length := by
        rw [annotate_children] at hcount; simp at hcount; omega
      have hgetD : (annotate c).children.getD i default = annotate c.children[i] := by
        rw [annotate_children]; simp [hic]
      rw [hgetD] at ih hvis
      have hpc := child_placed (c := c.children[i]) (hpl i hi hiv)
      exact Reached.step (fun q => Val.sub_array vs i hiv q) (hpos i hic hiv) hpc.1
        hvis (fun hd => ih rfl hd hpc.1 hpc.2)
    | .call (pre := pre) (args := vs) he hL hne hall _ =>
      have hat := call_args_At he hL hp
      obtain ⟨locs', hl, hlen', hpl⟩ :=
        children_tuple hlen (by rw [annotate_encoding, he]; simp) hall hat
      rw [hl] at hch; cases hch
      have hiv : i < vs.length := by omega
      have hic : i < c.children.length := by rw [DescAll.length_eq hall]; exact hiv
      have hgetD : (annotate c).children.getD i default = annotate c.children[i] := by
        rw [annotate_children]; simp [hic]
      rw [hgetD] at ih hvis
      have hpc := child_placed (c := c.children[i]) (hpl i hi hiv)
      exact Reached.step (fun q => Val.sub_call pre vs i hiv q) (DescAll.get hall i hic) hpc.1
        hvis (fun hd => ih rfl hd hpc.1 hpc.2)
    | .word _ _ hnav _ | .bytes _ _ hnav _ => rw [hop0] at hnav; simp [isNavOp] at hnav
    | .sliceWord _ hop' _ _ _ _ _ | .sliceBytes _ hop' _ _ _ _ _ => rw [hop0] at hop'; cases hop'
    | .logical _ _ hop' _ _ _ => rw [hop0] at hop'; simp at hop'
  | arrayIter locs i hi hop hch hvis ih =>
    intro c u hc hD hp _
    subst hc
    match hD with
    | .array (vs := vs) c0 cs he hcs h0 _ _ _ =>
      obtain ⟨locs', hl, hlen', hpl⟩ :=
        children_array hlen (by rw [annotate_encoding, he]; simp) hcs h0
          (by simpa [Placed] using hp)
      rw [hl] at hch; cases hch
      have hiv : i < vs.length := by omega
      have hhead : (annotate c).children.headD default = annotate c0 := by
        rw [annotate_children, hcs]; rfl
      rw [hhead] at ih hvis
      have hpc := child_placed (c := c0) (hpl i hi hiv)
      exact Reached.step (fun q => Val.sub_array vs i hiv q) (h0 _ (List.getElem_mem hiv))
        hpc.1 hvis (fun hd => ih rfl hd hpc.1 hpc.2)
    | .word _ _ hnav _ | .bytes _ _ hnav _ | .tuple _ _ _ hnav =>
      rcases hop with h | h <;> (rw [annotate_op_of h (by decide)] at hnav; simp [isNavOp] at hnav)
    | .sliceWord _ hop' _ _ _ _ _ | .sliceBytes _ hop' _ _ _ _ _ =>
      rcases hop with h | h <;> (rw [annotate_op_of h (by decide)] at hop'; cases hop')
    | .call _ _ _ _ hop' =>
      rcases hop with h | h <;> (rw [annotate_op_of h (by decide)] at hop'; simp at hop')
    | .logical _ _ hop' _ _ _ =>
      rcases hop with h | h <;> (rw [annotate_op_of h (by decide)] at hop'; simp at hop')
  | arrayTail locs j hj hop hch hle hjc hvis ih =>
    intro c u hc hD hp _
    subst hc
    have hop0 := annotate_op_of hop (by decide)
    match hD with
    | .array (vs := vs) c0 cs he hcs h0 _ htail _ =>
      obtain ⟨locs', hl, hlen', hpl⟩ :=
        children_array hlen (by rw [annotate_encoding, he]; simp) hcs h0
          (by simpa [Placed] using hp)
      rw [hl] at hch; cases hch
      have hcl : (annotate c).children.length = c.children.length := by
        rw [annotate_children]; simp
      have hjv : locs.length - (annotate c).children.length + j < vs.length := by omega
      have hjc' : j < c.children.length := by omega
      have hk : c.children.length ≤ vs.length := by omega
      have hgetD : (annotate c).children.getD j default = annotate c.children[j] := by
        rw [annotate_children]; simp [hjc']
      rw [hgetD] at ih hvis
      have hidx : vs.length - c.children.length + j = locs.length - (annotate c).children.length + j := by
        omega
      have hpc := child_placed (c := c.children[j]) (hpl _ hj hjv)
      have hDS := htail j hjc' hk
      have hDS' : DescS s c.children[j] vs[locs.length - (annotate c).children.length + j] := by
        simpa only [hidx] using hDS
      exact Reached.step (fun q => Val.sub_array vs _ hjv q) hDS' hpc.1 hvis
        (fun hd => ih rfl hd hpc.1 hpc.2)
    | .word _ _ hnav _ | .bytes _ _ hnav _ => rw [hop0] at hnav; simp [isNavOp] at hnav
    | .sliceWord _ hop' _ _ _ _ _ | .sliceBytes _ hop' _ _ _ _ _ => rw [hop0] at hop'; cases hop'
    | .tuple _ _ _ hnav => rcases hnav with h | h <;> (rw [hop0] at h; simp [isNavOp] at h)
    | .call _ _ _ _ hop' => rw [hop0] at hop'; simp at hop'
    | .logical _ _ hop' _ _ _ => rw [hop0] at hop'; simp at hop'
  | @slice _ loc p _ _ hop hb hbound hvis _ =>
    intro c u hc hD hp hr
    subst hc
    have hop0 := annotate_op_of hop (by decide)
    match hD with
    | .sliceWord (w := w) he _ hch hs1 hs32 hw hw32 =>
      have hmeta := (Desc.sliceWord he hop0 hch hs1 hs32 hw hw32 (s := s)).annotate_meta
      have hat : At data loc w := by simpa [Placed, enc] using hp
      simp only [hmeta.1, hmeta.2, Val.isStatic, ite_true, enc, annotate_compValue, hw32]
        at hbound hvis
      rw [annotate_children, hch] at hvis
      simp only [List.map_cons, List.map_nil, List.headD_cons, Nat.add_zero] at hvis
      have hbound' : sliceShift c.compValue + sliceSize c.compValue ≤ w.length := by omega
      have hwl := length_window hbound'
      obtain ⟨rfl, d0, bs', hd, hw0, hat0, h1', h32', hiw⟩ :=
        visit_win hvis (c := _) (bs := window w _ _) (by rw [hwl]) hw (At_window hat hbound')
          (by rw [hwl]; exact hs1) (by rw [hwl]; exact hs32)
      exact Or.inr (Or.inr (Or.inl ⟨d0, bs', _, hd, hw0, hat0, h1', h32', Val.sub_nil _,
        by simpa [content] using hiw.trans (IsWindow.window hbound')⟩))
    | .sliceBytes (u := u) he _ hch hs1 hs32 hw hu =>
      have hmeta := (Desc.sliceBytes he hop0 hch hs1 hs32 hw hu (s := s)).annotate_meta
      have hat := Placed.to_At_of_root hp hr (by rw [he]; decide) (by rw [he]; decide)
      rw [enc_bytesLike hu] at hat
      have hbd := hat.bound
      rw [length_encBytes] at hbd
      have hcl : (content u).length < 2 ^ 256 := by
        have : (2 : Nat) ^ 255 < 2 ^ 256 := by decide
        have := ceil32_ge (content u).length
        omega
      have hload : load data loc = (content u).length := by
        unfold encBytes at hat; rw [List.append_assoc] at hat
        exact load_of_At_append hat hcl
      simp only [hmeta.1, isStatic_bytesLike hu, Bool.false_eq_true, ite_false,
        annotate_compValue, hload] at hbound hvis
      rw [annotate_children, hch] at hvis
      simp only [List.map_cons, List.map_nil, List.headD_cons] at hvis
      have hwl := length_window hbound
      obtain ⟨rfl, d0, bs', hd, hw0, hat0, h1', h32', hiw⟩ :=
        visit_win hvis (c := _) (bs := window (content u) _ _) (by rw [hwl]) hw
          (At_window (At_content hat) hbound) (by rw [hwl]; exact hs1) (by rw [hwl]; exact hs32)
      exact Or.inr (Or.inr (Or.inl ⟨d0, bs', u, hd, hw0, hat0, h1', h32', Val.sub_nil u,
        hiw.trans (IsWindow.window hbound)⟩))
    | .word _ _ hnav _ | .bytes _ _ hnav _ => rw [hop0] at hnav; simp [isNavOp] at hnav
    | .tuple _ _ _ hnav => rcases hnav with h | h <;> (rw [hop0] at h; simp [isNavOp] at h)
    | .array _ _ _ _ _ _ _ hnav =>
      rcases hnav with h | h | h | h | h <;> (rw [hop0] at h; simp [isNavOp] at h)
    | .call _ _ _ _ hop' => rw [hop0] at hop'; simp at hop'
    | .logical _ _ hop' _ _ _ => rw [hop0] at hop'; simp at hop'

/-! ## `__input` -/

theorem Desc.input_eq {data : Bytes} (hlen : data.length < 2 ^ 255) {s : Bool} {c : Condition}
    {u : Val} {l : Nat} (hD : Desc s c u) (hat : At data l (enc u))
    (hne : (annotate c).encoding ≠ .None) :
    input data l (annotate c) = expectInput (enc u) := by
  have hmeta := hD.annotate_meta
  have hge := hD.enc_ge
  have hb := hat.bound
  have hsize : (if (annotate c).size ≠ 0 then (annotate c).size
      else Roles.size data l (annotate c)) = (enc u).length := by
    rw [hmeta.2]
    cases hs : u.isStatic
    · simp only [Bool.false_eq_true, ite_false]
      simp [Desc.size_eq hlen hD hat]
    · simp only [ite_true]
      rw [ite_eq_left (by omega)]
  unfold input
  rw [ite_eq_right hne]
  dsimp only
  rw [hsize, ite_eq_right (by omega)]
  unfold expectInput
  by_cases h32 : (enc u).length = 32
  · rw [ite_eq_left h32, ite_eq_left h32]
    congr 1
    unfold load
    rw [List.take_append_of_le_length (by simp; omega), ← h32, take_of_At hat]
  · rw [ite_eq_right h32, ite_eq_right h32, ite_eq_right (by omega), take_of_At hat]

/-- Below a `Slice`: the operand is the window, right-aligned in a word. -/
theorem Win.input_eq {data : Bytes} {c : Condition} {bs : Bytes} {l : Nat} (hw : Win c)
    (hat : At data l bs) (h1 : 1 ≤ bs.length) (h32 : bs.length ≤ 32) :
    input data l ((annotate c).withSize bs.length) = .word (wordVal bs) := by
  have he : c.encoding = .Static := by cases hw <;> assumption
  have hb := hat.bound
  have hne : ((annotate c).withSize bs.length).encoding ≠ .None := by
    rw [Condition.withSize_encoding, annotate_encoding, he]; decide
  have hsize : (if ((annotate c).withSize bs.length).size ≠ 0
      then ((annotate c).withSize bs.length).size
      else Roles.size data l ((annotate c).withSize bs.length)) = bs.length := by
    have h0 : bs.length ≠ 0 := by omega
    simp [h0]
  unfold input
  rw [ite_eq_right hne]
  dsimp only
  rw [hsize, ite_eq_right (by omega)]
  by_cases h : bs.length = 32
  · rw [ite_eq_left h]
    congr 1
    unfold load
    rw [List.take_append_of_le_length (by simp; omega), ← h, take_of_At hat]
  · rw [ite_eq_right h, ite_eq_left (by omega), take_of_At hat]

/-! ## Top-level statements -/

section Top

variable (root : Condition) (pre : Bytes) (args : List Val) (suffix : Bytes)

/-- Calldata: the leading bytes, the spec encoding of the arguments, and any
    trailing bytes. -/
def calldata : Bytes := pre ++ encTuple args ++ suffix

theorem root_placed : Placed (calldata pre args suffix) 0 (.call pre args) := by
  refine Or.inl ⟨rfl, ?_, ?_⟩
  · simp only [calldata, List.drop_zero]
    exact List.take_left' rfl
  · simp [calldata]

/-- **Locations.** Every node the evaluator visits is one of the four cases of
    `Reached`: at the spec encoding of the component it describes (same index
    path), at a window of that component's content (below `Slice`),
    non-structural, or inside a bytes-like interpretation that need not hold
    (only with `s = true`). -/
theorem layerA_locations {s : Bool}
    (hD : Desc s root (.call pre args)) (hR : RootOK root)
    (hlen : (calldata pre args suffix).length < 2 ^ 255)
    {p : List Nat} {d : Condition} {l : Nat}
    (hv : Visit (calldata pre args suffix) (annotate root) 0 p d l) :
    Reached s (calldata pre args suffix) (.call pre args) p d l :=
  visit_sound hlen hv rfl hD (root_placed pre args suffix) (fun _ _ => hR)

/-- With `s = false` (every interpretation holds) the fourth case is
    impossible. -/
theorem InStray.strict {data : Bytes} {u : Val} {p : List Nat} {d : Condition} {l : Nat} :
    ¬ InStray false data u p d l := fun h => Bool.false_ne_true h.1

/-- **Comparison operands.** For every visited node whose operator calls
    `__input` (`EqualTo`, `GreaterThan`, `LessThan`, signed comparisons,
    `WithinAllowance`, `Pluck`): the operand is exactly the spec encoding of
    the described component (one word as is, longer encodings as the bytes
    that are keccak-hashed); or below a `Slice`, exactly a window of the
    component's content, right-aligned; or the ether value
    (`EtherValue` nodes); or the node is inside an interpretation that need
    not hold (only with `s = true`). -/
theorem layerA_input {s : Bool}
    (hD : Desc s root (.call pre args)) (hR : RootOK root)
    (hlen : (calldata pre args suffix).length < 2 ^ 255)
    {p : List Nat} {d : Condition} {l : Nat}
    (hv : Visit (calldata pre args suffix) (annotate root) 0 p d l)
    (hop : readsInput d.operator = true) :
    (∃ u, (Val.call pre args).sub p = some u ∧
      input (calldata pre args suffix) l d = expectInput (enc u)) ∨
    (∃ u bs, (Val.call pre args).sub p = some u ∧ IsWindow bs (content u) ∧
      input (calldata pre args suffix) l d = .word (wordVal bs)) ∨
    input (calldata pre args suffix) l d = .etherValue ∨
    InStray s (calldata pre args suffix) (.call pre args) p d l := by
  have hlen' := hlen
  rcases layerA_locations root pre args suffix hD hR hlen hv with
    ⟨d0, u, rfl, hsub, hD0, hp, hr⟩ | ⟨d0, rfl, hns⟩ |
    ⟨d0, bs, u, rfl, hw, hat, h1, h32, hsub, hiw⟩ | hst
  · left
    refine ⟨u, hsub, ?_⟩
    have henc := hD0.plain_encoding (by
      refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> intro h <;> rw [h] at hop <;> simp [readsInput] at hop)
    exact Desc.input_eq hlen hD0 (Placed.to_At_of_root hp hr henc.1 henc.2.1)
      (by rw [annotate_encoding, ite_eq_right henc.2.2]; exact henc.2.1)
  · right; right; left
    unfold input
    rw [annotate_encoding]
    cases hns with
    | leaf he _ _ => rcases he with he | he <;> simp [he]
    | logical he _ _ => simp [he]
  · right; left
    exact ⟨u, bs, hsub, hiw, Win.input_eq hw hat h1 h32⟩
  · right; right; right; exact hst

/-- **Custom conditions.** `Custom` receives `(location, size)`: exactly the
    position and length of the spec encoding of the described component, or
    of the window below a `Slice`. -/
theorem layerA_custom_operand {s : Bool}
    (hD : Desc s root (.call pre args)) (hR : RootOK root)
    (hlen : (calldata pre args suffix).length < 2 ^ 255)
    {p : List Nat} {d : Condition} {l : Nat}
    (hv : Visit (calldata pre args suffix) (annotate root) 0 p d l)
    (hop : d.operator = .Custom) :
    (∃ u, (Val.call pre args).sub p = some u ∧ At (calldata pre args suffix) l (enc u) ∧
      (if d.size ≠ 0 then d.size else Roles.size (calldata pre args suffix) l d) =
        (enc u).length) ∨
    (∃ u bs, (Val.call pre args).sub p = some u ∧ IsWindow bs (content u) ∧
      At (calldata pre args suffix) l bs ∧
      (if d.size ≠ 0 then d.size else Roles.size (calldata pre args suffix) l d) = bs.length) ∨
    (∃ d0, d = annotate d0 ∧ NonStruct d0) ∨
    InStray s (calldata pre args suffix) (.call pre args) p d l := by
  rcases layerA_locations root pre args suffix hD hR hlen hv with
    ⟨d0, u, rfl, hsub, hD0, hp, hr⟩ | hns |
    ⟨d0, bs, u, rfl, hw, hat, h1, h32, hsub, hiw⟩ | hst
  · left
    refine ⟨u, hsub, ?_⟩
    have henc := hD0.plain_encoding (by
      refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> intro h <;> rw [h] at hop <;> cases hop)
    have key : At (calldata pre args suffix) l (enc u) :=
      Placed.to_At_of_root hp hr henc.1 henc.2.1
    refine ⟨key, ?_⟩
    have hmeta := hD0.annotate_meta
    have hge := hD0.enc_ge
    rw [hmeta.2]
    cases hs : u.isStatic
    · simp only [Bool.false_eq_true, ite_false]
      simp [Desc.size_eq hlen hD0 key]
    · simp only [ite_true]
      rw [ite_eq_left (by omega)]
  · right; right; left; exact hns
  · right; left
    refine ⟨u, bs, hsub, hiw, hat, ?_⟩
    have h0 : bs.length ≠ 0 := by omega
    simp [h0]
  · right; right; right; exact hst

/-- Components of a container value (tuple fields, array elements, call
    arguments). -/
def Val.components : Val → List Val
  | .tuple vs => vs
  | .array vs => vs
  | .call _ vs => vs
  | _ => []

theorem Desc.children_ok {data : Bytes} (hlen : data.length < 2 ^ 255) {s : Bool}
    {c : Condition} {u : Val} {loc : Nat} (hD : Desc s c u) (hp : Placed data loc u)
    (hcont : c.encoding = .Tuple ∨ c.encoding = .Array ∨ c.encoding = .AbiEncoded) :
    ∃ locs, children data
      ((if loc > 0 ∧ (annotate c).encoding = .AbiEncoded then loc + 32 else loc) +
        (annotate c).leadingBytes) (annotate c) = some locs ∧
      locs.length = u.components.length := by
  match hD with
  | .tuple he _ hall _ =>
    rw [matchesLoc_plain (.inl he)]
    obtain ⟨locs, hl, hlen', _⟩ := children_tuple hlen (by rw [annotate_encoding, he]; simp)
      hall (by simpa [Placed, enc_tuple] using hp)
    exact ⟨locs, hl, hlen'⟩
  | .array c0 _ he hcs h0 _ _ _ =>
    rw [matchesLoc_plain (.inr he)]
    obtain ⟨locs, hl, hlen', _⟩ := children_array hlen (by rw [annotate_encoding, he]; simp)
      hcs h0 (by simpa [Placed] using hp)
    exact ⟨locs, hl, hlen'⟩
  | .call he hL _ hall _ =>
    obtain ⟨locs, hl, hlen', _⟩ := children_tuple hlen (by rw [annotate_encoding, he]; simp)
      hall (call_args_At he hL hp)
    exact ⟨locs, hl, hlen'⟩
  | .word he _ _ _ | .bytes he _ _ _ | .sliceWord he _ _ _ _ _ _ | .sliceBytes he _ _ _ _ _ _
  | .logical _ he _ _ _ _ =>
    rcases hcont with h | h | h <;> rw [he] at h <;> cases h

/-- **No false rejections: containers.** Every visited container decodes its
    children without overflow, one location per component. -/
theorem layerA_children {s : Bool}
    (hD : Desc s root (.call pre args)) (hR : RootOK root)
    (hlen : (calldata pre args suffix).length < 2 ^ 255)
    {p : List Nat} {d : Condition} {l : Nat}
    (hv : Visit (calldata pre args suffix) (annotate root) 0 p d l)
    (hcont : d.encoding = .Tuple ∨ d.encoding = .Array ∨ d.encoding = .AbiEncoded) :
    (∃ u, (Val.call pre args).sub p = some u ∧
      ∃ locs, children (calldata pre args suffix)
        ((if l > 0 ∧ d.encoding = .AbiEncoded then l + 32 else l) + d.leadingBytes) d =
          some locs ∧ locs.length = u.components.length) ∨
    InStray s (calldata pre args suffix) (.call pre args) p d l := by
  rcases layerA_locations root pre args suffix hD hR hlen hv with
    ⟨d0, u, rfl, hsub, hD0, hp, _⟩ | ⟨d0, rfl, hns⟩ | ⟨d0, bs, u, rfl, hw, _⟩ | hst
  · left
    refine ⟨u, hsub, hD0.children_ok hlen hp ?_⟩
    rw [annotate_encoding] at hcont
    split at hcont
    · rcases hcont with h | h | h <;> cases h
    · exact hcont
  · exfalso
    rw [annotate_encoding] at hcont
    cases hns with
    | leaf he _ _ => rcases he with he | he <;> simp [he] at hcont
    | logical he _ _ => simp [he] at hcont
  · exfalso
    have he : d0.encoding = .Static := by cases hw <;> assumption
    rw [Condition.withSize_encoding, annotate_encoding, he] at hcont
    rcases hcont with h | h | h <;> cases h
  · right; exact hst

theorem Desc.slice_facts {s : Bool} {c : Condition} {u : Val} (hD : Desc s c u)
    (hop : (annotate c).operator = .Slice) :
    (c.encoding = .Static ∧ ∃ w, u = .word w ∧ w.length = 32) ∨
    (c.encoding = .Dynamic ∧ IsBytesLike u) := by
  have hop0 := annotate_op_of hop (by decide)
  match hD with
  | .sliceWord he _ _ _ _ _ hw => exact Or.inl ⟨he, _, rfl, hw⟩
  | .sliceBytes he _ _ _ _ _ hu => exact Or.inr ⟨he, hu⟩
  | .word _ _ hnav _ | .bytes _ _ hnav _ => rw [hop0] at hnav; simp [isNavOp] at hnav
  | .tuple _ _ _ hnav => rcases hnav with h | h <;> (rw [hop0] at h; simp [isNavOp] at h)
  | .array _ _ _ _ _ _ _ hnav =>
    rcases hnav with h | h | h | h | h <;> (rw [hop0] at h; simp [isNavOp] at h)
  | .call _ _ _ _ hop' => rw [hop0] at hop'; simp at hop'
  | .logical _ _ hop' _ _ _ => rw [hop0] at hop'; simp at hop'

/-- The length `_slice` checks against, for a `Slice` node describing `u`. -/
theorem Desc.slice_length {data : Bytes} {s : Bool} {d0 : Condition} {l : Nat}
    (hop : (annotate d0).operator = .Slice)
    {u : Val} (hD0 : Desc s d0 u)
    (hp : Placed data l u) (hr : l = 0 → IsCall u → RootOK d0)
    (hlen : data.length < 2 ^ 255) :
    ((annotate d0).inlined = false → l + 32 ≤ data.length) ∧
    (if (annotate d0).inlined then (annotate d0).size else load data l) = (content u).length := by
  have hmeta := hD0.annotate_meta
  rcases hD0.slice_facts hop with ⟨he, w, rfl, hw32⟩ | ⟨he, hu⟩
  · simp [hmeta.1, hmeta.2, Val.isStatic, enc, content, hw32]
  · have hat := Placed.to_At_of_root hp hr (by rw [he]; decide) (by rw [he]; decide)
    rw [enc_bytesLike hu] at hat
    have hbd := hat.bound
    rw [length_encBytes] at hbd
    have hcl : (content u).length < 2 ^ 256 := by
      have : (2 : Nat) ^ 255 < 2 ^ 256 := by decide
      have := ceil32_ge (content u).length
      omega
    have hload : load data l = (content u).length := by
      unfold encBytes at hat; rw [List.append_assoc] at hat
      exact load_of_At_append hat hcl
    simp only [hmeta.1, isStatic_bytesLike hu, Bool.false_eq_true, ite_false, hload]
    exact ⟨fun _ => by omega, trivial⟩

/-- **No false rejections: `Slice`.** For every visited `Slice` node, the
    length `_slice` checks `shift + size` against is exactly the length of
    the bytes the spec window is taken from: the component's content, or
    (for a nested `Slice`) the enclosing window. So a slice is rejected
    exactly when the spec window does not exist. -/
theorem layerA_slice {s : Bool}
    (hD : Desc s root (.call pre args)) (hR : RootOK root)
    (hlen : (calldata pre args suffix).length < 2 ^ 255)
    {p : List Nat} {d : Condition} {l : Nat}
    (hv : Visit (calldata pre args suffix) (annotate root) 0 p d l)
    (hop : d.operator = .Slice) :
    (∃ u, (Val.call pre args).sub p = some u ∧
      (d.inlined = false → l + 32 ≤ (calldata pre args suffix).length) ∧
      (if d.inlined then d.size else load (calldata pre args suffix) l) = (content u).length) ∨
    (∃ u bs, (Val.call pre args).sub p = some u ∧ IsWindow bs (content u) ∧
      At (calldata pre args suffix) l bs ∧ d.inlined = true ∧ d.size = bs.length) ∨
    InStray s (calldata pre args suffix) (.call pre args) p d l := by
  rcases layerA_locations root pre args suffix hD hR hlen hv with
    ⟨d0, u, rfl, hsub, hD0, hp, hr⟩ | ⟨d0, rfl, hns⟩ |
    ⟨d0, bs, u, rfl, hw, hat, _, _, hsub, hiw⟩ | hst
  · exact Or.inl ⟨u, hsub, Desc.slice_length hop hD0 hp hr hlen⟩
  · exfalso
    have := annotate_op_of hop (by decide)
    cases hns with
    | leaf _ _ hnav => rw [this] at hnav; simp [isNavOp] at hnav
    | logical _ hop' _ => rw [this] at hop'; simp at hop'
  · exact Or.inr (Or.inl ⟨u, bs, hsub, hiw, hat, (Win.annotate_meta hw).1, rfl⟩)
  · exact Or.inr (Or.inr hst)

end Top

end AbiLayerA
