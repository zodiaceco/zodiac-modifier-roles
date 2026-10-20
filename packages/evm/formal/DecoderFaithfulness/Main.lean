import DecoderFaithfulness.Decode

/-!
# Decoder faithfulness: on correctly encoded calldata, Roles reads exactly the spec bytes

Setting: a condition tree `root` that describes a call (`Desc s root (.call
pre args)`, `RootOK root`), and calldata that is the spec encoding of it:
`pre ++ encTuple args ++ suffix` (`pre` the leading bytes, normally the
4-byte selector; `suffix` arbitrary trailing bytes).

Main results, for every node `d` the evaluator visits at location `l`
(`Reached`):

* `decoder_locations`: `d` sits exactly where the spec puts the encoding of
  the component it describes, reached by the same index path; or `d` is
  below a `Slice` and sits exactly at a window of that component's content;
  or `d` is non-structural; or (only if `s = true`) `d` is inside a
  bytes-like interpretation that need not hold, which itself sits exactly at
  the right `bytes` value.
* `decoder_input`: every comparison operand `__input` produces is exactly the
  spec encoding of that component (one word as is, otherwise the bytes that
  are keccak-hashed), or the selected window (right-aligned) below a
  `Slice`.
* `decoder_custom_operand`: `Custom` conditions get exactly the spec region.
* `decoder_children`, `decoder_slice`: no false rejections. Containers decode
  without overflow, one location per component; `Slice` rejects exactly
  when the window exceeds the value's content.
-/

namespace DecoderFaithfulness
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
  | .logical _ _ h _ _ _ _ =>
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
  | _, _, .leaf _ hch _, .logical _ _ _ hm0 _ _ _ => by rw [hch] at hm0; simp at hm0
  | _, _, .logical he _ _, .word h _ _ _ | _, _, .logical he _ _, .sliceWord h _ _ _ _ _ _
  | _, _, .logical he _ _, .bytes h _ _ _ | _, _, .logical he _ _, .sliceBytes h _ _ _ _ _ _
  | _, _, .logical he _ _, .tuple h _ _ _ | _, _, .logical he _ _, .array _ _ h _ _ _ _ _
  | _, _, .logical he _ _, .call h _ _ _ _ => by rw [he] at h; cases h
  | _, _, .logical _ _ hall, .logical ch0 _ _ hm0 h0 _ _ =>
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

theorem Sub.trans {a b c : Condition} (hab : Sub a b) (hbc : Sub b c) : Sub a c := by
  induction hbc with
  | refl => exact hab
  | child hm _ ih => exact .child hm ih

theorem Sub.mem {ch c : Condition} (h : ch ∈ c.children) : Sub ch c := .child h (.refl ch)

theorem Val.sub_append {u v : Val} : ∀ {p : List Nat}, u.sub p = some v →
    ∀ q, u.sub (p ++ q) = v.sub q := by
  intro p
  induction p generalizing u with
  | nil => intro h q; rw [Val.sub_nil] at h; cases h; rfl
  | cons i p ih =>
    intro h q
    cases u with
    | tuple vs | array vs | call _ vs =>
      simp only [Val.sub, List.cons_append] at h ⊢
      split at h
      · exact ih h q
      · cases h
    | word | bytes => simp [Val.sub] at h

/-- Reached from `c` at `loc` by navigation: `Visit`, and Zip jumps over
    arrays plucked at nodes reached this way. -/
inductive Below (data : Bytes) (c : Condition) (loc : Nat) : List Nat → Condition → Nat → Prop
  | visit {p d l} : Visit data c loc p d l → Below data c loc p d l
  | zip {pp pk L field locs i p d l} (hi : i < locs.length) :
      Below data c loc pp pk L → pk.operator = .Pluck →
      children data L (zipStub field) = some locs →
      Visit data field locs[i] p d l → Below data c loc (pp ++ i :: p) d l

/-- Reached inside a bytes-like interpretation `ch` of the bytes value `us`,
    which sits correctly at `ls` (the interpretation itself need not hold). -/
def InStray (s : Bool) (data : Bytes) (u : Val) (p : List Nat) (d : Condition) (l : Nat) : Prop :=
  s = true ∧ ∃ p1 p2 ch us ls, p = p1 ++ p2 ∧ u.sub p1 = some us ∧ BytesLike ch ∧
    IsBytesLike us ∧ Placed data ls us ∧ Below data (annotate ch) ls p2 d l

/-- The four possible outcomes for a node `d` reached at `l` along path `p`
    from the node `top`, which describes `u`. -/
def Reached (s : Bool) (data : Bytes) (top : Condition) (u : Val) (p : List Nat) (d : Condition)
    (l : Nat) : Prop :=
  -- a node of `top` that describes component `u'` and sits at its spec encoding
  (∃ d0 u', Sub d0 top ∧ d = annotate d0 ∧ u.sub p = some u' ∧ Desc s d0 u' ∧
      Placed data l u' ∧ (l = 0 → IsCall u' → RootOK d0)) ∨
  -- non-structural (a Zip reads no calldata at its own location)
  (∃ d0, d = annotate d0 ∧ (NonStruct d0 ∨ ZipNode d0)) ∨
  -- below a `Slice`: sits at a window of component `u'`'s content
  (∃ d0 bs u', d = (annotate d0).withSize bs.length ∧ Win d0 ∧ At data l bs ∧
      1 ≤ bs.length ∧ bs.length ≤ 32 ∧ u.sub p = some u' ∧ IsWindow bs (content u')) ∨
  -- inside an interpretation that need not hold (only with `s = true`)
  InStray s data u p d l

/-- From a node `top` describing component `v` (at path `P` of `u`) to a node
    `top'` containing it. -/
theorem Reached.lift {s : Bool} {data : Bytes} {u v : Val} {P : List Nat}
    (hsub : ∀ q, u.sub (P ++ q) = v.sub q) {top top' : Condition} (htop : Sub top top')
    {p : List Nat} {d : Condition} {l : Nat}
    (h : Reached s data top v p d l) : Reached s data top' u (P ++ p) d l := by
  rcases h with ⟨d0, u', hst0, hd, hs, hD, hp, hr⟩ | hns |
    ⟨d0, bs, u', hd, hw, hat, h1, h32, hs, hiw⟩ |
    ⟨hst, p1, p2, ch, us, ls, rfl, hs, hb, hu, hp, hv⟩
  · exact Or.inl ⟨d0, u', hst0.trans htop, hd, by rw [hsub]; exact hs, hD, hp, hr⟩
  · exact Or.inr (Or.inl hns)
  · exact Or.inr (Or.inr (Or.inl ⟨d0, bs, u', hd, hw, hat, h1, h32, by rw [hsub]; exact hs, hiw⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨hst, P ++ p1, p2, ch, us, ls, by rw [List.append_assoc],
      by rw [hsub]; exact hs, hb, hu, hp, hv⟩))

/-- One structural step into node `ch` of `top` (component `v`, at path `P`
    of `u`). -/
theorem Reached.stepP {s : Bool} {data : Bytes} {u v : Val} {P : List Nat}
    (hsub : ∀ q, u.sub (P ++ q) = v.sub q) {ch top : Condition} (htop : Sub ch top) {lc : Nat}
    {p : List Nat} {d : Condition} {l : Nat} (hDS : DescS s ch v) (hp : Placed data lc v)
    (hvis : Visit data (annotate ch) lc p d l)
    (ih : Desc s ch v → Reached s data ch v p d l) : Reached s data top u (P ++ p) d l := by
  cases hDS with
  | desc hd => exact Reached.lift hsub htop (ih hd)
  | stray hst hb hu =>
    exact Or.inr (Or.inr (Or.inr ⟨hst, P, p, ch, v, lc, rfl,
      by rw [← List.append_nil P, hsub, Val.sub_nil], hb, hu, hp, .visit hvis⟩))

/-- One structural step into child `ch` of `top` (component `v` of `u`). -/
theorem Reached.step {s : Bool} {data : Bytes} {u v : Val} {i : Nat}
    (hsub : ∀ q, u.sub (i :: q) = v.sub q) {ch top : Condition} (hmem : ch ∈ top.children)
    {lc : Nat} {p : List Nat}
    {d : Condition} {l : Nat} (hDS : DescS s ch v) (hp : Placed data lc v)
    (hvis : Visit data (annotate ch) lc p d l)
    (ih : Desc s ch v → Reached s data ch v p d l) : Reached s data top u (i :: p) d l :=
  Reached.stepP (P := [i]) hsub (Sub.mem hmem) hDS hp hvis ih

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

theorem ZipNode.not_descS {s : Bool} {c : Condition} {u : Val} (hz : ZipNode c)
    (hd : DescS s c u) : False := by
  obtain ⟨_, he, hop, _⟩ := hz
  cases hd with
  | desc d =>
    cases d with
    | word h _ _ _ | bytes h _ _ _ | sliceWord h _ _ _ _ _ _ | sliceBytes h _ _ _ _ _ _
    | tuple h _ _ _ | array _ _ h _ _ _ _ _ | call h _ _ _ _ => rw [he] at h; cases h
    | logical _ _ h _ _ _ _ =>
      rcases hop with h' | h' <;> rcases h with h | h <;> rw [h'] at h <;> cases h
  | stray _ hb _ =>
    cases hb with
    | dyn h | abi h => rw [he] at h; cases h
    | logical _ _ h _ _ _ =>
      rcases hop with h' | h' <;> rcases h with h | h <;> rw [h'] at h <;> cases h

/-- A Zip node only reaches itself by `Visit` (its fields are evaluated by
    the Zip jump of `Eval`). -/
theorem ZipNode.visit {data : Bytes} {c0 : Condition} (hz : ZipNode c0) :
    ∀ {c' loc p d l}, Visit data c' loc p d l → c' = annotate c0 → p = [] ∧ d = c' := by
  obtain ⟨_, _, hop, _⟩ := hz
  intro c' loc p d l hv hc
  cases hv with
  | here => exact ⟨rfl, rfl⟩
  | logical _ h _ _ | arrayIter _ _ _ h _ _ =>
    subst hc
    rcases hop with h' | h' <;> rcases h with h | h <;>
      (rw [annotate_op_eq h' (by decide)] at h; cases h)
  | matchesChild _ _ _ h _ _ _ | arrayTail _ _ _ h _ _ _ _ | slice h _ _ _ =>
    subst hc
    rcases hop with h' | h' <;> (rw [annotate_op_eq h' (by decide)] at h; cases h)

theorem visit_sound {data : Bytes} (hlen : data.length < 2 ^ 255) {s : Bool} :
    ∀ {c' loc p d l}, Visit data c' loc p d l →
    ∀ {c u}, c' = annotate c → Desc s c u → Placed data loc u →
      (loc = 0 → IsCall u → RootOK c) → Reached s data c u p d l := by
  intro c' loc p d l hv
  induction hv with
  | here =>
    intro c u hc hD hp hr
    exact Or.inl ⟨c, u, .refl c, hc, Val.sub_nil u, hD, hp, hr⟩
  | @logical _ loc p _ _ ch hop hmem hvis ih =>
    intro c u hc hD hp hr
    subst hc
    match hD with
    | .logical _ he _ _ _ hall _ =>
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
            | zip hz => exact (hz.not_descS hDS).elim
        cases hDS with
        | desc hd => exact Reached.lift (P := []) (fun _ => rfl) (Sub.mem hm0) (ih rfl hd hp hrch)
        | stray hst hb hu =>
          exact Or.inr (Or.inr (Or.inr ⟨hst, [], p, ch0, u, loc, rfl, Val.sub_nil u,
            hb, hu, hp, .visit hvis⟩))
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
      exact Reached.step (fun q => Val.sub_tuple vs i hiv q) (List.getElem_mem hic)
        (DescAll.get hall i hic) hpc.1 hvis (fun hd => ih rfl hd hpc.1 hpc.2)
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
      exact Reached.step (fun q => Val.sub_array vs i hiv q) (List.getElem_mem hic)
        (hpos i hic hiv) hpc.1 hvis (fun hd => ih rfl hd hpc.1 hpc.2)
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
      exact Reached.step (fun q => Val.sub_call pre vs i hiv q) (List.getElem_mem hic)
        (DescAll.get hall i hic) hpc.1 hvis (fun hd => ih rfl hd hpc.1 hpc.2)
    | .word _ _ hnav _ | .bytes _ _ hnav _ => rw [hop0] at hnav; simp [isNavOp] at hnav
    | .sliceWord _ hop' _ _ _ _ _ | .sliceBytes _ hop' _ _ _ _ _ => rw [hop0] at hop'; cases hop'
    | .logical _ _ hop' _ _ _ _ => rw [hop0] at hop'; simp at hop'
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
      exact Reached.step (fun q => Val.sub_array vs i hiv q) (by rw [hcs]; simp)
        (h0 _ (List.getElem_mem hiv)) hpc.1 hvis (fun hd => ih rfl hd hpc.1 hpc.2)
    | .word _ _ hnav _ | .bytes _ _ hnav _ | .tuple _ _ _ hnav =>
      rcases hop with h | h <;> (rw [annotate_op_of h (by decide)] at hnav; simp [isNavOp] at hnav)
    | .sliceWord _ hop' _ _ _ _ _ | .sliceBytes _ hop' _ _ _ _ _ =>
      rcases hop with h | h <;> (rw [annotate_op_of h (by decide)] at hop'; cases hop')
    | .call _ _ _ _ hop' =>
      rcases hop with h | h <;> (rw [annotate_op_of h (by decide)] at hop'; simp at hop')
    | .logical _ _ hop' _ _ _ _ =>
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
      exact Reached.step (fun q => Val.sub_array vs _ hjv q) (List.getElem_mem hjc') hDS' hpc.1
        hvis (fun hd => ih rfl hd hpc.1 hpc.2)
    | .word _ _ hnav _ | .bytes _ _ hnav _ => rw [hop0] at hnav; simp [isNavOp] at hnav
    | .sliceWord _ hop' _ _ _ _ _ | .sliceBytes _ hop' _ _ _ _ _ => rw [hop0] at hop'; cases hop'
    | .tuple _ _ _ hnav => rcases hnav with h | h <;> (rw [hop0] at h; simp [isNavOp] at h)
    | .call _ _ _ _ hop' => rw [hop0] at hop'; simp at hop'
    | .logical _ _ hop' _ _ _ _ => rw [hop0] at hop'; simp at hop'
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
    | .logical _ _ hop' _ _ _ _ => rw [hop0] at hop'; simp at hop'

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

/-! ## Zip jumps -/

/-- `d` is what the evaluator sees for the raw node `d0` (with `size`
    possibly overridden by a `Slice`). -/
def Raw (d0 d : Condition) : Prop := d = annotate d0 ∨ ∃ n, d = (annotate d0).withSize n

/-- `d` is what the evaluator sees for a node of `root`, or the default node
    (`children[i]` past the end; Integrity rules that out). -/
def RawIn (root d : Condition) : Prop := ∃ d0, (Sub d0 root ∨ d0 = default) ∧ Raw d0 d

theorem annotate_default : annotate default = default := by
  rw [annotate_eq]; simp [isInlined_eq, inlinedSize_eq]; rfl

theorem Raw.children {d0 d : Condition} (h : Raw d0 d) : d.children = d0.children.map annotate := by
  rcases h with rfl | ⟨n, rfl⟩ <;> simp [annotate_children]

theorem Raw.compValue {d0 d : Condition} (h : Raw d0 d) : d.compValue = d0.compValue := by
  rcases h with rfl | ⟨n, rfl⟩ <;> simp [annotate_compValue]

theorem Raw.operator {d0 d : Condition} (h : Raw d0 d) : d.operator = (annotate d0).operator := by
  rcases h with rfl | ⟨n, rfl⟩ <;> simp

theorem Raw.encoding {d0 d : Condition} (h : Raw d0 d) : d.encoding = (annotate d0).encoding := by
  rcases h with rfl | ⟨n, rfl⟩ <;> simp

theorem RawIn.root (root : Condition) : RawIn root (annotate root) := ⟨root, .inl (.refl root), .inl rfl⟩

theorem RawIn.default' (root : Condition) : RawIn root default :=
  ⟨default, .inr rfl, .inl annotate_default.symm⟩

theorem RawIn.mem {root c ch : Condition} (hc : RawIn root c) (hm : ch ∈ c.children) :
    RawIn root ch := by
  obtain ⟨c0, hc0, hr⟩ := hc
  rw [hr.children] at hm
  obtain ⟨ch0, hm0, rfl⟩ := List.mem_map.mp hm
  refine ⟨ch0, ?_, .inl rfl⟩
  rcases hc0 with hs | rfl
  · exact .inl ((Sub.mem hm0).trans hs)
  · cases hm0

theorem RawIn.getD {root c : Condition} (hc : RawIn root c) (i : Nat) :
    RawIn root (c.children.getD i default) := by
  by_cases hi : i < c.children.length
  · have : c.children.getD i default = c.children[i] := by simp [hi]
    rw [this]; exact hc.mem (List.getElem_mem hi)
  · have : c.children.getD i default = default := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl
    rw [this]; exact RawIn.default' root

theorem RawIn.headD {root c : Condition} (hc : RawIn root c) :
    RawIn root (c.children.headD default) := by
  cases h : c.children with
  | nil => exact RawIn.default' root
  | cons ch _ => exact hc.mem (by rw [h]; simp)

theorem RawIn.withSize {root c : Condition} (hc : RawIn root c) (n : Nat) :
    RawIn root (c.withSize n) := by
  obtain ⟨c0, h0, hr⟩ := hc
  refine ⟨c0, h0, .inr ⟨n, ?_⟩⟩
  rcases hr with rfl | ⟨m, rfl⟩ <;> rfl

theorem Visit.rawIn {data : Bytes} {root : Condition} :
    ∀ {c loc p d l}, Visit data c loc p d l → RawIn root c → RawIn root d := by
  intro c loc p d l hv
  induction hv with
  | here => exact id
  | logical ch _ hm _ ih => exact fun hc => ih (hc.mem hm)
  | matchesChild _ i _ _ _ _ _ ih => exact fun hc => ih (hc.getD i)
  | arrayIter _ _ _ _ _ _ ih => exact fun hc => ih hc.headD
  | arrayTail _ j _ _ _ _ _ _ ih => exact fun hc => ih (hc.getD j)
  | slice _ _ _ _ ih => exact fun hc => ih (hc.headD.withSize _)

theorem Eval.rawIn {data : Bytes} {root : Condition} :
    ∀ {p d l}, Eval data (annotate root) p d l → RawIn root d := by
  intro p d l he
  induction he with
  | visit hv => exact Visit.rawIn hv (RawIn.root root)
  | zip f _ _ _ _ _ _ _ _ _ _ hvis ihz _ => exact Visit.rawIn hvis (ihz.headD.getD f)

theorem zipFields_raw {z0 z : Condition} (h : Raw z0 z) :
    zipFields z = (zipFields z0).map annotate := by
  unfold zipFields
  rw [h.children]
  cases z0.children with
  | nil => rfl
  | cons t _ => simp [annotate_children]

theorem Sub.zipField {z0 x : Condition} (hx : x ∈ zipFields z0) : Sub x z0 := by
  unfold zipFields at hx
  cases h : z0.children with
  | nil => rw [h] at hx; cases hx
  | cons t ts =>
    rw [h] at hx
    exact .child (by rw [h]; simp) (Sub.mem hx)

theorem Desc.array_of {s : Bool} {c : Condition} {V : Val} (hD : Desc s c V)
    (he : c.encoding = .Array) : ∃ vs, V = .array vs := by
  cases hD with
  | array => exact ⟨_, rfl⟩
  | word h _ _ _ | bytes h _ _ _ | sliceWord h _ _ _ _ _ _ | sliceBytes h _ _ _ _ _ _
  | tuple h _ _ _ | call h _ _ _ _ | logical _ h _ _ _ _ _ => rw [he] at h; cases h

theorem annotate_zipStub (f : Condition) : annotate (zipStub f) = zipStub (annotate f) := by
  rw [annotate_eq]; simp [zipStub, isInlined_eq]

/-- At a Zip jump, the Pluck node that field `f` of the Zip `z0` (a node of
    `root`) references sits at an array whose elements field `f` describes,
    or lies inside an interpretation that need not hold. -/
theorem zip_pluck {s : Bool} {data : Bytes} {root : Condition} {V0 : Val} {pp : List Nat}
    {pk : Condition} {L : Nat} {z0 : Condition} {f : Nat} (hZ : ZipOK s root)
    (hz0 : Sub z0 root) (hzop : z0.operator = .ZipSome ∨ z0.operator = .ZipEvery)
    (hf : f < (zipFields z0).length) (hpkop : pk.operator = .Pluck)
    (hidx : cvByte pk.compValue 0 = cvByte z0.compValue f) (hraw : RawIn root pk)
    (hR : Reached s data root V0 pp pk L) :
    (∃ vs, V0.sub pp = some (.array vs) ∧ At data L (enc (.array vs)) ∧
      ∀ v, v ∈ vs → DescS s (zipFields z0)[f] v) ∨ InStray s data V0 pp pk L := by
  -- The referenced Pluck node of `root` is an `Array` node.
  obtain ⟨pk1, hpk1, hr1⟩ := hraw
  have hop1 : (annotate pk1).operator = .Pluck := by rw [← hr1.operator]; exact hpkop
  have hop1' := annotate_op_of hop1 (by decide)
  have hpk1s : Sub pk1 root := by
    rcases hpk1 with h | rfl
    · exact h
    · cases hop1'
  have hcv1 : cvByte pk1.compValue 0 = cvByte z0.compValue f := by
    rw [← hidx, hr1.compValue]
  have henc1 := (hZ z0 pk1 f hz0 hpk1s hzop hf hop1' hcv1).1
  have hpkenc : pk.encoding = .Array := by rw [hr1.encoding, annotate_encoding, henc1]; simp
  rcases hR with ⟨d0, V, hd0, rfl, hsub, hD, hp, _⟩ | ⟨d0, rfl, hns⟩ |
    ⟨d0, bs, u', rfl, hw, _⟩ | hst
  · have hop0 := annotate_op_of hpkop (by decide)
    have hcv0 : cvByte d0.compValue 0 = cvByte z0.compValue f := by
      rw [← hidx, annotate_compValue]
    obtain ⟨he0, hall⟩ := hZ z0 d0 f hz0 hd0 hzop hf hop0 hcv0
    obtain ⟨vs, rfl⟩ := hD.array_of he0
    refine Or.inl ⟨vs, hsub, hp, fun v hv => ?_⟩
    have := hall vs hD v hv
    have hg : (zipFields z0).getD f default = (zipFields z0)[f] := by simp [hf]
    rwa [hg] at this
  · exfalso
    rw [annotate_encoding] at hpkenc
    rcases hns with hns | ⟨_, he, _, _⟩
    · cases hns with
      | leaf he _ _ => rcases he with he | he <;> simp [he] at hpkenc
      | logical he _ _ => simp [he] at hpkenc
    · simp [he] at hpkenc
  · exfalso
    have he : d0.encoding = .Static := by cases hw <;> assumption
    rw [Condition.withSize_encoding, annotate_encoding, he] at hpkenc
    cases hpkenc
  · exact Or.inr hst

/-- A reached Zip node is (as the evaluator sees it) a Zip node of `root`. -/
theorem Eval.zip_raw {data : Bytes} {root : Condition} {pz : List Nat} {z : Condition}
    {lz : Nat} (hzE : Eval data (annotate root) pz z lz)
    (hzop : z.operator = .ZipSome ∨ z.operator = .ZipEvery) :
    ∃ z0, Sub z0 root ∧ (z0.operator = .ZipSome ∨ z0.operator = .ZipEvery) ∧
      zipFields z = (zipFields z0).map annotate ∧ z.compValue = z0.compValue := by
  obtain ⟨z0, hz0, hrz⟩ := Eval.rawIn hzE
  have hzop0 : z0.operator = .ZipSome ∨ z0.operator = .ZipEvery := by
    rw [hrz.operator] at hzop
    rcases hzop with h | h
    · exact .inl (annotate_op_of h (by decide))
    · exact .inr (annotate_op_of h (by decide))
  refine ⟨z0, ?_, hzop0, zipFields_raw hrz, hrz.compValue⟩
  rcases hz0 with h | rfl
  · exact h
  · rcases hzop0 with h | h <;> cases h

/-- Soundness of navigation from the root, including Zip jumps. -/
theorem eval_sound {data : Bytes} (hlen : data.length < 2 ^ 255) {s : Bool} {root : Condition}
    {V0 : Val} (hD : Desc s root V0) (hR : RootOK root) (hp0 : Placed data 0 V0)
    (hZ : ZipOK s root) :
    ∀ {p d l}, Eval data (annotate root) p d l → Reached s data root V0 p d l := by
  intro p d l he
  induction he with
  | visit hv => exact visit_sound hlen hv rfl hD hp0 (fun _ _ => hR)
  | @zip pz z lz pp pk L p d l f locs i hi hzE hzop hf hpkE hpkop hidx hch hvis _ ihpk =>
    obtain ⟨z0, hz0s, hzop0, hfields, hcv⟩ := Eval.zip_raw hzE hzop
    have hf0 : f < (zipFields z0).length := by rw [hfields] at hf; simpa using hf
    have hfield : (zipFields z).getD f default = annotate (zipFields z0)[f] := by
      rw [hfields]; simp [hf0]
    have hidx0 : cvByte pk.compValue 0 = cvByte z0.compValue f := by rw [hidx, hcv]
    rcases zip_pluck hZ hz0s hzop0 hf0 hpkop hidx0 (Eval.rawIn hpkE) ihpk with
      ⟨vs, hsub, hat, hall⟩ | ⟨hs, p1, p2, ch, us, ls, rfl, hsub, hb, hu, hp, hbel⟩
    · rw [hfield, ← annotate_zipStub] at hch
      rw [hfield] at hvis
      obtain ⟨locs', hl, hlen', hpl⟩ := children_array hlen (c := zipStub (zipFields z0)[f])
        (by rw [annotate_encoding]; simp [zipStub]) rfl hall hat
      rw [hl] at hch; cases hch
      have hiv : i < vs.length := by omega
      have hpc := child_placed (c := (zipFields z0)[f]) (hpl i hi hiv)
      have hsubF : Sub (zipFields z0)[f] root :=
        (Sub.zipField (List.getElem_mem hf0)).trans hz0s
      have key := Reached.stepP (P := pp ++ [i]) (u := V0) (v := vs[i])
        (fun q => by rw [List.append_assoc, Val.sub_append hsub]; exact Val.sub_array vs i hiv q)
        hsubF (hall _ (List.getElem_mem hiv)) hpc.1 hvis
        (fun hd => visit_sound hlen hvis rfl hd hpc.1 hpc.2)
      simpa [List.append_assoc] using key
    · exact Or.inr (Or.inr (Or.inr ⟨hs, p1, p2 ++ i :: p, ch, us, ls, by simp, hsub, hb, hu, hp,
        .zip hi hbel hpkop hch hvis⟩))

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
theorem decoder_locations {s : Bool}
    (hD : Desc s root (.call pre args)) (hR : RootOK root) (hZ : ZipOK s root)
    (hlen : (calldata pre args suffix).length < 2 ^ 255)
    {p : List Nat} {d : Condition} {l : Nat}
    (hv : Eval (calldata pre args suffix) (annotate root) p d l) :
    Reached s (calldata pre args suffix) root (.call pre args) p d l :=
  eval_sound hlen hD hR (root_placed pre args suffix) hZ hv

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
theorem decoder_input {s : Bool}
    (hD : Desc s root (.call pre args)) (hR : RootOK root) (hZ : ZipOK s root)
    (hlen : (calldata pre args suffix).length < 2 ^ 255)
    {p : List Nat} {d : Condition} {l : Nat}
    (hv : Eval (calldata pre args suffix) (annotate root) p d l)
    (hop : readsInput d.operator = true) :
    (∃ u, (Val.call pre args).sub p = some u ∧
      input (calldata pre args suffix) l d = expectInput (enc u)) ∨
    (∃ u bs, (Val.call pre args).sub p = some u ∧ IsWindow bs (content u) ∧
      input (calldata pre args suffix) l d = .word (wordVal bs)) ∨
    input (calldata pre args suffix) l d = .etherValue ∨
    InStray s (calldata pre args suffix) (.call pre args) p d l := by
  have hlen' := hlen
  rcases decoder_locations root pre args suffix hD hR hZ hlen hv with
    ⟨d0, u, _, rfl, hsub, hD0, hp, hr⟩ | ⟨d0, rfl, hns⟩ |
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
    rcases hns with hns | ⟨_, he, _, _⟩
    · cases hns with
      | leaf he _ _ => rcases he with he | he <;> simp [he]
      | logical he _ _ => simp [he]
    · simp [he]
  · right; left
    exact ⟨u, bs, hsub, hiw, Win.input_eq hw hat h1 h32⟩
  · right; right; right; exact hst

/-- **Custom conditions.** `Custom` receives `(location, size)`: exactly the
    position and length of the spec encoding of the described component, or
    of the window below a `Slice`. -/
theorem decoder_custom_operand {s : Bool}
    (hD : Desc s root (.call pre args)) (hR : RootOK root) (hZ : ZipOK s root)
    (hlen : (calldata pre args suffix).length < 2 ^ 255)
    {p : List Nat} {d : Condition} {l : Nat}
    (hv : Eval (calldata pre args suffix) (annotate root) p d l)
    (hop : d.operator = .Custom) :
    (∃ u, (Val.call pre args).sub p = some u ∧ At (calldata pre args suffix) l (enc u) ∧
      (if d.size ≠ 0 then d.size else Roles.size (calldata pre args suffix) l d) =
        (enc u).length) ∨
    (∃ u bs, (Val.call pre args).sub p = some u ∧ IsWindow bs (content u) ∧
      At (calldata pre args suffix) l bs ∧
      (if d.size ≠ 0 then d.size else Roles.size (calldata pre args suffix) l d) = bs.length) ∨
    (∃ d0, d = annotate d0 ∧ NonStruct d0) ∨
    InStray s (calldata pre args suffix) (.call pre args) p d l := by
  rcases decoder_locations root pre args suffix hD hR hZ hlen hv with
    ⟨d0, u, _, rfl, hsub, hD0, hp, hr⟩ | hns |
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
  · right; right; left
    obtain ⟨d0, rfl, hns | ⟨_, _, hz, _⟩⟩ := hns
    · exact ⟨d0, rfl, hns⟩
    · rcases hz with h | h <;> (rw [annotate_op_eq h (by decide)] at hop; cases hop)
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
  | .logical _ he _ _ _ _ _ =>
    rcases hcont with h | h | h <;> rw [he] at h <;> cases h

/-- **No false rejections: containers.** Every visited container decodes its
    children without overflow, one location per component. -/
theorem decoder_children {s : Bool}
    (hD : Desc s root (.call pre args)) (hR : RootOK root) (hZ : ZipOK s root)
    (hlen : (calldata pre args suffix).length < 2 ^ 255)
    {p : List Nat} {d : Condition} {l : Nat}
    (hv : Eval (calldata pre args suffix) (annotate root) p d l)
    (hcont : d.encoding = .Tuple ∨ d.encoding = .Array ∨ d.encoding = .AbiEncoded) :
    (∃ u, (Val.call pre args).sub p = some u ∧
      ∃ locs, children (calldata pre args suffix)
        ((if l > 0 ∧ d.encoding = .AbiEncoded then l + 32 else l) + d.leadingBytes) d =
          some locs ∧ locs.length = u.components.length) ∨
    InStray s (calldata pre args suffix) (.call pre args) p d l := by
  rcases decoder_locations root pre args suffix hD hR hZ hlen hv with
    ⟨d0, u, _, rfl, hsub, hD0, hp, _⟩ | ⟨d0, rfl, hns⟩ | ⟨d0, bs, u, rfl, hw, _⟩ | hst
  · left
    refine ⟨u, hsub, hD0.children_ok hlen hp ?_⟩
    rw [annotate_encoding] at hcont
    split at hcont
    · rcases hcont with h | h | h <;> cases h
    · exact hcont
  · exfalso
    rw [annotate_encoding] at hcont
    rcases hns with hns | ⟨_, he, _, _⟩
    · cases hns with
      | leaf he _ _ => rcases he with he | he <;> simp [he] at hcont
      | logical he _ _ => simp [he] at hcont
    · simp [he] at hcont
  · exfalso
    have he : d0.encoding = .Static := by cases hw <;> assumption
    rw [Condition.withSize_encoding, annotate_encoding, he] at hcont
    rcases hcont with h | h | h <;> cases h
  · right; exact hst

/-- **No false rejections: Zip.** For a visited Zip, field `f`, and a
    visited Pluck node it references: the array at the Pluck's location
    decodes without overflow into one location per spec element of the
    plucked array. So the Zip reports `ZippedArrayLengthMismatch` exactly
    when the plucked arrays' spec lengths differ, and by `decoder_locations`
    each field is then evaluated at its element's spec position. -/
theorem decoder_zip {s : Bool}
    (hD : Desc s root (.call pre args)) (hR : RootOK root) (hZ : ZipOK s root)
    (hlen : (calldata pre args suffix).length < 2 ^ 255)
    {pz pp : List Nat} {z pk : Condition} {lz L f : Nat}
    (hz : Eval (calldata pre args suffix) (annotate root) pz z lz)
    (hzop : z.operator = .ZipSome ∨ z.operator = .ZipEvery) (hf : f < (zipFields z).length)
    (hpk : Eval (calldata pre args suffix) (annotate root) pp pk L)
    (hpkop : pk.operator = .Pluck) (hidx : cvByte pk.compValue 0 = cvByte z.compValue f) :
    (∃ vs locs, (Val.call pre args).sub pp = some (.array vs) ∧
      children (calldata pre args suffix) L (zipStub ((zipFields z).getD f default)) =
        some locs ∧ locs.length = vs.length) ∨
    InStray s (calldata pre args suffix) (.call pre args) pp pk L := by
  obtain ⟨z0, hz0s, hzop0, hfields, hcv⟩ := Eval.zip_raw hz hzop
  have hf0 : f < (zipFields z0).length := by rw [hfields] at hf; simpa using hf
  have hfield : (zipFields z).getD f default = annotate (zipFields z0)[f] := by
    rw [hfields]; simp [hf0]
  have hidx0 : cvByte pk.compValue 0 = cvByte z0.compValue f := by rw [hidx, hcv]
  rcases zip_pluck hZ hz0s hzop0 hf0 hpkop hidx0 (Eval.rawIn hpk)
      (decoder_locations root pre args suffix hD hR hZ hlen hpk) with
    ⟨vs, hsub, hat, hall⟩ | hst
  · obtain ⟨locs, hl, hlen', _⟩ := children_array hlen (c := zipStub (zipFields z0)[f])
      (by rw [annotate_encoding]; simp [zipStub]) rfl hall hat
    refine Or.inl ⟨vs, locs, hsub, ?_, hlen'⟩
    rw [hfield, ← annotate_zipStub]; exact hl
  · exact Or.inr hst

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
  | .logical _ _ hop' _ _ _ _ => rw [hop0] at hop'; simp at hop'

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
theorem decoder_slice {s : Bool}
    (hD : Desc s root (.call pre args)) (hR : RootOK root) (hZ : ZipOK s root)
    (hlen : (calldata pre args suffix).length < 2 ^ 255)
    {p : List Nat} {d : Condition} {l : Nat}
    (hv : Eval (calldata pre args suffix) (annotate root) p d l)
    (hop : d.operator = .Slice) :
    (∃ u, (Val.call pre args).sub p = some u ∧
      (d.inlined = false → l + 32 ≤ (calldata pre args suffix).length) ∧
      (if d.inlined then d.size else load (calldata pre args suffix) l) = (content u).length) ∨
    (∃ u bs, (Val.call pre args).sub p = some u ∧ IsWindow bs (content u) ∧
      At (calldata pre args suffix) l bs ∧ d.inlined = true ∧ d.size = bs.length) ∨
    InStray s (calldata pre args suffix) (.call pre args) p d l := by
  rcases decoder_locations root pre args suffix hD hR hZ hlen hv with
    ⟨d0, u, _, rfl, hsub, hD0, hp, hr⟩ | ⟨d0, rfl, hns⟩ |
    ⟨d0, bs, u, rfl, hw, hat, _, _, hsub, hiw⟩ | hst
  · exact Or.inl ⟨u, hsub, Desc.slice_length hop hD0 hp hr hlen⟩
  · exfalso
    have := annotate_op_of hop (by decide)
    rcases hns with hns | ⟨_, _, hz, _⟩
    · cases hns with
      | leaf _ _ hnav => rw [this] at hnav; simp [isNavOp] at hnav
      | logical _ hop' _ => rw [this] at hop'; simp at hop'
    · rw [this] at hz; rcases hz with h | h <;> cases h
  · exact Or.inr (Or.inl ⟨u, bs, hsub, hiw, hat, (Win.annotate_meta hw).1, rfl⟩)
  · exact Or.inr (Or.inr hst)

end Top

end DecoderFaithfulness
