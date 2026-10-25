import EIP712.Agree

/-!
# Checking the agreement hypotheses

`fitB` / `msgB` decide the hypotheses of `visit_agree` and `message_agree`
on a concrete (unpacked) condition tree and type tree; `fitB_sound` and
`msgB_sound` show they imply them. The driver's `fit` query runs `msgB` on
the conditions `allowSignTypedMessage` builds, so the fuzz corpus checks
that the SDK's permissions satisfy the theorem.
-/

namespace EIP712
open DecoderFaithfulness DecoderFaithfulness.Roles

def metaB (ch : Condition) (t : TN) : Bool :=
  match inlineSize t with
  | some isz => ch.inlined == decide (0 < isz) && ch.size == isz
  | none => false

theorem metaB_sound {ch : Condition} {t : TN} (h : metaB ch t = true) : MetaFit ch t := by
  unfold metaB at h
  split at h
  · rename_i isz hisz
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    refine ⟨isz, hisz, ?_, h.2⟩
    rw [h.1]; simp
  · simp at h

def noDescendB (op : Operator) : Bool :=
  !(op == .And || op == .Or || op == .Matches || op == .ArraySome || op == .ArrayEvery ||
    op == .ArrayTailMatches || op == .Slice)

theorem noDescendB_sound {op : Operator} (h : noDescendB op = true) : NoDescend op := by
  cases op <;> simp_all [noDescendB, NoDescend]

def isArrayOp (op : Operator) : Bool :=
  op == .Matches || op == .ArraySome || op == .ArrayEvery || op == .ArrayTailMatches

def fitB : Nat → Condition → TN → Bool
  | 0, _, _ => false
  | f + 1, c, t =>
    if noDescendB c.operator then true
    else if c.operator == .And || c.operator == .Or then
      c.children.all fun ch => metaB ch t && fitB f ch t
    else if c.operator == .Matches && t.encoding == .Tuple && c.encoding != .Array &&
        c.encoding != .AbiEncoded && c.leadingBytes == 0 &&
        c.children.length == t.children.length then
      (c.children.zip t.children).all fun (ch, tc) => metaB ch tc && fitB f ch tc
    else
      match t with
      | ⟨.Array, [l], _⟩ =>
        c.encoding == .Array && c.leadingBytes == 0 && !c.children.isEmpty &&
          isArrayOp c.operator && c.children.all fun ch => metaB ch l && fitB f ch l
      | _ => false

theorem zip_all_get {α β : Type} {p : α × β → Bool} :
    ∀ {as : List α} {bs : List β}, (as.zip bs).all p = true → as.length = bs.length →
    ∀ k (h1 : k < as.length) (h2 : k < bs.length), p (as[k], bs[k]) = true
  | [], [], _, _, k, h1, _ => by simp at h1
  | a :: as, b :: bs, h, hl, 0, _, _ => by simp at h; simpa using h.1
  | a :: as, b :: bs, h, hl, k + 1, h1, h2 => by
    simp only [List.zip_cons_cons, List.all_cons, Bool.and_eq_true] at h
    simpa using zip_all_get h.2 (by simpa using hl) k (by simp at h1; omega) (by simp at h2; omega)
  | [], _ :: _, _, hl, _, _, _ => by simp at hl
  | _ :: _, [], _, hl, _, _, _ => by simp at hl

theorem fitB_sound : ∀ (f : Nat) (c : Condition) (t : TN), fitB f c t = true → FitT c t
  | 0, _, _, h => by simp [fitB] at h
  | f + 1, c, t, h => by
    unfold fitB at h
    by_cases hn : noDescendB c.operator = true
    · exact .leaf (noDescendB_sound hn)
    rw [if_neg hn] at h
    by_cases hl : (c.operator == .And || c.operator == .Or) = true
    · rw [if_pos hl] at h
      rw [List.all_eq_true] at h
      refine .logical (by simpa using hl) (fun ch hm => metaB_sound (by
        have := h ch hm; simp only [Bool.and_eq_true] at this; exact this.1))
        (fun ch hm => fitB_sound f ch t (by
          have := h ch hm; simp only [Bool.and_eq_true] at this; exact this.2))
    rw [if_neg hl] at h
    split at h
    · rename_i ht
      simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at ht
      obtain ⟨⟨⟨⟨⟨hop, he⟩, hna⟩, hnabi⟩, hlb⟩, hlen⟩ := ht
      refine .tuple hop he hna hnabi hlb hlen (fun k h1 h2 => ?_) (fun k h1 h2 => ?_)
      · have := zip_all_get h hlen k h1 h2
        simp only [Bool.and_eq_true] at this
        exact metaB_sound this.1
      · have := zip_all_get h hlen k h1 h2
        simp only [Bool.and_eq_true] at this
        exact fitB_sound f _ _ this.2
    · split at h
      · simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', List.isEmpty_eq_false_iff,
          List.all_eq_true] at h
        obtain ⟨⟨⟨⟨he, hlb⟩, hne⟩, hop⟩, hall⟩ := h
        refine .array he hlb (by simpa using hne) (by
            simp only [isArrayOp, Bool.or_eq_true, beq_iff_eq] at hop
            rcases hop with ((h | h) | h) | h <;> simp [h])
          (fun ch hm => metaB_sound (hall ch hm).1)
          (fun ch hm => fitB_sound f ch _ (hall ch hm).2)
      · simp at h

/-- The hypotheses of `message_agree` on the condition node of the
    `message` (or `domain`) argument and the type tree of its struct. -/
def msgB (c : Condition) (tm : TN) : Bool :=
  c.operator == .Matches && c.encoding == .AbiEncoded && c.leadingBytes == 0 &&
    tm.encoding == .Tuple && c.children.length == tm.children.length &&
    (c.children.zip tm.children).all fun (ch, tc) => metaB ch tc && fitB 64 ch tc

theorem msgB_sound {c : Condition} {tm : TN} (h : msgB c tm = true) :
    c.operator = .Matches ∧ c.encoding = .AbiEncoded ∧ c.leadingBytes = 0 ∧
    tm.encoding = .Tuple ∧ c.children.length = tm.children.length ∧
    (∀ k (h1 : k < c.children.length) (h2 : k < tm.children.length),
      MetaFit c.children[k] tm.children[k]) ∧
    (∀ k (h1 : k < c.children.length) (h2 : k < tm.children.length),
      FitT c.children[k] tm.children[k]) := by
  unfold msgB at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨hop, he⟩, hlb⟩, hte⟩, hlen⟩, hall⟩ := h
  refine ⟨hop, he, hlb, hte, hlen, fun k h1 h2 => ?_, fun k h1 h2 => ?_⟩
  · have := zip_all_get hall hlen k h1 h2
    simp only [Bool.and_eq_true] at this
    exact metaB_sound this.1
  · have := zip_all_get hall hlen k h1 h2
    simp only [Bool.and_eq_true] at this
    exact fitB_sound _ _ _ this.2

end EIP712
