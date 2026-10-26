import EIP712.Sign

/-!
# Checking the agreement hypotheses

`fitB` / `msgB` / `rootB` decide the hypotheses of `visit_agree`,
`message_agree` and `sign_agree` on a concrete (unpacked) condition tree,
type trees and pluck table; `fitB_sound`, `msgB_sound` and `rootB_sound`
show they imply them. The driver's `fit` query runs `rootB` on the packed
permission, so the fuzz corpus checks that the permissions satisfy the
theorem.
-/

namespace EIP712
open DecoderFaithfulness DecoderFaithfulness.Roles

mutual
  def TN.beq : TN → TN → Bool
    | ⟨e1, c1, h1⟩, ⟨e2, c2, h2⟩ => e1 == e2 && h1 == h2 && TN.beqL c1 c2
  def TN.beqL : List TN → List TN → Bool
    | [], [] => true
    | a :: as, b :: bs => TN.beq a b && TN.beqL as bs
    | _, _ => false
end

mutual
  theorem TN.eq_of_beq : ∀ a b, TN.beq a b = true → a = b
    | ⟨e1, c1, h1⟩, ⟨e2, c2, h2⟩, h => by
      simp only [TN.beq, Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨⟨rfl, rfl⟩, hc⟩ := h
      rw [TN.eqL_of_beqL c1 c2 hc]
  theorem TN.eqL_of_beqL : ∀ as bs, TN.beqL as bs = true → as = bs
    | [], [], _ => rfl
    | a :: as, b :: bs, h => by
      simp only [TN.beqL, Bool.and_eq_true] at h
      rw [TN.eq_of_beq a b h.1, TN.eqL_of_beqL as bs h.2]
    | [], _ :: _, h => by simp [TN.beqL] at h
    | _ :: _, [], h => by simp [TN.beqL] at h
end

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

def isZipB (op : Operator) : Bool := op == .ZipSome || op == .ZipEvery

theorem isZipB_sound {op : Operator} (h : isZipB op = true) : IsZip op := by
  simp only [isZipB, Bool.or_eq_true, beq_iff_eq] at h; exact h

def noDescendB (op : Operator) : Bool :=
  !(op == .And || op == .Or || op == .Matches || op == .ArraySome || op == .ArrayEvery ||
    op == .ArrayTailMatches || op == .Slice || op == .Pluck || op == .ZipSome || op == .ZipEvery)

theorem noDescendB_sound {op : Operator} (h : noDescendB op = true) : NoDescend op := by
  cases op <;> simp_all [noDescendB, NoDescend]

def isArrayOp (op : Operator) : Bool :=
  op == .Matches || op == .ArraySome || op == .ArrayEvery || op == .ArrayTailMatches

/-- Decides `FitW`. -/
def fitWB (Γ : Plucks) : Nat → Condition → Bool
  | 0, _ => false
  | f + 1, c =>
    noDescendB c.operator ||
    (c.operator == .Pluck && (Γ (cvByte c.compValue 0)).isNone) ||
    (c.operator == .Slice && c.inlined && decide (0 < sliceSize c.compValue) &&
      decide (sliceSize c.compValue ≤ 32) && fitWB Γ f (c.children.headD default))

theorem fitWB_sound (Γ : Plucks) : ∀ f c, fitWB Γ f c = true → FitW Γ c
  | 0, _, h => by simp [fitWB] at h
  | f + 1, c, h => by
    simp only [fitWB, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq,
      Option.isNone_iff_eq_none] at h
    rcases h with (h | ⟨h1, h2⟩) | ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩
    · exact .leaf (noDescendB_sound h)
    · exact .pluck h1 h2
    · exact .slice h1 h2 h3 h4 (fitWB_sound Γ f _ h5)

/-- The `Pluck` case of `fitB`. -/
def pluckB (Γ : Plucks) (c : Condition) (t : TN) : Bool :=
  match Γ (cvByte c.compValue 0) with
  | none => true
  | some l => t.encoding == .Array && TN.beqL t.children [l]

theorem pluckB_sound {Γ : Plucks} {c : Condition} {t : TN} (h : pluckB Γ c t = true) :
    ∀ l, Γ (cvByte c.compValue 0) = some l → ∃ th, t = ⟨.Array, [l], th⟩ := by
  intro l hg
  unfold pluckB at h
  rw [hg] at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨he, hc⟩ := h
  have := TN.eqL_of_beqL _ _ hc
  obtain ⟨e, cs, th⟩ := t
  simp only at he this
  subst he; subst this
  exact ⟨th, rfl⟩

/-- Decides `FitT`. -/
def fitB (Γ : Plucks) : Nat → Condition → TN → Bool
  | 0, _, _ => false
  | f + 1, c, t =>
    if noDescendB c.operator then true
    else if c.operator == .Pluck then pluckB Γ c t
    else if isZipB c.operator then
      (List.range (zipFields c).length).all fun k =>
        match Γ (cvByte c.compValue k) with
        | none => false
        | some l => metaB ((zipFields c).getD k default) l &&
            fitB Γ f ((zipFields c).getD k default) l
    else if c.operator == .Slice then
      ((t.encoding == .Static && c.inlined && c.size == 32) ||
        (t.encoding == .Dynamic && !c.inlined)) &&
        decide (0 < sliceSize c.compValue) && decide (sliceSize c.compValue ≤ 32) &&
        fitWB Γ f (c.children.headD default)
    else if c.operator == .And || c.operator == .Or then
      c.children.all fun ch => (metaB ch t || isZipB ch.operator) && fitB Γ f ch t
    else if c.operator == .Matches && t.encoding == .Tuple && c.encoding != .Array &&
        c.encoding != .AbiEncoded && c.leadingBytes == 0 &&
        c.children.length == t.children.length then
      (c.children.zip t.children).all fun (ch, tc) => metaB ch tc && fitB Γ f ch tc
    else
      match t with
      | ⟨.Array, [l], _⟩ =>
        c.encoding == .Array && c.leadingBytes == 0 && !c.children.isEmpty &&
          isArrayOp c.operator && c.children.all fun ch => metaB ch l && fitB Γ f ch l
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

theorem fitB_sound (Γ : Plucks) : ∀ (f : Nat) (c : Condition) (t : TN), fitB Γ f c t = true →
    FitT Γ c t
  | 0, _, _, h => by simp [fitB] at h
  | f + 1, c, t, h => by
    unfold fitB at h
    by_cases hn : noDescendB c.operator = true
    · exact .leaf (noDescendB_sound hn)
    rw [if_neg hn] at h
    by_cases hp : (c.operator == .Pluck) = true
    · rw [if_pos hp] at h
      exact .pluck (by simpa using hp) (pluckB_sound h)
    rw [if_neg hp] at h
    by_cases hz : isZipB c.operator = true
    · rw [if_pos hz] at h
      rw [List.all_eq_true] at h
      have hk : ∀ k, k < (zipFields c).length → ∃ l, Γ (cvByte c.compValue k) = some l ∧
          metaB ((zipFields c).getD k default) l = true ∧
          fitB Γ f ((zipFields c).getD k default) l = true := by
        intro k hk
        have := h k (List.mem_range.mpr hk)
        revert this
        cases hg : Γ (cvByte c.compValue k) with
        | none => simp
        | some l =>
          intro this
          simp only [Bool.and_eq_true] at this
          exact ⟨l, rfl, this.1, this.2⟩
      refine .zip (isZipB_sound hz) (fun k hk' => ?_) (fun k l hk' hg => ?_)
      · obtain ⟨l, hg, hm, _⟩ := hk k hk'
        exact ⟨l, hg, metaB_sound hm⟩
      · obtain ⟨l', hg', _, hf⟩ := hk k hk'
        rw [hg] at hg'
        cases hg'
        exact fitB_sound Γ f _ _ hf
    rw [if_neg hz] at h
    by_cases hs : (c.operator == .Slice) = true
    · rw [if_pos hs] at h
      simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq,
        Bool.not_eq_true'] at h
      obtain ⟨⟨⟨hk, h1⟩, h2⟩, hw⟩ := h
      refine .slice (by simpa using hs) ?_ h1 h2 (fitWB_sound Γ f _ hw)
      rcases hk with ⟨⟨he, hi⟩, hsz⟩ | ⟨he, hi⟩
      · exact Or.inl ⟨he, hi, hsz⟩
      · exact Or.inr ⟨he, hi⟩
    rw [if_neg hs] at h
    by_cases hl : (c.operator == .And || c.operator == .Or) = true
    · rw [if_pos hl] at h
      rw [List.all_eq_true] at h
      refine .logical (by simpa using hl) (fun ch hm => ?_) (fun ch hm => fitB_sound Γ f ch t (by
          have := h ch hm; simp only [Bool.and_eq_true] at this; exact this.2))
      have := h ch hm
      simp only [Bool.and_eq_true, Bool.or_eq_true] at this
      rcases this.1 with h' | h'
      · exact Or.inl (metaB_sound h')
      · exact Or.inr (isZipB_sound h')
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
        exact fitB_sound Γ f _ _ this.2
    · split at h
      · simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', List.isEmpty_eq_false_iff,
          List.all_eq_true] at h
        obtain ⟨⟨⟨⟨he, hlb⟩, hne⟩, hop⟩, hall⟩ := h
        refine .array he hlb (by simpa using hne) (by
            simp only [isArrayOp, Bool.or_eq_true, beq_iff_eq] at hop
            rcases hop with ((h | h) | h) | h <;> simp [h])
          (fun ch hm => metaB_sound (hall ch hm).1)
          (fun ch hm => fitB_sound Γ f ch _ (hall ch hm).2)
      · simp at h

/-- Decides `MsgFit`. -/
def msgB (Γ : Plucks) (c : Condition) (tm : TN) : Bool :=
  c.operator == .Matches && c.encoding == .AbiEncoded && c.leadingBytes == 0 &&
    tm.encoding == .Tuple && c.children.length == tm.children.length &&
    (c.children.zip tm.children).all fun (ch, tc) => metaB ch tc && fitB Γ 64 ch tc

theorem msgB_sound {Γ : Plucks} {c : Condition} {tm : TN} (h : msgB Γ c tm = true) :
    MsgFit Γ c tm := by
  unfold msgB at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨hop, he⟩, hlb⟩, hte⟩, hlen⟩, hall⟩ := h
  refine ⟨hop, he, hlb, hte, hlen, fun k h1 h2 => ?_, fun k h1 h2 => ?_⟩
  · have := zip_all_get hall hlen k h1 h2
    simp only [Bool.and_eq_true] at this
    exact metaB_sound this.1
  · have := zip_all_get hall hlen k h1 h2
    simp only [Bool.and_eq_true] at this
    exact fitB_sound Γ _ _ _ this.2

/-- Decides `NoPZ` (with fuel). -/
def noPZB : Nat → Condition → Bool
  | 0, _ => false
  | f + 1, c => c.operator != .Pluck && c.operator != .ZipSome && c.operator != .ZipEvery &&
      c.children.all (noPZB f)

theorem noPZB_sound : ∀ f c, noPZB f c = true → NoPZ c
  | 0, _, h => by simp [noPZB] at h
  | f + 1, c, h => by
    simp only [noPZB, Bool.and_eq_true, bne_iff_ne, ne_eq, List.all_eq_true] at h
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
    exact .mk h1 h2 h3 fun ch hm => noPZB_sound f ch (h4 ch hm)

/-- Decides `RootFit` for the type trees `td` (`EIP712Domain`) and `tm`
    (the primary type). -/
def rootB (Γ : Plucks) (root : Condition) (td tm : TN) : Bool :=
  root.operator == .Matches && root.encoding == .AbiEncoded && root.leadingBytes == 4 &&
    root.children.length == 3 &&
    !(root.children.getD 0 default).inlined && !(root.children.getD 1 default).inlined &&
    msgB Γ (root.children.getD 0 default) td && msgB Γ (root.children.getD 1 default) tm &&
    noPZB 64 (root.children.getD 2 default)

theorem rootB_sound {Γ : Plucks} {root : Condition} {td tm : TN} (h : rootB Γ root td tm = true) :
    RootFit Γ root (fun j => if j = 0 then td else tm) := by
  unfold rootB at h
  simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hop, he⟩, hlb⟩, hlen⟩, h0⟩, h1⟩, hd⟩, hm⟩, ht⟩ := h
  refine ⟨hop, he, hlb, hlen, fun j hj => ?_, fun j hj => ?_, noPZB_sound _ _ ht⟩
  · rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl <;> assumption
  · rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl
    · exact msgB_sound hd
    · exact msgB_sound hm

end EIP712
