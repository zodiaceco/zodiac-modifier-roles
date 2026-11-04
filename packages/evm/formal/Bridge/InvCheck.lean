import Bridge.Final

/-!
# A decidable check of well-typedness

`invB` decides `inv` (`invB_sound`), so the differential test can ask, for
every tree the SDK check accepts, whether it is well-typed (the driver's
`iv` query).
-/

namespace Bridge
open DecoderFaithfulness DecoderFaithfulness.Roles Normalize Evaluate

/-- `P` holds of every node, as a Boolean. -/
def allB (p : Cond → Bool) : Cond → Bool
  | ⟨e, o, cv, ch⟩ => p ⟨e, o, cv, ch⟩ && ch.attach.all fun ⟨x, _⟩ => allB p x
termination_by c => sizeOf c
decreasing_by
  simp_wf
  have := List.sizeOf_lt_of_mem ‹_ ∈ ch›
  omega

theorem allB_sound {p : Cond → Bool} : ∀ c, allB p c = true → AllN (fun c => p c = true) c
  | ⟨e, o, cv, ch⟩, h => by
    rw [allB] at h
    simp only [Bool.and_eq_true, List.all_eq_true] at h
    exact .mk h.1 fun x hx => allB_sound x (h.2 ⟨x, hx⟩ (List.mem_attach _ _))
termination_by c => sizeOf c
decreasing_by exact Normalize.sizeOf_lt_of_mem hx

def winB (c : Cond) : Bool := c.enc == 0 || c.enc == 1 || c.enc == 6

def tdSlice (e : Nat) : List Cond → Bool
  | [w] => e != 1 || allB winB w
  | _ => false

theorem tdSlice_sound {e : Nat} : ∀ {ch : List Cond}, tdSlice e ch = true →
    ∃ w, ch = [w] ∧ (e = 1 → allB winB w = true)
  | [w], h => ⟨w, rfl, fun h1 => by
      unfold tdSlice at h; simp only [Bool.or_eq_true, bne_iff_ne, ne_eq] at h
      exact h.resolve_left (· h1)⟩
  | [], h => by cases h
  | _ :: _ :: _, h => by cases h

/-- `TD`, as a Boolean. -/
def tdB : Cond → Bool
  | ⟨e, o, cv, ch⟩ =>
    (e == 5 && o != 1 && o != 2) ||
    (o == 13 && (e == 1 || e == 2) && tdSlice e ch) ||
    (!navOp o && (e == 1 || e == 2 || e == 3 || e == 4) && ch.attach.all fun ⟨x, _⟩ => tdB x)
termination_by c => sizeOf c
decreasing_by
  simp_wf
  have := List.sizeOf_lt_of_mem ‹_ ∈ ch›
  omega

theorem tdB_sound : ∀ c, tdB c = true → TD c
  | ⟨e, o, cv, ch⟩, h => by
    rw [tdB] at h
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at h
    rcases h with (h | h) | h
    · exact .abi h.1.1 h.1.2 h.2
    · obtain ⟨⟨h13, he⟩, hw⟩ := h
      obtain ⟨w, hw1, hw2⟩ := tdSlice_sound hw
      subst hw1
      exact .slice h13 he rfl fun h1 => AllN.imp (fun c hc => by
        unfold winB at hc; unfold winEnc
        simp only [Bool.or_eq_true, beq_iff_eq] at hc; omega) (allB_sound w (hw2 h1))
    · obtain ⟨⟨hn, he⟩, hall⟩ := h
      simp only [Bool.not_eq_true'] at hn
      rw [List.all_eq_true] at hall
      exact .node hn (by dsimp only; omega) fun x hx => tdB_sound x (hall ⟨x, hx⟩ (List.mem_attach _ _))
termination_by c => sizeOf c
decreasing_by exact Normalize.sizeOf_lt_of_mem hx

section
variable (avatar : Bytes)

def layB (a b : Cond) : Bool := isInl a == isInl b && (!isInl a || rawSz avatar a == rawSz avatar b)
def zB (x : Cond) : Bool := isInl x && rawSz avatar x == 0

theorem layB_sound {a b : Cond} (h : layB avatar a b = true) : LayR avatar a b := by
  unfold layB at h
  simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true, Bool.not_eq_true'] at h
  exact ⟨h.1, fun hi => h.2.resolve_left (by rw [hi]; decide)⟩

theorem zB_sound {x : Cond} (h : zB avatar x = true) : Z avatar x := by
  unfold zB at h; simp only [Bool.and_eq_true, beq_iff_eq] at h; exact h

def adOkB (c : Cond) : Bool :=
  (ConditionPacking.opOf? c.op).isSome &&
  (!(c.op == 5 && (c.enc == 3 || c.enc == 5)) || c.ch.all isStruct) &&
  (c.op != 13 || c.ch.all fun x => x.ch.isEmpty && !navOp x.op) &&
  (!(c.op == 10 || c.op == 11) ||
    match c.ch with
    | t :: _ => t.op == 5 && t.enc == 3 && t.ch.all isStruct
    | [] => false)

theorem adOkB_sound {c : Cond} (h : adOkB c = true) : adOk c := by
  unfold adOkB at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff,
    bne_iff_ne, ne_eq, beq_iff_eq, List.all_eq_true, Bool.or_eq_false_iff, beq_eq_false_iff_ne] at h
  obtain ⟨⟨⟨h0, h5⟩, h13⟩, hz⟩ := h
  refine ⟨h0, fun ho he => ?_, fun ho => ?_, fun ho => ?_⟩
  · rcases h5 with h5 | h5
    · rcases h5 with h5 | h5
      · exact absurd ho h5
      · omega
    · exact h5
  · rcases h13 with h13 | h13
    · exact absurd ho h13
    · intro x hx
      have := h13 x hx
      simp only [Bool.and_eq_true, List.isEmpty_iff, Bool.not_eq_true'] at this
      exact this
  · rcases hz with hz | hz
    · omega
    · split at hz
      · rename_i t rest hch
        simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hz
        exact ⟨t, rest, hch, hz.1.1, hz.1.2, hz.2⟩
      · cases hz

/-- `invP`, as a Boolean. -/
def invPB (c : Cond) : Bool :=
  adOkB c &&
  (!(c.op == 1 || c.op == 2) ||
    (c.enc == 0 &&
     (c.ch.all fun x => c.ch.all fun y => !isStruct x || !isStruct y || layB avatar x y) &&
     (c.ch.all fun x => isStruct x || zB avatar x || c.ch.any fun y => isStruct y && !isInl y))) &&
  (!descOp c.op || c.ch.all tdB) &&
  ((c.op == 1 || c.op == 2) || keepsAsWritten c || (c.ch.all isStruct && (c.enc != 3 || !c.ch.isEmpty))) &&
  (!isStruct c || !isInl c || decide (0 < rawSz avatar c))

theorem invPB_sound {c : Cond} (h : invPB avatar c = true) : invP avatar c := by
  unfold invPB at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨ha, hl⟩, hd⟩, hn⟩, hp⟩ := h
  have hlog : isLog c → (c.op == 1 || c.op == 2) = true := fun h => by
    rcases h with h | h <;> simp [h]
  have hl' : isLog c → _ := fun h => by
    have := hlog h
    rw [this] at hl
    simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true, beq_iff_eq, List.all_eq_true,
      Bool.or_eq_true, Bool.not_eq_true', List.any_eq_true] at hl
    exact hl
  refine ⟨adOkB_sound ha, fun h => (hl' h).1.1, fun h => ⟨fun x hx y hy sx sy => ?_, fun x hx sx => ?_⟩,
    fun h => ?_, fun h hk => ?_, fun hs hi => ?_⟩
  · have := (hl' h).1.2 x hx y hy
    rw [sx, sy] at this
    exact layB_sound avatar (by simpa using this)
  · have := (hl' h).2 x hx
    rw [sx] at this
    simp only [Bool.false_eq_true, false_or] at this
    rcases this with hz | ⟨y, hy, hys, hyi⟩
    · exact .inl (zB_sound avatar hz)
    · exact .inr ⟨y, hy, hys, hyi⟩
  · rw [h] at hd; simp only [Bool.not_true, Bool.false_or, List.all_eq_true] at hd
    exact fun x hx => tdB_sound x (hd x hx)
  · have h12 : (c.op == 1 || c.op == 2) = false := by
      unfold isLog at h; simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne]; omega
    rw [h12, hk] at hn
    simp only [Bool.false_or, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, bne_iff_ne,
      ne_eq, Bool.not_eq_true', List.isEmpty_eq_false_iff] at hn
    exact ⟨hn.1, fun he => hn.2.resolve_left fun h' => h' he⟩
  · rw [hs, hi] at hp; simpa using hp

/-- **`inv`, decided.** -/
def invB (c : Cond) : Bool := allB (invPB avatar) c

theorem invB_sound {c : Cond} (h : invB avatar c = true) : inv avatar c :=
  AllN.imp (fun _ hc => invPB_sound avatar hc) (allB_sound c h)

end
end Bridge
