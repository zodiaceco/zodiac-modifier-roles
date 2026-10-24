import Bridge.Corr

/-!
# Adequacy: the evaluator computes the world's meaning

`adequacy`: for a tree `c` whose layout fits `m` (`Fits`), on calldata
that decodes as `m` (`Decodable`), with compValues the evaluator does not
revert on (`CvOk`), the evaluator transcription (`Evaluate.evalC`) and the
contract world (`sem (contractWorld ..) c (m, l)`) give the same result:
pass with the same consumptions (as a map), or fail; and the same slots.
-/

namespace Bridge
open DecoderFaithfulness DecoderFaithfulness.Roles Normalize Evaluate

section
variable (avatar : Bytes)

/-! ## The node the evaluator runs -/

theorem toRoles_eq (c : Cond) :
    toRoles avatar c =
      ⟨encN c.enc, opN c.op, c.ch.map (toRoles avatar), false, 0, lbOf c, cvOf avatar c⟩ := by
  rcases c with ⟨e, o, cv, ch⟩
  rw [toRoles, toRolesL_eq]

theorem opOf_avatar {o : Nat} (h : ConditionPacking.opOf? o = some .EqualToAvatar) : o = 15 := by
  unfold ConditionPacking.opOf? at h
  split at h <;> simp_all

theorem opN_ne_avatar (o : Nat) : opN o ≠ .EqualToAvatar := by
  unfold opN
  split
  · simp
  · rename_i h15
    rcases hh : ConditionPacking.opOf? o with _ | op
    · simp
    · simp only [Option.getD_some]
      intro he
      subst he
      exact h15 (opOf_avatar hh)

theorem D_operator (c : Cond) : (D avatar c).operator = opN c.op := by
  unfold D
  rw [annotate_operator, toRoles_eq]
  simp [opN_ne_avatar]

theorem D_encoding (c : Cond) :
    (D avatar c).encoding = if encN c.enc = .EtherValue then .None else encN c.enc := by
  unfold D; rw [annotate_encoding, toRoles_eq]

theorem D_children (c : Cond) : (D avatar c).children = c.ch.map (D avatar) := by
  unfold D; rw [annotate_children, toRoles_eq]; simp

theorem D_compValue (c : Cond) : (D avatar c).compValue = cvOf avatar c := by
  unfold D; rw [annotate_compValue, toRoles_eq]

theorem D_leadingBytes (c : Cond) :
    (D avatar c).leadingBytes = if encN c.enc = .AbiEncoded then lbOf c else 0 := by
  unfold D; rw [annotate_leadingBytes, toRoles_eq]

theorem Node.operator {c : Cond} {d : Condition} (h : Node avatar c d) : d.operator = opN c.op := by
  rw [h]; exact D_operator avatar c
theorem Node.encoding {c : Cond} {d : Condition} (h : Node avatar c d) :
    d.encoding = (D avatar c).encoding := by rw [h]
theorem Node.compValue {c : Cond} {d : Condition} (h : Node avatar c d) :
    d.compValue = cvOf avatar c := by rw [h]; exact D_compValue avatar c
theorem Node.children {c : Cond} {d : Condition} (h : Node avatar c d) :
    d.children = c.ch.map (D avatar) := by rw [h]; exact D_children avatar c
theorem Node.inlined {c : Cond} {d : Condition} (h : Node avatar c d) :
    d.inlined = (D avatar c).inlined := by rw [h]
theorem Node.refl (c : Cond) : Node avatar c (D avatar c) := by
  unfold Node; cases D avatar c; rfl

end

/-! ## Height (the recursion depth `evaluate` needs) -/

mutual
  def height : Cond → Nat
    | ⟨_, _, _, ch⟩ => heightL ch + 1
  def heightL : List Cond → Nat
    | [] => 0
    | x :: xs => max (height x) (heightL xs)
end

theorem heightL_mem : ∀ {l : List Cond} {x : Cond}, x ∈ l → height x ≤ heightL l
  | _ :: _, _, .head _ => by simp only [heightL]; omega
  | _ :: _, _, .tail _ h => by simp only [heightL]; have := heightL_mem h; omega

theorem height_mem {c x : Cond} (h : x ∈ c.ch) : height x < height c := by
  rcases c with ⟨e, o, cv, ch⟩
  have := heightL_mem (l := ch) h
  simp only [height]; omega

/-! ## `CvOk` -/

theorem cvOk_eq (n : Nat) (c : Cond) :
    CvOk n c = ((c.op = 5 → (prefixOf c.enc c.cv).length ≤ 32) ∧ (c.op = 13 → 3 ≤ c.cv.length) ∧
      (c.op = 14 → ∃ k ∈ c.cv.head?, k % 256 < n) ∧ (c.op = 10 ∨ c.op = 11 → ∀ k ∈ c.cv, k % 256 < n) ∧
      ∀ x ∈ c.ch, CvOk n x) := by
  rcases c with ⟨e, o, cv, ch⟩
  rw [CvOk]

theorem CvOk.child {n : Nat} {c x : Cond} (h : CvOk n c) (hx : x ∈ c.ch) : CvOk n x := by
  rw [cvOk_eq] at h; exact h.2.2.2.2 x hx

end Bridge
