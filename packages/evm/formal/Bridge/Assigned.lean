import Bridge.Pipeline
import ConditionCheck.Stored

/-!
# The SDK check's slot rule gives `za`

`za` is Integrity's Pluck-slot rule (`_validatePluckAssignments`,
`ConditionCheck.assigned`) for Zips only. Where `assigned` accepts the node
the evaluator runs, `za` accepts the tree (`za_of_assigned`). So the slot
hypotheses of `sdk_pipeline` hold when Integrity's rule accepts the tree as
written and the SDK check (`checkStored`) accepts the stored one
(`sdk_pipeline_checked`).
-/

namespace Bridge
open DecoderFaithfulness DecoderFaithfulness.Roles Normalize Evaluate ConditionPacking

/-- The Pluck and Zip nodes `za` reaches are not on calldata (so their
    compValue is the SDK's). -/
inductive KeyPlain : Cond → Prop
  | mk {c : Cond} : ((c.op = 14 ∨ c.op = 10 ∨ c.op = 11) → c.enc ≠ 5) →
      ((c.op = 1 ∨ c.op = 2 ∨ c.op = 5 ∨ c.op = 6 ∨ c.op = 7 ∨ c.op = 8 ∨ c.op = 13) →
        ∀ x ∈ c.ch, KeyPlain x) →
      ((c.op = 10 ∨ c.op = 11) → ∀ t ∈ c.ch, ∀ y ∈ t.ch, KeyPlain y) → KeyPlain c

theorem KeyPlain.self {c : Cond} (h : KeyPlain c) : (c.op = 14 ∨ c.op = 10 ∨ c.op = 11) → c.enc ≠ 5 := by
  cases h; assumption
theorem KeyPlain.ch {c : Cond} (h : KeyPlain c)
    (ho : c.op = 1 ∨ c.op = 2 ∨ c.op = 5 ∨ c.op = 6 ∨ c.op = 7 ∨ c.op = 8 ∨ c.op = 13) :
    ∀ x ∈ c.ch, KeyPlain x := by
  cases h with | mk _ h _ => exact h ho
theorem KeyPlain.fields {c : Cond} (h : KeyPlain c) (ho : c.op = 10 ∨ c.op = 11) :
    ∀ t ∈ c.ch, ∀ y ∈ t.ch, KeyPlain y := by
  cases h with | mk _ _ h => exact h ho

section
variable (avatar : Bytes)

theorem isPlain_opN {o : Nat} (h1 : o ≠ 1) (h2 : o ≠ 2) (h5 : o ≠ 5) (h6 : o ≠ 6) (h7 : o ≠ 7)
    (h8 : o ≠ 8) (h10 : o ≠ 10) (h11 : o ≠ 11) (h13 : o ≠ 13) (h14 : o ≠ 14) (h23 : o ≠ 23) :
    ConditionCheck.isPlain (opN o) = true := by
  unfold opN
  split
  · rfl
  · unfold ConditionPacking.opOf?
    split <;> simp_all [ConditionCheck.isPlain]

theorem cvByte_toBytes (cv : List Nat) (i : Nat) : cvByte (toBytes cv) i = cv.getD i 0 % 256 := by
  unfold cvByte toBytes
  by_cases h : i < cv.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : cv.length ≤ i)]

theorem zipSlots_toBytes (cv : List Nat) : ConditionCheck.zipSlots (toBytes cv) = zipKeys cv := by
  unfold ConditionCheck.zipSlots zipKeys
  apply List.ext_getElem
  · simp [toBytes]
  · intro i h1 h2
    simp only [List.getElem_map, List.getElem_range, cvByte_toBytes]
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using h2 : i < cv.length)]

/-- What `za_of_assigned` says of one tree. -/
def ZaQ (x : Cond) : Prop :=
  KeyPlain x → ∀ A A' B, ConditionCheck.SubS A A' → ConditionCheck.assigned (D avatar x) A = some B →
    ∃ B', za x A' = some B' ∧ ConditionCheck.SubS B B'

theorem seqL : ∀ (cs : List Cond), (∀ x ∈ cs, ZaQ avatar x) → (∀ x ∈ cs, KeyPlain x) →
    ∀ A A' B, ConditionCheck.SubS A A' → ConditionCheck.assignedSeq (cs.map (D avatar)) A = some B →
    ∃ B', zaSeq cs A' = some B' ∧ ConditionCheck.SubS B B'
  | [], _, _, A, A', B, hs, h => by
    simp only [List.map_nil, ConditionCheck.assignedSeq, Option.some.injEq] at h
    subst h; exact ⟨A', by rw [zaSeq], hs⟩
  | x :: xs, hq, hk, A, A', B, hs, h => by
    simp only [List.map_cons, ConditionCheck.assignedSeq, Option.bind_eq_some_iff] at h
    obtain ⟨a, ha, hb⟩ := h
    obtain ⟨a', ha', hsa⟩ := hq x (by simp) (hk x (by simp)) A A' a hs ha
    obtain ⟨b', hb', hsb⟩ := seqL xs (fun y hy => hq y (by simp [hy])) (fun y hy => hk y (by simp [hy]))
      a a' B hsa hb
    exact ⟨b', by rw [zaSeq, ha']; exact hb', hsb⟩

theorem orL : ∀ (cs : List Cond), (∀ x ∈ cs, ZaQ avatar x) → (∀ x ∈ cs, KeyPlain x) →
    ∀ A A' B, ConditionCheck.SubS A A' → ConditionCheck.assignedOr (cs.map (D avatar)) A = some B →
    ∃ B', zaOr cs A' = some B' ∧ ConditionCheck.SubS B B'
  | [], _, _, A, A', B, _, h => by
    simp only [List.map_nil, ConditionCheck.assignedOr, Option.some.injEq] at h
    subst h; exact ⟨fun _ => false, by rw [zaOr], fun _ h => h⟩
  | [x], hq, hk, A, A', B, hs, h => by
    simp only [List.map_cons, List.map_nil, ConditionCheck.assignedOr] at h
    obtain ⟨b', hb', hsb⟩ := hq x (by simp) (hk x (by simp)) A A' B hs h
    exact ⟨b', by rw [zaOr]; exact hb', hsb⟩
  | x :: x' :: xs, hq, hk, A, A', B, hs, h => by
    simp only [List.map_cons, ConditionCheck.assignedOr, Option.bind_eq_some_iff,
      Option.map_eq_some_iff] at h
    obtain ⟨a, ha, b, hb, rfl⟩ := h
    obtain ⟨a', ha', hsa⟩ := hq x (by simp) (hk x (by simp)) A A' a hs ha
    obtain ⟨b', hb', hsb⟩ := orL (x' :: xs) (fun y hy => hq y (List.mem_cons_of_mem _ hy))
      (fun y hy => hk y (List.mem_cons_of_mem _ hy)) A A' b hs (by simpa using hb)
    refine ⟨fun j => a' j && b' j, by rw [zaOr, ha']; simp [hb'], fun j hj => ?_⟩
    simp only [Bool.and_eq_true] at hj ⊢
    exact ⟨hsa j hj.1, hsb j hj.2⟩

theorem firstL (cs : List Cond) (hq : ∀ x ∈ cs, ZaQ avatar x) (hk : ∀ x ∈ cs, KeyPlain x)
    (A A' B : Nat → Bool) (hs : ConditionCheck.SubS A A')
    (h : ConditionCheck.assignedFirst (cs.map (D avatar)) A = some B) :
    ∃ B', zaFirst cs A' = some B' ∧ ConditionCheck.SubS B B' := by
  cases cs with
  | nil =>
    simp only [List.map_nil, ConditionCheck.assignedFirst, Option.some.injEq] at h
    subst h; exact ⟨A', by rw [zaFirst], hs⟩
  | cons x xs =>
    simp only [List.map_cons, ConditionCheck.assignedFirst] at h
    obtain ⟨b', hb', hsb⟩ := hq x (by simp) (hk x (by simp)) A A' B hs h
    exact ⟨b', by rw [zaFirst_cons]; exact hb', hsb⟩

theorem height_lt_of_mem {c x : Cond} {N : Nat} (h : height c ≤ N + 1) (hx : x ∈ c.ch) : height x ≤ N := by
  have := height_mem hx; omega

/-- **Integrity's slot rule gives `za`.** -/
theorem za_of_assigned : ∀ (N : Nat) (c : Cond), height c ≤ N → ZaQ avatar c
  | 0, c, hh => by have := height_pos c; omega
  | N + 1, c, hh => by
    intro hkp A A' B hs h
    have hq : ∀ x ∈ c.ch, ZaQ avatar x := fun x hx => za_of_assigned N x (height_lt_of_mem hh hx)
    have hself := hkp.self
    rw [ConditionCheck.assigned_eq, D_operator, D_children, D_compValue] at h
    rw [za_eq]
    by_cases h14 : c.op = 14
    · have hcv : cvOf avatar c = toBytes c.cv := cvOf_plain avatar (by omega) (by omega) (hself (.inl h14))
      rw [h14] at h; simp only [show opN 14 = .Pluck from rfl, ite_true, Option.some.injEq] at h
      subst h
      refine ⟨_, if_pos h14, fun j hj => ?_⟩
      rw [hcv, cvByte_toBytes] at hj
      simp only [ConditionCheck.Slots.add, Bool.or_eq_true, beq_iff_eq] at hj ⊢
      rcases hj with hj | hj
      · left; rw [hj]; cases c.cv <;> simp
      · exact .inr (hs j hj)
    rw [if_neg h14]
    by_cases hz : c.op = 10 ∨ c.op = 11
    · have hcv : cvOf avatar c = toBytes c.cv := cvOf_plain avatar (by omega) (by omega) (hself (.inr hz))
      have hop : opN c.op ≠ .Pluck ∧ opN c.op ≠ .WithinRatio ∧ (opN c.op = .ZipSome ∨ opN c.op = .ZipEvery) ∧
          (opN c.op = .ZipSome ↔ c.op = 10) := by
        rcases hz with h | h <;> rw [h] <;> decide
      rw [if_neg hop.1, if_neg hop.2.1, if_pos hop.2.2.1, hcv, zipSlots_toBytes] at h
      rw [if_pos hz]
      split at h
      case isFalse => cases h
      rename_i hall
      have hall' : (zipKeys c.cv).all A' = true := by
        rw [List.all_eq_true] at hall ⊢; exact fun k hk' => hs k (hall k hk')
      rw [if_pos hall']
      obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.1 h
      -- the fields: the children of the tuple child
      have hf : ∃ a', zaFields c.ch A' = some a' ∧ ConditionCheck.SubS a a' := by
        cases hch : c.ch with
        | nil =>
          rw [hch] at ha
          simp only [List.map_nil, ConditionCheck.assignedFields, Option.some.injEq] at ha
          subst ha; exact ⟨A', by rw [zaFields], hs⟩
        | cons t ts =>
          have ht : t ∈ c.ch := by rw [hch]; simp
          rw [hch, List.map_cons, ConditionCheck.assignedFields_eq] at ha
          simp only [List.headD_cons, D_children] at ha
          rw [zaFields_cons]
          exact seqL avatar t.ch
            (fun y hy => za_of_assigned N y (by
              have h1 := height_mem hy; have h2 := height_mem ht; omega))
            (fun y hy => hkp.fields hz t ht y hy) A A' a hs ha
      obtain ⟨a', ha', hsa⟩ := hf
      refine ⟨_, by rw [ha']; rfl, fun j hj => ?_⟩
      by_cases h10 : c.op = 10
      · simp only [hop.2.2.2.2 h10, ite_true, h10] at hj ⊢; exact hsa j hj
      · have : ¬ opN c.op = .ZipSome := fun e => h10 (hop.2.2.2.1 e)
        simp only [this, ite_false, h10] at hj ⊢; exact hs j hj
    rw [if_neg hz]
    by_cases h2 : c.op = 2
    · rw [h2] at h; simp only [show opN 2 = .Or from rfl] at h
      simp only [reduceCtorEq, ite_false, ite_true, false_or] at h
      rw [if_pos h2]
      exact orL avatar c.ch hq (hkp.ch (by omega)) A A' B hs h
    rw [if_neg h2]
    by_cases h67 : c.op = 6 ∨ c.op = 7
    · have hop : (opN c.op = .ArraySome ∨ opN c.op = .ArrayEvery) ∧ (opN c.op = .ArraySome ↔ c.op = 6) ∧
          opN c.op ≠ .Pluck ∧ opN c.op ≠ .WithinRatio ∧ ¬(opN c.op = .ZipSome ∨ opN c.op = .ZipEvery) ∧
          opN c.op ≠ .Or := by
        rcases h67 with h | h <;> rw [h] <;> decide
      rw [if_neg hop.2.2.1, if_neg hop.2.2.2.1, if_neg hop.2.2.2.2.1, if_neg hop.2.2.2.2.2,
        if_pos hop.1] at h
      rw [if_pos h67]
      obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.1 h
      obtain ⟨a', ha', hsa⟩ := firstL avatar c.ch hq (hkp.ch (by omega)) A A' a hs ha
      refine ⟨_, by rw [ha']; rfl, fun j hj => ?_⟩
      by_cases h6 : c.op = 6
      · simp only [hop.2.1.2 h6, ite_true, h6] at hj ⊢; exact hsa j hj
      · have : ¬ opN c.op = .ArraySome := fun e => h6 (hop.2.1.1 e)
        simp only [this, ite_false, h6] at hj ⊢; exact hs j hj
    rw [if_neg h67]
    by_cases h158 : c.op = 1 ∨ c.op = 5 ∨ c.op = 8
    · have hop : (opN c.op = .And ∨ opN c.op = .Matches ∨ opN c.op = .ArrayTailMatches) ∧
          opN c.op ≠ .Pluck ∧ opN c.op ≠ .WithinRatio ∧ ¬(opN c.op = .ZipSome ∨ opN c.op = .ZipEvery) ∧
          opN c.op ≠ .Or ∧ ¬(opN c.op = .ArraySome ∨ opN c.op = .ArrayEvery) := by
        rcases h158 with h | h | h <;> rw [h] <;> decide
      rw [if_neg hop.2.1, if_neg hop.2.2.1, if_neg hop.2.2.2.1, if_neg hop.2.2.2.2.1,
        if_neg hop.2.2.2.2.2, if_pos hop.1] at h
      rw [if_pos h158]
      exact seqL avatar c.ch hq (hkp.ch (by omega)) A A' B hs h
    rw [if_neg h158]
    by_cases h13 : c.op = 13
    · rw [h13] at h; simp only [show opN 13 = .Slice from rfl] at h
      simp only [reduceCtorEq, ite_false, ite_true, false_or, or_false, or_self] at h
      rw [if_pos h13]
      exact firstL avatar c.ch hq (hkp.ch (by omega)) A A' B hs h
    rw [if_neg h13]
    by_cases h23 : c.op = 23
    · rw [h23] at h; simp only [show opN 23 = .WithinRatio from rfl] at h
      simp only [reduceCtorEq, ite_false, ite_true] at h
      split at h
      · cases h; exact ⟨A', rfl, hs⟩
      · cases h
    have hp := isPlain_opN (o := c.op) (by omega) h2 (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) h13 h14 h23
    have hplain : ConditionCheck.assigned (D avatar c) A = some A := ConditionCheck.assigned_plain
      (by rw [D_operator]; exact hp)
    rw [ConditionCheck.assigned_eq, D_operator, D_children, D_compValue] at hplain
    rw [hplain] at h
    cases h
    exact ⟨A', rfl, hs⟩

theorem NsOk.keyPlain {c : Cond} (h : NsOk c) : KeyPlain c := by
  induction h with
  | @leaf c he hch _ =>
    exact .mk (fun _ => by omega) (fun _ x hx => by rw [hch] at hx; cases hx)
      (fun _ t ht => by rw [hch] at ht; cases ht)
  | @logical c hop he _ ih =>
    exact .mk (fun _ => by omega) (fun _ => ih) (fun h => by omega)

variable (P : Nat → Option Condition) in
/-- A tree that fits a layout has its Pluck and Zip nodes off calldata. -/
theorem Fits.keyPlain {c : Cond} {d m : Condition} (h : Fits avatar P c d m) : KeyPlain c := by
  induction h with
  | pass hop => exact .mk (fun _ => by omega) (fun h => by omega) (fun h => by omega)
  | ns _ hns => exact hns.keyPlain
  | logical hop he _ _ _ _ _ ih => exact .mk (fun _ => by omega) (fun _ => ih) (fun h => by omega)
  | tup h5 he _ _ _ _ _ _ _ _ ih =>
    refine .mk (fun _ => by omega) (fun _ x hx => ?_) (fun h => by omega)
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    exact ih i hi
  | arr hop _ _ _ _ _ _ _ _ ih => exact .mk (fun _ => by omega) (fun _ => ih) (fun h => by omega)
  | slice hop _ _ _ hch _ _ _ _ ih =>
    refine .mk (fun _ => by omega) (fun _ y hy => ?_) (fun h => by omega)
    rw [hch] at hy; simp at hy; subst hy; exact ih 0
  | leaf hop _ _ _ henc =>
    unfold leafOp at hop
    simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq] at hop
    exact .mk (fun _ => henc) (fun h => by omega) (fun h => by omega)
  | varAbi _ _ _ _ _ _ _ _ _ _ ih => exact ih
  | varDyn _ _ _ _ ih => exact ih
  | @zip c d m t hop he _ hch _ _ _ hlen _ hPs _ _ ih =>
    refine .mk (fun _ => by omega) (fun h => by omega) (fun _ t' ht' y hy => ?_)
    rw [hch] at ht'; simp at ht'; subst ht'
    obtain ⟨f, hf, rfl⟩ := List.getElem_of_mem hy
    have hfc : f < c.cv.length := by omega
    obtain ⟨ma, hma⟩ := Option.isSome_iff_exists.1 (hPs _ (List.getElem_mem hfc))
    have hg : c.cv.getD f 0 = c.cv[f] := by simp [List.getD_eq_getElem?_getD, hfc]
    exact ih f hf ma (by rw [hg]; exact hma)
  | zipLogical hop he _ _ _ _ _ ih => exact .mk (fun _ => by omega) (fun _ => ih) (fun h => by omega)

end

section
variable (avatar : Bytes) (env : Env) (henv : EnvOk env) (data : Calldata)
  (P : Nat → Option Condition)

theorem za_isSome {c : Cond} {d m : Condition} (h : Fits avatar P c d m)
    (ha : (ConditionCheck.assigned (D avatar c) fun _ => false).isSome) : (za c fun _ => false).isSome := by
  obtain ⟨B, hB⟩ := Option.isSome_iff_exists.1 ha
  obtain ⟨B', hB', -⟩ := za_of_assigned avatar (height c) c (Nat.le_refl _) (h.keyPlain avatar P)
    _ _ B (fun _ h => h) hB
  rw [hB']; rfl

include henv in
/-- **The SDK pipeline keeps the contract's verdict, for trees the check
    accepts.** As `sdk_pipeline`, for a user tree that Integrity's Pluck rule
    accepts, stored after the SDK check (`checkStored`) accepted it. -/
theorem sdk_pipeline_checked (c0 : Cond) (k : Nat) (fs : List Flat) (s : Bool)
    {v : ConditionCheck.Verdict} (hchk : ConditionCheck.checkStored s fs = some v)
    (hfs : nest fs 0 = normalize k c0) {m : Condition} (hfit : Fits avatar P c0 (D avatar c0) m)
    (hdec : Decodable data m 0) (junk junk' : Mem) {tree : Condition} {mp : Nat}
    (hu : unpack avatar (bufMem (pack junk fs) junk') = some (tree, mp)) (hcv : CvOk mp c0)
    (hint : (ConditionCheck.assigned (D avatar c0) fun _ => false).isSome) :
    Agree (run env data (D avatar c0) mp []) (run env data tree mp []) := by
  have hsound := ConditionCheck.checkStored_sound hchk avatar junk junk'
  have hP : Packable fs := hsound.1
  have hasg : (ConditionCheck.assigned (ConditionCheck.treeOf fs) fun _ => false).isSome := by
    unfold ConditionCheck.checkStored at hchk
    split at hchk
    · rename_i hc; simp only [Bool.and_eq_true] at hc; exact hc.2
    · cases hchk
  have hasg' : (ConditionCheck.assigned (D avatar (normalize k c0)) fun _ => false).isSome := by
    rw [← hfs, ← unpacked_eq avatar fs hP 0, ConditionCheck.assigned_annotate,
      ConditionCheck.assigned_avatar avatar (zeros 32)]
    exact hasg
  exact sdk_pipeline avatar env henv data P c0 k fs hP hfs hfit hdec junk junk' hu hcv
    (za_isSome avatar P hfit hint)
    (za_isSome avatar P (normalize_fits avatar P k c0 m hfit) hasg')

end
end Bridge
