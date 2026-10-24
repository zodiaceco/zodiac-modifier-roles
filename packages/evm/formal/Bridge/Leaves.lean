import Bridge.Adequacy

/-!
# Adequacy for the operators that read one value

Comparisons, `Bitmask`, `Pluck`, `Custom`, the allowances, `WithinRatio`
and `Empty`: each read the node's value (through `__input`, or the layout's
`inlined`/`size`) and the compValue. Given that the node and the layout agree
on what is read, the evaluator and the world agree.
-/

namespace Bridge
open DecoderFaithfulness DecoderFaithfulness.Roles Normalize Evaluate

section
variable (env : Env) (data : Calldata) (n f l : Nat) (d : Condition) (cons : List Consumption)
  (sl : Slots)

/-! ## `evaluate` by operator -/

theorem evalC_cmp {op : Operator} (hd : d.operator = op)
    (hop : op = .EqualTo ∨ op = .GreaterThan ∨ op = .LessThan ∨ op = .SignedIntGreaterThan ∨
      op = .SignedIntLessThan) :
    evalC env data n (f + 1) l d cons sl =
      match input data l d with
      | .overflow => violation sCalldataOverflow sl
      | v => result (compare op (inputB env v) d.compValue) cons sl := by
  rw [evalC, hd]
  rcases hop with rfl | rfl | rfl | rfl | rfl <;> rfl

theorem evalC_bitmask (hd : d.operator = .Bitmask) :
    evalC env data n (f + 1) l d cons sl =
      result (bitmaskStatus (bitmaskCheck data l d.compValue d.inlined d.size [])) cons sl := by
  rw [evalC, hd]

theorem evalC_empty (hd : d.operator = .Empty) :
    evalC env data n (f + 1) l d cons sl =
      result (if data.length = 0 then sOk else sCalldataNotEmpty) cons sl := by
  rw [evalC, hd]

theorem evalC_ratio (hd : d.operator = .WithinRatio) :
    evalC env data n (f + 1) l d cons sl = result (env.ratio d.compValue sl.values) cons sl := by
  rw [evalC, hd]

theorem evalC_cwa (hd : d.operator = .CallWithinAllowance) :
    evalC env data n (f + 1) l d cons sl =
      result (allowance env cons 1 d.compValue).1 (allowance env cons 1 d.compValue).2 sl := by
  rw [evalC, hd]

theorem evalC_wa (hd : d.operator = .WithinAllowance) :
    evalC env data n (f + 1) l d cons sl =
      match input data l d with
      | .overflow => violation sCalldataOverflow sl
      | v => result (allowance env cons (match inputB env v with
          | .w x => x
          | .h _ => 0) d.compValue).1
          (allowance env cons (match inputB env v with
          | .w x => x
          | .h _ => 0) d.compValue).2 sl := by
  rw [evalC, hd]; rfl

theorem evalC_custom (hd : d.operator = .Custom) :
    evalC env data n (f + 1) l d cons sl =
      match env.customCall d.compValue l (if d.size ≠ 0 then d.size else size data l d)
          sl.values with
      | .inl s => violation s sl
      | .inr chs => result (applyCharges env cons chs).1 (applyCharges env cons chs).2 sl := by
  rw [evalC, hd]; rfl

theorem evalC_pluck (hd : d.operator = .Pluck) :
    evalC env data n (f + 1) l d cons sl =
      match input data l d with
      | .overflow => violation sCalldataOverflow sl
      | v =>
        match cvAt d.compValue 0 with
        | none => violation revert sl
        | some k =>
          if k ≥ n then violation revert sl else
          ok cons ⟨fun j => if j = k then (match v with
                      | .etherValue => .word env.value
                      | v => v) else sl.values j,
                   fun j => if j = k then l else sl.locations j⟩ := by
  rw [evalC, hd]; rfl

end

/-! ## Consumptions through charges -/

theorem applyCharges_toMap (env : Env) : ∀ (cons : List Consumption) (chs : List (Bytes × Nat)),
    applyL (consumeM env.balance) (toMap cons) chs =
      if (applyCharges env cons chs).1 = sOk then some (toMap (applyCharges env cons chs).2)
      else none
  | cons, [] => by simp [applyL, applyCharges]
  | cons, (k, a) :: rest => by
    simp only [applyL, applyCharges]
    rw [consume_toMap]
    by_cases h : (Evaluate.consume env cons k a).1 = sOk
    · simp only [h, if_true, Option.bind_some, ne_eq, not_true_eq_false, ite_false]
      exact applyCharges_toMap env _ rest
    · simp only [h, ite_false, Option.bind_none, ne_eq, not_false_eq_true, if_true]

theorem applyCharges_status (env : Env) : ∀ (cons : List Consumption) (chs : List (Bytes × Nat)),
    (applyCharges env cons chs).1 ≠ revert
  | cons, [] => by simp [applyCharges, sOk, revert]
  | cons, (k, a) :: rest => by
    simp only [applyCharges]
    split
    · rename_i h
      rw [(consume_keeps env cons k a h).2]; decide
    · exact applyCharges_status env _ rest

theorem allowance_eq (env : Env) (cons : List Consumption) (v : Nat) (cv : Bytes) :
    allowance env cons v cv =
      if cv.length = 32 then Evaluate.consume env cons (key cv) v
      else if (env.scale cv v).1 = sOk then Evaluate.consume env cons (key cv) (env.scale cv v).2
      else ((env.scale cv v).1, cons) := by
  unfold allowance
  by_cases h32 : cv.length = 32
  · simp [h32]
  · by_cases hs : (env.scale cv v).1 = sOk <;> simp [h32, hs]

theorem consume_status (env : Env) (cons : List Consumption) (k : Bytes) (a : Nat) :
    (Evaluate.consume env cons k a).1 ≠ revert ∧
    (if (Evaluate.consume env cons k a).1 = sOk then some (toMap (Evaluate.consume env cons k a).2)
     else none) = consumeM env.balance (toMap cons) (k, a) := by
  rw [consume_toMap]
  refine ⟨?_, rfl⟩
  by_cases hs : (Evaluate.consume env cons k a).1 = sOk
  · rw [hs]; exact sOk_ne_revert
  · rw [(consume_keeps env cons k a hs).2]; decide

/-- `WithinAllowanceChecker.check` charges the map's `charge`. -/
theorem allowance_toMap (env : Env) (henv : EnvOk env) (cons : List Consumption) (v : Nat)
    (cv : Bytes) :
    (allowance env cons v cv).1 ≠ revert ∧
    (if (allowance env cons v cv).1 = sOk then some (toMap (allowance env cons v cv).2) else none) =
      ((charge env cv v).map ([·])).bind (applyL (consumeM env.balance) (toMap cons)) := by
  rw [allowance_eq]
  unfold charge
  by_cases h32 : cv.length = 32
  · simp only [h32, if_true, Option.map_some, Option.bind_some, applyL]
    have := consume_status env cons (key cv) v
    refine ⟨this.1, ?_⟩
    rw [this.2]; cases consumeM env.balance (toMap cons) (key cv, v) <;> rfl
  · simp only [h32, ite_false]
    by_cases hsc : (env.scale cv v).1 = sOk
    · simp only [hsc, if_true, Option.map_some, Option.bind_some, applyL]
      have := consume_status env cons (key cv) (env.scale cv v).2
      refine ⟨this.1, ?_⟩
      rw [this.2]; cases consumeM env.balance (toMap cons) (key cv, (env.scale cv v).2) <;> rfl
    · simp only [hsc, ite_false, Option.map_none, Option.bind_none]
      exact ⟨henv.scale cv v, trivial⟩

/-! ## Each operator -/

theorem compare_ne_revert (op : Operator) (v : B32) (cv : Bytes) :
    Evaluate.compare op v cv ≠ revert := by
  unfold Evaluate.compare
  repeat' split
  all_goals decide

theorem bitmaskStatus_ne_revert (b : BitmaskStatus) : bitmaskStatus b ≠ revert := by
  cases b <;> decide

theorem toOp_eq (o : Nat) : toOp o = opN o := rfl

section
variable (avatar : Bytes) (env : Env) (henv : EnvOk env) (data : Calldata) (n : Nat) (P : Nat → Option Condition) (f l : Nat)
  (d m : Condition) (e o : Nat) (cv : List Nat) (ss : List (Val' → T)) (cons : List Consumption)
  (sl : Slots)

theorem checkT_apply (b : Slots → Bool) (cs : CM) : checkT b sl cs = (if b sl then some cs else none, sl) :=
  rfl

theorem cmp_rel (ho : 15 ≤ o ∧ o ≤ 20) (hop : d.operator = opN o)
    (hin : input data l d = inputAt data e m l) (hcv : d.compValue = cmpValue avatar e o cv m) :
    Rel (evalC env data n (f + 1) l d cons sl)
      (extW avatar env data n P e o cv ss (m, l) sl (toMap cons)) := by
  have hext : extW avatar env data n P e o cv ss (m, l) =
      checkT fun _ => cmpOk avatar env data e o cv (m, l) := by
    obtain ⟨h1, h2⟩ := ho
    have : o = 15 ∨ o = 16 ∨ o = 17 ∨ o = 18 ∨ o = 19 ∨ o = 20 := by omega
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  have hopc : opN o = .EqualTo ∨ opN o = .GreaterThan ∨ opN o = .LessThan ∨
      opN o = .SignedIntGreaterThan ∨ opN o = .SignedIntLessThan := by
    obtain ⟨h1, h2⟩ := ho
    have : o = 15 ∨ o = 16 ∨ o = 17 ∨ o = 18 ∨ o = 19 ∨ o = 20 := by omega
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [opN, ConditionPacking.opOf?]
  rw [hext, checkT_apply, evalC_cmp env data n f l d cons sl hop hopc]
  unfold cmpOk
  simp only
  rw [hin, hcv, toOp_eq]
  cases inputAt data e m l with
  | overflow => exact Rel.violation (by decide) (by decide) sl
  | etherValue | word _ | hash _ =>
    simpa using Rel.result (compare_ne_revert _ _ _) cons sl

theorem bitmask_rel (hop : d.operator = .Bitmask) (hcv : d.compValue = toBytes cv)
    (hlay : d.inlined = m.inlined ∧ d.size = m.size) :
    Rel (evalC env data n (f + 1) l d cons sl)
      (extW avatar env data n P e 21 cv ss (m, l) sl (toMap cons)) := by
  rw [evalC_bitmask env data n f l d cons sl hop]
  show Rel _ (checkT (fun _ => bitmaskOk data cv (m, l)) sl (toMap cons))
  rw [checkT_apply]
  unfold bitmaskOk
  rw [hcv, hlay.1, hlay.2]
  simpa using Rel.result (bitmaskStatus_ne_revert _) cons sl

theorem empty_rel (hop : d.operator = .Empty) :
    Rel (evalC env data n (f + 1) l d cons sl)
      (extW avatar env data n P e 4 cv ss (m, l) sl (toMap cons)) := by
  rw [evalC_empty env data n f l d cons sl hop]
  show Rel _ (checkT (fun _ => data.length = 0) sl (toMap cons))
  rw [checkT_apply]
  by_cases h : data.length = 0
  · simpa [h] using Rel.result (s := sOk) (by decide) cons sl
  · have hne : sCalldataNotEmpty ≠ sOk := by decide
    simpa [h, hne] using Rel.result (s := sCalldataNotEmpty) (by decide) cons sl

include henv in
theorem ratio_rel (hop : d.operator = .WithinRatio) (hcv : d.compValue = toBytes cv) :
    Rel (evalC env data n (f + 1) l d cons sl)
      (extW avatar env data n P e 23 cv ss (m, l) sl (toMap cons)) := by
  rw [evalC_ratio env data n f l d cons sl hop]
  show Rel _ (checkT (fun sl => env.ratio (toBytes cv) sl.values = sOk) sl (toMap cons))
  rw [checkT_apply, hcv]
  simpa using Rel.result (henv.ratio _ _) cons sl

include henv in
theorem cwa_rel (hop : d.operator = .CallWithinAllowance) (hcv : d.compValue = toBytes cv) :
    Rel (evalC env data n (f + 1) l d cons sl)
      (extW avatar env data n P e 30 cv ss (m, l) sl (toMap cons)) := by
  rw [evalC_cwa env data n f l d cons sl hop]
  show Rel _ (chargesT env.balance (fun _ => (charge env (toBytes cv) 1).map ([·])) sl (toMap cons))
  unfold chargesT
  rw [hcv]
  have := allowance_toMap env henv cons 1 (toBytes cv)
  rw [← this.2]
  exact Rel.result this.1 _ sl

include henv in
theorem wa_rel (hop : d.operator = .WithinAllowance) (hcv : d.compValue = toBytes cv)
    (hin : input data l d = inputAt data e m l) :
    Rel (evalC env data n (f + 1) l d cons sl)
      (extW avatar env data n P e 28 cv ss (m, l) sl (toMap cons)) := by
  rw [evalC_wa env data n f l d cons sl hop]
  show Rel _ (chargesT env.balance (fun _ => allowanceCharge env data e cv (m, l)) sl (toMap cons))
  unfold chargesT allowanceCharge
  simp only
  rw [hin, hcv]
  cases inputAt data e m l with
  | overflow => exact Rel.violation (by decide) (by decide) sl
  | etherValue =>
    have := allowance_toMap env henv cons env.value (toBytes cv)
    simp only [inputB, amountOf]
    rw [← this.2]; exact Rel.result this.1 _ sl
  | word x =>
    have := allowance_toMap env henv cons x (toBytes cv)
    simp only [inputB, amountOf]
    rw [← this.2]; exact Rel.result this.1 _ sl
  | hash p =>
    have := allowance_toMap env henv cons 0 (toBytes cv)
    simp only [inputB, amountOf]
    rw [← this.2]; exact Rel.result this.1 _ sl

include henv in
theorem custom_rel (hop : d.operator = .Custom) (hcv : d.compValue = toBytes cv)
    (hcs : (if d.size ≠ 0 then d.size else size data l d) = customSize data e m l) :
    Rel (evalC env data n (f + 1) l d cons sl)
      (extW avatar env data n P e 22 cv ss (m, l) sl (toMap cons)) := by
  rw [evalC_custom env data n f l d cons sl hop]
  show Rel _ (chargesT env.balance (customCharges env data e cv (m, l)) sl (toMap cons))
  unfold chargesT customCharges
  simp only
  rw [hcv, hcs]
  rcases hc : env.customCall (toBytes cv) l (customSize data e m l) sl.values with s | chs
  · simp only [Option.bind_none]
    have := henv.custom _ _ _ _ s hc
    exact Rel.violation this.1 this.2 sl
  · simp only [Option.bind_some]
    rw [applyCharges_toMap]
    exact Rel.result (applyCharges_status env cons chs) _ sl

theorem cvAt_toBytes (cv : List Nat) : cvAt (toBytes cv) 0 = cv.head?.map (· % 256) := by
  cases cv <;> rfl

theorem pluck_rel (hop : d.operator = .Pluck) (hcv : d.compValue = toBytes cv)
    (hin : input data l d = inputAt data e m l) (hk : ∃ k ∈ cv.head?, k % 256 < n) :
    Rel (evalC env data n (f + 1) l d cons sl)
      (extW avatar env data n P e 14 cv ss (m, l) sl (toMap cons)) := by
  rw [evalC_pluck env data n f l d cons sl hop]
  show Rel _ (pluckT env data n e cv (m, l) sl (toMap cons))
  unfold pluckT
  simp only
  rw [hin, hcv, cvAt_toBytes]
  obtain ⟨k, hk1, hk2⟩ := hk
  rw [Option.mem_def] at hk1
  rw [hk1]
  simp only [Option.map_some]
  have hlt : ¬(k % 256 ≥ n) := by omega
  cases inputAt data e m l with
  | overflow => exact Rel.violation (by decide) (by decide) sl
  | etherValue | word _ | hash _ =>
    simp only [hlt, ite_false]
    refine ⟨rfl, ?_⟩
    simp [Evaluate.ok]

end
end Bridge
