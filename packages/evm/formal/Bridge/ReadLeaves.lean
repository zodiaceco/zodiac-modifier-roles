import Bridge.ReadOk

/-!
# The evaluator on one node

What `evalC` returns for each operator that reads one value, and that it
agrees with the reading (`Rel`): the comparisons, `Bitmask`, `Pluck`,
`Custom`, the allowances, `WithinRatio` and `Empty`. The reading reads the
same node as the evaluator, so this is the operator's own arithmetic.
-/

namespace Bridge
open DecoderFaithfulness DecoderFaithfulness.Roles Normalize Evaluate

/-- What is assumed of the outside: the external calls never report `Ok`
    as a failure, nor a status that reads as a revert. -/
structure EnvOk (env : Env) : Prop where
  scale : ∀ cv n, (env.scale cv n).1 ≠ revert
  custom : ∀ cv l sz vals s, env.customCall cv l sz vals = .inl s → s ≠ sOk ∧ s ≠ revert
  ratio : ∀ cv vals, env.ratio cv vals ≠ revert

theorem sOk_ne_revert : sOk ≠ revert := by decide

theorem Rel.ok (cons : List Consumption) (sl : Slots) :
    Rel (Evaluate.ok cons sl) (some (toMap cons), sl) := by
  refine ⟨rfl, ?_⟩
  simp [Evaluate.ok]

theorem Rel.violation {s : Nat} (h1 : s ≠ sOk) (h2 : s ≠ revert) (sl : Slots) :
    Rel (violation s sl) (none, sl) := by
  simp [Rel, Evaluate.violation, h1, h2]

theorem Rel.result {s : Nat} (h : s ≠ revert) (cons : List Consumption) (sl : Slots) :
    Rel (result s cons sl) (if s = sOk then some (toMap cons) else none, sl) := by
  unfold Evaluate.result
  by_cases hs : s = sOk
  · simp only [hs, ite_true]; exact Rel.ok cons sl
  · simp only [hs, ite_false]; exact Rel.violation hs h sl

theorem Rel.status_ne {r : Res} {x : Option CM × Slots} (h : Rel r x) : r.status ≠ revert := by
  obtain ⟨-, h2⟩ := h
  split at h2
  · rename_i hs; rw [hs]; exact sOk_ne_revert
  · exact h2.1

/-- A result that passes or fails like `x`, as a world result. -/
theorem Rel.eq {r : Res} {x : Option CM × Slots} (h : Rel r x) :
    x = (if r.status = sOk then some (toMap r.cons) else none, r.slots) := by
  obtain ⟨h1, h2⟩ := h
  rcases x with ⟨x1, x2⟩
  simp only at h1 h2
  subst h1
  split at h2
  · rename_i hs; simp [hs, h2]
  · rename_i hs; simp [hs, h2.2]


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


theorem checkT_apply (b : Slots → Bool) (sl : Slots) (cs : CM) :
    checkT b sl cs = (if b sl then some cs else none, sl) := rfl

section
variable (avatar : Bytes) (env : Env) (henv : EnvOk env) (data : Calldata) (n f : Nat)
  (c : Cond) (ss : List (RV → T)) (v : RV) (cons : List Consumption) (sl : Slots)

/-- The reading of `c` at `v`, for an operator `ext` covers. -/
abbrev RX := readExt avatar env data n c ss v sl (toMap cons)
/-- The evaluator on the same node. -/
abbrev EX := evalC env data n (f + 1) v.loc (nodeAt avatar c v) cons sl

theorem nodeAt_operator : (nodeAt avatar c v).operator = opN c.op := by
  cases v <;> simp [nodeAt, D_operator]

theorem nodeAt_compValue : (nodeAt avatar c v).compValue = cvOf avatar c := by
  cases v <;> simp [nodeAt, D_compValue]

theorem cmp_rel (ho : 15 ≤ c.op ∧ c.op ≤ 20) :
    Rel (EX avatar env data n f c v cons sl) (RX avatar env data n c ss v cons sl) := by
  have hext : readExt avatar env data n c ss v = checkT fun _ => cmpOk env data (nodeAt avatar c v) v.loc := by
    unfold readExt
    obtain ⟨h1, h2⟩ := ho
    have : c.op = 15 ∨ c.op = 16 ∨ c.op = 17 ∨ c.op = 18 ∨ c.op = 19 ∨ c.op = 20 := by omega
    rcases this with h | h | h | h | h | h <;> simp [h]
  have hopc : opN c.op = .EqualTo ∨ opN c.op = .GreaterThan ∨ opN c.op = .LessThan ∨
      opN c.op = .SignedIntGreaterThan ∨ opN c.op = .SignedIntLessThan := by
    obtain ⟨h1, h2⟩ := ho
    have : c.op = 15 ∨ c.op = 16 ∨ c.op = 17 ∨ c.op = 18 ∨ c.op = 19 ∨ c.op = 20 := by omega
    rcases this with h | h | h | h | h | h <;> simp [h, opN, ConditionPacking.opOf?]
  show Rel (evalC env data n (f + 1) v.loc (nodeAt avatar c v) cons sl)
    (readExt avatar env data n c ss v sl (toMap cons))
  rw [hext, checkT_apply, evalC_cmp env data n f v.loc _ cons sl (nodeAt_operator avatar c v) hopc]
  unfold cmpOk
  rw [nodeAt_operator]
  cases input data v.loc (nodeAt avatar c v) with
  | overflow => exact Rel.violation (by decide) (by decide) sl
  | etherValue | word _ | hash _ =>
    simpa using Rel.result (compare_ne_revert _ _ _) cons sl

theorem bitmask_rel (ho : c.op = 21) :
    Rel (EX avatar env data n f c v cons sl) (RX avatar env data n c ss v cons sl) := by
  have hop : (nodeAt avatar c v).operator = .Bitmask := by
    rw [nodeAt_operator, ho]; rfl
  show Rel (evalC env data n (f + 1) v.loc (nodeAt avatar c v) cons sl)
    (readExt avatar env data n c ss v sl (toMap cons))
  rw [evalC_bitmask env data n f v.loc _ cons sl hop]
  unfold readExt; simp only [ho]
  rw [checkT_apply]
  simpa using Rel.result (bitmaskStatus_ne_revert _) cons sl

theorem empty_rel (ho : c.op = 4) :
    Rel (EX avatar env data n f c v cons sl) (RX avatar env data n c ss v cons sl) := by
  have hop : (nodeAt avatar c v).operator = .Empty := by rw [nodeAt_operator, ho]; rfl
  show Rel (evalC env data n (f + 1) v.loc (nodeAt avatar c v) cons sl)
    (readExt avatar env data n c ss v sl (toMap cons))
  rw [evalC_empty env data n f v.loc _ cons sl hop]
  unfold readExt; simp only [ho]
  unfold emptyT
  rw [checkT_apply]
  by_cases h : data.length = 0
  · simpa [h] using Rel.result (s := sOk) (by decide) cons sl
  · have hne : sCalldataNotEmpty ≠ sOk := by decide
    simpa [h, hne] using Rel.result (s := sCalldataNotEmpty) (by decide) cons sl

include henv in
theorem ratio_rel (ho : c.op = 23) :
    Rel (EX avatar env data n f c v cons sl) (RX avatar env data n c ss v cons sl) := by
  have hop : (nodeAt avatar c v).operator = .WithinRatio := by rw [nodeAt_operator, ho]; rfl
  show Rel (evalC env data n (f + 1) v.loc (nodeAt avatar c v) cons sl)
    (readExt avatar env data n c ss v sl (toMap cons))
  rw [evalC_ratio env data n f v.loc _ cons sl hop]
  unfold readExt; simp only [ho]
  rw [checkT_apply]
  simpa using Rel.result (henv.ratio _ _) cons sl

include henv in
theorem cwa_rel (ho : c.op = 30) :
    Rel (EX avatar env data n f c v cons sl) (RX avatar env data n c ss v cons sl) := by
  have hop : (nodeAt avatar c v).operator = .CallWithinAllowance := by rw [nodeAt_operator, ho]; rfl
  show Rel (evalC env data n (f + 1) v.loc (nodeAt avatar c v) cons sl)
    (readExt avatar env data n c ss v sl (toMap cons))
  rw [evalC_cwa env data n f v.loc _ cons sl hop]
  unfold readExt; simp only [ho]
  unfold chargesT
  have := allowance_toMap env henv cons 1 (nodeAt avatar c v).compValue
  rw [← this.2]
  exact Rel.result this.1 _ sl

include henv in
theorem wa_rel (ho : c.op = 28) :
    Rel (EX avatar env data n f c v cons sl) (RX avatar env data n c ss v cons sl) := by
  have hop : (nodeAt avatar c v).operator = .WithinAllowance := by rw [nodeAt_operator, ho]; rfl
  show Rel (evalC env data n (f + 1) v.loc (nodeAt avatar c v) cons sl)
    (readExt avatar env data n c ss v sl (toMap cons))
  rw [evalC_wa env data n f v.loc _ cons sl hop]
  unfold readExt; simp only [ho]
  unfold chargesT allowanceCharge
  cases input data v.loc (nodeAt avatar c v) with
  | overflow => exact Rel.violation (by decide) (by decide) sl
  | etherValue =>
    have := allowance_toMap env henv cons env.value (nodeAt avatar c v).compValue
    simp only [inputB, amountOf]
    rw [← this.2]; exact Rel.result this.1 _ sl
  | word x =>
    have := allowance_toMap env henv cons x (nodeAt avatar c v).compValue
    simp only [inputB, amountOf]
    rw [← this.2]; exact Rel.result this.1 _ sl
  | hash p =>
    have := allowance_toMap env henv cons 0 (nodeAt avatar c v).compValue
    simp only [inputB, amountOf]
    rw [← this.2]; exact Rel.result this.1 _ sl

include henv in
theorem custom_rel (ho : c.op = 22) :
    Rel (EX avatar env data n f c v cons sl) (RX avatar env data n c ss v cons sl) := by
  have hop : (nodeAt avatar c v).operator = .Custom := by rw [nodeAt_operator, ho]; rfl
  show Rel (evalC env data n (f + 1) v.loc (nodeAt avatar c v) cons sl)
    (readExt avatar env data n c ss v sl (toMap cons))
  rw [evalC_custom env data n f v.loc _ cons sl hop]
  unfold readExt; simp only [ho]
  unfold chargesT customCharges
  rcases hc : env.customCall (nodeAt avatar c v).compValue v.loc
      (if (nodeAt avatar c v).size ≠ 0 then (nodeAt avatar c v).size
       else size data v.loc (nodeAt avatar c v)) sl.values with s | chs
  · simp only [Option.bind_none]
    have := henv.custom _ _ _ _ s hc
    exact Rel.violation this.1 this.2 sl
  · simp only [Option.bind_some]
    rw [applyCharges_toMap]
    exact Rel.result (applyCharges_status env cons chs) _ sl

theorem pluck_rel (ho : c.op = 14) (hne : (EX avatar env data n f c v cons sl).status ≠ revert) :
    Rel (EX avatar env data n f c v cons sl) (RX avatar env data n c ss v cons sl) := by
  have hop : (nodeAt avatar c v).operator = .Pluck := by rw [nodeAt_operator, ho]; rfl
  change (evalC env data n (f + 1) v.loc (nodeAt avatar c v) cons sl).status ≠ revert at hne
  show Rel (evalC env data n (f + 1) v.loc (nodeAt avatar c v) cons sl)
    (readExt avatar env data n c ss v sl (toMap cons))
  rw [evalC_pluck env data n f v.loc _ cons sl hop] at hne ⊢
  unfold readExt; simp only [ho]
  unfold pluckT
  rcases hi : input data v.loc (nodeAt avatar c v) with _ | _ | x | p
  all_goals simp only [hi] at hne ⊢
  all_goals first
    | exact Rel.violation (by decide) (by decide) sl
    | (rcases hk : cvAt (nodeAt avatar c v).compValue 0 with _ | k
       · simp [hk, Evaluate.violation] at hne
       · by_cases hn : k ≥ n
         · simp [hk, hn, Evaluate.violation] at hne
         · simp only [hk, hn, ite_false]
           exact ⟨rfl, by simp [Evaluate.ok]⟩)

end
end Bridge
