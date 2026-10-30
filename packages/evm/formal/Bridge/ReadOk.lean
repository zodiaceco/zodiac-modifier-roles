import Bridge.Read

/-!
# The contract's reading satisfies `World.Ok`

Allowance charges commute (`consumeM_comm`), only `Pluck` writes slots, only
`Custom`, `WithinAllowance` and `CallWithinAllowance` charge, and only the
choice operators (`ArraySome`, `ZipSome`) make their charges depend on
earlier ones.
-/

namespace Bridge
open DecoderFaithfulness DecoderFaithfulness.Roles Normalize Evaluate

theorem headD_mem_or {α} {P : α → Prop} {l : List α} {d : α} (hd : P d) (h : ∀ x ∈ l, P x) :
    P (l.headD d) := by
  cases l with
  | nil => exact hd
  | cons x xs => exact h x (by simp)

theorem mem_zipWith' {α β γ} {f : α → β → γ} {l1 : List α} {l2 : List β} {x : γ}
    (h : x ∈ List.zipWith f l1 l2) : ∃ a ∈ l1, ∃ b, x = f a b := by
  induction l1 generalizing l2 with
  | nil => simp at h
  | cons a as ih =>
    cases l2 with
    | nil => simp at h
    | cons b bs =>
      simp only [List.zipWith_cons_cons, List.mem_cons] at h
      rcases h with rfl | h
      · exact ⟨a, by simp, b, rfl⟩
      · obtain ⟨a', ha', b', rfl⟩ := ih h
        exact ⟨a', by simp [ha'], b', rfl⟩

theorem failT_pure : PureT failT := ⟨fun _ => false, fun _ _ => rfl⟩
theorem passT_pure : PureT (passT : T) := ⟨fun _ => true, fun _ _ => rfl⟩
theorem checkT_pure (b : Slots → Bool) : PureT (checkT b) := ⟨b, fun _ _ => rfl⟩

theorem chargesT_charger (env : Env) (g : Slots → Option (List (Bytes × Nat))) :
    ChargerT (consumeM env.balance) (chargesT env.balance g) := ⟨g, fun _ _ => rfl⟩

theorem keeps_pick {f : Slots → T} (h : ∀ sl, KeepsT (f sl)) : KeepsT fun sl cs => f sl sl cs :=
  fun sl cs => h sl sl cs

theorem pure_pick {f : Slots → T} (h : ∀ sl, PureT (f sl)) : PureT fun sl cs => f sl sl cs := by
  refine ⟨fun sl => Classical.choose (h sl) sl, fun sl cs => ?_⟩
  exact Classical.choose_spec (h sl) sl cs

theorem charger_pick {step : CM → Bytes × Nat → Option CM} {f : Slots → T}
    (h : ∀ sl, ChargerT step (f sl)) : ChargerT step fun sl cs => f sl sl cs := by
  refine ⟨fun sl => Classical.choose (h sl) sl, fun sl cs => ?_⟩
  exact Classical.choose_spec (h sl) sl cs

section
variable (avatar : Bytes) (env : Env) (data : Calldata) (n : Nat)

theorem iterT_ok (Q : T → Prop) (hf : Q failT) (hp : Q passT)
    (hseq : ∀ l : List T, (∀ t ∈ l, Q t) → Q (seqT l)) (hor : ∀ l : List T, (∀ t ∈ l, Q t) → Q (orT l))
    (every : Bool) (d : Condition) (l : Nat) (ss : List (RV → T)) (hss : ∀ s ∈ ss, ∀ w, Q (s w)) :
    Q (iterT data every d l ss) := by
  have kid : ∀ w, Q ((ss.headD fun _ => passT) w) := fun w =>
    headD_mem_or (P := fun s => Q (s w)) hp (fun s hs => hss s hs w)
  unfold iterT
  repeat' split
  all_goals first
    | exact hf | exact hp
    | exact hseq _ fun t ht => by obtain ⟨l, -, rfl⟩ := List.mem_map.1 ht; exact kid _
    | exact hor _ fun t ht => by obtain ⟨l, -, rfl⟩ := List.mem_map.1 ht; exact kid _

theorem iterT_true_ok (Q : T → Prop) (hf : Q failT) (hp : Q passT)
    (hseq : ∀ l : List T, (∀ t ∈ l, Q t) → Q (seqT l))
    (d : Condition) (l : Nat) (ss : List (RV → T)) (hss : ∀ s ∈ ss, ∀ w, Q (s w)) :
    Q (iterT data true d l ss) := by
  have kid : ∀ w, Q ((ss.headD fun _ => passT) w) := fun w =>
    headD_mem_or (P := fun s => Q (s w)) hp (fun s hs => hss s hs w)
  unfold iterT
  repeat' split
  all_goals first
    | exact hf | exact hp
    | exact hseq _ fun t ht => by obtain ⟨l, -, rfl⟩ := List.mem_map.1 ht; exact kid _
    | simp at *

theorem tailT_ok (Q : T → Prop) (hf : Q failT) (hseq : ∀ l : List T, (∀ t ∈ l, Q t) → Q (seqT l))
    (d : Condition) (l : Nat) (ss : List (RV → T)) (hss : ∀ s ∈ ss, ∀ w, Q (s w)) :
    Q (tailT data d l ss) := by
  unfold tailT
  repeat' split
  all_goals first
    | exact hf
    | exact hseq _ fun t ht => by
        obtain ⟨s, hs, l, rfl⟩ := mem_zipWith' ht
        exact hss s hs _

theorem marrT_ok (Q : T → Prop) (hf : Q failT) (hseq : ∀ l : List T, (∀ t ∈ l, Q t) → Q (seqT l))
    (e : Nat) (d : Condition) (l : Nat) (ss : List (RV → T)) (hss : ∀ s ∈ ss, ∀ w, Q (s w)) :
    Q (marrT data e d l ss) := by
  unfold marrT
  repeat' split
  all_goals first
    | exact hf
    | exact hseq _ fun t ht => by
        obtain ⟨s, hs, l, rfl⟩ := mem_zipWith' ht
        exact hss s hs _

theorem sliceT_ok (Q : T → Prop) (hf : Q failT) (d : Condition) (l : Nat) (kid : RV → T)
    (hk : ∀ w, Q (kid w)) : Q (sliceT data d l kid) := by
  unfold sliceT
  repeat' split
  all_goals first | exact hf | exact hk _

theorem zipT_ok (Q : T → Prop) (hf : Q failT) (hseq : ∀ l : List T, (∀ t ∈ l, Q t) → Q (seqT l))
    (hor : ∀ l : List T, (∀ t ∈ l, Q t) → Q (orT l))
    (pick : ∀ {f : Slots → T}, (∀ sl, Q (f sl)) → Q fun sl cs => f sl sl cs)
    (every : Bool) (d : Condition) (kid : RV → T) (hk : ∀ w, Q (kid w)) :
    Q (zipT data n every d kid) := by
  unfold zipT
  split
  · exact hf
  · refine pick fun sl => ?_
    unfold zipF
    repeat' split
    all_goals first
      | exact hf
      | exact hseq _ fun t ht => by obtain ⟨i, -, rfl⟩ := List.mem_map.1 ht; exact hk _
      | exact hor _ fun t ht => by obtain ⟨i, -, rfl⟩ := List.mem_map.1 ht; exact hk _

theorem zipT_every_ok (Q : T → Prop) (hf : Q failT) (hseq : ∀ l : List T, (∀ t ∈ l, Q t) → Q (seqT l))
    (pick : ∀ {f : Slots → T}, (∀ sl, Q (f sl)) → Q fun sl cs => f sl sl cs)
    (d : Condition) (kid : RV → T) (hk : ∀ w, Q (kid w)) :
    Q (zipT data n true d kid) := by
  unfold zipT
  split
  · exact hf
  · refine pick fun sl => ?_
    unfold zipF
    repeat' split
    all_goals first
      | exact hf
      | exact hseq _ fun t ht => by obtain ⟨i, -, rfl⟩ := List.mem_map.1 ht; exact hk _
      | simp at *

theorem readWorld_keeps (c : Cond) (ss : List (RV → T)) (h14 : c.op ≠ 14)
    (hss : ∀ s ∈ ss, ∀ v, KeepsT (s v)) (v : RV) :
    KeepsT ((readWorld avatar env data n).ext c ss v) := by
  have hf : KeepsT failT := fun _ _ => rfl
  have hp : KeepsT (passT : T) := fun _ _ => rfl
  have kid : ∀ w, KeepsT ((ss.headD fun _ => passT) w) := fun w =>
    headD_mem_or (P := fun s => KeepsT (s w)) hp (fun s hs => hss s hs w)
  show KeepsT (readExt avatar env data n c ss v)
  unfold readExt
  split
  all_goals first
    | exact (h14 (by assumption)).elim
    | exact (checkT_pure _).keeps
    | exact (chargesT_charger env _).keeps
    | exact hf
    | exact iterT_ok data KeepsT hf hp (fun _ h => seqT_keeps h) (fun _ h => orT_keeps h) _ _ _ _ hss
    | exact tailT_ok data KeepsT hf (fun _ h => seqT_keeps h) _ _ _ hss
    | exact marrT_ok data KeepsT hf (fun _ h => seqT_keeps h) _ _ _ _ hss
    | exact sliceT_ok data KeepsT hf _ _ _ kid
    | exact zipT_ok data n KeepsT hf (fun _ h => seqT_keeps h) (fun _ h => orT_keeps h)
        (fun h => keeps_pick h) _ _ _ kid

theorem readWorld_pure (c : Cond) (ss : List (RV → T))
    (h14 : c.op ≠ 14) (h22 : c.op ≠ 22) (h28 : c.op ≠ 28) (h30 : c.op ≠ 30)
    (hss : ∀ s ∈ ss, ∀ v, PureT (s v)) (v : RV) :
    PureT ((readWorld avatar env data n).ext c ss v) := by
  have kid : ∀ w, PureT ((ss.headD fun _ => passT) w) := fun w =>
    headD_mem_or (P := fun s => PureT (s w)) passT_pure (fun s hs => hss s hs w)
  show PureT (readExt avatar env data n c ss v)
  unfold readExt
  split
  all_goals first
    | exact (h14 (by assumption)).elim
    | exact (h22 (by assumption)).elim
    | exact (h28 (by assumption)).elim
    | exact (h30 (by assumption)).elim
    | exact checkT_pure _
    | exact failT_pure
    | exact iterT_ok data PureT failT_pure passT_pure (fun _ h => seqT_pure h) (fun _ h => orT_pure h)
        _ _ _ _ hss
    | exact tailT_ok data PureT failT_pure (fun _ h => seqT_pure h) _ _ _ hss
    | exact marrT_ok data PureT failT_pure (fun _ h => seqT_pure h) _ _ _ _ hss
    | exact sliceT_ok data PureT failT_pure _ _ _ kid
    | exact zipT_ok data n PureT failT_pure (fun _ h => seqT_pure h) (fun _ h => orT_pure h)
        (fun h => pure_pick h) _ _ _ kid

theorem readWorld_charger (c : Cond) (ss : List (RV → T))
    (h14 : c.op ≠ 14) (h2 : c.op ≠ 2) (h6 : c.op ≠ 6) (h10 : c.op ≠ 10)
    (hss : ∀ s ∈ ss, ∀ v, ChargerT (consumeM env.balance) (s v)) (v : RV) :
    ChargerT (consumeM env.balance) ((readWorld avatar env data n).ext c ss v) := by
  have hf : ChargerT (consumeM env.balance) failT := failT_pure.charger _
  have hp : ChargerT (consumeM env.balance) (passT : T) := passT_pure.charger _
  have kid : ∀ w, ChargerT (consumeM env.balance) ((ss.headD fun _ => passT) w) := fun w =>
    headD_mem_or (P := fun s => ChargerT (consumeM env.balance) (s w)) hp (fun s hs => hss s hs w)
  show ChargerT (consumeM env.balance) (readExt avatar env data n c ss v)
  unfold readExt
  split
  all_goals first
    | exact (h14 (by assumption)).elim
    | exact (h6 (by assumption)).elim
    | exact (h10 (by assumption)).elim
    | exact (checkT_pure _).charger _
    | exact chargesT_charger env _
    | exact hf
    | exact iterT_true_ok data (ChargerT (consumeM env.balance)) hf hp (fun _ h => seqT_charger h)
        _ _ _ hss
    | exact tailT_ok data (ChargerT (consumeM env.balance)) hf (fun _ h => seqT_charger h) _ _ _ hss
    | exact marrT_ok data (ChargerT (consumeM env.balance)) hf (fun _ h => seqT_charger h) _ _ _ _ hss
    | exact sliceT_ok data (ChargerT (consumeM env.balance)) hf _ _ _ kid
    | exact zipT_every_ok data n (ChargerT (consumeM env.balance)) hf (fun _ h => seqT_charger h)
        (fun h => charger_pick h) _ _ kid

/-- **The contract's reading satisfies the normalization proof's assumptions.** -/
theorem readWorld_ok : (readWorld avatar env data n).Ok (consumeM env.balance) where
  comm := consumeM_comm env.balance
  keeps := readWorld_keeps avatar env data n
  pure := readWorld_pure avatar env data n
  charger := readWorld_charger avatar env data n

end
end Bridge
