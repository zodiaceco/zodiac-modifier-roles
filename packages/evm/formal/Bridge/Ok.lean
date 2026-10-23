import Bridge.World

/-!
# The contract world satisfies `World.Ok`

The normalization proof assumes five things of the operators it does not
rewrite (`Normalize.World.Ok`). For the contract world they are theorems:
allowance charges commute (`consumeM_comm`), a trailing `Pass` does not
change a tuple or calldata operator, only `Pluck` writes slots, only
`Custom`, `WithinAllowance` and `CallWithinAllowance` charge, and only the
choice operators make their charges depend on earlier ones.
-/

namespace Bridge
open DecoderFaithfulness DecoderFaithfulness.Roles Normalize Evaluate

section
variable (avatar : Bytes) (env : Env) (data : Calldata) (n : Nat)

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
theorem passK_pure (v : Val') : PureT (passK v) := ⟨fun _ => true, fun _ _ => rfl⟩

theorem chargesT_charger (g : Slots → Option (List (Bytes × Nat))) :
    ChargerT (consumeM env.balance) (chargesT env.balance g) := ⟨g, fun _ _ => rfl⟩

/-- A thunk that passes or fails on a condition of the slots alone. -/
theorem pure_of {t : T} (b : Slots → Bool) (h : ∀ sl cs, t sl cs = (if b sl then some cs else none, sl)) :
    PureT t := ⟨b, h⟩

theorem checkT_pure (b : Slots → Bool) : PureT (checkT b) := ⟨b, fun _ _ => rfl⟩

theorem iterT_ok (P : T → Prop) (hf : P failT)
    (hseq : ∀ l : List T, (∀ t ∈ l, P t) → P (seqT l))
    (hor : ∀ l : List T, (∀ t ∈ l, P t) → P (orT l))
    (every : Bool) (e : Nat) (kid : Val' → T) (hk : ∀ w, P (kid w)) (v : Val') :
    P (iterT data every e kid v) := by
  unfold iterT
  split
  · exact hf
  · split
    · split
      · exact hseq _ (by simp only [List.mem_map]; rintro _ ⟨l, -, rfl⟩; exact hk _)
      · exact hor _ (by simp only [List.mem_map]; rintro _ ⟨l, -, rfl⟩; exact hk _)
    · exact hf

theorem iterT_true_ok (P : T → Prop) (hf : P failT)
    (hseq : ∀ l : List T, (∀ t ∈ l, P t) → P (seqT l))
    (e : Nat) (kid : Val' → T) (hk : ∀ w, P (kid w)) (v : Val') :
    P (iterT data true e kid v) := by
  unfold iterT
  split
  · exact hf
  · split
    · exact hseq _ (by simp only [List.mem_map]; rintro _ ⟨l, -, rfl⟩; exact hk _)
    · exact hf

theorem tailT_ok (P : T → Prop) (hf : P failT)
    (hseq : ∀ l : List T, (∀ t ∈ l, P t) → P (seqT l))
    (e : Nat) (ss : List (Val' → T)) (hk : ∀ s ∈ ss, ∀ w, P (s w)) (v : Val') :
    P (tailT data e ss v) := by
  unfold tailT
  split
  · exact hf
  · split
    · split
      · exact hf
      · exact hseq _ fun t ht => by
          obtain ⟨s, hs, l, rfl⟩ := mem_zipWith' ht
          exact hk s hs _
    · exact hf

theorem matchesArrT_ok (P : T → Prop) (hf : P failT)
    (hseq : ∀ l : List T, (∀ t ∈ l, P t) → P (seqT l))
    (e : Nat) (cv : List Nat) (ss : List (Val' → T)) (hk : ∀ s ∈ ss, ∀ w, P (s w)) (v : Val') :
    P (matchesArrT data e cv ss v) := by
  unfold matchesArrT
  split
  · exact hf
  · split
    · split
      · exact hf
      · exact hseq _ fun t ht => by
          obtain ⟨s, hs, l, rfl⟩ := mem_zipWith' ht
          exact hk s hs _
    · exact hf

theorem sliceT_ok (P : T → Prop) (hf : P failT) (e : Nat) (cv : List Nat) (kid : Val' → T)
    (hk : ∀ w, P (kid w)) (v : Val') : P (sliceT data e cv kid v) := by
  unfold sliceT
  split
  · exact hf
  · split
    · exact hf
    · repeat' split
      all_goals first | exact hf | exact hk _

theorem contractWorld_keeps (e o : Nat) (cv : List Nat) (ss : List (Val' → T)) (h14 : o ≠ 14)
    (hss : ∀ s ∈ ss, ∀ v, KeepsT (s v)) (v : Val') :
    KeepsT ((contractWorld avatar env data n).ext e o cv ss v) := by
  have kid : ∀ w, KeepsT ((ss.headD passK) w) := fun w =>
    headD_mem_or (P := fun s => KeepsT (s w)) (fun _ _ => rfl) (fun s hs => hss s hs w)
  have hf : KeepsT failT := fun _ _ => rfl
  simp only [contractWorld]
  unfold extW
  split
  all_goals first
    | exact h14 rfl |> False.elim
    | exact (checkT_pure _).keeps
    | exact (chargesT_charger env _).keeps
    | exact hf
    | exact iterT_ok data KeepsT hf (fun _ h => seqT_keeps h) (fun _ h => orT_keeps h) _ _ _ kid v
    | exact tailT_ok data KeepsT hf (fun _ h => seqT_keeps h) _ _ hss v
    | exact matchesArrT_ok data KeepsT hf (fun _ h => seqT_keeps h) _ _ _ hss v
    | exact sliceT_ok data KeepsT hf _ _ _ kid v

theorem contractWorld_pure (e o : Nat) (cv : List Nat) (ss : List (Val' → T))
    (h14 : o ≠ 14) (h22 : o ≠ 22) (h28 : o ≠ 28) (h30 : o ≠ 30)
    (hss : ∀ s ∈ ss, ∀ v, PureT (s v)) (v : Val') :
    PureT ((contractWorld avatar env data n).ext e o cv ss v) := by
  have kid : ∀ w, PureT ((ss.headD passK) w) := fun w =>
    headD_mem_or (P := fun s => PureT (s w)) (passK_pure w) (fun s hs => hss s hs w)
  simp only [contractWorld]
  unfold extW
  split
  all_goals first
    | exact h14 rfl |> False.elim
    | exact h22 rfl |> False.elim
    | exact h28 rfl |> False.elim
    | exact h30 rfl |> False.elim
    | exact checkT_pure _
    | exact failT_pure
    | exact iterT_ok data PureT failT_pure (fun _ h => seqT_pure h) (fun _ h => orT_pure h) _ _ _ kid v
    | exact tailT_ok data PureT failT_pure (fun _ h => seqT_pure h) _ _ hss v
    | exact matchesArrT_ok data PureT failT_pure (fun _ h => seqT_pure h) _ _ _ hss v
    | exact sliceT_ok data PureT failT_pure _ _ _ kid v

theorem contractWorld_charger (e o : Nat) (cv : List Nat) (ss : List (Val' → T))
    (h14 : o ≠ 14) (h2 : o ≠ 2) (h6 : o ≠ 6) (h10 : o ≠ 10)
    (hss : ∀ s ∈ ss, ∀ v, ChargerT (consumeM env.balance) (s v)) (v : Val') :
    ChargerT (consumeM env.balance) ((contractWorld avatar env data n).ext e o cv ss v) := by
  have hf : ChargerT (consumeM env.balance) failT := failT_pure.charger _
  have kid : ∀ w, ChargerT (consumeM env.balance) ((ss.headD passK) w) := fun w =>
    headD_mem_or (P := fun s => ChargerT (consumeM env.balance) (s w))
      ((passK_pure w).charger _) (fun s hs => hss s hs w)
  simp only [contractWorld]
  unfold extW
  split
  all_goals first
    | exact h14 rfl |> False.elim
    | exact h6 rfl |> False.elim
    | exact (checkT_pure _).charger _
    | exact chargesT_charger env _
    | exact hf
    | exact iterT_true_ok data (ChargerT (consumeM env.balance)) hf (fun _ h => seqT_charger h)
        _ _ kid v
    | exact tailT_ok data (ChargerT (consumeM env.balance)) hf (fun _ h => seqT_charger h) _ _ hss v
    | exact matchesArrT_ok data (ChargerT (consumeM env.balance)) hf (fun _ h => seqT_charger h)
        _ _ _ hss v
    | exact sliceT_ok data (ChargerT (consumeM env.balance)) hf _ _ _ kid v

/-- **The contract satisfies the normalization proof's assumptions.** -/
theorem contractWorld_ok : (contractWorld avatar env data n).Ok (consumeM env.balance) where
  comm := consumeM_comm env.balance
  keeps := contractWorld_keeps avatar env data n
  pure := contractWorld_pure avatar env data n
  charger := contractWorld_charger avatar env data n

end
end Bridge
