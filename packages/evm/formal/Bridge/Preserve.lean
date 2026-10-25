import Bridge.TypeDesc

/-!
# Normalization keeps a tree fitting its layout

`normalize_fits`: if `c` fits layout `m`, so does `normalize k c`. Every step
keeps where each parameter is read: pruning drops trailing `Pass` children of
containers that are not inlined, padding appends `Pass` children of the
layout's types to such containers only, and the logical rewrites (flatten,
dedupe, unwrap, push-down, sort) keep every branch at the layout.
-/

namespace Bridge
open DecoderFaithfulness DecoderFaithfulness.Roles Normalize Evaluate

section
variable (avatar : Bytes) (P : Nat → Option Condition)

local notation "F" => fun (c : Cond) (m : Condition) => Fits avatar P c (D avatar c) m

/-! ## Containers -/

theorem lay_transfer {c c' : Cond} {m : Condition} (h : isInl c = isInl c' ∧ (isInl c = true → rawSz avatar c = rawSz avatar c'))
    (hs : Sane avatar c) (hl : LayEq (D avatar c) m) : Sane avatar c' ∧ LayEq (D avatar c') m := by
  have hD : (D avatar c').inlined = (D avatar c).inlined ∧ (D avatar c').size = (D avatar c).size := by
    rw [D_inlined, D_inlined, D_size, D_size, ← h.1]
    by_cases hi : isInl c = true
    · rw [h.2 hi]; simp [hi]
    · simp [hi]
  refine ⟨?_, ?_, ?_⟩
  · unfold Sane at hs ⊢; rw [hD.1, ← hs, h.1]
  · rw [hD.1]; exact hl.1
  · rw [hD.2]; exact hl.2

/-! ## Step 1: the children -/

/-- Any environment (to instantiate the world when only `isStruct` matters). -/
def env0 : Env := ⟨0, fun _ => 0, fun _ _ => (0, 0), fun _ _ _ _ => .inl 1, fun _ _ => 0⟩

theorem isStruct_normalize (k : Nat) (c : Cond) : isStruct (normalize k c) = isStruct c :=
  (normalize_same (W := contractWorld [] env0 [] 0 fun _ => none) (contractWorld_ok [] env0 [] 0 fun _ => none) k c).2

theorem Plain.ch {c : Cond} (h : Plain c) : ∀ x ∈ c.ch, Plain x := by
  rcases h with ⟨_, _, _, _, h⟩; exact h

theorem map_normalize_plain (k : Nat) {c : Cond} (h : Plain c) : c.ch.map (normalize k) = c.ch := by
  conv => rhs; rw [← List.map_id c.ch]
  exact List.map_congr_left fun x hx => normalize_plain k x (h.ch x hx)

theorem with_ch_self (c : Cond) : ({ c with ch := c.ch } : Cond) = c := by cases c; rfl

theorem NsOk.isStruct {c : Cond} (h : NsOk c) : isStruct c = false := by
  induction h with
  | @leaf c he _ _ => rw [isStruct_eq]; rcases he with h | h <;> simp_all
  | @logical c hop _ _ ih =>
    rw [isStruct_eq]
    have : (c.op == 1 || c.op == 2) = true := by rcases hop with h | h <;> simp [h]
    rw [this]; simp only [ite_true, List.any_eq_false]
    intro x hx; simp [ih x hx]

theorem isStruct_withCh (c : Cond) (l : List Cond) (h : l.any isStruct = c.ch.any isStruct) :
    isStruct { c with ch := l } = isStruct c := by
  rw [isStruct_eq, isStruct_eq]; simp only [h]

theorem any_map_normalize (k : Nat) (l : List Cond) :
    (l.map (normalize k)).any isStruct = l.any isStruct := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons, List.any_cons, isStruct_normalize, ih]

theorem D_encoding_withCh (c : Cond) (l : List Cond) :
    (D avatar { c with ch := l }).encoding = (D avatar c).encoding := by
  rw [D_encoding, D_encoding]

theorem D_leadingBytes_withCh (c : Cond) (l : List Cond) :
    (D avatar { c with ch := l }).leadingBytes = (D avatar c).leadingBytes := by
  rw [D_leadingBytes, D_leadingBytes]; rfl

/-- A call node is never inlined: its layout metadata does not depend on
    its children. -/
theorem D_lay_abi {x : Cond} (he : x.enc = 5) : (D avatar x).inlined = false ∧ (D avatar x).size = 0 := by
  have : isInl x = false := by rw [isInl_eq, he]; rfl
  rw [D_inlined, D_size, this]; simp

theorem layEq_abi {x x' : Cond} {m : Condition} (he : x.enc = 5) (he' : x'.enc = 5)
    (hl : LayEq (D avatar x) m) : LayEq (D avatar x') m := by
  obtain ⟨a1, a2⟩ := D_lay_abi avatar he
  obtain ⟨b1, b2⟩ := D_lay_abi avatar he'
  exact ⟨by rw [b1, ← a1]; exact hl.1, by rw [b2, ← a2]; exact hl.2⟩

/-- A check of the plain `bytes` value of a variant is plain. -/
theorem Fits.plain_dyn {c : Cond} {d : Condition} (h : Fits avatar P c d dynLay) (he : c.enc = 2) :
    Plain c := by
  have nil : c.op ≠ 1 → c.op ≠ 2 → c.op ≠ 5 → c.ch = [] → Plain c := fun h1 h2 h5 hch =>
    .mk h1 h2 h5 (fun _ => by rw [hch]; simp) (fun x hx => by rw [hch] at hx; cases hx)
  cases h with
  | pass h0 _ _ _ _ _ hch => exact nil (by omega) (by omega) (by omega) (hch (.inr he))
  | slice _ _ _ _ _ _ hp _ _ => exact hp
  | leaf hop _ _ _ _ _ _ _ _ hch _ _ =>
    unfold leafOp at hop
    simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq] at hop
    exact nil (by omega) (by omega) (by omega) (hch (.inr he))
  | ns hs hns _ => rcases hns with ⟨h, _, _⟩ | ⟨_, h, _⟩ <;> omega
  | logical _ h _ _ _ _ _ => omega
  | tup _ h _ _ _ _ _ _ _ _ => omega
  | arr _ h _ _ _ _ _ _ _ => omega
  | varAbi _ h _ _ _ _ _ _ _ _ => omega
  | varDyn hv _ _ _ => simp [dynLay, isVarLay] at hv
  | zip _ h => omega
  | zipLogical _ h => omega

/-- A `Matches` on calldata that fits a call layout: the `tup` facts. -/
theorem Fits.abi_tup {c : Cond} {k : Condition} (h : F c k) (h5 : c.op = 5) (he : c.enc = 5)
    (hke : k.encoding = .AbiEncoded) :
    (D avatar c).encoding = k.encoding ∧ LayEq (D avatar c) k ∧
      (D avatar c).leadingBytes = k.leadingBytes ∧ (∀ x ∈ c.ch, isStruct x = true) ∧
      c.ch.length ≤ k.children.length ∧
      (∀ i (h : i < c.ch.length), F c.ch[i] (k.children.getD i default)) ∧
      isInl c = (D avatar c).inlined := by
  cases h with
  | tup _ _ _ hm hl hlb hs hk hch hsn => exact ⟨hm, hl, hlb, hs, hk, hch, hsn⟩
  | pass h0 => omega
  | ns hs _ _ => rw [isStruct_eq] at hs; simp [h5, he] at hs
  | logical hop => omega
  | arr _ he' => omega
  | slice h13 => omega
  | leaf hop => simp [leafOp, h5] at hop
  | varAbi _ _ _ hv _ _ _ _ _ _ => simp [isVarLay, hke] at hv
  | varDyn _ he' => omega
  | zip hop => omega
  | zipLogical hop => omega

theorem fits_children_tup (k : Nat) (IH : ∀ x m', F x m' → F (normalize k x) m') {c : Cond}
    {m : Condition} (h5 : c.op = 5) (he : c.enc = 3 ∨ c.enc = 5)
    (hm : (D avatar c).encoding = m.encoding) (hl : LayEq (D avatar c) m)
    (hlb : (D avatar c).leadingBytes = m.leadingBytes) (hs : ∀ x ∈ c.ch, isStruct x = true)
    (hk : c.ch.length ≤ m.children.length)
    (hch : ∀ i (h : i < c.ch.length), F c.ch[i] (m.children.getD i default))
    (hsn : isInl c = (D avatar c).inlined) : F { c with ch := c.ch.map (normalize k) } m := by
  have hlen : (c.ch.map (normalize k)).length = c.ch.length := by simp
  have hch' : ∀ i (hi : i < (c.ch.map (normalize k)).length),
      F (c.ch.map (normalize k))[i] (m.children.getD i default) := by
    intro i hi
    simp only [List.getElem_map]
    exact IH _ _ (hch i (by simpa using hi))
  have hraw := container_raw avatar (c := c) (c' := { c with ch := c.ch.map (normalize k) }) rfl
    hlen.symm (fun i h1 h2 => by
      simp only [List.getElem_map]
      have r1 := (hch i h1).raw avatar P (hs _ (List.getElem_mem h1))
      have r2 := (IH _ _ (hch i h1)).raw avatar P
        (by rw [isStruct_normalize]; exact hs _ (List.getElem_mem h1))
      refine ⟨r1.1.trans r2.1.symm, fun hi => (r1.2.1 hi).trans (r2.2.1 (r2.1.trans (r1.1.symm.trans hi))).symm⟩)
  obtain ⟨hsn', hl'⟩ := lay_transfer avatar hraw hsn hl
  refine .tup h5 he rfl (by rw [D_encoding_withCh]; exact hm) hl' (by rw [D_leadingBytes_withCh]; exact hlb)
    ?_ (by rw [hlen]; exact hk) hch' hsn'
  intro x' hx'
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hx'
  rw [isStruct_normalize]; exact hs x hx

theorem NsOk.noZip {c : Cond} (h : NsOk c) : hasZip c = false := by
  induction h with
  | @leaf c _ hch hop =>
    rw [hasZip_eq, hch]
    unfold nsOp at hop
    simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq] at hop
    have h10 : c.op ≠ 10 := by omega
    have h11 : c.op ≠ 11 := by omega
    simp [h10, h11]
  | @logical c hop _ _ ih =>
    rw [hasZip_eq]
    have h10 : c.op ≠ 10 := by omega
    have h11 : c.op ≠ 11 := by omega
    have : c.ch.any hasZip = false := by
      rw [List.any_eq_false]; intro x hx; simp [ih x hx]
    simp [h10, h11, this]

/-- An `And`/`Or` whose children all fit `m` fits `m`. -/
theorem logical_withCh {c : Cond} {m : Condition} (hop : c.op = 1 ∨ c.op = 2) (he : c.enc = 0)
    (l : List Cond) (hl : ∀ x ∈ l, F x m) : F { c with ch := l } m := by
  by_cases hs : isStruct { c with ch := l } = true
  · obtain ⟨hl', hsn'⟩ := logical_lay avatar P (c := { c with ch := l }) hop he hs hl
    exact .logical hop he hs rfl hl' hl hsn'
  · have hs' : ∀ x ∈ l, isStruct x = false := by
      intro x hx
      rw [isStruct_eq] at hs
      have : (c.op == 1 || c.op == 2) = true := by rcases hop with h | h <;> simp [h]
      simp only [this, ite_true, Bool.not_eq_true, List.any_eq_false] at hs
      simpa using hs x hx
    have hk := fun x hx => (hl x hx).nsOk avatar P (hs' x hx)
    have h10 : c.op ≠ 10 := by omega
    have h11 : c.op ≠ 11 := by omega
    have h14 : c.op ≠ 14 := by omega
    by_cases hz : ∃ x ∈ l, hasZip x = true
    · obtain ⟨x, hx, hzx⟩ := hz
      have hm : m.inlined = false := by
        rcases hk x hx with ⟨hn, -⟩ | ⟨-, hm⟩
        · rw [hn.noZip] at hzx; cases hzx
        · exact hm
      refine .zipLogical hop he (by simpa using hs) ?_ rfl hm hl
      rw [hasZip_eq]; simp only [Bool.or_eq_true, List.any_eq_true]; exact Or.inr ⟨x, hx, hzx⟩
    · have hall : ∀ x ∈ l, NsOk x ∧ ∀ k ∈ plucks x, P k = none := by
        intro x hx
        rcases hk x hx with h | ⟨hzx, -⟩
        · exact h
        · exact absurd ⟨x, hx, hzx⟩ hz
      have hns : NsOk { c with ch := l } := .logical hop he fun x hx => (hall x hx).1
      refine .ns hns.isStruct hns rfl fun k hk' => ?_
      rw [plucks_eq] at hk'
      simp only [h14, ite_false, List.nil_append, List.mem_flatMap] at hk'
      obtain ⟨x, hx, hkx⟩ := hk'
      exact (hall x hx).2 k hkx

theorem fits_children (k : Nat) (IH : ∀ x m', F x m' → F (normalize k x) m') {c : Cond}
    {m : Condition} (h : F c m) (hkw : keepsAsWritten c = false) :
    F { c with ch := c.ch.map (normalize k) } m := by
  have h0 := h
  cases h with
  | zip hop =>
    unfold keepsAsWritten at hkw; rcases hop with h | h <;> simp [h] at hkw
  | pass h0' hnode hs hl htd hsn hch =>
    obtain ⟨htd', hr⟩ := td_map avatar k htd
    have hl' := (hr.D avatar).layEq
    refine .pass h0' (Node.refl avatar _) (by rw [isStruct_withCh _ _ (any_map_normalize k c.ch)]; exact hs)
      ⟨hl'.1.trans hl.1, hl'.2.trans hl.2⟩ htd' ?_ (fun he => by rw [hch he]; rfl)
    rw [hr.inl avatar, hsn]; exact ((hr.D avatar).layEq.1).symm
  | slice _ _ _ _ _ _ hp _ _ => rw [map_normalize_plain k hp]; cases c; exact h0
  | leaf hop hs hnode hty henc h16 htd hsn h4 h12 h5 h14 =>
    obtain ⟨htd', hr⟩ := td_map avatar k htd
    refine .leaf hop (by rw [isStruct_withCh _ _ (any_map_normalize k c.ch)]; exact hs) (Node.refl avatar _) ((hr.D avatar).trans hty) henc
      (fun h => by rw [hr.inl avatar]; exact h16 h) htd' ?_ (fun h => by simpa using h4 h)
      (fun h => by rw [h12 h]; rfl) h5 h14
    rw [hr.inl avatar, hsn]; exact ((hr.D avatar).layEq.1).symm
  | ns hs hns _ hpl =>
    cases hns with
    | leaf _ hch _ => rw [hch]; simp only [List.map_nil]; rw [← hch]; cases c; exact h0
    | logical hop he hall =>
      exact logical_withCh avatar P hop he _ fun x' hx' => by
        obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hx'
        exact IH x m (.ns (hall x hx).isStruct (hall x hx) rfl fun j hj => hpl j (plucks_child hx hj))
  | zipLogical hop he _ _ _ _ hch =>
    exact logical_withCh avatar P hop he _ fun x' hx' => by
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hx'
      exact IH x m (hch x hx)
  | logical hop he hs _ _ hch _ =>
    have hch' : ∀ x ∈ ({ c with ch := c.ch.map (normalize k) } : Cond).ch,
        F x m := by
      intro x' hx'
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hx'
      exact IH x m (hch x hx)
    have hs' : isStruct { c with ch := c.ch.map (normalize k) } = true := by
      rw [isStruct_withCh _ _ (any_map_normalize k c.ch)]; exact hs
    obtain ⟨hl', hsn'⟩ := logical_lay avatar P (c := { c with ch := c.ch.map (normalize k) }) hop he hs' hch'
    exact .logical hop he hs' rfl hl' hch' hsn'
  | tup h5 he _ hm hl hlb hs hk hch hsn =>
    exact fits_children_tup avatar P k IH h5 he hm hl hlb hs hk hch hsn
  | varAbi h5 he _ hv hl hmem hke hkey hu hf =>
    obtain ⟨hm', hl', hlb', hs', hk', hch', hsn'⟩ := hf.abi_tup avatar P h5 he hke
    exact .varAbi h5 he rfl hv (layEq_abi avatar he he hl) hmem hke hkey hu
      (fits_children_tup avatar P k IH h5 (.inr he) hm' hl' hlb' hs' hk' hch' hsn')
  | varDyn _ he2 _ hf => rw [map_normalize_plain k (hf.plain_dyn avatar P he2)]; cases c; exact h0
  | arr hop he _ hm hl hne hs hch hsn =>
    have hraw : isInl c = isInl { c with ch := c.ch.map (normalize k) } ∧
        (isInl c = true → rawSz avatar c = rawSz avatar { c with ch := c.ch.map (normalize k) }) := by
      have h1 : isInl c = false := by rw [isInl_eq, he]; rfl
      have h2 : isInl { c with ch := c.ch.map (normalize k) } = false := by rw [isInl_eq]; simp [he]
      rw [h1, h2]; simp
    obtain ⟨hsn', hl'⟩ := lay_transfer avatar hraw hsn hl
    refine .arr hop he rfl hm hl' (by simpa using hne) ?_ ?_ hsn'
    · intro x' hx'
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hx'
      rw [isStruct_normalize]; exact hs x hx
    · intro x' hx'
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hx'
      exact IH x _ (hch x hx)

/-! ## Step 2: pruning -/

theorem isDynL_eq (l : List Cond) : isDynL l = l.any isDyn := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp [isDynL, ih]

theorem isDyn_eq (c : Cond) :
    isDyn c = if (c.enc == 1 || c.enc == 6) then false
      else if (c.enc == 2 || c.enc == 4) then true else c.ch.any isDyn := by
  rcases c with ⟨e, o, cv, ch⟩; rw [isDyn, isDynL_eq]

theorem isDyn_notInl (c : Cond) (h : isDyn c = true) : isInl c = false := by
  rw [isDyn_eq] at h
  rw [isInl_eq]
  by_cases h1 : (c.enc == 1 || c.enc == 6) = true
  · rw [if_pos h1] at h; exact absurd h (by simp)
  rw [if_neg h1] at h
  by_cases h2 : (c.enc == 2 || c.enc == 4) = true
  · simp only [Bool.or_eq_true, beq_iff_eq] at h2; rcases h2 with h2 | h2 <;> simp [h2]
  rw [if_neg h2] at h
  obtain ⟨x, hx, hdx⟩ := List.any_eq_true.1 h
  have := isDyn_notInl x hdx
  simp only [Bool.and_eq_false_iff]
  right
  rw [List.all_eq_false]
  exact ⟨x, hx, by simp [this]⟩
termination_by sizeOf c
decreasing_by exact sizeOf_lt_of_mem hx

theorem reorderGA_struct {cs : List Cond} (h : ∀ x ∈ cs, isStruct x = true) : reorderGA cs = cs := by
  unfold reorderGA
  split
  · have h1 : cs.filter (fun x => !isGlobalAllowance x) = cs := by
      rw [List.filter_eq_self]
      intro x hx; simp [isGlobalAllowance, h x hx]
    have h2 : cs.filter isGlobalAllowance = [] := by
      rw [List.filter_eq_nil_iff]
      intro x hx; simp [isGlobalAllowance, h x hx]
    rw [h1, h2, List.append_nil]
  · rfl

theorem pruneList_struct {ch : List Cond} (keep : Nat) (h : ∀ x ∈ ch, isStruct x = true) :
    pruneList ch keep = ch.take (cutIdx ch keep) := by
  unfold pruneList
  have : (ch.drop (cutIdx ch keep)).filter (fun x => !isPass x) = [] := by
    rw [List.filter_eq_nil_iff]
    intro x hx
    have h1 := mem_drop_cutIdx hx
    have h2 := h x (List.mem_of_mem_drop hx)
    simp [h2] at h1; simp [h1]
  rw [this, List.append_nil]

theorem cutIdx_ge (ch : List Cond) (keep : Nat) (hk : keep < ch.length) : keep < cutIdx ch keep := by
  unfold cutIdx; omega

theorem prune_tup {c : Cond} {m : Condition} (h5 : c.op = 5) (he : c.enc = 3 ∨ c.enc = 5)
    (hcase : c.enc = 5 ∨ dynTuple c = true)
    (hm : (D avatar c).encoding = m.encoding) (hl : LayEq (D avatar c) m)
    (hlb : (D avatar c).leadingBytes = m.leadingBytes) (hs : ∀ x ∈ c.ch, isStruct x = true)
    (hk : c.ch.length ≤ m.children.length)
    (hch : ∀ i (h : i < c.ch.length), F c.ch[i] (m.children.getD i default))
    (hsn : isInl c = (D avatar c).inlined) : F { c with ch := pruneCh c } m := by
  have hre := reorderGA_struct hs
  have hpc : pruneCh c = c.ch.take (cutIdx c.ch (if dynTuple c then c.ch.findIdx isDyn else 0)) := by
    unfold pruneCh; rw [hre, pruneList_struct _ hs]
  rw [hpc]
  generalize hcut : cutIdx c.ch (if dynTuple c then c.ch.findIdx isDyn else 0) = cut
  have hinl : isInl c = false ∧ isInl { c with ch := c.ch.take cut } = false := by
    rcases hcase with h' | h'
    · constructor <;> (rw [isInl_eq]; simp [h'])
    · unfold dynTuple at h'
      simp only [Bool.and_eq_true, beq_iff_eq] at h'
      obtain ⟨h3, hdyn⟩ := h'
      refine ⟨isDyn_notInl c hdyn, ?_⟩
      rw [isDyn_eq] at hdyn
      simp [h3] at hdyn
      obtain ⟨x, hx, hdx⟩ := hdyn
      have hfi : c.ch.findIdx isDyn < c.ch.length := by
        rw [List.findIdx_lt_length]; exact ⟨x, hx, hdx⟩
      have hdt : dynTuple c = true := by
        unfold dynTuple; rw [isDyn_eq]; simp [h3]; exact ⟨x, hx, hdx⟩
      rw [if_pos hdt] at hcut
      apply isDyn_notInl
      rw [isDyn_eq]; simp [h3]
      refine ⟨c.ch[c.ch.findIdx isDyn], ?_, ?_⟩
      · rw [List.mem_take_iff_getElem]
        exact ⟨_, by have := cutIdx_ge c.ch _ hfi; omega, rfl⟩
      · exact List.findIdx_getElem (w := hfi)
  obtain ⟨hsn', hl'⟩ := lay_transfer avatar ⟨hinl.1.trans hinl.2.symm, fun h => by
    rw [hinl.1] at h; exact absurd h (by simp)⟩ hsn hl
  refine .tup h5 he rfl (by rw [D_encoding_withCh]; exact hm) hl' (by rw [D_leadingBytes_withCh]; exact hlb)
    (fun x hx => hs x (List.mem_of_mem_take hx)) (by simp; omega) ?_ hsn'
  intro i hi
  simp only [List.getElem_take]
  exact hch i (by simp at hi; omega)

theorem prune_fits {c : Cond} {m : Condition} (h : F c m) : F (prune c) m := by
  unfold prune
  split
  · rename_i hcond
    simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true] at hcond
    obtain ⟨h5, hcase⟩ := hcond
    have h0 := h
    cases h with
    | pass hop => omega
    | ns _ hns _ =>
      cases hns with
      | leaf _ _ hop => simp [nsOp, h5] at hop
      | logical hop => omega
    | logical hop => omega
    | arr _ he =>
      exfalso
      rcases hcase with h' | h'
      · omega
      · unfold dynTuple at h'; simp at h'; omega
    | slice hop => omega
    | leaf hop => simp [leafOp, h5] at hop
    | tup _ he _ hm hl hlb hs hk hch hsn => exact prune_tup avatar P h5 he hcase hm hl hlb hs hk hch hsn
    | varAbi _ he _ hv hl hmem hke hkey hu hf =>
      obtain ⟨hm', hl', hlb', hs', hk', hch', hsn'⟩ := hf.abi_tup avatar P h5 he hke
      exact .varAbi h5 he rfl hv (layEq_abi avatar he he hl) hmem hke hkey hu
        (prune_tup avatar P h5 (.inr he) hcase hm' hl' hlb' hs' hk' hch' hsn')
    | varDyn _ he2 _ _ =>
      exfalso
      rcases hcase with h' | h'
      · omega
      · unfold dynTuple at h'; simp [he2] at h'
    | zip hop => omega
    | zipLogical hop => omega
  · exact h

/-! ## Logical nodes -/

/-- The children of a logical node that fits `m` fit `m`. -/
theorem Fits.logical_ch {c : Cond} {m : Condition} (h : F c m) (hop : c.op = 1 ∨ c.op = 2) :
    c.enc = 0 ∧ ∀ x ∈ c.ch, F x m := by
  cases h with
  | logical _ he _ _ _ hch _ => exact ⟨he, hch⟩
  | ns _ hns _ hpl =>
    cases hns with
    | leaf _ _ hop' => exfalso; rcases hop with h | h <;> simp [nsOp, h] at hop'
    | logical _ he hall =>
      exact ⟨he, fun x hx => .ns (hall x hx).isStruct (hall x hx) rfl fun j hj => hpl j (plucks_child hx hj)⟩
  | zipLogical _ he _ _ _ _ hch => exact ⟨he, hch⟩
  | zip hop' => omega
  | pass h0 => omega
  | tup h5 => omega
  | arr hop' => omega
  | slice h13 => omega
  | leaf hop' => exfalso; rcases hop with h | h <;> simp [leafOp, h] at hop'
  | varAbi h5 => omega
  | varDyn _ he2 _ hf => exact absurd hop (by have := hf.dyn_op avatar P he2; omega)

theorem withCh_eq_self {c : Cond} {l : List Cond} (h : l = c.ch) : ({ c with ch := l } : Cond) = c := by
  subst h; cases c; rfl

theorem flatten_fits {c : Cond} {m : Condition} (h : F c m) : F (flatten c) m := by
  unfold flatten
  split
  · rename_i hlog
    have hop := logical_op hlog
    obtain ⟨he, hch⟩ := h.logical_ch avatar P hop
    apply logical_withCh avatar P hop he
    intro x hx
    unfold flattenCh at hx
    obtain ⟨y, hy, hxy⟩ := List.mem_flatMap.1 hx
    split at hxy
    · rename_i hyop
      have hyop' : y.op = 1 ∨ y.op = 2 := by simp at hyop; omega
      exact ((hch y hy).logical_ch avatar P hyop').2 x hxy
    · simp at hxy; subst hxy; exact hch x hy
  · exact h

theorem dedupe_fits {c : Cond} {m : Condition} (h : F c m) : F (dedupe c) m := by
  unfold dedupe
  split
  · rename_i hc
    have hop := logical_op (by simp only [Bool.and_eq_true] at hc; exact hc.1)
    obtain ⟨he, hch⟩ := h.logical_ch avatar P hop
    exact logical_withCh avatar P hop he _ fun x hx => hch x (mem_dedupeL hx)
  · exact h

theorem unwrap_fits {c : Cond} {m : Condition} (h : F c m) : F (unwrap c) m := by
  unfold unwrap
  split
  · rename_i hlog
    obtain ⟨_, hch⟩ := h.logical_ch avatar P (logical_op hlog)
    split
    · rename_i x hx; exact hch x (by rw [hx]; simp)
    · exact h
  · exact h

theorem sortB_fits {c : Cond} {m : Condition} (h : F c m) : F (sortB c) m := by
  unfold sortB
  split
  · rename_i hc
    have hop := logical_op (by simp only [Bool.and_eq_true] at hc; exact hc.1)
    obtain ⟨he, hch⟩ := h.logical_ch avatar P hop
    exact logical_withCh avatar P hop he _ fun x hx => hch x ((sortCh_perm c.ch).mem_iff.1 hx)
  · exact h

/-! ## Step: pushing an `Or` down -/

theorem length_replaceAt (l : List Cond) (h : Nat) (y : Cond) : (replaceAt l h y).length = l.length := by
  rw [replaceAt_set, List.length_set]

theorem getElem_replaceAt (l : List Cond) (h : Nat) (y : Cond) (i : Nat) (hi : i < (replaceAt l h y).length) :
    (replaceAt l h y)[i] = if i = h then y else l[i]'(by rw [length_replaceAt] at hi; exact hi) := by
  simp only [replaceAt_set, List.getElem_set]
  by_cases hih : i = h
  · subst hih; simp
  · simp [hih, Ne.symm hih]

/-- The fields of a `Matches` on a tuple or calldata that fits `m`. -/
theorem Fits.tup_inv {x : Cond} {m : Condition} (h : F x m) (h5 : x.op = 5) (he : x.enc = 3 ∨ x.enc = 5)
    (hnv : isVarLay m = false) :
    (D avatar x).encoding = m.encoding ∧ LayEq (D avatar x) m ∧ (D avatar x).leadingBytes = m.leadingBytes ∧
      (∀ y ∈ x.ch, isStruct y = true) ∧ x.ch.length ≤ m.children.length ∧
      (∀ i (h : i < x.ch.length), F x.ch[i] (m.children.getD i default)) ∧ Sane avatar x := by
  cases h with
  | tup _ _ _ hm hl hlb hs hk hch hsn => exact ⟨hm, hl, hlb, hs, hk, hch, hsn⟩
  | pass h0 => omega
  | ns _ hns _ =>
    cases hns with
    | leaf _ _ hop => simp [nsOp, h5] at hop
    | logical hop => omega
  | logical hop => omega
  | arr _ he' => omega
  | slice h13 => omega
  | leaf hop => simp [leafOp, h5] at hop
  | varAbi _ _ _ hv => rw [hv] at hnv; cases hnv
  | varDyn hv => rw [hv] at hnv; cases hnv
  | zip hop => omega
  | zipLogical hop => omega

theorem orNode_fits {hs : List Cond} {m : Condition} (h : ∀ x ∈ hs, F x m) : F (orNode hs) m := by
  have := logical_withCh avatar P (c := ⟨0, 2, [], []⟩) (Or.inr rfl) rfl hs h
  exact this

theorem pushStep_fits_nv {c n : Cond} {m : Condition} (h : F c m)
    (hnv : c.ch.all (·.op == 5) = true → isVarLay m = false) (hp : pushStep c = some n) : F n m := by
  unfold pushStep at hp
  split at hp
  · rename_i hcond
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, Bool.not_eq_true',
      List.all_eq_true, List.any_eq_false] at hcond
    obtain ⟨⟨⟨h2, hlen⟩, henc⟩, _⟩ := hcond
    obtain ⟨_, hch⟩ := h.logical_ch avatar P (Or.inr h2)
    have hhead : c.ch.head! ∈ c.ch := by
      obtain ⟨x, xs, hc⟩ : ∃ x xs, c.ch = x :: xs := by
        cases hc : c.ch with
        | nil => rw [hc] at hlen; simp at hlen
        | cons x xs => exact ⟨x, xs, rfl⟩
      rw [hc]; exact List.mem_cons.2 (Or.inl rfl)
    split at hp
    · -- all `Matches`
      rename_i hall
      have hnv' : isVarLay m = false := hnv hall
      simp only [List.all_eq_true, beq_iff_eq] at hall
      obtain ⟨nch, hm, rfl⟩ := Option.map_eq_some_iff.1 hp
      unfold mergeMatches at hm
      split at hm; · simp at hm
      rename_i hhe
      have hhe' : c.ch.head!.enc = 3 ∨ c.ch.head!.enc = 5 := by
        by_cases h3 : c.ch.head!.enc = 3
        · exact Or.inl h3
        by_cases h5' : c.ch.head!.enc = 5
        · exact Or.inr h5'
        exfalso; apply hhe; simp [h3, h5']
      split at hm; · simp at hm
      split at hm; · simp at hm
      split at hm
      · simp at hm
      rename_i hi hhinge
      obtain ⟨hh, hsplit⟩ := hingeM_spec hhinge
      split at hm; · simp at hm
      split at hm; · simp at hm
      split at hm; · simp at hm
      simp only [Option.some.injEq] at hm
      subst hm
      have hft := (hch _ hhead).tup_inv avatar P (hall _ hhead) hhe' hnv'
      obtain ⟨hm1, hl1, hlb1, hs1, hk1, hch1, hsn1⟩ := hft
      -- the branches' children at the hinge fit the hinge's layout
      have hhinges : ∀ y ∈ c.ch.map (·.ch[hi]!), F y (m.children.getD hi default) := by
        intro y hy
        obtain ⟨o, ho, rfl⟩ := List.mem_map.1 hy
        have hoe : o.enc = 3 ∨ o.enc = 5 := by rw [henc o ho]; exact hhe'
        have hfo := (hch o ho).tup_inv avatar P (hall o ho) hoe hnv'
        have hol : o.ch.length = c.ch.head!.ch.length := by
          have := congrArg List.length (hsplit o ho); simp at this; omega
        rw [getElem!_eq (by omega)]
        exact hfo.2.2.2.2.2.1 hi (by omega)
      have hor := orNode_fits avatar P hhinges
      have hhs : c.ch.head!.ch[hi] ∈ c.ch.map (·.ch[hi]!) :=
        List.mem_map.2 ⟨_, hhead, getElem!_eq hh⟩
      have hors : isStruct (orNode (c.ch.map (·.ch[hi]!))) = true := by
        unfold orNode; rw [isStruct_eq]; simp only [beq_self_eq_true, Bool.or_true, ite_true]
        exact List.any_eq_true.2 ⟨_, hhs, hs1 _ (List.getElem_mem hh)⟩
      have hraw := container_raw avatar (c := c.ch.head!)
        (c' := { c.ch.head! with ch := replaceAt c.ch.head!.ch hi (orNode (c.ch.map (·.ch[hi]!))) }) rfl
        (by simp [length_replaceAt]) (fun i h1 h2 => by
          simp only [getElem_replaceAt]
          split
          · rename_i hih; subst hih
            have r1 := (hch1 i h1).raw avatar P (hs1 _ (List.getElem_mem h1))
            have r2 := hor.raw avatar P hors
            exact ⟨r1.1.trans r2.1.symm, fun hi' => (r1.2.1 hi').trans (r2.2.1 (r2.1.trans (r1.1.symm.trans hi'))).symm⟩
          · exact ⟨rfl, fun _ => rfl⟩)
      obtain ⟨hsn', hl'⟩ := lay_transfer avatar hraw hsn1 hl1
      have h5h : c.ch.head!.op = 5 := hall _ hhead
      refine .tup h5h hhe' rfl (by rw [D_encoding_withCh]; exact hm1) hl'
        (by rw [D_leadingBytes_withCh]; exact hlb1) ?_ (by rw [length_replaceAt]; exact hk1) ?_ hsn'
      · intro y hy
        rcases mem_replaceAt hy with hy | rfl
        · exact hs1 y hy
        · exact hors
      · intro i hi'
        simp only [getElem_replaceAt]
        split
        · rename_i hih; subst hih; exact hor
        · exact hch1 i (by rw [length_replaceAt] at hi'; exact hi')
    · split at hp
      · -- all `And`
        rename_i _ hall
        simp only [List.all_eq_true, beq_iff_eq] at hall
        obtain ⟨nch, hm, rfl⟩ := Option.map_eq_some_iff.1 hp
        unfold mergeAnd at hm
        split at hm; · simp at hm
        split at hm; · simp at hm
        split at hm; · simp at hm
        rename_i hok
        have hok' : hingeOk c.ch = true := by simpa using hok
        split at hm; · simp at hm
        split at hm; · simp at hm
        simp only [Option.some.injEq] at hm
        subst hm
        obtain ⟨he0, hch0⟩ := (hch _ hhead).logical_ch avatar P (Or.inl (hall _ hhead))
        have hys : ∀ y ∈ c.ch.map (fun o => o.ch[hingeOf c.ch o]!), F y m := by
          intro y hy
          obtain ⟨o, ho, rfl⟩ := List.mem_map.1 hy
          have hlt := (hingeOk_spec hok' o ho).1
          rw [getElem!_eq hlt]
          exact ((hch o ho).logical_ch avatar P (Or.inl (hall o ho))).2 _ (List.getElem_mem hlt)
        have h1h : c.ch.head!.op = 1 := hall _ hhead
        apply logical_withCh avatar P (c := c.ch.head!) (Or.inl h1h) he0
        intro y hy
        rcases mem_replaceAt hy with hy | rfl
        · exact hch0 y hy
        · exact orNode_fits avatar P hys
      · simp at hp
  · simp at hp

/-- A `Matches` at a variant: a call interpretation, fitting its candidate. -/
theorem Fits.var_inv {o : Cond} {m : Condition} (h : F o m) (hv : isVarLay m = true) (h5 : o.op = 5) :
    o.enc = 5 ∧ ∃ k ∈ m.children, k.encoding = .AbiEncoded ∧ k.compValue = prefixOf 5 o.cv ∧
      KeyUnique m k ∧ F o k ∧ LayEq (D avatar o) m := by
  have hmd : m.encoding = .Dynamic := by unfold isVarLay at hv; simp at hv; exact hv.2
  cases h with
  | varAbi _ he _ _ hl hmem hke hkey hu hf => exact ⟨he, _, hmem, hke, hkey, hu, hf, hl⟩
  | tup _ he _ hm =>
    exfalso; rw [hmd, D_encoding] at hm
    rcases he with h | h <;> simp [h, encN, ConditionPacking.encOf?] at hm
  | pass h0 => omega
  | ns _ hns _ =>
    cases hns with
    | leaf _ _ hop => simp [nsOp, h5] at hop
    | logical hop => omega
  | logical hop => omega
  | arr _ _ _ hm => rw [hmd] at hm; cases hm
  | slice h13 => omega
  | leaf hop => simp [leafOp, h5] at hop
  | varDyn _ he2 _ hf =>
    exfalso; obtain ⟨_, _, h5', _, _⟩ := hf.plain_dyn avatar P he2; exact h5' h5
  | zip hop => omega
  | zipLogical hop => omega

theorem KeyUnique.eq {m k k' : Condition} (hu : KeyUnique m k) (hm : k' ∈ m.children)
    (he : k'.compValue = k.compValue) : k' = k := by
  by_cases h : k' = k
  · exact h
  · exact absurd (he ▸ List.prefix_refl _) (hu k' hm h).1

theorem pushStep_fits {c n : Cond} {m : Condition} (h : F c m) (hp : pushStep c = some n) : F n m := by
  cases hv : isVarLay m
  · exact pushStep_fits_nv avatar P h (fun _ => hv) hp
  cases hall : c.ch.all (·.op == 5)
  · exact pushStep_fits_nv avatar P h (fun h' => by rw [hall] at h'; cases h') hp
  -- a variant `Or` of call interpretations with one compValue: merged at
  -- their common candidate
  have hp' := hp
  unfold pushStep at hp'
  split at hp'
  · rename_i hcond
    obtain ⟨nch, hm, rfl⟩ := Option.map_eq_some_iff.1 hp'
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, Bool.not_eq_true',
      List.all_eq_true, List.any_eq_false] at hcond
    obtain ⟨⟨⟨h2, hlen⟩, _⟩, _⟩ := hcond
    obtain ⟨he0, hch⟩ := h.logical_ch avatar P (Or.inr h2)
    have hhead : c.ch.head! ∈ c.ch := by
      obtain ⟨x, xs, hc⟩ : ∃ x xs, c.ch = x :: xs := by
        cases hc : c.ch with
        | nil => rw [hc] at hlen; simp at hlen
        | cons x xs => exact ⟨x, xs, rfl⟩
      rw [hc]; exact List.mem_cons.2 (Or.inl rfl)
    simp only [List.all_eq_true, beq_iff_eq] at hall
    have hcv : ∀ o ∈ c.ch, o.cv = c.ch.head!.cv := by
      unfold mergeMatches at hm
      split at hm; · simp at hm
      split at hm; · simp at hm
      rename_i hc
      intro o ho
      have hc' : c.ch.all (fun x => x.cv == c.ch.head!.cv) = true := by
        cases h' : c.ch.all (fun x => x.cv == c.ch.head!.cv)
        · rw [h'] at hc; simp at hc
        · rfl
      simpa using List.all_eq_true.1 hc' o ho
    obtain ⟨he5, k0, hmem0, hke0, hkey0, hu0, _, hl0⟩ := (hch _ hhead).var_inv avatar P hv (hall _ hhead)
    have hk : ∀ o ∈ c.ch, F o k0 := by
      intro o ho
      obtain ⟨_, k, hmem, _, hkey, _, hf, _⟩ := (hch o ho).var_inv avatar P hv (hall o ho)
      have : k = k0 := hu0.eq hmem (by rw [hkey, hkey0, hcv o ho])
      exact this ▸ hf
    have hck : F c k0 := by
      have := logical_withCh avatar P (c := c) (Or.inr h2) he0 c.ch hk
      rwa [withCh_eq_self rfl] at this
    have hn := pushStep_fits_nv avatar P hck (fun _ => by simp [isVarLay, hke0]) hp
    exact .varAbi (hall c.ch.head! hhead) he5 rfl hv (layEq_abi avatar he5 he5 hl0) hmem0 hke0 hkey0 hu0 hn
  · simp at hp'

theorem pushDownOr_fits {c : Cond} {m : Condition} (f : Cond → Cond) (hf : ∀ n, F n m → F (f n) m)
    (h : F c m) : F (pushDownOr f c) m := by
  unfold pushDownOr
  split
  · rename_i n hn; exact hf n (pushStep_fits avatar P h hn)
  · exact h

end
end Bridge
