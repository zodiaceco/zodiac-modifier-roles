import Bridge.Leaves

/-!
# Adequacy

`adequacy`: for a tree that fits layout `m`, on calldata that decodes as
`m`, the evaluator transcription and the contract world agree.
-/

namespace Bridge
open DecoderFaithfulness DecoderFaithfulness.Roles Normalize Evaluate

/-! ## Helpers -/

theorem childrenLoop_length (data : Calldata) (loc : Nat) (f : Nat → Condition) :
    ∀ (k i h : Nat) (locs : List Nat), childrenLoop data loc f k i h = some locs → locs.length = k
  | 0, _, _, locs, h => by simp [childrenLoop] at h; simp [← h]
  | k + 1, i, h, locs, hk => by
    simp only [childrenLoop] at hk
    cases hfi : (f i).inlined <;> simp only [hfi, Bool.false_eq_true, ite_false, ite_true] at hk <;>
    · split at hk
      · simp at hk
      · obtain ⟨rest, hrest, rfl⟩ := Option.map_eq_some_iff.1 hk
        simp [childrenLoop_length data loc f k _ _ rest hrest]

theorem assign_struct {V : Type} (d : V) : ∀ (cs : List Cond) (fs : List V) (v : V),
    (∀ x ∈ cs, isStruct x = true) → cs.length ≤ fs.length → assign d cs fs v = cs.zip fs
  | [], _, _, _, _ => by simp [assign]
  | _ :: _, [], _, _, h => by simp at h
  | c :: cs, f :: fs, v, hs, hl => by
    simp only [assign, hs c (by simp), if_true, List.headD_cons, List.tail_cons, List.zip_cons_cons]
    rw [assign_struct d cs fs v (fun x hx => hs x (by simp [hx])) (by simp at hl; omega)]

section
variable (avatar : Bytes) (env : Env) (henv : EnvOk env) (data : Calldata) (n : Nat)

abbrev W := contractWorld avatar env data n

theorem Corr.of_map {α : Type} (f : Nat) (g : α → Condition × Nat) (h : α → T) :
    ∀ (xs : List α), (∀ x ∈ xs, ∀ cons sl,
      Rel (evalC env data n f (g x).2 (g x).1 cons sl) (h x sl (toMap cons))) →
      Corr env data n f (xs.map g) (xs.map h)
  | [], _ => .nil
  | x :: xs, hx => .cons (hx x (by simp)) (Corr.of_map f g h xs fun y hy => hx y (by simp [hy]))

theorem Fits.layEq {x : Cond} {d m : Condition} (h : Fits avatar x d m) (hs : isStruct x = true) :
    LayEq d m := by
  cases h with
  | pass _ _ _ hl _ _ _ => exact hl
  | ns hns => rw [hns] at hs; exact absurd hs (by simp)
  | logical _ _ _ _ hl _ _ => exact hl
  | tup _ _ _ _ hl _ _ _ _ _ => exact hl
  | arr _ _ _ _ hl _ _ _ _ => exact hl
  | slice _ _ _ hl _ _ _ _ _ => exact hl
  | leaf _ _ _ ht _ _ _ _ _ _ _ _ => exact ht.layEq

theorem cvOf_plain {c : Cond} (h15 : c.op ≠ 15) (h16 : c.op ≠ 16) (h5 : c.enc ≠ 5) :
    cvOf avatar c = toBytes c.cv := by
  unfold cvOf; simp [h15, h16, h5]

theorem sem_ext {c : Cond} (h0 : c.op ≠ 0) (h1 : c.op ≠ 1) (h2 : c.op ≠ 2) (h5 : c.op ≠ 5)
    (v : Val') :
    sem (W avatar env data n) c v = extW avatar env data n c.enc c.op c.cv (c.ch.map (sem (W avatar env data n))) v := by
  rw [sem_eq]
  simp only [h0, h1, h2, ite_false]
  rw [ite_neg' (by omega)]
  rfl

include henv in
/-- The operators that read one value, given how the node and the layout
    agree. -/
theorem ext_rel (c : Cond) (d m : Condition) (f l : Nat) (cons : List Consumption) (sl : Slots)
    (ss : List (Val' → T))
    (hop : d.operator = opN c.op) (hops : c.op = 4 ∨ leafOp c.op = true) (henc : c.enc ≠ 5)
    (hin : input data l d = inputAt data c.enc m l)
    (hlay : c.op = 21 → d.inlined = m.inlined ∧ d.size = m.size)
    (hcs : c.op = 22 → (if d.size ≠ 0 then d.size else size data l d) = customSize data c.enc m l)
    (hcv : d.compValue = cvOf avatar c)
    (hinl : c.op = 16 → (if c.enc = 0 ∨ c.enc = 6 then true else m.inlined) = isInl c)
    (hk : c.op = 14 → ∃ k ∈ c.cv.head?, k % 256 < n) :
    Rel (evalC env data n (f + 1) l d cons sl)
      (extW avatar env data n c.enc c.op c.cv ss (m, l) sl (toMap cons)) := by
  rcases c with ⟨e, o, cv, ch⟩
  simp only at hop hops henc hin hlay hcs hcv hinl hk ⊢
  rcases hops with rfl | hops
  · exact empty_rel avatar env data n f l d m e cv ss cons sl (by rw [hop]; rfl)
  unfold leafOp at hops
  simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq] at hops
  have hplain : o ≠ 15 → o ≠ 16 → d.compValue = toBytes cv := fun a b => by
    rw [hcv]; exact cvOf_plain avatar a b henc
  rcases hops with ((rfl | ⟨h1, h2⟩) | rfl) | rfl
  · exact pluck_rel avatar env data n f l d m e cv ss cons sl (by rw [hop]; rfl)
      (hplain (by decide) (by decide)) hin (hk rfl)
  · have : o = 15 ∨ o = 16 ∨ o = 17 ∨ o = 18 ∨ o = 19 ∨ o = 20 ∨ o = 21 ∨ o = 22 ∨ o = 23 := by
      omega
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact cmp_rel avatar env data n f l d m e 15 cv ss cons sl (by decide) hop hin
        (by rw [hcv]; unfold cvOf cmpValue; simp)
    · refine cmp_rel avatar env data n f l d m e 16 cv ss cons sl (by decide) hop hin ?_
      rw [hcv]
      have hi := hinl rfl
      unfold cvOf cmpValue
      simp only [henc, ite_false]
      by_cases he : e = 0 ∨ e = 6
      · simp only [he, ite_true] at hi
        simp [he, ← hi]
      · simp only [he, ite_false] at hi
        simp [he, hi]
    all_goals first
      | exact cmp_rel avatar env data n f l d m e _ cv ss cons sl (by decide) hop hin
          (by rw [hplain (by decide) (by decide)]; unfold cmpValue; simp)
      | exact bitmask_rel avatar env data n f l d m e cv ss cons sl (by rw [hop]; rfl)
          (hplain (by decide) (by decide)) (hlay rfl)
      | exact custom_rel avatar env henv data n f l d m e cv ss cons sl (by rw [hop]; rfl)
          (hplain (by decide) (by decide)) (hcs rfl)
      | exact ratio_rel avatar env henv data n f l d m e cv ss cons sl (by rw [hop]; rfl)
          (hplain (by decide) (by decide))
  · exact wa_rel avatar env henv data n f l d m e cv ss cons sl (by rw [hop]; rfl)
      (hplain (by decide) (by decide)) hin
  · exact cwa_rel avatar env henv data n f l d m e cv ss cons sl (by rw [hop]; rfl)
      (hplain (by decide) (by decide))

theorem fuel_succ {c : Cond} {fuel : Nat} (h : height c < fuel) : ∃ f, fuel = f + 1 ∧ height c ≤ f :=
  ⟨fuel - 1, by omega, by omega⟩

theorem height_pos (c : Cond) : 0 < height c := by rcases c; simp [height]

theorem evalC_pass (f l : Nat) (d : Condition) (cons : List Consumption) (sl : Slots)
    (hd : d.operator = .Pass) : evalC env data n (f + 1) l d cons sl = Evaluate.ok cons sl := by
  rw [evalC, hd]

theorem evalC_and (f l : Nat) (d : Condition) (cons : List Consumption) (sl : Slots)
    (hd : d.operator = .And) :
    evalC env data n (f + 1) l d cons sl = seqLoop env data n f (d.children.map (·, l)) cons sl := by
  rw [evalC, hd]

theorem evalC_or (f l : Nat) (d : Condition) (cons : List Consumption) (sl : Slots)
    (hd : d.operator = .Or) :
    evalC env data n (f + 1) l d cons sl = orLoop env data n f d.children l cons sl := by
  rw [evalC, hd]

theorem D_encoding_ns {c : Cond} (he : c.enc = 0 ∨ c.enc = 6) : (D avatar c).encoding = .None := by
  rw [D_encoding]; rcases he with h | h <;> simp [h, encN, ConditionPacking.encOf?]

theorem isInl_leaf {c : Cond} (he : c.enc = 0 ∨ c.enc = 6) (hch : c.ch = []) : isInl c = true := by
  rcases c with ⟨e, o, cv, ch⟩
  simp only at he hch; subst hch
  rcases he with rfl | rfl <;> rfl

theorem D_size_leaf {c : Cond} (he : c.enc = 0 ∨ c.enc = 6) (hch : c.ch = []) : (D avatar c).size = 0 := by
  unfold D
  rw [annotate_size, toRoles_eq, hch]
  rcases he with h | h <;> simp [h, encN, ConditionPacking.encOf?, isInlined, isInlinedAll,
    inlinedSize, inlinedSizeLoop]

include henv in
/-- Non-structural subtrees read no calldata location: any layout fits. -/
theorem ns_adequacy : ∀ {c : Cond}, NsOk c → ∀ (m : Condition) (fuel l : Nat) (cons : List Consumption)
    (sl : Slots), height c < fuel → CvOk n c →
    Rel (evalC env data n fuel l (D avatar c) cons sl)
      (sem (W avatar env data n) c (m, l) sl (toMap cons)) := by
  intro c hns
  induction hns with
  | @leaf c he hch hop =>
    intro m fuel l cons sl hh hcv
    obtain ⟨f, rfl, -⟩ := fuel_succ hh
    unfold nsOp at hop
    simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq] at hop
    by_cases h0 : c.op = 0
    · rw [evalC_pass env data n f l _ cons sl (by rw [D_operator, h0]; rfl), sem_eq, ite_pos' h0]
      exact Rel.ok cons sl
    have hops : c.op = 4 ∨ leafOp c.op = true := by
      unfold leafOp; simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq]
      omega
    rw [sem_ext avatar env data n h0 (by omega) (by omega) (by omega)]
    rw [cvOk_eq] at hcv
    have hDenc := D_encoding_ns avatar he
    refine ext_rel avatar env henv data n c (D avatar c) m f l cons sl _ (D_operator avatar c) hops
      (by rcases he with h | h <;> omega) ?_ ?_ ?_ (D_compValue avatar c) ?_ hcv.2.2.1
    · unfold input inputAt; simp [hDenc, he]
    · intro h21; omega
    · intro _
      rw [D_size_leaf avatar he hch, size_eq, hDenc, D_children, hch]
      unfold customSize
      simp [he, sizeNone]
    · intro _; simp [he, isInl_leaf he hch]
  | @logical c hop _ hall ih =>
    intro m fuel l cons sl hh hcv
    obtain ⟨f, rfl, hf⟩ := fuel_succ hh
    have hcorr : Corr env data n f (c.ch.map fun x => (D avatar x, l))
        (c.ch.map fun x => sem (W avatar env data n) x (m, l)) :=
      Corr.of_map env data n f _ _ c.ch fun x hx cons sl =>
        ih x hx m f l cons sl (by have := height_mem hx; omega) (hcv.child hx)
    rcases hop with h1 | h2
    · rw [evalC_and env data n f l _ cons sl (by rw [D_operator, h1]; rfl), sem_eq,
        ite_neg' (by omega), ite_pos' h1, D_children, List.map_map]
      exact seqLoop_rel env data _ _ hcorr cons sl
    · rw [evalC_or env data n f l _ cons sl (by rw [D_operator, h2]; rfl), sem_eq,
        ite_neg' (by omega), ite_neg' (by omega), ite_pos' h2, D_children]
      refine orLoop_rel env data l ?_ cons sl
      rw [List.map_map]; exact hcorr

theorem evalC_matches (f l : Nat) (d : Condition) (cons : List Consumption) (sl : Slots)
    (hd : d.operator = .Matches) :
    evalC env data n (f + 1) l d cons sl =
      match leadingCheck data (if l > 0 ∧ d.encoding = .AbiEncoded then l + 32 else l) d.compValue with
      | some s => violation s sl
      | none =>
        match childrenE data ((if l > 0 ∧ d.encoding = .AbiEncoded then l + 32 else l) + d.leadingBytes) d with
        | .inl s => violation s sl
        | .inr none => violation sCalldataOverflow sl
        | .inr (some locs) =>
          if d.children.length ≠ locs.length then violation sParameterNotAMatch sl
          else seqLoop env data n f (d.children.zip locs) cons sl := by
  rw [evalC, hd]; rfl

theorem Corr.of_idx (f : Nat) : ∀ (ps : List (Condition × Nat)) (ts : List T), ps.length = ts.length →
    (∀ i (h1 : i < ps.length) (h2 : i < ts.length), ∀ cons sl,
      Rel (evalC env data n f ps[i].2 ps[i].1 cons sl) (ts[i] sl (toMap cons))) →
    Corr env data n f ps ts
  | [], [], _, _ => .nil
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | p :: ps, t :: ts, h, hi => .cons (hi 0 (by simp) (by simp)) (Corr.of_idx f ps ts (by simpa using h)
      fun i h1 h2 => hi (i + 1) (by simpa using h1) (by simpa using h2))

theorem leadingCheck_cases (data : Calldata) (loc : Nat) (cv : Bytes) (h : cv.length ≤ 32) :
    leadingCheck data loc cv = none ∨ leadingCheck data loc cv = some sCalldataOverflow ∨
      leadingCheck data loc cv = some sLeadingBytesNotAMatch := by
  unfold leadingCheck
  repeat' split
  all_goals first | (left; rfl) | (right; left; rfl) | (right; right; rfl) | omega

theorem encN_ne_ether {e : Nat} (h : e = 3 ∨ e = 4 ∨ e = 5 ∨ e = 1 ∨ e = 2) : encN e ≠ .EtherValue := by
  rcases h with rfl | rfl | rfl | rfl | rfl <;> decide

theorem D_encoding_of {c : Cond} (h : c.enc = 3 ∨ c.enc = 4 ∨ c.enc = 5 ∨ c.enc = 1 ∨ c.enc = 2) :
    (D avatar c).encoding = encN c.enc := by
  rw [D_encoding, if_neg (encN_ne_ether h)]

theorem prefixOf_cvOf {c : Cond} (h5 : c.op = 5) (he : c.enc = 3 ∨ c.enc = 5) :
    cvOf avatar c = prefixOf c.enc c.cv := by
  unfold cvOf prefixOf
  rcases he with h | h
  · simp [h, h5]
  · simp only [h5, h, ite_true]
    simp
    split
    · rename_i hc; simp [hc, toBytes]
    · rfl

theorem childrenE_plain (data : Calldata) (L : Nat) (d : Condition) (h : d.encoding ≠ .Array) :
    childrenE data L d = .inr (children data L d) := by
  unfold childrenE allocPanics; simp [h]

theorem children_plain (data : Calldata) (L : Nat) (d : Condition) (h : d.encoding ≠ .Array) :
    children data L d = childrenLoop data L (fun i => d.children.getD i default) d.children.length 0 0 := by
  unfold children; simp [h]

theorem decodeAt_some {data : Calldata} {e : Nat} {m : Condition} {l : Nat} {locs : List Nat}
    (hm : m.encoding ≠ .Array) (h : decodeAt data e m l = some locs) :
    children data (adjust e l + m.leadingBytes) m = some locs := by
  unfold decodeAt at h
  rw [childrenE_plain data _ m hm] at h
  split at h
  · rename_i heq; simp only [Sum.inr.injEq] at heq; rw [heq]; simpa using h
  · simp at h

include henv in
theorem tup_rel {c : Cond} {m : Condition} (f l : Nat) (cons : List Consumption) (sl : Slots)
    (h5 : c.op = 5) (he : c.enc = 3 ∨ c.enc = 5) (hm : (D avatar c).encoding = m.encoding)
    (hlb : (D avatar c).leadingBytes = m.leadingBytes)
    (hs : ∀ x ∈ c.ch, isStruct x = true) (hk : c.ch.length ≤ m.children.length)
    (hlay : ∀ i (h : i < c.ch.length), LayEq (D avatar c.ch[i]) (m.children.getD i default))
    (ih : ∀ i (h : i < c.ch.length) (l' : Nat), Decodable data (m.children.getD i default) l' →
      ∀ cons sl, Rel (evalC env data n f l' (D avatar c.ch[i]) cons sl)
        (sem (W avatar env data n) c.ch[i] (m.children.getD i default, l') sl (toMap cons)))
    (hcv : (prefixOf c.enc c.cv).length ≤ 32) (hdec : Decodable data m l) :
    Rel (evalC env data n (f + 1) l (D avatar c) cons sl)
      (sem (W avatar env data n) c (m, l) sl (toMap cons)) := by
  have hDe := D_encoding_of avatar (c := c) (by omega)
  have hsem : sem (W avatar env data n) c (m, l) = matchesT (W avatar env data n) c.enc c.cv c.ch (m, l) := by
    have h0 : ¬ c.op = 0 := by omega
    have h1 : ¬ c.op = 1 := by omega
    have h2 : ¬ c.op = 2 := by omega
    rw [sem_eq, ite_neg' h0, ite_neg' h1, ite_neg' h2, ite_pos' ⟨h5, he⟩]
  rw [evalC_matches env data n f l _ cons sl (by rw [D_operator, h5]; rfl), hsem]
  unfold matchesT
  have hadj : (if l > 0 ∧ (D avatar c).encoding = .AbiEncoded then l + 32 else l) = adjust c.enc l := by
    rw [hDe]; unfold adjust
    rcases he with h | h <;> simp [h, encN, ConditionPacking.encOf?]
  have hnarr : m.encoding ≠ .Array := by
    rw [← hm, hDe]; rcases he with h | h <;> simp [h, encN, ConditionPacking.encOf?]
  have hnarrD : (D avatar c).encoding ≠ .Array := by rw [hm]; exact hnarr
  rw [hadj, D_compValue, prefixOf_cvOf avatar h5 he]
  show Rel _ (if ((leadingCheck data (adjust c.enc l) (prefixOf c.enc c.cv)).isNone &&
      (decodeAt data c.enc m l).isSome) = true then _ else _)
  rcases leadingCheck_cases data (adjust c.enc l) (prefixOf c.enc c.cv) hcv with h | h | h
  · rw [h]
    simp only [Option.isNone_none, Bool.true_and]
    cases hdec with
    | leaf h1 h2 _ =>
      exfalso; rw [← hm, hDe] at h1 h2; rcases he with h | h <;> simp_all [encN, ConditionPacking.encOf?]
    | arr _ h1 _ _ => exact absurd h1 hnarr
    | tup locsM _ hdl hdch =>
      have hde : decodeAt data c.enc m l = some locsM := by
        have : (if m.encoding = .AbiEncoded then 5 else 3) = c.enc := by
          rw [← hm, hDe]; rcases he with h | h <;> simp [h, encN, ConditionPacking.encOf?]
        unfold decodeL at hdl; rw [this] at hdl; exact hdl
      have hcm := decodeAt_some hnarr hde
      rw [children_plain data _ m hnarr] at hcm
      have hK := childrenLoop_length data _ _ _ _ _ _ hcm
      have hpre := childrenLoop_prefix data _ _ c.ch.length m.children.length 0 0 locsM hk hcm
      have hDch := D_children avatar c
      have hcd : children data (adjust c.enc l + m.leadingBytes) (D avatar c) =
          some (locsM.take c.ch.length) := by
        rw [children_plain data _ _ hnarrD, hDch, List.length_map, ← hpre]
        apply childrenLoop_congr
        intro j _ hj
        simp only [Nat.zero_add] at hj
        have := hlay j hj
        simpa [List.getElem?_map, List.getElem?_eq_getElem hj, List.getD_eq_getElem?_getD] using this
      rw [hlb, childrenE_plain data _ _ hnarrD, hcd, hde]
      simp only [Option.isSome_some, ite_true]
      have hlen : (D avatar c).children.length = (locsM.take c.ch.length).length := by
        rw [hDch]; simp; omega
      rw [if_neg (by rw [hlen]; exact fun h => h rfl)]
      have hfields : (W avatar env data n).fields c.enc (m, l) = m.children.zip locsM := by
        show (match decodeAt data c.enc m l with
          | some locs => m.children.zip locs
          | none => []) = _
        rw [hde]
      rw [hfields, assign_struct _ c.ch _ _ hs (by simp; omega)]
      refine seqLoop_rel env data _ _ (Corr.of_idx env data n f _ _ (by simp [hDch]; omega) ?_) cons sl
      intro i h1 h2 cons' sl'
      have hi : i < c.ch.length := by simp at h1; omega
      have hiK : i < locsM.length := by omega
      have hgm : m.children.getD i default = m.children[i]'(by omega) := by
        simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show i < m.children.length by omega)]
      have := ih i hi locsM[i] (hdch i hiK) cons' sl'
      rw [hgm] at this
      simpa [hDch] using this
  · rw [h]; exact Rel.violation (by decide) (by decide) sl
  · rw [h]; exact Rel.violation (by decide) (by decide) sl

theorem childrenE_arr (data : Calldata) (l : Nat) (d m : Condition) (hd : d.encoding = .Array)
    (hm : m.encoding = .Array) (ht : LayEq (d.children.headD default) (m.children.headD default)) :
    childrenE data l d = childrenE data l m := by
  unfold childrenE allocPanics children
  simp only [hd, hm, ite_true]
  split
  · rfl
  · congr 2
    exact childrenLoop_congr data _ _ _ _ 0 0 fun _ _ _ => ht

theorem evalC_iter (f l : Nat) (d : Condition) (cons : List Consumption) (sl : Slots)
    (every : Bool) (hd : d.operator = if every then .ArrayEvery else .ArraySome) :
    evalC env data n (f + 1) l d cons sl =
      match childrenE data l d with
      | .inl s => violation s sl
      | .inr none => violation sCalldataOverflow sl
      | .inr (some locs) =>
        match d.children with
        | [] => if locs = [] then
                  (if d.operator = .ArrayEvery then Evaluate.ok cons sl
                   else violation sNoArrayElementPasses sl)
                else violation revert sl
        | ch :: _ =>
          if d.operator = .ArrayEvery then everyLoop env data n f ch locs cons sl
          else someLoop env data n f ch locs cons sl := by
  rw [evalC]
  cases every <;> simp only [hd, Bool.false_eq_true, ite_false, ite_true] <;> rfl

theorem evalC_tail (f l : Nat) (d : Condition) (cons : List Consumption) (sl : Slots)
    (hd : d.operator = .ArrayTailMatches) :
    evalC env data n (f + 1) l d cons sl =
      match childrenE data l d with
      | .inl s => violation s sl
      | .inr none => violation sCalldataOverflow sl
      | .inr (some locs) =>
        if locs.length < d.children.length then violation sParameterNotAMatch sl
        else seqLoop env data n f (d.children.zip (locs.drop (locs.length - d.children.length)))
          cons sl := by
  rw [evalC, hd]; rfl

theorem evalC_slice (f l : Nat) (d : Condition) (cons : List Consumption) (sl : Slots)
    (hd : d.operator = .Slice) :
    evalC env data n (f + 1) l d cons sl =
      match cvAt d.compValue 2 with
      | none => violation revert sl
      | some sz =>
        if d.inlined = false ∧ l + 32 > data.length then violation sCalldataOverflow sl
        else
          if shiftOf d.compValue + sz > (if d.inlined then d.size else load data l) then
            violation sCalldataOverflow sl
          else
            match d.children with
            | [] => violation revert sl
            | ch :: _ =>
              evalC env data n f (l + (if d.inlined then 0 else 32) + shiftOf d.compValue)
                (ch.withSize sz) cons sl := by
  rw [evalC, hd]; rfl

theorem sem_ext' {c : Cond} (h0 : c.op ≠ 0) (h1 : c.op ≠ 1) (h2 : c.op ≠ 2)
    (h5 : ¬(c.op = 5 ∧ (c.enc = 3 ∨ c.enc = 5))) (v : Val') :
    sem (W avatar env data n) c v =
      extW avatar env data n c.enc c.op c.cv (c.ch.map (sem (W avatar env data n))) v := by
  rw [sem_eq]
  simp only [h0, h1, h2, ite_false]
  rw [ite_neg' h5]
  rfl

theorem D_enc_arr {c : Cond} (he : c.enc = 4) : (D avatar c).encoding = .Array := by
  rw [D_encoding_of avatar (by omega), he]; rfl

theorem Decodable.arr_locs {data : Calldata} {m : Condition} {l : Nat} (hm : m.encoding = .Array)
    (h : Decodable data m l) :
    ∃ locs, childrenE data l m = .inr (some locs) ∧ ∀ l' ∈ locs, Decodable data (tmpl m) l' := by
  cases h with
  | leaf _ _ h3 => exact absurd hm h3
  | tup _ h1 _ _ => rcases h1 with h1 | h1 <;> rw [hm] at h1 <;> exact absurd h1 (by decide)
  | arr locs _ h2 h3 => exact ⟨locs, h2, h3⟩

include henv in
theorem iter_rel {c : Cond} {m : Condition} (f l : Nat) (cons : List Consumption) (sl : Slots)
    (every : Bool) (hop : c.op = if every then 7 else 6) (he : c.enc = 4) (hm : m.encoding = .Array)
    {x : Cond} {xs : List Cond} (hch : c.ch = x :: xs) (hlx : LayEq (D avatar x) (tmpl m))
    (ih : ∀ l', Decodable data (tmpl m) l' → ∀ cons sl,
      Rel (evalC env data n f l' (D avatar x) cons sl)
        (sem (W avatar env data n) x (tmpl m, l') sl (toMap cons)))
    (hdec : Decodable data m l) :
    Rel (evalC env data n (f + 1) l (D avatar c) cons sl)
      (sem (W avatar env data n) c (m, l) sl (toMap cons)) := by
  have hDop : (D avatar c).operator = if every then .ArrayEvery else .ArraySome := by
    rw [D_operator, hop]; cases every <;> rfl
  have hDch : (D avatar c).children = D avatar x :: xs.map (D avatar) := by
    rw [D_children, hch]; rfl
  rw [evalC_iter env data n f l _ cons sl every hDop]
  rw [sem_ext' avatar env data n (by cases every <;> simp_all) (by cases every <;> simp_all)
    (by cases every <;> simp_all) (by cases every <;> simp_all)]
  obtain ⟨locs, hlocs, hdl⟩ := hdec.arr_locs hm
  have hce : childrenE data l (D avatar c) = .inr (some locs) := by
    rw [childrenE_arr data l _ m (D_enc_arr avatar he) hm (by rw [hDch]; exact hlx), hlocs]
  rw [hce, hDch]
  simp only
  have hcorr : Corr env data n f (locs.map (D avatar x, ·))
      (locs.map fun l' => sem (W avatar env data n) x (tmpl m, l')) :=
    Corr.of_map env data n f _ _ locs fun l' hl' cons sl => ih l' (hdl l' hl') cons sl
  have hhead : (c.ch.map (sem (W avatar env data n))).headD passK = sem (W avatar env data n) x := by
    rw [hch]; rfl
  cases every
  · simp only [hop, ite_false] at hDop ⊢
    rw [hDop]
    show Rel _ (iterT data false c.enc _ (m, l) sl (toMap cons))
    unfold iterT
    rw [he, hhead, hlocs]
    simp only [ne_eq, not_true_eq_false, ite_false, Bool.false_eq_true]
    exact someLoop_rel env data (D avatar x) hcorr cons sl
  · simp only [hop, ite_true] at hDop ⊢
    rw [hDop]
    show Rel _ (iterT data true c.enc _ (m, l) sl (toMap cons))
    unfold iterT
    rw [he, hhead, hlocs]
    simp only [ne_eq, not_true_eq_false, ite_false, ite_true]
    exact everyLoop_rel env data (D avatar x) hcorr cons sl

include henv in
theorem tail_rel {c : Cond} {m : Condition} (f l : Nat) (cons : List Consumption) (sl : Slots)
    (hop : c.op = 8) (he : c.enc = 4) (hm : m.encoding = .Array) (hne : c.ch ≠ [])
    (hlx : ∀ x ∈ c.ch, LayEq (D avatar x) (tmpl m))
    (ih : ∀ x ∈ c.ch, ∀ l', Decodable data (tmpl m) l' → ∀ cons sl,
      Rel (evalC env data n f l' (D avatar x) cons sl)
        (sem (W avatar env data n) x (tmpl m, l') sl (toMap cons)))
    (hdec : Decodable data m l) :
    Rel (evalC env data n (f + 1) l (D avatar c) cons sl)
      (sem (W avatar env data n) c (m, l) sl (toMap cons)) := by
  obtain ⟨x, xs, hch⟩ : ∃ x xs, c.ch = x :: xs := by
    cases h : c.ch with
    | nil => exact absurd h hne
    | cons x xs => exact ⟨x, xs, rfl⟩
  have hDch := D_children avatar c
  rw [evalC_tail env data n f l _ cons sl (by rw [D_operator, hop]; rfl)]
  rw [sem_ext' avatar env data n (by omega) (by omega) (by omega) (by omega)]
  obtain ⟨locs, hlocs, hdl⟩ := hdec.arr_locs hm
  have hce : childrenE data l (D avatar c) = .inr (some locs) := by
    rw [childrenE_arr data l _ m (D_enc_arr avatar he) hm
      (by rw [hDch, hch]; exact hlx x (by rw [hch]; simp)), hlocs]
  rw [hce, hop]
  show Rel _ (tailT data c.enc _ (m, l) sl (toMap cons))
  unfold tailT
  rw [he, hlocs]
  simp only [ne_eq, not_true_eq_false, ite_false, List.length_map, hDch]
  split
  · exact Rel.violation (by decide) (by decide) sl
  · rename_i hlt
    refine seqLoop_rel env data _ _ (Corr.of_idx env data n f _ _ (by simp) ?_) cons sl
    intro i h1 h2 cons' sl'
    have hi : i < c.ch.length := by simp at h1; omega
    have hmem : c.ch[i] ∈ c.ch := List.getElem_mem hi
    have hj : locs.length - c.ch.length + i < locs.length := by omega
    have hd := hdl (locs[locs.length - c.ch.length + i]) (List.getElem_mem hj)
    have := ih c.ch[i] hmem _ hd cons' sl'
    simpa [List.getElem_zip, List.getElem_drop, List.getElem_zipWith, List.getElem_map] using this

include henv in
theorem marr_rel {c : Cond} {m : Condition} (f l : Nat) (cons : List Consumption) (sl : Slots)
    (hop : c.op = 5) (he : c.enc = 4) (hm : m.encoding = .Array) (hne : c.ch ≠ [])
    (hlx : ∀ x ∈ c.ch, LayEq (D avatar x) (tmpl m))
    (ih : ∀ x ∈ c.ch, ∀ l', Decodable data (tmpl m) l' → ∀ cons sl,
      Rel (evalC env data n f l' (D avatar x) cons sl)
        (sem (W avatar env data n) x (tmpl m, l') sl (toMap cons)))
    (hcv : (prefixOf c.enc c.cv).length ≤ 32) (hdec : Decodable data m l) :
    Rel (evalC env data n (f + 1) l (D avatar c) cons sl)
      (sem (W avatar env data n) c (m, l) sl (toMap cons)) := by
  obtain ⟨x, xs, hch⟩ : ∃ x xs, c.ch = x :: xs := by
    cases h : c.ch with
    | nil => exact absurd h hne
    | cons x xs => exact ⟨x, xs, rfl⟩
  have hDch := D_children avatar c
  have hDe := D_enc_arr avatar he
  rw [evalC_matches env data n f l _ cons sl (by rw [D_operator, hop]; rfl)]
  rw [sem_ext' avatar env data n (by omega) (by omega) (by omega) (by omega)]
  obtain ⟨locs, hlocs, hdl⟩ := hdec.arr_locs hm
  have hlb : (D avatar c).leadingBytes = 0 := by
    rw [D_leadingBytes, he]; rfl
  have hce : childrenE data l (D avatar c) = .inr (some locs) := by
    rw [childrenE_arr data l _ m hDe hm
      (by rw [hDch, hch]; exact hlx x (by rw [hch]; simp)), hlocs]
  have hcvD : (D avatar c).compValue = toBytes c.cv := by
    rw [D_compValue]; exact cvOf_plain avatar (by omega) (by omega) (by omega)
  have hloc : (if l > 0 ∧ (D avatar c).encoding = .AbiEncoded then l + 32 else l) = l := by
    rw [hDe]; simp
  rw [hloc, hlb, Nat.add_zero, hce, hcvD, hop]
  show Rel _ (matchesArrT data c.enc c.cv _ (m, l) sl (toMap cons))
  unfold matchesArrT
  rw [he, hlocs]
  simp only [ne_eq, not_true_eq_false, ite_false]
  have hp : prefixOf c.enc c.cv = toBytes c.cv := by unfold prefixOf; simp [he]
  rw [hp] at hcv
  rcases leadingCheck_cases data l (toBytes c.cv) hcv with h | h | h
  · rw [h]
    simp only [List.length_map, hDch]
    split
    · exact Rel.violation (by decide) (by decide) sl
    · rename_i hlen
      refine seqLoop_rel env data _ _ (Corr.of_idx env data n f _ _ (by simp) ?_) cons sl
      intro i h1 h2 cons' sl'
      have hi : i < c.ch.length := by simp at h1; omega
      have hmem : c.ch[i] ∈ c.ch := List.getElem_mem hi
      have hil : i < locs.length := by simp at h1; omega
      have := ih c.ch[i] hmem _ (hdl _ (List.getElem_mem hil)) cons' sl'
      simpa [List.getElem_zip, List.getElem_zipWith, List.getElem_map] using this
  · rw [h]; exact Rel.violation (by decide) (by decide) sl
  · rw [h]; exact Rel.violation (by decide) (by decide) sl

include henv in
theorem slice_rel {c x : Cond} {d m : Condition} (f l : Nat) (cons : List Consumption) (sl : Slots)
    (hop : c.op = 13) (he : c.enc = 1 ∨ c.enc = 2) (hnode : Node avatar c d) (hlay : LayEq d m)
    (hch : c.ch = [x])
    (ih : ∀ sz l', ∀ cons sl,
      Rel (evalC env data n f l' { D avatar x with size := sz } cons sl)
        (sem (W avatar env data n) x (winMeta sz, l') sl (toMap cons)))
    (hcv : 3 ≤ c.cv.length) :
    Rel (evalC env data n (f + 1) l d cons sl) (sem (W avatar env data n) c (m, l) sl (toMap cons)) := by
  rw [evalC_slice env data n f l d cons sl (by rw [hnode.operator, hop]; rfl)]
  rw [sem_ext' avatar env data n (by omega) (by omega) (by omega) (by omega)]
  have hcvD : d.compValue = toBytes c.cv := by
    rw [hnode.compValue]; exact cvOf_plain avatar (by omega) (by omega) (by omega)
  rw [hcvD, hnode.children, hch, hop]
  show Rel _ (sliceT data c.enc c.cv _ (m, l) sl (toMap cons))
  unfold sliceT
  simp only [he, not_true_eq_false, ite_false, List.map_cons, List.map_nil, List.headD_cons]
  obtain ⟨b, bs, hb⟩ : ∃ b bs, c.cv = b :: bs := by
    cases h : c.cv with
    | nil => rw [h] at hcv; simp at hcv
    | cons b bs => exact ⟨b, bs, rfl⟩
  have hsz : ∃ sz, cvAt (toBytes c.cv) 2 = some sz := by
    unfold cvAt toBytes
    have : 2 < (c.cv.map fun n => (⟨n % 256, Nat.mod_lt _ (by decide)⟩ : Fin 256)).length := by
      simp; omega
    exact ⟨_, by rw [List.getElem?_eq_getElem this]; rfl⟩
  obtain ⟨sz, hsz⟩ := hsz
  rw [hsz]
  simp only
  rw [hlay.1, hlay.2]
  repeat' split
  all_goals first
    | exact Rel.violation (s := sCalldataOverflow) (by decide) (by decide) sl
    | exact ih sz _ cons sl
    | (exfalso; simp_all)

theorem leafOp_ne {o : Nat} (h : leafOp o = true) : o ≠ 0 ∧ o ≠ 1 ∧ o ≠ 2 ∧ o ≠ 5 ∧ o ≠ 4 := by
  unfold leafOp at h
  simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq] at h
  omega

theorem struct_enc {c : Cond} (hs : isStruct c = true) (h1 : c.op ≠ 1) (h2 : c.op ≠ 2) :
    c.enc ≠ 0 ∧ c.enc ≠ 6 := by
  rw [isStruct_eq] at hs
  have : (c.op == 1 || c.op == 2) = false := by simp [h1, h2]
  rw [this] at hs
  simp only [Bool.false_eq_true, ite_false, Bool.not_eq_true', Bool.or_eq_false_iff, beq_eq_false_iff_ne] at hs
  exact hs

include henv in
/-- **Adequacy.** The evaluator transcription computes the contract world's
    meaning, for every tree whose layout fits `m`, on calldata that decodes
    as `m`. -/
theorem adequacy {c : Cond} {d m : Condition} (hfit : Fits avatar c d m) :
    ∀ (fuel l : Nat) (cons : List Consumption) (sl : Slots), height c < fuel → CvOk n c →
      Decodable data m l →
      Rel (evalC env data n fuel l d cons sl) (sem (W avatar env data n) c (m, l) sl (toMap cons)) := by
  induction hfit with
  | @pass c d m hop hnode _ _ _ _ _ =>
    intro fuel l cons sl hh _ _
    obtain ⟨f, rfl, -⟩ := fuel_succ hh
    rw [evalC_pass env data n f l d cons sl (by rw [hnode.operator, hop]; rfl), sem_eq, ite_pos' hop]
    exact Rel.ok cons sl
  | @ns c d m _ hns hd =>
    intro fuel l cons sl hh hcv _
    subst hd
    exact ns_adequacy avatar env henv data n hns m fuel l cons sl hh hcv
  | @logical c d m hop _ _ hd _ _ _ ih =>
    intro fuel l cons sl hh hcv hdec
    obtain ⟨f, rfl, hf⟩ := fuel_succ hh
    subst hd
    have hcorr : Corr env data n f (c.ch.map fun x => (D avatar x, l))
        (c.ch.map fun x => sem (W avatar env data n) x (m, l)) :=
      Corr.of_map env data n f _ _ c.ch fun x hx cons sl =>
        ih x hx f l cons sl (by have := height_mem hx; omega) (hcv.child hx) hdec
    rcases hop with h1 | h2
    · rw [evalC_and env data n f l _ cons sl (by rw [D_operator, h1]; rfl), sem_eq,
        ite_neg' (by omega), ite_pos' h1, D_children, List.map_map]
      exact seqLoop_rel env data _ _ hcorr cons sl
    · rw [evalC_or env data n f l _ cons sl (by rw [D_operator, h2]; rfl), sem_eq,
        ite_neg' (by omega), ite_neg' (by omega), ite_pos' h2, D_children]
      refine orLoop_rel env data l ?_ cons sl
      rw [List.map_map]; exact hcorr
  | @tup c d m h5 he hd hm hlay hlb hs hk hch _ ih =>
    intro fuel l cons sl hh hcv hdec
    obtain ⟨f, rfl, hf⟩ := fuel_succ hh
    subst hd
    have hcv' := hcv
    rw [cvOk_eq] at hcv'
    exact tup_rel avatar env henv data n f l cons sl h5 he hm hlb hs hk
      (fun i h => Fits.layEq avatar (hch i h) (hs _ (List.getElem_mem h)))
      (fun i h l' hd' cons sl => ih i h f l' cons sl
        (by have := height_mem (List.getElem_mem h); omega)
        (hcv.child (List.getElem_mem h)) hd')
      (hcv'.1 h5) hdec
  | @arr c d m hop he hd hm _ hne hs hch _ ih =>
    intro fuel l cons sl hh hcv hdec
    obtain ⟨f, rfl, hf⟩ := fuel_succ hh
    subst hd
    have hlx : ∀ x ∈ c.ch, LayEq (D avatar x) (tmpl m) := fun x hx =>
      Fits.layEq avatar (hch x hx) (hs x hx)
    have ih' : ∀ x ∈ c.ch, ∀ l', Decodable data (tmpl m) l' → ∀ cons sl,
        Rel (evalC env data n f l' (D avatar x) cons sl)
          (sem (W avatar env data n) x (tmpl m, l') sl (toMap cons)) :=
      fun x hx l' hd' cons sl => ih x hx f l' cons sl
        (by have := height_mem hx; omega) (hcv.child hx) hd'
    have hcv' := hcv
    rw [cvOk_eq] at hcv'
    rcases hop with h | h | h | h
    · exact marr_rel avatar env henv data n f l cons sl h he hm hne hlx ih' (hcv'.1 h) hdec
    · obtain ⟨x, xs, hx⟩ : ∃ x xs, c.ch = x :: xs := by
        cases h' : c.ch with
        | nil => exact absurd h' hne
        | cons x xs => exact ⟨x, xs, rfl⟩
      exact iter_rel avatar env henv data n f l cons sl false (by simp [h]) he hm hx
        (hlx x (by rw [hx]; simp)) (ih' x (by rw [hx]; simp)) hdec
    · obtain ⟨x, xs, hx⟩ : ∃ x xs, c.ch = x :: xs := by
        cases h' : c.ch with
        | nil => exact absurd h' hne
        | cons x xs => exact ⟨x, xs, rfl⟩
      exact iter_rel avatar env henv data n f l cons sl true (by simp [h]) he hm hx
        (hlx x (by rw [hx]; simp)) (ih' x (by rw [hx]; simp)) hdec
    · exact tail_rel avatar env henv data n f l cons sl h he hm hne hlx ih' hdec
  | @slice c d m x hop he hnode hlay hch _ _ _ _ ih =>
    intro fuel l cons sl hh hcv _
    obtain ⟨f, rfl, hf⟩ := fuel_succ hh
    have hx : x ∈ c.ch := by rw [hch]; simp
    have hcv' := hcv
    rw [cvOk_eq] at hcv'
    exact slice_rel avatar env henv data n f l cons sl hop he hnode hlay hch
      (fun sz l' cons sl => ih sz f l' cons sl (by have := height_mem hx; omega) (hcv.child hx)
        (.leaf (by simp [winMeta]) (by simp [winMeta]) (by simp [winMeta])))
      (hcv'.2.1 hop)
  | @leaf c d m hop hs hnode hty henc hinl _ _ _ _ _ _ =>
    intro fuel l cons sl hh hcv _
    obtain ⟨f, rfl, -⟩ := fuel_succ hh
    have hne := leafOp_ne hop
    have hse := struct_enc hs hne.2.1 hne.2.2.1
    have hether : ¬(c.enc = 0 ∨ c.enc = 6) := by omega
    rw [sem_ext avatar env data n hne.1 hne.2.1 hne.2.2.1 hne.2.2.2.1]
    have hcv' := hcv
    rw [cvOk_eq] at hcv'
    refine ext_rel avatar env henv data n c d m f l cons sl _ hnode.operator (Or.inr hop) henc
      ?_ (fun _ => ⟨hty.layEq.1, hty.layEq.2⟩) ?_ hnode.compValue ?_ hcv'.2.2.1
    · unfold inputAt; rw [ite_neg' hether]; exact input_tyEq data hty l
    · intro _; unfold customSize; rw [ite_neg' hether, hty.layEq.2, size_tyEq data hty l]
    · intro h16; rw [ite_neg' hether]; exact (hinl h16).symm

end
end Bridge
