import ConditionPacking.Unpack

/-!
# Pack/unpack round trip

`pack_roundtrip`: for every flat condition array that satisfies the checks
Integrity runs (`Packable`), unpacking the packed buffer gives back the input
tree, with the metadata the decoder proof assumes (`annotate`), and
`maxPluckValue` is one more than the largest Pluck index.
-/

namespace ConditionPacking
open DecoderFaithfulness DecoderFaithfulness.Roles

/-! ## The unpacker loop -/

theorem unpack_loop (avatar : Bytes) (junk : Mem) (fs : List Flat) (h : Packable fs) :
    ∀ k ≤ fs.length,
      (List.range k).foldl (unpackStep avatar (bufMem (packSpec (transform fs)) junk))
          ⟨3, cvOff (transform fs) 0, 1, []⟩ =
        ⟨3 + 4 * k, cvOff (transform fs) k, 1 + cnt fs k, (List.range k).map (expRec avatar fs)⟩ := by
  intro k hk
  induction k with
  | zero => simp [cnt_zero]
  | succ k ih =>
    rw [List.range_succ, List.foldl_append, ih (by omega), List.foldl_cons, List.foldl_nil,
      unpackStep_eq avatar junk fs h k (by omega), List.map_append, List.map_cons, List.map_nil]

/-! ## Rebuilding the tree -/

theorem encOf_map (e : Encoding) :
    encOf? (if encCode e = 6 then 0 else encCode e) = some (if e = .EtherValue then .None else e) := by
  cases e <;> rfl

theorem opOf_map (o : Operator) :
    opOf? (if opCode o = 15 then 16 else opCode o) = some (if o = .EqualToAvatar then .EqualTo else o) := by
  cases o <;> rfl

theorem mapM_some {α β : Type} (l : List α) (g : α → Option β) (r : α → β)
    (h : ∀ x ∈ l, g x = some (r x)) : l.mapM g = some (l.map r) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.mapM_cons, h a (by simp), ih (fun x hx => h x (by simp [hx]))]
    rfl

theorem annotate_eq (c : Condition) :
    annotate c =
      { encoding := if c.encoding = .EtherValue then .None else c.encoding
        operator := if c.operator = .EqualToAvatar then .EqualTo else c.operator
        children := c.children.map annotate
        inlined := decide ((if Roles.isInlined c then Roles.inlinedSize c else 0) > 0)
        size := if Roles.isInlined c then Roles.inlinedSize c else 0
        leadingBytes := if c.encoding = .AbiEncoded then c.leadingBytes else 0
        compValue := c.compValue } := by
  cases c
  rw [annotate]
  simp only [attach_map' _ annotate]

theorem children_expRec (avatar : Bytes) (fs : List Flat) (h : Packable fs) (i : Nat) :
    (expRec avatar fs i).children = kids fs i := by
  simp only [expRec]
  split
  · exact (kids_eq_range' fs h.bfs h.nonempty i).symm
  · rename_i hk; exact (List.eq_nil_of_length_eq_zero (by omega)).symm

theorem toTree_eq (avatar : Bytes) (fs : List Flat) (h : Packable fs) (i : Nat) (hi : i < fs.length)
    (fuel : Nat) (hf : fs.length - i ≤ fuel) :
    toTree ((List.range fs.length).map (expRec avatar fs)) fuel i =
      some (annotate (rawTree avatar fs i)) := by
  obtain ⟨f', rfl⟩ : ∃ f', fuel = f' + 1 := ⟨fuel - 1, by omega⟩
  have hkids : ∀ j ∈ kids fs i,
      toTree ((List.range fs.length).map (expRec avatar fs)) f' j = some (annotate (rawTree avatar fs j)) :=
    fun j hj => by
      have := mem_kids hj
      exact toTree_eq avatar fs h j this.2 f' (by omega)
  have hs1 := isInlined_rawTree avatar fs h.bfs h.nonempty i
  have hs2 := inlinedSize_rawTree avatar fs h.bfs h.nonempty i
  have he : (expRec avatar fs i).encoding =
      if encCode (at! fs i).paramType = 6 then 0 else encCode (at! fs i).paramType := rfl
  have ho : (expRec avatar fs i).operator =
      if opCode (at! fs i).operator = 15 then 16 else opCode (at! fs i).operator := rfl
  rw [toTree, List.getElem?_map, List.getElem?_range hi]
  simp only [Option.map_some, Option.bind_eq_bind, Option.bind_some, Option.pure_def, he, ho,
    encOf_map, opOf_map, children_expRec avatar fs h i, mapM_some _ _ _ hkids]
  rw [annotate_eq, hs1, hs2, rawTree_eq]
  simp only [expRec, List.map_map, Function.comp_def]
  congr 2
  split <;> simp_all
termination_by fs.length - i
decreasing_by all_goals omega

/-! ## `maxPluckValue` -/

def maxStep (acc : Nat) (f : Flat) : Nat :=
  if f.operator = .Pluck then max acc ((f.compValue.headD 0).val + 1) else acc

theorem countStep_snd (acc : Nat × Nat) (f : Flat) :
    (countStep acc f).2 =
      if f.operator = .Pluck then
        (if (f.compValue.headD 0).val + 1 > acc.2 then (f.compValue.headD 0).val + 1 else acc.2)
      else acc.2 := rfl

theorem count_snd_take (fs : List Flat) (h : Packable fs) (k : Nat) (hk : k ≤ fs.length) :
    (List.foldl countStep (0, 0) ((transform fs).take k)).2 = List.foldl maxStep 0 (fs.take k) ∧
      List.foldl maxStep 0 (fs.take k) ≤ 255 := by
  induction k with
  | zero => simp
  | succ k ih =>
    obtain ⟨ih1, ih2⟩ := ih (by omega)
    rw [take_succ_at (transform fs) k (by simp; omega), take_succ_at fs k (by omega),
      List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_nil, List.foldl_cons,
      List.foldl_nil, countStep_snd, ih1, at_transform fs k (by omega)]
    simp only [maxStep]
    by_cases hp : (at! fs k).operator = .Pluck
    · obtain ⟨hne, hle⟩ := h.pluck k (by omega) hp
      have hcv : transformCv (shapes fs) k (at! fs k) = (at! fs k).compValue := by
        unfold transformCv
        have : (at! fs k).compValue.length ≠ 0 := fun h0 => hne (List.eq_nil_of_length_eq_zero h0)
        simp [hp, this]
      simp only [hp, ite_true, hcv]
      constructor
      · rw [Nat.max_def]; split <;> split <;> omega
      · rw [Nat.max_def]; split <;> omega
    · simp only [hp, ite_false]
      exact ⟨trivial, ih2⟩

theorem count_snd (fs : List Flat) (h : Packable fs) :
    (count (transform fs)).2 = maxPluck fs ∧ maxPluck fs ≤ 255 := by
  have := count_snd_take fs h fs.length (Nat.le_refl _)
  rw [List.take_of_length_le (by simp), List.take_length] at this
  exact this

/-! ## The round trip -/

/-- **Pack/unpack round trip.** For a flat condition array `fs` that passes the
    checks Integrity runs (`Packable`), `ConditionPacker.pack` followed by
    `ConditionUnpacker.unpack` yields the input tree (rooted at node 0), with
    the `inlined`/`size`/`leadingBytes` metadata of `annotate`, and
    `maxPluckValue = max(pluckIndex) + 1`. `junk` and `junk'` are the
    surrounding memory at pack and unpack time; `avatar` is
    `abi.encode(avatar)`. -/
theorem pack_roundtrip (avatar : Bytes) (junk junk' : Mem) (fs : List Flat) (h : Packable fs) :
    unpack avatar (bufMem (pack junk fs) junk') = some (annotate (rawTree avatar fs 0), maxPluck fs) := by
  obtain ⟨hmp, hmp255⟩ := count_snd fs h
  have hbuf : pack junk fs = packSpec (transform fs) := by
    unfold pack
    apply packBuffer_eq
    · intro i hi
      simp only [transform_length] at hi
      exact (nodeWord_fields fs i (h.child_count i hi) (h.inlined_size i hi)).1
    · intro i hi
      simp only [transform_length] at hi
      rw [at_transform fs i hi]
      have := length_transformCv_le (shapes fs) i (at! fs i)
      have := h.comp_value_length i hi
      simp only; omega
    · have := h.node_count; simp only [transform_length]; omega
    · omega
  rw [hbuf]
  unfold unpack
  have hh : header (transform fs) = fs.length * 256 + maxPluck fs := by
    unfold header; rw [hmp, transform_length]
  have hlt : header (transform fs) < 256 ^ 3 := by
    rw [hh]; have := h.node_count; have : (256 : Nat) ^ 3 = 2 ^ 24 := rfl; omega
  have hhv : wordVal ((bufMem (packSpec (transform fs)) junk').read 0 3) =
      fs.length * 256 + maxPluck fs := by
    rw [read_header, wordVal_natBE _ _ hlt, hh]
  dsimp only
  rw [hhv]
  have hn : (fs.length * 256 + maxPluck fs) >>> 8 = fs.length := by
    rw [Nat.shiftRight_eq_div_pow]; omega
  have hm : (fs.length * 256 + maxPluck fs) &&& 0xFF = maxPluck fs := by
    rw [show (0xFF : Nat) = 2 ^ 8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]; omega
  rw [hn, hm]
  have hinit : (⟨3, 3 + fs.length * 4, 1, []⟩ : UState) = ⟨3, cvOff (transform fs) 0, 1, []⟩ := by
    simp [cvOff]; omega
  rw [hinit, unpack_loop avatar junk' fs h fs.length (Nat.le_refl _)]
  simp only
  rw [toTree_eq avatar fs h 0 h.nonempty fs.length (by omega)]
  rfl

end ConditionPacking
