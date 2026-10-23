import ConditionPacking.Pack

/-!
# The unpacker reads `packSpec` back

Running `ConditionUnpacker.unpack` on the buffer `packSpec (transform fs)`
(with arbitrary memory after it) yields `annotate` of the input tree.
-/

namespace ConditionPacking
open DecoderFaithfulness DecoderFaithfulness.Roles

/-! ## `_transform` -/

@[simp] theorem transform_length (fs : List Flat) : (transform fs).length = fs.length := by
  simp [transform]

theorem at!_lt (fs : List Flat) (i : Nat) (h : i < fs.length) : at! fs i = fs[i] := by
  simp [at!, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

theorem at_transform (fs : List Flat) (i : Nat) (hi : i < fs.length) :
    at! (transform fs) i = { at! fs i with compValue := transformCv (shapes fs) i (at! fs i) } := by
  rw [at!_lt _ _ (by simpa using hi)]
  simp [transform]

theorem shapes_transform (fs : List Flat) : shapes (transform fs) = shapes fs := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [shapes_length, transform_length] at h1 h2
  simp [shapes, transform, at!_lt fs i h2]

theorem length_transformCv_le (sh : List Shape) (i : Nat) (f : Flat) :
    (transformCv sh i f).length ≤ max 2 f.compValue.length := by
  unfold transformCv
  split <;> split <;> simp_all <;> omega

/-! ## Node words -/

theorem shl_or (a i b : Nat) (hb : b < 2 ^ i) : a <<< i ||| b = a * 2 ^ i + b := by
  rw [← Nat.shiftLeft_add_eq_or_of_lt hb, Nat.shiftLeft_eq]

theorem packedNode_eq (e o k s h : Nat) (ho : o < 32) (hk : k < 1024) (hs : s < 8192)
    (hh : h < 2) :
    packedNode e o k s h = e * 2 ^ 29 + (o * 2 ^ 24 + (k * 2 ^ 14 + (s * 2 ^ 1 + h))) := by
  unfold packedNode
  simp only [Nat.or_assoc]
  rw [shl_or s 1 h (by omega), shl_or k 14 _ (by omega), shl_or o 24 _ (by omega),
    shl_or e 29 _ (by omega)]

/-- The fields `_unpackConditions` extracts from a node word. -/
theorem packedNode_fields (e o k s h : Nat) (he : e < 8) (ho : o < 32) (hk : k < 1024)
    (hs : s < 8192) (hh : h < 2) :
    let p := packedNode e o k s h
    p < 2 ^ 32 ∧ p >>> 29 = e ∧ (p >>> 24) &&& 0x1F = o ∧ (p >>> 14) &&& 0x3FF = k ∧
      (p >>> 1) &&& 0x1FFF = s ∧ p &&& 1 = h := by
  intro p
  have hp : p = e * 2 ^ 29 + (o * 2 ^ 24 + (k * 2 ^ 14 + (s * 2 ^ 1 + h))) :=
    packedNode_eq e o k s h ho hk hs hh
  rw [show (0x1F : Nat) = 2 ^ 5 - 1 from rfl, show (0x3FF : Nat) = 2 ^ 10 - 1 from rfl,
    show (0x1FFF : Nat) = 2 ^ 13 - 1 from rfl, show (1 : Nat) = 2 ^ 0 * 2 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod, Nat.and_two_pow_sub_one_eq_mod,
    Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow,
    Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow]
  have : (2 : Nat) ^ 0 * 2 - 1 = 2 ^ 1 - 1 := rfl
  rw [this, Nat.and_two_pow_sub_one_eq_mod]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

theorem encCode_lt (e : Encoding) : encCode e < 7 := by cases e <;> decide
theorem opCode_lt (o : Operator) : opCode o < 31 := by cases o <;> decide

/-- Bounds that make every node word fit (from `Packable`). -/
theorem nodeWord_fields (fs : List Flat) (i : Nat)
    (hk : (childBounds (shapes fs) i).2 ≤ 1023)
    (hs : isInlined (shapes fs) i = true → inlinedSize (shapes fs) i ≤ 8191) :
    nodeWord (transform fs) i < 2 ^ 32 ∧
      nodeWord (transform fs) i >>> 29 = encCode (at! (transform fs) i).paramType ∧
      (nodeWord (transform fs) i >>> 24) &&& 0x1F = opCode (at! (transform fs) i).operator ∧
      (nodeWord (transform fs) i >>> 14) &&& 0x3FF = (childBounds (shapes fs) i).2 ∧
      (nodeWord (transform fs) i >>> 1) &&& 0x1FFF =
        (if isInlined (shapes fs) i then inlinedSize (shapes fs) i else 0) ∧
      nodeWord (transform fs) i &&& 1 =
        (if (at! (transform fs) i).compValue.length > 0 then 1 else 0) := by
  have := packedNode_fields (encCode (at! (transform fs) i).paramType)
    (opCode (at! (transform fs) i).operator)
    (childBounds (shapes fs) i).2 (if isInlined (shapes fs) i then inlinedSize (shapes fs) i else 0)
    (if (at! (transform fs) i).compValue.length > 0 then 1 else 0)
    (by have := encCode_lt (at! (transform fs) i).paramType; omega)
    (by have := opCode_lt (at! (transform fs) i).operator; omega) (by omega)
    (by split <;> first | decide | exact Nat.lt_of_le_of_lt (hs ‹_›) (by decide))
    (by split <;> decide)
  unfold nodeWord
  rw [shapes_transform]
  exact this

/-! ## Reading the buffer -/

theorem read_bufMem (B : Bytes) (junk : Mem) (p : Nat) (l : Bytes) (hp : p + l.length ≤ B.length)
    (h : ∀ i < l.length, B.getD (p + i) 0 = l.getD i 0) : (bufMem B junk).read p l.length = l := by
  apply Mem.read_eq
  intro i hi
  simp only [bufMem]
  rw [if_pos (by omega), h i hi]

/-- Node word `c`. -/
theorem read_node (g : List Flat) (junk : Mem) (c : Nat) (hc : c < g.length) :
    (bufMem (packSpec g) junk).read (3 + 4 * c) 4 = nodeBytes g c := by
  have hl : (nodeBytes g c).length = 4 := by simp [nodeBytes, length_natBE]
  have := read_bufMem (packSpec g) junk (3 + 4 * c) (nodeBytes g c)
    (by rw [length_packSpec, hl]; omega) (by
      intro i hi
      rw [hl] at hi
      unfold packSpec
      rw [getD_app, getD_app, List.length_append, length_natBE, length_region_nodes,
        if_pos (by omega), if_neg (by omega),
        show 3 + 4 * c + i - 3 = (region (nodeBytes g) c).length + i by rw [length_region_nodes]; omega,
        region_getD_block _ hc (by omega)])
  rwa [hl] at this

theorem read_header (g : List Flat) (junk : Mem) :
    (bufMem (packSpec g) junk).read 0 3 = natBE 3 (header g) := by
  have hl : (natBE 3 (header g)).length = 3 := length_natBE 3 _
  rw [← hl]
  apply read_bufMem
  · rw [length_packSpec, hl]; omega
  · intro i hi
    rw [hl] at hi
    unfold packSpec
    rw [getD_app, getD_app, List.length_append, length_natBE, if_pos (by omega),
      if_pos (by omega), Nat.zero_add]

/-- Where compValue block `c` starts. -/
def cvOff (g : List Flat) (c : Nat) : Nat := 3 + 4 * g.length + (region (cvBlock g) c).length

/-- Bytes `j .. j + k` of compValue block `c`. -/
theorem read_cv (g : List Flat) (junk : Mem) (c j k : Nat) (hc : c < g.length)
    (hjk : j + k ≤ (cvBlock g c).length) :
    (bufMem (packSpec g) junk).read (cvOff g c + j) k = ((cvBlock g c).drop j).take k := by
  have hl : (((cvBlock g c).drop j).take k).length = k := by simp; omega
  conv => lhs; rw [← hl]
  have hreg : (region (cvBlock g) (c + 1)).length ≤ (region (cvBlock g) g.length).length :=
    length_region_mono _ (by omega)
  have hsucc : (region (cvBlock g) (c + 1)).length =
      (region (cvBlock g) c).length + (cvBlock g c).length := by
    rw [region_succ, List.length_append]
  apply read_bufMem
  · rw [length_packSpec, hl, cvOff]; omega
  · intro i hi
    rw [hl] at hi
    unfold packSpec cvOff
    rw [getD_app, getD_app, List.length_append, length_natBE, length_region_nodes,
      if_neg (by omega),
      show 3 + 4 * g.length + (region (cvBlock g) c).length + j + i - (3 + 4 * g.length) =
        (region (cvBlock g) c).length + (j + i) by omega,
      region_getD_block _ hc (by omega)]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_take, List.getElem?_drop]
    rw [if_pos hi]

/-! ## One iteration of `_unpackConditions` -/

/-- Closes the leftover arithmetic and "no children" goals of a step. -/
local macro "step_arith" : tactic =>
  `(tactic| first
    | omega
    | exact List.eq_nil_of_length_eq_zero (by omega)
    | exact ⟨by omega, List.eq_nil_of_length_eq_zero (by omega)⟩
    | exact ⟨by omega, by omega, List.eq_nil_of_length_eq_zero (by omega)⟩)

/-- The struct `_unpackConditions` fills for node `c`. -/
def expRec (avatar : Bytes) (fs : List Flat) (c : Nat) : URec :=
  let f := at! fs c
  let cv := transformCv (shapes fs) c f
  let k := (kids fs c).length
  let sz := if isInlined (shapes fs) c then inlinedSize (shapes fs) c else 0
  { encoding := if encCode f.paramType = 6 then 0 else encCode f.paramType
    operator := if opCode f.operator = 15 then 16 else opCode f.operator
    children := if k > 0 then List.range' (1 + cnt fs c) k else []
    inlined := decide (sz > 0)
    size := sz
    leadingBytes := if f.paramType = .AbiEncoded then wordVal (cv.take 2) else 0
    compValue :=
      if f.operator = .EqualToAvatar then avatar
      else if f.paramType = .AbiEncoded then cv.drop 2 else cv }

theorem encCode_eq_5 (e : Encoding) : encCode e = 5 ↔ e = .AbiEncoded := by cases e <;> decide
theorem encCode_eq_6 (e : Encoding) : encCode e = 6 ↔ e = .EtherValue := by cases e <;> decide
theorem opCode_eq_15 (o : Operator) : opCode o = 15 ↔ o = .EqualToAvatar := by cases o <;> decide

theorem cvOff_succ (g : List Flat) (c : Nat) : cvOff g (c + 1) = cvOff g c + (cvBlock g c).length := by
  simp [cvOff, region_succ]; omega

theorem unpackStep_eq (avatar : Bytes) (junk : Mem) (fs : List Flat) (h : Packable fs) (c : Nat)
    (hc : c < fs.length) (recs : List URec) :
    unpackStep avatar (bufMem (packSpec (transform fs)) junk)
        ⟨3 + 4 * c, cvOff (transform fs) c, 1 + cnt fs c, recs⟩ c =
      ⟨3 + 4 * (c + 1), cvOff (transform fs) (c + 1), 1 + cnt fs (c + 1),
        recs ++ [expRec avatar fs c]⟩ := by
  have hcg : c < (transform fs).length := by simpa using hc
  obtain ⟨hlt, he, ho, hk, hs, hh⟩ :=
    nodeWord_fields fs c (h.child_count c hc) (h.inlined_size c hc)
  have hpacked : shr 224 (mload (bufMem (packSpec (transform fs)) junk) (3 + 4 * c)) =
      nodeWord (transform fs) c := by
    rw [shr224_mload, read_node _ junk c hcg, nodeBytes,
      wordVal_natBE _ _ (by have : (256 : Nat) ^ 4 = 2 ^ 32 := rfl; omega)]
  have hat := at_transform fs c hc
  rw [hat] at he ho hh
  simp only at he ho hh
  rw [childBounds_eq fs h.bfs h.nonempty c] at hk
  simp only at hk
  have hcnt := cnt_succ fs h.bfs h.nonempty c
  have hblk : cvBlock (transform fs) c =
      if (transformCv (shapes fs) c (at! fs c)).length > 0
      then natBE 2 (transformCv (shapes fs) c (at! fs c)).length ++ transformCv (shapes fs) c (at! fs c)
      else [] := by
    unfold cvBlock; rw [hat]
  have hrd := read_cv (transform fs) junk c
  have hsucc := cvOff_succ (transform fs) c
  have hLlt : (transformCv (shapes fs) c (at! fs c)).length < 2 ^ 16 := by
    have := length_transformCv_le (shapes fs) c (at! fs c)
    have := h.comp_value_length c hc
    omega
  have hAb : (at! fs c).paramType = .AbiEncoded →
      2 ≤ (transformCv (shapes fs) c (at! fs c)).length := by
    intro hA
    obtain ⟨h1, h2⟩ := h.abi_encoded c hc hA
    unfold transformCv
    simp only [hA, h2, true_and, false_and, ite_false]
    split
    · simp
    · omega
  unfold unpackStep expRec
  dsimp only
  generalize transformCv (shapes fs) c (at! fs c) = cv at *
  generalize hf : at! fs c = f at *
  simp only [hpacked, he, ho, hk, hs, hh, hf, shr240_mload]
  have hE : (if encCode f.paramType = 6 then 0 else encCode f.paramType) = 5 ↔
      f.paramType = .AbiEncoded := by
    generalize f.paramType = e; cases e <;> decide
  by_cases hL : cv.length > 0
  · rw [hblk, if_pos hL] at hrd hsucc
    simp only [List.length_append, length_natBE] at hrd hsucc
    have hlen : (bufMem (packSpec (transform fs)) junk).read (cvOff (transform fs) c) 2 =
        natBE 2 cv.length := by
      rw [show cvOff (transform fs) c = cvOff (transform fs) c + 0 from rfl, hrd 0 2 hcg (by omega),
        List.drop_zero, List.take_left' (length_natBE 2 _)]
    have hLv : wordVal (natBE 2 cv.length) = cv.length :=
      wordVal_natBE _ _ (by have : (256 : Nat) ^ 2 = 2 ^ 16 := rfl; omega)
    simp only [hL, ite_true, show (1 : Nat) ≠ 0 by decide, ne_eq, not_false_eq_true, hlen, hLv]
    by_cases hA : f.paramType = .AbiEncoded
    · have h2 := hAb hA
      have hlb : (bufMem (packSpec (transform fs)) junk).read (cvOff (transform fs) c + 2) 2 =
          cv.take 2 := by
        rw [hrd 2 2 hcg (by omega), List.drop_left' (length_natBE 2 _)]
      have hrest : (bufMem (packSpec (transform fs)) junk).read (cvOff (transform fs) c + 2 + 2)
          (cv.length - 2) = cv.drop 2 := by
        have := hrd 4 (cv.length - 2) hcg (by omega)
        rw [show cvOff (transform fs) c + 2 + 2 = cvOff (transform fs) c + 4 by omega, this]
        rw [show (4 : Nat) = 2 + 2 from rfl, ← List.drop_drop, List.drop_left' (length_natBE 2 _),
          List.take_of_length_le (by simp)]
      have hsub : (cv.length + 2 ^ 256 - 2) % 2 ^ 256 = cv.length - 2 := by omega
      simp (config := { decide := true }) only [hA, encCode, hlb, hsub, hrest, ite_true, ite_false]
      by_cases h3 : cv.length - 2 > 0
      · simp only [h3, ite_true, hrest]
        rw [hsucc, hcnt]
        by_cases hk0 : (kids fs c).length > 0 <;> by_cases ho15 : f.operator = .EqualToAvatar <;>
          simp [hk0, ho15, hA, (opCode_eq_15 _), List.length_eq_zero_iff] <;> step_arith
      · have hd : cv.drop 2 = [] := List.drop_eq_nil_of_le (by omega)
        simp only [h3, ite_false, hd]
        rw [hsucc, hcnt]
        by_cases hk0 : (kids fs c).length > 0 <;> by_cases ho15 : f.operator = .EqualToAvatar <;>
          simp [hk0, ho15, hA, hd, (opCode_eq_15 _), List.length_eq_zero_iff] <;> step_arith
    · have hn5 : ¬ (if encCode f.paramType = 6 then 0 else encCode f.paramType) = 5 :=
        fun h' => hA ((hE).1 h')
      have hcvr : (bufMem (packSpec (transform fs)) junk).read (cvOff (transform fs) c + 2)
          cv.length = cv := by
        rw [hrd 2 cv.length hcg (by omega), List.drop_left' (length_natBE 2 _),
          List.take_of_length_le (by simp)]
      simp only [hn5, ite_false, hL, ite_true, hcvr]
      rw [hsucc, hcnt]
      by_cases hk0 : (kids fs c).length > 0 <;> by_cases ho15 : f.operator = .EqualToAvatar <;>
        simp [hk0, ho15, hA, (opCode_eq_15 _), List.length_eq_zero_iff] <;> step_arith
  · have hcv0 : cv = [] := List.eq_nil_of_length_eq_zero (by omega)
    rw [hblk, if_neg hL] at hsucc
    simp only [hL, ite_false, ne_eq, not_true_eq_false]
    rw [hsucc, hcnt, hcv0]
    by_cases hk0 : (kids fs c).length > 0 <;> by_cases ho15 : f.operator = .EqualToAvatar <;>
      simp [hk0, ho15, (opCode_eq_15 _), List.length_eq_zero_iff] <;> step_arith

end ConditionPacking
