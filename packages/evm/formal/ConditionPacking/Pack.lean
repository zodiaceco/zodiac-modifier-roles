import ConditionPacking.Topology

/-!
# The packer writes header ++ nodes ++ compValues

`packBuffer` (the part of `ConditionPacker.pack` after `_transform`) returns
`packSpec`: a 3-byte header, one 4-byte word per node, then each non-empty
compValue with a 2-byte length. Proven on the memory model: the zero-filled
allocation, the `or(mload, shl)` node writes, the 32-byte `mstore`s that run
past their field (and past the buffer) and the `mcopy`s.
-/

namespace ConditionPacking
open DecoderFaithfulness

/-! ## The expected buffer -/

/-- The 32-bit word `_packNodes` stores for node `i`. -/
def nodeWord (fs : List Flat) (i : Nat) : Nat :=
  let sh := shapes fs
  let c := at! fs i
  packedNode (encCode c.paramType) (opCode c.operator) (childBounds sh i).2
    (if isInlined sh i then inlinedSize sh i else 0)
    (if c.compValue.length > 0 then 1 else 0)

def nodeBytes (fs : List Flat) (i : Nat) : Bytes := natBE 4 (nodeWord fs i)

/-- The compValue of node `i` with its 2-byte length (nothing if empty). -/
def cvBlock (fs : List Flat) (i : Nat) : Bytes :=
  let cv := (at! fs i).compValue
  if cv.length > 0 then natBE 2 cv.length ++ cv else []

/-- Blocks `0 .. k-1`, concatenated. -/
def region (f : Nat → Bytes) (k : Nat) : Bytes := (List.range k).flatMap f

def header (fs : List Flat) : Nat := fs.length * 256 + (count fs).2

/-- The buffer, as the packer's layout comment describes it. -/
def packSpec (fs : List Flat) : Bytes :=
  natBE 3 (header fs) ++ region (nodeBytes fs) fs.length ++ region (cvBlock fs) fs.length

/-! ## Regions -/

theorem region_succ (f : Nat → Bytes) (k : Nat) : region f (k + 1) = region f k ++ f k := by
  simp [region, List.range_succ, List.flatMap_append]

@[simp] theorem region_zero (f : Nat → Bytes) : region f 0 = [] := rfl

theorem length_region_nodes (fs : List Flat) (k : Nat) : (region (nodeBytes fs) k).length = 4 * k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [region_succ, List.length_append, ih, nodeBytes, length_natBE]; omega

theorem length_region_mono (f : Nat → Bytes) {i k : Nat} (h : i ≤ k) :
    (region f i).length ≤ (region f k).length := by
  induction k with
  | zero => have : i = 0 := by omega
            subst this; exact Nat.le_refl _
  | succ k ih =>
    by_cases hi : i = k + 1
    · subst hi; exact Nat.le_refl _
    · rw [region_succ, List.length_append]; have := ih (by omega); omega

/-- A byte inside the first `i` blocks reads the same in `region f k`. -/
theorem region_getD_prefix (f : Nat → Bytes) {i k q : Nat} (h : i ≤ k)
    (hq : q < (region f i).length) : (region f k).getD q 0 = (region f i).getD q 0 := by
  induction k with
  | zero => have : i = 0 := by omega
            subst this; rfl
  | succ k ih =>
    by_cases hi : i = k + 1
    · subst hi; rfl
    · rw [region_succ, getD_app, if_pos (Nat.lt_of_lt_of_le hq (length_region_mono f (by omega))),
        ih (by omega)]

/-- Byte `r` of block `i`. -/
theorem region_getD_block (f : Nat → Bytes) {i k r : Nat} (h : i < k) (hr : r < (f i).length) :
    (region f k).getD ((region f i).length + r) 0 = (f i).getD r 0 := by
  rw [region_getD_prefix f (show i + 1 ≤ k by omega) (by rw [region_succ, List.length_append]; omega),
    region_succ, getD_app, if_neg (by omega), Nat.add_sub_cancel_left]

/-! ## `_count` -/

theorem take_succ_at (g : List Flat) (n : Nat) (h : n < g.length) :
    g.take (n + 1) = g.take n ++ [at! g n] := by
  rw [List.take_succ, List.getElem?_eq_getElem h]
  simp [at!, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

theorem count_fst_take (g : List Flat) (n : Nat) (h : n ≤ g.length) :
    (List.foldl countStep (0, 0) (g.take n)).1 = (region (cvBlock g) n).length := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [take_succ_at g n (by omega), List.foldl_append, region_succ, List.length_append,
      ← ih (by omega)]
    simp only [List.foldl_cons, List.foldl_nil, countStep, cvBlock]
    split <;> simp_all [length_natBE] <;> omega

theorem count_fst (g : List Flat) : (count g).1 = (region (cvBlock g) g.length).length := by
  rw [count, ← count_fst_take g g.length (Nat.le_refl _), List.take_length]

/-! ## Packing -/

/-- Expected buffer bytes after `i` nodes are written (`n` nodes in all): the
    header, the first `i` node words, zeros, the first `i` compValue blocks,
    zeros. -/
def target (g : List Flat) (i q : Nat) : Byte :=
  let n := g.length
  if q < 3 then (natBE 3 (header g)).getD q 0
  else if q < 3 + 4 * i then (region (nodeBytes g) n).getD (q - 3) 0
  else if q < 3 + 4 * n then 0
  else if q < 3 + 4 * n + (region (cvBlock g) i).length then
    (region (cvBlock g) n).getD (q - (3 + 4 * n)) 0
  else 0

structure Inv (g : List Flat) (len i : Nat) (st : PackState) : Prop where
  offset : st.offset = 3 + 4 * i
  cvOffset : st.compValueOffset = 3 + 4 * g.length + (region (cvBlock g) i).length
  mem : ∀ q < len, st.m q = target g i q

theorem packStep_inv (g : List Flat) (i : Nat) (st : PackState) (hi : i < g.length)
    (hw : nodeWord g i < 2 ^ 32) (hL : (at! g i).compValue.length < 2 ^ 16)
    (h : Inv g (3 + 4 * g.length + (region (cvBlock g) g.length).length) i st) :
    Inv g (3 + 4 * g.length + (region (cvBlock g) g.length).length) (i + 1)
      (packStep (shapes g) g st i) := by
  obtain ⟨hoff, hcv, hm⟩ := h
  have hlenC : (region (cvBlock g) (i + 1)).length ≤ (region (cvBlock g) g.length).length :=
    length_region_mono _ (by omega)
  -- the node write
  have hz : ∀ r < 4, st.m (st.offset + r) = 0 := by
    intro r hr
    rw [hm _ (by omega), target, hoff]
    simp only [show ¬ 3 + 4 * i + r < 3 by omega, show ¬ 3 + 4 * i + r < 3 + 4 * i by omega,
      show 3 + 4 * i + r < 3 + 4 * g.length by omega, ite_false, ite_true]
  have hnode := mstore_or_shl224 st.m st.offset (nodeWord g i) hw hz
  -- the node block of the target
  have hblk : ∀ r < 4, (region (nodeBytes g) g.length).getD (4 * i + r) 0 = (natBE 4 (nodeWord g i)).getD r 0 := by
    intro r hr
    have := region_getD_block (nodeBytes g) (k := g.length) (r := r) hi (by simp [nodeBytes, length_natBE, hr])
    rw [length_region_nodes] at this; rw [this]; rfl
  unfold packStep
  dsimp only
  rw [show packedNode (encCode (at! g i).paramType) (opCode (at! g i).operator)
      (childBounds (shapes g) i).2
      (if isInlined (shapes g) i then inlinedSize (shapes g) i else 0)
      (if decide ((at! g i).compValue.length > 0) = true then 1 else 0) = nodeWord g i by
    simp [nodeWord], hnode]
  have hcvb : cvBlock g i = if (at! g i).compValue.length > 0
      then natBE 2 (at! g i).compValue.length ++ (at! g i).compValue else [] := rfl
  split
  · -- with a compValue
    rename_i hpos
    simp only [decide_eq_true_eq] at hpos
    generalize hcvdef : (at! g i).compValue = cv at *
    have hb : cvBlock g i = natBE 2 cv.length ++ cv := by rw [hcvb, if_pos hpos]
    have hreg : (region (cvBlock g) (i + 1)).length = (region (cvBlock g) i).length + 2 + cv.length := by
      rw [region_succ, List.length_append, hb, List.length_append, length_natBE]; omega
    rw [show 240 = 8 * (32 - 2) from rfl, mstore_shl _ _ 2 _ (by decide) (by simpa using hL)]
    refine ⟨by simp [hoff]; omega, by simp [hcv, hreg]; omega, ?_⟩
    intro q hq
    simp only [Mem.write_apply, List.length_append, length_natBE, length_zeros]
    have hc0 := hcv
    by_cases ha : st.compValueOffset + 2 ≤ q ∧ q < st.compValueOffset + 2 + cv.length
    · -- compValue body
      rw [if_pos ha, target]
      simp only [show ¬ q < 3 by omega, show ¬ q < 3 + 4 * (i + 1) by omega,
        show ¬ q < 3 + 4 * g.length by omega, ite_false]
      rw [if_pos (by omega)]
      have := region_getD_block (cvBlock g) (k := g.length) (r := q - st.compValueOffset) hi
        (by rw [hb, List.length_append, length_natBE]; omega)
      rw [show q - (3 + 4 * g.length) = (region (cvBlock g) i).length + (q - st.compValueOffset) by omega, this, hb,
        getD_app, length_natBE, if_neg (by omega), Nat.sub_sub]
    · rw [if_neg ha]
      by_cases hb2 : st.compValueOffset ≤ q ∧ q < st.compValueOffset + (2 + 30)
      · -- length field, or the zeros after the body
        rw [if_pos hb2, getD_app, length_natBE, target]
        simp only [show ¬ q < 3 by omega, show ¬ q < 3 + 4 * (i + 1) by omega,
          show ¬ q < 3 + 4 * g.length by omega, ite_false]
        by_cases hl : q - st.compValueOffset < 2
        · rw [if_pos hl, if_pos (by omega)]
          have := region_getD_block (cvBlock g) (k := g.length) (r := q - st.compValueOffset) hi
            (by rw [hb, List.length_append, length_natBE]; omega)
          rw [show q - (3 + 4 * g.length) = (region (cvBlock g) i).length + (q - st.compValueOffset) by omega, this, hb,
            getD_app, length_natBE, if_pos hl]
        · rw [if_neg hl, getD_zeros, if_neg (by omega)]
      · rw [if_neg hb2]
        by_cases hd : st.offset ≤ q ∧ q < st.offset + 4
        · -- node word
          rw [if_pos hd, target]
          simp only [show ¬ q < 3 by omega, show q < 3 + 4 * (i + 1) by omega, ite_false, ite_true]
          rw [show q - 3 = 4 * i + (q - st.offset) by omega, hblk _ (by omega)]
        · rw [if_neg hd, hm q hq]
          unfold target
          by_cases h1 : q < 3
          · simp [h1]
          · by_cases h2 : q < 3 + 4 * i
            · simp only [h1, h2, ite_false, ite_true, show q < 3 + 4 * (i + 1) by omega]
            · by_cases h3 : q < 3 + 4 * g.length
              · simp only [h1, h2, h3, ite_false, ite_true,
                  show ¬ q < 3 + 4 * (i + 1) by omega]
              · simp only [h1, h2, h3, ite_false, show ¬ q < 3 + 4 * (i + 1) by omega, hreg]
                by_cases h4 : q < 3 + 4 * g.length + (region (cvBlock g) i).length
                · rw [if_pos h4, if_pos (by omega)]
                · rw [if_neg h4, if_neg (by omega)]
  · -- without a compValue: the block is empty
    rename_i hpos
    simp only [decide_eq_true_eq] at hpos
    have hb : cvBlock g i = [] := by rw [hcvb, if_neg hpos]
    have hreg : region (cvBlock g) (i + 1) = region (cvBlock g) i := by
      rw [region_succ, hb, List.append_nil]
    refine ⟨by simp [hoff]; omega, by simp [hcv, hreg], ?_⟩
    intro q hq
    show st.m.write st.offset (natBE 4 (nodeWord g i)) q = _
    rw [Mem.write_apply, length_natBE]
    by_cases hd : st.offset ≤ q ∧ q < st.offset + 4
    · rw [if_pos hd, target]
      simp only [show ¬ q < 3 by omega, show q < 3 + 4 * (i + 1) by omega, ite_false, ite_true]
      rw [show q - 3 = 4 * i + (q - st.offset) by omega, hblk _ (by omega)]
    · rw [if_neg hd, hm q hq]
      unfold target
      rw [hreg]
      by_cases h1 : q < 3
      · simp [h1]
      · by_cases h2 : q < 3 + 4 * i
        · simp only [h1, h2, ite_false, ite_true, show q < 3 + 4 * (i + 1) by omega]
        · simp only [h1, h2, ite_false, show ¬ q < 3 + 4 * (i + 1) by omega]

theorem packNodes_inv (g : List Flat) (st : PackState)
    (hw : ∀ i < g.length, nodeWord g i < 2 ^ 32)
    (hL : ∀ i < g.length, (at! g i).compValue.length < 2 ^ 16)
    (h0 : Inv g (3 + 4 * g.length + (region (cvBlock g) g.length).length) 0 st) :
    ∀ k ≤ g.length, Inv g (3 + 4 * g.length + (region (cvBlock g) g.length).length) k
      ((List.range k).foldl (packStep (shapes g) g) st) := by
  intro k hk
  induction k with
  | zero => exact h0
  | succ k ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact packStep_inv g k _ (by omega) (hw k (by omega)) (hL k (by omega)) (ih (by omega))

theorem length_packSpec (g : List Flat) :
    (packSpec g).length = 3 + 4 * g.length + (region (cvBlock g) g.length).length := by
  simp [packSpec, length_natBE, length_region_nodes]; omega

/-- The packer writes `packSpec`. -/
theorem packBuffer_eq (junk : Mem) (g : List Flat)
    (hw : ∀ i < g.length, nodeWord g i < 2 ^ 32)
    (hL : ∀ i < g.length, (at! g i).compValue.length < 2 ^ 16)
    (hn : g.length < 2 ^ 16) (hmp : (count g).2 < 256) :
    packBuffer junk g = packSpec g := by
  have hcs := count_fst g
  have hhdr : (g.length <<< 8) ||| (count g).2 = header g := by
    rw [Nat.shiftLeft_eq, Nat.mul_comm, ← Nat.two_pow_add_eq_or_of_lt hmp, header, Nat.mul_comm]
  have hhlt : header g < 256 ^ 3 := by unfold header; have : (256 : Nat) ^ 3 = 2 ^ 24 := rfl; omega
  unfold packBuffer
  generalize hc : count g = c at hcs hhdr hmp
  obtain ⟨cs, mp⟩ := c
  dsimp only at hcs hhdr hmp ⊢
  rw [hhdr, show 232 = 8 * (32 - 3) from rfl, mstore_shl _ _ 3 _ (by decide) hhlt]
  subst hcs
  generalize hlen : 3 + g.length * 4 + (region (cvBlock g) g.length).length = len
  have hlen' : len = 3 + 4 * g.length + (region (cvBlock g) g.length).length := by omega
  have h0 : Inv g len 0
      ⟨Mem.write (fun q => if q < len then 0 else junk q) 0 (natBE 3 (header g) ++ zeros (32 - 3)), 3,
        3 + g.length * 4⟩ := by
    refine ⟨rfl, by simp; omega, ?_⟩
    intro q hq
    dsimp only
    rw [Mem.write_apply, target]
    simp only [List.length_append, length_natBE, length_zeros, Nat.mul_zero, Nat.add_zero,
      region_zero, List.length_nil]
    by_cases h3 : q < 3
    · rw [if_pos (by omega), if_pos h3, getD_app, length_natBE, if_pos (by omega), Nat.sub_zero]
    · rw [if_neg h3, if_neg h3]
      by_cases h32 : q < 3 + 29
      · rw [if_pos (by omega), getD_app, length_natBE, if_neg (by omega), getD_zeros]
        split <;> simp_all <;> omega
      · rw [if_neg (by omega), if_pos hq]; split <;> simp_all <;> omega
  subst hlen'
  have hinv := packNodes_inv g _ hw hL h0 g.length (Nat.le_refl _)
  unfold packNodes
  rw [← length_packSpec g] at hinv ⊢
  apply ext_getD (by simp)
  intro q hq
  simp only [Mem.length_read] at hq
  rw [Mem.getD_read _ _ _ _ hq, Nat.zero_add, hinv.mem q hq, target]
  rw [length_packSpec] at hq
  unfold packSpec
  rw [getD_app, getD_app, List.length_append, length_natBE, length_region_nodes]
  by_cases h3 : q < 3
  · rw [if_pos h3, if_pos (by omega), if_pos h3]
  · rw [if_neg h3, if_neg h3]
    by_cases h4 : q < 3 + 4 * g.length
    · rw [if_pos h4, if_pos h4]
    · rw [if_neg h4, if_neg h4, if_neg h4, if_pos hq]

end ConditionPacking
