import DecoderFaithfulness.Roles

/-!
# Condition packing: transcription

Transcribed from `packages/evm/contracts` (branch `formal/abi-layer-a`):

* `core/serialize/Topology.sol`        → `childBounds`, `isInlined`, `inlinedSize`
* `core/serialize/ConditionPacker.sol` → `transform`, `count`, `packNodes`, `pack`
* `core/serialize/ConditionUnpacker.sol` → `unpackStep`, `unpack`

Memory is modeled byte by byte (`Mem`), and the assembly blocks are
transcribed with the EVM's word semantics (`mload`, `mstore`, `shl`, `shr`,
`or`). Positions are relative to the buffer's data area (`add(buffer, 0x20)`
is position 0). Deviations from the Solidity, all outside the inputs the
theorems cover:

* Arithmetic is on `Nat`. The values are bounded by the theorem's hypotheses
  (which Integrity enforces), so no Solidity expression overflows.
* `Pluck` with an empty compValue panics in `_count` (`compValue[0]`), and
  `EqualTo` with a compValue shorter than 32 bytes underflows in `_transform`.
  Both are excluded by the hypotheses; the model reads a default instead.
* Placeholder operators (`_Placeholder03`, ...) are valid Solidity enum values
  but have no `Operator` constructor here. An input cannot contain them (the
  type has none), and the unpacker model maps such a code to `none`.
* The unpacker builds a graph of `Condition` structs whose `children` are
  pointers into one `Condition[]` array. `toTree` reads that graph as a tree
  by following child indices; the pointers themselves are not modeled.
* The packer's `mstore`s may write past the end of the buffer. That memory
  is free (the buffer is the last allocation), so it is not tracked: the
  theorem quantifies over arbitrary memory outside the buffer.
-/

namespace ConditionPacking
open DecoderFaithfulness DecoderFaithfulness.Roles

/-! ## Input and enum codes -/

/-- `struct ConditionFlat` (`types/Condition.sol`). -/
structure Flat where
  parent : Nat
  paramType : Encoding
  operator : Operator
  compValue : Bytes
  deriving Inhabited

/-- `conditions[i]` (all accesses below are in bounds under the hypotheses). -/
def at! (fs : List Flat) (i : Nat) : Flat := fs.getD i default

/-- `uint256(encoding)`. -/
def encCode : Encoding → Nat
  | .None => 0 | .Static => 1 | .Dynamic => 2 | .Tuple => 3 | .Array => 4
  | .AbiEncoded => 5 | .EtherValue => 6

/-- `Encoding(n)`: Solidity panics on values above 6. -/
def encOf? : Nat → Option Encoding
  | 0 => some .None | 1 => some .Static | 2 => some .Dynamic | 3 => some .Tuple
  | 4 => some .Array | 5 => some .AbiEncoded | 6 => some .EtherValue | _ => none

/-- `uint256(operator)`, values as in `types/Operator.sol`. -/
def opCode : Operator → Nat
  | .Pass => 0 | .And => 1 | .Or => 2 | .Empty => 4 | .Matches => 5
  | .ArraySome => 6 | .ArrayEvery => 7 | .ArrayTailMatches => 8
  | .ZipSome => 10 | .ZipEvery => 11 | .Slice => 13 | .Pluck => 14
  | .EqualToAvatar => 15 | .EqualTo => 16 | .GreaterThan => 17 | .LessThan => 18
  | .SignedIntGreaterThan => 19 | .SignedIntLessThan => 20 | .Bitmask => 21
  | .Custom => 22 | .WithinRatio => 23 | .WithinAllowance => 28
  | .CallWithinAllowance => 30

/-- `Operator(n)`; placeholders map to `none` (see the header). -/
def opOf? : Nat → Option Operator
  | 0 => some .Pass | 1 => some .And | 2 => some .Or | 4 => some .Empty
  | 5 => some .Matches | 6 => some .ArraySome | 7 => some .ArrayEvery
  | 8 => some .ArrayTailMatches | 10 => some .ZipSome | 11 => some .ZipEvery
  | 13 => some .Slice | 14 => some .Pluck | 15 => some .EqualToAvatar
  | 16 => some .EqualTo | 17 => some .GreaterThan | 18 => some .LessThan
  | 19 => some .SignedIntGreaterThan | 20 => some .SignedIntLessThan
  | 21 => some .Bitmask | 22 => some .Custom | 23 => some .WithinRatio
  | 28 => some .WithinAllowance | 30 => some .CallWithinAllowance | _ => none

/-! ## Topology.sol

`Topology` reads only `parent` and `paramType`, so it is defined on those
(`Shape`). `_transform` rewrites compValues while it calls `isInlined`; that
cannot change the result. -/

structure Shape where
  parent : Nat
  paramType : Encoding
  deriving Inhabited

def shapes (fs : List Flat) : List Shape := fs.map fun f => ⟨f.parent, f.paramType⟩

/-- The loop of `childBounds`, from `j` on, with the running `childStart`
    and `childCount`. -/
def childBoundsFrom (sh : List Shape) (index : Nat) (j start count : Nat) : Nat × Nat :=
  if h : j < sh.length then
    let parent := sh[j].parent
    if parent = index then
      childBoundsFrom sh index (j + 1) (if count = 0 then j else start) (count + 1)
    else if parent > index then (start, count)
    else childBoundsFrom sh index (j + 1) start count
  else (start, count)
termination_by sh.length - j

/-- `Topology.childBounds`: `(childStart, childCount)`. -/
def childBounds (sh : List Shape) (index : Nat) : Nat × Nat :=
  childBoundsFrom sh index (index + 1) 0 0

theorem childBoundsFrom_fst_of_pos (sh : List Shape) (index j start count : Nat)
    (hc : 0 < count) : (childBoundsFrom sh index j start count).1 = start := by
  rw [childBoundsFrom]
  split
  · dsimp only
    split
    · rw [childBoundsFrom_fst_of_pos sh index (j + 1) _ _ (by omega)]
      simp; omega
    · split
      · rfl
      · exact childBoundsFrom_fst_of_pos sh index (j + 1) _ _ hc
  · rfl
termination_by sh.length - j

theorem childBoundsFrom_start (sh : List Shape) (index j start count : Nat) :
    0 < (childBoundsFrom sh index j start count).2 → count = 0 →
      j ≤ (childBoundsFrom sh index j start count).1 ∧
      (childBoundsFrom sh index j start count).1 < sh.length := by
  intro h0 hc
  subst hc
  rw [childBoundsFrom] at h0 ⊢
  split at h0
  · rename_i hj
    simp only [dif_pos hj]
    dsimp only at h0 ⊢
    split at h0
    · rename_i hp
      simp only [hp, if_true]
      rw [childBoundsFrom_fst_of_pos sh index (j + 1) _ _ (by omega)]
      simp; omega
    · rename_i hp
      split at h0
      · simp at h0
      · rename_i hg
        simp only [hp, hg, if_false]
        have := childBoundsFrom_start sh index (j + 1) start 0 h0 rfl
        omega
  · simp at h0
termination_by sh.length - j

theorem childBounds_start {sh : List Shape} {index : Nat}
    (h : 0 < (childBounds sh index).2) :
    index < (childBounds sh index).1 ∧ (childBounds sh index).1 < sh.length := by
  have := childBoundsFrom_start sh index (index + 1) 0 0 h rfl
  unfold childBounds; omega

/-- `Topology.isInlined`. -/
def isInlined (sh : List Shape) (index : Nat) : Bool :=
  let encoding := (sh.getD index default).paramType
  if encoding = .Dynamic ∨ encoding = .Array ∨ encoding = .AbiEncoded then false
  else
    (List.range (childBounds sh index).2).attach.all fun ⟨i, _⟩ =>
      isInlined sh ((childBounds sh index).1 + i)
termination_by sh.length - index
decreasing_by
  rename_i hi
  have := childBounds_start (sh := sh) (index := index) (by simp at hi; omega)
  omega

/-- The children loop of `inlinedSize`: `None` returns the first non-zero
    child size, other encodings sum. -/
def sizeLoop (isNone : Bool) : List Nat → Nat
  | [] => 0
  | childSize :: rest => if isNone ∧ childSize > 0 then childSize else childSize + sizeLoop isNone rest

/-- `Topology.inlinedSize` (only called on inlined nodes; its `assert` is
    omitted). -/
def inlinedSize (sh : List Shape) (index : Nat) : Nat :=
  let encoding := (sh.getD index default).paramType
  if encoding = .Static then 32
  else
    sizeLoop (encoding = .None) <|
      (List.range (childBounds sh index).2).attach.map fun ⟨i, _⟩ =>
        inlinedSize sh ((childBounds sh index).1 + i)
termination_by sh.length - index
decreasing_by
  rename_i hi
  have := childBounds_start (sh := sh) (index := index) (by simp at hi; omega)
  omega

/-! ## EVM memory -/

abbrev Mem := Nat → Byte

/-- `k` bytes of memory from position `p`. -/
def Mem.read (m : Mem) (p k : Nat) : Bytes := (List.range k).map fun i => m (p + i)

/-- Memory with `bs` written at `p`. -/
def Mem.write (m : Mem) (p : Nat) (bs : Bytes) : Mem :=
  fun q => if p ≤ q ∧ q < p + bs.length then bs.getD (q - p) 0 else m q

/-- `mload(p)`. -/
def mload (m : Mem) (p : Nat) : Nat := wordVal (m.read p 32)

/-- `mstore(p, w)` (`word` keeps `w mod 2^256`). -/
def mstore (m : Mem) (p w : Nat) : Mem := m.write p (word w)

/-- `shl(s, x)` on 256-bit words. -/
def shl (s x : Nat) : Nat := (x <<< s) % 2 ^ 256

/-- `shr(s, x)`. -/
def shr (s x : Nat) : Nat := x >>> s

/-! ## ConditionPacker.sol -/

/-- `_transform` on node `i`: `AbiEncoded` without compValue gets
    `0x0004`, and `EqualTo` on a non-inlined node drops its first word. -/
def transformCv (sh : List Shape) (i : Nat) (f : Flat) : Bytes :=
  let cv := if f.paramType = .AbiEncoded ∧ f.compValue.length = 0 then [0, 4] else f.compValue
  if f.operator = .EqualTo ∧ isInlined sh i = false then cv.drop 32 else cv

/-- `_transform` (in place in Solidity). -/
def transform (fs : List Flat) : List Flat :=
  (List.range fs.length).map fun i =>
    let f := at! fs i
    { f with compValue := transformCv (shapes fs) i f }

/-- One iteration of `_count`: `(compValuesSize, maxPluckCount)`. -/
def countStep (acc : Nat × Nat) (f : Flat) : Nat × Nat :=
  let maxPluckCount :=
    if f.operator = .Pluck then
      let pluckIndex := (f.compValue.headD 0).val
      if pluckIndex + 1 > acc.2 then pluckIndex + 1 else acc.2
    else acc.2
  let length := f.compValue.length
  let compValuesSize := if length > 0 then acc.1 + (2 + length) else acc.1
  (compValuesSize, maxPluckCount)

/-- `_count`. -/
def count (fs : List Flat) : Nat × Nat := fs.foldl countStep (0, 0)

/-- The 32-bit node word of `_packNodes`. -/
def packedNode (encoding operator childCount inlinedSize hasCompValue : Nat) : Nat :=
  (encoding <<< 29) ||| (operator <<< 24) ||| (childCount <<< 14) |||
    (inlinedSize <<< 1) ||| hasCompValue

structure PackState where
  m : Mem
  offset : Nat
  compValueOffset : Nat

/-- One iteration of the `_packNodes` loop. -/
def packStep (sh : List Shape) (fs : List Flat) (st : PackState) (i : Nat) : PackState :=
  let condition := at! fs i
  let childCount := (childBounds sh i).2
  let inlinedSz := if isInlined sh i then inlinedSize sh i else 0
  let compValue := condition.compValue
  let compValueLength := compValue.length
  let hasCompValue := decide (compValueLength > 0)
  let packed := packedNode (encCode condition.paramType) (opCode condition.operator)
    childCount inlinedSz (if hasCompValue then 1 else 0)
  -- mstore(dest, or(mload(dest), shl(224, packed)))
  let m := mstore st.m st.offset (mload st.m st.offset ||| shl 224 packed)
  let offset := st.offset + 4
  if hasCompValue then
    -- mstore(dest, shl(240, compValueLength)); mcopy(add(dest, 2), compValue, length)
    let m := mstore m st.compValueOffset (shl 240 compValueLength)
    let m := m.write (st.compValueOffset + 2) compValue
    ⟨m, offset, st.compValueOffset + 2 + compValueLength⟩
  else ⟨m, offset, st.compValueOffset⟩

/-- `_packNodes`. -/
def packNodes (sh : List Shape) (fs : List Flat) (st : PackState) : PackState :=
  (List.range fs.length).foldl (packStep sh fs) st

/-- `ConditionPacker.pack` after `_transform`. `junk` is the memory outside
    the new buffer; `new bytes(len)` zeroes the buffer itself. -/
def packBuffer (junk : Mem) (fs : List Flat) : Bytes :=
  let (compValuesSize, maxPluckCount) := count fs
  let nodeCount := fs.length
  let len := 3 + nodeCount * 4 + compValuesSize
  let m : Mem := fun q => if q < len then 0 else junk q
  let header := (nodeCount <<< 8) ||| maxPluckCount
  let m := mstore m 0 (shl 232 header)
  let st := packNodes (shapes fs) fs ⟨m, 3, 3 + nodeCount * 4⟩
  st.m.read 0 len

/-- `ConditionPacker.pack`. -/
def pack (junk : Mem) (fs : List Flat) : Bytes := packBuffer junk (transform fs)

/-! ## ConditionUnpacker.sol -/

/-- A `Condition` struct as the unpacker fills it; `children` are indices
    into the `Condition[]` array. -/
structure URec where
  encoding : Nat
  operator : Nat
  children : List Nat
  inlined : Bool
  size : Nat
  leadingBytes : Nat
  compValue : Bytes

structure UState where
  offset : Nat
  compValueOffset : Nat
  childConditionPtr : Nat
  recs : List URec

/-- One iteration of the `_unpackConditions` loop. `avatar` is
    `abi.encode(avatar)` for the address in `AVATAR_SLOT`. -/
def unpackStep (avatar : Bytes) (m : Mem) (st : UState) (_c : Nat) : UState :=
  let packed := shr 224 (mload m st.offset)
  let offset := st.offset + 4
  let encoding := packed >>> 29
  let encoding := if encoding = 6 then 0 else encoding
  let childCount := (packed >>> 14) &&& 0x3FF
  let inlinedSz := (packed >>> 1) &&& 0x1FFF
  let operator := (packed >>> 24) &&& 0x1F
  let (compValueOffset, leadingBytes, compValue) :=
    if (packed &&& 1) ≠ 0 then
      let length := shr 240 (mload m st.compValueOffset)
      let compValueOffset := st.compValueOffset + 2
      let (compValueOffset, leadingBytes, length) :=
        if encoding = 5 then
          (compValueOffset + 2, shr 240 (mload m compValueOffset),
            (length + 2 ^ 256 - 2) % 2 ^ 256)  -- sub(length, 2)
        else (compValueOffset, 0, length)
      if length > 0 then (compValueOffset + length, leadingBytes, m.read compValueOffset length)
      else (compValueOffset, leadingBytes, [])
    else (st.compValueOffset, 0, [])
  let (children, childConditionPtr) :=
    if childCount > 0 then (List.range' st.childConditionPtr childCount, st.childConditionPtr + childCount)
    else ([], st.childConditionPtr)
  -- EqualToAvatar: replace with EqualTo + avatar address
  let (operator, compValue) := if operator = 15 then (16, avatar) else (operator, compValue)
  { offset, compValueOffset, childConditionPtr,
    recs := st.recs ++ [⟨encoding, operator, children, inlinedSz > 0, inlinedSz, leadingBytes, compValue⟩] }

/-- The tree reachable from struct `i`, following child indices (`fuel`
    bounds the depth). `none` where Solidity would panic (`Encoding(7)`,
    an index past the array) or for a placeholder operator. -/
def toTree (recs : List URec) : Nat → Nat → Option Condition
  | 0, _ => none
  | fuel + 1, i => do
    let r ← recs[i]?
    let encoding ← encOf? r.encoding
    let operator ← opOf? r.operator
    let children ← r.children.mapM (toTree recs fuel)
    pure ⟨encoding, operator, children, r.inlined, r.size, r.leadingBytes, r.compValue⟩

/-- `ConditionUnpacker.unpack`: the root condition and `maxPluckValue`. -/
def unpack (avatar : Bytes) (m : Mem) : Option (Condition × Nat) :=
  let header := wordVal (m.read 0 3)  -- uint24(bytes3(buffer))
  let nodeCount := header >>> 8
  let st := (List.range nodeCount).foldl (unpackStep avatar m) ⟨3, 3 + nodeCount * 4, 1, []⟩
  (toTree st.recs nodeCount 0).map fun c => (c, header &&& 0xFF)

/-- Memory holding `buf` at position 0 and `junk` elsewhere. -/
def bufMem (buf : Bytes) (junk : Mem) : Mem :=
  fun q => if q < buf.length then buf.getD q 0 else junk q

/-! ## What the round trip should produce -/

/-- The children of node `i`: the later nodes whose `parent` is `i`. -/
def kids (fs : List Flat) (i : Nat) : List Nat :=
  (List.range fs.length).filter fun j => i < j ∧ (at! fs j).parent = i

theorem mem_kids {fs : List Flat} {i j : Nat} (h : j ∈ kids fs i) : i < j ∧ j < fs.length := by
  simp [kids] at h; omega

/-- The input tree rooted at node `i`, in the form of `Roles.Condition`
    before `annotate`: `compValue` as `_transform` leaves it, except that
    `AbiEncoded` keeps its leading bytes in `leadingBytes`, and
    `EqualToAvatar` compares against the avatar. -/
def rawTree (avatar : Bytes) (fs : List Flat) (i : Nat) : Condition :=
  let f := at! fs i
  let cv := transformCv (shapes fs) i f
  { encoding := f.paramType
    operator := f.operator
    children := (kids fs i).attach.map fun ⟨j, _⟩ => rawTree avatar fs j
    inlined := false
    size := 0
    leadingBytes := if f.paramType = .AbiEncoded then wordVal (cv.take 2) else 0
    compValue :=
      if f.operator = .EqualToAvatar then avatar
      else if f.paramType = .AbiEncoded then cv.drop 2 else cv }
termination_by fs.length - i
decreasing_by
  rename_i hj
  have := mem_kids hj
  omega

/-- `max(pluckIndex) + 1` over the `Pluck` nodes, or 0. -/
def maxPluck (fs : List Flat) : Nat :=
  fs.foldl (fun acc f =>
    if f.operator = .Pluck then max acc ((f.compValue.headD 0).val + 1) else acc) 0

/-- What `_validateBFS` checks: every node after the root has an earlier
    parent, and parents never decrease. -/
structure BFS (fs : List Flat) : Prop where
  parent_lt : ∀ j, 0 < j → j < fs.length → (at! fs j).parent < j
  parent_mono : ∀ j, 0 < j → j + 1 < fs.length → (at! fs j).parent ≤ (at! fs (j + 1)).parent

/-- The inputs the theorem covers. Each is checked by `Integrity.enforce`
    (see the README). -/
structure Packable (fs : List Flat) : Prop where
  nonempty : 0 < fs.length
  node_count : fs.length ≤ 65535
  bfs : BFS fs
  comp_value_length : ∀ j < fs.length, (at! fs j).compValue.length ≤ 65535
  child_count : ∀ j < fs.length, (childBounds (shapes fs) j).2 ≤ 1023
  inlined_size : ∀ j < fs.length, isInlined (shapes fs) j = true → inlinedSize (shapes fs) j ≤ 8191
  pluck : ∀ j < fs.length, (at! fs j).operator = .Pluck →
    (at! fs j).compValue ≠ [] ∧ ((at! fs j).compValue.headD 0).val ≤ 254
  equal_to : ∀ j < fs.length, (at! fs j).operator = .EqualTo → isInlined (shapes fs) j = false →
    32 ≤ (at! fs j).compValue.length
  abi_encoded : ∀ j < fs.length, (at! fs j).paramType = .AbiEncoded →
    (at! fs j).compValue.length ≠ 1 ∧ (at! fs j).operator ≠ .EqualTo

end ConditionPacking
