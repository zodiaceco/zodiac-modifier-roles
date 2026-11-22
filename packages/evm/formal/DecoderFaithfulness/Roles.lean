import DecoderFaithfulness.Bytes

/-!
# Zodiac Roles v3 decoder — transcription

Transcribed from `packages/evm/contracts`:

* `common/AbiLocation.sol`         → `child`, `children`, `elements`,
                                     `slicePayload`, `sliceRegion`
* `core/serialize/ConditionPacker.sol` + `ConditionUnpacker.sol`
                                   → `isInlined`, `inlinedSize`
                                     (`ConditionPacker._layout`) and
                                     `annotate` (the `inlineSize` /
                                     `leadingBytes` metadata the evaluator sees)
* `core/evaluate/ConditionEvaluator.sol`
                                   → `input` (`_read`), `Visit` (which node
                                     `_evaluate` visits at which calldata
                                     slice) and `Eval` (adds the Zip jump of
                                     `_zipIterator` / `_zipElements` via the
                                     spans `_pluck` stores)
* `core/evaluate/BitmaskChecker.sol` → `bitmaskCheck`

This file does not import the ABI spec. Each definition follows the Solidity
control flow; deviations are listed here and at the definition:

* Arithmetic is on `Nat`. Solidity uses checked `uint256` arithmetic, which
  reverts on overflow. A revert denies the transaction, so it can only make
  Roles stricter than this model, never more permissive.
* A `bytes calldata` slice is its offset in the calldata of the transaction
  and its length (`Slice`). A word is read at an offset of the calldata,
  zero-filled past its end. The Solidity reads a word only within the slice
  it has checked, so what lies past the calldata is never read; the one
  exception is the last chunk of a `Bitmask`, which is rinsed.
* A function returns `none` where Solidity returns `ok = false`; every
  caller discards the other results then.
* `sliceRegion` returns the length of the region, which starts where the
  slice does.
* The tree is the recursive `Condition` the unpacker produces, not the flat
  `ConditionFlat[]`. `ConditionPacker._layout` computes the inlined size on
  the flat array, in one bottom-up pass; `isInlined` and `inlinedSize` here
  define it by recursion on the tree. On a BFS-ordered array (enforced by
  Integrity) the nodes whose `parent` is a node are its children, in order,
  as used here. That the pass computes these values is proven in
  `ConditionPacking/Layout.lean` (`layout_eq`).
-/

namespace DecoderFaithfulness.Roles

/-- `Encoding` in `types/Condition.sol`. -/
inductive Encoding where
  | None | Static | Dynamic | Tuple | Array | AbiEncoded | EtherValue
  deriving DecidableEq, Repr, Inhabited

/-- `Operator` in `types/Operator.sol` (placeholders omitted; `EqualToAvatar`
    is rewritten to `EqualTo` by the unpacker). -/
inductive Operator where
  | Pass | And | Or | Empty | Matches | ArraySome | ArrayEvery | ArrayTailMatches
  | ZipSome | ZipEvery | Slice | Pluck | EqualToAvatar | EqualTo | GreaterThan
  | LessThan | SignedIntGreaterThan | SignedIntLessThan | Bitmask | Custom
  | WithinRatio | WithinAllowance | CallWithinAllowance
  deriving DecidableEq, Repr, Inhabited

/-- `struct Condition` (the BFS `index` is omitted). -/
structure Condition where
  encoding : Encoding
  operator : Operator
  children : List Condition
  inlineSize : Nat
  leadingBytes : Nat
  compValue : Bytes
  deriving Inhabited

abbrev Calldata := Bytes

/-- A `bytes calldata` slice (and the `Span` that packs one): `length` bytes
    at `offset` of the calldata of the transaction. -/
structure Slice where
  offset : Nat
  length : Nat
  deriving DecidableEq, Repr, Inhabited

/-- The bytes of a slice. -/
def Slice.bytes (data : Calldata) (s : Slice) : Bytes := (data.drop s.offset).take s.length

/-- `calldataload(add(data.offset, p))`: 32 bytes, zero-filled past the end. -/
def load (data : Calldata) (p : Nat) : Nat :=
  wordVal ((data.drop p ++ zeros 32).take 32)

/-- `calldataload(add(data.offset, p))` as bytes, zero-filled past the end of
    `data` (on-chain, whatever follows `data` in `msg.data`). -/
def loadBytes (data : Calldata) (p : Nat) : Bytes := (data.drop p ++ zeros 32).take 32

/-- `~uint256(31)`. -/
def notU31 : Nat := 2 ^ 256 - 32

/-! ## AbiLocation.sol

`_slice`, `_suffix` and `_word` are inlined: a slice of a slice adds to its
offset, and `_word(slice, start)` is `load data (slice.offset + start)`. -/

/-- `AbiLocation._slotSize`. -/
def slotSize (inlineSize : Nat) : Nat := if inlineSize > 0 then inlineSize else 32

/-- `AbiLocation._child`: the child whose slot is `head` bytes into `body`,
    and the offset of the slot after it. -/
def child (data : Calldata) (body : Slice) (head inlineSize : Nat) : Option (Slice × Nat) :=
  let room := body.length
  if head > room ∨ slotSize inlineSize > room - head then none
  else
    let next := head + slotSize inlineSize
    if inlineSize > 0 then some (⟨body.offset + head, slotSize inlineSize⟩, next)
    else
      let offset := load data (body.offset + head)
      if offset < next ∨ offset > room ∨ room - offset < 32 then none
      else some (⟨body.offset + offset, room - offset⟩, next)

/-- The loop of `AbiLocation.children` and of `elements`, for `i` in
    `[i, i + n)`. `sizeAt i` is the `inlineSize` of child `i`. -/
def childrenLoop (data : Calldata) (body : Slice) (sizeAt : Nat → Nat) :
    (n i head : Nat) → Option (List Slice)
  | 0, _, _ => some []
  | n + 1, i, head =>
    match child data body head (sizeAt i) with
    | none => none
    | some (span, next) => (childrenLoop data body sizeAt n (i + 1) next).map (span :: ·)

/-- `AbiLocation._array`: the block of elements past the count word, and the
    count. -/
def array (data : Calldata) (s : Slice) (elementSize : Nat) : Option (Slice × Nat) :=
  if s.length < 32 then none
  else
    let body : Slice := ⟨s.offset + 32, s.length - 32⟩
    let count := load data s.offset
    if count ≤ body.length / slotSize elementSize then some (body, count) else none

/-- `AbiLocation.elements`. -/
def elements (data : Calldata) (s : Slice) (elementSize : Nat) : Option (List Slice) :=
  match array data s elementSize with
  | none => none
  | some (body, count) => childrenLoop data body (fun _ => elementSize) count 0 0

/-- `AbiLocation.children`. -/
def children (data : Calldata) (s : Slice) (condition : Condition) : Option (List Slice) :=
  if condition.encoding = .Array then
    match condition.children with
    | [] => none
    | c0 :: _ => elements data s c0.inlineSize
  else
    childrenLoop data s (fun i => (condition.children.getD i default).inlineSize)
      condition.children.length 0 0

/-- `AbiLocation.slicePayload`. -/
def slicePayload (data : Calldata) (s : Slice) (inlineSize : Nat) : Option Slice :=
  if inlineSize > 0 then
    if inlineSize > s.length then none else some ⟨s.offset, inlineSize⟩
  else if s.length < 32 then none
  else
    let length := load data s.offset
    if length > s.length - 32 then none else some ⟨s.offset + 32, length⟩

/-- The head of a Tuple: one slot per child. -/
def headSize : List Condition → Nat
  | [] => 0
  | c :: cs => slotSize c.inlineSize + headSize cs

/-- Step 5 of `sliceRegion` for an Array of referenced elements (`regionOf`
    stands for the recursive `sliceRegion(.., children[0])`): `n` elements
    left, the next slot at `head`, the next tail expected at `cursor`. -/
def regionArrayLoop (data : Calldata) (body : Slice) (regionOf : Slice → Option Nat) :
    (n head cursor : Nat) → Option Nat
  | 0, _, cursor => some cursor
  | n + 1, head, cursor =>
    if load data (body.offset + head) ≠ cursor then none
    else
      match regionOf ⟨body.offset + cursor, body.length - cursor⟩ with
      | none => none
      | some len => regionArrayLoop data body regionOf n (head + 32) (cursor + len)

mutual
  /-- `AbiLocation.sliceRegion`: the length of the region (it starts where
      the slice does). -/
  def region (data : Calldata) (s : Slice) : Condition → Option Nat
    | ⟨encoding, _, cs, inlineSize, _, _⟩ =>
      -- 1. Inlined
      if inlineSize > 0 then
        if inlineSize > s.length then none else some inlineSize
      -- 2. Dynamic, or nested AbiEncoded
      else if encoding = .Dynamic ∨ encoding = .AbiEncoded then
        match slicePayload data s 0 with
        | none => none
        | some payload =>
          let padded := (payload.length + 31) &&& notU31
          -- `payload.length & 31`
          let rest := payload.length % 32
          if padded > s.length - 32 then none
          -- `_word(data, padded) << (rest * 8) != 0`
          else if rest ≠ 0 ∧ (loadBytes data (s.offset + padded)).drop rest ≠ zeros (32 - rest)
          then none
          else some (32 + padded)
      -- 3. Logical combinator
      else if encoding = .None then regionNone data s cs
      -- 4. Array or Tuple
      else if encoding = .Array then
        match cs with
        | [] => none
        | c0 :: _ =>
          match array data s c0.inlineSize with
          | none => none
          | some (body, count) =>
            if c0.inlineSize > 0 then some (32 + count * c0.inlineSize)
            else
              (regionArrayLoop data body (fun sl => region data sl c0) count 0 (count * 32)).map
                (32 + ·)
      else if encoding = .Tuple then
        if headSize cs > s.length then none else regionTuple data s cs 0 (headSize cs)
      else none

  /-- `Encoding.None` branch of `sliceRegion`: the first child that yields a
      region. -/
  def regionNone (data : Calldata) (s : Slice) : List Condition → Option Nat
    | [] => none
    | c :: cs =>
      match region data s c with
      | some len => some len
      | none => regionNone data s cs

  /-- Step 5 of `sliceRegion` for a Tuple: the next slot at `head`, the next
      tail expected at `cursor`. -/
  def regionTuple (data : Calldata) (body : Slice) : List Condition → Nat → Nat → Option Nat
    | [], _, cursor => some cursor
    | c :: cs, head, cursor =>
      if c.inlineSize > 0 then regionTuple data body cs (head + c.inlineSize) cursor
      else if load data (body.offset + head) ≠ cursor then none
      else
        match region data ⟨body.offset + cursor, body.length - cursor⟩ c with
        | none => none
        | some len => regionTuple data body cs (head + 32) (cursor + len)
end

/-- `AbiLocation.sliceRegion`. -/
def sliceRegion (data : Calldata) (s : Slice) (condition : Condition) : Option Slice :=
  (region data s condition).map fun len => ⟨s.offset, len⟩

/-! ## Inlined and inlined size (computed at pack time, on the flat array) -/

mutual
  def isInlined : Condition → Bool
    | ⟨encoding, _, cs, _, _, _⟩ =>
      if encoding = .Dynamic ∨ encoding = .Array ∨ encoding = .AbiEncoded then false
      else isInlinedAll cs

  def isInlinedAll : List Condition → Bool
    | [] => true
    | c :: cs => isInlined c && isInlinedAll cs
end

mutual
  def inlinedSize : Condition → Nat
    | ⟨encoding, _, cs, _, _, _⟩ =>
      if encoding = .Static then 32 else inlinedSizeLoop (encoding = .None) cs

  /-- Children loop of `inlinedSize`: `None` returns the first non-zero
      child size, other encodings sum. -/
  def inlinedSizeLoop (isNone : Bool) : List Condition → Nat
    | [] => 0
    | c :: cs =>
      let childSize := inlinedSize c
      if isNone ∧ childSize > 0 then childSize
      else childSize + inlinedSizeLoop isNone cs
end

/-! ## Pack + unpack: the metadata the evaluator sees

`ConditionPacker` stores `inlinedSize` for an inlined node and 0 otherwise;
`ConditionUnpacker` sets `inlineSize` to it, maps `EtherValue` to `None`, and
sets `leadingBytes` for `AbiEncoded` from the compValue (default `4`, patched
in by `ConditionPacker._transform`).

A raw node's `leadingBytes` field holds the value encoded in its compValue
(or 4 if none); `inlineSize` of raw nodes is ignored. `compValue` is passed
through unchanged: the only compValue that affects locations is `Slice`'s,
which packing does not touch (the `AbiEncoded` prefix split and `EqualTo`
rewrites only concern compValues that are compared, not used to navigate). -/

def annotate : Condition → Condition
  | c@⟨encoding, operator, cs, _, lb, cv⟩ =>
    { encoding := if encoding = .EtherValue then .None else encoding
      operator := if operator = .EqualToAvatar then .EqualTo else operator
      children := cs.attach.map (fun ⟨ch, _⟩ => annotate ch)
      inlineSize := if isInlined c then inlinedSize c else 0
      leadingBytes := if encoding = .AbiEncoded then lb else 0
      compValue := cv }

/-! ## ConditionEvaluator.sol

The root slice (`context.data`) is the whole calldata, `⟨0, data.length⟩`:
the `location` of a slice, its offset from the root's, is its `offset`. -/

/-- What `_read` hands to the comparison operators. A value longer than 32
    bytes is hashed with keccak256; it is represented by its preimage, so two
    inputs are equal here iff the hashed bytes are equal (soundness of this
    representation only needs keccak to be a function). -/
inductive Input where
  | etherValue
  | overflow
  | word (n : Nat)
  | hash (preimage : Bytes)
  deriving Inhabited, DecidableEq

/-- The operand of `_read`, `_pluck` and `_custom`: in place when inlined (or
    below a Slice), otherwise sized from calldata. -/
def operand (data : Calldata) (s : Slice) (inlineSize : Nat) (condition : Condition) :
    Option Slice :=
  if inlineSize > 0 then slicePayload data s inlineSize else sliceRegion data s condition

/-- `ConditionEvaluator._read` (the word). -/
def input (data : Calldata) (s : Slice) (inlineSize : Nat) (condition : Condition) : Input :=
  if condition.encoding = .None then .etherValue
  else
    match operand data s inlineSize condition with
    | none => .overflow
    | some op =>
      -- `bytes32(operand) >> ((32 - length) * 8)`
      if op.length > 32 then .hash (op.bytes data) else .word (wordVal (op.bytes data))

/-- The length `_compare` takes of its operand: 32 for the ether value. -/
def inputLength (data : Calldata) (s : Slice) (inlineSize : Nat) (condition : Condition) : Nat :=
  if condition.encoding = .None then 32
  else
    match operand data s inlineSize condition with
    | none => 0
    | some op => op.length

/-- `_slice` compValue: `uint16(bytes2(compValue))`. -/
def sliceShift (cv : Bytes) : Nat := (cv.getD 0 0).val * 256 + (cv.getD 1 0).val

/-- `_slice` compValue: `uint8(compValue[2])`. -/
def sliceSize (cv : Bytes) : Nat := (cv.getD 2 0).val

/-- Operators that call `_read` on their own node. -/
def readsInput : Operator → Bool
  | .EqualTo | .GreaterThan | .LessThan | .SignedIntGreaterThan
  | .SignedIntLessThan | .WithinAllowance | .Pluck => true
  | _ => false

/-- The block `_matches` finds the children in: the slice itself, or for
    `AbiEncoded` the payload of the `bytes` value (the slice itself at the
    root) past the leading bytes. -/
def matchesBody (data : Calldata) (s : Slice) (condition : Condition) : Option Slice :=
  if condition.encoding = .AbiEncoded then
    match (if s.offset ≠ 0 then slicePayload data s 0 else some s) with
    | none => none
    | some body =>
      if condition.leadingBytes > body.length then none
      else some ⟨body.offset + condition.leadingBytes, body.length - condition.leadingBytes⟩
  else some s

/-- `Visit data c s z p d l y`: evaluating `c` at slice `s` (with
    `inlineSize` `z`) can evaluate node `d` at `l` (with `inlineSize` `y`).
    `p` records the ABI component index of each structural step (`Matches`
    child `i`, array element `i`); `And`/`Or` add no step. One constructor
    per branch of `_evaluate` that recurses into a child at a slice derived
    from its own. Short-circuiting only removes visits, so it is not
    modeled. `Zip*` reads spans stored by earlier `Pluck` nodes instead;
    that jump is added by `Eval` below. -/
inductive Visit (data : Calldata) :
    Condition → Slice → Nat → List Nat → Condition → Slice → Nat → Prop
  | here {c s z} : Visit data c s z [] c s z
  /-- `_and` / `_or`: every child at the same slice. -/
  | logical {c s z p d l y} (ch : Condition) :
      (c.operator = .And ∨ c.operator = .Or) → ch ∈ c.children →
      Visit data ch s ch.inlineSize p d l y → Visit data c s z p d l y
  /-- `_matches`: decodes `children(body)` and requires one span per
      child. -/
  | matchesChild {c s z p d l y} (body : Slice) (spans : List Slice) (i : Nat)
      (hi : i < spans.length) :
      c.operator = .Matches →
      matchesBody data s c = some body →
      children data body c = some spans →
      c.children.length = spans.length →
      Visit data (c.children.getD i default) spans[i]
        (c.children.getD i default).inlineSize p d l y →
      Visit data c s z (i :: p) d l y
  /-- `_arrayIterator` (`ArraySome` / `ArrayEvery`): `children[0]` at every
      element. -/
  | arrayIter {c s z p d l y} (spans : List Slice) (i : Nat) (hi : i < spans.length) :
      (c.operator = .ArraySome ∨ c.operator = .ArrayEvery) →
      children data s c = some spans →
      Visit data (c.children.headD default) spans[i]
        (c.children.headD default).inlineSize p d l y →
      Visit data c s z (i :: p) d l y
  /-- `_arrayTailMatches`: `children[j]` at element `count - #children + j`. -/
  | arrayTail {c s z p d l y} (spans : List Slice) (j : Nat)
      (hj : spans.length - c.children.length + j < spans.length) :
      c.operator = .ArrayTailMatches →
      children data s c = some spans →
      c.children.length ≤ spans.length →
      j < c.children.length →
      Visit data (c.children.getD j default) spans[spans.length - c.children.length + j]
        (c.children.getD j default).inlineSize p d l y →
      Visit data c s z ((spans.length - c.children.length + j) :: p) d l y
  /-- `_slice`: the window `[shift, shift + size)` of the payload (a static
      value, or the content of a dynamic value after its length word),
      evaluated by `children[0]` with the window size as `inlineSize`. No
      index step: the child still describes (part of) the same component. -/
  | slice {c s z p d l y} (payload : Slice) :
      c.operator = .Slice →
      slicePayload data s z = some payload →
      sliceShift c.compValue + sliceSize c.compValue ≤ payload.length →
      Visit data (c.children.headD default)
        ⟨payload.offset + sliceShift c.compValue, sliceSize c.compValue⟩
        (sliceSize c.compValue) p d l y →
      Visit data c s z p d l y

/-! ## ConditionEvaluator.sol: `ZipSome` / `ZipEvery`

`_pluck` stores the span of its operand in
`context.pluckedLocations[compValue[0]]` (an empty span for the ether
value); `_zipElements` decodes field `f` of the Zip as the array in
`pluckedLocations[compValue[f]]`, with the `inlineSize` of `fields[f]` as
element size, and `_zipIterator` evaluates `fields[f]` at element `i`.

Modeling assumption (from Integrity, not proven here): when a Zip reads
slot `k`, the slot holds the span the unique Pluck node with index `k`
stored. Integrity's `_plucks` makes the Pluck node unique, `_slots` makes
every slot a Zip reads written before on that evaluation path, and `_pluck`
is the only writer. -/

/-- `condition.children[0].children`: the fields of a Zip. -/
def zipFields (c : Condition) : List Condition := (c.children.headD default).children

/-- `uint8(compValue[k])`. (Out of range panics in Solidity; Integrity sizes
    the compValues of Zip and Pluck.) -/
def cvByte (cv : Bytes) (k : Nat) : Nat := (cv.getD k 0).val

/-- The span `_pluck` stores. -/
def pluckSpan (data : Calldata) (s : Slice) (inlineSize : Nat) (condition : Condition) :
    Option Slice :=
  if condition.encoding = .None then some ⟨0, 0⟩ else operand data s inlineSize condition

/-- `Eval data root p d l y`: evaluating `root` at the calldata can evaluate
    `d` at `l` (with `inlineSize` `y`). `Visit`, plus Zip jumps: field `f`
    of a visited Zip is evaluated at element `i` of the array in the span a
    visited Pluck node with the referenced index stored. `p` is the
    component path of `d` from the root: the Pluck node's path, then the
    element index. The Zip's own slice is unused, as in `_zipIterator`. -/
inductive Eval (data : Calldata) (root : Condition) :
    List Nat → Condition → Slice → Nat → Prop
  | visit {p d l y} :
      Visit data root ⟨0, data.length⟩ root.inlineSize p d l y → Eval data root p d l y
  | zip {pz z lz yz pp pk L yk p d l y} (f : Nat) (op : Slice) (spans : List Slice) (i : Nat)
      (hi : i < spans.length) :
      Eval data root pz z lz yz →
      (z.operator = .ZipSome ∨ z.operator = .ZipEvery) →
      f < (zipFields z).length →
      Eval data root pp pk L yk →
      pk.operator = .Pluck →
      cvByte pk.compValue 0 = cvByte z.compValue f →
      pluckSpan data L yk pk = some op →
      elements data op ((zipFields z).getD f default).inlineSize = some spans →
      Visit data ((zipFields z).getD f default) spans[i]
        ((zipFields z).getD f default).inlineSize p d l y →
      Eval data root (pp ++ i :: p) d l y

/-! ## BitmaskChecker.sol

`bytes32` values are modeled as their 32 bytes, so `&` is bytewise and `==`
is equality of byte lists. -/

/-- The `Status` values `BitmaskChecker.check` returns. -/
inductive BitmaskStatus where
  | Ok | BitmaskOverflow | BitmaskNotAllowed | CalldataOverflow
  deriving DecidableEq, Repr, Inhabited

/-- `a & b` on `bytes32`. -/
def band (a b : Bytes) : Bytes := List.zipWith (· &&& ·) a b

/-- `mload(add(add(compValue, 0x22), p))`: the 32 bytes at byte `2 + p` of the
    compValue (after its length word). Past its end, memory holds whatever
    follows (`junk`, arbitrary). -/
def mloadCv (cv junk : Bytes) (p : Nat) : Bytes := (cv.drop (2 + p) ++ junk ++ zeros 32).take 32

/-- `_rinseMask(bytesLeft)`: `min(bytesLeft, 32)` leading `0xff` bytes, then
    zeros. -/
def rinseMask (bytesLeft : Nat) : Bytes :=
  List.replicate (min bytesLeft 32) 255 ++ zeros (32 - min bytesLeft 32)

/-- The chunk loop of `check`, `for (i = 0; i < n; i += 32)`, with `fuel`
    iterations available (`n` is enough: the loop runs `⌈n/32⌉ ≤ n` times).
    `value` is the calldata from the start of the operand on: a chunk may
    reach past the operand, and what it reads there is rinsed. -/
def bitmaskLoop (value cv junk : Bytes) (shift n : Nat) : (fuel i : Nat) → BitmaskStatus
  | 0, _ => .Ok
  | fuel + 1, i =>
    if i < n then
      let mask := mloadCv cv junk i
      let expected := mloadCv cv junk (n + i)
      let actual := loadBytes value (shift + i)
      let rinse := rinseMask (n - i)
      if band expected rinse ≠ band (band actual mask) rinse then .BitmaskNotAllowed
      else bitmaskLoop value cv junk shift n fuel (i + 32)
    else .Ok

/-- `BitmaskChecker.check(operand, compValue)`. `compValue.length - 2`
    reverts in Solidity for a compValue shorter than 2 bytes (Integrity
    requires at least 4); here it is 0. -/
def bitmaskCheck (data : Calldata) (operand : Slice) (cv junk : Bytes) : BitmaskStatus :=
  let shift := sliceShift cv
  let n := (cv.length - 2) / 2
  -- the mask window must fit within the operand
  if shift + n > operand.length then .BitmaskOverflow
  else bitmaskLoop (data.drop operand.offset) cv junk shift n n 0

/-- `ConditionEvaluator._bitmask`. -/
def bitmask (data : Calldata) (s : Slice) (inlineSize : Nat) (cv junk : Bytes) : BitmaskStatus :=
  match slicePayload data s inlineSize with
  | none => .CalldataOverflow
  | some payload => bitmaskCheck data payload cv junk

end DecoderFaithfulness.Roles
