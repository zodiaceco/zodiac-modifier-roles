import DecoderFaithfulness.Bytes

/-!
# Zodiac Roles v3 decoder — transcription

Transcribed from `packages/evm/contracts` (branch `main`, commit 9a63c505):

* `common/AbiLocation.sol`         → `tailLocation`, `children`, `size`
* `core/serialize/Topology.sol`    → `isInlined`, `inlinedSize`
* `core/serialize/ConditionPacker.sol` + `ConditionUnpacker.sol`
                                   → `annotate` (the `inlined` / `size` /
                                     `leadingBytes` metadata the evaluator sees)
* `core/evaluate/ConditionEvaluator.sol`
                                   → `input` (`__input`), `Visit` (which
                                     node `evaluate` visits at which calldata
                                     location) and `Eval` (adds the Zip jump
                                     of `_zipIterator` / `_zipLocations` via
                                     the locations `_pluck` stores)
* `core/evaluate/BitmaskChecker.sol` → `bitmaskCheck`

This file does not import the ABI spec. Each definition follows the Solidity
control flow; deviations are listed here and at the definition:

* Arithmetic is on `Nat`. Solidity uses checked `uint256` arithmetic, which
  reverts on overflow. A revert denies the transaction, so it can only make
  Roles stricter than this model, never more permissive.
* `children` returns `none` where Solidity returns `(partialResult, true)`;
  every caller discards the result when the flag is set.
* `Condition.children[0]` on an empty array panics in Solidity; here it reads
  a default node. Integrity rejects containers without children, and the
  theorems assume trees accepted by Integrity.
* The tree is the recursive `Condition` the unpacker produces, not the flat
  `ConditionFlat[]`. `Topology` walks the flat array via `childBounds`; on a
  BFS-ordered array (enforced by Integrity) that yields the node's children,
  in order, as used here.
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
  inlined : Bool
  size : Nat
  leadingBytes : Nat
  compValue : Bytes
  deriving Inhabited

/-- `condition.size = n` (as `_slice` does to its child). -/
def Condition.withSize (c : Condition) (n : Nat) : Condition := { c with size := n }

@[simp] theorem Condition.withSize_encoding (c : Condition) (n : Nat) :
    (c.withSize n).encoding = c.encoding := rfl
@[simp] theorem Condition.withSize_operator (c : Condition) (n : Nat) :
    (c.withSize n).operator = c.operator := rfl
@[simp] theorem Condition.withSize_children (c : Condition) (n : Nat) :
    (c.withSize n).children = c.children := rfl
@[simp] theorem Condition.withSize_inlined (c : Condition) (n : Nat) :
    (c.withSize n).inlined = c.inlined := rfl
@[simp] theorem Condition.withSize_size (c : Condition) (n : Nat) :
    (c.withSize n).size = n := rfl
@[simp] theorem Condition.withSize_compValue (c : Condition) (n : Nat) :
    (c.withSize n).compValue = c.compValue := rfl
@[simp] theorem Condition.withSize_leadingBytes (c : Condition) (n : Nat) :
    (c.withSize n).leadingBytes = c.leadingBytes := rfl

abbrev Calldata := Bytes

/-- `calldataload(add(data.offset, p))`: 32 bytes, zero-filled past the end. -/
def load (data : Calldata) (p : Nat) : Nat :=
  wordVal ((data.drop p ++ zeros 32).take 32)

/-- `~uint256(31)`. -/
def notU31 : Nat := 2 ^ 256 - 32

/-! ## AbiLocation.sol -/

/-- `AbiLocation._tailLocation`. -/
def tailLocation (data : Calldata) (location headOffset : Nat) : Nat :=
  -- HEAD overflows buffer
  if location + headOffset + 32 > data.length then data.length + 1
  else
    let tailOffset := load data (location + headOffset)
    -- TAIL points backwards (malicious or malformed)
    if tailOffset ≤ headOffset then data.length + 1
    -- TAIL overflows buffer
    else if location + tailOffset + 32 > data.length then data.length + 1
    else location + tailOffset

/-- Loop body of `AbiLocation.children`, for `i` in `[i, i + n)`. `childAt i`
    is `condition.children[isArray ? 0 : i]`. -/
def childrenLoop (data : Calldata) (location : Nat) (childAt : Nat → Condition) :
    (n i headOffset : Nat) → Option (List Nat)
  | 0, _, _ => some []
  | n + 1, i, headOffset =>
    let child := childAt i
    let r := if child.inlined then location + headOffset
             else tailLocation data location headOffset
    let headOffset' := if child.inlined then headOffset + child.size else headOffset + 32
    if r > data.length then none
    else (childrenLoop data location childAt n (i + 1) headOffset').map (r :: ·)

/-- `AbiLocation.children`. -/
def children (data : Calldata) (location : Nat) (condition : Condition) : Option (List Nat) :=
  if condition.encoding = .Array then
    if location + 32 > data.length then none
    else
      let childCount := load data location
      childrenLoop data (location + 32) (fun _ => condition.children.headD default)
        childCount 0 0
  else
    childrenLoop data location (fun i => condition.children.getD i default)
      condition.children.length 0 0

/-- Array loop of `AbiLocation.size` (`isArray`: every element uses
    `children[0]`; `sizeOf` stands for the recursive `size(.., child)`). -/
def sizeArrayLoop (data : Calldata) (location : Nat) (child : Condition)
    (sizeOf : Nat → Nat) : (n headOffset : Nat) → Nat
  | 0, _ => 0
  | n + 1, headOffset =>
    if child.inlined then
      child.size + sizeArrayLoop data location child sizeOf n (headOffset + child.size)
    else
      32 + sizeOf (tailLocation data location headOffset)
        + sizeArrayLoop data location child sizeOf n (headOffset + 32)

mutual
  /-- `AbiLocation.size`. -/
  def size (data : Calldata) (location : Nat) : Condition → Nat
    | ⟨encoding, _, cs, _, _, _, _⟩ =>
      -- Every ABI-encoded element occupies at least one word.
      if location + 32 > data.length then data.length + 1
      else if encoding = .Static then 32
      else if encoding = .Dynamic ∨ encoding = .AbiEncoded then
        32 + ((load data location + 31) &&& notU31)
      else if encoding = .None then sizeNone data location cs
      else if encoding = .Array then
        match cs with
        | [] => 32  -- children[0] is only read when the element count is > 0
        | c0 :: _ =>
          32 + sizeArrayLoop data (location + 32) c0 (fun l => size data l c0)
                 (load data location) 0
      else sizeTuple data location cs 0

  /-- `Encoding.None` branch of `size`: first child with a plausible size. -/
  def sizeNone (data : Calldata) (location : Nat) : List Condition → Nat
    | [] => data.length + 1
    | c :: cs =>
      let result := size data location c
      if result > 0 ∧ result ≤ data.length then result else sizeNone data location cs

  /-- Tuple loop of `size` (`!isArray`: element `i` uses `children[i]`). -/
  def sizeTuple (data : Calldata) (location : Nat) : List Condition → Nat → Nat
    | [], _ => 0
    | c :: cs, headOffset =>
      if c.inlined then c.size + sizeTuple data location cs (headOffset + c.size)
      else 32 + size data (tailLocation data location headOffset) c
             + sizeTuple data location cs (headOffset + 32)
end

/-! ## Topology.sol (run at pack time on the flat tree) -/

mutual
  def isInlined : Condition → Bool
    | ⟨encoding, _, cs, _, _, _, _⟩ =>
      if encoding = .Dynamic ∨ encoding = .Array ∨ encoding = .AbiEncoded then false
      else isInlinedAll cs

  def isInlinedAll : List Condition → Bool
    | [] => true
    | c :: cs => isInlined c && isInlinedAll cs
end

mutual
  def inlinedSize : Condition → Nat
    | ⟨encoding, _, cs, _, _, _, _⟩ =>
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

`ConditionPacker._packNodes` stores `inlinedSize = isInlined ? inlinedSize : 0`;
`ConditionUnpacker` sets `inlined = inlinedSize > 0`, `size = inlinedSize`,
maps `EtherValue` to `None`, and sets `leadingBytes` for `AbiEncoded` from the
compValue (default `4`, patched in by `ConditionPacker._transform`).

A raw node's `leadingBytes` field holds the value encoded in its compValue
(or 4 if none); `inlined` and `size` of raw nodes are ignored. `compValue` is
passed through unchanged: the only compValue that affects locations is
`Slice`'s, which packing does not touch (the `AbiEncoded` prefix split and
`EqualTo` rewrites only concern compValues that are compared, not used to
navigate). -/

def annotate : Condition → Condition
  | c@⟨encoding, operator, cs, _, _, lb, cv⟩ =>
    let s := if isInlined c then inlinedSize c else 0
    { encoding := if encoding = .EtherValue then .None else encoding
      operator := if operator = .EqualToAvatar then .EqualTo else operator
      children := cs.attach.map (fun ⟨ch, _⟩ => annotate ch)
      inlined := s > 0
      size := s
      leadingBytes := if encoding = .AbiEncoded then lb else 0
      compValue := cv }

/-! ## ConditionEvaluator.sol -/

/-- What `__input` hands to the comparison operators. A value longer than 32
    bytes is hashed with keccak256; it is represented by its preimage, so two
    inputs are equal here iff the hashed bytes are equal (soundness of this
    representation only needs keccak to be a function). -/
inductive Input where
  | etherValue
  | overflow
  | word (n : Nat)
  | hash (preimage : Bytes)
  deriving Inhabited, DecidableEq

/-- `ConditionEvaluator.__input`. -/
def input (data : Calldata) (location : Nat) (condition : Condition) : Input :=
  if condition.encoding = .None then .etherValue
  else
    let size := if condition.size ≠ 0 then condition.size
                else Roles.size data location condition
    if location + size > data.length then .overflow
    else if size = 32 then .word (load data location)
    -- `bytes32(data[location:location + size]) >> ((32 - size) * 8)`
    else if size < 32 then .word (wordVal ((data.drop location).take size))
    else .hash ((data.drop location).take size)

/-- `_slice` compValue: `uint16(bytes2(compValue))`. -/
def sliceShift (cv : Bytes) : Nat := (cv.getD 0 0).val * 256 + (cv.getD 1 0).val

/-- `_slice` compValue: `uint8(compValue[2])`. -/
def sliceSize (cv : Bytes) : Nat := (cv.getD 2 0).val

/-- Operators that call `__input` on their own node. -/
def readsInput : Operator → Bool
  | .EqualTo | .GreaterThan | .LessThan | .SignedIntGreaterThan
  | .SignedIntLessThan | .WithinAllowance | .Pluck => true
  | _ => false

/-- `Visit data c loc p d l`: evaluating `c` at `loc` can evaluate node `d`
    at `l`. `p` records the ABI component index of each structural step
    (`Matches` child `i`, array element `i`); `And`/`Or` add no step.
    One constructor per branch of `evaluate` that recurses into a child at a
    location derived from its own. Short-circuiting only removes visits, so
    it is not modeled. `Zip*` reads locations stored by earlier `Pluck`
    nodes instead; that jump is added by `Eval` below. -/
inductive Visit (data : Calldata) : Condition → Nat → List Nat → Condition → Nat → Prop
  | here {c loc} : Visit data c loc [] c loc
  /-- `_and` / `_or`: every child at the same location. -/
  | logical {c loc p d l} (ch : Condition) :
      (c.operator = .And ∨ c.operator = .Or) → ch ∈ c.children →
      Visit data ch loc p d l → Visit data c loc p d l
  /-- `Matches`: `location += 32` for nested `AbiEncoded`, then `_matches`
      decodes `children(location + leadingBytes)` and requires one location
      per child. -/
  | matchesChild {c loc p d l} (locs : List Nat) (i : Nat) (hi : i < locs.length) :
      c.operator = .Matches →
      children data
        ((if loc > 0 ∧ c.encoding = .AbiEncoded then loc + 32 else loc) + c.leadingBytes)
        c = some locs →
      c.children.length = locs.length →
      Visit data (c.children.getD i default) locs[i] p d l →
      Visit data c loc (i :: p) d l
  /-- `_arrayIterator` (`ArraySome` / `ArrayEvery`): `children[0]` at every
      element. -/
  | arrayIter {c loc p d l} (locs : List Nat) (i : Nat) (hi : i < locs.length) :
      (c.operator = .ArraySome ∨ c.operator = .ArrayEvery) →
      children data loc c = some locs →
      Visit data (c.children.headD default) locs[i] p d l →
      Visit data c loc (i :: p) d l
  /-- `_arrayTailMatches`: `children[j]` at element `count - #children + j`. -/
  | arrayTail {c loc p d l} (locs : List Nat) (j : Nat)
      (hj : locs.length - c.children.length + j < locs.length) :
      c.operator = .ArrayTailMatches →
      children data loc c = some locs →
      c.children.length ≤ locs.length →
      j < c.children.length →
      Visit data (c.children.getD j default) locs[locs.length - c.children.length + j] p d l →
      Visit data c loc ((locs.length - c.children.length + j) :: p) d l
  /-- `_slice`: the window `[shift, shift + size)` of the operand (a static
      word, or the content of a dynamic value after its length word),
      evaluated by `children[0]` with `size` overridden. No index step: the
      child still describes (part of) the same component. -/
  | slice {c loc p d l} :
      c.operator = .Slice →
      (c.inlined = false → loc + 32 ≤ data.length) →
      sliceShift c.compValue + sliceSize c.compValue ≤
        (if c.inlined then c.size else load data loc) →
      Visit data ((c.children.headD default).withSize (sliceSize c.compValue))
        (loc + (if c.inlined then 0 else 32) + sliceShift c.compValue) p d l →
      Visit data c loc p d l

/-! ## ConditionEvaluator.sol: `ZipSome` / `ZipEvery`

`_pluck` stores the location it is evaluated at in
`context.pluckedLocations[compValue[0]]`; `_zipLocations` decodes field `f`
of the Zip as an array at `pluckedLocations[compValue[f]]`, with
`fields[f]` as element template (the `stub`), and `_zipIterator` evaluates
`fields[f]` at element `i`.

Modeling assumption (from Integrity, not proven here): when a Zip reads
slot `k`, the slot holds a location at which the unique Pluck node with
index `k` was evaluated. `_validateUniquePluckDefinitions` makes the Pluck
node unique, `_validatePluckAssignments` makes every slot a Zip reads
written before on that evaluation path, and `_pluck` is the only writer. -/

/-- `condition.children[0].children`: the fields of a Zip. -/
def zipFields (c : Condition) : List Condition := (c.children.headD default).children

/-- `uint8(compValue[k])`. (Out of range panics in Solidity; Integrity sizes
    the compValues of Zip and Pluck.) -/
def cvByte (cv : Bytes) (k : Nat) : Nat := (cv.getD k 0).val

/-- `stub` in `_zipLocations`: an `Array` node with `field` as element
    template; every other member is zero. -/
def zipStub (field : Condition) : Condition :=
  ⟨.Array, .Pass, [field], false, 0, 0, []⟩

/-- `Eval data root p d l`: evaluating `root` at location 0 can evaluate `d`
    at `l`. `Visit`, plus Zip jumps: field `f` of a visited Zip is evaluated
    at element `i` of the array decoded at the location of a visited Pluck
    node with the referenced index. `p` is the component path of `d` from
    the root: the Pluck node's path, then the element index. The Zip's own
    location is unused, as in `_zipIterator`. -/
inductive Eval (data : Calldata) (root : Condition) : List Nat → Condition → Nat → Prop
  | visit {p d l} : Visit data root 0 p d l → Eval data root p d l
  | zip {pz z lz pp pk L p d l} (f : Nat) (locs : List Nat) (i : Nat) (hi : i < locs.length) :
      Eval data root pz z lz →
      (z.operator = .ZipSome ∨ z.operator = .ZipEvery) →
      f < (zipFields z).length →
      Eval data root pp pk L →
      pk.operator = .Pluck →
      cvByte pk.compValue 0 = cvByte z.compValue f →
      children data L (zipStub ((zipFields z).getD f default)) = some locs →
      Visit data ((zipFields z).getD f default) locs[i] p d l →
      Eval data root (pp ++ i :: p) d l

/-! ## BitmaskChecker.sol

`bytes32` values are modeled as their 32 bytes, so `&` is bytewise and `==`
is equality of byte lists. -/

/-- The `Status` values `BitmaskChecker.check` returns. -/
inductive BitmaskStatus where
  | Ok | BitmaskOverflow | BitmaskNotAllowed | CalldataOverflow
  deriving DecidableEq, Repr, Inhabited

/-- `a & b` on `bytes32`. -/
def band (a b : Bytes) : Bytes := List.zipWith (· &&& ·) a b

/-- `calldataload(add(data.offset, p))` as bytes, zero-filled past the end of
    `data` (on-chain, whatever follows `data` in `msg.data`; the loop only
    compares bytes that are in bounds, the rest is rinsed). -/
def loadBytes (data : Calldata) (p : Nat) : Bytes := (data.drop p ++ zeros 32).take 32

/-- `mload(add(add(compValue, 0x22), p))`: the 32 bytes at byte `2 + p` of the
    compValue (after its length word). Past its end, memory holds whatever
    follows (`junk`, arbitrary). -/
def mloadCv (cv junk : Bytes) (p : Nat) : Bytes := (cv.drop (2 + p) ++ junk ++ zeros 32).take 32

/-- `_rinseMask(bytesLeft)`: `min(bytesLeft, 32)` leading `0xff` bytes, then
    zeros. -/
def rinseMask (bytesLeft : Nat) : Bytes :=
  List.replicate (min bytesLeft 32) 255 ++ zeros (32 - min bytesLeft 32)

/-- The chunk loop of `check`, `for (i = start; i < n; i += 32)`, with `fuel`
    iterations available (`n` is enough: the loop runs `⌈n/32⌉ ≤ n` times).
    `value` is `data[start:]`. -/
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

/-- `BitmaskChecker.check(data, location, compValue, inlined, size)`.
    `compValue.length - 2` reverts in Solidity for a compValue shorter than 2
    bytes (Integrity requires at least 4); here it is 0. -/
def bitmaskCheck (data : Calldata) (location : Nat) (cv : Bytes) (inlined : Bool)
    (size : Nat) (junk : Bytes) : BitmaskStatus :=
  let shift := sliceShift cv
  let n := (cv.length - 2) / 2
  if inlined = false ∧ location + 32 > data.length then .BitmaskOverflow
  else
    let start := if inlined then location else location + 32
    let encodedLength := if inlined then size else load data location
    -- mask window must fit within the declared value length
    if shift + n > encodedLength then .BitmaskOverflow
    -- declared value length must be physically present in calldata
    else if start + encodedLength > data.length then .CalldataOverflow
    else bitmaskLoop (data.drop start) cv junk shift n n 0

end DecoderFaithfulness.Roles
