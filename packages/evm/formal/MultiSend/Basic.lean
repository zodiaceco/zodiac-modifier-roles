import DecoderFaithfulness.Roles

/-!
# MultiSend: the format, the unwrapper, and what MultiSend executes

`parse` is the format of a MultiSend batch as Safe's `MultiSend` documents
it: transactions concatenated, each `abi.encodePacked(uint8 operation,
address to, uint256 value, uint256 dataLength, bytes data)`, operation `0`
(call) or `1` (delegatecall). It is the reference for both transcriptions:

* `unwrap`: `MultiSendUnwrapper.unwrap`, the list of transactions Roles
  checks (`Authorization._authorize` checks each entry with its calldata
  slice `data[dataLocation : dataLocation + dataSize]`).
* `execLoop`: the assembly loop of `MultiSend.multiSend`, the calls a Safe
  makes when it delegatecalls `MultiSend` with the same calldata.

Fields are big-endian numbers: `to` the 20 address bytes, `value` the
32-byte word.
-/

namespace MultiSend
open DecoderFaithfulness DecoderFaithfulness.Roles

/-- One transaction: what `MultiSend` calls, and what Roles checks. -/
structure Entry where
  op : Nat
  to : Nat
  value : Nat
  data : Bytes
  deriving DecidableEq, Repr

/-! ## The format -/

/-- A batch, read transaction by transaction: `none` unless the bytes are
    exactly a concatenation of transactions with operation `0` or `1`. -/
def parse (c : Bytes) : Option (List Entry) :=
  match hc : c with
  | [] => some []
  | b :: _ =>
    if h : c.length < 85 then none
    else
      let len := wordVal ((c.drop 53).take 32)
      if 1 < b.val then none
      else if h2 : c.length < 85 + len then none
      else (parse (c.drop (85 + len))).map
        (⟨b.val, wordVal ((c.drop 1).take 20), wordVal ((c.drop 21).take 32),
          (c.drop 85).take len⟩ :: ·)
termination_by c.length
decreasing_by simp only [List.length_drop]; subst hc; simp only [List.length_cons] at *; omega

/-! ## `MultiSendUnwrapper.unwrap` -/

/-- `multiSend(bytes)`. -/
def selMultiSend : Bytes := [0x8d, 0x80, 0xff, 0x0a]

/-- `bytes32(data[x:])`: the slice reverts past the end; a short slice is
    zero-padded. -/
def rd32 (data : Bytes) (x : Nat) : Option Nat :=
  if x ≤ data.length then some (load data x) else none

/-- `uint8(bytes1(data[x:]))`. -/
def rd1 (data : Bytes) (x : Nat) : Option Nat :=
  if x ≤ data.length then some (wordVal ((data.drop x ++ zeros 1).take 1)) else none

/-- `address(bytes20(data[x:]))`. -/
def rd20 (data : Bytes) (x : Nat) : Option Nat :=
  if x ≤ data.length then some (wordVal ((data.drop x ++ zeros 20).take 20)) else none

/-- `_validateHeader`. -/
def validateHeader (data : Bytes) : Option Unit :=
  if (data ++ zeros 4).take 4 ≠ selMultiSend then none
  else
    match rd32 data 4, rd32 data 36 with
    | some o, some len =>
      if o ≠ 32 then none
      else if 4 + ceil32 (32 + 32 + len) ≠ data.length then none
      else some ()
    | _, _ => none

/-- The loop of `_validateEntries` (`fuel` stands for gas; every iteration
    advances at least 85 bytes). Returns `count`. -/
def validateLoop (data : Bytes) (stop : Nat) : Nat → Nat → Nat → Option Nat
  | 0, _, _ => none
  | f + 1, offset, count =>
    if offset < stop then
      match rd1 data offset with
      | none => none
      | some op =>
        if op > 1 then none
        else
          match rd32 data (offset + 53) with
          | none => none
          | some len =>
            if offset + 85 + len > stop then none
            else validateLoop data stop f (offset + 85 + len) (count + 1)
    else if count = 0 then none else some count

/-- `UnwrappedTransaction`. -/
structure Unwrapped where
  op : Nat
  to : Nat
  value : Nat
  loc : Nat
  size : Nat
  deriving DecidableEq, Repr

/-- `_unwrapEntries`. (`Operation(uint8(..))` panics outside the enum.) -/
def unwrapLoop (data : Bytes) : Nat → Nat → Option (List Unwrapped)
  | 0, _ => some []
  | n + 1, offset =>
    match rd1 data offset, rd20 data (offset + 1), rd32 data (offset + 21),
        rd32 data (offset + 53) with
    | some op, some to, some value, some size =>
      if op > 1 then none
      else (unwrapLoop data n (offset + 85 + size)).map (⟨op, to, value, offset + 85, size⟩ :: ·)
    | _, _, _, _ => none

/-- `MultiSendUnwrapper.unwrap(to, value, data, operation)` (`op = 1`:
    `DelegateCall`). -/
def unwrap (data : Bytes) (value op : Nat) : Option (List Unwrapped) :=
  if value ≠ 0 ∨ op ≠ 1 then none
  else
    match validateHeader data with
    | none => none
    | some () =>
      match validateLoop data (68 + load data 36) (data.length + 1) 68 0 with
      | none => none
      | some count => unwrapLoop data count 68

/-- The transaction Roles checks for an unwrapped entry: its fields, and
    the calldata slice `data[loc : loc + size]`. -/
def Unwrapped.view (data : Bytes) (u : Unwrapped) : Entry :=
  ⟨u.op, u.to, u.value, (data.drop u.loc).take u.size⟩

/-! ## `MultiSend.multiSend` -/

/-- `mload(add(transactions, x))`: `mem` is memory from the `transactions`
    pointer on (the length word, the bytes, then whatever follows). -/
def mload (mem : Bytes) (x : Nat) : Nat := wordVal ((mem.drop x ++ zeros 32).take 32)

/-- The assembly loop of `multiSend`: the transactions it executes, in
    order (`none`: it reverts on an operation other than `0` / `1`; a
    failing call reverts the whole batch too, which only removes
    executions). `length` is `mload(transactions)`. -/
def execLoop (mem : Bytes) (length : Nat) : Nat → Nat → Option (List Entry)
  | 0, _ => none
  | f + 1, i =>
    if ¬ i < length then some []
    else
      let operation := mload mem i / 2 ^ 248
      let to := mload mem (i + 1) / 2 ^ 96
      let value := mload mem (i + 21)
      let dataLength := mload mem (i + 53)
      if operation = 0 ∨ operation = 1 then
        -- the call reads `data` from memory
        let d := (mem.drop (i + 85) ++ zeros dataLength).take dataLength
        (execLoop mem length f ((i + (85 + dataLength)) % 2 ^ 256)).map
          (⟨operation, to, value, d⟩ :: ·)
      else none

end MultiSend
