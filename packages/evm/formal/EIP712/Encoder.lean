import DecoderFaithfulness.Roles

/-!
# `EIP712Encoder.sol` — transcription

Transcribed from `packages/evm/contracts/periphery/signing/EIP712Encoder.sol`.
Each definition follows the Solidity control flow. `none` is a revert.

* `bytes calldata data` is the byte view the library reads: `_word` is
  `calldataload`, `data[left:right]` copies calldata. Both read zeros past
  the end of `msg.data`. `SignTypedMessageLib`'s fallback sets the offsets
  and lengths of `domain` / `message` by hand, without checking them against
  `msg.data`, so a view can run past the end of the calldata; that tail
  reads as zeros. `View.lean` builds the view from calldata.
* Arithmetic is on `Nat`. Checked `uint256` arithmetic reverts on overflow;
  here the following bound check fails instead, so the outcome (revert) is
  the same. `new bytes32[](childCount)` with a huge count runs out of gas;
  here the loop fails at the first child that does not fit.
* `keccak256` is a parameter `K`. `abi.encodePacked(typeHash, result)` of
  `bytes32` values is their concatenation.
* `hashField` takes fuel: the recursion depth. `height t` is enough, so the
  fuel never runs out on a tree (`hashField_fuel`); it only makes the
  definition structurally recursive.
-/

namespace EIP712
open DecoderFaithfulness DecoderFaithfulness.Roles

/-- `struct TypeNodeFlat`. -/
structure TNF where
  parent : Nat
  encoding : Encoding
  typeHash : Bytes
  deriving Inhabited, DecidableEq, Repr

/-- `struct TypeNode`. -/
structure TN where
  encoding : Encoding
  children : List TN
  typeHash : Bytes
  deriving Inhabited

mutual
  def TN.height : TN → Nat
    | ⟨_, cs, _⟩ => TN.heightL cs + 1
  def TN.heightL : List TN → Nat
    | [] => 0
    | c :: cs => max (TN.height c) (TN.heightL cs)
end

/-- `_toTree(types, index)`: the nodes after `index` whose `parent` is
    `index`, in order, are its children. `types[index]` out of range panics.
    `fuel`: `types.length + 1` is enough (indices increase along a path). -/
def toTree (types : List TNF) : Nat → Nat → Option TN
  | 0, _ => none
  | fuel + 1, index =>
    match types[index]? with
    | none => none
    | some n =>
      let kids := (List.range types.length).filter fun i =>
        index < i ∧ (types.getD i default).parent = index
      (kids.mapM (toTree types fuel)).map fun cs => ⟨n.encoding, cs, n.typeHash⟩

mutual
  /-- `_inlineSize`: `0` for an offset slot, else the inline size. Reverts
      on an empty tuple or an encoding other than Static / Dynamic / Tuple /
      Array. A tuple returns `0` at its first child of size `0`. -/
  def inlineSize : TN → Option Nat
    | ⟨e, cs, _⟩ =>
      if e = .Dynamic ∨ e = .Array then some 0
      else if e = .Static then some 32
      else if e ≠ .Tuple then none
      else if cs = [] then none
      else inlineSizeL cs 0
  def inlineSizeL : List TN → Nat → Option Nat
    | [], acc => some acc
    | c :: cs, acc =>
      match inlineSize c with
      | none => none
      | some 0 => some 0
      | some k => inlineSizeL cs (acc + k)
end

/-- `_word`: the 32 bytes at `location`; reverts past the end of the view. -/
def wordAt (data : Bytes) (location : Nat) : Option Bytes :=
  if location + 32 > data.length then none else some ((data.drop location).take 32)

/-- `_childLocation(data, blockLocation, headOffset, child)`: the child's
    location and inline size. -/
def childLocation (data : Bytes) (blockLocation headOffset : Nat) (child : TN) :
    Option (Nat × Nat) :=
  match inlineSize child with
  | none => none
  | some isz =>
    let headLocation := blockLocation + headOffset
    if isz > 0 then
      if headLocation + 32 > data.length then none else some (headLocation, isz)
    else if headLocation + 32 > data.length then none
    else
      let tailOffset := load data headLocation
      if tailOffset ≤ headOffset then none
      else
        let childLocation := blockLocation + tailOffset
        if childLocation + 32 > data.length then none else some (childLocation, 0)

/-- The loop of `_hashBlock` for children `i, i+1, …` (`n` left), with the
    child hash function `hf` (`_hashField` one level down). Generic in the
    result so that `Read.lean` can run the same walk to read values. -/
def blockLoop {α : Type} (data : Bytes) (hf : TN → Nat → Option α) (cs : List TN) (isArray : Bool)
    (blockLocation : Nat) : (n i headOffset : Nat) → Option (List α)
  | 0, _, _ => some []
  | n + 1, i, headOffset =>
    let child := cs.getD (if isArray then 0 else i) default
    match childLocation data blockLocation headOffset child with
    | none => none
    | some (loc, isz) =>
      match hf child loc with
      | none => none
      | some r =>
        (blockLoop data hf cs isArray blockLocation n (i + 1)
          (headOffset + if isz > 0 then isz else 32)).map (r :: ·)

/-- `abi.encodePacked(typeHash, result)` or `abi.encodePacked(result)`. -/
def packBlock (K : Bytes → Bytes) (typeHash : Bytes) (rs : List Bytes) : Bytes :=
  K (if typeHash ≠ zeros 32 then typeHash ++ rs.flatten else rs.flatten)

/-- `_hashBlock`. -/
def hashBlock (K : Bytes → Bytes) (data : Bytes) (hf : TN → Nat → Option Bytes) (t : TN)
    (blockLocation childCount : Nat) (isArray : Bool) : Option Bytes :=
  if isArray ∧ t.children.length ≠ 1 then none
  else (blockLoop data hf t.children isArray blockLocation childCount 0 0).map
    (packBlock K t.typeHash)

/-- `_hashField(data, layout, location)`. -/
def hashField (K : Bytes → Bytes) (data : Bytes) : Nat → TN → Nat → Option Bytes
  | 0, _, _ => none
  | fuel + 1, t, location =>
    if t.encoding = .Static then wordAt data location
    else if t.encoding = .Dynamic then
      match wordAt data location with
      | none => none
      | some w =>
        let left := location + 32
        let right := left + wordVal w
        if right > data.length then none else some (K ((data.drop left).take (right - left)))
    else if t.encoding = .Array then
      match wordAt data location with
      | none => none
      | some w => hashBlock K data (hashField K data fuel) t (location + 32) (wordVal w) true
    else if t.encoding = .Tuple then
      hashBlock K data (hashField K data fuel) t location t.children.length false
    else none

/-- `_hashStruct(data, types, index)`. -/
def hashStructE (K : Bytes → Bytes) (data : Bytes) (types : List TNF) (index : Nat) : Option Bytes :=
  match toTree types (types.length + 1) index with
  | none => none
  | some root =>
    if root.encoding ≠ .Tuple ∨ root.typeHash = zeros 32 then none
    else hashField K data root.height root 0

/-- `hashTypedMessage(domain, message, types)`. -/
def hashTypedMessage (K : Bytes → Bytes) (domain message : Bytes) (types : List TNF) :
    Option Bytes :=
  match hashStructE K domain types 0, hashStructE K message types 1 with
  | some ds, some mh => some (K ([0x19, 0x01] ++ ds ++ mh))
  | _, _ => none

end EIP712
