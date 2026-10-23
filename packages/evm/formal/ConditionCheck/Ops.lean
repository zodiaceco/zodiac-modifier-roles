import ConditionCheck.Flat

/-!
# Operator rules

`opsOk fs` transcribes the per-node rules of `Integrity.sol`
(`_validateOperator`, `_validateEncoding`, `_validateUniquePluckDefinitions`)
on the flat array: which encodings each operator takes, compValue lengths and
fields, child counts. Rules about structural children and type trees
(`_sChildBounds`, `TypeTree`, `_validateVariantTypes`,
`_validatePluckZipTypes`) are left to `classify` and `zipCheck`, which decide
them differently on purpose (see the README).

These rules are not about where `evaluate` reads, so nothing about them is
proven here. They keep the check at least as strict as Integrity on operator
arguments; `test/formal/integrity-gaps.spec.ts` (`GAP_CHECK=1`) compares.
-/

namespace ConditionCheck
open DecoderFaithfulness DecoderFaithfulness.Roles
open ConditionPacking (Flat at! shapes childBounds kids)

def cvAt (cv : Bytes) (k : Nat) : Nat := (cv.getD k 0).val

/-- `_findPluck`: the first Pluck node with slot `k`. -/
def findPluck (fs : List Flat) (k : Nat) : Option Nat :=
  (List.range fs.length).find? fun i =>
    (at! fs i).operator == .Pluck && cvAt (at! fs i).compValue 0 == k

/-- `a` is `j` or an ancestor of `j` (parents come first, so `fuel = j`
    suffices). -/
def isUnder (fs : List Flat) (a : Nat) : (fuel j : Nat) → Bool
  | 0, j => j == a
  | fuel + 1, j => j == a || (j != 0 && isUnder fs a fuel (at! fs j).parent)

/-- `_checkAdapterBlob`: the offset after the blob, or `none`. -/
def adapterBlob (cv : Bytes) (off : Nat) : Option Nat :=
  let len := cvAt cv off
  if len != 0 && len < 20 then none
  else if off + 1 + len > cv.length then none
  else some (off + 1 + len)

def withinRatioCvOk (cv : Bytes) : Bool :=
  let len := cv.length
  let blobs : Option Nat :=
    (if len > 12 then adapterBlob cv 12 else some 12).bind fun o =>
      if len > o then adapterBlob cv o else some o
  12 ≤ len && len ≤ 65535 && blobs == some len &&
    cvAt cv 1 ≤ 27 && cvAt cv 3 ≤ 27 &&
    (let minR := wordVal ((cv.drop 4).take 4)
     let maxR := wordVal ((cv.drop 8).take 4)
     !(minR == 0 && maxR == 0) && (minR == 0 || maxR == 0 || minR ≤ maxR))

/-- The rules of one node. -/
def opOk (fs : List Flat) (j : Nat) : Bool :=
  let f := at! fs j
  let e := f.paramType
  let cv := f.compValue
  let len := cv.length
  let cc := (childBounds (shapes fs) j).2
  let ch0 := (kids fs j).headD 0
  -- `_validateEncoding`: leaves have no children (except `Slice`)
  let leafRule := !((e == .Static || e == .Dynamic || e == .EtherValue) && f.operator != .Slice) ||
    cc == 0
  let pluckEnc (k : Nat) (ok : Encoding → Bool) : Bool :=
    match findPluck fs k with
    | some i => ok (at! fs i).paramType
    | none => true
  leafRule &&
  match f.operator with
  | .Pass => len == 0
  | .And | .Or => e == .None && len == 0 && cc ≥ 1
  | .Empty => e == .None && len == 0 && cc == 0
  | .Matches =>
    (e == .Tuple || e == .Array || e == .AbiEncoded) &&
      (if e == .AbiEncoded then
        len == 0 || len == 2 ||
          (len == 2 + (cvAt cv 0 * 256 + cvAt cv 1) && cvAt cv 0 * 256 + cvAt cv 1 ≤ 32)
      else len == 0)
  | .ArraySome | .ArrayEvery => e == .Array && len == 0 && cc == 1
  | .ArrayTailMatches => e == .Array && len == 0
  | .ZipSome | .ZipEvery =>
    e == .None && len ≥ 2 && cc == 1 && (at! fs ch0).paramType == .Tuple &&
      (childBounds (shapes fs) ch0).2 == len &&
      -- distinct slots, each with an Array Pluck
      (List.range len).all (fun a => (List.range len).all fun b =>
        a == b || cvAt cv a != cvAt cv b) &&
      (List.range len).all (fun k =>
        match findPluck fs (cvAt cv k) with
        | some i => (at! fs i).paramType == .Array
        | none => false) &&
      -- no Pluck below the Zip
      (List.range fs.length).all fun i =>
        (at! fs i).operator != .Pluck || !isUnder fs ch0 i i
  | .Slice =>
    (e == .Static || e == .Dynamic) && len == 3 && 1 ≤ cvAt cv 2 && cvAt cv 2 ≤ 32 &&
      cc == 1 && (at! fs ch0).paramType == .Static
  | .Pluck => (e == .Static || e == .EtherValue || e == .Array) && len == 1 && cvAt cv 0 != 255
  | .EqualToAvatar => e == .Static && len == 0
  | .EqualTo =>
    match e with
    | .Static | .EtherValue => len == 32
    | .Dynamic => 64 ≤ len && len ≤ 65535
    | .Tuple | .Array =>
      (if ConditionPacking.isInlined (shapes fs) j then 32 else 64) ≤ len && len ≤ 65535
    | _ => false
  | .GreaterThan | .LessThan | .SignedIntGreaterThan | .SignedIntLessThan =>
    (e == .Static || e == .EtherValue) && len == 32
  | .Bitmask => (e == .Static || e == .Dynamic) && 4 ≤ len && len ≤ 65535 && len % 2 == 0
  | .Custom =>
    (e == .Static || e == .Dynamic || e == .Tuple || e == .Array || e == .EtherValue) &&
      20 ≤ len && len ≤ 65535
  | .WithinRatio =>
    e == .None && withinRatioCvOk cv && cc == 0 &&
      pluckEnc (cvAt cv 0) (fun e' => e' == .Static || e' == .EtherValue) &&
      pluckEnc (cvAt cv 2) (fun e' => e' == .Static || e' == .EtherValue)
  | .WithinAllowance =>
    (e == .Static || e == .EtherValue) && len ≤ 65535 && (len == 32 || len == 34 || 54 ≤ len) &&
      (len ≤ 32 || (cvAt cv 32 ≤ 27 && cvAt cv 33 ≤ 27))
  | .CallWithinAllowance => e == .None && len == 32 && cc == 0

/-- Every node's rules, and no two Pluck nodes share a slot. -/
def opsOk (fs : List Flat) : Bool :=
  (List.range fs.length).all (opOk fs) &&
    (List.range fs.length).all fun i => (List.range fs.length).all fun i' =>
      i' ≤ i || (at! fs i).operator != .Pluck || (at! fs i').operator != .Pluck ||
        cvAt (at! fs i).compValue 0 != cvAt (at! fs i').compValue 0

end ConditionCheck
