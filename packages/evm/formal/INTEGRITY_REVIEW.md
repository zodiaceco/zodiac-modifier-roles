# Trees the SDK check accepts and Integrity rejects

The SDK stores conditions with the `...Packed` setters, which skip
`Integrity.enforce`. Its gate is `checkStored`
(`packages/sdk/src/main/condition/checkStored.ts`, a transcription of the Lean
`ConditionCheck.checkStored`). It keeps Integrity's per-operator rules,
compValue formats, Pluck rules (`_validatePluckAssignments`, unique slots, ≥ 2
arrays per Zip) and packing limits. It differs only in how types are compared.

Integrity compares the `TypeTree` hashes of siblings (`_validateVariantTypes`,
`_validatePluckZipTypes`). A mismatch passes `_isTypeCompatible` only if both
sides are `Dynamic`, `AbiEncoded` or `None` at the level compared. The SDK
check instead asks, per node, that the tree describe the ABI value where each
node is read. Below are the four classes where that is looser, each with an
example that Integrity rejects with `UnsuitableChildTypeTree`.

In a 3,000-tree fuzz run, 148 trees fell into these classes. Another 89 made
`Integrity.enforce` run out of gas at 16M.

**Why looser is safe, in general.** Lean proves that for every array
`checkStored` accepts:

- packing and unpacking returns the tree;
- `evaluate` reads every node it reaches at that parameter's ABI location;
- no node reads an unwritten Pluck slot.

These are `checkStored_sound` in `ConditionCheck/` and the decoder theorems in
`DecoderFaithfulness/`. On chain, the fuzzer evaluates accepted trees through
the packed path against the Lean evaluator model (`GAP_PACKED=1`), with 0
differences. The examples below run on the Roles contract in
`test/formal/integrity-review.spec.ts`. Each is rejected by `allowFunction`,
stored with `allowFunctionPacked`, and allows and denies exactly the
intended calls.

## 1. Checks of a prefix of one tuple, side by side

`fn((bytes, uint256, uint256) x)`, allow if `x.b == 1 || x.c == 2`:

```
Matches:AbiEncoded[
  Or[ Matches:Tuple[Pass:Dynamic, EqualTo(1)],
      Matches:Tuple[Pass:Dynamic, Pass:Static, EqualTo(2)] ] ]
```

Each branch lists only the fields it checks. The SDK stores it as written:
it no longer pads branches to one full type.

**Integrity:** the two tuples have 2 and 3 type children, so their hashes
differ, and neither is `Dynamic`-ish.

**Safe:** a `Matches` on a tuple that is not inlined reads its fields through
the tuple's head. Field *i*'s location doesn't depend on how many later fields
the condition lists. A prefix may only describe a non-inlined tuple or
calldata (a shorter inlined tuple would move what follows it). The `Or`'s
type is its most specific child, and every child must be a prefix of it.

## 2. A `Slice` and a plain check of the same type

`fn(uint256[] a)`, allow if every element ends in byte `0x01` and some element is > 1000:

```
Matches:AbiEncoded[
  And[ ArrayEvery:Array[Slice:Static(shift 31, size 1)[EqualTo(1)]],
       ArraySome:Array[GreaterThan(1000)] ] ]
```

**Integrity:** `TypeTree.resolve` counts the `Slice`'s window child as a type
child, so `Static[Static]` and `Static` hash differently. This happens wherever
types are compared: in an `And`/`Or` (backlog item 4), inside compared
arrays/tuples as here, and between a Zip field and its plucked array's
elements.

**Safe:** a `Slice` on `Static` is read, sized and inlined like any static word
(32 bytes), and on `Dynamic` like any `bytes`. The window child only selects
bytes inside that value. The check types a `Slice` node by its own encoding and
requires its child to be a static window of 1–32 bytes.

## 3. `bytes` read as nested calldata by one check and as bytes by another

`fn(bytes[] calls)`, allow if every element is `transfer(_, amount < 100)` and
one element is exactly `transfer(0xaaaa, 5)`:

```
Matches:AbiEncoded[
  And[ ArrayEvery:Array[Matches:AbiEncoded(0x0004 a9059cbb)[Pass:Static, LessThan(100)]],
       ArraySome:Array[EqualTo:Dynamic(abi.encode(bytes))] ] ]
```

**Integrity:** `_isTypeCompatible` accepts `Dynamic` vs `AbiEncoded` siblings,
but only at the top of the comparison. Here they are the element types of two
arrays, so the array hashes differ and the arrays themselves are not
`Dynamic`-ish.

**Safe:** nested calldata is a `bytes` value in the parent's encoding.
`AbiLocation.size` treats `Dynamic` and `AbiEncoded` alike, and neither is
inlined. So both arrays decode the same element locations, and each check
reads its own interpretation at the element's location. The check types
bytes-like interpretations of one value as one `bytes` type.

## 4. A Zip next to a tuple check

`fn((uint256[] a, uint256[] b, string s) x)`, allow if `x.b[i] == 7` for every `i` (zipped with `x.a`):

```
Matches:AbiEncoded[
  And[ Matches:Tuple[Pluck(0):Array[Static], Pluck(1):Array[Static], Pass:Dynamic],
       ZipEvery(slots 0, 1)[Matches:Tuple[Pass:Static, EqualTo(7)]] ] ]
```

**Integrity:** the Zip node resolves to `None[Tuple[…]]`, a typed sibling of
the `Tuple` with a different hash. `None` is `Dynamic`-ish, but `Tuple` is not.
Only the root form `And[Matches:AbiEncoded[…], Zip]` gets through (backlog
item 10).

**Safe:** a Zip reads no field of the value it sits at. It decodes the arrays at
the locations its Pluck slots hold, with its fields' layout. Two things could
go wrong next to a typed sibling, and the check excludes both:

- **Zip first:** the logical node would take the Zip's size. The check
  requires the first typed child to come before any Zip.
- **Static value:** the logical node would be inlined with a size that
  includes the Zip's. The check rejects a Zip in an `And`/`Or` of static
  type.

Integrity's Zip rules still apply: slots written before the Zip, and field
types compatible with the plucked elements.

## Where Integrity accepts and the SDK check rejects

For completeness, the other direction (about 230 trees in the same run). It is
rejected because the decoder theorems can't vouch for the tree. In some cases
it is misread, such as a Zip among a call's parameters (`INTEGRITY_BACKLOG.md`
item 1, a policy bypass):

- **Zip placement:** a Zip directly under `Matches`, or first in an `And`.
- **Exact type unknown:** an `And`/`Or` or a tuple `Matches` below a check that
  reads its whole value. A `Matches` may list fewer fields, so its size
  isn't the value's.
- **Non-structural children** (`EtherValue`, `None`) inside a tuple or array
  type description.
