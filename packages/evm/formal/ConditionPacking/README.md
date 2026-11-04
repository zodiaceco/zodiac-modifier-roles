# Condition packing

Machine-checked proof that `ConditionPacker.pack` followed by
`ConditionUnpacker.unpack` returns the condition tree it was given, for every
`Packable` flat condition array (the width, order and compValue checks we read
Integrity as enforcing; that Integrity implies `Packable` is not proven). The
proof works on
the byte buffer and on a byte-level model of EVM memory, including the assembly
in both libraries.

The formulas are in the [overview](../README.md#condition-packing). This page
has the details.

```
cd packages/evm/formal
lake build ConditionPacking
```

## What is proven

`Main.lean`, `pack_roundtrip`: for every `fs : List Flat` (the `ConditionFlat[]`
argument) with `Packable fs`, every `avatar` word, and arbitrary memory `junk`
(around the buffer while packing) and `junk'` (after the buffer while
unpacking):

```lean
unpack avatar (bufMem (pack junk fs) junk') =
  some (annotate (rawTree avatar fs 0), maxPluck fs)
```

- `rawTree avatar fs 0` is the tree the parent pointers describe, rooted at
  node 0. Children are the later nodes whose `parent` is the node, in array
  order. Each node keeps its `paramType` and `operator`. Its compValue is the
  one `_transform` produces: `AbiEncoded` without a compValue gets `0x0004`, and
  `EqualTo` on a non-inlined node drops its first word. `AbiEncoded` then splits
  off its first two bytes as `leadingBytes`, and `EqualToAvatar` compares
  against `abi.encode(avatar)`.
- `annotate` adds the metadata the evaluator reads: `inlined` and `size`
  (`Topology.isInlined` / `inlinedSize`), and `EtherValue` read as `None`. It is
  the same function the decoder proof assumes
  (`DecoderFaithfulness/Roles.lean`), so the decoder theorems apply to the tree
  `unpack` returns.
- `maxPluck fs` is one more than the largest Pluck index, or 0.

On the way, `Pack.lean`, `packBuffer_eq` pins down the buffer format: after
`_transform`, the packer writes exactly

```
header (3 bytes: nodeCount, maxPluckValue)
++ one 4-byte word per node (encoding, operator, childCount, inlinedSize, hasCompValue)
++ for each node with a compValue: its length (2 bytes) ++ the compValue
```

(`packSpec`). This is the format a client must produce for the `...Packed`
setters.

## Hypotheses: `Packable`, and where Integrity checks them

| `Packable` field                                          | Why packing needs it                                             | Integrity check                                                                                      |
| --------------------------------------------------------- | ---------------------------------------------------------------- | ---------------------------------------------------------------------------------------------------- |
| `nonempty`, `bfs`: parents earlier, never decreasing      | `childBounds` and the unpacker's child pointer assume BFS order  | `_validateBFS` (`UnsuitableRootNode`, `NotBFS`)                                                      |
| `node_count ≤ 65535`                                      | 16-bit node count in the header                                  | `ConditionNodeCountExceedsMax`                                                                       |
| `comp_value_length ≤ 65535`                               | 16-bit length prefix                                             | `_validatePackedWidths` (`UnsuitableCompValue`)                                                      |
| `child_count ≤ 1023`                                      | 10-bit field                                                     | `ConditionChildCountExceedsMax`                                                                      |
| `inlined_size ≤ 8191`                                     | 13-bit field                                                     | `ConditionInlinedSizeExceedsMax`                                                                     |
| `pluck`: compValue non-empty, index ≤ 254                 | `compValue[0]` in `_count`; 8-bit `maxPluckValue` in the header  | `_checkPluck` (exactly 1 byte, not 255)                                                              |
| `equal_to`: non-inlined `EqualTo` has ≥ 32 bytes          | `_transform` drops 32 bytes in assembly (no underflow check)     | `_checkEqualTo` (`Dynamic` and non-inlined `Tuple`/`Array` ≥ 64 bytes; `None`/`AbiEncoded` rejected) |
| `abi_encoded`: compValue length ≠ 1, operator ≠ `EqualTo` | the unpacker reads 2 bytes of leading bytes from every compValue | `_checkPass` (empty), `_checkMatches` (0, 2 or 2 + n bytes), other operators reject `AbiEncoded`     |

The table's last column is from reading `Integrity.sol`; "Integrity ⇒
`Packable`" is not proven in Lean. Outside these hypotheses the buffer is
corrupt. For example, a 1-byte `AbiEncoded` compValue makes the unpacker's
`sub(length, 2)` wrap, and an inlined size of 8192 overflows into the child
count bits. The `...Packed` setters store a buffer without any check (and
`MalformedConditionBuffer` is never raised), so a client that builds buffers
itself must enforce `Packable` itself.

## Model

`Model.lean` transcribes `Topology.sol`, `ConditionPacker.sol` and
`ConditionUnpacker.sol`:

- **Memory** is a function from positions to bytes (`Mem`). `mload`, `mstore`,
  `mcopy`, `shl`, `shr` and `or` have the EVM's 256-bit word semantics. The
  packer's `mstore(dest, or(mload(dest), shl(224, packed)))` and its 32-byte
  stores for 2-byte lengths are transcribed as written. The proof shows that
  their spill into neighbouring fields and past the buffer is harmless.
- **Allocation:** `new bytes(len)` gives a zeroed buffer. All memory outside the
  buffer is arbitrary (`junk`), also while unpacking, where `mload` reads up to
  32 bytes past the last field.
- **Topology** reads only `parent` and `paramType` (`Shape`). `_transform`
  mutates compValues while calling `isInlined`, which therefore can't change the
  result.
- **Unpacked structs:** the unpacker builds `Condition` structs whose `children`
  are pointers into one `Condition[]` array. The model records the child indices
  (`URec`) and `toTree` follows them. Pointers and the free memory pointer are
  not modeled.
- **Deviations,** all outside `Packable`: arithmetic is on `Nat`. `compValue[0]`
  of an empty Pluck compValue (a panic) and the `EqualTo` underflow read
  defaults. Placeholder operator codes have no constructor and decode to `none`.

## Proof structure

| File            | Contents                                                                                                               |
| --------------- | ---------------------------------------------------------------------------------------------------------------------- |
| `Model.lean`    | The transcription, `rawTree`, `maxPluck`, `Packable`                                                                   |
| `Bytes.lean`    | Big-endian bytes, memory reads/writes, `shr(mload)`, `mstore(shl)` and the `or(mload, shl)` node write                 |
| `Bfs.lean`      | BFS order: the children of node `i` are the block `[1 + cnt i, 1 + cnt (i+1))`; `childBounds` finds exactly that block |
| `Topology.lean` | On BFS input, `Topology.isInlined` / `inlinedSize` on the flat array equal the tree versions the decoder proof uses    |
| `Pack.lean`     | `packBuffer_eq`: the packer's memory equals `packSpec` (loop invariant over the node loop)                             |
| `Unpack.lean`   | Reading `packSpec`: each iteration of `_unpackConditions` decodes node `c` to the expected struct (`unpackStep_eq`)    |
| `Main.lean`     | The unpacker loop, rebuilding the tree (`toTree_eq`), `maxPluckValue`, and `pack_roundtrip`                            |

## Tests

`test/formal/lean-model.spec.ts` ("packs and unpacks like ...") checks the
transcription against the contracts. For random condition trees with random
compValues of every shape Integrity accepts, it requires:

- the model's `pack` to produce byte-identical buffers to `ConditionPacker.pack`
  (via `MockPackerUnpacker.pack`);
- the model's `unpack` of the contract's buffer to give the same tree as
  `ConditionUnpacker.unpack` (via `MockPackerUnpacker.roundtrip`).

Driver: `lake build roles-model`, queries `pk` and `up` (see `Diff.lean`).

`NonVacuity.lean` (built with the library) shows `Packable` holds on
non-trivial arrays (several levels, a non-inlined `EqualTo`, Plucks, a Zip)
and that `rawTree` is the expected tree for them.

## Trusted base

- `Model.lean` matches the Solidity: a hand transcription, tested as above.
- The EVM semantics of the memory instructions used, as written in `Model.lean`.
- `ImmutableStorage` returns the bytes it stored (the buffer is written with
  `store` and read back with `extcodecopy` between pack and unpack).
- The Lean 4.35 kernel.
