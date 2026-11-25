# Condition tree integrity

The rules a condition tree must satisfy to be stored. A tree is valid iff it
satisfies every rule below.

The input is the flat array `ConditionFlat[]` as passed to the setters, before
the packer rewrites any `compValue`. Each node has a `parent` index, an
encoding (`paramType`), an operator and a `compValue`.

The packer rewrites two kinds of `compValue`. An AbiEncoded node without one
gets `0x0004`. An EqualTo on a node that is not inlined (L5) loses its first
32 bytes.

Each rule names the error the contract reverts with when a tree breaks that
rule and no other. `i` is the index of the node the error reports. A tree that
breaks several rules, or one rule at several nodes, is rejected with the error
of one of them. Which one is not specified.

## Terms

- **Word encoding:** Static or EtherValue.
- **Container:** a node with encoding Tuple, Array or AbiEncoded.
- **Logical node:** an And or an Or.
- **Zip:** a ZipSome or a ZipEvery.
- **Navigating operator:** And, Or, Matches, ArraySome, ArrayEvery,
  ArrayTailMatches, Slice, ZipSome, ZipEvery. These evaluate their children.
  Every other operator never evaluates its children.

## 1. Layout

- **L1. Node count.** The array has 1 to 65,535 nodes.
  Empty: `UnsuitableRootNode`. Too many: `ConditionNodeCountExceedsMax`.
- **L2. Parents.** Node 0 is the root and has parent 0. For every `i > 0`,
  the parent is less than `i` and not less than the parent of node `i - 1`.
  So the array is in breadth-first order and the children of a node are
  contiguous.
  Root with another parent, or a later node that is its own parent:
  `UnsuitableRootNode`. Otherwise: `NotBFS`.
- **L3. Codes.** The encoding is 0 to 6: None, Static, Dynamic, Tuple, Array,
  AbiEncoded, EtherValue (`UnsuitableParameterType(i)`). The operator is 0 to
  31 (`UnsupportedOperator(i)`). Codes without an operator are rejected by
  O19.
- **L4. Field widths.** A `compValue` has at most 65,535 bytes
  (`UnsuitableCompValue(i)`). A node has at most 1,023 children
  (`ConditionChildCountExceedsMax(i)`).
- **L5. Inlined size.** A node is _inlined_ unless its encoding is Dynamic,
  Array or AbiEncoded, or one of its children is not inlined. A Zip is not
  inlined and is ignored by its parent. The size of an inlined node is:
  - Static: 32
  - None: the size of its first child that has a size above 0, or 0
  - Tuple, EtherValue: the sum of its children's sizes

  The size of an inlined node is at most 8,191
  (`ConditionInlinedSizeExceedsMax(i)`).

## 2. Operators

Lengths are `compValue` lengths in bytes. Integers in a `compValue` are
unsigned and big-endian. Unless a row says otherwise, a wrong encoding is
`UnsuitableParameterType(i)` and a wrong `compValue` is
`UnsuitableCompValue(i)`.

| Rule    | Operator (code)                                                                    | Encoding                                     | compValue                                    | Children       |
| ------- | ---------------------------------------------------------------------------------- | -------------------------------------------- | -------------------------------------------- | -------------- |
| **O1**  | Pass (0)                                                                           | any                                          | empty                                        | see O18 and T2 |
| **O2**  | And (1), Or (2)                                                                    | None                                         | empty                                        | at least one   |
| **O3**  | Empty (4)                                                                          | None                                         | empty                                        | none           |
| **O4**  | Matches (5)                                                                        | Tuple, Array, AbiEncoded                     | see below                                    | see T2         |
| **O5**  | ArraySome (6), ArrayEvery (7)                                                      | Array                                        | empty                                        | exactly one    |
| **O6**  | ArrayTailMatches (8)                                                               | Array                                        | empty                                        | see T2         |
| **O7**  | ZipSome (10), ZipEvery (11)                                                        | None                                         | see below                                    | see below      |
| **O8**  | Pluck (14)                                                                         | Static, EtherValue, Array                    | 1 byte, the slot, 0 to 254                   | see O18 and T2 |
| **O9**  | Slice (13)                                                                         | Static, Dynamic                              | see below                                    | see below      |
| **O10** | EqualToAvatar (15)                                                                 | Static                                       | empty                                        | none (O18)     |
| **O11** | EqualTo (16)                                                                       | Static, Dynamic, Tuple, Array, EtherValue    | see below                                    | see O18 and T2 |
| **O12** | GreaterThan (17), LessThan (18), SignedIntGreaterThan (19), SignedIntLessThan (20) | Static, EtherValue                           | 32 bytes                                     | none (O18)     |
| **O13** | Bitmask (21)                                                                       | Static, Dynamic                              | at least 4 bytes, even length                | none (O18)     |
| **O14** | Custom (22)                                                                        | Static, Dynamic, Tuple, Array, EtherValue    | at least 20 bytes                            | see O18 and T2 |
| **O15** | WithinRatio (23)                                                                   | None                                         | see below                                    | none           |
| **O16** | WithinAllowance (28)                                                               | Static, EtherValue                           | see below                                    | none (O18)     |
| **O17** | CallWithinAllowance (30)                                                           | None                                         | 32 bytes                                     | none           |

Wrong child count in O2 and O5: `UnsuitableChildCount(i)`. A child where a row
says "none": `LeafNodeCannotHaveChildren(i)`.

- **O4. Matches.** On Tuple and Array the `compValue` is empty. On AbiEncoded
  it is one of:
  - empty
  - 2 bytes, a count `N` of any value
  - 2 bytes holding `N`, then exactly `N` bytes, with `N` from 1 to 32
- **O7. Zip.**
  - The `compValue` has at least 1 byte, one slot per byte.
  - It has exactly one child (`UnsuitableChildCount(i)`).
  - The child has encoding Tuple (`UnsuitableChildTypeTree(i)`).
  - The child has as many children as the `compValue` has bytes
    (`UnsuitableCompValue(i)`).
  - The child's operator is Matches (`UnsupportedOperator(child)`).
  - Each slot is written by a Pluck with encoding Array
    (`UnsuitableCompValue(i)`). A slot may appear more than once.
- **O9. Slice.**
  - The `compValue` has 3 bytes: 2 of shift, 1 of size. The size is 1 to 32.
  - It has exactly one child (`UnsuitableChildCount(i)`).
  - The child has encoding Static, no children, and an operator that does
    not navigate (`SliceChildNotStatic(i)`).
- **O11. EqualTo.**
  - Word encoding: 32 bytes.
  - An inlined node (a Tuple, by L5): exactly its inlined size.
  - Otherwise (Dynamic, Array, a Tuple that is not inlined): at least 64
    bytes. The first 32 are the offset word of `abi.encode(value)`. The
    packer drops them, and their content is not checked.
- **O15. WithinRatio.**
  - At least 12 bytes: reference slot, reference decimals, relative slot,
    relative decimals (1 byte each), minimum ratio, maximum ratio (4 bytes
    each).
  - Then at most two adapter blobs. A blob is a length byte `n`, then `n`
    bytes, where `n` is 0 or at least 20. Nothing follows the blobs.
  - Both decimals are at most 27 (`AllowanceDecimalsExceedMax(i)`).
  - If a Pluck writes the reference slot or the relative slot, that Pluck
    has a word encoding (`WithinRatioTargetNotStatic(i)`).
  - The two ratios are not both 0 (`WithinRatioNoRatioProvided(i)`).
  - If both are above 0, the minimum is not above the maximum
    (`WithinRatioMinExceedsMax(i)`).
- **O16. WithinAllowance.** 32 bytes (the key), or 34 (key and two decimals
  bytes), or at least 54 (key, decimals, adapter address, adapter
  parameters). When present, both decimals are at most 27
  (`AllowanceDecimalsExceedMax(i)`).
- **O18. Leaves.** These nodes have no children
  (`LeafNodeCannotHaveChildren(i)`):
  - encoding Static, Dynamic or EtherValue, with any operator but Slice
  - encoding None or AbiEncoded, with operator Pass
- **O19. Unassigned codes.** Operators 3, 9, 12, 24 to 27, 29 and 31 are
  rejected (`UnsupportedOperator(i)`).

## 3. Types

- **T1. Kind.** Every node has one kind:
  - _No type_: the encoding is None or EtherValue, and the node is not
    logical (including a Zip). Such a node reads no calldata where it sits.
  - _Word_: the encoding is Static.
  - _Bytes_: the encoding is Dynamic.
  - _Tuple_, _array_ or _call_: a container (T2).
  - A logical node takes its kind from its children (T4).

  The encoding decides first: a logical node whose encoding is Static,
  Dynamic, Tuple, Array or AbiEncoded has the kind of that encoding.
- **T2. Containers.**
  - A Tuple or Array has at least one child (`UnsuitableChildCount(i)`). An
    AbiEncoded node may have none.
  - An Array whose operator does not navigate has exactly one child
    (`UnsuitableChildCount(i)`).
  - No child of a container has kind _no type_ (`UnsuitableChildCount(i)`).
  - A container whose operator does not navigate has only _exact_ children
    (`UnsuitableChildTypeTree(i)`). A node is exact if its operator is Pass
    and all its children are exact.
  - A tuple type lists the types of its children in order. It is _open_ if
    the operator is Matches and _closed_ otherwise.
  - A call type (AbiEncoded) is interchangeable with bytes.
- **T3. Arrays.** The element type of an Array is the type of its first
  child. It fits (T5) the type of every other child
  (`UnsuitableChildTypeTree(i)`).
- **T4. Logical nodes.**
  - If no child has a type, the node has _no type_.
  - Otherwise the node's type is the first child type that fits (T5) the
    type of every other typed child. If there is none:
    `UnsuitableChildTypeTree(i)`.
- **T5. Fit.** Type A fits type B in these cases only:
  - Both are words.
  - Each is bytes or a call.
  - Both are arrays and A's element type fits B's.
  - Both are tuples, B is closed, A is closed, they have the same number of
    fields, and each field of A fits the field of B at its position.
  - Both are tuples, B is open and static, they have the same number of
    fields, and: if A is closed, each field of A fits B's; if A is open,
    each field of A is the same as B's.
  - Both are tuples, B is open and not static, A has at least as many fields
    as B, and each of A's first fields fits the field of B at its position.

  A type is _static_ if it is a word or a tuple whose fields are all static.
  Two types are _the same_ if both are words, or both are tuples that are
  both open or both closed, with the same number of fields, each the same as
  its counterpart.
- **T6. Root.** The root is one of (`UnsuitableRootNode`):
  - an AbiEncoded node
  - a node with _no type_
  - a logical node whose children are each a valid logical root by this
    rule, an AbiEncoded node, or a node with _no type_
- **T7. Zip fields.** For each slot of a Zip, in order: the type of the child
  of the Pluck that writes the slot fits (T5) the type of the Zip field at
  that position (`UnsuitableChildTypeTree(i)`).

## 4. Pluck slots

- **P1. One writer.** At most one Pluck in the tree names a given slot
  (`DuplicatePluckIndex(i, slot)`, at the later Pluck).

The remaining rules walk the tree from the root with a set `A` of slots that
are known to be written, starting empty. Each node receives a set and returns
one.

- **P2. Writes.** A Pluck returns `A` plus its slot.
- **P3. Reads.** A read of a slot that is not in the set received is
  rejected (`PluckNotVisitedBeforeRef(i, slot)`).
  - WithinRatio reads its reference slot and its relative slot, and returns
    `A`.
  - A Zip reads every slot in its `compValue`.
- **P4. Flow.**
  - And, Matches, ArrayTailMatches: each child receives what the previous
    child returned. The node returns what the last child returned, or `A` if
    it has none.
  - Or: every child receives `A`. The node returns the slots that every
    child returned.
  - ArraySome: returns what its child returns.
  - ArrayEvery: its child is checked from `A`. The node returns `A`.
  - Zip: its fields (the children of its Tuple child) are checked in
    sequence from `A`. ZipSome returns what its last field returns. ZipEvery
    returns `A`.
  - Slice: returns what its child returns.
- **P5. Everything else.** Any other node returns `A`.
