# Condition check

`checkStored s fs` is a decidable check on a flat condition array, with proofs
that every array it accepts is stored, unpacked and evaluated as intended. It
is the specification for the check the SDK runs before storing a tree with a
`...Packed` setter, which skips `Integrity` on-chain. Unlike Integrity, it
rejects the shapes in [INTEGRITY_BACKLOG.md](../../../sdk/INTEGRITY_BACKLOG.md)
that `evaluate` misreads.

The formulas are in the [overview](../README.md#condition-check). This page has
the details.

```
cd packages/evm/formal
lake build ConditionCheck
```

## The check

`checkStored s fs : Option Verdict` (`Stored.lean`) accepts `fs` when all of
these hold. It returns `typed t` (the root describes calldata of type `t`) or
`noCalldata` (the root reads no calldata, e.g. only `EtherValue` checks).

| Part             | File         | What it requires                                                                                          | Proven                                                   |
| ---------------- | ------------ | --------------------------------------------------------------------------------------------------------- | -------------------------------------------------------- |
| `packableB`      | `Flat.lean`  | `Packable`: BFS order, field widths, Pluck index ≤ 254, compValue shapes the packer relies on             | decides `Packable` (`packableB_sound`)                   |
| `opsOk`          | `Ops.lean`   | Integrity's per-operator rules: encodings, compValue lengths and fields, child counts, unique Pluck slots | nothing (a transcription; tested against Integrity)      |
| `assigned`       | `Slots.lean` | `_validatePluckAssignments`: every slot a Zip or `WithinRatio` reads is written first, on every path      | no execution reads an unwritten slot (`assigned_no_bad`) |
| `checkCondition` | `Check.lean` | the tree describes an ABI type (below)                                                                    | the decoder hypotheses (`checkCondition_sound`)          |
| or `ns` root     | `Check.lean` | the root is non-structural                                                                                | only the ether value is read (`ns_root_input`)           |

The tree checks run on `rawTree (zeros 32) fs 0`, the tree the array
describes. Its `EqualToAvatar` compValues hold the avatar, which can change
after storing; `checkCondition_avatar` and `assigned_avatar` show the result
does not depend on it.

### The type check (`checkCondition`)

`checkCondition s root : Option Ty` returns the ABI type the tree describes, or
`none`. `Ty` is `static`, `dynamic`, `tuple ts`, `array t` or `call lb ts`
(nested calldata with `lb` leading bytes). Every node is classified bottom-up
as structural with a type, non-structural (`ns`), or a Zip:

| Node                                       | Accepted when                                                                                                                                                                 | Kind               |
| ------------------------------------------ | ----------------------------------------------------------------------------------------------------------------------------------------------------------------------------- | ------------------ |
| `Static` / `Dynamic` leaf                  | no children, operator not `And`/`Or`/`Matches`/array/`Slice`/`Zip`                                                                                                            | `static`/`dynamic` |
| `Static` / `Dynamic` `Slice`               | one `Static` child of kind `static` (a leaf or another slice), slice size 1–32                                                                                                | `static`/`dynamic` |
| `Tuple`                                    | ≥ 1 child, all structural; operator `Matches` or a non-navigating one (`Pass`, `EqualTo`, ...)                                                                                | `tuple ts`         |
| `Array`                                    | ≥ 1 child, all structural with the same type `t` (or, with `s = true`, all bytes-like: a variant array, typed `array dynamic`); `Matches`, array iterators, or non-navigating | `array t`          |
| `AbiEncoded`                               | ≥ 1 child, all structural; `Matches` or `Pass`                                                                                                                                | `call lb ts`       |
| `None` / `EtherValue` leaf                 | no children, non-navigating operator                                                                                                                                          | `ns`               |
| `None` `ZipSome` / `ZipEvery`              | exactly one child, of kind `tuple _` (the fields)                                                                                                                             | `zip`              |
| `None` `And` / `Or`, all children `ns`     | ≥ 1 child                                                                                                                                                                     | `ns`               |
| `None` `And` / `Or`, some child structural | see below                                                                                                                                                                     | `t`                |

An `And`/`Or` with a structural child:

- only `ns` children come before the first structural child (no Zip before the
  child that describes the value);
- all structural children have the same type `t`, or, with `s = true` only,
  all have bytes-like types (`dynamic` or `call`): a **variant**, typed
  `dynamic`;
- a Zip child is allowed only if `t` is not static.

On the whole tree:

- the root is of kind `ty t`, and `AbiEncoded` or an `And`/`Or` over roots,
  `ns` nodes and Zips (`rootOk`);
- for every Zip `z`, field `f`, and every `Pluck` node whose index equals
  `z`'s slot for `f`: the Pluck node is an `Array`, and its element type fits
  the field's type (`zipCheck`, `tyCompat`): equal, or a `dynamic` field over
  bytes-like elements, or (with `s = true`) any two bytes-like types.

`s` is the strictness flag of the decoder theorems. With `s = false`,
variants are rejected and the theorems give the full guarantee. With
`s = true`, variants are accepted and the theorems allow "an interpretation
that does not fit" (case (iv)).

## What is proven

### `checkStored_sound` (`Stored.lean`)

If `checkStored s fs = some v`, then for every avatar and any memory contents:

1. `Packable fs`, so `unpack (pack fs) = annotate (rawTree avatar fs 0)`
   ([condition packing](../ConditionPacking/README.md)): `evaluate` sees the
   tree that was checked;
2. no execution of that tree reads an unwritten Pluck slot;
3. for `v = typed t`: `RootOK`, `ZipOK s` and `Desc s root (.call pre args)`
   for every calldata of type `t`, so every
   [decoder theorem](../DecoderFaithfulness/README.md) applies; for
   `v = noCalldata`: every node `evaluate` reaches reads only the ether value.

### The type check (`Sound.lean`)

`checkCondition_sound`: if `checkCondition s root = some t`, then

```lean
RootOK root ∧ ZipOK s root ∧
  ∀ pre args, HasT s (.call pre args) t → Strict s (.call pre args) t →
    Desc s root (.call pre args)
```

`HasT s u t` says value `u` has type `t`: a 32-byte word for `static`, any
`bytes` value (plain or nested calldata) for `dynamic`, componentwise for
tuples, elementwise for arrays. For `call lb ts`, the value is nested calldata
with `lb` leading bytes and arguments of types `ts`; with `s = true` any
`bytes` value also counts. `Strict` requires the root itself to parse as its
`call` type.

Two directions, both by recursion on the tree: `desc_of_ty` (a node of type
`t` describes every value of type `t`) and `hasT_of_descS` (a value a node
describes has its type; needed for Zips, whose fields must describe whatever
the Pluck node's elements are).

### Pluck slots (`Slots.lean`)

`Run c A o A'` models `evaluate`'s control flow with respect to slots:
`And`/`Matches`/`ArrayTailMatches` evaluate children in order and stop at the
first failure, `Or` stops at the first success, `ArraySome`/`ArrayEvery` and
Zips iterate over any number of elements, `_pluck` writes its slot, and a Zip
or `WithinRatio` reading an unwritten slot is the outcome `bad`. Leaf results
are arbitrary, so `Run` covers every execution. `run_sound`: if `assigned`
accepts the tree, every `Run` ends in `ok` or `fail`, never `bad`.

The decoder model assumes that a slot a Zip reads holds the location where a
Pluck with that index was evaluated. With this theorem, that assumption reduces
to two facts about the Solidity: `Run` matches the evaluator's control flow, and
`_pluck` is the only writer of `pluckedLocations`. Unique Pluck indices are
**not** needed for it. A slot always holds the location of some evaluated
Pluck with that index, and `ZipOK` constrains every such Pluck.

### Comparison operators (`Compare.lean`)

`comparePasses` transcribes the comparison branch of `evaluate` (`__compare`,
`__compareSigned`) on `__input`'s result. keccak256 is a parameter; the
`EqualTo` theorems assume it has no collisions (`KeyInjective`).

- `equalTo_iff`: an `EqualTo` on a parameter `u` passes exactly when
  `enc(u)` equals the stored compValue.
- `equalTo_intended`: with the compValue the SDK writes, `abi.encode(v)` (the
  packer drops the offset word for dynamic values, `storedCv`), it passes
  exactly when `enc(u) = enc(v)`.
- `compare_word`: `GreaterThan`/`LessThan` compare the 32-byte word as an
  unsigned integer, the signed variants as two's complement (`toInt`).
- `checked_equalTo`: end to end on a stored array the check accepts.

Not covered: `Bitmask` (proven in the decoder proof), `Custom` (an external
contract), `WithinAllowance`/`CallWithinAllowance` (allowance storage),
`WithinRatio` (Pluck values and price adapters).

### Roots that read no calldata (`Flat.lean`)

`ns_root_input`: if the root is non-structural, every node `evaluate`
reaches, including through Zips, reads the ether value.

## Findings: where Integrity and the check differ

Found while transcribing Integrity and by the fuzzer's checker mode
(`GAP_CHECK=1`, with `GAP_MUTATE` probing operator rules). In 2,000+
unmutated and mutated runs, every difference fell into one of these classes.

**Integrity accepts, `evaluate` misreads; the check rejects** (backlog items):

- a Zip anywhere but under `And`/`Or` (item 1, bypass), or before the child
  that describes the value;
- a non-structural child of a `Tuple`/`Array` under `Pass`/`EqualTo` (item 2);
- a root that is not `AbiEncoded`/logical, e.g. a `Dynamic` variant (item 6).

**Integrity accepts, the check rejects, not a misread:**

- a `None`-encoded node with children under `Pass` (Integrity's `Pass` rule
  takes any encoding). `evaluate` treats it like a tuple; a probe through
  `MockEvaluator` read the following parameter correctly. The decoder proof
  doesn't model it, so the check rejects it; the SDK has no reason to produce
  it.

**Integrity rejects, but the tree is read correctly; the check accepts:**

- `Slice` next to plain checks in an `And`/`Or` (item 4,
  `UnsuitableChildTypeTree`).
- A Zip in an `And`/`Or` next to a `Tuple` or `Array` check, e.g.
  `And[Matches:Tuple[...], ZipSome[...]]` on a dynamic tuple (item 10).
  `_validateVariantTypes` counts the Zip as a typed sibling that is only
  compatible with `Dynamic`/`AbiEncoded` ones. Only the root form
  `And[Matches:AbiEncoded[...], Zip]` gets through.

Every "check accepts, Integrity rejects" case in the fuzzer runs is one of
these two.

**Integrity rules the decoder does not need; the check keeps them anyway**
(they are about intent, not safety):

- `DuplicatePluckIndex`: two Pluck nodes with one slot only make the Zip read
  whichever ran last, and `ZipOK` covers both.
- A Zip needs at least two arrays (`compValue.length ≥ 2`); `ArraySome`/
  `ArrayEvery` cover one.

**Notes for the SDK:**

- The `...Packed` setters check nothing, not even what `pack_roundtrip` needs
  (`MalformedConditionBuffer` is never raised). `checkStored` must run.
- `Custom` checkers receive `pluckedValues`, but no rule says which slots
  they read, so a checker may see unwritten (zero) slots. Integrity cannot
  check this either.
- Integrity's `_findPluck` in `WithinRatio` skips missing Plucks; the
  assignment check catches them instead.
- A Pluck with an empty compValue after a Zip makes Integrity revert with a
  `Panic` (array index out of bounds in `_findPluck`, called from
  `_checkZipIterator` before the Pluck's own check) instead of
  `UnsuitableCompValue`. It is still rejected; the fuzzer counts Panics as
  accepted, so such cases show up as "Integrity accepts, check rejects".

## Tests

`test/formal/integrity-gaps.spec.ts` with `GAP_CHECK=1` runs `checkStored`
through the Lean driver's `ck` query on every fuzzed tree. Each tree it accepts
is evaluated without Integrity (`MockEvaluator.evaluateUnchecked`, as stored
by a `...Packed` setter) and must agree with the reference evaluator. It also
lists the tagged shapes the check rejects and Integrity accepts, and the
reverse. `GAP_MUTATE=0.5` changes one node of half the trees (operator,
encoding, compValue length or a boundary byte) to compare the operator rules
with Integrity's; `GAP_EXAMPLES=1` prints one tree per category.

```
cd packages/evm/formal && lake build roles-model && cd ..
GAP_CASES=2000 GAP_CHECK=1 GAP_MUTATE=0.5 npx hardhat test test/formal/integrity-gaps.spec.ts
```

## Proof structure

| File            | Contents                                                                                        |
| --------------- | ----------------------------------------------------------------------------------------------- |
| `Check.lean`    | `Ty`, `HasT`, `classify`, `rootOk`, `zipCheck`, `checkCondition`                                |
| `Sound.lean`    | `desc_of_ty`, `hasT_of_descS`, `zipOK_of`, `rootOK_of`, `checkCondition_sound`, `checked_input` |
| `Flat.lean`     | `packableB`, avatar independence (`skel`), non-structural roots                                 |
| `Ops.lean`      | `opsOk`: Integrity's per-operator rules                                                         |
| `Slots.lean`    | `assigned`, the execution model `Run`, `run_sound`                                              |
| `EndToEnd.lean` | `stored_input`: packing + check + `decoder_input`                                               |
| `Stored.lean`   | `checkStored`, `checkStored_sound`                                                              |
| `Compare.lean`  | comparison operators: `equalTo_iff`, `equalTo_intended`, `compare_word`, `checked_equalTo`      |
| `Examples.lean` | accepted and rejected trees                                                                     |

## Trusted base

- The decoder proof's and the packing proof's trusted bases.
- `Run` matches `evaluate`'s control flow, and `_pluck` is the only writer of
  `pluckedLocations` (a hand transcription, not differentially tested).
- `comparePasses` matches `__compare`/`__compareSigned` (hand transcription;
  the fuzzer's reference evaluator agrees with `evaluate` on `EqualTo` and
  comparisons end to end).
- keccak256 has no collisions (`KeyInjective`), for the `EqualTo` theorems.
- `opsOk` is not proven; it only makes the check stricter.
