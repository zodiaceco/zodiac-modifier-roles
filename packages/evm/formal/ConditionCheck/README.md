# Condition check

A decidable check on condition trees, `checkCondition`, with a proof that every
tree it accepts satisfies the hypotheses of the
[decoder theorems](../DecoderFaithfulness/README.md). It is the specification
for the check the SDK runs before storing a tree with a `...Packed` setter,
which skips `Integrity`. Unlike Integrity, it rejects the shapes in
[INTEGRITY_BACKLOG.md](../../../sdk/INTEGRITY_BACKLOG.md) that `evaluate`
misreads.

The formulas are in the [overview](../README.md#condition-check). This page has
the details.

```
cd packages/evm/formal
lake build ConditionCheck
```

## The check

`checkCondition s root : Option Ty` (`Check.lean`) returns the ABI type the
tree describes, or `none`. `Ty` is `static`, `dynamic`, `tuple ts`, `array t`
or `call lb ts` (nested calldata with `lb` leading bytes). Every node is
classified bottom-up as structural with a type, non-structural (`ns`), or a Zip:

| Node                                       | Accepted when                                                                                                         | Kind               |
| ------------------------------------------ | --------------------------------------------------------------------------------------------------------------------- | ------------------ |
| `Static` / `Dynamic` leaf                  | no children, operator not `And`/`Or`/`Matches`/array/`Slice`/`Zip`                                                    | `static`/`dynamic` |
| `Static` / `Dynamic` `Slice`               | one `Static` child of kind `static` (a leaf or another slice), slice size 1–32                                        | `static`/`dynamic` |
| `Tuple`                                    | ≥ 1 child, all structural; operator `Matches` or a non-navigating one (`Pass`, `EqualTo`, ...)                        | `tuple ts`         |
| `Array`                                    | ≥ 1 child, all structural with the same type `t`; operator `Matches`, `ArraySome/Every/TailMatches` or non-navigating | `array t`          |
| `AbiEncoded`                               | ≥ 1 child, all structural; `Matches` or `Pass`                                                                        | `call lb ts`       |
| `None` / `EtherValue` leaf                 | no children, non-navigating operator                                                                                  | `ns`               |
| `None` `ZipSome` / `ZipEvery`              | exactly one child, of kind `tuple _` (the fields)                                                                     | `zip`              |
| `None` `And` / `Or`, all children `ns`     | ≥ 1 child                                                                                                             | `ns`               |
| `None` `And` / `Or`, some child structural | see below                                                                                                             | `t`                |

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
  `z`'s slot for `f`: the Pluck node is an `Array`, and its element template
  has the field's type (`zipCheck`).

`s` is the strictness flag of the decoder theorems. With `s = false`,
variants are rejected and the theorems give the full guarantee. With
`s = true`, variants are accepted and the theorems allow "an interpretation
that does not fit" (case (iv)).

## What is proven

`Sound.lean`, `checkCondition_sound`: if `checkCondition s root = some t`, then

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
`call` type. `checkCondition_call` restates this for a root of type
`call lb ts`: every calldata with `lb` leading bytes and arguments of types
`ts`.

The proof has two directions, both by recursion on the tree:

- `desc_of_ty`: a node of type `t` describes every value of type `t`. This is
  the main result.
- `hasT_of_descS`: a value a node describes has the node's type. It is needed
  for Zips: `ZipOK` says a Zip field describes whatever the Pluck node's
  elements are, and the check only compares types.

`checked_input` composes this with `decoder_input`: on a checked tree, for every
well-typed calldata, the comparison operands are the spec bytes.

`EndToEnd.lean`, `stored_input` adds [condition packing](../ConditionPacking/README.md):
for a flat array `fs` that is `Packable` and whose tree passes the check, the
tree `unpack` returns from `pack fs` (what a `...Packed` setter stores and
`evaluate` reads) gets the same guarantee.

`Examples.lean`: the decoder proof's three example trees pass (the variant one
only with `s = true`), and the backlog's Zip-among-`Matches`-children bypass is
rejected. All by `decide`.

## What the check does not cover

- **`Packable`.** BFS order, field widths and compValue shapes (for example
  Pluck indices ≤ 254, `AbiEncoded` leading-bytes compValues) are hypotheses of
  `pack_roundtrip`, checked on the flat array, not here.
- **Pluck slots.** The decoder model assumes that the slot a Zip reads holds
  the location of the unique Pluck with that index, evaluated before the Zip
  (Integrity's `_validateUniquePluckDefinitions` and
  `_validatePluckAssignments`). The check does not enforce it yet.
- **Operator semantics.** Which operators make sense on which encoding, and
  their compValue formats (`Bitmask` lengths, `WithinRatio`, `Custom`, ...),
  are not about locations and not proven here.
- **Calldata with no arguments.** An `AbiEncoded` node needs at least one child,
  as `Desc` requires.

Compared with Integrity, the check is stricter on the backlog shapes (a Zip
anywhere but under `And`/`Or`, non-structural children of containers, a Zip
before the described child, root encodings) and looser on one: it accepts
`Slice` next to plain checks in an `And`/`Or` (backlog item 4), which Integrity
rejects but the decoder proof covers.

## Tests

`test/formal/integrity-gaps.spec.ts` with `GAP_CHECK=1` runs the check (through
the Lean driver's `ck` query) on every fuzzed tree. Each tree it accepts is
evaluated without Integrity (`MockEvaluator.evaluateUnchecked`, as stored by a
`...Packed` setter) and must agree with the reference evaluator. It also lists
the tagged shapes the check rejects and Integrity accepts, and the reverse.

```
cd packages/evm/formal && lake build roles-model && cd ..
GAP_CASES=2000 GAP_CHECK=1 npx hardhat test test/formal/integrity-gaps.spec.ts
```

## Proof structure

| File            | Contents                                                                                                          |
| --------------- | ----------------------------------------------------------------------------------------------------------------- |
| `Check.lean`    | `Ty`, `HasT`, `classify`, `rootOk`, `zipCheck`, `checkCondition`                                                  |
| `Sound.lean`    | Inversion lemmas, `desc_of_ty`, `hasT_of_descS`, `zipOK_of`, `rootOK_of`, `checkCondition_sound`, `checked_input` |
| `EndToEnd.lean` | `stored_input`: packing + check + decoder                                                                         |
| `Examples.lean` | Accepted and rejected trees                                                                                       |

## Trusted base

Nothing beyond the decoder proof's: `checkCondition` is the specification
itself, and its soundness is proven against `Desc`, `RootOK` and `ZipOK`. An
SDK implementation must match `Check.lean`, which a differential test against
the Lean driver can check.
