# Decoder faithfulness

Machine-checked proof that, **on correctly ABI-encoded calldata**, the Roles
v3 condition evaluator reads exactly the bytes the Solidity ABI specification
assigns to each parameter it checks. This includes the bytes selected by
`Slice` and parameters checked under several nested-calldata interpretations
(variant `And`/`Or`).

The formulas are in the [overview](../README.md#decoder-faithfulness). This
page has the details.

```
cd packages/evm/formal
lake build                 # checks every proof (Lean 4.35, no Mathlib)
```

## What is proven

Setting (`Main.lean`):

- `root` is a condition tree that describes a call: `Desc s root (.call pre
args)` and `RootOK root` (the root is `AbiEncoded`, possibly under
  `And`/`Or`).
- The calldata is `pre ++ encTuple args ++ suffix`: the leading bytes (normally
  the 4-byte selector), the **spec encoding** of the arguments, then
  arbitrary trailing bytes.
- The evaluator runs on `annotate root`, the tree as pack + unpack leave it
  (with the `inlined` / `size` / `leadingBytes` metadata `Topology` computes).

Every node `d` the evaluator visits at location `l` is one of four cases
(`Reached`):

1. **Component:** `d` describes the component `u` reached by the same index
   path (`Matches` child _i_ = tuple field / array element / call argument
   _i_), and sits exactly at `u`'s spec encoding.
2. **Window:** `d` is below a `Slice` and sits exactly at a window of `u`'s
   content (the static word, or the bytes without length word and padding).
3. **Non-structural:** e.g. an `EtherValue` comparison; never reads calldata.
4. **Interpretation that need not hold** (only if `s = true`): `d` is inside
   a bytes-like child, such as the `approve(...)` branch of
   `Or[transfer(...), approve(...)]` on a `transfer` call. That child itself
   sits exactly at the right `bytes` value. Inside it, nothing is promised,
   because the data was not encoded that way (see "Not covered").

With `s = false`, every interpretation in the tree must hold and case 4 is
impossible (`InStray.strict`).

| Theorem                  | Statement                                                                                                                                                                                                                                                                                                                                                                                                       |
| ------------------------ | --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `decoder_locations`      | The four cases above, for every visited node.                                                                                                                                                                                                                                                                                                                                                                   |
| `decoder_input`          | For every visited `EqualTo`, `GreaterThan`, `LessThan`, signed comparison, `WithinAllowance` or `Pluck` node, `__input` returns exactly the spec encoding of the component (the word itself when it is 32 bytes, otherwise exactly the bytes that get keccak-hashed). Below a `Slice` it returns exactly a window of the component's content, right-aligned. For `EtherValue` it returns the transaction value. |
| `decoder_custom_operand` | `Custom` conditions receive exactly the spec position and length (of the component, or of the window).                                                                                                                                                                                                                                                                                                          |
| `decoder_children`       | No false rejections: every visited container decodes its children without `CalldataOverflow`, one per component.                                                                                                                                                                                                                                                                                                |
| `decoder_slice`          | No false rejections for `Slice`: the length `_slice` checks `shift + size` against is exactly the length of the bytes the spec window comes from. So a slice is rejected exactly when the spec window does not exist.                                                                                                                                                                                           |

Covered ABI shapes: static words (`uintN`, `intN`, `address`, `bool`,
`bytesN`), `bytes`/`string`, tuples (including fixed-size arrays `T[k]`,
which the ABI encodes as tuples), dynamic arrays `T[]`, and nested calldata
(`AbiEncoded` with any `leadingBytes`), nested arbitrarily. Covered operators:
`Matches`, `And`/`Or` (variant and non-variant), `ArraySome`/`ArrayEvery`/
`ArrayTailMatches` (including variant arrays), `Slice` (nested), `Pass`, and
all leaf operators via the location and operand theorems.

## How it is built

| File                              | Contents                                                                                                                                                                                                   | Depends on        |
| --------------------------------- | ---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- | ----------------- |
| `Spec.lean`                       | ABI encoding, transcribed from the [formal spec section](https://docs.soliditylang.org/en/latest/abi-spec.html#formal-specification-of-the-encoding) of the Solidity docs: values in, bytes out.           | `Bytes.lean` only |
| `Roles.lean`                      | Line-by-line transcription of `AbiLocation.sol`, `Topology.sol`, the pack/unpack metadata, `ConditionEvaluator.__input`, and which node `evaluate` visits at which location (`Visit`, including `_slice`). | `Bytes.lean` only |
| `Desc.lean`                       | `Desc s c u`: condition tree `c` describes value `u` (the structural rules Integrity enforces).                                                                                                            | both              |
| `Basic`, `Meta`, `Decode`, `Main` | Proofs.                                                                                                                                                                                                    |                   |
| `Example.lean`                    | `f(uint256, bytes)` in strict mode; `f(bytes, uint256)` with a variant `Or` (one interpretation does not fit) and a `Slice` on the last byte. Hypotheses hold, conclusions checked on concrete bytes.      |                   |

The two models are independent by construction. The spec builds bytes from
values and never reads anything back; there is no reference decoder. The
Roles side walks calldata and reads offsets. The proof has to show that the
walker inverts the encoder. A mistake shared by both sides (for example,
forgetting nested calldata's `leadingBytes`) makes the theorems false and the
build fail.

## Checking the transcription against the Solidity

`Roles.lean` is a hand translation, so it is tested against the deployed code
by `test/formal/lean-model.spec.ts`:

- **Decoder, differential.** Random function signatures and matching
  condition trees (including `And`/`Or` wrappers, variant `Or` with a second
  nested-calldata interpretation, `Slice` nodes and non-structural siblings),
  with calldata encoded by ethers' `AbiCoder` (half of it then corrupted). The
  test walks the trees the way `evaluate` does and compares every
  `AbiLocation.children` and `AbiLocation.size` result from `MockLocator`
  (Integrity → pack → unpack → AbiLocation, on-chain) with the Lean model's,
  via the `roles-model` executable (`../Diff.lean`).
- **Slice, end to end.** For random signatures, a `Slice` + `EqualTo` on one
  argument is run through the real `ConditionEvaluator.evaluate` (`MockEvaluator`).
  The result must be exactly what the spec window predicts: `Ok` for the
  right value, `ParameterNotAllowed` for a different one, `CalldataOverflow`
  when the window lies outside the value.

```
cd packages/evm/formal && lake build roles-model
cd .. && LEAN_DIFF_CASES=60 LEAN_DIFF_SEED=1 npx hardhat test mocha test/formal/lean-model.spec.ts
```

Calls that revert on-chain (out of gas or array-allocation panics, mostly on
corrupted data) are skipped and counted. Reverting denies the transaction,
so it is the safe direction. The `Visit` relation and `__input` are otherwise
reviewed by hand; `MockLocator` does not expose them.

## Assumptions (trusted base)

- **The transcription** of the Solidity in `Roles.lean`. Mitigated by the
  tests above.
- **The spec transcription** in `Spec.lean` (about 40 lines, mirrors the
  docs' formal definition).
- **Integrity**: the theorems are about trees satisfying `Desc` and
  `RootOK`. That `Integrity.enforce` only accepts such trees (for a given
  signature) is not proven here. Also assumed: inlined sizes ≤ 8191 bytes
  (Integrity rejects larger), and the flat-BFS-array-to-tree view of
  `Topology`.
- **Arithmetic**: modeled on unbounded naturals. Solidity's checked
  `uint256` arithmetic reverts on overflow, and a revert denies.
  `calldata.length < 2^255` is a hypothesis.
- **Lean 4.35** kernel and core library.

## Not covered

- **Malformed or adversarial calldata.** Whether Roles and the target
  contract's decoder agree on non-canonical encodings (out-of-order or
  overlapping offsets, dirty padding, trailing junk inside values). That
  depends on the target's decoder, so it is a separate property. This
  includes what happens inside an interpretation that does not fit the data
  (case 4).
- `ZipSome`/`ZipEvery` (they read locations stored by earlier `Pluck` nodes,
  which needs a stateful model of evaluation), the internals of
  `BitmaskChecker`, and comparison semantics (`__compare`, keccak). Only the
  operand is proven, not what is done with it.
