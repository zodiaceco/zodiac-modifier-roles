# EIP-712 signing

Machine-checked proofs about how a Roles member gets the avatar to sign an
EIP-712 message: the `allowSignTypedMessage` permission (SDK), Roles'
evaluation of the `signTypedMessage` call to `SignTypedMessageLib`, and the
digest `EIP712Encoder` computes. The EIP-712 standard itself is the reference:
`Spec.lean` transcribes it directly (`encodeType`, `typeHash`, `encodeData`,
`hashStruct`, the `\x19\x01` digest), independent of the ABI and of Roles.

```
cd packages/evm/formal
lake build EIP712
```

## What is proven

`K` is keccak256, a parameter: no theorem assumes anything of it, except that a
struct's `typeHash` is not zero (the encoder tells structs from fixed-size
arrays by a non-zero `typeHash`).

| Theorem                                | Statement                                                                                                                                                                                                                                                                                                                                                                  |
| -------------------------------------- | -------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `hashField_spec` (`Hash.lean`)         | **On any bytes**, `_hashField` is the EIP-712 spec applied to what it reads: it reverts exactly when its walk (`readV`) fails, and otherwise returns `encV` (EIP-712 `enc`; `hashStruct` for a struct) of the value read.                                                                                                                                                  |
| `readV_enc` (`Decode.lean`)            | On the Solidity ABI spec encoding (`DecoderFaithfulness.enc`) of a typed value, the walk reads exactly that value. With `inlineSize_lay`: `_inlineSize` on the type tree agrees with the ABI's static / dynamic and head sizes.                                                                                                                                          |
| `hashTypedMessage_spec` (`Digest.lean`) | When `types` rebuilds (`_toTree`) into the type trees of `EIP712Domain` (node 0) and the primary type (node 1), and `domain` / `message` are the ABI encodings of typed values, the contract returns the EIP-712 digest of those values.                                                                                                                                |
| `visit_agree` (`Agree.lean`)           | **On any calldata**, every node `evaluate` visits from a node that follows the type tree (`FitT`) is a `Site`: it sits exactly where the encoder reads the corresponding member, and that member was read (`Member`), or, below a `Slice`, it reads `size` bytes inside the member's word or inside the content of its `bytes` / `string` (`Window`). `loop_agree` / `children_agree_*`: Roles' `AbiLocation.children` and the encoder's block loop find every child at the same place; Roles only adds bound checks against `msg.data`. |
| `static_input`, `dynamic_input`        | At a member, the operand Roles compares is the word the encoder hashes, or (for `bytes` / `string`) `__input` of exactly the length word and the bytes the encoder hashes.                                                                                                                                                                                              |
| `window_input`                         | In a window, the operand Roles compares is bytes `[sh, sh + size)` of the word, or of the `bytes` / `string` content, the encoder hashes.                                                                                                                                                                                                                                |
| `fallback_offset`, `message_agree`     | `SignTypedMessageLib`'s fallback, which sets the offsets of `domain`, `message` and `types` by hand, reads each argument where Roles' root `Matches` finds it; below the `message` (or `domain`) condition, every visited node is a `Site` in the library's view of the argument.                                                                                      |
| `sign_agree` (`Sign.lean`)             | **The whole permission, Zip jumps included.** `Eval` adds to `Visit` the jumps of `ZipSome` / `ZipEvery` to arrays stored by `Pluck` nodes anywhere in the tree. When `domain` and `message` follow their type trees with one pluck table `Γ` (slot ↦ element type: a `Pluck` sits on an array of that element type, each Zip field follows the element type of its slot) and `types` has no `Pluck` / Zip (`RootFit`), every node `evaluate` reaches is the root, one of its children, below `types`, or a `Site` of the argument its path starts with. |
| `fitB_sound`, `msgB_sound`, `rootB_sound` | Decidable checks for these hypotheses (`FitCheck.lean`), run by the driver's `fit` query. The driver computes `Γ` from the `Pluck` nodes; the check does not trust it.                                                                                                                                                                                                 |
| `layOf_lay`                            | `layOf` computes the type tree of a type; the driver's `lay` query compares it with `_toTree` of the SDK's `toAbiTypes` output.                                                                                                                                                                                                                                             |

Together: when Roles authorizes a `signTypedMessage` call under a
permission that passes `fit` (every `allowSignTypedMessage` permission, and
hand-written ones with `Slice`, `Pluck` and Zip), every member the permission
checks is the member the library hashes, or a window of it, and the library
returns the EIP-712 digest of what it read. For the SDK's own encoding (`encodeSignTypedMessage`) that is
the digest of the typed message.

On non-canonical calldata the library may read a word that is not the
encoding of any value of its type (an address with high bits set, say). The
digest is then `encV` of that word, which, unless keccak256 collides, is the
digest of no well-typed message: no verifier that hashes typed values
accepts the signature. `Atom.Canon` defines the canonical words.

## The view of an argument

The fallback hands the library `bytes calldata` slices whose offset and
length it read from calldata without checking them against `msg.data`. The
library reads `view data base m` (`Agree.lean`): calldata from `base`, zeros
past its end, as `calldataload` does. Roles checks its reads against
`msg.data`, so it only fails where the library would read zeros.

## Hypotheses checked on the SDK's output

The theorems take the SDK's artifacts as hypotheses; the differential tests
check them on every generated case (`test/formal/eip712.spec.ts`):

- `_toTree(toAbiTypes(...))` is the type tree (`lay`).
- The permission `allowSignTypedMessage` builds, as `checkAndPackCondition`
  packs it, satisfies `RootFit` (`fit`).

## Differential tests

`test/formal/eip712.spec.ts` (with the Lean driver built; `EIP712_CASES`,
`EIP712_MUTATIONS`, `EIP712_SEED`). Random typed data: up to four structs,
nested and referenced through `T[]` and `T[k]` (including `T[k][]` and
`T[][k]`), every atomic type, `bytes`, `string`, random domains, declared or
inferred `EIP712Domain`, `chainId` as number or bigint.

1. Three independent digests agree: ethers' `TypedDataEncoder`, the Lean
   spec (`es`), and the contract (`MockEIP712Encoder`) fed by the SDK's
   `encodeTypedDomain` / `encodeTypedMessage` / `toAbiTypes`. The SDK's
   `hashType` agrees with the Lean `typeHash`. The Lean spec reproduces the
   example in EIP-712 (`Mail`, digest `0xbe60…7bd2`).
2. The Lean encoder (`eh`) returns what the contract returns, hash or revert,
   on the SDK's encoding and on mutated bytes and type nodes. 5 seeds × 800
   messages × 8 mutations: 0 differences (about 59% of the mutations are
   still accepted by the contract).
3. `allowSignTypedMessage` permissions (`scripts/formal/eip712-permissions.ts`, in its own
   process: the SDK's authoring helpers do not load under Hardhat): the
   SDK accepts its own permission, the `fit` hypotheses hold, the evaluator
   model accepts `encodeSignTypedMessage`'s calldata, and rejects it when a
   scoped member or a type node changes. About a third of the permissions
   also get hand-written conditions the SDK has no helper for: a `Slice`
   comparing a window of a member's word or `bytes` / `string` content, and
   on `T[]` members two `Pluck`s with a `ZipSome` (comparing an element) or
   `ZipEvery`. Changing a byte in the window or the zipped element must be
   rejected, and variants that break the hypotheses (a `Slice` of the wrong
   kind, a Zip reading an empty slot or with a mistyped field), packed
   without the SDK's check, must fail `fit`. 5 seeds × 300 permissions:
   about 125 Slices and 85 Zips each, all fit, about 620 changed calls and
   250 broken variants each, all rejected.

## Findings (all fixed in the SDK)

- `parseType` read the first array dimension instead of the last: `T[2][]`
  was handled as `T[2]`, `T[][2]` as `T[]`.
- Only power-of-two integer widths were atomic: `uint160`, `uint48`,
  `uint24` and the like were taken for struct names (Permit2's
  `PermitDetails` could not be encoded).
- `typesForDomain` dropped a `bigint` `chainId`.
- A declared `EIP712Domain` was ignored in favour of fields inferred from the
  domain value, so a dapp whose domain type differs got a different digest.
- Recursive types made `toAbiTypes` expand forever; the encoder's layout
  cannot express them, so the SDK now rejects them.
- The SDK's authoring helpers (`c.matches`, `c.eq`, `describeStructure`, for
  every permission, not only signing) described a fixed-size array `T[k]`
  as a dynamic array. The ABI encodes `T[k]` as the tuple `(T, …, T)`, so
  Roles read the parameters after it at the wrong place, and honest calls
  failed. `T[k]` is now a `Tuple` of `k` children; `every` / `some` reject
  it. In the mainnet snapshot (`investigations/roles-pruning`), the three
  functions with a fixed-size array parameter that carry a condition store
  it correctly, as a tuple.

## Not covered

- `encodeType` in the SDK (`hashType`) and `toAbiTypes` are tested against
  the Lean spec and ethers, not proven.
- `SignTypedMessageLib`'s storage write: `SafeStorage` matches the Safe 1.3
  / 1.4.1 layout by inspection. The `SafeMessage` wrapping and the Safe's
  `isValidSignature`, and `personalSign` / `signMessage`: see
  [SafeSigning](../SafeSigning/README.md).
- A `Slice` of a `Slice` is covered by the proof (the contract accepts
  it), but the SDK refuses it (it is one `Slice`), so the tests do not
  generate it.
- `Pluck` nodes inside Zip fields, and Zips in the `types` condition: `fit`
  rejects them (the driver does not give their slots an element type).
- `WithinRatio` compares plucked values, not locations: it is a leaf here,
  and its operands are the values the `Pluck` nodes read at their `Site`.
- Empty structs and `T[0]`: the encoder reverts (fails closed). Solidity has
  neither.
- What the signature authorizes elsewhere (Permit, orders, `RoleTx` of
  another Roles instance): that is the permission's intent, see
  [the overview](../README.md).

## Files

| File            | Contents                                                                    |
| --------------- | --------------------------------------------------------------------------- |
| `Spec.lean`     | EIP-712, transcribed: types, values, `encodeType`, `encodeData`, the digest |
| `Encoder.lean`  | Transcription of `EIP712Encoder.sol`                                        |
| `Read.lean`     | The encoder's walk returning values (`readV`), type trees (`Lay`)           |
| `Hash.lean`     | `hashField_spec`                                                            |
| `Decode.lean`   | `readV_enc`, `inlineSize_lay`                                               |
| `Digest.lean`   | `hashTypedMessage_spec`, `layOf`                                            |
| `Agree.lean`    | Roles' reading against the encoder's, on any calldata (members, windows)    |
| `Sign.lean`     | The whole permission, Zip jumps included (`sign_agree`)                     |
| `FitCheck.lean` | Decidable checks for the agreement hypotheses                               |
| `Keccak.lean`   | Executable keccak256 for the driver (no theorem uses it)                    |
