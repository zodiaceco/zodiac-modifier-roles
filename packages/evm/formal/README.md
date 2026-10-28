# Formal verification of Roles v3

Machine-checked proofs (Lean 4) of properties of the Zodiac Roles Modifier v3
contracts. Each property is one Lean library in this Lake package, with its own
README. This page tracks what is proven, in simplified notation; the Lean
statements are the authoritative versions.

```
cd packages/evm/formal
lake build                 # checks every proof (Lean 4.35 via elan, no Mathlib)
```

A successful build means every theorem below is proven. There is no `sorry`,
`admit` or custom `axiom`; the theorems depend only on Lean's standard axioms
(`propext`, `Classical.choice`, `Quot.sound`).

## Status

| Property                                                                                                                                                      | Library                                                | Status |
| ------------------------------------------------------------------------------------------------------------------------------------------------------------- | ------------------------------------------------------ | ------ |
| [Decoder faithfulness](#decoder-faithfulness): on correctly encoded calldata, every condition checks exactly the bytes the ABI spec assigns to its parameter  | [`DecoderFaithfulness`](DecoderFaithfulness/README.md) | Proven |
| [Condition packing](#condition-packing): unpacking a packed condition array returns the input tree, for every array Integrity's width and order checks accept | [`ConditionPacking`](ConditionPacking/README.md)       | Proven |
| [Condition check](#condition-check): a decidable check on stored arrays (the spec for the SDK): packing, Pluck slots and the decoder hypotheses hold          | [`ConditionCheck`](ConditionCheck/README.md)           | Proven |
| [Normalization](#normalization): the SDK's `normalizeCondition` never changes what a condition means (on decoded values)                                       | [`Normalize`](Normalize/README.md)                     | Proven |
| [Evaluation on calldata](#evaluation-on-calldata): on every calldata, the evaluator computes the contract's own reading, which meets normalization's assumptions   | [`Bridge`](Bridge/)                                    | Proven |
| [Normalization on calldata](#normalization-on-calldata): on every calldata, the normalized tree computes the contract's reading of the tree as written            | [`Bridge`](Bridge/)                                    | Proven |
| [SDK pipeline](#the-sdk-pipeline-end-to-end): normalize → flatten → pack → unpack → evaluate computes the reading of the user's tree                              | [`Bridge`](Bridge/)                                    | Proven |
| [Evaluator model](#the-evaluator-model): `Evaluate/Model.lean` against `ConditionEvaluator.evaluate`                                                             | [`Evaluate`](Evaluate/)                                | Tested |
| [EIP-712 signing](#eip-712-signing): the contract signs the EIP-712 digest of what it reads, and Roles checks exactly the members it hashes                     | [`EIP712`](EIP712/README.md)                           | Proven |
| [MultiSend](#multisend): the transactions Roles checks in a batch are exactly the transactions MultiSend executes                                                | [`MultiSend`](MultiSend/README.md)                     | Proven |
| [Signing through the Safe](#signing-through-the-safe): each signing function makes exactly its hash valid in the Safe's `isValidSignature`; `signMessage` signs raw hashes | [`SafeSigning`](SafeSigning/README.md)                 | Proven |
| [Allowances](#allowances): spending limit over any transactions; charges with decimals and prices round up once, so rounding never accumulates in the role's favour | [`Allowance`](Allowance/README.md)                     | Proven |
| [End to end](#end-to-end): signing permissions reach a Roles Modifier's `RoleTx` only through the permissions `permissionHazards` flags; every transaction the avatar executes, batches included, passed its own permission, and the spending limit holds across executions | [`EndToEnd`](EndToEnd/README.md) | Proven |
| [Attribution and reentrancy](#end-to-end): executions never interleave; each runs as an enabled, active member, each signature once | [`EndToEnd`](EndToEnd/README.md#attribution-and-reentrancy) | Tested |
| [Target decoding](TargetDecode/README.md): on every layout solc's decoder accepts (tails reordered, shared or gapped, dirty padding), each node Roles visits is where the target reads its component; static operands are exactly the decoded values, an `EqualTo` passes only if the target decoded the pinned value, `Bitmask` and `Slice` see the bytes the target decodes. That checks combine per `Or` branch is tested | [`TargetDecode`](TargetDecode/README.md) | Proven |

Not covered yet:

- **Integrity ⇒ `Desc`, `ZipOK`.** That `Integrity.enforce` only accepts
  condition trees that describe some ABI type, and enforces the Zip type rules.
  Decoder faithfulness assumes it, and it is false today: trees Integrity
  accepts but `evaluate` misreads are tracked in
  [packages/sdk/INTEGRITY_BACKLOG.md](../../sdk/INTEGRITY_BACKLOG.md), found
  with the fuzzer `test/formal/integrity-gaps.spec.ts`. The
  [condition check](#condition-check) proves the hypotheses for every tree it
  accepts instead, for clients that store trees with the `...Packed` setters.
- **Pluck slots, in the decoder model.** That the slot a Zip reads holds the
  location where a Pluck with that index was evaluated. The decoder model
  assumes it. The condition check proves no unwritten slot is read, against a
  model of `evaluate`'s control flow (`Run`). `Bridge` needs no such assumption: its
  reading is the contract's own, so a Zip reads whatever its slots hold, in
  the tree as written and in the normalized tree alike.
- **Integrity ⇒ `Packable`.** The condition packing theorem assumes the width,
  order and compValue checks listed in its
  [README](ConditionPacking/README.md#hypotheses-packable-and-where-integrity-checks-them);
  that Integrity enforces them is from reading the code, not proven.
- What `WithinRatio` and `Custom` checkers do with their operands.
  (Allowances are proven in [`Allowance`](#allowances) and
  [`EndToEnd`](#end-to-end); `Bitmask` and the comparison operators are proven, `EqualTo` up to a
  keccak256 collision on the operand and the compValue; see
  [comparison operators](#comparison-operators).)
- **The reading, not execution, is the reference.** `Bridge` proves that
  the stored tree computes the contract's *reading* of the tree as written.
  The reading treats a branch that panics as a failed branch. The contract
  stops instead: the tree as written can revert where the normalized tree
  passes. Example (a regression test in `test/formal/sdk-normalize.spec.ts`):
  `Or[Matches(ArrayEvery[EqualTo(1)]), Pass]` on `f(uint256[])`, with
  calldata claiming $`2^{64}`$ elements. `AbiLocation.children` allocates
  before it reads, so the tree as written panics; normalization sorts the
  `Pass` branch first, which passes. The model has no gas: the contract also
  runs out of gas allocating from about 90,000 claimed elements (under the
  $`2^{24}`$ transaction gas cap), where the model fails the branch. Both
  need malformed calldata (the count is the caller's word, not the calldata's
  size). Accepted: in the reading, as in the tree's intent, the `Pass` branch
  allows the call. Requiring the stored tree to revert wherever the tree as
  written does would forbid reordering any branch that can panic, which is
  almost any branch that reads an array.
- **The tree as written versus what the user meant.** The proofs start
  from a condition tree. That the SDK's authoring helpers, ABI selection or
  a UI build the tree the user meant is not covered. (For signing, the
  `fit` check covers the permissions `allowSignTypedMessage` builds; it
  found that the helpers described fixed-size arrays as dynamic arrays.)
- **The Integrity path.** Trees stored with the setters that run
  `Integrity` (not `...Packed`) get none of these guarantees: Integrity
  accepts trees `evaluate` misreads (the backlog above). It is a separate,
  known-unsafe entry path, not an unfinished proof.
- **Buffers the SDK did not pack.** `pack_roundtrip` is about the packer's
  output. A buffer passed to a `...Packed` setter by other means is not
  covered.
- **CI.** The repository's CI does not build the Lean proofs or the
  driver; the differential tests skip without it, and the evaluator fuzzer
  runs only when asked (`GAP_EVAL`). A green CI run says nothing about
  them yet.
- A Zip inside a type node, e.g. `f(uint256[] a, uint256[] b, uint256 c)` with
  `Matches[Pluck a, Pluck b, ZipEvery(…), EqualTo(c)]`. Only a Zip whose
  ancestors are all `And`/`Or` is modeled. The SDK check rejects the others
  (a `Matches` child must read a parameter), and so does `Bridge`'s
  well-typedness `inv`, so trees stored through the SDK never have one.
  Integrity accepts such trees, but the decoder gives the Zip a
  parameter slot or inline size: later parameters are read at the wrong place (a
  policy bypass, reproduced on-chain), and a Zip over dynamic fields falsely
  overflows. See the [details](DecoderFaithfulness/README.md#not-covered) and
  the backlog.
- **`checkStored` ⇒ `inv`.** `Bridge` assumes the tree is well-typed
  (`inv`, node by node `invP` in `Bridge/ReadNorm.lean`): adequacy's
  `adOk`, the children of an `And`/`Or` that read a parameter share one
  layout, checks on a whole value have type descriptions as children, and
  so on. Each clause is a rule of the SDK check. That `checkStored` implies
  `inv` is tested, not proven: `invB` decides `inv` (`invB_sound`,
  `Bridge/InvCheck.lean`, the driver's `iv` query), and the differential
  tests ask it of every array `checkStored` accepts
  (`test/formal/sdk-check.spec.ts`; 11,600 over 4 seeds, all well-typed,
  while half the rejected ones are not) and of every user tree whose
  normalized form it accepts (`test/formal/sdk-normalize.spec.ts`; 14,300
  over 8 seeds, all well-typed as written). `checkAndPackCondition` (the SDK
  entry point for the whole path) checks the tree as written too, so the
  proof's hypothesis is enforced, not inferred. The test found one rule
  missing: the check accepted a `Slice` over a `Slice`, which adequacy does
  not model; it now requires a leaf below a `Slice` (one `Slice` with the
  combined shift does the same).
- **Non-canonical calldata, on the target.** For targets compiled by solc,
  [target decoding](TargetDecode/README.md) proves that each check Roles
  makes is a check on what the target decodes. That the checks then combine
  to the same verdict is tested (Plucks, Zips, `WithinRatio` and nested
  calldata included), not proven; crafted encodings can choose
  among `Or` branches (documented). Targets with other decoders (Vyper,
  hand-written) and custom checkers are not covered.
- **Memberships, signatures and reentrancy** are tested on chain, not
  proven ([attribution and reentrancy](EndToEnd/README.md#attribution-and-reentrancy)).
- **Settlement order.** That settlement equals running the charges in
  order holds unless the executed transaction changes the Roles Modifier's
  own state (documented caveat, shown in
  `integration-tests/test/e2e/composition.spec.ts`).

## Notation

| Symbol                                                                                             | Meaning                                                                                                                                                                    |
| -------------------------------------------------------------------------------------------------- | -------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| $`\mathsf{enc}(u)`$                                                                                | ABI spec encoding of value $`u`$ (`Spec.lean`, from the Solidity docs)                                                                                                     |
| $`v = \mathsf{call}(\mathit{pre}, \vec a)`$                                                        | the call: leading bytes $`\mathit{pre}`$ (normally the selector) and arguments $`\vec a`$                                                                                  |
| $`\mathsf{cd} = \mathit{pre} \mathbin{+\!\!+} \mathsf{enc}(\vec a) \mathbin{+\!\!+} \mathit{sfx}`$ | correctly encoded calldata, with arbitrary trailing bytes $`\mathit{sfx}`$                                                                                                 |
| $`\mathsf{cd}[\ell, n]`$                                                                           | the $`n`$ bytes of $`\mathsf{cd}`$ starting at position $`\ell`$                                                                                                           |
| $`\mathsf{Desc}_s(c, v)`$                                                                          | condition tree $`c`$ describes value $`v`$ (the structural rules Integrity enforces); with $`s = \mathsf{true}`$, alternative nested-calldata interpretations need not fit |
| $`(d, \ell, p) \in \mathsf{Eval}(\mathsf{cd}, c)`$                                                 | evaluating $`c`$ on $`\mathsf{cd}`$ reaches node $`d`$ at byte $`\ell`$ along component path $`p`$ (including through Zips)                                                |
| $`v\vert_p`$                                                                                       | the component of $`v`$ at path $`p`$ (tuple field / array element / argument $`i`$ per step)                                                                               |
| $`\mathsf{content}(u)`$                                                                            | the 32-byte word of a static $`u`$, or the bytes of a `bytes`/`string` value without length word and padding                                                               |
| $`w \sqsubseteq x`$                                                                                | $`w`$ is a contiguous part of $`x`$                                                                                                                                        |

## Decoder faithfulness

[Details](DecoderFaithfulness/README.md) · Lean: `DecoderFaithfulness/Main.lean`

All theorems share the hypotheses

```math
\mathsf{Desc}_s(c, v), \qquad \mathsf{RootOK}(c), \qquad \mathsf{ZipOK}_s(c), \qquad |\mathsf{cd}| < 2^{255}, \qquad (d, \ell, p) \in \mathsf{Eval}(\mathsf{cd}, c), \qquad u = v|_p
```

where $`\mathsf{RootOK}(c)`$ says the root is `AbiEncoded`, possibly under
`And`/`Or`, and $`\mathsf{ZipOK}_s(c)`$ is Integrity's Zip type rule: each Pluck
a Zip references is an array node, and Zip field $`f`$ describes every element
of the arrays that Pluck describes (trivial without Zips). In short:

```math
\mathsf{cd} = \mathit{pre} \mathbin{+\!\!+} \mathsf{enc}(\vec a) \mathbin{+\!\!+} \mathit{sfx}
\;\Longrightarrow\;
\forall (d, \ell, p) \in \mathsf{Visit}:\;
\mathsf{cd}[\ell, |\mathsf{enc}(v|_p)|] = \mathsf{enc}(v|_p)
\;\wedge\; \mathsf{input}(d) = \mathsf{enc}(v|_p)
\;\wedge\; \mathsf{bitmask}(d) = \mathsf{bitmaskSpec}(\mathsf{content}(v|_p))
\;\wedge\; \text{no false } \texttt{CalldataOverflow}
```

Zip fields are evaluated at element $`i`$ of the array a Pluck reached at path
$`p`$, so their component path is $`p \mathbin{+\!\!+} [i] \mathbin{+\!\!+} q`$
and the same statements apply to them.

The exact statements also cover nodes below `Slice` (windows), nodes that never
read calldata, and interpretations that don't fit the data. Each theorem ends
with **or (iv)**: with $`s = \mathsf{true}`$, $`d`$ may lie inside an
interpretation that does not fit the data. That interpretation's root sits
exactly at the right `bytes` value, but nothing is promised inside it. With
$`s = \mathsf{false}`$, (iv) is impossible (`InStray.strict`).

### `decoder_locations`: every visited node sits where the spec puts its component

One of:

```math
\begin{aligned}
&\text{(i)}\quad \mathsf{Desc}_s(d, u) \;\wedge\; \mathsf{cd}[\ell, |\mathsf{enc}(u)|] = \mathsf{enc}(u) \\
&\text{(ii)}\quad \exists\, w \sqsubseteq \mathsf{content}(u),\; 1 \le |w| \le 32:\; \mathsf{cd}[\ell, |w|] = w \qquad \text{(below }\texttt{Slice}\text{)} \\
&\text{(iii)}\quad d \text{ never reads calldata (e.g. }\texttt{EtherValue}\text{)} \\
&\text{(iv)}\quad \text{inside an interpretation that does not fit}
\end{aligned}
```

In (i), the root call at $`\ell = 0`$ has no length word:
$`\mathsf{cd}[0, |\mathit{pre}| + |\mathsf{enc}(\vec a)|] = \mathit{pre} \mathbin{+\!\!+} \mathsf{enc}(\vec a)`$.

### `decoder_input`: comparison operands are exactly the spec bytes

For every `EqualTo`, `GreaterThan`, `LessThan`, signed comparison,
`WithinAllowance` or `Pluck` node $`d`$, one of:

```math
\begin{aligned}
&\mathsf{input}(\mathsf{cd}, \ell, d) =
  \begin{cases}
    \mathsf{word}(\mathsf{enc}(u)) & \text{if } |\mathsf{enc}(u)| = 32 \\
    \mathsf{hash}(\mathsf{enc}(u)) & \text{otherwise (the bytes that get keccak-hashed)}
  \end{cases} \\
&\mathsf{input}(\mathsf{cd}, \ell, d) = \mathsf{word}(w) \text{ for some } w \sqsubseteq \mathsf{content}(u) \qquad \text{(below }\texttt{Slice}\text{, right-aligned)} \\
&\mathsf{input}(\mathsf{cd}, \ell, d) = \texttt{msg.value} \qquad \text{(}\texttt{EtherValue}\text{)} \\
&\text{(iv)}
\end{aligned}
```

### `decoder_custom_operand`: `Custom` gets exactly the spec region

For a `Custom` node $`d`$, the $`(\mathit{location}, \mathit{size})`$ passed to
the checker is one of:

```math
(\ell,\ |\mathsf{enc}(u)|) \text{ with } \mathsf{cd}[\ell, |\mathsf{enc}(u)|] = \mathsf{enc}(u)
\qquad
(\ell,\ |w|) \text{ with } \mathsf{cd}[\ell, |w|] = w \sqsubseteq \mathsf{content}(u)
\qquad
d \text{ never reads calldata}
\qquad
\text{(iv)}
```

### `decoder_children`: containers never falsely overflow

For $`d`$ a `Tuple`, `Array` or `AbiEncoded` node:

```math
\exists\, \vec\ell:\;\; \mathsf{children}(\mathsf{cd}, \ell', d) = \mathsf{some}(\vec\ell)
\;\wedge\; |\vec\ell| = |\mathsf{components}(u)|
\qquad \text{or (iv)}
```

Here $`\ell'`$ is $`\ell`$ moved past the length word and leading bytes for
nested calldata. By `decoder_locations`, each $`\ell_i`$ is then where the spec
put component $`i`$.

### `decoder_slice`: `Slice` rejects exactly when the spec window doesn't exist

For a `Slice` node $`d`$, the length $`L`$ that `_slice` checks
$`\mathit{shift} + \mathit{size} \le L`$ against is:

```math
L = |\mathsf{content}(u)|
\qquad\text{or}\qquad
L = |w| \text{ for the enclosing window } w \sqsubseteq \mathsf{content}(u) \text{ (nested }\texttt{Slice}\text{)}
\qquad\text{or (iv)}
```

### `decoder_bitmask`: Bitmask checks exactly the spec bits

For a `Bitmask` node $`d`$ on a `Static` or `Dynamic` parameter (as Integrity
requires), with compValue $`\mathit{cv}`$ = shift, mask, expected ($`n`$ bytes
each), and any memory contents after the compValue:

```math
\mathsf{bitmaskCheck}(\mathsf{cd}, \ell, d) = \mathsf{bitmaskSpec}(b, \mathit{cv})
\quad\text{with } b = \mathsf{content}(u) \text{, or } b = w \sqsubseteq \mathsf{content}(u) \text{ below }\texttt{Slice}\text{, or (iv)}
```

```math
\mathsf{bitmaskSpec}(b, \mathit{cv}) =
\begin{cases}
\texttt{BitmaskOverflow} & \text{if } \mathit{shift} + n > |b| \\
\texttt{Ok} & \text{if } \forall j < n:\; b[\mathit{shift} + j] \mathbin{\&} \mathit{mask}[j] = \mathit{expected}[j] \\
\texttt{BitmaskNotAllowed} & \text{otherwise}
\end{cases}
```

So it never reports `CalldataOverflow` on correct calldata, and the 32-byte
chunks with a rinse mask compare exactly these bytes.

### `decoder_zip`: Zip decodes exactly the plucked spec arrays

For a reached Zip $`z`$, field $`f`$, and a reached Pluck node at $`(\ell, p)`$
with the slot $`z`$ references for $`f`$:

```math
v|_p = \mathsf{array}(u_0, \dots, u_{k-1})
\;\wedge\;
\mathsf{children}(\mathsf{cd}, \ell, \mathsf{stub}(\mathit{field}_f)) = \mathsf{some}(\ell_0, \dots, \ell_{k-1})
\qquad \text{or (iv)}
```

So `ZippedArrayLengthMismatch` is reported exactly when the plucked spec arrays
differ in length, and by `decoder_locations` field $`f`$ is evaluated at element
$`i`$ exactly where the spec put $`u_i`$.

### Trusted base

- `Roles.lean` matches the Solidity. It's a hand transcription, tested against
  the contracts by `test/formal/lean-model.spec.ts`. Its `annotate` (what pack
  - unpack leave of the tree) is proven against the byte-level packer and
    unpacker by [condition packing](#condition-packing).
- `Spec.lean` matches the Solidity docs' formal ABI encoding (about 40 lines).
- Integrity only accepts trees with $`\mathsf{Desc}_s`$, $`\mathsf{RootOK}`$ and
  $`\mathsf{ZipOK}_s`$ (not proven yet, and false for navigating nodes below
  an operator that reads its whole value, which $`\mathsf{Desc}_s`$ excludes;
  see [Findings](#findings)).
- When a Zip reads a Pluck slot, it holds a location where a Pluck with that
  index was evaluated (Integrity's slot-filled-before-use rule; the
  [condition check](#condition-check) proves its version against a model of
  the control flow).
- The Lean 4.35 kernel.

## Condition packing

[Details](ConditionPacking/README.md) · Lean: `ConditionPacking/Main.lean`

### `pack_roundtrip`: unpack ∘ pack returns the input tree

For a flat condition array $`\mathit{fs}`$ (the `ConditionFlat[]` argument of
the setters) that is $`\mathsf{Packable}`$ (BFS order, field widths, and the
compValue shapes Integrity requires), any avatar, and any memory around the
buffer:

```math
\mathsf{unpack}(\mathsf{pack}(\mathit{fs})) = \big(\mathsf{annotate}(\mathsf{tree}(\mathit{fs})),\ 1 + \max \mathsf{pluckIndex}(\mathit{fs})\big)
```

$`\mathsf{tree}(\mathit{fs})`$ is the tree the parent pointers describe
(children in array order), with compValues as `_transform` leaves them.
$`\mathsf{annotate}`$ adds the `inlined` / `size` / `leadingBytes` metadata. It
is the function the decoder proof assumes, so the decoder theorems hold for the
tree `unpack` returns.

### `packBuffer_eq`: the buffer format

```math
\mathsf{pack}(\mathit{fs}) = \mathsf{be}_3(n \cdot 256 + \mathit{maxPluck})
\mathbin{+\!\!+} \mathop{+\!\!+}_{i < n} \mathsf{be}_4(\mathsf{node}_i)
\mathbin{+\!\!+} \mathop{+\!\!+}_{i < n,\ \mathit{cv}_i \ne []} \big(\mathsf{be}_2(|\mathit{cv}_i|) \mathbin{+\!\!+} \mathit{cv}_i\big)
```

$`\mathsf{node}_i`$ packs encoding, operator, child count, inlined size and
has-compValue into 32 bits. A client that calls the `...Packed` setters must
produce exactly this.

### Trusted base

- `ConditionPacking/Model.lean` matches the Solidity, including the assembly.
  It's tested against the contracts (byte-identical buffers and identical
  unpacked trees) by `test/formal/lean-model.spec.ts`.
- The EVM semantics of `mload` / `mstore` / `mcopy` / `shl` / `shr` / `or` as
  modeled. `ImmutableStorage` returns the stored bytes.
- The Lean 4.35 kernel.

## Condition check

[Details](ConditionCheck/README.md) · Lean: `ConditionCheck/Stored.lean`

`checkStored s fs` checks a flat condition array before it is stored with a
`...Packed` setter: `Packable`, Integrity's per-operator rules, the Pluck slot
assignment rule, and a type check. `checkCondition s c` classifies every node
bottom-up: structural with an ABI type $`t`$ (`static`, `dynamic`, `tuple`,
`array`, `call lb ts`), non-structural, or a Zip. The type of a `Matches` on
a tuple or calldata is *open*: it lists the first fields, the value may have
more (a tree may leave trailing parameters out). Containers need structural children of the
right types; the children of one `And`/`Or`, and the elements of an array,
must all contain the most specific of them (`Ty.sub`: equal, a prefix of one
dynamic tuple or call, or bytes-like interpretations of one value). A Zip may
only be a child of `And`/`Or` (after the child that describes the value, and
only over a dynamic value), and each Pluck a Zip reads is an array whose
element type fits the field. The check returns the root's type, or that the
root reads no calldata.

### `checkStored_sound`: what an accepted array guarantees

For every avatar and memory contents:

```math
\mathsf{checkStored}_s(\mathit{fs}) = \mathsf{some}(\mathsf{typed}\ t)
\;\Longrightarrow\;
\mathsf{unpack}(\mathsf{pack}(\mathit{fs})) = \mathsf{annotate}(c)
\;\wedge\; \neg\,\mathsf{Run}(c) \text{ reads an unwritten slot}
\;\wedge\; \mathsf{RootOK}(c) \;\wedge\; \mathsf{ZipOK}_s(c) \;\wedge\;
\forall v : t.\ \mathsf{Desc}_s(c, v)
```

where $`c = \mathsf{tree}(\mathit{fs})`$ and $`v : t`$ is "the calldata
$`v = \mathsf{call}(\mathit{pre}, \vec a)`$ has type $`t`$":
$`|\mathit{pre}| = lb`$ and each argument has its type (for an open type,
the first arguments; real calldata with the trailing parameters a tree
leaves out has the type too). Nested calldata has its
`call` type only if it parses as such; with $`s = \mathsf{true}`$, any `bytes`
value also counts. So every decoder theorem holds for every well-typed
calldata. For $`\mathsf{noCalldata}`$, every node `evaluate` reaches reads only
the ether value.

The parts: `checkCondition_sound` (the type check gives the decoder
hypotheses), `run_sound` (the slot rule: no execution reads an unwritten
slot), `packableB_sound`, and `checkCondition_avatar` (the avatar stored in
`EqualToAvatar` nodes doesn't matter).

### Comparison operators

```math
\texttt{EqualTo}(\mathsf{abi.encode}(w)) \text{ passes on } u \iff \mathsf{enc}(u) = \mathsf{enc}(w)
\qquad
\texttt{GreaterThan}(x) \text{ passes on } u \iff \mathsf{uint}(\mathsf{enc}(u)) > \mathsf{uint}(x)
```

(`equalTo_intended`, `compare_word`, signed variants likewise, `checked_equalTo`
end to end), for an operand and compValue of one length class (both 32 bytes,
or both longer), unless the two differ and keccak256 collides on exactly
these two values (`KeyCollides`, impossible for words). The check keeps a
static operand's compValue at exactly its size.

### Findings

Where Integrity and the check differ (details in the
[README](ConditionCheck/README.md#findings-where-integrity-and-the-check-differ)):
Integrity accepts trees `evaluate` misreads (backlog items 1, 2, 6), and
rejects shapes that are read correctly: `Slice` next to plain checks
(item 4), a Zip next to a `Tuple`/`Array` check (item 10), checks of a
prefix of one dynamic tuple or call (branches written with fewer
parameters; the SDK no longer pads them to one type tree), and two checks of one array whose elements are
different interpretations. Unique Pluck indices are not needed for safe
decoding.

### Trusted base

- The decoder and packing proofs' trusted bases.
- `Run` (`Slots.lean`) matches `evaluate`'s control flow, and `_pluck` is the
  only writer of the slots.
- `comparePasses` matches `__compare`/`__compareSigned`.
- The fuzzer (`GAP_CHECK=1`) also evaluates every accepted tree without
  Integrity and compares with a reference evaluator.

## Normalization

[Details](Normalize/README.md) · Lean: `Normalize/Sound.lean`

The SDK normalizes every condition before it is stored (`normalizeCondition`:
flatten, dedupe and unwrap `And`/`Or`, push `Or` down into `Matches`/`And`,
sort). It used to pad branches to one type tree, as Integrity requires; the
SDK stores trees with the `...Packed` setters, and its check accepts checks
of a prefix of one tuple as siblings, so padding was removed (with it, bug 13
below and about 1,500 lines of proof). It also used to prune trailing `Pass`
nodes. The contract locates every child of a `Matches` before evaluating
any, so pruning could change the verdict on calldata (see the end of Findings
on calldata). Pruning was removed; on the live mainnet permissions it saved
3.6% of storing gas and about 2.8k gas per call for each `Pass` it removed
([decision and gas](../../sdk/CONDITION_GAS.md)). `Normalize/Defs.lean`
transcribes it; `test/formal/sdk-normalize.spec.ts` checks the transcription
against the TypeScript on random trees (40,000 over 8 seeds, no difference).

### `normalize_sound`: normalization keeps the meaning

$`[\![c]\!](v, \sigma, \kappa)`$ evaluates condition $`c`$ on the decoded value
$`v`$ with plucked slots $`\sigma`$ and allowance consumptions $`\kappa`$, and
returns whether it passes, the slots after it, and (if it passes) the
consumptions after it. `Pass`, `And`, `Or` and `Matches` on tuples and calldata
are defined as `evaluate` runs them: slots written by a failing `Or` branch stay
written, consumptions start over in every branch. Every other operator is
opaque. For every fuel $`n`$:

```math
\forall v\, \sigma\, \kappa.\quad [\![\mathsf{normalize}_n(c)]\!](v, \sigma, \kappa) = [\![c]\!](v, \sigma, \kappa)
```

The opaque operators are assumed to (`World.Ok`): see their children only
through their meanings; write slots only if `Pluck`; charge only if
`Custom`, `WithinAllowance` or `CallWithinAllowance`; and choose between
charges depending on earlier ones only if `ArraySome` or `ZipSome`. Charges
commute, which `consume_comm` proves of `AllowanceConsumer.consume`.

A world that reads a value through the tree's own types (where a field of a
`Matches` is depends on its children's sizes) also needs `World.NormOk`: an
invariant `inv` of the trees, kept by every rewrite, under which a
normalized child is read where the child was, and the `Or` a merge puts at
the hinge is read where each branch's hinge child was. For worlds that ignore
the tree's types it holds with `inv = True`.

### Findings

Normalization changed what conditions check in eight ways, all fixed in the SDK
(`packages/sdk/src/main/condition/normalize`, with regression tests in
`effects.test.ts`):

1. `pushDownOr` compared children by the packed `conditionId`, which joins
   compValues without lengths: different tuples could collide and `Or`
   branches were merged into a **wider** permission.
2. Merging `Or[sel A(…), sel B(…)]` kept only the first branch's leading bytes:
   one selector was lost and the other **widened**.
3. `Or` branches that charge allowances were sorted: a different allowance was
   charged.
4. `And` children were sorted past the `Pluck` that writes the slot a Zip reads
   (fails safe: the check rejects it).
5. Duplicate allowance checks in an `And` were removed: each copy charges.
6. A merged `Or` commits to its first passing hinge child, while the original
   could backtrack when a later sibling exceeded an allowance (narrower).
7. An `And` whose child chooses between charges (`Or[W₁, W₂]`) was sorted next
   to another charging child: the choice depends on what was charged before.
8. Padding paired a node's children with the sibling's type-tree children by
   position, but type trees list only structural children: with a
   non-structural child first (e.g. an ether value check), the wrong parameter
   was padded. A static tuple grew, and every later parameter was **read at the
   wrong offset**, in both branches. It also padded nodes with the type tree of
   a different encoding (an array like a tuple).

The calldata-level bug 8 is outside the theorem (which is about decoded
values); writing down what padding may do at the value level exposed it.

### Findings on calldata

Lifting the theorem to calldata (below) and the on-chain fuzzer
(`GAP_NORMALIZE=1` in `test/formal/integrity-gaps.spec.ts`) found more, fixed
in the SDK with regression tests (`effects.test.ts`,
`test/formal/sdk-normalize-layout.spec.ts`):

9. Padding appended fields to a static tuple of one call interpretation with
   the type of another (`Or[f((uint) t, uint x), g((uint, uint) t)]` at a
   `bytes` parameter): `t` grew and `x` was read one word later, where any
   appended calldata could sit. Padding now extends only containers that are
   not inlined (their size does not depend on their children), and never a
   call interpretation directly under the `Or` (the contract accepts calldata
   variants of different types as they are).
10. Pruning and padding inside a Zip's fields or a plucked array changed their
    types, which Integrity then rejects; those subtrees are now left as written.
11. Pushing an `Or` down merged children of incompatible types (e.g. a `Slice`
    next to a plain check), which Integrity rejects. Merges now require
    branches of exactly the same type tree: every child of the merged `Or`
    has the same SDK-check type (`compatibleSiblings`, `siblingsSameType` in
    checkStored.ts). A `bytes` check and a nested call, or checks of a prefix
    of one tuple, stay separate branches.
12. `createTypeTree` gave an `And`/`Or` the type of its first child, and none
    when that child reads no parameter, so the parent's type tree lost a field;
    it now takes the first structural child, as the contract's `TypeTree` does.
    The SDK also crashed on such nodes while padding.
13. Padding extended the call branches of a variant `Or` inside a tuple with
    the parameters of a call with another selector (from a sibling tuple):
    the stored tree rejected calls the written one accepted (narrowing, on
    the packed path only: Integrity rejects the tree). Removed with padding.

Removed with pruning: `Pass` places no constraint on a value, including
whether it is well-formed. A trailing `Pass` still makes the contract locate
the field (follow its offset), so on a malformed encoding the tree as written
could fail where the pruned one passed. Example: `f(bytes b)` with
`Matches:AbiEncoded[EqualTo(1), Pass:Dynamic]` on `b` fails on
`b = abi.encode(1)` (`CalldataOverflow`), its normalized form
`Matches:AbiEncoded[EqualTo(1)]` passed. Roles never checks ABI
well-formedness (a `Pass:Static` field is not read, trailing data and
non-canonical offsets are accepted), so this side effect is not a check to
rely on. On top-level calldata a Solidity target rejects such calldata
anyway. Without pruning, the tree as written and the normalized tree locate
the same fields, so the theorems below hold on every calldata, malformed or
not.

## Evaluation on calldata

Lean: `Evaluate/Model.lean`, `Bridge/`

`Evaluate/Model.lean` transcribes `ConditionEvaluator.evaluate` (every
operator, with `AllowanceConsumer`, `WithinAllowanceChecker` and the custom
checker's charges). What it reads from outside (`msg.value`, accrued
allowance balances, custom checkers, price adapters, `WithinRatio`) is a
parameter, assumed only to never report `Ok` as a failure (`EnvOk`); it may
revert (a price adapter, an overflow while scaling), and the theorems are
about runs that do not. It is a fixed function of its arguments: dependence
on gas or on anything else is not modeled.

The **reading** (`Bridge/Read.lean`, `readWorld`) is the contract's own
reading of calldata as a normalization world. A value is where the
evaluator stands: a location, a `Slice` window (the window's size, which
`_slice` gives its child), or an element of a Zip (its fields' locations).
Every operator reads the node the evaluator runs for it, `D(c)`: a
`Matches` locates its children with `AbiLocation.children`, from its
children's `inlined` and `size`; a Zip decodes the arrays at its slots'
locations with its own field types. Nothing is assumed of the calldata, or of
how the tree relates to an ABI type.

### `readWorld_ok`: the normalization proof's assumptions hold

The four assumptions `World.Ok` of `normalize_sound` are theorems for the
reading: charges commute (consumptions as a map from allowance key to
balance and consumed), only `Pluck` writes slots, only `Custom`,
`WithinAllowance` and `CallWithinAllowance` charge, only
`ArraySome`/`ZipSome` choose.

### `adequacy_gen`: the evaluator computes the reading

For every tree whose nodes are well-formed for the evaluator (`adOk`: known
operators, a `Matches` on a tuple or calldata whose children all read a
parameter, a `Slice` over a leaf, a Zip over a tuple of fields), on every
calldata, slots and consumptions:

```math
\mathsf{evaluate}(\mathit{cd}, \ell, D(c), \kappa, \sigma) \neq \mathsf{revert}
\;\Longrightarrow\;
\mathsf{evaluate}(\mathit{cd}, \ell, D(c), \kappa, \sigma) \sim [\![c]\!]_{\mathsf{read}}(\ell, \sigma, \kappa)
```

where $`\sim`$: same slots; both pass with the same consumptions (as a map),
or both fail. A revert (an array length above $`2^{64}-1`$, a compValue the
evaluator cannot read, an external call) denies the call. Gas is not
modeled: the contract also reverts out of gas where the model fails or
passes.

## Normalization on calldata

Lean: `Bridge/ReadNorm.lean`, `Bridge/TyLay.lean`, `Bridge/Final.lean`

### `norm_inv`: normalization keeps every node's layout

`inv c` (well-typed): every node satisfies `invP`, the local rules of the SDK
check: `adOk`; an `And`/`Or` has no encoding, its children that read a
parameter share one layout (`inlined`, and `size` if inlined), and its other
children are empty (inlined, size 0) unless one that reads a parameter is not
inlined; the children of a check on a whole value describe its type (`TD`,
the SDK check's `exactTy`); the children of the other nodes normalization
rewrites read a parameter, and a tuple has one; an inlined node that reads a
parameter has a size.

```math
\mathsf{inv}(c) \;\Longrightarrow\; \mathsf{inv}(\mathsf{normalize}_k(c)) \;\wedge\; \mathsf{lay}(\mathsf{normalize}_k(c)) = \mathsf{lay}(c)
```

An `And`/`Or` takes the layout of its children that read a parameter, so
flattening, deduplication, sorting and unwrapping keep it. A merge puts an
`Or` of the branches' hinge children at the hinge; `sameType` (all of them
have the same SDK-check type) gives them one layout (`sameType_lay`: the
SDK check's type determines `inlined` and `size`), so the `Or` has it too.
Inside a type description normalization keeps the type (`td_normalize`).

`readWorld_normOk` turns this into `World.NormOk` for the reading: a
`Matches` locates normalized children where it located the originals, and
every other operator reads the normalized node as the original.

### `normalize_meaning`: the normalized tree computes the reading of the tree as written

For a well-typed tree, on every calldata:

```math
\mathsf{evaluate}(\mathit{cd}, \ell, D(\mathsf{normalize}_k(c)), \kappa, \sigma) \neq \mathsf{revert}
\;\Longrightarrow\;
\mathsf{evaluate}(\mathit{cd}, \ell, D(\mathsf{normalize}_k(c)), \kappa, \sigma) \sim [\![c]\!]_{\mathsf{read}}(\ell, \sigma, \kappa)
```

from `adequacy_gen` for the normalized tree, `norm_inv` and `normalize_sound`
with `readWorld_ok` and `readWorld_normOk`. `normalize_calldata`: the
evaluations of `c` and of `normalize_k(c)` agree (same verdict, same
consumptions as a map, same slots) whenever neither reverts. The stored tree
never passes where the reading of the tree as written fails. Where one of
them reverts they can differ either way (an `Or` reordered past a branch
that panics, see Not covered): the reference is the reading, not the
execution of the tree as written.

Covered: call variants of any types under one `Or` (each branch is read
with its own types, as the contract does), Zips, `Slice` and nested calldata
in type descriptions, and malformed calldata.

## The SDK pipeline, end to end

Lean: `Bridge/Pipeline.lean`

### `sdk_pipeline`

The SDK normalizes the user's tree $`c_0`$, flattens it to $`\mathit{fs}`$ and
stores `pack(fs)`; the contract unpacks and evaluates. If $`c_0`$ is
well-typed, $`\mathit{fs}`$ is `Packable` (which `checkStored` proves) and
reads back as $`\mathsf{normalize}_k(c_0)`$ (`nest`: node $`i`$'s children
are the later nodes whose parent is $`i`$), then on every calldata:

```math
\mathsf{run}(\mathit{cd}, \mathsf{unpack}(\mathsf{pack}(\mathit{fs}))) \neq \mathsf{revert}
\;\Longrightarrow\;
\mathsf{run}(\mathit{cd}, \mathsf{unpack}(\mathsf{pack}(\mathit{fs}))) \sim [\![c_0]\!]_{\mathsf{read}}(0, \emptyset, \emptyset)
```

The contract enforces what the contract's reading of the tree as written
says, whenever the stored tree does not revert. Chains
`pack_roundtrip`, `unpacked_eq` (the unpacked tree is $`D`$ of the tree read
back) and `normalize_meaning`. `sdk_pipeline_agree`: the contract's
evaluations of the stored tree and of $`D(c_0)`$ agree whenever neither
reverts.

Trusted (tested, not proven):

- that `checkStored` on the tree as written implies `inv` (see Not covered;
  `checkAndPackCondition` runs it);
- that `flattenCondition` produces an array that reads back as its input
  (`fl` in `test/formal/sdk-normalize.spec.ts`: trees reach the driver
  nested, independently of `flattenCondition`);
- the TypeScript transcriptions: `normalizeCondition`, `checkStored`, the
  packer;
- the Solidity transcriptions: the evaluator (next section), the decoder,
  the packer and unpacker (memory pointers are not modeled), the
  comparisons;
- `EnvOk` and an environment that is a fixed function of its arguments;
- keccak256: theorems that depend on it hold unless keccak256 collides on
  two inputs they name (see [hash collisions](#hash-collisions)); the
  evaluator model also represents a hash by its preimage, distinct from
  every word (`B32`), which a caller can only break with a collision or a
  preimage;
- natural numbers for EVM words where the model needs no wraparound, and no
  gas;
- the Lean kernel and toolchain; for the tests, the Lean compiler and the
  driver;
- that callers use the checked path (`checkAndPackCondition`, or
  `checkAndPack` on a normalized tree) and store exactly its output.

## EIP-712 signing

`EIP712` transcribes the EIP-712 standard itself (`Spec.lean`) and the
contract's `EIP712Encoder`, and proves, for `SignTypedMessageLib`'s
`signTypedMessage` under an `allowSignTypedMessage` permission, or a
hand-written one with `Slice`, `Pluck` and Zip conditions:

- `hashField_spec`: on any bytes, the encoder returns the EIP-712 spec hash of
  the value it reads (or reverts).
- `readV_enc`, `hashTypedMessage_spec`: on the SDK's ABI encoding of a typed
  message it reads that message, so it returns its EIP-712 digest.
- `visit_agree`, `message_agree`, `sign_agree`: on any calldata, every member
  Roles' condition checks is the member the encoder hashes, at the same bytes
  (the fallback's hand-set offsets included), or a window inside it (below a
  `Slice`); Zip fields read elements of the arrays the encoder hashes.

The hypotheses on the SDK's output (its type trees, and that the permission's
conditions follow them) are decided in Lean and checked on every generated
case. Differential tests against ethers and the contract found six SDK bugs,
one of them outside signing: the authoring helpers described fixed-size arrays
`T[k]` as dynamic arrays. Details, findings and limits:
[EIP712/README.md](EIP712/README.md).

## MultiSend

`MultiSend` defines the batch format from Safe's documentation and proves
against it both `MultiSendUnwrapper.unwrap` (the entries Roles checks, with
their calldata slices) and the assembly loop of `MultiSend.multiSend` (the
calls it makes): when the unwrapper accepts, MultiSend executes exactly the
transactions Roles checked, in order (`unwrap_exec`). Tested against both
contracts on chain. Details: [MultiSend/README.md](MultiSend/README.md).

## Hash collisions

keccak256 is a parameter `K` of the theorems. Where a statement depends on
it, the alternative is a collision on inputs the theorem names, computed from
its own values (`SafeSigning.CollisionIn K xs`,
`ConditionCheck.KeyCollides`). So the theorem says: the property holds, or
these specific byte strings are a keccak256 collision, which no one knows how
to find. An alternative "keccak256 has some collision" would be vacuous: it
has more inputs than outputs, so collisions exist.

## Signing through the Safe

`SafeSigning` takes EIP-191 as the reference and proves that the library's
`uintToString` is the decimal, that `personalSign` and `signTypedMessage`
make exactly their hash valid in the Safe's `isValidSignature` (unless
keccak256 collides on the inputs involved), and that `signMessage` with a 32-byte message signs that
raw hash, so it subsumes every other signing permission. Tested against a
real Safe and its fallback handler. Details:
[SafeSigning/README.md](SafeSigning/README.md).


## Allowances

`Allowance` transcribes the refill, the conversion of a spend into balance
units (decimals and price adapter), and what each transaction stores.

- **Spending limit:** over any transactions, the role is charged at most the
  stored balance plus `refill` for each full period since the stored
  timestamp.
- **Rounding:** each charge is the spend's value rounded up once, so
  splitting a spend can only cost more. Over any mix of prices and decimals,
  the total charged covers the total value.
- **Refill:** when transactions happen does not change the balance, and
  nothing overflows.
- **`updateAllowance` is retroactive:** it doesn't accrue first, so a new
  refill also pays for periods that elapsed before it. The SDK's
  `accrueThenUpdate` credits the old refill first (`update_limit`), and
  `checkAllowanceUnits` rejects conditions that disagree on an allowance's
  balance decimals.

`test/formal/allowance.spec.ts` compares Roles with the model on random
allowances, prices, decimals and block times. Details:
[Allowance/README.md](Allowance/README.md).

## The evaluator model

`GAP_EVAL=<n>` in `test/formal/integrity-gaps.spec.ts`: generated trees with
allowance checks, generated calldata (corrupted in half the cases), random
allowance balances and `msg.value`, against `MockEvaluator.evaluateWith`
(Integrity → pack → unpack → evaluate). For every tree Integrity accepts, the
exact `Status` and the consumption list must match. 3,000 cases: 1,171
compared, 0 differences, 18 different statuses reached (the others were
rejected by Integrity or ran out of gas on corrupted array lengths).

`GAP_PACKED=1` takes the path the SDK uses: trees are gated by the SDK's
`checkStored` instead of Integrity, packed by the SDK's `packConditions` and
evaluated from that buffer without Integrity
(`MockEvaluator.evaluatePackedWith`), as the `...Packed` setters store them.
3,000 cases (seed 31): 1,147 compared, 0 differences. 237 of them are trees
the SDK check accepts and Integrity rejects (`UnsuitableChildTypeTree`; see
`ConditionCheck/README.md` for the classes).

Limits: the driver's custom checkers, price adapters and `WithinRatio`
always fail, so successful custom charges and conversions are not
compared; allowances start at period zero with given balances (no accrual
or refill); the final Pluck slots are not compared, only what later nodes
read of them; out-of-gas cases are skipped; trees and arrays are small.
Case counts and mutation scores are evidence, not a measure of how likely
the transcription is right.

Found: `AbiLocation.children` allocates the location array before decoding,
so an array length above $`2^{64}-1`$ panics there; the decoder transcription
reports an overflow (both deny). The evaluator model has the panic.

## Mutation testing

`node scripts/formal/mutate.mjs <normalize|check|pack>` changes one operator,
comparison or early return at a time in the SDK code the differential tests
cover and reports the mutants the test does not notice. Last run: normalize
186 of 239 killed (most survivors are equivalent, e.g. `invariant` conditions
and sort ties, or in the packed `conditionId` this test does not cover),
check 389 of 425 (most survivors are equivalent rewrites or sit at
Packable size limits the generators rarely reach), pack 7 of 9 (survivors in the `checkAndPack`
wrapper).

`node scripts/formal/mutate-consumer.mjs` targets what the Lean models cannot
see: memory aliasing. The models treat the consumption list as an immutable
value; `AllowanceConsumer` gets that from copy-on-write over shared entry
pointers. Four hand-written mutants break it (an entry updated in place, the
list updated in place, the free memory pointer not advanced, or one word
short) and run the unit tests, the evaluator differential test and
`batch.spec`. All four are killed. The two in-place mutants were first
caught only by `batch.spec`; a unit test (`02Or.spec`: a failed `Or` branch
charging an allowance charged before the `Or`) now catches them too, and
so does the evaluator differential test: in `GAP_EVAL` mode the generator
adds `And[charge(k), Or[And[charge(k), fail], n], charge(k)?]` around about
one node in eight, also inside array element conditions (in 300 cases, 33
compared with the shape).

## Layout

| Path                   | Contents                                                                             |
| ---------------------- | ------------------------------------------------------------------------------------ |
| `lakefile.toml`        | The Lake package: one `lean_lib` per property, plus the `roles-model` test driver    |
| `DecoderFaithfulness/` | Decoder faithfulness: models, proofs, examples, README                               |
| `ConditionPacking/`    | Condition packing: byte-level pack/unpack model, round-trip proof, README            |
| `ConditionCheck/`      | Condition check: the decidable check, its soundness, end-to-end theorem, README      |
| `Normalize/`           | Normalization: transcription of the SDK's normalizeCondition, semantics, proof       |
| `Evaluate/`            | Transcription of `ConditionEvaluator.evaluate` (differentially tested)               |
| `Bridge/`              | The contract's reading, adequacy, normalization on calldata, the SDK pipeline        |
| `EIP712/`              | EIP-712: the standard, the encoder, the digest, Roles against the encoder, README    |
| `MultiSend/`           | The batch format, the unwrapper and MultiSend's loop, README                         |
| `SafeSigning/`         | EIP-191, `uintToString`, the stored keys and the Safe's `isValidSignature`, README   |
| `Allowance/`           | Refill, charging with decimals and prices, the spending limit, README                |
| `EndToEnd/`            | Signing routes, batches, the spending limit over executions, README                  |
| `TargetDecode/`        | Values read by following offsets, solc's decoder, Roles' walker on any layout, README |
| `Diff.lean`            | `roles-model` executable: runs the Lean models on queries from the differential test |
| `../test/formal/`      | Tests of the Lean models against the Solidity contracts                              |

To add a property, add a `[[lean_lib]]` to `lakefile.toml` and append its name
to `defaultTargets`. Then add a row to the status table and a section with its
theorems here.

## End to end

`EndToEnd` is about how the contracts compose, not about one function. A
Safe that is a member of a Roles Modifier `R` answers `R`'s
`execTransactionWithSignature` through EIP-1271, and roles on the Safe's
own Roles Modifier can make it sign. `only_flagged` proves which signing
permissions can make it sign a `RoleTx` for `R`:
- `signMessage` without a pin;
- typed messages without pinned types, or with `RoleTx` types;
- never `personalSign`.

These are exactly the permissions the SDK's `permissionHazards` flags. The
proof goes through Roles' reader against Solidity's ABI decoder
(`route_bytes`) and against the signing library's hand-written fallback
(`route_types`), on any calldata. Two of the check's rules came from it: the
`types` element shape, and the head position of a pin.

For batches, `executed_authorized` proves that every transaction the avatar
executes passed its own permission: the call itself, or each transaction
`MultiSend` runs (through `MultiSend.unwrap_exec`). `evalC_steps` and
`steps_spec` prove that a passing evaluation charges only along the path
that passed, and that the consumption list never holds a key twice.
`_persist` writes every entry, so a second entry for a key would overwrite
the first. Together, a batch settles as one `Allowance.tx` per allowance
(`authorize_persist`), and the spending limit holds over any executions
(`executions_limit`). The hypotheses:
- unwrappers are registered only for `MultiSend`;
- conditions that read outside state see it as it was before the batch;
- nothing else writes the allowances in between.

Attribution and reentrancy are tested on chain, not proven: executions of
one Roles Modifier never interleave (every external call before the
avatar's is a staticcall, a nested execution reverts, and only owner and
caller-keyed functions succeed during one), which is the sequential history
the spending limit assumes. A stateful fuzz with hostile targets and
ERC-1271 signers predicts every outcome. It found that with `shouldRevert`
false the submitter of a relayed transaction can make the call fail for lack
of gas while using up the signature (documented).

`permissionHazards` is tested against `pinsArg` itself
(`test/formal/hazards-pins.spec.ts`): on random conditions over the signing
library's arguments, packed and unpacked as the contract does, the SDK never
reports a pin `pinsArg` rejects (three seeds of 3,000; it is stricter on
about 1% of the `types` cases).

See [`EndToEnd/README.md`](EndToEnd/README.md).

