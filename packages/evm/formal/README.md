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
| [Evaluation on calldata](#evaluation-on-calldata): the evaluator computes the contract world's meaning, which satisfies normalization's assumptions             | [`Bridge`](Bridge/)                                    | Proven |
| [Normalization on calldata](#normalization-on-calldata): the contract gives the normalized tree the verdict it gives the tree as written                          | [`Bridge`](Bridge/)                                    | Proven |
| [SDK pipeline](#the-sdk-pipeline-end-to-end): normalize → flatten → pack → unpack → evaluate agrees with evaluating the user's tree                               | [`Bridge`](Bridge/)                                    | Proven |
| [Evaluator model](#the-evaluator-model): `Evaluate/Model.lean` against `ConditionEvaluator.evaluate`                                                             | [`Evaluate`](Evaluate/)                                | Tested |

Not covered yet:

- **Integrity ⇒ `Desc`, `ZipOK`.** That `Integrity.enforce` only accepts
  condition trees that describe some ABI type, and enforces the Zip type rules.
  Decoder faithfulness assumes it, and it is false today: trees Integrity
  accepts but `evaluate` misreads are tracked in
  [packages/sdk/INTEGRITY_BACKLOG.md](../../sdk/INTEGRITY_BACKLOG.md), found
  with the fuzzer `test/formal/integrity-gaps.spec.ts`. The
  [condition check](#condition-check) proves the hypotheses for every tree it
  accepts instead, for clients that store trees with the `...Packed` setters.
- **Pluck slots, fully.** That the slot a Zip reads holds the location where a
  Pluck with that index was evaluated. The decoder model assumes it. The
  condition check proves no unwritten slot is read, against a model of
  `evaluate`'s control flow (`Run`); that `Run` matches the Solidity is
  trusted.
- **Integrity ⇒ `Packable`.** The condition packing theorem assumes the width,
  order and compValue checks listed in its
  [README](ConditionPacking/README.md#hypotheses-packable-and-where-integrity-checks-them);
  that Integrity enforces them is from reading the code, not proven.
- What `WithinRatio`, `Custom` checkers and allowances do with their
  operands. (`Bitmask` and the comparison operators are proven, the latter
  assuming keccak256 has no collisions.)
- A Zip inside a type node (only a Zip whose ancestors are all `And`/`Or` is
  modeled). Integrity accepts such trees, but the decoder gives the Zip a
  parameter slot or inline size: later parameters are read at the wrong place (a
  policy bypass, reproduced on-chain), and a Zip over dynamic fields falsely
  overflows. See the [details](DecoderFaithfulness/README.md#not-covered) and
  the backlog.
- **Malformed calldata.** Whether Roles and the target contract decode
  non-canonical encodings the same way. Not planned for now; it depends on each
  target's decoder.
- The rest of the contract: authorization flow, memberships, allowances,
  unwrappers.

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
  $`\mathsf{ZipOK}_s`$ (not proven yet).
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
`array`, `call lb ts`), non-structural, or a Zip. Containers need structural
children of the right types, a Zip may only be a child of `And`/`Or` (after
the child that describes the value, and only over a dynamic value), and each
Pluck a Zip reads is an array whose element type fits the field. The check
returns the root's type, or that the root reads no calldata.

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
$`|\mathit{pre}| = lb`$ and each argument has its type. Nested calldata has its
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
end to end), assuming keccak256 has no collisions.

### Findings

Where Integrity and the check differ (details in the
[README](ConditionCheck/README.md#findings-where-integrity-and-the-check-differ)):
Integrity accepts trees `evaluate` misreads (backlog items 1, 2, 6), and
rejects two shapes that are read correctly: `Slice` next to plain checks
(item 4) and a Zip next to a `Tuple`/`Array` check (item 10). Unique Pluck
indices are not needed for safe decoding.

### Trusted base

- The decoder and packing proofs' trusted bases.
- `Run` (`Slots.lean`) matches `evaluate`'s control flow, and `_pluck` is the
  only writer of the slots.
- `comparePasses` matches `__compare`/`__compareSigned`; keccak256 has no
  collisions (for `EqualTo`).
- The fuzzer (`GAP_CHECK=1`) also evaluates every accepted tree without
  Integrity and compares with a reference evaluator.

## Normalization

[Details](Normalize/README.md) · Lean: `Normalize/Sound.lean`

The SDK normalizes every condition before it is stored (`normalizeCondition`:
prune trailing `Pass` nodes, pad branches to one type tree, flatten, dedupe and
unwrap `And`/`Or`, push `Or` down into `Matches`/`And`, sort). `Normalize/Defs.lean`
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
through their meanings; ignore trailing `Pass` children of tuple and calldata
nodes (they describe type); write slots only if `Pluck`; charge only if
`Custom`, `WithinAllowance` or `CallWithinAllowance`; and choose between
charges depending on earlier ones only if `ArraySome` or `ZipSome`. Charges
commute, which `consume_comm` proves of `AllowanceConsumer.consume`.

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
    next to a plain check), which Integrity rejects; merges now require
    Integrity's type compatibility (`compatibleSiblings`, the contract's
    `TypeTree` rule).
12. `createTypeTree` gave an `And`/`Or` the type of its first child, and none
    when that child reads no parameter, so the parent's type tree lost a field;
    it now takes the first structural child, as the contract's `TypeTree` does.
    The SDK also crashed on such nodes while padding.

By design, not changed: `Pass` places no constraint on a value, including
whether it is well-formed. A trailing `Pass` still makes the contract locate
the field (follow its offset), so on a malformed encoding the tree as written
can fail where the pruned one passes. Example: `f(bytes b)` with
`Matches:AbiEncoded[EqualTo(1), Pass:Dynamic]` on `b` fails on
`b = abi.encode(1)` (`CalldataOverflow`), its normalized form
`Matches:AbiEncoded[EqualTo(1)]` passes. Roles never checks ABI
well-formedness (a `Pass:Static` field is not read, trailing data and
non-canonical offsets are accepted), so this side effect is not a check to
rely on. On top-level calldata a Solidity target rejects such calldata
anyway. The theorems below hold on calldata that decodes as the parameter's
full type (`Decodable`), which excludes exactly these cases; padding, the
other way round, can make a branch fail on them.

## Evaluation on calldata

Lean: `Evaluate/Model.lean`, `Bridge/`

`Evaluate/Model.lean` transcribes `ConditionEvaluator.evaluate` (every
operator, with `AllowanceConsumer`, `WithinAllowanceChecker` and the custom
checker's charges). What it reads from outside (`msg.value`, accrued
allowance balances, custom checkers, price adapters, `WithinRatio`) is a
parameter, assumed only to never report `Ok` as a failure or a revert
(`EnvOk`).

The **contract world** (`Bridge/World.lean`) is the evaluator as a
normalization world: a value is a layout (a `Condition` whose `inlined`,
`size`, `leadingBytes` and children give the encoding) and a location;
children are decoded with `AbiLocation` using the layout's metadata, so the
world does not depend on the tree.

### `contractWorld_ok`: the normalization proof's assumptions hold

The five assumptions `World.Ok` of `normalize_sound` are theorems for the
contract world: charges commute (consumptions as a map from allowance key to
balance and consumed), a trailing `Pass` does not change a tuple or calldata
operator, only `Pluck` writes slots, only `Custom`, `WithinAllowance` and
`CallWithinAllowance` charge, only `ArraySome`/`ZipSome` choose.

### `adequacy`: the evaluator computes the world's meaning

`Fits c d m`: the tree `c` (evaluated as node `d`) fits layout `m`: every
structural node has `m`'s `inlined` and `size`; containers list `m`'s
children (a `Matches` on calldata or a dynamic tuple may leave out trailing
ones); checks on a whole value see exactly `m`'s type. Zips are not covered.
`Decodable data m l`: decoding the calldata with `m` at `l` does not
overflow, all the way down. `CvOk n c`: no compValue the evaluator reverts on.

```math
\mathsf{Fits}(c, D(c), m) \wedge \mathsf{Decodable}(\mathit{cd}, m, \ell) \wedge \mathsf{CvOk}_n(c)
\;\Longrightarrow\;
\mathsf{evaluate}(\mathit{cd}, \ell, D(c), \kappa, \sigma) \sim [\![c]\!]_{\mathsf{contract}}((m, \ell), \sigma, \kappa)
```

where $`\sim`$: same slots; both pass with the same consumptions (as a map),
or both fail; no revert.

## Normalization on calldata

Lean: `Bridge/Final.lean`, `Bridge/Preserve.lean`, `Bridge/PadFits.lean`

### `normalize_fits`: normalization keeps the layout

```math
\mathsf{Fits}(c, D(c), m) \;\Longrightarrow\; \mathsf{Fits}(\mathsf{normalize}_k(c), D(\mathsf{normalize}_k(c)), m)
```

Pruning drops trailing `Pass` children of containers that are not inlined,
padding appends `Pass` children of the layout's types to such containers, and
every rewrite of `And`/`Or` keeps each branch at the layout. Also
`cvOk_normalize`.

### `normalize_calldata'`: the contract's verdict does not change

For a tree that fits layout $`m`$, on every calldata that decodes as $`m`$:

```math
\mathsf{evaluate}(\mathit{cd}, \ell, D(\mathsf{normalize}_k(c)), \kappa, \sigma) \;\approx\; \mathsf{evaluate}(\mathit{cd}, \ell, D(c), \kappa, \sigma)
```

($`\approx`$: same verdict, same consumptions as a map, same slots, no revert),
from `adequacy` for both trees, `normalize_fits` and `normalize_sound` with
`contractWorld_ok`.

Not covered: trees with call interpretations of different types under one
`Or` (they do not fit one layout; the contract reads the interpretation that
does not hold as whatever its bytes are). They are covered by the on-chain
fuzzer only. Zips.

## The SDK pipeline, end to end

Lean: `Bridge/Pipeline.lean`

### `sdk_pipeline`

The SDK normalizes the user's tree $`c_0`$, flattens it to $`\mathit{fs}`$ and
stores `pack(fs)`; the contract unpacks and evaluates. If $`\mathit{fs}`$ is
`Packable` (which `checkStored` proves) and reads back as
$`\mathsf{normalize}_k(c_0)`$ (`nest`: node $`i`$'s children are the later nodes
whose parent is $`i`$), then for every calldata that decodes as the layout
$`c_0`$ fits:

```math
\mathsf{run}(\mathit{cd}, \mathsf{unpack}(\mathsf{pack}(\mathit{fs}))) \;\approx\; \mathsf{run}(\mathit{cd}, D(c_0))
```

The contract enforces exactly what it would enforce for the tree as written.
Chains `pack_roundtrip`, `unpacked_eq` (the unpacked tree is $`D`$ of the tree
read back), `normalize_calldata'`.

Trusted: that `flattenCondition` produces an array that reads back as its
input (tested through the driver's `buildCond` in the normalization and check
differential tests); `EnvOk`; the evaluator transcription (next section).

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
3,000 cases: 1,220 compared, 0 differences. 167 trees the SDK check accepts
and Integrity rejects (`UnsuitableChildTypeTree`) were evaluated too; all
fall in the three documented classes (`ConditionCheck/README.md`), one of
them new.

Found: `AbiLocation.children` allocates the location array before decoding,
so an array length above $`2^{64}-1`$ panics there; the decoder transcription
reports an overflow (both deny). The evaluator model has the panic.

## Mutation testing

`node test/formal/mutate.mjs <normalize|check|pack>` changes one operator,
comparison or early return at a time in the SDK code the differential tests
cover and reports the mutants the test does not notice. Last run: normalize
186 of 239 killed (most survivors are equivalent, e.g. `invariant` conditions
and sort ties, or in the packed `conditionId` this test does not cover),
check 389 of 425 (most survivors are equivalent rewrites or sit at
Packable size limits the generators rarely reach), pack 7 of 9 (survivors in the `checkAndPack`
wrapper).

## Layout

| Path                   | Contents                                                                             |
| ---------------------- | ------------------------------------------------------------------------------------ |
| `lakefile.toml`        | The Lake package: one `lean_lib` per property, plus the `roles-model` test driver    |
| `DecoderFaithfulness/` | Decoder faithfulness: models, proofs, examples, README                               |
| `ConditionPacking/`    | Condition packing: byte-level pack/unpack model, round-trip proof, README            |
| `ConditionCheck/`      | Condition check: the decidable check, its soundness, end-to-end theorem, README      |
| `Normalize/`           | Normalization: transcription of the SDK's normalizeCondition, semantics, proof       |
| `Evaluate/`            | Transcription of `ConditionEvaluator.evaluate` (differentially tested)               |
| `Bridge/`              | The contract world, adequacy, normalization on calldata, the SDK pipeline            |
| `Diff.lean`            | `roles-model` executable: runs the Lean models on queries from the differential test |
| `../test/formal/`      | Tests of the Lean models against the Solidity contracts                              |

To add a property, add a `[[lean_lib]]` to `lakefile.toml` and append its name
to `defaultTargets`. Then add a row to the status table and a section with its
theorems here.
