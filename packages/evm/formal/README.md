# Formal verification of Roles v3

Machine-checked proofs (Lean 4) of properties of the Zodiac Roles Modifier
v3 contracts. Each property is one Lean library in this Lake package, with its
own README. This page tracks what is proven, in simplified notation; the
Lean statements are the authoritative versions.

```
cd packages/evm/formal
lake build                 # checks every proof (Lean 4.35 via elan, no Mathlib)
```

A successful build means every theorem below is proven. There is no `sorry`,
`admit` or custom `axiom`; the theorems depend only on Lean's standard axioms
(`propext`, `Classical.choice`, `Quot.sound`).

## Status

| Property                                                                                                                                                     | Library                                                | Status |
| ------------------------------------------------------------------------------------------------------------------------------------------------------------ | ------------------------------------------------------ | ------ |
| [Decoder faithfulness](#decoder-faithfulness): on correctly encoded calldata, every condition checks exactly the bytes the ABI spec assigns to its parameter | [`DecoderFaithfulness`](DecoderFaithfulness/README.md) | Proven |

Not covered yet:

- **Integrity ⇒ `Desc`.** That `Integrity.enforce` only accepts condition
  trees that describe some ABI type. Decoder faithfulness assumes it.
- `ZipSome`/`ZipEvery`, `BitmaskChecker` internals, and what comparison
  operators do with their operand (`__compare`, keccak).
- **Malformed calldata.** Whether Roles and the target contract decode
  non-canonical encodings the same way. Not planned for now; it depends on
  each target's decoder.
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
| $`(d, \ell, p) \in \mathsf{Visit}(\mathsf{cd}, c)`$                                                | evaluating $`c`$ on $`\mathsf{cd}`$ reaches node $`d`$ at byte $`\ell`$ along child-index path $`p`$                                                                       |
| $`v\vert_p`$                                                                                       | the component of $`v`$ at path $`p`$ (tuple field / array element / argument $`i`$ per step)                                                                               |
| $`\mathsf{content}(u)`$                                                                            | the 32-byte word of a static $`u`$, or the bytes of a `bytes`/`string` value without length word and padding                                                               |
| $`w \sqsubseteq x`$                                                                                | $`w`$ is a contiguous part of $`x`$                                                                                                                                        |

## Decoder faithfulness

[Details](DecoderFaithfulness/README.md) · Lean: `DecoderFaithfulness/Main.lean`

All theorems share the hypotheses

```math
\mathsf{Desc}_s(c, v), \qquad \mathsf{RootOK}(c), \qquad |\mathsf{cd}| < 2^{255}, \qquad (d, \ell, p) \in \mathsf{Visit}(\mathsf{cd}, c), \qquad u = v|_p
```

where $`\mathsf{RootOK}(c)`$ says the root is `AbiEncoded`, possibly under
`And`/`Or`. In short:

```math
\mathsf{cd} = \mathit{pre} \mathbin{+\!\!+} \mathsf{enc}(\vec a) \mathbin{+\!\!+} \mathit{sfx}
\;\Longrightarrow\;
\forall (d, \ell, p) \in \mathsf{Visit}:\;
\mathsf{cd}[\ell, |\mathsf{enc}(v|_p)|] = \mathsf{enc}(v|_p)
\;\wedge\; \mathsf{input}(d) = \mathsf{enc}(v|_p)
\;\wedge\; \text{no false } \texttt{CalldataOverflow}
```

The exact statements also cover nodes below `Slice` (windows), nodes that
never read calldata, and interpretations that don't fit the data. Each
theorem ends with **or (iv)**: with $`s = \mathsf{true}`$, $`d`$ may lie inside
an interpretation that does not fit the data. That interpretation's root
sits exactly at the right `bytes` value, but nothing is promised inside it.
With $`s = \mathsf{false}`$, (iv) is impossible (`InStray.strict`).

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

For every `EqualTo`, `GreaterThan`, `LessThan`, signed
comparison, `WithinAllowance` or `Pluck` node $`d`$, one of:

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

For a `Custom` node $`d`$, the $`(\mathit{location}, \mathit{size})`$
passed to the checker is one of:

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
nested calldata. By `decoder_locations`, each $`\ell_i`$ is then where the
spec put component $`i`$.

### `decoder_slice`: `Slice` rejects exactly when the spec window doesn't exist

For a `Slice` node $`d`$, the length $`L`$ that `_slice` checks
$`\mathit{shift} + \mathit{size} \le L`$ against is:

```math
L = |\mathsf{content}(u)|
\qquad\text{or}\qquad
L = |w| \text{ for the enclosing window } w \sqsubseteq \mathsf{content}(u) \text{ (nested }\texttt{Slice}\text{)}
\qquad\text{or (iv)}
```

### Trusted base

- `Roles.lean` matches the Solidity. It's a hand transcription, tested
  against the contracts by `test/formal/lean-model.spec.ts`.
- `Spec.lean` matches the Solidity docs' formal ABI encoding (about 40
  lines).
- Integrity only accepts trees with $`\mathsf{Desc}_s`$ and
  $`\mathsf{RootOK}`$ (not proven yet).
- The Lean 4.35 kernel.

## Layout

| Path                   | Contents                                                                                    |
| ---------------------- | ------------------------------------------------------------------------------------------- |
| `lakefile.toml`        | The Lake package: one `lean_lib` per property, plus the `roles-model` test driver           |
| `DecoderFaithfulness/` | Decoder faithfulness: models, proofs, examples, README                                      |
| `Diff.lean`            | `roles-model` executable: runs the Lean decoder model on queries from the differential test |
| `../test/formal/`      | Tests of the Lean models against the Solidity contracts                                     |

To add a property, add a `[[lean_lib]]` to `lakefile.toml` and append its name
to `defaultTargets`. Then add a row to the status table and a section with
its theorems here.
