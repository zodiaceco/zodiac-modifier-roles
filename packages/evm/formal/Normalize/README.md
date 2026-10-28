# Normalize: the SDK's normalization keeps the meaning

`normalizeCondition` (`packages/sdk/src/main/condition/normalize`) rewrites
every condition before the SDK stores it, so that equivalent conditions get
one form. This library proves the rewrites never change what a condition
means.

```
lake build Normalize
```

## Files

| File            | Contents                                                                                                        |
| --------------- | --------------------------------------------------------------------------------------------------------------- |
| `Defs.lean`     | The transcription: `flatten`, `dedupe`, `unwrap`, `pushDownOr`, `sortB`, `normalize` (with fuel)        |
| `Sem.lean`      | `sem`: the meaning of a condition; effect classes (`KeepsT`, `PureT`, `ChargerT`); `World.Ok`                    |
| `Effects.lean`  | The SDK's effect checks (`writes`, `charges`, `chooses`) imply effect classes; reordering lemmas                |
| `Steps.lean`    | Each of flatten, dedupe, unwrap, sort keeps the meaning                                                  |
| `PushDown.lean` | `pushDownOr` keeps the meaning (distributivity)                                                                 |
| `Sound.lean`    | `normalize_sound`; `consume_comm` (the contract's allowance charges commute)                                    |

## The semantics

`sem W c v sl cs` evaluates `c` on the decoded value `v`, with slots `sl`
(plucked values) and consumptions `cs` (allowance charges), and returns
`(some cs', sl')` (passes) or `(none, sl')` (fails). As in
`ConditionEvaluator`:

- `And`, `Matches`: children in order, stop at the first failure.
- `Or`: children in order from the same consumptions (copy-on-write), stop at
  the first success; slots written by a failed branch stay written.
- `Matches` on a tuple or calldata: structural children read the fields in
  order, non-structural children (encoding `None`/`EtherValue`, or `And`/`Or`
  with no structural child) read no field.
- Everything else is the world's `ext`, which gets the node itself (for what
  it reads of its own encoding and children) and its children's meanings.

`World.NormOk` assumes, among other things, that rewriting a node's children
does not change what `ext` does (`ext`). It also takes an invariant `inv` of
the trees, which `normalize_sound` requires of its input. For the contract's
reading both are proven on well-typed trees (`Bridge.readWorld_normOk`).

`World.Ok` collects what is assumed of the effects of `ext` and of charging. `comm` (charges
commute) holds for the contract's `consume` (`consume_comm`). The rest are
statements about operators normalization doesn't rewrite: only `Pluck` writes
slots; only `Custom`, `WithinAllowance`, `CallWithinAllowance` charge; and
only `ArraySome`, `ZipSome` (besides `Or`) choose a branch, so only they can
pick charges depending on earlier ones.

## Why each step is sound

| Step         | Argument                                                                                                                   |
| ------------ | -------------------------------------------------------------------------------------------------------------------------- |
| flatten      | `And`/`Or` are associative                                                                                                 |
| dedupe       | A duplicate that charges nothing (`And`) passed already; a duplicate in an `Or` failed already. Skipped next to `Pluck`s   |
| unwrap       | `And[x] = Or[x] = x`                                                                                                       |
| pushDownOr   | Distributivity: no slot writes, so re-running the shared children gives the same result; the hinge charges nothing         |
| sort         | `And`: children commute if no slot writes and (at most one charges, or none chooses). `Or`: if no child charges or writes   |

The `isStruct` side of `Same` keeps every rewrite from shifting the fields
later `Matches` siblings read.

## Testing the transcription

`packages/evm/test/formal/sdk-normalize.spec.ts` normalizes random trees with
the TypeScript and with `Normalize.normalize` (driver query `nz`) and compares.
Trees on which the TypeScript throws (`createTypeTree` on tuples without
structural children) are skipped; the transcription returns a result there. Deliberately broken transcriptions are caught (checked by mutating
`canReorderOr`, the hinge charge check and `mergeArrays`).
