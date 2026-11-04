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
| `Exclusive.lean`| `disjoint` branches never both pass (`disjoint_sound`); an `Or` that `canReorderOr` allows means the same in every order (`orT_perm`); the rule does not depend on the order (`canReorderOr_perm`) |
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
`World.NormOk.twin` assumes that two `Matches` with the same encoding and
compValue, over children of the same types position by position
(`twinCh`), read the same fields; for the contract's reading it follows
from the children's layouts (`matchLocs_congr`, `sameType_lay`).

`World.Ok` collects what is assumed of the effects of `ext` and of charging. `comm` (charges
commute) holds for the contract's `consume` (`consume_comm`). The rest are
statements about operators normalization doesn't rewrite: only `Pluck` writes
slots; only `Custom`, `WithinAllowance`, `CallWithinAllowance` charge; and
only `ArraySome`, `ZipSome` (besides `Or`) choose a branch, so only they can
pick charges depending on earlier ones. `eqWord`: a static `EqualTo` with
no children on one 32-byte word (`pinned`) passes only on that word, so two
with different words never both pass on one value; for the contract's
reading, `Bridge.readWorld_eqWord` (both read the same word, which
`ConditionEvaluator` compares with `bytes32(compValue)`).

## Why each step is sound

| Step         | Argument                                                                                                                   |
| ------------ | -------------------------------------------------------------------------------------------------------------------------- |
| flatten      | `And`/`Or` are associative                                                                                                 |
| dedupe       | A duplicate that charges nothing (`And`) passed already; a duplicate in an `Or` failed already. Skipped next to `Pluck`s   |
| unwrap       | `And[x] = Or[x] = x`                                                                                                       |
| pushDownOr   | Distributivity: no slot writes, so re-running the shared children gives the same result; the hinge charges nothing         |
| sort         | `And`: children commute if no slot writes and (at most one charges, or none chooses). `Or`: no child writes slots, and no child charges or every charging child excludes every other child (same type, `disjoint`): then at most one branch passes from any state, so which one is first does not matter |

The `isStruct` side of `Same` keeps every rewrite from shifting the fields
later `Matches` siblings read.

## Exclusive `Or` branches

`disjoint a b` is syntactic: an `And` is disjoint from `b` if one of its
children is; an `Or` if all of its children are; two `Matches` on tuples or
calldata with the same encoding, the same compValue and children of the same
types position by position (`twinCh`) if two structural children at the
same position are (they read the same field, as `assign` pairs them); two
static `EqualTo`s on one word if the words differ. Anything else is not
disjoint. `disjoint_sound` holds for every value and any slots and
consumptions each side starts from, so it covers an `Or` that is not first
in its parent and branches whose earlier siblings consumed allowances.

Exclusivity is a property of the values Roles reads, so it holds on any
calldata, crafted encodings included: with exclusive branches at most one
passes, and the [TargetDecode finding](../TargetDecode/README.md#finding-the-caller-can-choose-the-or-branch)
(a caller choosing among overlapping branches with a non-canonical layout)
has no choice to offer. The rule is narrower than "never both pass": it
requires the same compValue on `Matches` (leading bytes and selector), no
children on the `EqualTo` (an `EqualTo` on a non-inlined node compares
something else), and `Matches` children that all have a type (in a
well-typed tree every child of a tuple or calldata reads a field).

## Testing the transcription

`packages/evm/test/formal/sdk-normalize.spec.ts` normalizes random trees with
the TypeScript and with `Normalize.normalize` (driver query `nz`) and compares.
Trees on which the TypeScript throws (`createTypeTree` on tuples without
structural children) are skipped; the transcription returns a result there. Deliberately broken transcriptions are caught (checked by mutating
`canReorderOr`, the hinge charge check and `mergeArrays`). The generator
builds `Or`s of capped branches that pin one field to a word, a set of
words or nothing (`cappedOr`), so the exclusivity rule sorts some and keeps
others; the test prints how many normalized trees have an `Or` with a
charging child (`cappedOr`) and how many of those the rule lets sort
(`cappedOrSorted`).
