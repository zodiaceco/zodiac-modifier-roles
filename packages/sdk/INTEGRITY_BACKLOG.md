# Integrity backlog: extra checks for the SDK

On-chain, `Integrity.enforce`
(packages/evm/contracts/core/serialize/Integrity.sol) is the only gate between a
condition tree and `evaluate`, and only on the validated setters (`allowTarget`,
`allowFunction`, `scopeFunction`, ...): the `...Packed` setters store a buffer
without running it. Some trees pass Integrity but are not read the way their
author meant: `evaluate` checks the wrong bytes (a policy bypass) or rejects
calls it should allow. This file lists those shapes. Each entry should become a
check in the SDK's `checkConditionIntegrity`
(src/main/condition/conditionIntegrity.ts), so that the SDK refuses to produce
them, and ideally a fix in the contracts.

Sources: the decoder proof in packages/evm/formal (its hypotheses say which
trees it covers), a fuzzer that compares `evaluate` with a reference evaluator
on Integrity-accepted trees (packages/evm/test/formal/integrity-gaps.spec.ts),
and targeted on-chain probes through `MockEvaluator` (Integrity → pack → unpack
→ evaluate).

Severity:

- **bypass**: a call the author meant to forbid is allowed.
- **false reject**: a call the author meant to allow is rejected (fails safe).
- **usability**: a legitimate tree cannot be stored.

| #   | Shape                                            | Severity     | Status                           |
| --- | ------------------------------------------------ | ------------ | -------------------------------- |
| 0   | SDK checker predates v3                          | prerequisite | —                                |
| 1   | Zip anywhere but under And/Or only               | bypass       | confirmed on-chain (5 shapes)    |
| 2   | Non-structural child in a Pass/EqualTo container | false reject | confirmed (fuzzer + on-chain)    |
| 3   | Integrity gas grows ~3× per nesting level        | usability    | measured                         |
| 4   | `Slice` and plain checks can't share an And/Or   | usability    | confirmed (Integrity rejects)    |
| 5   | Checks below Pass/EqualTo/Custom/Pluck never run | lint         | by design, easy to misread       |
| 6   | Root encoding not checked on-chain               | low          | code reading; SDK already checks |

## 0. The SDK checker predates v3

`conditionIntegrity.ts` and the SDK's `Operator`/`Encoding` enums know none of
`Pluck`, `ZipSome`, `ZipEvery` or `EtherValue`, and the rules differ from
`Integrity.sol` in other places. Before adding the checks below, port
`Integrity.enforce` to the SDK (or run `packConditions` via `eth_call`), so that
the SDK at least rejects what the chain rejects.

## 1. Zip anywhere but under And/Or only (bypass)

`TypeTree` counts a `ZipSome`/`ZipEvery` node as structural (its hash is
non-zero), so Integrity accepts it wherever a parameter may stand. But a Zip
reads its arrays from Pluck slots, not from its position. Wherever it sits
inside a type node, `AbiLocation` and `Topology` give it a parameter slot or an
inline size of its own, and later reads shift.

Confirmed on-chain (2026-10-20):

| Shape                                                                                     | Effect                                                                         |
| ----------------------------------------------------------------------------------------- | ------------------------------------------------------------------------------ |
| `f(uint256[] a, uint256[] b, uint256 c)`, `Matches[Pluck a, Pluck b, Zip, EqualTo(c, 5)]` | `EqualTo` reads `a[0]`: `a = [5], c = 999` passes; `c = 5` is rejected         |
| same inside a nested tuple: `f((uint256[], uint256[], uint256))`                          | same: `a = [5], c = 999` passes                                                |
| Zip inside a static tuple: `Matches[Pluck a, Pluck b, Tuple[Static, Zip], EqualTo(c, 5)]` | the tuple's inline size grows by the Zip's fields, `c` is read from `a`'s tail |
| `f(.., bytes[] c)`, `ArrayTailMatches[EqualTo(“ok”), Zip]` (meant: last element is “ok”)  | the check reads the second-to-last element: `c = ["ok", "evil"]` passes        |
| `ArrayTailMatches[Zip, EqualTo(“ok”)]`                                                    | the Zip is the element template, locations are wrong: `["ok", "evil"]` passes  |
| trailing Zip over dynamic fields (`f(bytes[], bytes[])`)                                  | every call fails with `CalldataOverflow`                                       |

Roles' own tests use the trailing-`Matches`-child form, which only works when
the Zip's fields are static and the container is not inline. The form that is
always correct (and the only one the decoder proof covers) is a Zip whose
ancestors are all `And`/`Or`, for example
`And[Matches[Pluck a, Pluck b, ...], ZipEvery(...)]`, with the Zip after the
sibling that describes the value. One consequence: a Zip over arrays plucked
inside each element of an outer array (per-element zip) has no correct form
today.

SDK check: every ancestor of a Zip is an `And` or `Or`. Contract fix: make
`TypeTree.hash` return 0 for a Zip, so Integrity rejects it among positional
children, and have `Topology`/`AbiLocation` give it no slot and no size.

## 2. Non-structural child in a Pass/EqualTo container (false reject)

`Matches` and the array iterators require all children to be structural. `Pass`,
`EqualTo` and `Custom` on a `Tuple` or `Array` only require at least one. A
non-structural child (an `EtherValue` comparison, `Empty`, or an And/Or of
those) is then counted by `AbiLocation.size`: it has inline size 0, so the
unpacker marks it as not inline and `size` reads an offset for it. As the first
child of an `Array` it becomes the element template.

Found by the fuzzer (tags `np-in-EqualTo-tuple`, `np-in-Pass-tuple`,
`np-in-EqualTo-array-first`): `EqualTo` on the container or on an ancestor
hashes the wrong range, so calls are rejected with `ParameterNotAllowed` or
`CalldataOverflow`. For `f((bytes))` the size is 261 bytes instead of 96.

This fails safe for `EqualTo`: the hashed range can only equal the expected
encoding if it is that encoding. `Custom` receives the wrong size, so a custom
checker could misjudge it.

SDK check: every child of a `Tuple`, `Array` or `AbiEncoded` node is structural,
whatever the operator.

## 3. Integrity gas grows ~3× per nesting level (usability)

`TypeTree.resolve` and `hash` re-resolve each subtree at every level, and
Integrity calls them for every node. Gas for `MockPackerUnpacker.roundtrip`
(Integrity + pack + unpack):

| depth (a chain of nested tuples) | 4    | 5    | 6    | 7    | 8     |
| -------------------------------- | ---- | ---- | ---- | ---- | ----- |
| gas                              | 0.3M | 0.7M | 1.8M | 5.3M | > 16M |

With two children per level, depth 7 already needs 12M. Since Fusaka (EIP-7825)
one transaction may use at most 2^24 ≈ 16.8M gas, so a validated setter cannot
store a tree nested 8 levels deep, however few nodes it has. And/Or wrappers and
nested calldata add levels quickly. About a third of the fuzzer's random trees
(depth ≥ 7) ran out of gas.

SDK check: estimate the depth and warn before a setter would exceed the cap;
fall back to `...Packed` setters with `packConditions` via `eth_call` (RPC gas
caps are usually higher). Contract fix: memoize hashes per node within
`enforce`.

## 4. Slice and plain checks can't share an And/Or (usability)

A `Slice` node's type hash includes its child, so `Slice:Static` differs from
`Static`. `And[Slice:Static(...)[...], EqualTo:Static(...)]` on the same word is
rejected with `UnsuitableChildTypeTree`. For `Dynamic` the same shape is
accepted, because both sides count as "dynamic-ish". Safe, but inconsistent.

SDK: mirror the rule (so the error shows up early), or the contract ignores a
Slice's child in `TypeTree.hash`.

## 5. Checks below Pass/EqualTo/Custom/Pluck never run (lint)

Children of `Pass`, `EqualTo`, `Custom` and `Pluck` only describe the type;
`evaluate` never visits them. Integrity accepts any operator there, so
`Pass:Tuple[EqualTo:Static(5)]` passes every value. This is by design, but an
author can easily expect the inner check to apply.

SDK check: below those operators, only `Pass` (and the structure) is allowed, or
warn.

## 6. Root encoding not checked on-chain (low)

Integrity does not require the root to be `AbiEncoded` (or a logical node over
`AbiEncoded` nodes). A root `Tuple` reads the selector as part of the first
word. A root-level `Dynamic` variant (`Or[AbiEncoded…, Slice:Dynamic…]`) reads
the first calldata word as a length and slices 32 bytes too far. The SDK's
`checkRootConditionIntegrity` already requires an `AbiEncoded` root type, but it
still accepts the `Dynamic` variant beside it. Keep the root check when porting
(item 0), and reject `Dynamic` at the root.

## Running the fuzzer

```
cd packages/evm
GAP_CASES=2000 npx hardhat test test/formal/integrity-gaps.spec.ts
GAP_CASES=300 GAP_CLEAN=1 npx hardhat test test/formal/integrity-gaps.spec.ts  # reference sanity check
```

Mismatches are grouped by the tags of the shapes the generator added. In clean
mode (only shapes inside the decoder proof's hypotheses) it should report none.
