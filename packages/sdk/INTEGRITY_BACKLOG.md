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

The Lean check `checkStored` (packages/evm/formal/ConditionCheck) is the
specification for the SDK's check on a flat array before a `...Packed` setter.
It covers `Packable`, Integrity's operator rules, the Pluck-slot rule and the
type rules, and is proven to give the decoder proof's hypotheses. It rejects
items 1, 2 and 6, accepts the safe shapes of items 4 and 10, and covers item 7.
The SDK implements it in src/main/condition/checkStored.ts, differentially
tested against the Lean definition (packages/evm/test/formal/sdk-check.spec.ts).
It is not wired into the SDK's apply flow yet.

Severity:

- **bypass**: a call the author meant to forbid is allowed.
- **false reject**: a call the author meant to allow is rejected (fails safe).
- **usability**: a legitimate tree cannot be stored.

| #   | Shape                                            | Severity     | Status                             |
| --- | ------------------------------------------------ | ------------ | ---------------------------------- |
| 0   | SDK checker predates v3                          | prerequisite | —                                  |
| 1   | Zip anywhere but under And/Or only               | bypass       | confirmed on-chain (5 shapes)      |
| 2   | Non-structural child in a Pass/EqualTo container | false reject | confirmed (fuzzer + on-chain)      |
| 3   | Integrity dominates storing cost, hits tx cap    | usability    | measured                           |
| 4   | `Slice` and plain checks can't share an And/Or   | usability    | confirmed (Integrity rejects)      |
| 5   | Checks below Pass/EqualTo/Custom/Pluck never run | lint         | by design, easy to misread         |
| 6   | Root encoding not checked on-chain               | low          | code reading; SDK already checks   |
| 7   | `...Packed` setters skip every check             | prerequisite | code reading; proven what to check |
| 8   | `Custom` checkers can read unwritten Pluck slots | lint         | code reading                       |
| 9   | Integrity rules not needed for safe decoding     | info         | proof                              |
| 10  | Zip next to a `Tuple`/`Array` check is rejected  | usability    | fuzzer (checker mode)              |

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

## 3. Integrity dominates the cost of storing permissions (usability)

`TypeTree.resolve`/`hash` re-resolve each subtree at every level and Integrity
calls them for every node, so its gas grows ~3× per nesting level and roughly
quadratically with the number of nodes. Measured on a local chain (2026-10-20),
all leaves `EqualTo` with a 32-byte compValue. Integrity, pack and store are
measured inside one call with `gasleft()`; the setters are full transactions:

| tree                                                     | nodes | depth | Integrity | pack | store | `allowFunction` | `allowFunctionPacked` | Integrity share |
| -------------------------------------------------------- | ----- | ----- | --------- | ---- | ----- | --------------- | --------------------- | --------------- |
| chain of nested tuples                                   | 4     | 4     | 197k      | 29k  | 51k   | 330k            | 90k                   | 60%             |
|                                                          | 6     | 6     | 1.7M      | 75k  | 53k   | 1.9M            | 92k                   | 90%             |
|                                                          | 8     | 8     | 15.9M     | 158k | 56k   | 16.2M           | 94k                   | 98%             |
|                                                          | 9     | 9     | 54.9M     | 217k | 59k   | over the cap    | 95k                   | —               |
| binary tuple tree                                        | 16    | 5     | 6.1M      | 392k | 109k  | 6.7M            | 154k                  | 91%             |
|                                                          | 32    | 6     | 54.3M     | 1.7M | 183k  | over the cap    | 230k                  | —               |
| flat: one call, n static params                          | 11    | 2     | 285k      | 91k  | 118k  | 577k            | 165k                  | 49%             |
|                                                          | 51    | 2     | 4.0M      | 1.4M | 424k  | 6.0M            | 507k                  | 66%             |
|                                                          | 101   | 2     | 14.4M     | 5.1M | 808k  | over the cap    | 935k                  | —               |
| `Or` of b calls with 3 params                            | 17    | 3     | 1.1M      | 140k | 139k  | 1.4M            | 188k                  | 74%             |
|                                                          | 65    | 3     | 10.9M     | 1.4M | 436k  | 13.0M           | 518k                  | 83%             |
| `Or` of b calls, each with a tuple param holding an `Or` | 33    | 5     | 6.4M      | 519k | 208k  | 7.3M            | 264k                  | 88%             |
|                                                          | 65    | 5     | 19.9M     | 1.7M | 377k  | over the cap    | 449k                  | —               |

"Over the cap" means more than 2^24 ≈ 16.8M gas, the per-transaction limit since
Fusaka (EIP-7825). Takeaways:

- Above ~10 nodes Integrity is most of a validated setter's cost, above ~30
  nodes (or depth 6) it is 80–98%. Storing the same tree with the `...Packed`
  setter costs 5–70× less.
- Validated setters fail beyond depth 8, or around 65–100 nodes, which realistic
  `Or`-heavy permissions reach. `packConditions` via `eth_call` runs the same
  code; at depth 10 or 200 flat params it exceeds 60M, more than many RPC gas
  caps allow.
- Packing is also superlinear (5.1M for 101 nodes), but an order of magnitude
  below Integrity.

SDK: run Integrity locally (item 0) and apply with `...Packed` setters, so its
cost never lands on-chain; warn when a tree would not fit a validated setter.
Contract fix: memoize type hashes per node within `enforce` and avoid the
per-node `childBounds` scans; Integrity should then be roughly linear.

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

## 7. `...Packed` setters skip every check (prerequisite)

`allowTargetPacked`, `allowFunctionPacked` and `allowFunctionGloballyPacked`
store a buffer as given; `MalformedConditionBuffer` is never raised. Besides
the shapes above, a client that builds buffers must itself enforce what the
packer and unpacker rely on (`Packable` in
packages/evm/formal/ConditionPacking: BFS order, field widths, Pluck index
≤ 254, `AbiEncoded` and `EqualTo` compValue shapes; otherwise the buffer
decodes to a different tree) and that every slot a Zip or `WithinRatio` reads
is written first (an unwritten slot reads as location 0: the Zip decodes an
array at the start of calldata).

SDK check: `checkStored` (all of it). Its parts are proven sufficient:
`packableB_sound`, `run_sound`, `checkCondition_sound`.

## 8. `Custom` checkers can read unwritten Pluck slots (lint)

`Custom` receives `context.pluckedValues`, but nothing says which slots a
checker reads, so Integrity cannot require them to be written. A checker that
reads a slot no Pluck wrote on the current path sees zero.

SDK: document for custom checker authors; optionally let the author declare
the slots a `Custom` node reads and check them like `WithinRatio`'s.

## 9. Integrity rules not needed for safe decoding (info)

The proof of the condition check shows that some rules Integrity enforces are
not needed for `evaluate` to read the right bytes. The SDK check keeps them,
since they catch likely mistakes:

- `DuplicatePluckIndex`: with two Pluck nodes on one slot, a Zip reads
  whichever ran last; both are constrained by the Zip type rule, so the read
  is still correct.
- A Zip needs at least two arrays (`ArraySome`/`ArrayEvery` cover one).

Items 4 and 10 are the rules found that reject trees the decoder reads
correctly and that an author would want.

## 10. Zip next to a `Tuple`/`Array` check is rejected (usability)

`_validateVariantTypes` treats a Zip as a typed sibling in an `And`/`Or`,
compatible only with `Dynamic`/`AbiEncoded` siblings. So
`And[Matches:Tuple[..., a[], b[]], ZipEvery(...)]` on a dynamic tuple
parameter is rejected with `UnsuitableChildTypeTree`, although the decoder
reads it correctly (the checker-mode fuzzer evaluates such trees without
Integrity and they match the reference). Only the root form
`And[Matches:AbiEncoded[...], Zip]` passes, so zipping arrays inside a tuple
parameter needs the Zip at the root.

SDK: `checkStored` accepts it (for `...Packed` setters). Contract fix: give a
Zip hash 0 in `TypeTree`, together with item 1.

## Running the fuzzer

```
cd packages/evm
GAP_CASES=2000 npx hardhat test test/formal/integrity-gaps.spec.ts
GAP_CASES=300 GAP_CLEAN=1 npx hardhat test test/formal/integrity-gaps.spec.ts  # reference sanity check
GAP_CASES=2000 GAP_CHECK=1 GAP_MUTATE=0.5 npx hardhat test test/formal/integrity-gaps.spec.ts  # the SDK check vs Integrity
```

Mismatches are grouped by the tags of the shapes the generator added. In clean
mode (only shapes inside the decoder proof's hypotheses) it should report none.
