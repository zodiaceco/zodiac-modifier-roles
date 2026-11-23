# Integrity backlog

What `Integrity.enforce`
(packages/evm/contracts/core/serialize/Integrity.sol) and the SDK's
`checkStored` (src/main/condition/checkStored.ts) still leave to the author of
a condition tree. Item numbers are kept from the original backlog, because
other files refer to them; the items that are resolved are listed at the end.

| #   | Shape                                            | Kind      | Status                            |
| --- | ------------------------------------------------ | --------- | --------------------------------- |
| 5   | Leaf checks below Pass/EqualTo/Custom/Pluck      | lint      | open: accepted, never evaluated   |
| 7   | `...Packed` setters skip every check             | by design | the client must run `checkStored` |
| 8   | `Custom` checkers can read unwritten Pluck slots | lint      | open                              |
| 9   | Integrity rules not needed for safe decoding     | info      | kept: they catch likely mistakes  |

## 5. Leaf checks below Pass/EqualTo/Custom/Pluck never run (lint)

Children of `Pass`, `EqualTo`, `Custom` and `Pluck` only describe the type;
`evaluate` never visits them. Integrity rejects a `Matches` or an `And`/`Or`
there (`UnsuitableChildTypeTree`), since those would not give the value's
size. It still accepts a leaf check, so `Pass:Tuple[EqualTo:Static(5)]` passes
every value. This is by design, but an author can easily expect the inner
check to apply.

SDK check: below those operators, only `Pass` (and the structure) is allowed, or
warn.

## 7. `...Packed` setters skip every check (by design)

`allowTargetPacked`, `allowFunctionPacked` and `allowFunctionGloballyPacked`
store a buffer as given. A client that builds buffers must itself enforce what
the packer and unpacker rely on (`Packable` in
packages/evm/formal/ConditionPacking: BFS order, field widths,
Pluck index ≤ 254, `AbiEncoded` and `EqualTo` compValue shapes; otherwise the
buffer decodes to a different tree), the type rules, and that every slot a Zip
or `WithinRatio` reads is written first (an unwritten slot reads as location 0:
the Zip decodes an array at the start of calldata).

SDK check: `checkStored` (all of it), which `checkAndPack`
(src/main/condition/packConditions.ts) runs before it packs. Its parts are
proven sufficient: `packableB_sound`, `run_sound`, `checkCondition_sound`.

## 8. `Custom` checkers can read unwritten Pluck slots (lint)

`Custom` receives `context.pluckedValues`, but nothing says which slots a
checker reads, so Integrity cannot require them to be written. A checker that
reads a slot no Pluck wrote on the current path sees zero.

SDK: document for custom checker authors; optionally let the author declare
the slots a `Custom` node reads and check them like `WithinRatio`'s.

## 9. Integrity rules not needed for safe decoding (info)

The proof of the condition check shows that two rules Integrity enforces are
not needed for `evaluate` to read the right bytes. Integrity and the SDK check
keep them, since they catch likely mistakes:

- `DuplicatePluckIndex`: with two Pluck nodes on one slot, a Zip reads
  whichever ran last; both are constrained by the Zip type rule, so the read
  is still correct.
- A Zip needs at least two arrays (`ArraySome`/`ArrayEvery` cover one).

## Resolved

Integrity was rewritten to follow the rules of `checkStored`. The packer now
walks the nodes in linear time. Integrity still compares sibling types, which
can require quadratic work for wide `And` or `Or` nodes. Checked on
2026-11-19 by running each named shape through `Roles.packConditions`, and with
the fuzzer below (2,000 cases: 777 trees accepted, 720 compared with the
reference evaluator, no mismatch, none out of gas).

| #   | Shape                                            | Was          | Now                                                                                             |
| --- | ------------------------------------------------ | ------------ | ----------------------------------------------------------------------------------------------- |
| 0   | SDK checker predates v3                          | prerequisite | the SDK has `checkStored` and `checkAndPack`                                                    |
| 1   | Zip anywhere but under And/Or only               | bypass       | Integrity rejects a Zip inside a call, tuple or array (`UnsuitableChildCount`)                  |
| 2   | Non-structural child in a Pass/EqualTo container | false reject | Integrity rejects it (`UnsuitableChildCount`)                                                   |
| 3   | Integrity dominates storing cost, hits tx cap    | usability    | `allowFunction`: 9 nested tuples 267k gas, 100 flat checks 2.74M (both were over the 16.8M cap) |
| 4   | `Slice` and plain checks can't share an And/Or   | usability    | Integrity accepts it                                                                            |
| 6   | Root encoding not checked on-chain               | low          | a root `Tuple` or a `Dynamic` variant at the root is rejected (`UnsuitableRootNode`)            |
| 10  | Zip next to a `Tuple`/`Array` check is rejected  | usability    | Integrity accepts it                                                                            |

Item 1 was a policy bypass confirmed on-chain on 2026-10-20: with a Zip among
the parameters of a `Matches`, later checks read the wrong parameter. The full
write-up of the resolved items is in this file's git history.

## Running the fuzzer

```
cd packages/evm
GAP_CASES=2000 npx hardhat test formal/test/integrity-gaps.spec.ts
GAP_CASES=300 GAP_CLEAN=1 npx hardhat test formal/test/integrity-gaps.spec.ts  # reference sanity check
GAP_CASES=2000 GAP_CHECK=1 GAP_MUTATE=0.5 npx hardhat test formal/test/integrity-gaps.spec.ts  # the SDK check vs Integrity
```

Mismatches are grouped by the tags of the shapes the generator added. In clean
mode (only shapes inside the decoder proof's hypotheses) it should report none.
