# Integrity backlog: extra checks for the SDK

On-chain, `Integrity.enforce`
(packages/evm/contracts/core/serialize/Integrity.sol) is the only gate between a
stored condition tree and `evaluate`. Some trees pass it but are not read the
way their author meant: `evaluate` checks the wrong bytes (a possible policy
bypass) or rejects every call. This file lists those shapes. Each entry should
become a check in the SDK's `checkConditionIntegrity`
(src/main/condition/conditionIntegrity.ts), so that
`processPermissions`/`applyTargets` refuse to produce them.

The list comes from the formal verification work in packages/evm/formal (the
decoder proof states which trees it covers) and from fuzzing Integrity-accepted
trees against a reference evaluator
(packages/evm/test/formal/integrity-gaps.spec.ts).

Severity:

- **bypass**: a call the author meant to forbid is allowed.
- **false reject**: a call the author meant to allow is rejected (fails safe).

## 0. The SDK checker predates v3

`conditionIntegrity.ts` and the SDK's `Operator`/`Encoding` enums know none of
`Pluck`, `ZipSome`, `ZipEvery` or `EtherValue`, and the rules differ from
`Integrity.sol` in other places. Before adding the extra checks below, port
`Integrity.enforce` to the SDK (or run it via a local EVM call), so that the SDK
at least rejects what the chain rejects.

## 1. Zip as a positional child (bypass)

Status: confirmed on-chain (2026-10-20).

A `ZipSome`/`ZipEvery` node placed among the children of `Matches` (AbiEncoded
or Tuple). Roles' own tests place it there as the trailing child. `TypeTree`
counts a Zip as structural (its hash is non-zero), so `_checkMatches` accepts
it. `AbiLocation.children` then gives the Zip a parameter slot of its own, and
every later parameter is read from the wrong place.

- `f(uint256[] a, uint256[] b, uint256 c)` with
  `Matches[Pluck(a), Pluck(b), ZipEvery(...), EqualTo(c, 5)]`: the `EqualTo`
  reads `a[0]`. A call with `a = [5], c = 999` passes, and `c = 5` is rejected.
- Trailing Zip, fields dynamic (`f(bytes[], bytes[])`): every call fails with
  `CalldataOverflow`.

Safe form: `And[Matches[Pluck(a), Pluck(b), ...], ZipEvery(...)]`.

SDK check: a Zip (or an And/Or whose subtree contains a Zip) must not be a child
of a `Tuple`, `Array` or `AbiEncoded` node. Place it under an `And` beside the
container. Contract fix: `TypeTree` treats a Zip as non-structural, or Integrity
rejects it there.

## 2. Non-structural child of a non-Matches Tuple (false reject)

Status: confirmed on-chain (2026-10-18).

A `Tuple` with operator `EqualTo` (or `Pass`/`Custom`) and a non-structural
child such as an `EtherValue` comparison. `Matches` requires all children to be
structural, but the other operators only require at least one.
`AbiLocation.size` counts the extra child as a dynamic field: for `f((bytes))`
it computes 261 bytes instead of 96. The instance found fails safe (overflow, so
the call is denied). Other shapes are unchecked.

SDK check: every child of a `Tuple`/`Array`/`AbiEncoded` node must be
structural, whatever the operator.
