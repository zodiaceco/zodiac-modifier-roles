# Evaluator harness

For testing an off-chain evaluator against the contract from another repo,
without Hardhat there.

`evaluator-harness.json` holds the runtime code of
[`EvaluatorHarness`](../contracts/__test__/harness/EvaluatorHarness.sol), the
libraries it links, and
[`EvenLastByteCondition`](../contracts/__test__/harness/EvenLastByteCondition.sol)
(a custom condition that passes when the last byte of its value is even), by
address, plus the harness ABI.

To use it, load every entry of `code` into a local chain (`anvil_setCode`, or
`hardhat_setCode` on a Hardhat node) and `eth_call`
`EvaluatorHarness.evaluate(call, conditions, allowanceKeys, allowanceBalances)`.
It runs the conditions exactly as `Roles` does (Integrity, pack, unpack,
evaluate) and returns `ConditionViolation`'s status, node index and calldata
offset (status 0: allowed). Integrity's errors revert.

Regenerate it after contract changes:

```sh
npx hardhat run scripts/export-evaluator-harness.ts
```
