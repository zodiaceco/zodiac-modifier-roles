# MultiSend: Roles checks exactly what MultiSend executes

A Roles member can send a batch: a delegatecall from the Safe to `MultiSend`
with `multiSend(bytes transactions)`. Roles does not check the batch as one
call; `MultiSendUnwrapper` splits it and Roles checks each transaction with
its own permission. That is only safe if the transactions Roles checks are
the transactions MultiSend then executes.

```
cd packages/evm/formal
lake build MultiSend
```

## The reference

`parse` (`Basic.lean`) is the batch format as Safe's `MultiSend` documents
it: transactions concatenated, each `abi.encodePacked(uint8 operation,
address to, uint256 value, uint256 dataLength, bytes data)`, operation `0`
(call) or `1` (delegatecall). Both contracts are compared with it, not with
each other.

## What is proven

| Theorem                     | Statement                                                                                                                                                                                                                                                         |
| --------------------------- | ----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `exec_parse` (`Agree.lean`) | On a batch in the format, `multiSend`'s assembly loop executes exactly its transactions, in order, whatever memory follows the batch.                                                                                                                             |
| `unwrap_parse`              | When `MultiSendUnwrapper.unwrap` succeeds, the outer call is a delegatecall without value, the calldata is `multiSend(bytes)` with the standard head (offset `0x20`, length `L`, `4 + ceil32(64 + L)` bytes), the batch is not empty, and the entries it returns, with Roles' calldata slices `data[dataLocation : dataLocation + dataSize]`, are `parse` of the batch. |
| `unwrap_exec`               | Together: MultiSend, handed `data[68 : 68 + L]` by the Solidity ABI decoder, executes exactly the transactions Roles checks, with the same operation, target, value and calldata.                                                                                |

No assumption on the calldata beyond `data.length < 2^256`. The proofs use
only Lean's standard axioms, with no `sorry`.

## The transcriptions

- `unwrap`: `MultiSendUnwrapper.sol`, slice reads included (a read past the
  end of `data` reverts, a short read is zero-padded). The unwrapper reads an
  entry's length word before checking that the entry fits; the proof covers
  that order.
- `execLoop`: the assembly loop of `MultiSend.multiSend`
  (`contracts/__test__/fixtures/MultiSend.sol`, the same loop as Safe's
  `MultiSend` 1.3.0 / 1.4.1). Memory past the batch is arbitrary. The loop
  condition is `i < length` with `i` starting at `0x20`, so MultiSend skips an
  entry that starts in the last 32 bytes of a batch; no entry of a batch in
  the format starts there (every entry has at least 85 bytes).
- A call that fails reverts the whole batch; the model leaves that out (it
  only removes executions).
- `MultiSendCallOnly` reverts on delegatecall entries: it executes the same
  transactions or nothing.

## Differential test

`test/formal/multisend.spec.ts` (with the Lean driver built;
`MULTISEND_CASES`, `MULTISEND_SEED`): random batches, valid and mutated
(operation `2`+, trailing bytes, wrong data lengths, header edits, empty
batches, random byte flips).

1. `MultiSendUnwrapper.unwrap` on chain returns what the Lean `unwrap`
   returns, entries or revert.
2. MultiSend, delegatecalled like the Safe does it (`MockDelegator`), calls
   what the Lean `execLoop` executes (calls recorded by `MockRecorder`).
   Skipped: calldata that is not a `multiSend` call, batches whose loop reads
   memory past the batch, and calls sending more ether than the caller has.
3. When the unwrapper accepts, the Lean MultiSend executes exactly the
   unwrapped entries with their slices.

4 seeds, 6,400 batches: 0 differences; about 1,750 accepted batches, about
4,400 executions compared on chain.

## Not covered

- That the unwrapper is registered only for the real `MultiSend` /
  `MultiSendCallOnly` addresses (`setTransactionUnwrapper` is owner
  configuration).
- The Solidity ABI decoder handing `multiSend` the bytes at the offset in
  the head: standard, and exercised by the differential test.
