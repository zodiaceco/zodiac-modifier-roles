# End to end: how authority composes across contracts

The other libraries each prove one contract or function faithful. This one
is about how they compose:
- Roles with the Safe it controls;
- the signing library the Safe delegatecalls;
- other Roles Modifiers that accept the Safe's EIP-1271 signature;
- MultiSend batches, whose transactions are checked one by one and settled
  together;
- who an execution is attributed to, and reentrancy (tested on chain, not
  proven; see [below](#attribution-and-reentrancy)).

```
cd packages/evm/formal
lake build EndToEnd
```

## Signing routes into Roles authority

A Roles Modifier `R` runs `execTransactionWithSignature` for a module `S` (a
Safe) once `S.isValidSignature(D, sig)` accepts the digest `D` of a `RoleTx`
for `R`. zodiac-core passes `sig = signature[20:]`, which the relayer
chooses. Only an empty `sig` reaches the Safe's `signedMessages` (what
`validBytes` models); a non-empty one goes to the Safe's owner check, a
route listed separately below. A role on `S`'s own Roles Modifier can make
`S` accept digests through `SignTypedMessageLib`. The question: which of
those permissions let a role act with `S`'s roles on `R`?

| Theorem                       | Statement                                                                                                                                                                                                                                                                                                                       |
| ----------------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `personal_ne_typed` (`Hashes`) | A `personal_sign` hash is never an EIP-712 digest, unless keccak256 collides on the two digests' inputs.                                                                                                                                                                                                                                            |
| `typed_typeHash`              | If the encoder's digest has the EIP-712 form with type hash `th`, then `types[1]` (the message root) carries `th`, unless keccak256 collides on the two digests' inputs.                                                                                                                                                                             |
| `pinsArg_sound` (`Pins`)      | If `evaluate` passes a condition that pins argument `i` (every passing branch reaches, through `Or` / `And` and the calldata `Matches`, an `EqualTo` of the expected shape at `i`'s head position), the bytes Roles reads at `tailLocation(data, 4, 32 * i)` are one of the pinned values.                                       |
| `route_bytes` (`Library`)     | **Roles' reader and Solidity's decoder agree.** If Roles passes a call with the `bytes` argument pinned and Solidity's ABI decoder accepts the calldata, the message `signMessage` / `personalSign` gets is a pinned message, on any calldata.                                                                                     |
| `route_types`                 | **Roles' reader and the hand-written fallback agree.** If Roles passes a call with `types` pinned (an array of 96-byte elements), the fallback's `typesPtr = calldataload(0x44) + 4` points at the same bytes, and the length and elements it reads are those of a pinned value.                                                    |
| `route_typed`                 | So a typed-message permission with pinned types produces a `RoleTx` digest only if a pinned value has the `RoleTx` type hash at `types[1]`.                                                                                                                                                                                     |
| `only_flagged` (`Routes`)     | **Only flagged signing permissions reach a `RoleTx`.** If the key the library stored under a permission Roles passed makes the Safe accept a `RoleTx` digest `D`, then: `signMessage` without a pin, or with `D` itself pinned; or a typed message without pinned types, or with `RoleTx` types; never `personalSign`. Each unless keccak256 collides on inputs computed from the call and `D`. |

`only_flagged` is about `pinsArg` (`FlaggedOrExact`), and covers the
`SignTypedMessageLib` route only. The SDK's `permissionHazards` checks the
same conditions (`sign-message`, `sign-typed-message-types`,
`sign-typed-message-authority`); that it flags whatever `pinsArg` rejects is
tested (`hazards-pins.spec.ts`, below), not proven. The SDK is stricter in
about 1% of the `types` cases. Two of its rules came from the proof:
- the `types` pin must read 96-byte elements, or Roles compares fewer bytes
  than the library hashes;
- a pin must sit at its argument's head position (the arguments before it
  one word each), or Roles reads it elsewhere than the library does.

The other ways to make a Safe's EIP-1271 check accept something sit outside
the signing library. `permissionHazards` flags them as well; no theorem
covers them:
- the Safe's owners;
- delegatecall into other code;
- calls to the Safe itself (fallback handler, owners, modules);
- `approveHash` / `execTransaction` on Safes it owns.

Assumptions:
- keccak256: the evaluator model compares values longer than 32 bytes by
  their preimages; the signing theorems hold unless keccak256 collides on
  inputs they name (`CollisionIn K xs`, see
  [hash collisions](../README.md#hash-collisions)).
- Calldata is shorter than `2^256` bytes.

## Tests

`packages/integration-tests/test/e2e/pins.spec.ts` uses a real Safe 1.4.1,
the v3 `Roles` and `SignTypedMessageLib`. It sends random and malformed
calldata through a role that may only sign pinned messages, or typed
messages with pinned types. The mutations:
- moved offsets and lengths;
- decoys the offsets can point at;
- dirty padding;
- truncation and junk;
- swapped head words.

For every call Roles lets through and the library executes, the stored key
is checked:
- `signMessage`: it is a pinned message's key;
- `signTypedMessage`: it is the key of the digest of the pinned types, with
  the `domain` and `message` the fallback reads.

Three seeds of 1,000 calls each: 0 violations. `signMessage`: about 230
signed, 770 refused by Roles, none refused by the library after Roles let
them through. Typed: about 350 signed, 600 refused by Roles, 50 refused by
the library.

`packages/evm/test/formal/hazards-pins.spec.ts` tests the SDK's
`permissionHazards` against `pinsArg` itself, the definition `only_flagged`
is about. It generates random conditions on the signing library's arguments
(pins of the right and wrong shapes, `And`/`Or` over them, other arguments
that do or do not take one head word, other leading bytes) and runs
`pinsArg` on the tree the packing model packs and unpacks (`pn` query).
Wherever the SDK raises no `sign-message` or `sign-typed-message-types`
hazard, `pinsArg` must hold. Three seeds of 3,000: no exception; about 500
`bytes` and 290 `types` cases pinned. The SDK is stricter in about 30
`types` cases per seed (about 1%), all with an argument before `types`
described by an `And` over children of different types: the SDK cannot tell
how many head words it takes, the unpacked tree can.

`NonVacuity.lean` (built with the library): a concrete two-transaction batch
with real charges that `authorize` lets through, so the hypotheses of
`executed_authorized`, `authorize_persist` and `executions_limit` hold on a
non-trivial input.

## Batches: every executed transaction passed its permission

`Authorization._authorize` checks a call through a role. For a call whose
target and selector have an unwrapper registered, it checks each transaction
of the batch instead, threading one consumption list through them. After the
avatar executes, `Settlement._persist` writes that list.

`Batch.lean` transcribes `_authorize` and `_transaction` (`authorize`):
- scope resolution (the target or function entry, then the global entry);
- the calldata length check;
- the execution options;
- the condition, run by the evaluator model `Evaluate`.

It also transcribes `_persist` on the allowances (`persist`, in
`Consume.lean`).

The glue around them is checked by reading the code, not modelled: each
execution entry point reaches `_authorize`, the avatar is called with the
same `to, value, data, operation`, and `_persist` runs only on success. All
four entry points go through `_execWithRole` / `_execWithRoleReturnData`.

| Theorem                          | Statement                                                                                                                                                                                                                                                                                  |
| -------------------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ |
| `evalC_steps` (`Consume`)        | **Failed branches leave no trace.** When `evaluate` passes, the consumptions it returns are the input list after a sequence of successful `consume` steps: the charges on the path that passed. That holds for every tree, under `Or`, the array operators and `Zip` alike.                    |
| `steps_spec`                     | **One entry per key.** Along such steps the list never holds a key twice. Each entry keeps the accrued balance and is never overdrawn. For every key, the steps are exactly `Allowance.consumeAll` on that key's charges.                                                                     |
| `persist_get`, `persist_tx`      | `_persist` writes every entry in order, so a second entry for a key would overwrite the first. With one entry per key, each key is written once. What it stores for every key is `Allowance.tx` on that key's charges.                                                                     |
| `executed_authorized` (`Batch`)  | **Every transaction the avatar executes passed its permission.** When `_authorize` lets a call through, the avatar executes either the call itself or, with an unwrapper registered, exactly the transactions `MultiSend`'s loop runs (`MultiSend.unwrap_exec`). Each of them resolved a scope entry for its target and selector, had options that allow its value and operation, and passed its condition on its own calldata, with the consumptions threaded from one transaction to the next (`chain p envOf [] es = some cons`; `Permitted` alone only says some consumptions exist). |
| `authorize_persist`              | **Settlement after a batch is one `Allowance.tx` per allowance**, with the charges of all the batch's transactions, in order.                                                                                                                                                                |
| `executions_limit`               | **Spending limit, end to end.** Over any executions through Roles at block times up to `T`, batches included, the raw amounts charged to an allowance total at most its stored balance plus `refill` for each full period up to `T` (`Allowance.spending_limit`).                                |

`executions_limit` bounds charged amounts. The conversion of a priced spend
into balance units (`Env.scale` in the evaluator model) is abstract here:
no theorem ties it to `Allowance.charge`. The value-level results
(`value_limit`, `charged_covers`) are about the `Allowance` model; they are
tested through Roles on single calls (`allowance.spec.ts`), not in batches.

`envOf e` is not tied to `e` in the statements: the theorems hold for every
`envOf`. `Permitted p (envOf e) e` means "its ether-value checks saw
`e.value`" when `envOf` is chosen that way, as the driver (`Diff.lean`)
does.

Hypotheses. Each is a fact about the deployment, not something the code can
check:
- **Unwrappers.** An unwrapper is registered only as `MultiSendUnwrapper` for
  a `MultiSend` or `MultiSendCallOnly`. Roles checks what the unwrapper
  returns and never the outer call, so a custom unwrapper must return exactly
  what its target executes.
- **The state before the batch.** The transactions of a batch are all checked
  before any of them executes. Conditions that read outside state (custom
  checkers, `WithinRatio`, price adapters) see it as it was before the batch,
  for every transaction in it. In the model, one `envOf` holds for the whole
  batch. Accrued balances are read once, at the first charge.
- **Nothing else writes the allowances** between executions: neither owner
  calls nor the executed transactions themselves. This is the settlement
  caveat in the docs.
- A custom checker that fails reports a failure status, not `Ok` (as
  `EnvOk` in `Bridge`).

Not modelled:
- A batch nested in a batch, a delegatecall to `MultiSend` as one
  transaction of a batch. It is not unwrapped: Roles checks it as a plain
  delegatecall, against a permission on `MultiSend`, and
  `permissionHazards` flags delegatecall permissions.
- Membership, which is checked once per execution (see
  [attribution and reentrancy](#attribution-and-reentrancy)).

### Test

`packages/integration-tests/test/e2e/batch.spec.ts` uses a real Safe 1.4.1,
the v3 `Roles`, `MultiSend` and `MultiSendUnwrapper`. Each case gives a fresh
role random permissions (target-wide, per function, global) whose
conditions charge three allowances:
- on parameters and array elements;
- on the ether value, and per call;
- twice in one `And`;
- in `Or` branches that fail after charging.

The role then sends one call or a MultiSend batch of one to four
transactions, sometimes malformed, sometimes sending value or
delegatecalling. The Lean driver runs `EndToEnd.authorize` on the same
input (`az` query). For every case the test compares:
- whether Roles lets the call through;
- every allowance's stored balance afterwards.

`BATCH_CASES`, `BATCH_SEED`. Three seeds of 1,000 cases each: 0 differences.
Per seed, about 290 calls went through: about 145 batches and 145 single
calls, with about 245 allowance balances charged. The rest were refused, by
scope, options, conditions, exceeded allowances or malformed batches, and
Roles refused exactly those the model refused.

## Attribution and reentrancy

Tested on chain, not proven in Lean. What can go wrong here is EVM
behaviour: transient storage, staticcalls, rollback on revert, a call that
fails without reverting. A Lean model would have to assume exactly that, so
the test runs the compiled contracts with a real Safe instead.

### The reentrancy argument

1. All four execution entry points start with `nonReentrant`, a transient
   flag set before any external call and cleared on exit. `moduleOnly` and
   `moduleOnlySigned` (zodiac-core) add a second transient guard, the
   authenticated module (`AlreadyAuthenticated`).
2. Before the avatar's call, every external call Roles makes to other
   code is a staticcall: the ERC-1271 `isValidSignature`, the unwrapper (a
   `view` function), custom checkers, price adapters. `CustomConditionChecker.check`
   and `WithinRatioChecker.check` are external library functions, which
   Solidity calls with DELEGATECALL into Roles' own linked libraries; those
   staticcall the checkers and adapters. Between entry and the avatar's call
   nothing changes state except Roles' own write of the used digest.
3. During the avatar's call, a nested execution reverts with `Reentrancy`.
   Of the other state-changing functions, a caller who is not the owner can
   only use those keyed by the caller: `invalidate` (its own digests) and
   `renounceRole` (its own memberships). Every other one is owner-only.
4. After the call, `_persist` writes what was computed before it.

So the successful executions of one Roles Modifier never interleave. Each
reads the state at its entry, and the only writes between those reads and
its settlement are owner calls and the caller-keyed ones. That is the
sequential history `Execs` (`Batch.lean`) describes, apart from owner writes
made during an execution, which settlement overwrites (the documented
caveat). So `executions_limit` holds for every on-chain history in which the
owner does not change allowances during an execution. Different Roles
Modifiers, even on one Safe, have separate guards: one can execute inside
another's execution, and each settles its own state.

### Test

`packages/integration-tests/test/e2e/attribution.spec.ts`, with a real Safe
1.4.1, the v3 `Roles` (two on the same Safe), and hostile helpers
(`integration-tests/contracts/Adversaries.sol`): a target that calls into
Roles while the avatar calls it, an ERC-1271 signer that is also a module
and can misbehave (always valid, revert, wrong or short answers, try to
execute during the check), a target that reverts.

Deterministic cases:
- From inside an executed call, all four entry points revert with
  `Reentrancy`, also when the caller is an enabled member that can run the
  same calls at the top level.
- From inside an executed call, every state-changing function of Roles' ABI
  (29) is called: 4 `Reentrancy`, 22 owner-only, `setUp` already
  initialized, and only `invalidate` and `renounceRole` succeed. The list
  comes from the ABI, so a new function is covered automatically.
- An ERC-1271 signer cannot execute from inside `isValidSignature`.
- The signature parser: too short, the module list's sentinel (address 1,
  which passes the `modules[signer] != 0` check but has no key and no code),
  an EOA named as a contract signer, a non-member's signature, another
  Roles Modifier's digest, a changed field, replay, cancellation with
  `invalidate`, 65-byte contract signatures.
- A failed call with `shouldRevert` false uses the digest and changes
  nothing else; with `true` everything reverts.
- Memberships: a batch is one use; a disabled module with a membership
  cannot execute, directly or by signature.
- Nesting an execution through a second Roles Modifier on the same Safe.

A stateful fuzz runs random sequences of owner changes (grants with start,
end and uses, revocations, default roles, enabling and disabling modules,
allowances), time jumps, renouncements, cancellations, signer modes, and
executions: direct (all entry points, EOA and contract modules, non-modules)
and relayed (ECDSA, ERC-1271 in every mode, malformed, replayed, changed
and cross-domain signatures), of calls that succeed, fail, re-enter Roles,
are batches or are not allowed. A reference model predicts the exact outcome
(success, a failed call, or the error) and the state after each step: the
allowance, the used digests, the membership updates and uses, the ether
sent, and that every nested execution was refused. `ATTRIBUTION_STEPS`,
`ATTRIBUTION_SEED`. Three seeds of 5,000 steps: every outcome predicted.
Per seed, about 175 direct and 85 relayed executions succeeded, 30 calls
failed without reverting, 105 executions re-entered (all refused), 185
replays were refused, and the rest were refused for membership, module,
signature or permission reasons.

### Findings (documented in `docs/general/membership.mdx`)

- **The submitter picks the gas.** With `shouldRevert` false, a relayed
  call that fails does not revert the submission. Whoever submits it can
  give the call too little gas: the call fails and the signature is used
  up. In the test, the lowest gas limit without a revert is 178,000 with
  `shouldRevert` false (the call fails) and 272,000 with `true` (the call
  runs). The fuzz uses a fixed gas limit for this reason; an estimated one
  produced exactly this case.
- **A 65-byte contract signature is read as ECDSA first.** If that recovers
  an address, it is the signer, so the contract's valid signature is
  rejected. It is never wrongly accepted.
- **Renouncing inside the own execution.** A member that renounces a role
  during an execution under that role keeps it if its uses are limited
  (settlement writes the uses back), and loses it if they are unlimited
  (settlement writes nothing). Only the member itself can do this.
- A batch is one use of a membership.

## Not covered (yet)

- Settlement: equal to running the steps in order, unless the executed
  transaction changes the Roles Modifier's own state (documented caveat;
  `integration-tests/test/e2e/composition.spec.ts` shows the overwrite).
