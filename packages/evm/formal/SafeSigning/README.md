# Signing through the Safe

`SignTypedMessageLib` (delegatecalled by the Safe) marks messages as signed
in the Safe's `signedMessages`; the Safe's `CompatibilityFallbackHandler`
answers EIP-1271 `isValidSignature` with an empty signature by looking the
mapping up. This library proves that each signing function makes exactly
the intended hash valid, and what `signMessage` implies.

```
cd packages/evm/formal
lake build SafeSigning
```

## The reference

EIP-191 itself: the `personal_sign` hash of a message `m` is
`keccak256("\x19Ethereum Signed Message:\n" ++ decimal(len m) ++ m)`
(`personalHash`), with `decimal` the base-10 digits, most significant
first. `keccak256` is a parameter `K`.

## What is proven

| Theorem                                              | Statement                                                                                                                                                                                                              |
| ---------------------------------------------------- | ---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `uintToString_eq` (`Agree.lean`)                     | The library's `uintToString` is the decimal representation, for every value.                                                                                                                                           |
| `personalSign_valid`                                 | After `personalSign(m)`, `isValidSignature(personalHash m, "")` finds the stored key.                                                                                                                                 |
| `personalSign_exact`                                 | If a hash (or, for the `bytes` form of `isValidSignature`, data) is valid because of that key, it is `personalHash m`, unless keccak256 has a collision.                                                               |
| `signTyped_valid`, `signTyped_exact`                 | The same for `signTypedMessage` and its digest (`EIP712.hashTypedMessage_spec`: the EIP-712 digest of the typed message).                                                                                             |
| `signMessage_raw`                                    | `signMessage(m)` with a 32-byte `m` makes `isValidSignature(m, "")` valid: the Safe signs the raw hash `m`.                                                                                                           |
| `signMessage_personal`, `signMessage_typed`          | `signMessage` of the EIP-191 hash of a text stores the key of `personalSign` of that text; of an EIP-712 digest, the key of `signTypedMessage` of that message.                                                       |

So a permission that lets the role call `signMessage` with a 32-byte
message it does not pin lets the role sign any personal message and any
EIP-712 message (permits, orders, …), whatever `allowPersonalSign` /
`allowSignTypedMessage` permissions say. The SDK has no helper that allows
`signMessage`, and none should.

The handler's constant `SAFE_MSG_TYPEHASH` is a hypothesis of the theorems
(`hTH`: it is `keccak256("SafeMessage(bytes message)")`); the test checks it
with the executable keccak256.

## Tests

- `test/formal/safe-signing.spec.ts`: `uintToString` on chain
  (`MockUintToString`), the Lean transcription and JavaScript's decimal agree
  on 500 values (powers of ten and their neighbours, `2^256 - 1`, random).
- `packages/integration-tests/test/eip712/safe-signing-lean.spec.ts`, against
  a real Safe 1.4.1 and its handler: for random messages, the keys
  `personalSign` and `signMessage` store are the Lean keys; the Lean EIP-191
  hash is ethers' `hashMessage`; the handler accepts it after `personalSign`
  and rejects a random hash; `signMessage(h)` makes `h` valid; `signMessage`
  of an EIP-191 hash stores `personalSign`'s key; `getMessageHashForSafe` is
  the Lean `safeMessageHash`. 150 messages: 0 differences.

## Not covered

- The storage write: `SafeStorage` matches the Safe 1.3 / 1.4.1 layout by
  inspection (the integration test reads the result through the handler).
- `isValidSignature` with a non-empty signature (owners' signatures).
- What the Roles permission on `personalSign` admits: `allowPersonalSign` is
  a `Bitmask` on the message prefix, which decoder faithfulness covers.
