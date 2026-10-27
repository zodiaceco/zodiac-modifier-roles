import EndToEnd.Library

/-!
# Routes from a signing permission to a `RoleTx`

A Roles Modifier `R` runs `execTransactionWithSignature` for a module `S` (a
Safe) once `S.isValidSignature(D, "")` accepts the digest `D` of a `RoleTx`
for `R` (`typedDigest K domainSep_R typeHash_RoleTx fields`). The Safe
accepts `D` because some key is set in `signedMessages`. If that key was
written by `SignTypedMessageLib` in a call a role of `S`'s own Roles
Modifier made, this file says which permissions allow it:

* `signMessage`: only if the message is not pinned, or a pinned message is
  `D` itself (the permission author pinned that exact hash);
* `signTypedMessage` (any selector): only if `types` is not pinned, or a
  pinned value has the `RoleTx` type hash at `types[1]`;
* `personalSign`: never.

each unless keccak256 has a collision. These are the permissions the SDK's
`permissionHazards` flags (`sign-message`, `sign-typed-message-types`,
`sign-typed-message-authority`); the pins here are what it checks
(`pinsArg leafBytes 0`, `pinsArg leafTypes 2`).
-/

namespace EndToEnd
open DecoderFaithfulness DecoderFaithfulness.Roles Evaluate SafeSigning

/-- What a call into `SignTypedMessageLib` (delegatecalled by the Safe with
    domain separator `ds`) stores in `signedMessages`, by entry point.
    `domainArg` and `messageArg` are the `domain` and `message` bytes the
    fallback hands to the encoder (their offsets do not matter here). -/
inductive LibSign (K : Bytes → Bytes) (ds : Bytes) (data : Bytes) : Bytes → Prop
  | message {m : Bytes} (hm : solDecodeBytes data = some m) :
      LibSign K ds data (signMessageKey K ds m)
  | personal {m : Bytes} (hm : solDecodeBytes data = some m) :
      LibSign K ds data (personalSignKey K ds m)
  | typed {ts : List EIP712.TNF} {domainArg messageArg digest : Bytes}
      (hts : decodeTypes (typesLen data) (typesRaw data) = some ts)
      (hd : EIP712.hashTypedMessage K domainArg messageArg ts = some digest) :
      LibSign K ds data (signTypedKey K ds digest)

/-- The permission (condition `root`) is one `permissionHazards` flags for
    the entry point the stored key comes from, or pins exactly the hash
    `D`. -/
def FlaggedOrExact (root : Condition) (fuel : Nat) (roleTypeHash D : Bytes) :
    (kind : Nat) → Prop
  -- signMessage
  | 0 => pinsArg leafBytes 0 fuel root = false ∨
      ∃ e, PinUnder 0 root e ∧ pinnedLeaf leafBytes e = true ∧ pinnedBytes e.compValue = D
  -- signTypedMessage
  | 1 => pinsArg leafTypes 2 fuel root = false ∨
      ∃ e ts, PinUnder 2 root e ∧ pinnedLeaf leafTypes e = true ∧
        decodeTypes (wordVal (key e.compValue)) (pinnedRaw e.compValue) = some ts ∧
        (ts.getD 1 default).typeHash = roleTypeHash
  -- personalSign
  | _ => False

/-- **Only flagged signing permissions reach a `RoleTx`.** A role's call
    into the signing library passed Roles (`evaluate` on `data` returned
    `Ok`); the key the library stored makes the Safe accept the digest `D`
    of an EIP-712 message with type hash `roleTypeHash` (a `RoleTx`). Then
    the permission is flagged (or pins exactly `D`) for the entry point
    used, or keccak256 has a collision. `th` is the handler's
    `SAFE_MSG_TYPEHASH`; `K` returns 32 bytes. -/
theorem only_flagged {env : Env} {data : Calldata} {n F f : Nat} {root : Condition}
    {cons : List Consumption} {sl : Slots} (K : Bytes → Bytes) (hK : ∀ x, (K x).length = 32)
    (hdl : data.length < 2 ^ 256)
    (hrun : (evalC env data n F 0 root cons sl).status = sOk)
    {ds th k domainSep roleTypeHash fields : Bytes} (hTH : th = safeTypeHash K)
    (hdsl : domainSep.length = 32) (hrl : roleTypeHash.length = 32)
    (hsign : LibSign K ds data k)
    (hvalid : validBytes K th ds (· = k) (typedDigest K domainSep roleTypeHash fields)) :
    (∃ kind, FlaggedOrExact root f roleTypeHash (typedDigest K domainSep roleTypeHash fields) kind ∧
      ((kind = 0 ∧ ∃ m, solDecodeBytes data = some m ∧ k = signMessageKey K ds m) ∨
       (kind = 1 ∧ ∃ dg, k = signTypedKey K ds dg))) ∨ Collision K := by
  cases hsign with
  | @message m hm =>
    -- the Safe accepts `D` because of `signMessage(m)`: `m = D`
    rcases signTyped_exact K th ds m _ hTH hvalid with hD | hc
    · refine .inl ⟨0, ?_, .inl ⟨rfl, m, hm, rfl⟩⟩
      cases hp : pinsArg leafBytes 0 f root
      · exact .inl hp
      · obtain ⟨e, hu, hl, hme⟩ := route_bytes hp hrun hm
        exact .inr ⟨e, hu, hl, by rw [← hme, hD]⟩
    · exact .inr hc
  | @personal m hm =>
    -- a personal_sign hash is never a typed digest
    have hv : validBytes K th ds (· = personalSignKey K ds m)
        (typedDigest K domainSep roleTypeHash fields) := hvalid
    rcases personalSign_exact K th ds m _ hTH hv with hD | hc
    · exact .inr (personal_ne_typed K m domainSep roleTypeHash fields hD.symm)
    · exact .inr hc
  | @typed ts domainArg messageArg digest hts hd =>
    rcases signTyped_exact K th ds digest _ hTH hvalid with hD | hc
    · rw [← hD] at hd
      cases hp : pinsArg leafTypes 2 f root
      · exact .inl ⟨1, .inl hp, .inr ⟨rfl, _, rfl⟩⟩
      · rcases route_typed K hK hdl hp hrun hts hdsl hrl hd with
          ⟨e, hu, hl, hdec, hth1⟩ | hc
        · exact .inl ⟨1, .inr ⟨e, ts, hu, hl, hdec, hth1⟩, .inr ⟨rfl, _, rfl⟩⟩
        · exact .inr hc
    · exact .inr hc

end EndToEnd
