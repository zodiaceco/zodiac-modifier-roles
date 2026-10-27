import EIP712
import SafeSigning

/-!
# Which digests a signing call can produce

The Safe's EIP-1271 check accepts a 32-byte hash `h` once
`signedMessages[safeMessageHash(abi.encode(h))]` is set (`SafeSigning`).
`SignTypedMessageLib` sets it for:

* `signMessage(m)`: `m` itself (a 32-byte `m` is `abi.encode(m)`);
* `personalSign(m)`: the EIP-191 hash of `m`;
* `signTypedMessage(domain, message, types)` (any selector): the digest
  `EIP712Encoder.hashTypedMessage` computes.

A Roles Modifier's `execTransactionWithSignature` accepts a module's
EIP-1271 signature on the digest of a `RoleTx`:
`keccak256(0x1901 ‖ domainSeparator ‖ hashStruct(RoleTx))`, with
`hashStruct(RoleTx) = keccak256(RoleTx typehash ‖ encoded fields)`.

This file shows which of the three can produce such a digest: a
`personalSign` never, a `signTypedMessage` only with `types[1]` (the
message root) carrying the `RoleTx` type hash, unless keccak256 has a
collision. `signMessage` signs whatever 32 bytes it is given.
-/

namespace EndToEnd
open DecoderFaithfulness SafeSigning

/-- A digest of the EIP-712 form: `K(0x1901 ‖ domainSeparator ‖ structHash)`,
    with the struct hash `K(typeHash ‖ fields)`. A `RoleTx` digest is one
    with `typeHash = K("RoleTx(…)")`. -/
def typedDigest (K : Bytes → Bytes) (domainSep typeHash fields : Bytes) : Bytes :=
  K ([0x19, 0x01] ++ domainSep ++ K (typeHash ++ fields))

theorem append_inj {a b c d : Bytes} (h : a ++ b = c ++ d) (hl : a.length = c.length) :
    a = c ∧ b = d := by
  have h1 := congrArg (List.take a.length) h
  have h2 := congrArg (List.drop a.length) h
  simp [hl] at h1 h2
  exact ⟨h1, h2⟩

/-- Without a collision, `K` is injective. -/
theorem inj_of_noCollision {K : Bytes → Bytes} (hc : ¬ Collision K) {x y : Bytes}
    (h : K x = K y) : x = y := by
  by_cases hne : x = y
  · exact hne
  · exact absurd ⟨x, y, hne, h⟩ hc

/-- **A `personal_sign` hash is never an EIP-712 digest**, unless keccak256
    has a collision: the preimages differ in their second byte (`'E'`, from
    `"\x19Ethereum Signed Message:\n"`, against `0x01`). -/
theorem personal_ne_typed (K : Bytes → Bytes) (m domainSep typeHash fields : Bytes)
    (h : personalHash K m = typedDigest K domainSep typeHash fields) : Collision K := by
  refine ⟨_, _, ?_, h⟩
  intro heq
  have := congrArg (fun l : Bytes => l[1]?) heq
  simp [prefix191, ascii] at this

/-- `_toTree` keeps the node's own type hash. -/
theorem toTree_typeHash {types : List EIP712.TNF} {fuel index : Nat} {t : EIP712.TN}
    (h : EIP712.toTree types fuel index = some t) :
    t.typeHash = (types.getD index default).typeHash := by
  cases fuel with
  | zero => simp [EIP712.toTree] at h
  | succ f =>
    unfold EIP712.toTree at h
    split at h
    · simp at h
    · rename_i n hn
      obtain ⟨cs, _, rfl⟩ := Option.map_eq_some_iff.mp h
      simp [List.getD, hn]

/-- **What `_hashStruct` returns is the struct hash of `types[index]`**:
    `K(typeHash ‖ fields)`, with the node's type hash (never zero there). -/
theorem hashStructE_form (K : Bytes → Bytes) (data : Bytes) (types : List EIP712.TNF)
    (index : Nat) (r : Bytes) (h : EIP712.hashStructE K data types index = some r) :
    ∃ fields, r = K ((types.getD index default).typeHash ++ fields) := by
  unfold EIP712.hashStructE at h
  split at h
  · simp at h
  · rename_i root hroot
    split at h
    · simp at h
    · rename_i hne
      simp only [not_or] at hne
      have hth := toTree_typeHash hroot
      cases hfuel : root.height with
      | zero => simp [hfuel, EIP712.hashField] at h
      | succ f =>
        have he : root.encoding = .Tuple := by simpa using hne.1
        rw [hfuel] at h
        unfold EIP712.hashField at h
        simp only [he, reduceCtorEq, ite_false, ite_true] at h
        unfold EIP712.hashBlock at h
        simp only [Bool.false_eq_true, false_and, ite_false] at h
        obtain ⟨rs, _, rfl⟩ := Option.map_eq_some_iff.mp h
        refine ⟨rs.flatten, ?_⟩
        unfold EIP712.packBlock
        rw [hth] at hne ⊢
        rw [if_pos hne.2]

/-- **The digest `signTypedMessage` signs has the message root's type hash.**
    When `hashTypedMessage` returns a digest of the EIP-712 form with type
    hash `th`, then `types[1]` (the message root `_hashStruct(message, types,
    1)` starts from) carries `th`, unless keccak256 has a collision. `K`
    returns 32 bytes; the domain separator and type hashes are 32 bytes. -/
theorem typed_typeHash (K : Bytes → Bytes) (hK : ∀ x, (K x).length = 32)
    (domain message : Bytes) (types : List EIP712.TNF) (domainSep th fields : Bytes)
    (hds : domainSep.length = 32) (hth : th.length = 32)
    (h1 : (types.getD 1 default).typeHash.length = 32)
    (h : EIP712.hashTypedMessage K domain message types =
      some (typedDigest K domainSep th fields)) :
    (types.getD 1 default).typeHash = th ∨ Collision K := by
  by_cases hc : Collision K
  · exact .inr hc
  left
  unfold EIP712.hashTypedMessage at h
  split at h
  · rename_i ds mh hd hm
    simp only [Option.some.injEq] at h
    have e1 := inj_of_noCollision hc h
    simp only [List.append_assoc] at e1
    have e2 := List.append_cancel_left e1
    obtain ⟨x, rfl⟩ := hashStructE_form K domain types 0 ds hd
    obtain ⟨y, rfl⟩ := hashStructE_form K message types 1 mh hm
    have e3 := (append_inj e2 (by rw [hK, hds])).2
    exact (append_inj (inj_of_noCollision hc e3) (by rw [h1, hth])).1
  · simp at h

end EndToEnd
