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
message root) carrying the `RoleTx` type hash, unless keccak256 collides on
two inputs the statement names (`CollisionIn`). `signMessage` signs whatever
32 bytes it is given.
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

/-- The two inputs hashed for `typedDigest K domainSep typeHash fields`. -/
def typedDigestInputs (K : Bytes → Bytes) (domainSep typeHash fields : Bytes) : List Bytes :=
  [typeHash ++ fields, [0x19, 0x01] ++ domainSep ++ K (typeHash ++ fields)]

/-- **A `personal_sign` hash is never an EIP-712 digest**, unless keccak256
    collides on the two inputs: they differ in their second byte (`'E'`,
    from `"\x19Ethereum Signed Message:\n"`, against `0x01`). -/
theorem personal_ne_typed (K : Bytes → Bytes) (m domainSep typeHash fields : Bytes)
    (h : personalHash K m = typedDigest K domainSep typeHash fields) :
    CollisionIn K ((prefix191 ++ decimal m.length ++ m) ::
      typedDigestInputs K domainSep typeHash fields) := by
  refine ⟨_, by simp, _, by simp [typedDigestInputs], ?_, h⟩
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

/-- The input `_hashStruct(data, types, index)` hashes, `typeHash ‖ fields`,
    when it succeeds. -/
def hashStructInput (K : Bytes → Bytes) (data : Bytes) (types : List EIP712.TNF) (index : Nat) :
    Option Bytes :=
  match EIP712.toTree types (types.length + 1) index with
  | none => none
  | some root =>
    if root.encoding ≠ .Tuple ∨ root.typeHash = zeros 32 then none
    else match root.height with
      | 0 => none
      | f + 1 => (EIP712.blockLoop data (EIP712.hashField K data f) root.children false 0
          root.children.length 0 0).map fun rs => root.typeHash ++ rs.flatten

/-- `_hashStruct` hashes `hashStructInput`. -/
theorem hashStructE_input (K : Bytes → Bytes) (data : Bytes) (types : List EIP712.TNF)
    (index : Nat) : EIP712.hashStructE K data types index = (hashStructInput K data types index).map K := by
  unfold EIP712.hashStructE hashStructInput
  rcases EIP712.toTree types (types.length + 1) index with _ | root
  · rfl
  · simp only
    by_cases hne : root.encoding ≠ .Tuple ∨ root.typeHash = zeros 32
    · simp [hne]
    · rw [if_neg hne, if_neg hne]
      simp only [not_or] at hne
      have he : root.encoding = .Tuple := Decidable.of_not_not hne.1
      rcases root.height with _ | f
      · simp [EIP712.hashField]
      · unfold EIP712.hashField
        simp only [he, reduceCtorEq, ite_false, ite_true]
        unfold EIP712.hashBlock
        simp only [Bool.false_eq_true, false_and, ite_false, Option.map_map]
        apply congrArg (fun g => Option.map g _)
        funext rs
        simp [EIP712.packBlock, hne.2]

/-- `hashStructInput` starts with `types[index]`'s type hash. -/
theorem hashStructInput_form {K : Bytes → Bytes} {data : Bytes} {types : List EIP712.TNF}
    {index : Nat} {p : Bytes} (h : hashStructInput K data types index = some p) :
    ∃ fields, p = (types.getD index default).typeHash ++ fields := by
  unfold hashStructInput at h
  split at h
  · simp at h
  · rename_i root hroot
    split at h
    · simp at h
    · have hth := toTree_typeHash hroot
      split at h
      · simp at h
      · obtain ⟨rs, _, rfl⟩ := Option.map_eq_some_iff.mp h
        exact ⟨rs.flatten, by rw [hth]⟩

/-- The two inputs `hashTypedMessage` hashes last: the message's struct
    input and the digest input. -/
def typedInputs (K : Bytes → Bytes) (domain message : Bytes) (types : List EIP712.TNF) :
    List Bytes :=
  match EIP712.hashStructE K domain types 0, hashStructInput K message types 1 with
  | some ds, some p => [p, [0x19, 0x01] ++ ds ++ K p]
  | _, _ => []

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
    1)` starts from) carries `th`, unless keccak256 collides on the inputs
    of the two digests. `K` returns 32 bytes; the domain separator and type
    hashes are 32 bytes. -/
theorem typed_typeHash (K : Bytes → Bytes) (hK : ∀ x, (K x).length = 32)
    (domain message : Bytes) (types : List EIP712.TNF) (domainSep th fields : Bytes)
    (hds : domainSep.length = 32) (hth : th.length = 32)
    (h1 : (types.getD 1 default).typeHash.length = 32)
    (h : EIP712.hashTypedMessage K domain message types =
      some (typedDigest K domainSep th fields)) :
    (types.getD 1 default).typeHash = th ∨
      CollisionIn K (typedInputs K domain message types ++ typedDigestInputs K domainSep th fields) := by
  unfold EIP712.hashTypedMessage at h
  rw [hashStructE_input K message] at h
  unfold typedInputs
  split at h
  · rename_i ds mh hd hm
    obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.mp hm
    simp only [Option.some.injEq] at h
    rw [hd, hp]
    simp only
    rcases eq_or_collision (xs := [p, [0x19, 0x01] ++ ds ++ K p] ++
        typedDigestInputs K domainSep th fields) (by simp) (by simp [typedDigestInputs]) h with
      e1 | hc
    · simp only [List.append_assoc] at e1
      have e2 := List.append_cancel_left e1
      obtain ⟨x, rfl⟩ := hashStructE_form K domain types 0 ds hd
      obtain ⟨y, rfl⟩ := hashStructInput_form hp
      have e3 := (append_inj e2 (by rw [hK, hds])).2
      rcases eq_or_collision (xs := [(types.getD 1 default).typeHash ++ y, [0x19, 0x01] ++
          K ((types.getD 0 default).typeHash ++ x) ++ K ((types.getD 1 default).typeHash ++ y)] ++
          typedDigestInputs K domainSep th fields) (by simp) (by simp [typedDigestInputs]) e3 with
        e4 | hc
      · exact .inl (append_inj e4 (by rw [h1, hth])).1
      · exact .inr hc
    · exact .inr hc
  · simp at h

end EndToEnd
