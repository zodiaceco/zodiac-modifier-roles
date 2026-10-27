import DecoderFaithfulness.Bytes

/-!
# Signing through the Safe: what `SignTypedMessageLib` stores and what the
# Safe's `isValidSignature` checks

`SignTypedMessageLib` runs in the Safe (delegatecall) and writes
`signedMessages[key] = 1`. The Safe's `CompatibilityFallbackHandler` (1.3.0 /
1.4.1, transcribed here) answers EIP-1271 `isValidSignature` with an empty
signature by looking that mapping up. Both build the key as Safe's
`SafeMessage` hash.

`K` is keccak256, a parameter. The only fact about it the theorems use is
that its outputs are 32 bytes. "Nothing else is signed" holds unless `K`
collides on two inputs the statement names (`CollisionIn K xs`, with `xs`
computed from the statement's own values): exhibiting one would be a
keccak256 collision. (Some collision of keccak256 exists, since it has more
inputs than outputs, so "unless `K` has any collision" would prove nothing.)

The reference for `personalSign` is EIP-191 itself: the message is prefixed
with `"\x19Ethereum Signed Message:\n"` and its length in decimal.
-/

namespace SafeSigning
open DecoderFaithfulness

/-- ASCII bytes of a string. -/
def ascii (s : String) : Bytes := s.toList.map fun c => ⟨c.toNat % 256, Nat.mod_lt _ (by decide)⟩

/-! ## EIP-191 (spec) -/

/-- `n` in decimal, most significant digit first (ASCII). -/
def decimal (n : Nat) : Bytes :=
  if h : n < 10 then [⟨48 + n, by omega⟩]
  else decimal (n / 10) ++ [⟨48 + n % 10, by have := Nat.mod_lt n (show 10 > 0 by decide); omega⟩]
termination_by n
decreasing_by omega

/-- `"\x19Ethereum Signed Message:\n"`. -/
def prefix191 : Bytes := [0x19] ++ ascii "Ethereum Signed Message:\n"

/-- The EIP-191 `personal_sign` hash of a message (ethers' `hashMessage`). -/
def personalHash (K : Bytes → Bytes) (m : Bytes) : Bytes :=
  K (prefix191 ++ decimal m.length ++ m)

/-! ## `uintToString` (`SignTypedMessageLib.sol`) -/

/-- First loop: count the digits. -/
def countLoop : Nat → Nat → Nat → Nat
  | 0, _, digits => digits
  | f + 1, temp, digits => if temp = 0 then digits else countLoop f (temp / 10) (digits + 1)

/-- Second loop: write the digits from the end of the buffer. -/
def fillLoop : Nat → Nat → Nat → Bytes → Bytes
  | 0, _, _, buffer => buffer
  | f + 1, value, digits, buffer =>
    if value = 0 then buffer
    else
      fillLoop f (value / 10) (digits - 1)
        (buffer.set (digits - 1) ⟨48 + value % 10, by
          have := Nat.mod_lt value (show 10 > 0 by decide); omega⟩)

/-- `uintToString(value)` (fuel `value + 1`: every iteration divides by 10). -/
def uintToString (value : Nat) : Bytes :=
  if value = 0 then ascii "0"
  else
    let digits := countLoop (value + 1) value 0
    fillLoop (value + 1) value digits (zeros digits)

/-! ## The `SafeMessage` hash -/

/-- `keccak256("SafeMessage(bytes message)")`, as the library computes it. -/
def safeTypeHash (K : Bytes → Bytes) : Bytes := K (ascii "SafeMessage(bytes message)")

/-- `keccak256(abi.encodePacked(0x19, 0x01, domainSeparator,
    keccak256(abi.encode(typeHash, keccak256(message)))))`: the library's
    `safeMessagePreimage` hashed, and the handler's
    `getMessageHashForSafe`. -/
def safeMessageHash (K : Bytes → Bytes) (typeHash ds m : Bytes) : Bytes :=
  K ([0x19, 0x01] ++ ds ++ K (typeHash ++ K m))

/-! ## `SignTypedMessageLib`: the key each function stores -/

/-- `signMessage(message)`. -/
def signMessageKey (K : Bytes → Bytes) (ds m : Bytes) : Bytes :=
  safeMessageHash K (safeTypeHash K) ds m

/-- `personalSign(message)`: `abi.encode(keccak256(wrapped))` is the
    32-byte hash itself. -/
def personalSignKey (K : Bytes → Bytes) (ds m : Bytes) : Bytes :=
  safeMessageHash K (safeTypeHash K) ds (K (prefix191 ++ uintToString m.length ++ m))

/-- `signTypedMessage`: `abi.encode(hashTypedMessage(..))` is the 32-byte
    digest (`EIP712.hashTypedMessage_spec`: the EIP-712 digest). -/
def signTypedKey (K : Bytes → Bytes) (ds digest : Bytes) : Bytes :=
  safeMessageHash K (safeTypeHash K) ds digest

/-! ## `CompatibilityFallbackHandler.isValidSignature`, empty signature -/

/-- `isValidSignature(bytes data, "")`: the magic value iff
    `signedMessages[getMessageHashForSafe(safe, data)] != 0` (else it
    reverts). `signed` is the set of keys with a non-zero entry;
    `handlerTypeHash` is the handler's constant `SAFE_MSG_TYPEHASH`. -/
def validBytes (K : Bytes → Bytes) (handlerTypeHash ds : Bytes) (signed : Bytes → Prop)
    (data : Bytes) : Prop :=
  signed (safeMessageHash K handlerTypeHash ds data)

/-- `isValidSignature(bytes32 hash, "")`: the legacy check on
    `abi.encode(hash)`, the 32 bytes of `hash`. -/
def valid32 (K : Bytes → Bytes) (handlerTypeHash ds : Bytes) (signed : Bytes → Prop)
    (h : Bytes) : Prop :=
  validBytes K handlerTypeHash ds signed h

/-- `K` collides on two of the inputs `xs`. Theorems name `xs` explicitly,
    from their own values, so the alternative is a concrete collision. -/
def CollisionIn (K : Bytes → Bytes) (xs : List Bytes) : Prop :=
  ∃ x ∈ xs, ∃ y ∈ xs, x ≠ y ∧ K x = K y

theorem CollisionIn.mono {K : Bytes → Bytes} {xs ys : List Bytes} (h : CollisionIn K xs)
    (hs : ∀ x ∈ xs, x ∈ ys) : CollisionIn K ys := by
  obtain ⟨x, hx, y, hy, hne, he⟩ := h
  exact ⟨x, hs x hx, y, hs y hy, hne, he⟩

/-- `K x = K y` for named `x`, `y`: they are equal, or a collision among them. -/
theorem eq_or_collision {K : Bytes → Bytes} {x y : Bytes} {xs : List Bytes}
    (hx : x ∈ xs) (hy : y ∈ xs) (h : K x = K y) : x = y ∨ CollisionIn K xs := by
  by_cases hne : x = y
  · exact .inl hne
  · exact .inr ⟨x, hx, y, hy, hne, h⟩

/-- The three inputs `safeMessageHash K typeHash ds m` hashes. -/
def safeMessageInputs (K : Bytes → Bytes) (typeHash ds m : Bytes) : List Bytes :=
  [m, typeHash ++ K m, [0x19, 0x01] ++ ds ++ K (typeHash ++ K m)]

end SafeSigning
