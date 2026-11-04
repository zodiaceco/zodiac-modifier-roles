import SafeSigning.Basic

/-!
# What each signing function makes valid

* `uintToString_eq`: the library's `uintToString` is the decimal
  representation, for every `uint256` (every `Nat`).
* `personalSign_valid` / `personalSign_exact`: after `personalSign(m)`, the
  Safe's `isValidSignature(hash, "")` accepts the EIP-191 hash of `m`, and,
  unless keccak256 collides, no other hash or data.
* `signTyped_valid` / `signTyped_exact`: the same for `signTypedMessage` and
  the EIP-712 digest.
* `signMessage_raw`, `signMessage_personal`, `signMessage_typed`:
  `signMessage(m)` with a 32-byte `m` makes the raw hash `m` valid. For `m`
  the EIP-191 hash of a text, or the EIP-712 digest of a typed message, it
  stores the same key as `personalSign` / `signTypedMessage` of it: a
  permission that lets 32-byte messages through `signMessage` lets the role
  sign anything.
-/

namespace SafeSigning
open DecoderFaithfulness

/-! ## `uintToString` is the decimal -/

theorem decimal_lt {n : Nat} (h : n < 10) : decimal n = [⟨48 + n, by omega⟩] := by
  unfold decimal; rw [dif_pos h]

theorem decimal_ge {n : Nat} (h : ¬ n < 10) :
    decimal n = decimal (n / 10) ++
      [⟨48 + n % 10, by have := Nat.mod_lt n (show 10 > 0 by decide); omega⟩] := by
  rw [decimal, dif_neg h]

theorem countLoop_eq : ∀ (v f k : Nat), 0 < v → v < f → countLoop f v k = k + (decimal v).length := by
  intro v
  induction v using Nat.strongRecOn with
  | _ v ih =>
    intro f k hv hf
    obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
    simp only [countLoop, if_neg (show v ≠ 0 by omega)]
    by_cases h10 : v < 10
    · rw [decimal_lt h10, Nat.div_eq_of_lt h10]
      cases f <;> simp [countLoop]
    · rw [ih (v / 10) (by omega) f (k + 1) (by omega) (by omega), decimal_ge h10]
      simp; omega

theorem set_zeros (s : Bytes) (x : Byte) : ∀ n, (zeros (n + 1) ++ s).set n x = zeros n ++ x :: s
  | 0 => by simp [zeros]
  | n + 1 => by
    have : zeros (n + 1 + 1) ++ s = 0 :: (zeros (n + 1) ++ s) := by simp [zeros, List.replicate_succ]
    rw [this, List.set_cons_succ, set_zeros s x n]
    simp [zeros, List.replicate_succ]

theorem fillLoop_eq : ∀ (v f : Nat) (s : Bytes), 0 < v → v < f →
    fillLoop f v (decimal v).length (zeros (decimal v).length ++ s) = decimal v ++ s := by
  intro v
  induction v using Nat.strongRecOn with
  | _ v ih =>
    intro f s hv hf
    obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
    simp only [fillLoop, if_neg (show v ≠ 0 by omega)]
    by_cases h10 : v < 10
    · rw [decimal_lt h10]
      simp only [List.length_singleton, Nat.sub_self, Nat.div_eq_of_lt h10]
      rw [show zeros 1 ++ s = zeros (0 + 1) ++ s by rfl, set_zeros]
      have hd : (⟨48 + v % 10, by omega⟩ : Byte) = ⟨48 + v, by omega⟩ := by
        ext; simp [Nat.mod_eq_of_lt h10]
      cases f <;> simp [fillLoop, hd, zeros]
    · rw [decimal_ge h10]
      simp only [List.length_append, List.length_singleton, Nat.add_sub_cancel]
      rw [set_zeros]
      rw [ih (v / 10) (by omega) f _ (by omega) (by omega)]
      simp

/-- **`uintToString` is the decimal representation**, for every value. -/
theorem uintToString_eq (n : Nat) : uintToString n = decimal n := by
  unfold uintToString
  by_cases h : n = 0
  · subst h; rw [if_pos rfl, decimal_lt (by decide)]; rfl
  · rw [if_neg h]
    simp only
    rw [countLoop_eq n (n + 1) 0 (by omega) (by omega), Nat.zero_add]
    have := fillLoop_eq n (n + 1) [] (by omega) (by omega)
    simpa using this

/-! ## The `SafeMessage` hash determines its message, unless keccak collides -/

theorem safeMessageHash_inj (K : Bytes → Bytes) (th ds a b : Bytes)
    (h : safeMessageHash K th ds a = safeMessageHash K th ds b) :
    a = b ∨ CollisionIn K (safeMessageInputs K th ds a ++ safeMessageInputs K th ds b) := by
  unfold safeMessageHash at h
  rcases eq_or_collision (xs := safeMessageInputs K th ds a ++ safeMessageInputs K th ds b)
    (by simp [safeMessageInputs]) (by simp [safeMessageInputs]) h with h1 | hc
  · rcases eq_or_collision (xs := safeMessageInputs K th ds a ++ safeMessageInputs K th ds b)
      (by simp [safeMessageInputs]) (by simp [safeMessageInputs])
      (List.append_cancel_left h1) with h3 | hc
    · exact eq_or_collision (by simp [safeMessageInputs]) (by simp [safeMessageInputs])
        (List.append_cancel_left h3)
    · exact .inr hc
  · exact .inr hc

/-! ## `personalSign` -/

/-- **`personalSign(m)` makes the EIP-191 hash of `m` valid**: the Safe's
    `isValidSignature(personalHash m, "")` finds the key the library
    stored (`hTH`: the handler's `SAFE_MSG_TYPEHASH` is
    `keccak256("SafeMessage(bytes message)")`). -/
theorem personalSign_valid (K : Bytes → Bytes) (th ds m : Bytes) (hTH : th = safeTypeHash K) :
    valid32 K th ds (· = personalSignKey K ds m) (personalHash K m) := by
  unfold valid32 validBytes personalSignKey personalHash
  rw [hTH, uintToString_eq]

/-- **… and nothing else**: if a hash (or, for the `bytes` form, data) is
    valid because of that key, it is the EIP-191 hash of `m`, unless
    keccak256 collides. -/
theorem personalSign_exact (K : Bytes → Bytes) (th ds m h : Bytes) (hTH : th = safeTypeHash K)
    (hv : validBytes K th ds (· = personalSignKey K ds m) h) :
    h = personalHash K m ∨
      CollisionIn K (safeMessageInputs K th ds h ++ safeMessageInputs K th ds (personalHash K m)) := by
  unfold validBytes personalSignKey at hv
  subst hTH
  rw [uintToString_eq] at hv
  exact safeMessageHash_inj K _ ds h _ hv

/-! ## `signTypedMessage` -/

theorem signTyped_valid (K : Bytes → Bytes) (th ds digest : Bytes) (hTH : th = safeTypeHash K) :
    valid32 K th ds (· = signTypedKey K ds digest) digest := by
  unfold valid32 validBytes signTypedKey; rw [hTH]

theorem signTyped_exact (K : Bytes → Bytes) (th ds digest h : Bytes) (hTH : th = safeTypeHash K)
    (hv : validBytes K th ds (· = signTypedKey K ds digest) h) :
    h = digest ∨ CollisionIn K (safeMessageInputs K th ds h ++ safeMessageInputs K th ds digest) := by
  unfold validBytes signTypedKey at hv
  subst hTH
  exact safeMessageHash_inj K _ ds h _ hv

/-! ## `signMessage` signs raw hashes -/

/-- **`signMessage(m)` makes `isValidSignature(bytes32 m, "")` valid** for
    a 32-byte `m` (the handler checks `abi.encode(m)`, which is `m`): the
    Safe signs the raw hash `m`. -/
theorem signMessage_raw (K : Bytes → Bytes) (th ds m : Bytes) (hTH : th = safeTypeHash K) :
    valid32 K th ds (· = signMessageKey K ds m) m := by
  unfold valid32 validBytes signMessageKey; rw [hTH]

/-- `signMessage` of the EIP-191 hash of a text stores the key of
    `personalSign` of that text. -/
theorem signMessage_personal (K : Bytes → Bytes) (ds m : Bytes) :
    signMessageKey K ds (personalHash K m) = personalSignKey K ds m := by
  unfold signMessageKey personalSignKey personalHash; rw [uintToString_eq]

/-- `signMessage` of an EIP-712 digest stores the key of `signTypedMessage`
    of that message. -/
theorem signMessage_typed (K : Bytes → Bytes) (ds digest : Bytes) :
    signMessageKey K ds digest = signTypedKey K ds digest := rfl

end SafeSigning
