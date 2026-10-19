/-!
# Bytes and 32-byte words

Shared by the ABI specification (`Spec.lean`) and the Roles transcription
(`Roles.lean`). Only generic big-endian helpers live here, nothing
ABI- or Roles-specific.
-/

namespace AbiLayerA

abbrev Byte := Fin 256
abbrev Bytes := List Byte

/-- Big-endian value of a byte string. -/
def wordVal (bs : Bytes) : Nat :=
  bs.foldl (fun acc b => acc * 256 + b.val) 0

/-- `k`-byte big-endian encoding of `n` (truncated mod `256^k`). -/
def natBE : Nat → Nat → Bytes
  | 0, _ => []
  | k + 1, n => natBE k (n / 256) ++ [⟨n % 256, Nat.mod_lt _ (by decide)⟩]

/-- A 32-byte ABI word holding `n`. -/
def word (n : Nat) : Bytes := natBE 32 n

def zeros (k : Nat) : Bytes := List.replicate k 0

/-- Round up to a multiple of 32. -/
def ceil32 (n : Nat) : Nat := (n + 31) / 32 * 32

theorem length_natBE (k n : Nat) : (natBE k n).length = k := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih => simp [natBE, ih]

@[simp] theorem length_word (n : Nat) : (word n).length = 32 := length_natBE 32 n

@[simp] theorem length_zeros (k : Nat) : (zeros k).length = k := by simp [zeros]

theorem wordVal_append_single (l : Bytes) (b : Byte) :
    wordVal (l ++ [b]) = wordVal l * 256 + b.val := by
  simp [wordVal, List.foldl_append]

theorem wordVal_natBE (k n : Nat) (h : n < 256 ^ k) : wordVal (natBE k n) = n := by
  induction k generalizing n with
  | zero => simp [Nat.pow_zero] at h; subst h; rfl
  | succ k ih =>
    simp only [natBE, wordVal_append_single]
    have h' : n / 256 < 256 ^ k := by
      rw [Nat.pow_succ] at h
      exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact h)
    rw [ih _ h']
    show n / 256 * 256 + n % 256 = n
    have := Nat.div_add_mod n 256
    omega

theorem wordVal_word (n : Nat) (h : n < 2 ^ 256) : wordVal (word n) = n := by
  apply wordVal_natBE
  have : (256 : Nat) ^ 32 = 2 ^ 256 := by decide
  omega

theorem ceil32_ge (n : Nat) : n ≤ ceil32 n := by
  unfold ceil32
  have := Nat.div_add_mod (n + 31) 32
  have := Nat.mod_lt (n + 31) (show 32 > 0 by decide)
  omega

end AbiLayerA
