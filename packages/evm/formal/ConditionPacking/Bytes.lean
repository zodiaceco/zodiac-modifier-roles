import ConditionPacking.Model

/-! # Lemmas: big-endian bytes, memory, EVM word operations -/

namespace ConditionPacking
open DecoderFaithfulness DecoderFaithfulness.Roles

/-! ## `getD` on lists -/

theorem getD_app (a b : Bytes) (q : Nat) :
    (a ++ b).getD q 0 = if q < a.length then a.getD q 0 else b.getD (q - a.length) 0 := by
  simp only [List.getD_eq_getElem?_getD]
  split
  · rw [List.getElem?_append_left (by omega)]
  · rw [List.getElem?_append_right (by omega)]

@[simp] theorem getD_zeros (k q : Nat) : (zeros k).getD q 0 = 0 := by
  simp only [zeros, List.getD_eq_getElem?_getD, List.getElem?_replicate]
  split <;> rfl

theorem getD_of_ge (l : Bytes) (q : Nat) (h : l.length ≤ q) : l.getD q 0 = 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

/-- Two lists are equal if they have the same length and agree under `getD`. -/
theorem ext_getD {a b : Bytes} (hl : a.length = b.length)
    (h : ∀ q < a.length, a.getD q 0 = b.getD q 0) : a = b := by
  apply List.ext_getElem hl
  intro q h1 h2
  have := h q h1
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1,
    List.getElem?_eq_getElem h2, Option.getD_some] at this
  exact this

/-! ## Big-endian values -/

theorem snoc_induction {P : Bytes → Prop} (h0 : P []) (h1 : ∀ l x, P l → P (l ++ [x]))
    (l : Bytes) : P l := by
  rw [← List.reverse_reverse l]
  induction l.reverse with
  | nil => exact h0
  | cons x t ih => rw [List.reverse_cons]; exact h1 _ _ ih

@[simp] theorem wordVal_nil : wordVal [] = 0 := rfl

theorem wordVal_append (a b : Bytes) :
    wordVal (a ++ b) = wordVal a * 256 ^ b.length + wordVal b := by
  induction b using snoc_induction with
  | h0 => simp
  | h1 b x ih =>
    rw [← List.append_assoc, wordVal_append_single, wordVal_append_single, ih,
      List.length_append, List.length_singleton, Nat.pow_succ, Nat.add_mul, Nat.mul_assoc,
      Nat.add_assoc]

theorem wordVal_lt (l : Bytes) : wordVal l < 256 ^ l.length := by
  induction l using snoc_induction with
  | h0 => simp
  | h1 l x ih =>
    rw [wordVal_append_single, List.length_append, List.length_singleton, Nat.pow_succ]
    have := x.isLt
    generalize wordVal l = w at *
    generalize 256 ^ l.length = P at *
    have : w + 1 ≤ P := ih
    have : (w + 1) * 256 ≤ P * 256 := Nat.mul_le_mul_right _ this
    rw [Nat.add_mul] at this
    omega

theorem natBE_wordVal (l : Bytes) : natBE l.length (wordVal l) = l := by
  induction l using snoc_induction with
  | h0 => rfl
  | h1 l x ih =>
    rw [List.length_append, List.length_singleton, natBE, wordVal_append_single]
    have hx := x.isLt
    have h1 : (wordVal l * 256 + x.val) / 256 = wordVal l := by omega
    have h2 : (wordVal l * 256 + x.val) % 256 = x.val := by omega
    rw [h1, ih]
    congr

theorem natBE_add (a b x y : Nat) (hy : y < 256 ^ b) :
    natBE (a + b) (x * 256 ^ b + y) = natBE a x ++ natBE b y := by
  induction b generalizing y with
  | zero => simp [Nat.pow_zero] at hy; subst hy; simp [natBE]
  | succ b ih =>
    rw [← Nat.add_assoc, natBE, natBE]
    have hy' : y / 256 < 256 ^ b := by
      rw [Nat.pow_succ] at hy; exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hy)
    have e1 : (x * 256 ^ (b + 1) + y) / 256 = x * 256 ^ b + y / 256 := by
      rw [Nat.pow_succ, ← Nat.mul_assoc]; generalize x * 256 ^ b = X; omega
    have e2 : (x * 256 ^ (b + 1) + y) % 256 = y % 256 := by
      rw [Nat.pow_succ, ← Nat.mul_assoc]; generalize x * 256 ^ b = X; omega
    simp only [e1, e2, ih _ hy', List.append_assoc]

theorem natBE_zero (k : Nat) : natBE k 0 = zeros k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [natBE, Nat.zero_div, ih]; simp [zeros, List.replicate_succ']

theorem wordVal_natBE' (k n : Nat) (h : n < 256 ^ k) : wordVal (natBE k n) = n :=
  wordVal_natBE k n h

/-! ## Memory -/

@[simp] theorem Mem.length_read (m : Mem) (p k : Nat) : (m.read p k).length = k := by
  simp [Mem.read]

theorem Mem.getD_read (m : Mem) (p k i : Nat) (h : i < k) : (m.read p k).getD i 0 = m (p + i) := by
  simp [Mem.read, List.getD_eq_getElem?_getD, h]

theorem Mem.read_ext {m m' : Mem} {p k : Nat} (h : ∀ i < k, m (p + i) = m' (p + i)) :
    m.read p k = m'.read p k := by
  apply ext_getD (by simp)
  intro q hq; simp at hq
  rw [Mem.getD_read _ _ _ _ hq, Mem.getD_read _ _ _ _ hq, h q hq]

theorem Mem.read_add (m : Mem) (p a b : Nat) : m.read p (a + b) = m.read p a ++ m.read (p + a) b := by
  apply ext_getD (by simp)
  intro q hq; simp at hq
  rw [Mem.getD_read _ _ _ _ hq, getD_app]
  simp only [Mem.length_read]
  split
  · rw [Mem.getD_read _ _ _ _ (by omega)]
  · rw [Mem.getD_read _ _ _ _ (by omega)]; congr 1; omega

/-- Reading back what is in memory: `m.read p k = l` iff the bytes match. -/
theorem Mem.read_eq {m : Mem} {p : Nat} {l : Bytes}
    (h : ∀ i < l.length, m (p + i) = l.getD i 0) : m.read p l.length = l := by
  apply ext_getD (by simp)
  intro q hq; simp at hq
  rw [Mem.getD_read _ _ _ _ hq, h q hq]

theorem Mem.write_apply (m : Mem) (p : Nat) (bs : Bytes) (q : Nat) :
    m.write p bs q = if p ≤ q ∧ q < p + bs.length then bs.getD (q - p) 0 else m q := rfl

/-! ## EVM word operations -/

theorem two_pow_8 (k : Nat) : 2 ^ (8 * k) = 256 ^ k := by
  rw [Nat.pow_mul]

/-- `shr(8 * (32 - k), mload(p))` is the big-endian value of the first `k`
    bytes at `p`. -/
theorem shr_mload (m : Mem) (p k : Nat) (hk : k ≤ 32) :
    shr (8 * (32 - k)) (mload m p) = wordVal (m.read p k) := by
  unfold shr mload
  have : 32 = k + (32 - k) := by omega
  rw [this, Mem.read_add, wordVal_append, ← this]
  simp only [Mem.length_read]
  rw [Nat.shiftRight_eq_div_pow, two_pow_8]
  have := wordVal_lt (m.read (p + k) (32 - k))
  simp only [Mem.length_read] at this
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.pow_pos (by decide)),
    Nat.div_eq_of_lt this, Nat.zero_add]

theorem shr224_mload (m : Mem) (p : Nat) : shr 224 (mload m p) = wordVal (m.read p 4) :=
  shr_mload m p 4 (by decide)

theorem shr240_mload (m : Mem) (p : Nat) : shr 240 (mload m p) = wordVal (m.read p 2) :=
  shr_mload m p 2 (by decide)

theorem shl_eq (s x : Nat) (h : x * 2 ^ s < 2 ^ 256) : shl s x = x * 2 ^ s := by
  unfold shl; rw [Nat.shiftLeft_eq, Nat.mod_eq_of_lt h]

/-- `mstore(p, shl(8 * (32 - k), x))` writes `x` as `k` bytes, then zeros. -/
theorem mstore_shl (m : Mem) (p k x : Nat) (hk : k ≤ 32) (hx : x < 256 ^ k) :
    mstore m p (shl (8 * (32 - k)) x) = m.write p (natBE k x ++ zeros (32 - k)) := by
  have hlt : x * 256 ^ (32 - k) < 2 ^ 256 :=
    calc x * 256 ^ (32 - k) < 256 ^ k * 256 ^ (32 - k) :=
          Nat.mul_lt_mul_of_pos_right hx (Nat.pow_pos (by decide))
      _ = 256 ^ 32 := by rw [← Nat.pow_add, Nat.add_sub_cancel' hk]
      _ = 2 ^ 256 := by decide
  unfold mstore word
  rw [shl_eq _ _ (by rw [two_pow_8]; exact hlt), two_pow_8]
  have h := natBE_add k (32 - k) x 0 (Nat.pow_pos (by decide))
  rw [Nat.add_sub_cancel' hk, Nat.add_zero, natBE_zero] at h
  rw [h]

/-- The node write of `_packNodes`: `mstore(p, or(mload(p), shl(224, x)))`
    on four zero bytes writes `x` there and leaves the other 28 bytes. -/
theorem mstore_or_shl224 (m : Mem) (p x : Nat) (hx : x < 2 ^ 32)
    (hz : ∀ i < 4, m (p + i) = 0) :
    mstore m p (mload m p ||| shl 224 x) = m.write p (natBE 4 x) := by
  have hread : m.read p 32 = zeros 4 ++ m.read (p + 4) 28 := by
    rw [show (32 : Nat) = 4 + 28 from rfl, Mem.read_add]
    congr 1
    have := Mem.read_eq (m := m) (p := p) (l := zeros 4) (by
      intro i hi; simp at hi; rw [hz i hi, getD_zeros])
    simpa using this
  have hw : mload m p = wordVal (m.read (p + 4) 28) := by
    unfold mload; rw [hread, wordVal_append]
    simp [zeros, wordVal]
  have hlt := wordVal_lt (m.read (p + 4) 28)
  simp only [Mem.length_read] at hlt
  have hshl : shl 224 x = 2 ^ 224 * x := by
    rw [shl_eq _ _ (by
      calc x * 2 ^ 224 < 2 ^ 32 * 2 ^ 224 :=
            Nat.mul_lt_mul_of_pos_right hx (Nat.pow_pos (by decide))
        _ = 2 ^ 256 := by rw [← Nat.pow_add]), Nat.mul_comm]
  have hor : mload m p ||| shl 224 x = x * 256 ^ 28 + wordVal (m.read (p + 4) 28) := by
    rw [hw, hshl, Nat.or_comm, ← Nat.two_pow_add_eq_or_of_lt (by
      have : (256 : Nat) ^ 28 = 2 ^ 224 := by decide
      omega), Nat.mul_comm]
  unfold mstore word
  rw [hor, show (32 : Nat) = 4 + 28 from rfl, natBE_add _ _ _ _ hlt]
  have := natBE_wordVal (m.read (p + 4) 28)
  simp only [Mem.length_read] at this
  rw [this]
  have hR : ∀ i < 28, (m.read (p + 4) 28).getD i 0 = m (p + 4 + i) :=
    fun i hi => Mem.getD_read _ _ _ _ hi
  have hRl : (m.read (p + 4) 28).length = 28 := Mem.length_read _ _ _
  have hAl : (natBE 4 x).length = 4 := length_natBE 4 x
  generalize m.read (p + 4) 28 = R at *
  generalize natBE 4 x = A at *
  funext q
  rw [Mem.write_apply, Mem.write_apply, List.length_append, hAl, hRl]
  by_cases h2 : p ≤ q ∧ q < p + (4 + 28)
  · rw [if_pos h2]
    by_cases h1 : p ≤ q ∧ q < p + 4
    · rw [if_pos h1, getD_app, hAl, if_pos (show q - p < 4 by omega)]
    · rw [if_neg h1, getD_app, hAl, if_neg (show ¬ q - p < 4 by omega),
        hR (q - p - 4) (by omega), show p + 4 + (q - p - 4) = q by omega]
  · rw [if_neg h2, if_neg (show ¬ (p ≤ q ∧ q < p + 4) by omega)]

end ConditionPacking
