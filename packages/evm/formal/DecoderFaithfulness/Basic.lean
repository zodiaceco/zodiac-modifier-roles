import DecoderFaithfulness.Desc

/-! # Basic lemmas: words, placement, spec encoding -/

namespace DecoderFaithfulness
open Roles

/-! ## Rounding: `(x + 31) & ~uint256(31)` -/

theorem and_notU31 (x : Nat) (h : x < 2 ^ 256) : x &&& notU31 = x / 32 * 32 := by
  unfold notU31
  apply Nat.eq_of_testBit_eq
  intro i
  have hm : (2 ^ 256 - 32 : Nat) = (2 ^ 251 - 1) <<< 5 := by decide
  have hq : x / 32 * 32 = (x >>> 5) <<< 5 := by
    simp [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  rw [hm, hq, Nat.testBit_and, Nat.testBit_shiftLeft, Nat.testBit_shiftLeft,
    Nat.testBit_two_pow_sub_one, Nat.testBit_shiftRight]
  by_cases h5 : 5 ≤ i
  · have : 5 + (i - 5) = i := by omega
    rw [this]
    by_cases h256 : i < 256
    · simp [h5]; omega
    · have hx : x.testBit i = false := Nat.testBit_lt_two_pow (by
        calc x < 2 ^ 256 := h
          _ ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) (by omega))
      simp [h5, hx]
  · simp [h5]

theorem roundUp_eq (n : Nat) (h : n + 31 < 2 ^ 256) : (n + 31) &&& notU31 = ceil32 n := by
  rw [and_notU31 _ h]; rfl

/-! ## Placement -/

theorem At.bound {data : Bytes} {l : Nat} {bs : Bytes} (h : At data l bs) :
    l + bs.length ≤ data.length := h.2

theorem At_append {data : Bytes} {l : Nat} {a b : Bytes} :
    At data l (a ++ b) ↔ At data l a ∧ At data (l + a.length) b := by
  unfold At
  simp only [List.length_append]
  constructor
  · rintro ⟨h1, h2⟩
    rw [List.take_add] at h1
    have hlen : ((data.drop l).take a.length).length = a.length := by
      simp; omega
    obtain ⟨ha, hb⟩ := List.append_inj h1 hlen
    refine ⟨⟨ha, by omega⟩, ?_, by omega⟩
    rw [List.drop_drop] at hb
    exact hb
  · rintro ⟨⟨ha, _⟩, hb, hb2⟩
    refine ⟨?_, by omega⟩
    rw [List.take_add, ha, List.drop_drop, hb]

theorem At_nil (data : Bytes) (l : Nat) (h : l ≤ data.length) : At data l [] := by
  simp [At, h]

/-- Reading a word that the encoding placed. -/
theorem load_of_At {data : Bytes} {l n : Nat} (h : At data l (word n)) (hn : n < 2 ^ 256) :
    load data l = n := by
  unfold load
  obtain ⟨h1, h2⟩ := h
  simp only [length_word] at h1 h2
  rw [List.take_append_of_le_length (by simp; omega), h1, wordVal_word n hn]

theorem load_of_At_append {data : Bytes} {l n : Nat} {rest : Bytes}
    (h : At data l (word n ++ rest)) (hn : n < 2 ^ 256) : load data l = n :=
  load_of_At (At_append.mp h).1 hn

/-- Bytes Roles extracts with `data[l:l+size]`. -/
theorem take_of_At {data : Bytes} {l : Nat} {bs : Bytes} (h : At data l bs) :
    (data.drop l).take bs.length = bs := h.1

/-! ## Spec encoding: shapes and lengths -/

theorem encParts_fst_length (vs : List Val) (off : Nat) :
    (encParts vs off).1.length = headLen vs := by
  induction vs generalizing off with
  | nil => simp [encParts, headLen]
  | cons v vs ih =>
    by_cases hs : v.isStatic
    · simp [encParts, headLen, hs, ih]
    · simp [encParts, headLen, hs, ih]

theorem encParts_snd_nil (vs : List Val) (off : Nat) (h : Val.allStatic vs = true) :
    (encParts vs off).2 = [] := by
  induction vs generalizing off with
  | nil => simp [encParts]
  | cons v vs ih =>
    simp [Val.allStatic] at h
    simp [encParts, h.1, ih _ h.2]

theorem encTuple_length_static (vs : List Val) (h : Val.allStatic vs = true) :
    (encTuple vs).length = headLen vs := by
  simp [encTuple, encParts_snd_nil vs _ h, encParts_fst_length]

theorem length_encBytes (b : Bytes) : (encBytes b).length = 32 + ceil32 b.length := by
  simp [encBytes]
  have := ceil32_ge b.length
  omega

theorem encTuple_length_ge (vs : List Val) : headLen vs ≤ (encTuple vs).length := by
  simp [encTuple, encParts_fst_length]

/-! ## Bytes-like values and windows -/

theorem enc_bytesLike {u : Val} (h : IsBytesLike u) : enc u = encBytes (content u) := by
  cases u with
  | bytes b => simp [enc, content]
  | call pre args => simp [enc_call, content]
  | _ => simp [IsBytesLike] at h

theorem isStatic_bytesLike {u : Val} (h : IsBytesLike u) : u.isStatic = false := by
  cases u <;> simp_all [IsBytesLike, Val.isStatic]

/-- The content of an encoded bytes value starts after its length word. -/
theorem At_content {data : Bytes} {l : Nat} {b : Bytes} (h : At data l (encBytes b)) :
    At data (l + 32) b := by
  unfold encBytes at h
  have := (At_append.mp (At_append.mp h).1).2
  simpa using this

theorem length_window {bs : Bytes} {shift size : Nat} (h : shift + size ≤ bs.length) :
    (window bs shift size).length = size := by
  simp [window]; omega

theorem At_window {data : Bytes} {l : Nat} {bs : Bytes} {shift size : Nat}
    (h : At data l bs) (hb : shift + size ≤ bs.length) :
    At data (l + shift) (window bs shift size) := by
  obtain ⟨h1, h2⟩ := h
  unfold At
  rw [length_window hb]
  refine ⟨?_, by omega⟩
  unfold window
  rw [← List.drop_drop]
  conv => rhs; rw [← h1]
  rw [List.drop_take, List.take_take]
  congr 1
  omega

theorem IsWindow.refl (bs : Bytes) : IsWindow bs bs := ⟨0, by simp, by simp⟩

theorem IsWindow.window {bs : Bytes} {shift size : Nat} (h : shift + size ≤ bs.length) :
    IsWindow (window bs shift size) bs :=
  ⟨shift, by rw [length_window h]; exact h, by rw [length_window h]; rfl⟩

theorem IsWindow.trans {a b c : Bytes} (hab : IsWindow a b) (hbc : IsWindow b c) :
    IsWindow a c := by
  obtain ⟨i, hi, ha⟩ := hab
  obtain ⟨j, hj, hb⟩ := hbc
  refine ⟨j + i, by omega, ?_⟩
  calc a = (b.drop i).take a.length := ha
    _ = (((c.drop j).take b.length).drop i).take a.length := by rw [← hb]
    _ = (c.drop (j + i)).take a.length := by
      rw [List.drop_take, List.take_take, List.drop_drop]
      congr 1
      omega

end DecoderFaithfulness
