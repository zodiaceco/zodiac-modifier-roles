import DecoderFaithfulness.Main

/-!
# Bitmask: the checked bits are bits of the spec bytes

`bitmaskSpec bs cv` states what a `Bitmask` condition with compValue `cv`
checks on the operand bytes `bs`, byte by byte. `decoder_bitmask` shows
that `BitmaskChecker.check`, which works on 32-byte chunks with a rinse mask
for the last chunk, returns exactly that on correctly encoded calldata,
with `bs` the spec bytes of the parameter: its 32-byte word, its content
for `bytes`/`string`, or the window below a `Slice`.
-/

namespace DecoderFaithfulness
open Roles

/-! ## Specification -/

/-- compValue layout (`BitmaskChecker` docs): `shift` (2 bytes), then `mask`
    and `expected`, `n` bytes each. -/
def bmN (cv : Bytes) : Nat := (cv.length - 2) / 2
def bmMask (cv : Bytes) : Bytes := (cv.drop 2).take (bmN cv)
def bmExpected (cv : Bytes) : Bytes := (cv.drop (2 + bmN cv)).take (bmN cv)

/-- What a Bitmask checks on the operand bytes `bs`: the `n` bytes at
    `shift` must exist (else `BitmaskOverflow`), and
    `bs[shift + j] & mask[j] = expected[j]` for every `j < n`. -/
def bitmaskSpec (bs cv : Bytes) : BitmaskStatus :=
  if sliceShift cv + bmN cv > bs.length then .BitmaskOverflow
  else if bmExpected cv = band ((bs.drop (sliceShift cv)).take (bmN cv)) (bmMask cv) then .Ok
  else .BitmaskNotAllowed

/-! ## Bytewise lemmas -/

theorem byte_and_255 (b : Byte) : b &&& 255 = b := by
  apply Fin.ext
  show (b.val &&& 255) % 256 = b.val
  have h : (255 : Nat) = 2 ^ 8 - 1 := by decide
  rw [h, Nat.and_two_pow_sub_one_eq_mod]
  simp [Nat.mod_eq_of_lt b.isLt]

theorem byte_and_0 (b : Byte) : b &&& 0 = 0 := by
  apply Fin.ext
  show (b.val &&& 0) % 256 = 0
  simp

theorem band_ones : ∀ l : Bytes, band l (List.replicate l.length 255) = l
  | [] => rfl
  | b :: l => by
    simp only [band, List.length_cons, List.replicate_succ, List.zipWith_cons_cons,
      byte_and_255]
    congr 1
    exact band_ones l

theorem band_zeros : ∀ l : Bytes, band l (zeros l.length) = zeros l.length
  | [] => rfl
  | b :: l => by
    simp only [band, zeros, List.length_cons, List.replicate_succ, List.zipWith_cons_cons,
      byte_and_0]
    congr 1
    exact band_zeros l

theorem length_band (a b : Bytes) : (band a b).length = min a.length b.length := by
  simp [band]

/-- The rinse mask keeps the first `k` bytes. -/
theorem band_rinse {x : Bytes} (hx : x.length = 32) (k : Nat) :
    band x (rinseMask k) = x.take (min k 32) ++ zeros (32 - min k 32) := by
  unfold rinseMask
  have hlen : (x.take (min k 32)).length = min k 32 := by simp [hx] <;> omega
  conv => lhs; rw [← List.take_append_drop (min k 32) x]
  unfold band
  rw [List.zipWith_append (by simp [hlen])]
  have h1 := band_ones (x.take (min k 32))
  have h2 := band_zeros (x.drop (min k 32))
  rw [hlen] at h1
  have hd : (x.drop (min k 32)).length = 32 - min k 32 := by simp [hx]
  rw [hd] at h2
  unfold band at h1 h2
  rw [h1, h2]

/-- `l.drop a ++ rest`, cut to 32 bytes, then to `k ≤ 32` bytes in bounds. -/
theorem take_chunk (l rest : Bytes) (a k : Nat) (hk : k ≤ 32) (h : a + k ≤ l.length) :
    ((l.drop a ++ rest).take 32).take k = (l.drop a).take k := by
  rw [List.take_take, Nat.min_eq_left hk, List.take_append_of_le_length (by simp; omega)]

theorem take_drop_take (l : Bytes) (n i k : Nat) (h : i + k ≤ n) :
    ((l.take n).drop i).take k = (l.drop i).take k := by
  rw [List.drop_take, List.take_take]
  congr 1
  omega

/-! ## The chunk loop -/

section Loop

variable (value cv junk bs : Bytes) (shift n : Nat)

/-- The loop compares `expected`, `actual & mask` chunk by chunk from byte
    `i`; that is equality of the whole remaining byte strings. `A`, `V`,
    `M` are the `expected`, operand and `mask` bytes (`n` each). -/
theorem bitmaskLoop_eq (A V M : Bytes)
    (hA : A = (cv.drop (2 + n)).take n) (hV : V = (bs.drop shift).take n)
    (hM : M = (cv.drop 2).take n)
    (hn : 2 + 2 * n ≤ cv.length ∨ n = 0)
    (hval : (value.take bs.length) = bs) (hbs : shift + n ≤ bs.length)
    (hvl : bs.length ≤ value.length) :
    ∀ f i, n ≤ i + 32 * f →
      bitmaskLoop value cv junk shift n f i =
        if A.drop i = band (V.drop i) (M.drop i) then .Ok else .BitmaskNotAllowed := by
  have hAl : A.length = n := by rw [hA]; simp; omega
  have hVl : V.length = n := by rw [hV]; simp; omega
  have hMl : M.length = n := by rw [hM]; simp; omega
  have hend : ∀ i, n ≤ i → A.drop i = band (V.drop i) (M.drop i) := by
    intro i hi
    rw [List.drop_eq_nil_of_le (by omega), List.drop_eq_nil_of_le (by omega),
      List.drop_eq_nil_of_le (by omega)]
    rfl
  intro f
  induction f with
  | zero =>
    intro i hi
    simp only [bitmaskLoop]
    rw [ite_eq_left (hend i (by omega))]
  | succ f ih =>
    intro i hi
    simp only [bitmaskLoop]
    by_cases hin : i < n
    · rw [ite_eq_left hin]
      have hcv : 2 + 2 * n ≤ cv.length := by rcases hn with h | h <;> omega
      have hk32 : min (n - i) 32 ≤ 32 := Nat.min_le_right _ _
      have hik : i + min (n - i) 32 ≤ n := by omega
      -- The chunks the loop compares, cut to `k = min (n - i) 32` bytes.
      have hexp : (mloadCv cv junk (n + i)).take (min (n - i) 32) =
          (A.drop i).take (min (n - i) 32) := by
        unfold mloadCv
        rw [List.append_assoc, take_chunk _ _ _ _ hk32 (by omega), hA,
          take_drop_take _ _ _ _ hik, List.drop_drop]
        congr 2; omega
      have hmask : (mloadCv cv junk i).take (min (n - i) 32) =
          (M.drop i).take (min (n - i) 32) := by
        unfold mloadCv
        rw [List.append_assoc, take_chunk _ _ _ _ hk32 (by omega), hM,
          take_drop_take _ _ _ _ hik, List.drop_drop]
      have hact : (loadBytes value (shift + i)).take (min (n - i) 32) =
          (V.drop i).take (min (n - i) 32) := by
        unfold loadBytes
        rw [take_chunk _ _ _ _ hk32 (by omega), hV, take_drop_take _ _ _ _ hik, List.drop_drop]
        conv => rhs; rw [← hval]
        rw [List.drop_take, List.take_take]
        congr 1; omega
      have hexpl : (mloadCv cv junk (n + i)).length = 32 := by simp [mloadCv] <;> omega
      have hmaskl : (mloadCv cv junk i).length = 32 := by simp [mloadCv] <;> omega
      have hactl : (loadBytes value (shift + i)).length = 32 := by simp [loadBytes] <;> omega
      have hbl : (band (loadBytes value (shift + i)) (mloadCv cv junk i)).length = 32 := by
        rw [length_band, hactl, hmaskl]; simp
      rw [band_rinse hexpl, band_rinse hbl]
      -- Chunk equality is equality of the first `k` bytes.
      have hA32 : (A.drop i).take 32 = (A.drop i).take (min (n - i) 32) := by
        rw [List.take_eq_take_iff]; simp [hAl]; omega
      have hB32 : (band (V.drop i) (M.drop i)).take 32 =
          (band (V.drop i) (M.drop i)).take (min (n - i) 32) := by
        rw [List.take_eq_take_iff]; simp [length_band, hVl, hMl]; omega
      have hchunk : (mloadCv cv junk (n + i)).take (min (n - i) 32) ++ zeros (32 - min (n - i) 32) =
            (band (loadBytes value (shift + i)) (mloadCv cv junk i)).take (min (n - i) 32) ++
              zeros (32 - min (n - i) 32) ↔
          (A.drop i).take 32 = (band (V.drop i) (M.drop i)).take 32 := by
        rw [hA32, hB32, hexp]
        have hb1 : (band (loadBytes value (shift + i)) (mloadCv cv junk i)).take (min (n - i) 32) =
            (band (V.drop i) (M.drop i)).take (min (n - i) 32) := by
          unfold band
          rw [List.take_zipWith, List.take_zipWith]
          unfold band at hact hmask
          rw [hact, hmask]
        rw [hb1]
        constructor
        · intro h; exact List.append_cancel_right h
        · intro h; rw [h]
      have hsplit : ∀ X Y : Bytes, X = Y ↔ X.take 32 = Y.take 32 ∧ X.drop 32 = Y.drop 32 := by
        intro X Y
        constructor
        · rintro rfl; exact ⟨rfl, rfl⟩
        · rintro ⟨h1, h2⟩
          rw [← List.take_append_drop 32 X, ← List.take_append_drop 32 Y, h1, h2]
      have hdropA : (A.drop i).drop 32 = A.drop (i + 32) := by rw [List.drop_drop]
      have hdropB : (band (V.drop i) (M.drop i)).drop 32 =
          band (V.drop (i + 32)) (M.drop (i + 32)) := by
        unfold band; rw [List.drop_zipWith, List.drop_drop, List.drop_drop]
      by_cases hc : (mloadCv cv junk (n + i)).take (min (n - i) 32) ++
            zeros (32 - min (n - i) 32) =
          (band (loadBytes value (shift + i)) (mloadCv cv junk i)).take (min (n - i) 32) ++
            zeros (32 - min (n - i) 32)
      · rw [ite_eq_right (fun h => h hc), ih (i + 32) (by omega)]
        have h32 := hchunk.mp hc
        have hiff : (A.drop i = band (V.drop i) (M.drop i)) ↔
            (A.drop (i + 32) = band (V.drop (i + 32)) (M.drop (i + 32))) := by
          rw [hsplit (A.drop i), hdropA, hdropB]
          simp only [h32, true_and]
        by_cases hfull : A.drop (i + 32) = band (V.drop (i + 32)) (M.drop (i + 32))
        · rw [ite_eq_left hfull, ite_eq_left (hiff.mpr hfull)]
        · rw [ite_eq_right hfull, ite_eq_right (fun h => hfull (hiff.mp h))]
      · rw [ite_eq_left hc, ite_eq_right]
        intro h
        exact hc (hchunk.mpr ((hsplit _ _).mp h).1)
    · rw [ite_eq_right hin, ite_eq_left (hend i (by omega))]

end Loop

/-- With the operand bytes `bs` at `start` (and `shift + n` within them),
    the loop returns the spec's verdict. -/
theorem bitmaskLoop_spec {data : Bytes} {start : Nat} {bs cv junk : Bytes}
    (hat : At data start bs) (hbs : sliceShift cv + bmN cv ≤ bs.length) :
    bitmaskLoop (data.drop start) cv junk (sliceShift cv) (bmN cv) (bmN cv) 0 =
      if bmExpected cv = band ((bs.drop (sliceShift cv)).take (bmN cv)) (bmMask cv)
      then .Ok else .BitmaskNotAllowed := by
  have hb := hat.bound
  rw [bitmaskLoop_eq (data.drop start) cv junk bs (sliceShift cv) (bmN cv) _ _ _ rfl rfl rfl
    (by unfold bmN; omega) hat.1 hbs (by simp; omega) (bmN cv) 0 (by omega)]
  simp only [List.drop_zero]; rfl

/-- Static operand (`inlined`): `size` bytes at `location`. -/
theorem bitmaskCheck_inlined {data : Bytes} {l : Nat} {bs : Bytes} (cv junk : Bytes)
    (hat : At data l bs) :
    bitmaskCheck data l cv true bs.length junk = bitmaskSpec bs cv := by
  have hb := hat.bound
  unfold bitmaskCheck bitmaskSpec
  simp only [Bool.true_eq_false, false_and, ite_false, ite_true]
  by_cases hov : sliceShift cv + bmN cv > bs.length
  · rw [show (cv.length - 2) / 2 = bmN cv from rfl, ite_eq_left hov, ite_eq_left hov]
  · rw [show (cv.length - 2) / 2 = bmN cv from rfl, ite_eq_right hov, ite_eq_right hov,
      ite_eq_right (by omega), bitmaskLoop_spec hat (by omega)]

/-- Dynamic operand: a length word at `location`, the content after it. -/
theorem bitmaskCheck_dynamic {data : Bytes} (hlen : data.length < 2 ^ 255) {l : Nat}
    {b : Bytes} (cv junk : Bytes) (size : Nat) (hat : At data l (encBytes b)) :
    bitmaskCheck data l cv false size junk = bitmaskSpec b cv := by
  have hb := hat.bound
  rw [length_encBytes] at hb
  have hcl : b.length < 2 ^ 256 := by
    have : (2 : Nat) ^ 255 < 2 ^ 256 := by decide
    have := ceil32_ge b.length
    omega
  have hload : load data l = b.length := by
    have h := hat
    unfold encBytes at h; rw [List.append_assoc] at h
    exact load_of_At_append h hcl
  have hc := At_content hat
  have hcb := hc.bound
  unfold bitmaskCheck bitmaskSpec
  simp only [Bool.false_eq_true, ite_false, hload, true_and]
  rw [ite_eq_right (by omega), show (cv.length - 2) / 2 = bmN cv from rfl]
  by_cases hov : sliceShift cv + bmN cv > b.length
  · rw [ite_eq_left hov, ite_eq_left hov]
  · rw [ite_eq_right hov, ite_eq_right hov, ite_eq_right (by omega), bitmaskLoop_spec hc (by omega)]

/-! ## Top-level statement -/

section Top

variable (root : Condition) (pre : Bytes) (args : List Val) (suffix : Bytes)

/-- **Bitmask.** For every visited `Bitmask` node (Integrity: on a `Static`
    or `Dynamic` parameter), `BitmaskChecker.check` returns exactly
    `bitmaskSpec` on the spec bytes of the described component: its word,
    its content for `bytes`/`string`, or below a `Slice` the window. This
    holds for any memory contents after the compValue (`junk`). Or the node
    is inside an interpretation that need not hold (only with `s = true`). -/
theorem decoder_bitmask {s : Bool}
    (hD : Desc s root (.call pre args)) (hR : RootOK root) (hZ : ZipOK s root)
    (hlen : (calldata pre args suffix).length < 2 ^ 255)
    {p : List Nat} {d : Condition} {l : Nat}
    (hv : Eval (calldata pre args suffix) (annotate root) p d l)
    (hop : d.operator = .Bitmask) (henc : d.encoding = .Static ∨ d.encoding = .Dynamic)
    (junk : Bytes) :
    (∃ u, (Val.call pre args).sub p = some u ∧
      bitmaskCheck (calldata pre args suffix) l d.compValue d.inlined d.size junk =
        bitmaskSpec (content u) d.compValue) ∨
    (∃ u bs, (Val.call pre args).sub p = some u ∧ IsWindow bs (content u) ∧
      bitmaskCheck (calldata pre args suffix) l d.compValue d.inlined d.size junk =
        bitmaskSpec bs d.compValue) ∨
    InStray s (calldata pre args suffix) (.call pre args) p d l := by
  rcases decoder_locations root pre args suffix hD hR hZ hlen hv with
    ⟨d0, u, _, rfl, hsub, hD0, hp, hr⟩ | ⟨d0, rfl, hns⟩ |
    ⟨d0, bs, u, rfl, hw, hat, _, _, hsub, hiw⟩ | hst
  · left
    refine ⟨u, hsub, ?_⟩
    have hop0 := annotate_op_of hop (by decide)
    have hmeta := hD0.annotate_meta
    rw [annotate_encoding] at henc
    match hD0 with
    | .word he _ _ hw =>
      have hat : At (calldata pre args suffix) l _ := hp
      simp only [hmeta.1, hmeta.2, Val.isStatic, ite_true, enc, annotate_compValue] at hat ⊢
      simpa [content] using bitmaskCheck_inlined (data := calldata pre args suffix) d0.compValue junk hat
    | .bytes he _ _ hu =>
      have hat := Placed.to_At_of_root hp hr (by rw [he]; decide) (by rw [he]; decide)
      rw [enc_bytesLike hu] at hat
      simp only [hmeta.1, isStatic_bytesLike hu, annotate_compValue]
      exact bitmaskCheck_dynamic hlen _ junk _ hat
    | .sliceWord _ h _ _ _ _ _ | .sliceBytes _ h _ _ _ _ _ => rw [hop0] at h; cases h
    | .tuple he _ _ _ | .array _ _ he _ _ _ _ _ | .call he _ _ _ _ | .logical _ he _ _ _ _ _ =>
      rw [he] at henc; simp at henc
  · exfalso
    rw [annotate_encoding] at henc
    rcases hns with hns | ⟨_, he, _, _⟩
    · cases hns with
      | leaf he _ _ => rcases he with he | he <;> simp [he] at henc
      | logical he _ _ => simp [he] at henc
    · simp [he] at henc
  · right; left
    refine ⟨u, bs, hsub, hiw, ?_⟩
    have hm := Win.annotate_meta hw
    simp only [Condition.withSize_inlined, Condition.withSize_size, Condition.withSize_compValue,
      hm.1, annotate_compValue]
    exact bitmaskCheck_inlined _ junk hat
  · right; right; exact hst

end Top

end DecoderFaithfulness
