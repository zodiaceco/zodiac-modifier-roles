import TargetDecode.Loose
import DecoderFaithfulness.Basic

/-!
# The spec encoding is one of the layouts

A value whose spec encoding sits at `l` is also what following offsets from
`l` reads: `canon_LP`. With `LP.det`, a region that holds the spec encoding
of `v` is read as `v` by any decoder that follows offsets from its start,
whatever else the calldata holds (`region_det`).
-/

namespace TargetDecode
open DecoderFaithfulness DecoderFaithfulness.Roles

theorem At_self (c : Bytes) : At c 0 c := by simp [At]

mutual
  /-- Every array of the value has fewer than `2^256` elements (its count
      fits in a word). -/
  def small : Val → Bool
    | .word _ | .bytes _ => true
    | .tuple vs => smallAll vs
    | .array vs => decide (vs.length < 2 ^ 256) && smallAll vs
    | .call _ args => smallAll args
  def smallAll : List Val → Bool
    | [] => true
    | v :: vs => small v && smallAll vs
end

theorem smallAll_get : ∀ {vs : List Val}, smallAll vs = true →
    ∀ i (h : i < vs.length), small vs[i] = true
  | v :: vs, h, 0, _ => by simp only [smallAll, Bool.and_eq_true] at h; exact h.1
  | v :: vs, h, i + 1, hi => by
    simp only [smallAll, Bool.and_eq_true] at h
    exact smallAll_get h.2 i (by simp at hi; omega)

/-- The components of a block in spec encoding: static ones in place, dynamic
    ones through an offset word that points at their encoding. -/
theorem slots_canon {data : Bytes} (hlen : data.length < 2 ^ 255) (st : Nat) :
    ∀ (vs : List Val) (h off : Nat),
    At data (st + h) (encParts vs off).1 → At data (st + off) (encParts vs off).2 →
    ∀ k (hk : k < vs.length),
      (vs[k].isStatic = true → At data (st + h + headOff vs k) (enc vs[k])) ∧
      (vs[k].isStatic = false → st + h + headOff vs k + 32 ≤ data.length ∧
        At data (st + load data (st + h + headOff vs k)) (enc vs[k]))
  | [], _, _, _, _, k, hk => by simp at hk
  | v :: vs, h, off, hH, hT, k, hk => by
    by_cases hs : v.isStatic
    · simp only [encParts, hs, ite_true] at hH hT
      obtain ⟨hv, hH'⟩ := At_append.mp hH
      cases k with
      | zero =>
        simp only [List.getElem_cons_zero, headOff, Nat.add_zero, hs]
        exact ⟨fun _ => hv, fun h => by simp at h⟩
      | succ k =>
        have ih := slots_canon hlen st vs (h + (enc v).length) off
          (by rw [← Nat.add_assoc]; exact hH') hT k (by simp at hk; omega)
        simp only [List.getElem_cons_succ, headOff, hs, ite_true]
        rw [show st + h + ((enc v).length + headOff vs k) =
          st + (h + (enc v).length) + headOff vs k by omega]
        exact ih
    · simp only [encParts, hs, ite_false, Bool.false_eq_true] at hH hT
      obtain ⟨hw, hH'⟩ := At_append.mp hH
      obtain ⟨hv, hT'⟩ := At_append.mp hT
      cases k with
      | zero =>
        simp only [List.getElem_cons_zero, headOff, Nat.add_zero]
        have hb := hT.bound
        have hwb := hw.bound
        simp only [length_word] at hwb
        have hoff : off < 2 ^ 256 := by
          have : (2 : Nat) ^ 255 < 2 ^ 256 := by decide
          omega
        rw [load_of_At hw hoff]
        exact ⟨fun h => by simp [hs] at h, fun _ => ⟨hwb, hv⟩⟩
      | succ k =>
        have ih := slots_canon hlen st vs (h + 32) (off + (enc v).length)
          (by simp only [length_word] at hH'; rw [← Nat.add_assoc]; exact hH')
          (by rw [← Nat.add_assoc]; exact hT') k (by simp at hk; omega)
        simp only [List.getElem_cons_succ, headOff, hs, ite_false, Bool.false_eq_true]
        rw [show st + h + (32 + headOff vs k) = st + (h + 32) + headOff vs k by omega]
        exact ih

/-- A block in spec encoding at `st`: its components are where `LP` looks. -/
theorem block_canon {data : Bytes} (hlen : data.length < 2 ^ 255) {st : Nat} {vs : List Val}
    (h : At data st (encTuple vs)) :
    ∀ k (hk : k < vs.length),
      (vs[k].isStatic = true → At data (st + headOff vs k) (enc vs[k])) ∧
      (vs[k].isStatic = false → st + headOff vs k + 32 ≤ data.length ∧
        At data (st + load data (st + headOff vs k)) (enc vs[k])) := by
  unfold encTuple at h
  obtain ⟨h1, h2⟩ := At_append.mp h
  rw [encParts_fst_length] at h2
  intro k hk
  have := slots_canon hlen st vs 0 (headLen vs) (by simpa using h1) h2 k hk
  simpa using this

/-- **The spec encoding is one of the layouts.** -/
theorem canon_LP : ∀ (v : Val) (data : Bytes) (l : Nat), data.length < 2 ^ 255 →
    small v = true → At data l (enc v) → LP data l v
  | .word w, data, l, _, _, h => .word (by simpa [enc] using h)
  | .bytes b, data, l, hlen, _, h => by
    simp only [enc, encBytes] at h
    obtain ⟨h1, h2⟩ := At_append.mp h
    obtain ⟨hw, hb⟩ := At_append.mp h1
    have hbb := h2.bound
    have hbl : b.length < 2 ^ 256 := by
      simp only [List.length_append, length_word] at hbb hb
      have : (2 : Nat) ^ 255 < 2 ^ 256 := by decide
      have := hb.bound
      omega
    have hwb := hw.bound
    simp only [length_word] at hwb hb
    exact .bytes hwb (load_of_At hw hbl) hb
  | .tuple vs, data, l, hlen, hsm, h => by
    rw [enc_tuple] at h
    simp only [small] at hsm
    have hs := block_canon hlen h
    exact .tuple
      (fun i hi hst => canon_LP vs[i] data _ hlen (smallAll_get hsm i hi) ((hs i hi).1 hst))
      (fun i hi hst => ((hs i hi).2 hst).1)
      (fun i hi hst => canon_LP vs[i] data _ hlen (smallAll_get hsm i hi) ((hs i hi).2 hst).2)
  | .array vs, data, l, hlen, hsm, h => by
    rw [enc_array] at h
    obtain ⟨hw, ht⟩ := At_append.mp h
    simp only [length_word] at ht
    have hs := block_canon hlen ht
    have hwb := hw.bound
    have htb := ht.bound
    simp only [length_word] at hwb
    simp only [small, Bool.and_eq_true, decide_eq_true_eq] at hsm
    exact .array hwb (load_of_At hw hsm.1)
      (fun i hi hst => canon_LP vs[i] data _ hlen (smallAll_get hsm.2 i hi) ((hs i hi).1 hst))
      (fun i hi hst => ((hs i hi).2 hst).1)
      (fun i hi hst => canon_LP vs[i] data _ hlen (smallAll_get hsm.2 i hi) ((hs i hi).2 hst).2)
  | .call pre args, data, l, hlen, hsm, h => by
    simp only [small] at hsm
    rw [enc_call] at h
    simp only [encBytes] at h
    obtain ⟨h1, _⟩ := At_append.mp h
    obtain ⟨hw, hc⟩ := At_append.mp h1
    simp only [length_word] at hc
    have hcb := hc.bound
    have hwb := hw.bound
    simp only [length_word] at hwb
    have hcl : (pre ++ encTuple args).length < 2 ^ 256 := by
      have : (2 : Nat) ^ 255 < 2 ^ 256 := by decide
      omega
    have hclen : (pre ++ encTuple args).length < 2 ^ 255 := by omega
    have hin : At (pre ++ encTuple args) pre.length (encTuple args) := by
      simpa using (At_append.mp (At_self (pre ++ encTuple args))).2
    have hs := block_canon hclen hin
    exact .call hwb (load_of_At hw hcl) hc (by simp) (by simp)
      (fun i hi hst => canon_LP args[i] _ _ hclen (smallAll_get hsm i hi) ((hs i hi).1 hst))
      (fun i hi hst => ((hs i hi).2 hst).1)
      (fun i hi hst => canon_LP args[i] _ _ hclen (smallAll_get hsm i hi) ((hs i hi).2 hst).2)
termination_by v => sizeOf v
decreasing_by
  all_goals
    simp_wf
    have := List.sizeOf_lt_of_mem (List.getElem_mem (by assumption))
    omega

/-- **A region holding the spec encoding of `v` is read as `v`.** If `u`
    is what following offsets from `l` reads, and the bytes at `l` are the
    spec encoding of a value `v` of the same shape, then `u = v`. -/
theorem region_det {data : Bytes} (hlen : data.length < 2 ^ 255) {l : Nat} {u v : Val}
    {s : Sh} (hu : LP data l u) (hv : At data l (enc v)) (hsm : small v = true)
    (hsu : HasSh u s) (hsv : HasSh v s) : u = v :=
  hu.det (canon_LP v data l hlen hsm hv) hsu hsv

end TargetDecode
