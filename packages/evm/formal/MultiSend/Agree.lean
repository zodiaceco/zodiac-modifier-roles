import MultiSend.Basic

/-!
# Roles checks exactly what MultiSend executes

* `exec_parse`: on a batch in the format (`parse`), MultiSend's loop
  executes exactly its transactions, whatever memory follows the batch.
* `unwrap_parse`: when `MultiSendUnwrapper.unwrap` succeeds, the calldata
  is `multiSend(bytes transactions)` with the standard head, and the
  entries it returns, with Roles' calldata slices, are exactly
  `parse transactions`.
* `unwrap_exec`: together, the transactions Roles checks are the
  transactions MultiSend executes, in order, with the same operation,
  target, value and calldata.
-/

namespace MultiSend
open DecoderFaithfulness DecoderFaithfulness.Roles

/-! ## Bytes -/

theorem foldl_acc (b : Bytes) : ∀ acc : Nat,
    b.foldl (fun acc b => acc * 256 + b.val) acc = acc * 256 ^ b.length + wordVal b := by
  induction b with
  | nil => intro acc; simp [wordVal]
  | cons x b ih =>
    intro acc
    have hx : wordVal (x :: b) = x.val * 256 ^ b.length + wordVal b := by
      show List.foldl _ (0 * 256 + x.val) b = _
      rw [ih]; simp
    simp only [List.foldl_cons, List.length_cons]
    rw [ih, hx, Nat.pow_succ, Nat.add_mul, Nat.add_assoc]
    congr 1
    rw [Nat.mul_assoc, Nat.mul_comm 256]

theorem wordVal_append (a b : Bytes) :
    wordVal (a ++ b) = wordVal a * 256 ^ b.length + wordVal b := by
  show List.foldl _ 0 (a ++ b) = _
  rw [List.foldl_append]
  exact foldl_acc b _

theorem wordVal_lt (b : Bytes) : wordVal b < 256 ^ b.length := by
  induction b with
  | nil => simp [wordVal]
  | cons x b ih =>
    have hx : wordVal (x :: b) = x.val * 256 ^ b.length + wordVal b := by
      show List.foldl _ (0 * 256 + x.val) b = _
      rw [foldl_acc]; simp
    rw [hx, List.length_cons, Nat.pow_succ]
    have h1 : x.val * 256 ^ b.length ≤ 255 * 256 ^ b.length :=
      Nat.mul_le_mul_right _ (by have := x.isLt; omega)
    have h2 : 255 * 256 ^ b.length + 256 ^ b.length = 256 ^ b.length * 256 := by
      rw [Nat.mul_comm (256 ^ b.length) 256]; omega
    omega

theorem wordVal_div (a b : Bytes) : wordVal (a ++ b) / 256 ^ b.length = wordVal a := by
  rw [wordVal_append, Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.pow_pos (by decide)),
    Nat.div_eq_of_lt (wordVal_lt b), Nat.zero_add]

/-- Reading `n` bytes at `x + k`, zero-padded, inside a block `c` that
    starts at `x`. -/
theorem read_at {mem c junk : Bytes} {x : Nat} (hm : mem.drop x = c ++ junk) (k n : Nat)
    (hk : k + n ≤ c.length) :
    (mem.drop (x + k) ++ zeros n).take n = (c.drop k).take n := by
  rw [← List.drop_drop, hm, List.drop_append_of_le_length (by omega), List.append_assoc,
    List.take_append_of_le_length (by simp; omega)]

theorem mload_at {mem c junk : Bytes} {x : Nat} (hm : mem.drop x = c ++ junk) (k : Nat)
    (hk : k + 32 ≤ c.length) : mload mem (x + k) = wordVal ((c.drop k).take 32) := by
  unfold mload; rw [read_at hm k 32 hk]

theorem load_at {data c junk : Bytes} {x : Nat} (hm : data.drop x = c ++ junk) (k : Nat)
    (hk : k + 32 ≤ c.length) : load data (x + k) = wordVal ((c.drop k).take 32) := by
  unfold load; rw [read_at hm k 32 hk]

/-- The first byte of a word. -/
theorem first_byte (b : Byte) (t : Bytes) (ht : 31 ≤ t.length) :
    wordVal (((b :: t).drop 0).take 32) / 2 ^ 248 = b.val := by
  have : ((b :: t).drop 0).take 32 = [b] ++ t.take 31 := by simp
  have hl : (t.take 31).length = 31 := by simp; omega
  have h2 : (2 : Nat) ^ 248 = 256 ^ (t.take 31).length := by rw [hl]
  rw [this, h2, wordVal_div]
  simp [wordVal]

/-- The 20 address bytes at the front of a word. -/
theorem addr_bytes (c : Bytes) (k : Nat) (hk : k + 32 ≤ c.length) :
    wordVal ((c.drop k).take 32) / 2 ^ 96 = wordVal ((c.drop k).take 20) := by
  have : (c.drop k).take 32 = (c.drop k).take 20 ++ ((c.drop k).drop 20).take 12 := by
    rw [← List.take_add]
  have hl : (((c.drop k).drop 20).take 12).length = 12 := by simp; omega
  have h2 : (2 : Nat) ^ 96 = 256 ^ (((c.drop k).drop 20).take 12).length := by rw [hl]
  rw [this, h2, wordVal_div]

/-! ## MultiSend executes the batch -/

theorem exec_parse_gen (mem junk : Bytes) (L : Nat) (hL : L + 32 < 2 ^ 256) :
    ∀ n (c : Bytes) (p : Nat) (es : List Entry), c.length = n → mem.drop (32 + p) = c ++ junk →
      p + c.length = L → parse c = some es → ∀ f, es.length < f →
      execLoop mem L f (32 + p) = some es := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro c p es hn hm hp hpar f hf
    obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
    match c, hm, hn, hp, hpar with
    | [], _, _, hp, hpar =>
      simp [parse] at hpar; subst hpar
      simp only [execLoop]
      rw [if_pos (by simp at hp; omega)]
    | b :: t, hm, hn, hp, hpar =>
      rw [parse] at hpar
      simp only at hpar
      split at hpar
      · simp at hpar
      · rename_i h85
        split at hpar
        · simp at hpar
        · rename_i hop
          split at hpar
          · simp at hpar
          · rename_i hlen
            simp only [List.length_cons] at h85 hlen hp hn
            generalize hlen_def : wordVal (((b :: t).drop 53).take 32) = len at hpar hlen h85
            cases hr : parse ((b :: t).drop (85 + len)) with
            | none => rw [hr] at hpar; simp at hpar
            | some es' =>
              rw [hr] at hpar
              simp at hpar
              subst hpar
              simp only [List.length_cons] at hf
              simp only [execLoop]
              rw [if_neg (by omega)]
              have hop' : mload mem (32 + p) / 2 ^ 248 = b.val := by
                rw [show 32 + p = 32 + p + 0 by rfl, mload_at hm 0 (by simp; omega)]
                exact first_byte b t (by omega)
              have hto : mload mem (32 + p + 1) / 2 ^ 96 = wordVal (((b :: t).drop 1).take 20) := by
                rw [mload_at hm 1 (by simp; omega)]
                exact addr_bytes _ 1 (by simp; omega)
              have hval : mload mem (32 + p + 21) = wordVal (((b :: t).drop 21).take 32) :=
                mload_at hm 21 (by simp; omega)
              have hdl : mload mem (32 + p + 53) = len := by
                rw [← hlen_def]; exact mload_at hm 53 (by simp; omega)
              have hd : (mem.drop (32 + p + 85) ++ zeros len).take len = ((b :: t).drop 85).take len :=
                read_at hm 85 len (by simp; omega)
              rw [hop', hto, hval, hdl, hd, if_pos (by omega)]
              have hnext : (32 + p + (85 + len)) % 2 ^ 256 = 32 + (p + 85 + len) := by
                rw [Nat.mod_eq_of_lt (by omega)]; omega
              rw [hnext]
              have hm' : mem.drop (32 + (p + 85 + len)) = (b :: t).drop (85 + len) ++ junk := by
                rw [show 32 + (p + 85 + len) = 32 + p + (85 + len) by omega, ← List.drop_drop, hm,
                  List.drop_append_of_le_length (by simp; omega)]
              rw [ih ((b :: t).drop (85 + len)).length (by simp; omega) _ (p + 85 + len) es' rfl hm'
                (by simp; omega) hr f (by omega)]
              rfl

/-- **MultiSend executes exactly the batch**: on bytes in the format, with
    any memory after them, the loop calls each transaction in order. -/
theorem exec_parse (tx junk : Bytes) (es : List Entry) (h : parse tx = some es)
    (hL : tx.length + 32 < 2 ^ 256) :
    let mem := word tx.length ++ tx ++ junk
    execLoop mem (mload mem 0) (es.length + 1) 32 = some es := by
  intro mem
  have hm : mem.drop (32 + 0) = tx ++ junk := by simp [mem]
  have hlen : mload mem 0 = tx.length := by
    unfold mload
    simp only [mem, List.drop_zero, List.append_assoc]
    rw [List.take_append_of_le_length (by simp), List.take_of_length_le (by simp),
      wordVal_word _ (by omega)]
  rw [hlen]
  exact exec_parse_gen mem junk tx.length hL _ tx 0 es rfl hm (by simp) h _ (by omega)

/-! ## The unwrapper reads the batch -/

theorem validate_parse (data : Bytes) (L : Nat) (hdl : 68 + L ≤ data.length) :
    ∀ f p k n, p ≤ L → validateLoop data (68 + L) f (68 + p) k = some n →
      n ≠ 0 ∧ ∃ es us, parse ((data.drop (68 + p)).take (L - p)) = some es ∧
        n = k + es.length ∧ unwrapLoop data es.length (68 + p) = some us ∧
        us.map (Unwrapped.view data) = es
  | 0, _, _, _, _, h => by simp [validateLoop] at h
  | f + 1, p, k, n, hpL, h => by
    simp only [validateLoop] at h
    by_cases hlt : 68 + p < 68 + L
    · rw [if_pos hlt] at h
      -- the block from `68 + p`
      generalize hc : (data.drop (68 + p)).take (L - p) = c
      have hcl : c.length = L - p := by rw [← hc]; simp; omega
      have hm : data.drop (68 + p) = c ++ data.drop (68 + L) := by
        rw [← hc]
        have := List.take_append_drop (L - p) (data.drop (68 + p))
        rw [List.drop_drop, show 68 + p + (L - p) = 68 + L by omega] at this
        exact this.symm
      obtain ⟨b, t, hbt⟩ : ∃ b t, c = b :: t := by
        cases hcc : c with
        | nil => rw [hcc] at hcl; simp at hcl; omega
        | cons b t => exact ⟨b, t, rfl⟩
      have hrd1 : rd1 data (68 + p) = some b.val := by
        unfold rd1
        rw [if_pos (by omega), show 68 + p = 68 + p + 0 by rfl,
          read_at hm 0 1 (by rw [hbt]; simp)]
        simp [hbt, wordVal]
      rw [hrd1] at h
      simp only at h
      split at h
      · simp at h
      · rename_i hop
        cases hrd32 : rd32 data (68 + p + 53) with
        | none => rw [hrd32] at h; simp at h
        | some len =>
        rw [hrd32] at h
        simp only at h
        split at h
        · simp at h
        · rename_i hfit
          have hlen : load data (68 + p + 53) = len := by
            unfold rd32 at hrd32; split at hrd32 <;> simp_all
          have hlen' : len = wordVal ((c.drop 53).take 32) := by
            rw [← hlen]; exact load_at hm 53 (by omega)
          obtain ⟨hn0, es', us', hpar', hn', hun', hview'⟩ :=
            validate_parse data L hdl f (p + 85 + len) (k + 1) n (by omega)
              (by rw [show 68 + (p + 85 + len) = 68 + p + 85 + len by omega]; exact h)
          refine ⟨hn0, ?_⟩
          -- the entry at `68 + p`
          have hto : rd20 data (68 + p + 1) = some (wordVal ((c.drop 1).take 20)) := by
            unfold rd20; rw [if_pos (by omega), read_at hm 1 20 (by omega)]
          have hval : rd32 data (68 + p + 21) = some (wordVal ((c.drop 21).take 32)) := by
            unfold rd32; rw [if_pos (by omega), load_at hm 21 (by omega)]
          have hd : (data.drop (68 + p + 85)).take len = (c.drop 85).take len := by
            rw [← List.drop_drop, hm, List.drop_append_of_le_length (by omega),
              List.take_append_of_le_length (by simp; omega)]
          have hrest : c.drop (85 + len) = (data.drop (68 + (p + 85 + len))).take (L - (p + 85 + len)) := by
            rw [← hc, List.drop_take, List.drop_drop,
              show 68 + p + (85 + len) = 68 + (p + 85 + len) by omega,
              show L - p - (85 + len) = L - (p + 85 + len) by omega]
          refine ⟨⟨b.val, wordVal ((c.drop 1).take 20), wordVal ((c.drop 21).take 32),
            (c.drop 85).take len⟩ :: es',
            ⟨b.val, wordVal ((c.drop 1).take 20), wordVal ((c.drop 21).take 32), 68 + p + 85, len⟩ :: us',
            ?_, by simp; omega, ?_, ?_⟩
          · rw [hbt, parse]
            simp only
            rw [dif_neg (by rw [← hbt]; omega), if_neg (by omega), dif_neg (by rw [← hbt, ← hlen']; omega)]
            rw [← hbt, ← hlen', hrest, hpar']
            rfl
          · simp only [List.length_cons, unwrapLoop, hrd1, hto, hval, hrd32]
            rw [if_neg (by omega), show 68 + p + 85 + len = 68 + (p + 85 + len) by omega, hun']
            rfl
          · simp only [List.map_cons, hview']
            simp only [Unwrapped.view, hd]
    · rw [if_neg hlt] at h
      split at h
      · simp at h
      · rename_i hk
        simp at h
        subst h
        refine ⟨hk, [], [], ?_, by simp, by simp [unwrapLoop], rfl⟩
        rw [show L - p = 0 by omega]
        simp [parse]

/-- **What the unwrapper accepts**: `multiSend(bytes)` with the standard
    head (offset `0x20`, length `L`, the calldata exactly `4 + ceil32(64 +
    L)` bytes), a non-empty batch, and the entries are `parse` of the
    batch, with Roles' calldata slices. -/
theorem unwrap_parse (data : Bytes) (value op : Nat) (us : List Unwrapped)
    (h : unwrap data value op = some us) :
    value = 0 ∧ op = 1 ∧ (data ++ zeros 4).take 4 = selMultiSend ∧ load data 4 = 32 ∧
      data.length = 4 + ceil32 (64 + load data 36) ∧ us ≠ [] ∧
      parse ((data.drop 68).take (load data 36)) = some (us.map (Unwrapped.view data)) := by
  unfold unwrap at h
  split at h
  · simp at h
  · rename_i hvo
    simp only [not_or, Decidable.not_not] at hvo
    obtain ⟨rfl, rfl⟩ := hvo
    split at h
    · simp at h
    · rename_i hhead
      unfold validateHeader at hhead
      split at hhead
      · simp at hhead
      · rename_i hsel
        split at hhead
        · rename_i o len h4 h36
          split at hhead
          · simp at hhead
          · rename_i ho
            split at hhead
            · simp at hhead
            · rename_i hsize
              simp only [Decidable.not_not] at hsel ho hsize
              unfold rd32 at h4 h36
              split at h4 <;> simp at h4
              split at h36 <;> simp at h36
              subst h4; subst h36
              have hdl : 68 + load data 36 ≤ data.length := by
                have := ceil32_ge (32 + 32 + load data 36); omega
              split at h
              · simp at h
              · rename_i n hv
                obtain ⟨hn0, es, us', hpar, hn, hun, hview⟩ :=
                  validate_parse data (load data 36) hdl _ 0 0 n (by omega) hv
                simp only [Nat.zero_add] at hn
                subst hn
                rw [hun] at h
                cases h
                refine ⟨rfl, rfl, hsel, ho, by rw [← hsize], ?_, ?_⟩
                · intro hnil; subst hnil; simp_all
                · rw [hview]; simpa using hpar
        · simp at hhead

/-- **Roles checks exactly the transactions MultiSend executes.** When
    `MultiSendUnwrapper.unwrap` accepts the calldata of a delegatecall to
    `MultiSend`, the Solidity ABI decoder hands `multiSend` the bytes
    `data[68 : 68 + L]` (offset `0x20`, length `L`), and MultiSend's loop
    executes, in order, exactly the transactions Roles checks: the
    unwrapped entries with their calldata slices. -/
theorem unwrap_exec (data junk : Bytes) (value op : Nat) (us : List Unwrapped)
    (h : unwrap data value op = some us) (hb : data.length < 2 ^ 256) :
    let tx := (data.drop 68).take (load data 36)
    let mem := word tx.length ++ tx ++ junk
    execLoop mem (mload mem 0) (us.length + 1) 32 = some (us.map (Unwrapped.view data)) := by
  intro tx mem
  obtain ⟨_, _, _, _, hsize, _, hpar⟩ := unwrap_parse data value op us h
  have hc := ceil32_ge (64 + load data 36)
  have htx : tx.length = load data 36 := by simp [tx]; omega
  have := exec_parse tx junk _ hpar (by omega)
  rw [List.length_map] at this
  exact this

end MultiSend
