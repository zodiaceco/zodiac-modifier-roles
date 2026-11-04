import TargetDecode.Loose

/-!
# solc's ABI decoder

`decode`: what a Solidity function's parameter decoder (ABI coder v2,
parameters in `memory`) accepts, transcribed from the Yul solc generates
(`abi_decode_tuple_*`, `abi_decode_t_bytes_memory_ptr`,
`abi_decode_available_length_t_array_*`, the `validator_revert_t_*`
cleanups):

* a tuple's head must fit (`slt(sub(dataEnd, headStart), headSize)`);
* an offset word above `2^64 - 1` reverts; the component is decoded at the
  block start plus the offset;
* `bytes` / `string` and dynamic arrays need their length word in calldata
  (`slt(add(offset, 0x1f), end)`), a length above `2^64 - 1` panics (memory
  allocation), and the content (`length` bytes, or `length` elements of
  their stride) must fit;
* words are validated for their type: `uintN` / `address` below `2^N`,
  `intN` sign-extended, `bool` 0 or 1, `bytesN` with zero low bytes.

Fixed-size arrays `T[k]` are tuples of `k` components. Positions stay far
below `2^255` (calldata is shorter), so solc's signed comparisons are
unsigned ones.

`decode_LP`: when it accepts, the decoded value is what following offsets
reads (`LP`), with the type's shape. Parameters in `calldata` are decoded
lazily, field by field, with the same arithmetic; the differential test
(`test/formal/integrity-gaps.spec.ts`, `GAP_TARGET`) compiles both kinds and
compares them with this model.
-/

namespace TargetDecode
open DecoderFaithfulness DecoderFaithfulness.Roles

/-- A Solidity ABI type. -/
inductive STy where
  | uint (bits : Nat)
  | int (bits : Nat)
  | address
  | bool
  | fixedBytes (n : Nat)
  | bytes
  | tuple (cs : List STy)
  | array (e : STy)
  | farray (e : STy) (k : Nat)
  deriving Inhabited

mutual
  def STy.sh : STy → Sh
    | .bytes => .bytes
    | .tuple cs => .tuple (STy.shs cs)
    | .array e => .array e.sh
    | .farray e k => .tuple (List.replicate k e.sh)
    | _ => .word
  def STy.shs : List STy → List Sh
    | [] => []
    | c :: cs => c.sh :: STy.shs cs
end

/-- `x` as a two's complement `int256`. -/
def toInt256 (x : Nat) : Int := if x < 2 ^ 255 then x else (x : Int) - 2 ^ 256

/-- solc's cleanup check for a word of this type. -/
def wordValid : STy → Nat → Bool
  | .uint bits, x => decide (x < 2 ^ bits)
  | .int bits, x =>
    let v := toInt256 x
    decide (-(2 ^ (bits - 1) : Int) ≤ v ∧ v < 2 ^ (bits - 1))
  | .address, x => decide (x < 2 ^ 160)
  | .bool, x => decide (x < 2)
  | .fixedBytes n, x => decide (x % 2 ^ (8 * (32 - n)) = 0)
  | _, _ => false

def STy.isWord : STy → Bool
  | .uint _ | .int _ | .address | .bool | .fixedBytes _ => true
  | _ => false

mutual
  def STy.isStatic : STy → Bool
    | .tuple cs => STy.allStatic cs
    | .farray e k => k == 0 || e.isStatic
    | t => t.isWord
  def STy.allStatic : List STy → Bool
    | [] => true
    | c :: cs => c.isStatic && STy.allStatic cs
end

/-- The head size of a component: its encoding if static, else one word. -/
def STy.headSize (t : STy) : Nat := if t.isStatic then t.sh.size else 32

def U64 : Nat := 2 ^ 64 - 1

mutual
  /-- Decode a value of type `t` at `pos` (its head position if static, its
      tail position if dynamic). -/
  def decode (data : Bytes) : Nat → STy → Nat → Option Val
    | 0, _, _ => none
    | fuel + 1, t, pos =>
      if t.isWord then
        if pos + 32 > data.length then none
        else
          let w := (data.drop pos).take 32
          if wordValid t (wordVal w) then some (.word w) else none
      else match t with
      | .bytes =>
        if ¬ pos + 31 < data.length then none
        else
          let len := load data pos
          if len > U64 then none
          else if pos + 32 + len > data.length then none
          else some (.bytes ((data.drop (pos + 32)).take len))
      | .tuple cs => (decodeBlock data fuel cs pos 0).map .tuple
      | .farray e k => (decodeBlock data fuel (List.replicate k e) pos 0).map .tuple
      | .array e =>
        if ¬ pos + 31 < data.length then none
        else
          let n := load data pos
          if n > U64 then none
          else if pos + 32 + n * e.headSize > data.length then none
          else (decodeBlock data fuel (List.replicate n e) (pos + 32) 0).map .array
      | _ => none

  /-- The components `ts` of the block at `start`, from head offset `h`. -/
  def decodeBlock (data : Bytes) : Nat → List STy → Nat → Nat → Option (List Val)
    | _, [], _, _ => some []
    | fuel, t :: ts, start, h =>
      if start + h + t.headSize > data.length then none
      else
        let v? := if t.isStatic then decode data fuel t (start + h)
          else
            let off := load data (start + h)
            if off > U64 then none else decode data fuel t (start + off)
        match v? with
        | none => none
        | some v => (decodeBlock data fuel ts start (h + t.headSize)).map (v :: ·)
end

mutual
  /-- Nesting depth: the fuel `decode` needs. -/
  def STy.depth : STy → Nat
    | .tuple cs => STy.depthAll cs + 1
    | .array e | .farray e _ => e.depth + 1
    | _ => 1
  def STy.depthAll : List STy → Nat
    | [] => 0
    | c :: cs => max c.depth (STy.depthAll cs)
end

/-- The calldata of a function with parameters `ts` after `n` leading bytes. -/
def decodeCall (data : Bytes) (n : Nat) (ts : List STy) : Option (List Val) :=
  if data.length < n then none else decodeBlock data (STy.depthAll ts + 1) ts n 0

/-! ## Soundness: what solc accepts is loosely placed -/

theorem allStatic_replicate (k : Nat) (c : Sh) :
    Sh.allStatic (List.replicate k c) = (k == 0 || c.isStatic) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [List.replicate_succ, Sh.allStatic, ih]
    cases c.isStatic <;> simp

mutual
  theorem STy.isStatic_sh : ∀ t : STy, t.isStatic = t.sh.isStatic
    | .uint _ | .int _ | .address | .bool | .fixedBytes _ => rfl
    | .bytes => rfl
    | .array _ => rfl
    | .tuple cs => by
      simp only [STy.isStatic, STy.sh, Sh.isStatic]
      exact STy.allStatic_shs cs
    | .farray e k => by
      simp only [STy.isStatic, STy.sh, Sh.isStatic, allStatic_replicate, STy.isStatic_sh e]
  theorem STy.allStatic_shs : ∀ cs : List STy, STy.allStatic cs = Sh.allStatic (STy.shs cs)
    | [] => rfl
    | c :: cs => by
      simp only [STy.allStatic, STy.shs, Sh.allStatic, STy.isStatic_sh c, STy.allStatic_shs cs]
end

theorem shs_length : ∀ cs : List STy, (STy.shs cs).length = cs.length
  | [] => rfl
  | _ :: cs => by simp [STy.shs, shs_length cs]

theorem shs_get : ∀ (cs : List STy) (i : Nat) (h : i < cs.length) (h' : i < (STy.shs cs).length),
    (STy.shs cs)[i] = cs[i].sh
  | c :: cs, 0, _, _ => rfl
  | c :: cs, i + 1, h, h' => by
    simp only [STy.shs, List.getElem_cons_succ]
    exact shs_get cs i (by simp at h; omega) _

/-- What `decodeBlock` returns: one value per type, each of its shape and
    found in its slot. -/
def BlockOK (data : Bytes) (ts : List STy) (start h : Nat) (vs : List Val) : Prop :=
  vs.length = ts.length ∧ ∀ i (hi : i < vs.length) (hi' : i < ts.length),
    HasSh vs[i] ts[i].sh ∧
    (vs[i].isStatic = true → LP data (start + h + headOff vs i) vs[i]) ∧
    (vs[i].isStatic = false → start + h + headOff vs i + 32 ≤ data.length ∧
      LP data (start + load data (start + h + headOff vs i)) vs[i])

theorem decode_sound (data : Bytes) : ∀ fuel,
    (∀ t pos u, decode data fuel t pos = some u → LP data pos u ∧ HasSh u t.sh) ∧
    (∀ ts start h vs, decodeBlock data fuel ts start h = some vs → BlockOK data ts start h vs) := by
  intro fuel
  induction fuel with
  | zero =>
    have hd : ∀ t pos u, decode data 0 t pos = some u → LP data pos u ∧ HasSh u t.sh := by
      intro t pos u h; simp [decode] at h
    refine ⟨hd, ?_⟩
    intro ts
    induction ts with
    | nil =>
      intro start h vs hb
      simp only [decodeBlock, Option.some.injEq] at hb
      subst hb; exact ⟨rfl, fun i hi => by simp at hi⟩
    | cons t ts _ =>
      intro start h vs hb
      simp only [decodeBlock] at hb
      split at hb
      · simp at hb
      · split at hb
        · simp at hb
        · rename_i v hv
          exfalso
          split at hv
          · exact absurd hv (by simp [decode])
          · split at hv
            · simp at hv
            · exact absurd hv (by simp [decode])
  | succ f ih =>
    have hword : ∀ t pos u, t.isWord = true → decode data (f + 1) t pos = some u →
        LP data pos u ∧ HasSh u t.sh := by
      intro t pos u hw h
      unfold decode at h
      rw [if_pos hw] at h
      dsimp only at h
      split at h
      · simp at h
      · split at h
        · simp only [Option.some.injEq] at h
          subst h
          have hl : ((data.drop pos).take 32).length = 32 := by simp; omega
          have hsh : t.sh = .word := by
            cases t <;> simp_all [STy.isWord, STy.sh]
          rw [hsh]
          exact ⟨.word ⟨by rw [hl], by rw [hl]; omega⟩, .word hl⟩
        · simp at h
    have hd : ∀ t pos u, decode data (f + 1) t pos = some u → LP data pos u ∧ HasSh u t.sh := by
      intro t pos u h
      cases t with
      | uint _ => exact hword _ _ _ rfl h
      | int _ => exact hword _ _ _ rfl h
      | address => exact hword _ _ _ rfl h
      | bool => exact hword _ _ _ rfl h
      | fixedBytes _ => exact hword _ _ _ rfl h
      | bytes =>
        unfold decode at h
        simp only [STy.isWord, Bool.false_eq_true, ite_false] at h
        try dsimp only at h
        split at h
        · simp at h
        · split at h
          · simp at h
          · split at h
            · simp at h
            · simp only [Option.some.injEq] at h
              subst h
              have hl : ((data.drop (pos + 32)).take (load data pos)).length = load data pos := by
                simp; omega
              exact ⟨.bytes (by omega) hl.symm ⟨by rw [hl], by rw [hl]; omega⟩, .bytes⟩
      | tuple cs =>
        unfold decode at h
        simp only [STy.isWord, Bool.false_eq_true, ite_false] at h
        obtain ⟨vs, hb, rfl⟩ := Option.map_eq_some_iff.mp h
        obtain ⟨hlen, hok⟩ := ih.2 cs pos 0 vs hb
        refine ⟨.tuple (fun i hi hs => by simpa using (hok i hi (by omega)).2.1 hs)
          (fun i hi hs => by simpa using ((hok i hi (by omega)).2.2 hs).1)
          (fun i hi hs => by simpa using ((hok i hi (by omega)).2.2 hs).2), ?_⟩
        simp only [STy.sh]
        exact .tuple (by rw [shs_length]; exact hlen) (fun i hi hi' => by
          rw [shs_get cs i (by omega) hi']; exact (hok i hi (by omega)).1)
      | farray e k =>
        unfold decode at h
        simp only [STy.isWord, Bool.false_eq_true, ite_false] at h
        obtain ⟨vs, hb, rfl⟩ := Option.map_eq_some_iff.mp h
        obtain ⟨hlen, hok⟩ := ih.2 _ pos 0 vs hb
        simp only [List.length_replicate] at hlen
        refine ⟨.tuple (fun i hi hs => by simpa using (hok i hi (by simp; omega)).2.1 hs)
          (fun i hi hs => by simpa using ((hok i hi (by simp; omega)).2.2 hs).1)
          (fun i hi hs => by simpa using ((hok i hi (by simp; omega)).2.2 hs).2), ?_⟩
        simp only [STy.sh]
        exact .tuple (by simp [hlen]) (fun i hi hi' => by
          have := (hok i hi (by simp; omega)).1
          simpa using this)
      | array e =>
        unfold decode at h
        simp only [STy.isWord, Bool.false_eq_true, ite_false] at h
        try dsimp only at h
        split at h
        · simp at h
        · split at h
          · simp at h
          · split at h
            · simp at h
            · obtain ⟨vs, hb, rfl⟩ := Option.map_eq_some_iff.mp h
              obtain ⟨hlen, hok⟩ := ih.2 _ (pos + 32) 0 vs hb
              simp only [List.length_replicate] at hlen
              refine ⟨.array (by omega) hlen.symm
                (fun i hi hs => by simpa using (hok i hi (by simp; omega)).2.1 hs)
                (fun i hi hs => by simpa using ((hok i hi (by simp; omega)).2.2 hs).1)
                (fun i hi hs => by simpa using ((hok i hi (by simp; omega)).2.2 hs).2), ?_⟩
              simp only [STy.sh]
              exact .array (fun i hi => by
                have := (hok i hi (by simp; omega)).1
                simpa using this)
    refine ⟨hd, ?_⟩
    intro ts
    induction ts with
    | nil =>
      intro start h vs hb
      simp only [decodeBlock, Option.some.injEq] at hb
      subst hb; exact ⟨rfl, fun i hi => by simp at hi⟩
    | cons t ts ihts =>
      intro start h vs hb
      simp only [decodeBlock] at hb
      split at hb
      · simp at hb
      · rename_i hfit
        split at hb
        · simp at hb
        · rename_i v hv
          obtain ⟨vs', hb', rfl⟩ := Option.map_eq_some_iff.mp hb
          obtain ⟨hlen', hok'⟩ := ihts start (h + t.headSize) vs' hb'
          -- the head value
          have hvt : (v.isStatic = true → LP data (start + h) v) ∧
              (v.isStatic = false → start + h + 32 ≤ data.length ∧
                LP data (start + load data (start + h)) v) ∧ HasSh v t.sh := by
            by_cases hst : t.isStatic
            · rw [if_pos hst] at hv
              obtain ⟨hl, hs⟩ := hd t _ v hv
              refine ⟨fun _ => hl, fun hv' => ?_, hs⟩
              rw [hs.isStatic, ← STy.isStatic_sh, hst] at hv'; cases hv'
            · rw [if_neg hst] at hv
              split at hv
              · simp at hv
              · obtain ⟨hl, hs⟩ := hd t _ v hv
                have hvs : v.isStatic = false := by
                  rw [hs.isStatic, ← STy.isStatic_sh]; simpa using hst
                refine ⟨fun h' => (by rw [hvs] at h'; cases h'), fun _ => ⟨?_, hl⟩, hs⟩
                simp only [STy.headSize, hst] at hfit
                simp at hfit; omega
          have hhs : (if v.isStatic then (enc v).length else 32) = t.headSize := by
            unfold STy.headSize
            rw [hvt.2.2.isStatic, ← STy.isStatic_sh]
            split
            · rename_i hs; rw [hvt.2.2.size (by rw [hvt.2.2.isStatic, ← STy.isStatic_sh]; exact hs)]
            · rfl
          refine ⟨by simp [hlen'], fun i hi hi' => ?_⟩
          cases i with
          | zero =>
            simp only [List.getElem_cons_zero, headOff, Nat.add_zero]
            exact ⟨hvt.2.2, hvt.1, hvt.2.1⟩
          | succ i =>
            have hk := hok' i (by simp at hi; omega) (by simp at hi'; omega)
            simp only [List.getElem_cons_succ, headOff]
            rw [hhs, show start + h + (t.headSize + headOff vs' i) =
              start + (h + t.headSize) + headOff vs' i by omega]
            exact hk

/-- **solc's decoder accepts only loosely placed values.** -/
theorem decodeCall_LP {data : Bytes} {n : Nat} {ts : List STy} {args : List Val}
    (h : decodeCall data n ts = some args) :
    BlockOK data ts n 0 args := by
  unfold decodeCall at h
  split at h
  · simp at h
  · exact (decode_sound data _).2 ts n 0 args h

end TargetDecode
