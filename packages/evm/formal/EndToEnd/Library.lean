import EndToEnd.Pins
import EndToEnd.Hashes

/-!
# What `SignTypedMessageLib` reads, against what Roles checked

Roles checks the calldata with its own reader (`AbiLocation`); the library
reads the same calldata with Solidity's ABI decoder (`signMessage(bytes)`,
`personalSign(bytes)`) or by hand (the `signTypedMessage` fallback). A pin
only restricts what gets signed if both read the same bytes, on any
calldata, also malformed. This file shows they do:

* `route_bytes`: when Roles passes a call whose `bytes` argument is pinned,
  and Solidity's decoder accepts the calldata, the message the library signs
  is one of the pinned messages.
* `route_types`: when Roles passes a call whose `types` argument is pinned
  (as an array of 96-byte elements), the type nodes the library hashes are
  the bytes of one of the pinned values.
-/

namespace EndToEnd
open DecoderFaithfulness DecoderFaithfulness.Roles Evaluate

/-! ## `bytes` arguments -/

/-- Solidity's ABI decoder (coder v2) for `f(bytes calldata message)`:
    `abi_decode_tuple_t_bytes_calldata_ptr` and
    `abi_decode_t_bytes_calldata_ptr`. `none` is a revert. -/
def solDecodeBytes (data : Bytes) : Option Bytes :=
  if data.length < 4 + 32 then none else
  let off := load data 4
  if off > 2 ^ 64 - 1 then none else
  let p := 4 + off
  if ¬ (p + 31 < data.length) then none else
  let len := load data p
  if len > 2 ^ 64 - 1 then none else
  if p + 32 + len > data.length then none else
  some ((data.drop (p + 32)).take len)

/-- The message a stored `EqualTo` compValue on `bytes` pins. The packer
    drops the offset word of `abi.encode(message)`, so the stored value is
    the length word followed by the (padded) content. -/
def pinnedBytes (cv : Bytes) : Bytes := (cv.drop 32).take (wordVal (key cv))

/-- The pin a lint should accept for a `bytes` argument: an `EqualTo`
    read as `Dynamic` (from its offset, size from its length word). -/
def leafBytes (c : Condition) : Bool :=
  c.encoding = .Dynamic && c.inlineSize = 0

theorem load_take {data : Bytes} {L : Nat} (h : L + 32 ≤ data.length) :
    load data L = wordVal ((data.drop L).take 32) := by
  unfold load
  congr 1
  rw [List.take_append_of_le_length (by simp; omega)]

theorem take_take_le {l : Bytes} {a b : Nat} (h : a ≤ b) : (l.take b).take a = l.take a := by
  rw [List.take_take, Nat.min_eq_left h]

/-- The operand `_read` resolves for a `Dynamic` value read from its
    offset: its region, the length word and the padded content. -/
theorem operand_dyn {data : Calldata} {L : Slice} {c : Condition} (he : c.encoding = .Dynamic)
    (hz : c.inlineSize = 0) {op : Slice} (h : operand data L 0 c = some op) :
    32 ≤ L.length ∧ load data L.offset ≤ L.length - 32 ∧
      op = ⟨L.offset, 32 + ((load data L.offset + 31) &&& notU31)⟩ ∧
      ((load data L.offset + 31) &&& notU31) ≤ L.length - 32 := by
  unfold operand sliceRegion at h
  simp only [Nat.lt_irrefl, ite_false] at h
  cases hr : region data L c with
  | none => rw [hr] at h; cases h
  | some k =>
    rw [hr] at h
    simp only [Option.map_some, Option.some.injEq] at h
    obtain ⟨h32, hle, rfl, hpad⟩ := region_bytes_some hz (.inl he) hr
    exact ⟨h32, hle, h.symm, hpad⟩

/-- **The library signs a pinned message.** When Roles passes `data` with
    the `bytes` argument pinned (`pinsArg leafBytes 0`), and Solidity's
    decoder accepts `data` (else the call reverts and nothing is signed),
    the decoded message is the message of a pinned compValue. -/
theorem route_bytes {env : Env} {data : Calldata} {n F f : Nat} {root : Condition}
    {cons : List Consumption} {sl : Slots} {m : Bytes}
    (hpin : pinsArg leafBytes 0 f root = true)
    (hrun : (evalC env data n F ⟨0, data.length⟩ root.inlineSize root cons sl).status = sOk)
    (hdec : solDecodeBytes data = some m) :
    ∃ e, PinUnder 0 root e ∧ pinnedLeaf leafBytes e = true ∧ m = pinnedBytes e.compValue := by
  obtain ⟨e, L, hu, hl, hoff, hwithin, hno, heq⟩ :=
    pinsArg_sound leafBytes 0 F f root cons sl hpin hrun
  refine ⟨e, hu, hl, ?_⟩
  simp only [Nat.mul_zero, Nat.add_zero] at hoff
  have hleaf := hl
  unfold pinnedLeaf leafBytes at hleaf
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hleaf
  obtain ⟨_, henc, hsz⟩ := hleaf
  have hne : e.encoding ≠ .None := by rw [henc]; decide
  -- Solidity's reading
  unfold solDecodeBytes at hdec
  simp only at hdec
  split at hdec; · simp at hdec
  split at hdec; · simp at hdec
  split at hdec; · simp at hdec
  split at hdec; · simp at hdec
  split at hdec; · simp at hdec
  rename_i _ _ _ hlen hfit
  simp only [Option.some.injEq] at hdec
  subst hdec
  rw [show 4 + load data 4 = L.offset by omega] at hlen hfit ⊢
  -- Roles' reading: the region at the same place
  rw [hsz] at hno heq
  cases hop : operand data L 0 e with
  | none => exfalso; apply hno; unfold input; rw [ite_eq_right hne, hop]
  | some op =>
    obtain ⟨h32, hle, rfl, hpad⟩ := operand_dyn henc hsz hop
    unfold input inputLength at heq
    rw [ite_eq_right hne, ite_eq_right hne, hop] at heq
    simp only [Slice.bytes] at heq
    generalize hlv : load data L.offset = len at hlen hfit hle hpad heq ⊢
    have hround : (len + 31) &&& notU31 = ceil32 len := roundUp_eq len (by omega)
    rw [hround] at heq hpad
    have hin : L.offset + 32 ≤ data.length := by omega
    unfold Evaluate.compare at heq
    simp only at heq
    by_cases hz : ceil32 len = 0
    · have hl0 : len = 0 := by have := ceil32_ge len; omega
      subst hl0
      rw [hz] at heq
      simp only [Nat.add_zero, Nat.lt_irrefl, ite_false, inputB] at heq
      split at heq
      · rename_i hc
        obtain ⟨_, hw⟩ := hc
        simp only [B32.w.injEq] at hw
        rw [← load_take hin, hlv] at hw
        simp [pinnedBytes, ← hw]
      · simp [sParameterNotAllowed, sOk] at heq
    · have hgt : 32 + ceil32 len > 32 := by omega
      simp only [hgt, ite_true, inputB] at heq
      split at heq
      · rename_i hc
        obtain ⟨_, hw⟩ := hc
        simp only [B32.h.injEq] at hw
        -- the stored value is exactly the bytes Roles hashed
        rw [← hw]
        have hk : key ((data.drop L.offset).take (32 + ceil32 len)) = (data.drop L.offset).take 32 := by
          unfold key
          rw [List.take_append_of_le_length (by simp; omega), take_take_le (by omega)]
        unfold pinnedBytes
        rw [hk, ← load_take hin, hlv, List.drop_take, List.drop_drop,
          show 32 + ceil32 len - 32 = ceil32 len by omega, take_take_le (ceil32_ge len)]
      · simp [sParameterNotAllowed, sOk] at heq


/-! ## The `types` argument -/

/-- The pin a lint should accept for `types`: an `EqualTo` read
    as an array of 96-byte elements (`(uint256, uint8, bytes32)`, three
    words). With another element shape Roles compares fewer bytes than the
    library reads. -/
def leafTypes (c : Condition) : Bool :=
  c.encoding = .Array && c.inlineSize = 0 &&
  match c.children with
  | [t] => t.inlineSize = 96
  | _ => false

/-- `types` as the library's fallback finds it: `typesPtr =
    calldataload(0x44) + 4`, the length at `typesPtr`, then the elements
    (zeros past the end of the calldata). -/
def typesPtr (data : Bytes) : Nat := (load data 68 + 4) % 2 ^ 256

def typesLen (data : Bytes) : Nat := load data (typesPtr data)

/-- The element bytes the library reads. -/
def typesRaw (data : Bytes) : Bytes :=
  ((data.drop (typesPtr data + 32)) ++ zeros (96 * typesLen data)).take (96 * typesLen data)

/-- The element bytes a stored `EqualTo` compValue on `types` pins (the
    stored value is the length word and the elements). -/
def pinnedRaw (cv : Bytes) : Bytes := (cv.drop 32).take (96 * wordVal (key cv))

/-- The operand `_read` resolves for an array of 96-byte elements read from
    its offset: the count word and the elements. -/
theorem operand_arr {data : Calldata} {L : Slice} {o : Operator} {t : Condition} {lb : Nat}
    {cv : Bytes} (ht : t.inlineSize = 96) {op : Slice}
    (h : operand data L 0 ⟨.Array, o, [t], 0, lb, cv⟩ = some op) :
    32 ≤ L.length ∧ 32 + load data L.offset * 96 ≤ L.length ∧
      op = ⟨L.offset, 32 + load data L.offset * 96⟩ := by
  unfold operand sliceRegion at h
  simp only [Nat.lt_irrefl, ite_false] at h
  rw [region_eq] at h
  simp only [Nat.lt_irrefl, ite_false, reduceCtorEq, or_self, ite_true, ht] at h
  cases ha : array data L 96 with
  | none => rw [ha] at h; simp at h
  | some q =>
    obtain ⟨body, count⟩ := q
    rw [ha] at h
    obtain ⟨h32, -, rfl, hcount⟩ := array_some ha
    have hs : slotSize 96 = 96 := rfl
    rw [hs, Nat.le_div_iff_mul_le (by decide)] at hcount
    simp only [show (96 : Nat) > 0 by decide, ite_true, Option.map_some, Option.some.injEq] at h
    exact ⟨h32, by omega, h.symm⟩

/-- **The library hashes pinned type nodes.** When Roles passes `data` with
    `types` pinned (`pinsArg leafTypes 2`), the length and element bytes the
    library's fallback reads are those of a pinned compValue (calldata is
    shorter than `2^256` bytes). -/
theorem route_types {env : Env} {data : Calldata} {n F f : Nat} {root : Condition}
    {cons : List Consumption} {sl : Slots} (hdl : data.length < 2 ^ 256)
    (hpin : pinsArg leafTypes 2 f root = true)
    (hrun : (evalC env data n F ⟨0, data.length⟩ root.inlineSize root cons sl).status = sOk) :
    ∃ e, PinUnder 2 root e ∧ pinnedLeaf leafTypes e = true ∧
      typesLen data = wordVal (key e.compValue) ∧ typesRaw data = pinnedRaw e.compValue := by
  obtain ⟨e, L, hu, hl, hoff, hwithin, hno, heq⟩ :=
    pinsArg_sound leafTypes 2 F f root cons sl hpin hrun
  refine ⟨e, hu, hl, ?_⟩
  have hleaf := hl
  unfold pinnedLeaf leafTypes at hleaf
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hleaf
  obtain ⟨_, ⟨henc, hsz⟩, hch⟩ := hleaf
  obtain ⟨enc, op, cs, sz, lb, cv⟩ := e
  simp only at henc hsz hch hno heq ⊢
  subst henc hsz
  -- the element: one inlined child of 96 bytes
  obtain ⟨t, rfl, ht⟩ : ∃ t, cs = [t] ∧ t.inlineSize = 96 := by
    cases cs with
    | nil => simp at hch
    | cons t rest =>
      cases rest with
      | nil =>
        simp only [decide_eq_true_eq] at hch
        exact ⟨t, rfl, hch⟩
      | cons _ _ => simp at hch
  have hne : (⟨.Array, op, [t], 0, lb, cv⟩ : Condition).encoding ≠ .None := by simp
  cases hop : operand data L 0 ⟨.Array, op, [t], 0, lb, cv⟩ with
  | none => exfalso; apply hno; unfold input; rw [ite_eq_right hne, hop]
  | some opnd =>
    obtain ⟨h32, hfitR, rfl⟩ := operand_arr ht hop
    unfold input inputLength at heq
    rw [ite_eq_right hne, ite_eq_right hne, hop] at heq
    simp only [Slice.bytes] at heq
    have hin : L.offset + 32 ≤ data.length := by omega
    -- the library's pointer is Roles' slice
    have hptr : typesPtr data = L.offset := by
      simp only [show 4 + 32 * 2 = 68 by rfl] at hoff
      unfold typesPtr; rw [Nat.mod_eq_of_lt (by omega)]; omega
    simp only [typesRaw, typesLen, hptr]
    generalize hlv : load data L.offset = len at heq hfitR
    unfold Evaluate.compare at heq
    simp only at heq
    by_cases hz : len = 0
    · subst hz
      simp only [Nat.zero_mul, Nat.add_zero, Nat.lt_irrefl, ite_false, inputB] at heq
      split at heq
      · rename_i hc
        obtain ⟨_, hw⟩ := hc
        simp only [B32.w.injEq] at hw
        rw [← load_take hin, hlv] at hw
        simp [pinnedRaw, ← hw]
      · simp [sParameterNotAllowed, sOk] at heq
    · have hgt : 32 + len * 96 > 32 := by omega
      simp only [hgt, ite_true, inputB] at heq
      split at heq
      · rename_i hc
        obtain ⟨_, hw⟩ := hc
        simp only [B32.h.injEq] at hw
        rw [← hw]
        have hk : key ((data.drop L.offset).take (32 + len * 96)) = (data.drop L.offset).take 32 := by
          unfold key
          rw [List.take_append_of_le_length (by simp; omega), take_take_le (by omega)]
        unfold pinnedRaw
        rw [hk, ← load_take hin, hlv]
        refine ⟨rfl, ?_⟩
        rw [List.take_append_of_le_length (by simp; omega), List.drop_take, List.drop_drop,
          show 32 + len * 96 - 32 = 96 * len by rw [Nat.mul_comm]; omega,
          take_take_le (Nat.le_refl _)]
      · simp [sParameterNotAllowed, sOk] at heq


/-! ## From the element bytes to the type nodes the encoder gets -/

/-- `enum Encoding` by its index; Solidity reverts on an index above 6 when
    the encoder reads `types[i].encoding`. -/
def encOf : Nat → Option Encoding
  | 0 => some .None | 1 => some .Static | 2 => some .Dynamic | 3 => some .Tuple
  | 4 => some .Array | 5 => some .AbiEncoded | 6 => some .EtherValue | _ => none

/-- Element `i` of `types`: three words (zeros past the end of `raw`). -/
def tnfAt (raw : Bytes) (i : Nat) : Option EIP712.TNF :=
  let w := (raw.drop (96 * i) ++ zeros 96).take 96
  (encOf (wordVal ((w.drop 32).take 32))).map fun e =>
    ⟨wordVal (w.take 32), e, (w.drop 64).take 32⟩

/-- `types` as the encoder reads it: `len` elements from the element bytes. -/
def decodeTypes (len : Nat) (raw : Bytes) : Option (List EIP712.TNF) :=
  (List.range len).mapM (tnfAt raw)

theorem tnfAt_typeHash_length {raw : Bytes} {i : Nat} {t : EIP712.TNF} (h : tnfAt raw i = some t) :
    t.typeHash.length = 32 := by
  unfold tnfAt at h
  obtain ⟨e, _, rfl⟩ := Option.map_eq_some_iff.mp h
  simp [zeros]

theorem mapM_some {α β : Type} {f : α → Option β} :
    ∀ {xs : List α} {ys : List β}, xs.mapM f = some ys →
    ys.length = xs.length ∧ ∀ i (h : i < xs.length) (h' : i < ys.length), f xs[i] = some ys[i]
  | [], ys, h => by simp at h; subst h; simp
  | x :: xs, ys, h => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq] at h
    obtain ⟨y, hy, ys', hys', rfl⟩ := h
    obtain ⟨hl, hall⟩ := mapM_some hys'
    refine ⟨by simp [hl], fun i hi hi' => ?_⟩
    cases i with
    | zero => simpa using hy
    | succ i => simpa using hall i (by simpa using hi) (by simpa using hi')

/-- `_toTree(types, 1)` succeeds only if `types[1]` exists. -/
theorem toTree_some_lt {types : List EIP712.TNF} {fuel index : Nat} {t : EIP712.TN}
    (h : EIP712.toTree types fuel index = some t) : index < types.length := by
  cases fuel with
  | zero => simp [EIP712.toTree] at h
  | succ f =>
    unfold EIP712.toTree at h
    split at h
    · simp at h
    · rename_i n hn
      exact (List.getElem?_eq_some_iff.mp hn).1

theorem hashStructE_lt {K : Bytes → Bytes} {data : Bytes} {types : List EIP712.TNF} {index : Nat}
    {r : Bytes} (h : EIP712.hashStructE K data types index = some r) : index < types.length := by
  unfold EIP712.hashStructE at h
  split at h
  · simp at h
  · rename_i root hroot; exact toTree_some_lt hroot

/-- **A typed-message permission with pinned types signs a `RoleTx` digest
    only if a pinned value has the `RoleTx` type hash at `types[1]`.** When
    Roles passes `data` with `types` pinned, and the library's fallback
    signs the digest `hashTypedMessage` computes from the `types` it reads,
    and that digest has the EIP-712 form with type hash `th` (e.g. a `RoleTx`
    for some Roles Modifier), then a pinned value decodes to type nodes whose
    message root carries `th`, unless keccak256 collides on the inputs of the
    two digests. -/
theorem route_typed {env : Env} {data : Calldata} {n F f : Nat} {root : Condition}
    {cons : List Consumption} {sl : Slots} (K : Bytes → Bytes) (hK : ∀ x, (K x).length = 32)
    (hdl : data.length < 2 ^ 256)
    (hpin : pinsArg leafTypes 2 f root = true)
    (hrun : (evalC env data n F ⟨0, data.length⟩ root.inlineSize root cons sl).status = sOk)
    {ts : List EIP712.TNF} (hts : decodeTypes (typesLen data) (typesRaw data) = some ts)
    {domain message domainSep th fields : Bytes} (hds : domainSep.length = 32) (hth : th.length = 32)
    (hD : EIP712.hashTypedMessage K domain message ts = some (typedDigest K domainSep th fields)) :
    (∃ e, PinUnder 2 root e ∧ pinnedLeaf leafTypes e = true ∧
      decodeTypes (wordVal (key e.compValue)) (pinnedRaw e.compValue) = some ts ∧
      (ts.getD 1 default).typeHash = th) ∨
      SafeSigning.CollisionIn K (typedInputs K domain message ts ++ typedDigestInputs K domainSep th fields) := by
  obtain ⟨e, hu, hl, hlen, hraw⟩ := route_types hdl hpin hrun
  -- `types[1]` exists (the encoder hashes the message from it) and is 32 bytes
  have h1 : 1 < ts.length := by
    unfold EIP712.hashTypedMessage at hD
    split at hD
    · rename_i _ _ _ hm; exact hashStructE_lt hm
    · simp at hD
  have hl1 : (ts.getD 1 default).typeHash.length = 32 := by
    obtain ⟨hlen', hall⟩ := mapM_some hts
    have hi : 1 < (List.range (typesLen data)).length := by rw [← hlen']; exact h1
    have := hall 1 hi h1
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1]
    exact tnfAt_typeHash_length this
  rcases typed_typeHash K hK domain message ts domainSep th fields hds hth hl1 hD with h | h
  · exact .inl ⟨e, hu, hl, by rw [← hlen, ← hraw]; exact hts, h⟩
  · exact .inr h

end EndToEnd
