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

/-- The pin `permissionHazards` accepts for a `bytes` argument: an `EqualTo`
    read as `Dynamic` (from its offset, size from its length word). -/
def leafBytes (c : Condition) : Bool :=
  c.encoding = .Dynamic && c.size = 0

theorem load_take {data : Bytes} {L : Nat} (h : L + 32 ≤ data.length) :
    load data L = wordVal ((data.drop L).take 32) := by
  unfold load
  congr 1
  rw [List.take_append_of_le_length (by simp; omega)]

theorem take_take_le {l : Bytes} {a b : Nat} (h : a ≤ b) : (l.take b).take a = l.take a := by
  rw [List.take_take, Nat.min_eq_left h]

/-- What `__input` reads for a `Dynamic` value read from its offset. -/
theorem input_dyn (data : Calldata) (L : Nat) (op : Operator) (cs : List Condition) (inl : Bool)
    (lb : Nat) (cv : Bytes) :
    input data L ⟨.Dynamic, op, cs, inl, 0, lb, cv⟩ =
      (let size := if L + 32 > data.length then data.length + 1
                   else 32 + ((load data L + 31) &&& notU31)
       if L + size > data.length then .overflow
       else if size = 32 then .word (load data L)
       else if size < 32 then .word (wordVal ((data.drop L).take size))
       else .hash ((data.drop L).take size)) := by
  have hs : Roles.size data L ⟨.Dynamic, op, cs, inl, 0, lb, cv⟩ =
      if L + 32 > data.length then data.length + 1
      else 32 + ((load data L + 31) &&& notU31) := by
    unfold Roles.size; simp
  simp only [input, reduceCtorEq, ite_false, ne_eq, not_true_eq_false, hs]

/-- `tailLocation` of head word 0 at `4`, when in bounds: `4 + offset`. -/
theorem tail0 {data : Bytes} {L : Nat} (h : tailLocation data 4 0 = L) (hL : L ≤ data.length) :
    L = load data 4 + 4 := by
  have := EIP712.fallback_offset data 0 L (by simpa using h) hL
  simpa using this

/-- **The library signs a pinned message.** When Roles passes `data` with
    the `bytes` argument pinned (`pinsArg leafBytes 0`), and Solidity's
    decoder accepts `data` (else the call reverts and nothing is signed),
    the decoded message is the message of a pinned compValue. -/
theorem route_bytes {env : Env} {data : Calldata} {n F f : Nat} {root : Condition}
    {cons : List Consumption} {sl : Slots} {m : Bytes}
    (hpin : pinsArg leafBytes 0 f root = true)
    (hrun : (evalC env data n F 0 root cons sl).status = sOk)
    (hdec : solDecodeBytes data = some m) :
    ∃ e, PinUnder 0 root e ∧ pinnedLeaf leafBytes e = true ∧ m = pinnedBytes e.compValue := by
  obtain ⟨e, hu, hl, hno, heq⟩ := pinsArg_sound leafBytes 0 F f root cons sl hpin hrun
  refine ⟨e, hu, hl, ?_⟩
  simp only [Nat.mul_zero] at hno heq
  have hleaf := hl
  unfold pinnedLeaf leafBytes at hleaf
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hleaf
  obtain ⟨_, henc, hsz⟩ := hleaf
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
  generalize hL : tailLocation data 4 0 = L at hno heq
  -- Roles' reading: in bounds, so at the same place
  obtain ⟨enc, op, cs, inl, sz, lb, cv⟩ := e
  simp only at henc hsz ⊢
  subst henc hsz
  rw [input_dyn] at hno heq
  have hin : L + 32 ≤ data.length := by
    by_cases hc : L + 32 ≤ data.length
    · exact hc
    · exfalso; apply hno
      have h1 : data.length < L + 32 := by omega
      simp only [gt_iff_lt, h1, ite_true]
      rw [if_pos (by omega)]
  have hL4 : L = load data 4 + 4 := tail0 hL (by omega)
  rw [show 4 + load data 4 = L by omega] at hlen hfit ⊢
  generalize hlv : load data L = len at hlen hfit ⊢ hno heq
  have hround : (len + 31) &&& notU31 = ceil32 len := roundUp_eq len (by omega)
  simp only [show ¬(L + 32 > data.length) by omega, ite_false, hround] at hno heq
  have hfitR : L + (32 + ceil32 len) ≤ data.length := by
    by_cases hc : L + (32 + ceil32 len) ≤ data.length
    · exact hc
    · exfalso; apply hno; rw [if_pos (by omega)]
  rw [if_neg (by omega)] at heq
  by_cases hz : ceil32 len = 0
  · have hl0 : len = 0 := by have := ceil32_ge len; omega
    subst hl0
    rw [if_pos (by omega)] at heq
    unfold cvB at heq
    split at heq
    · simp [inputB] at heq
    · simp only [inputB, B32.w.injEq] at heq
      simp [pinnedBytes, ← heq]
  · rw [if_neg (by omega), if_neg (by omega)] at heq
    unfold cvB at heq
    split at heq
    · simp only [inputB, B32.h.injEq] at heq
      -- the stored value is exactly the bytes Roles hashed
      subst heq
      have hk : key ((data.drop L).take (32 + ceil32 len)) = (data.drop L).take 32 := by
        unfold key
        rw [List.take_append_of_le_length (by simp; omega), take_take_le (by omega)]
      unfold pinnedBytes
      rw [hk, ← load_take hin, hlv, List.drop_take, List.drop_drop,
        show 32 + ceil32 len - 32 = ceil32 len by omega, take_take_le (ceil32_ge len)]
    · simp [inputB] at heq


/-! ## The `types` argument -/

/-- The pin `permissionHazards` must accept for `types`: an `EqualTo` read
    as an array of 96-byte elements (`(uint256, uint8, bytes32)`, three
    words). With another element shape Roles compares fewer bytes than the
    library reads. -/
def leafTypes (c : Condition) : Bool :=
  c.encoding = .Array && c.size = 0 &&
  match c.children with
  | [t] => t.inlined && t.size = 96
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

/-- `AbiLocation.size`'s array loop over inlined elements. -/
theorem sizeArrayLoop_inlined (data : Calldata) (loc : Nat) (c : Condition) (sizeOf : Nat → Nat)
    (h : c.inlined = true) : ∀ (k h0 : Nat), sizeArrayLoop data loc c sizeOf k h0 = k * c.size
  | 0, _ => by simp [sizeArrayLoop]
  | k + 1, h0 => by
    simp only [sizeArrayLoop, h, ite_true]
    rw [sizeArrayLoop_inlined data loc c sizeOf h k]
    rw [Nat.succ_mul]; omega

/-- **The library hashes pinned type nodes.** When Roles passes `data` with
    `types` pinned (`pinsArg leafTypes 2`), the length and element bytes the
    library's fallback reads are those of a pinned compValue (calldata is
    shorter than `2^256` bytes). -/
theorem route_types {env : Env} {data : Calldata} {n F f : Nat} {root : Condition}
    {cons : List Consumption} {sl : Slots} (hdl : data.length < 2 ^ 256)
    (hpin : pinsArg leafTypes 2 f root = true)
    (hrun : (evalC env data n F 0 root cons sl).status = sOk) :
    ∃ e, PinUnder 2 root e ∧ pinnedLeaf leafTypes e = true ∧
      typesLen data = wordVal (key e.compValue) ∧ typesRaw data = pinnedRaw e.compValue := by
  obtain ⟨e, hu, hl, hno, heq⟩ := pinsArg_sound leafTypes 2 F f root cons sl hpin hrun
  refine ⟨e, hu, hl, ?_⟩
  have hleaf := hl
  unfold pinnedLeaf leafTypes at hleaf
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hleaf
  obtain ⟨_, ⟨henc, hsz⟩, hch⟩ := hleaf
  generalize hL : tailLocation data 4 (32 * 2) = L at hno heq
  obtain ⟨enc, op, cs, inl, sz, lb, cv⟩ := e
  simp only at henc hsz hch ⊢
  subst henc hsz
  -- the element: one inlined child of 96 bytes
  obtain ⟨t, rfl, ht⟩ : ∃ t, cs = [t] ∧ t.inlined = true ∧ t.size = 96 := by
    cases cs with
    | nil => simp at hch
    | cons t rest =>
      cases rest with
      | nil =>
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hch
        exact ⟨t, rfl, hch⟩
      | cons _ _ => simp at hch
  have hs : ∀ L, Roles.size data L ⟨.Array, op, [t], inl, 0, lb, cv⟩ =
      if L + 32 > data.length then data.length + 1 else 32 + load data L * 96 := by
    intro L
    unfold Roles.size
    simp only [reduceCtorEq, ite_false, or_self, ite_true]
    rw [sizeArrayLoop_inlined data (L + 32) t _ ht.1, ht.2]
  simp only [input, reduceCtorEq, ite_false, ne_eq, not_true_eq_false, hs] at hno heq
  have hin : L + 32 ≤ data.length := by
    by_cases hc : L + 32 ≤ data.length
    · exact hc
    · exfalso; apply hno
      have h1 : data.length < L + 32 := by omega
      simp only [gt_iff_lt, h1, ite_true]
      rw [if_pos (by omega)]
  simp only [show ¬(L + 32 > data.length) by omega, ite_false] at hno heq
  have hfitR : L + (32 + load data L * 96) ≤ data.length := by
    by_cases hc : L + (32 + load data L * 96) ≤ data.length
    · exact hc
    · exfalso; apply hno; rw [if_pos (by omega)]
  rw [if_neg (by omega)] at heq
  -- the library's pointer is Roles' location
  have hptr : typesPtr data = L := by
    have := EIP712.fallback_offset data 2 L hL (by omega)
    simp only [show 4 + 32 * 2 = 68 by rfl] at this
    unfold typesPtr; rw [Nat.mod_eq_of_lt (by omega)]; omega
  simp only [typesRaw, typesLen, hptr]
  generalize hlv : load data L = len at heq hfitR
  by_cases hz : len = 0
  · subst hz
    rw [if_pos (by omega)] at heq
    unfold cvB at heq
    split at heq
    · simp [inputB] at heq
    · simp only [inputB, B32.w.injEq] at heq
      simp [pinnedRaw, ← heq]
  · rw [if_neg (by omega), if_neg (by omega)] at heq
    unfold cvB at heq
    split at heq
    · simp only [inputB, B32.h.injEq] at heq
      subst heq
      have hk : key ((data.drop L).take (32 + len * 96)) = (data.drop L).take 32 := by
        unfold key
        rw [List.take_append_of_le_length (by simp; omega), take_take_le (by omega)]
      unfold pinnedRaw
      rw [hk, ← load_take hin, hlv]
      refine ⟨rfl, ?_⟩
      rw [List.take_append_of_le_length (by simp; omega), List.drop_take, List.drop_drop,
        show 32 + len * 96 - 32 = 96 * len by rw [Nat.mul_comm]; omega, take_take_le (Nat.le_refl _)]
    · simp [inputB] at heq


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
    (hrun : (evalC env data n F 0 root cons sl).status = sOk)
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
