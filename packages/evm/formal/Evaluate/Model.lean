import DecoderFaithfulness.Roles

/-!
# `ConditionEvaluator.evaluate`, transcribed

Transcribed from `packages/evm/contracts`:

* `core/evaluate/ConditionEvaluator.sol` → `evalC` and its loops
* `core/evaluate/WithinAllowanceChecker.sol`, `common/AllowanceConsumer.sol`
  → `allowance`, `consume`

It runs on the unpacked `Condition` the evaluator sees (what
`ConditionPacking.unpack` returns, `annotate` of the input tree), and uses
the decoder transcription for slices (`children`, `elements`,
`slicePayload`, `operand`, `input`) and `bitmask`. Differences from the
Solidity:

* Arithmetic is on `Nat`.
* A revert (`UnsupportedOperator`, a panic) is the status `revert`, which
  every caller passes up unchanged, as a revert ends the whole evaluation.
* What the evaluator gets from outside is a parameter (`Env`): `msg.value`,
  the accrued balance of each allowance key, and the results of the external
  calls (`Custom` checkers, `WithinRatio`, price adapters).
* A keccak256 hash is represented by its preimage (`Input.hash`). Two hashes
  are equal iff their preimages are; a hash never equals a word, and an
  ordering comparison on a hash fails. Integrity only allows `EqualTo` on
  values longer than 32 bytes.
* `Result.violatedNodeIndex` and `Result.calldataOffset` are not modeled.
* `fuel` bounds the recursion depth; `run` gives enough.
-/

namespace Evaluate
open DecoderFaithfulness DecoderFaithfulness.Roles

/-! ## Status codes (`types/Authorization.sol`) -/

def sOk := 0
def sOrViolation := 1
def sParameterNotAllowed := 2
def sParameterLessThanAllowed := 3
def sParameterGreaterThanAllowed := 4
def sParameterNotAMatch := 5
def sNotEveryArrayElementPasses := 6
def sNoArrayElementPasses := 7
def sAllowanceExceeded := 18
def sCalldataOverflow := 20
def sCalldataNotEmpty := 23
def sLeadingBytesNotAMatch := 24
def sZippedArrayLengthMismatch := 25
def sNoZippedElementPasses := 26
def sNotEveryZippedElementPasses := 27
/-- Not a status: the evaluation reverts. -/
def revert := 255

def bitmaskStatus : BitmaskStatus → Nat
  | .Ok => 0
  | .BitmaskOverflow => 8
  | .BitmaskNotAllowed => 9
  | .CalldataOverflow => 20

/-! ## State -/

/-- An entry of the running consumption list. -/
structure Consumption where
  key : Bytes
  balance : Nat
  consumed : Nat
  deriving DecidableEq, Repr

/-- `context.pluckedValues` and `context.pluckedLocations`. They are memory
    arrays written in place, so writes survive failing branches. -/
structure Slots where
  values : Nat → Input
  locations : Nat → Slice

def Slots.empty : Slots := ⟨fun _ => .word 0, fun _ => ⟨0, 0⟩⟩

/-- What `evaluate` reads besides calldata, the tree and its own state. -/
structure Env where
  /-- `context.value` (`msg.value` of the checked transaction). -/
  value : Nat
  /-- `AllowanceConsumer.accrue`: the balance of a key when first touched. -/
  balance : Bytes → Nat
  /-- `PriceLoader` and the conversion of `_scaleInput`, for compValues
      longer than 32 bytes: `(status, amount)`. -/
  scale : Bytes → Nat → Nat × Nat
  /-- The custom checker's answer in `CustomConditionChecker.check(compValue,
      .., location, length, consumptions, pluckedValues)`: a failure status,
      or the allowance charges it reports, which `_applyConsumptions` makes. -/
  customCall : Bytes → Nat → Nat → (Nat → Input) → Nat ⊕ List (Bytes × Nat)
  /-- `WithinRatioChecker.check(compValue, pluckedValues)`. -/
  ratio : Bytes → (Nat → Input) → Nat

/-- `Result`: status and consumptions (empty on a violation), plus the slots. -/
structure Res where
  status : Nat
  cons : List Consumption
  slots : Slots

def ok (cons : List Consumption) (sl : Slots) : Res := ⟨sOk, cons, sl⟩
def violation (s : Nat) (sl : Slots) : Res := ⟨s, [], sl⟩
/-- A check: `_violation` unless the status is `Ok`. -/
def result (s : Nat) (cons : List Consumption) (sl : Slots) : Res :=
  if s = sOk then ok cons sl else violation s sl

/-! ## Allowances -/

/-- `bytes32(compValue)`: the first 32 bytes, zero-padded. -/
def key (cv : Bytes) : Bytes := (cv ++ zeros 32).take 32

/-- `AllowanceConsumer.consume`: the entry of `k` (the first one; accrued
    and appended if there is none) must have `amount` left; it is replaced by
    a copy with the amount added. On failure the list is returned unchanged.
    (`_findOrAccrue` + `_copyOnWrite`, as a recursion over the list.) -/
def consume (env : Env) : List Consumption → Bytes → Nat → Nat × List Consumption
  | [], k, amount =>
    if amount > env.balance k then (sAllowanceExceeded, [])
    else (sOk, [⟨k, env.balance k, amount⟩])
  | e :: es, k, amount =>
    if e.key = k then
      if amount > e.balance - e.consumed then (sAllowanceExceeded, e :: es)
      else (sOk, { e with consumed := e.consumed + amount } :: es)
    else ((consume env es k amount).1, e :: (consume env es k amount).2)

/-- `WithinAllowanceChecker.check`. -/
def allowance (env : Env) (cons : List Consumption) (value : Nat) (cv : Bytes) :
    Nat × List Consumption :=
  let (s, amount) := if cv.length = 32 then (sOk, value) else env.scale cv value
  if s ≠ sOk then (s, cons) else consume env cons (key cv) amount

/-- `CustomConditionChecker._applyConsumptions`: charge in order, stop at the
    first failure. -/
def applyCharges (env : Env) : List Consumption → List (Bytes × Nat) → Nat × List Consumption
  | cons, [] => (sOk, cons)
  | cons, (k, a) :: rest =>
    let r := consume env cons k a
    if r.1 ≠ sOk then r else applyCharges env r.2 rest

/-! ## Comparisons -/

/-- `bytes32` values: a word, or the keccak256 of some bytes. -/
inductive B32 where
  | w (n : Nat)
  | h (pre : Bytes)
  deriving DecidableEq

/-- The word `_read` returns (`Encoding.None` reads `context.value`). -/
def inputB (env : Env) : Input → B32
  | .etherValue => .w env.value
  | .word n => .w n
  | .hash pre => .h pre
  | .overflow => .w 0

def toSigned (n : Nat) : Int := if n < 2 ^ 255 then n else (n : Int) - 2 ^ 256

/-- `signextend(length - 1, n)` as an `int256`: a value of fewer than 32
    bytes carries its sign in its top bit. (For 32 bytes and more, and for
    0, where `length - 1` wraps, `signextend` leaves `n` as it is.) -/
def signExtend (length n : Nat) : Int :=
  if 0 < length ∧ length < 32 then
    if n % 2 ^ (8 * length) < 2 ^ (8 * length - 1) then ((n % 2 ^ (8 * length) : Nat) : Int)
    else ((n % 2 ^ (8 * length) : Nat) : Int) - 2 ^ (8 * length)
  else toSigned n

/-- `_compare`, on the word `v` of an operand of `length` bytes. -/
def compare (op : Operator) (v : B32) (length : Nat) (cv : Bytes) : Nat :=
  match op with
  | .EqualTo =>
    -- a word against a word, or a hash against the hash of a compValue as long
    if (if length > 32 then cv.length = length ∧ v = .h cv
        else cv.length = 32 ∧ v = .w (wordVal (key cv))) then sOk
    else sParameterNotAllowed
  | .GreaterThan =>
    match v with
    | .w a => if a > wordVal (key cv) then sOk else sParameterLessThanAllowed
    | .h _ => sParameterLessThanAllowed
  | .LessThan =>
    match v with
    | .w a => if a < wordVal (key cv) then sOk else sParameterGreaterThanAllowed
    | .h _ => sParameterGreaterThanAllowed
  | .SignedIntGreaterThan =>
    match v with
    | .w a =>
      if signExtend length a > toSigned (wordVal (key cv)) then sOk else sParameterLessThanAllowed
    | .h _ => sParameterLessThanAllowed
  | _ =>
    match v with
    | .w a =>
      if signExtend length a < toSigned (wordVal (key cv)) then sOk
      else sParameterGreaterThanAllowed
    | .h _ => sParameterGreaterThanAllowed

/-! ## `_matches`: the block of the children -/

/-- The leading-bytes check of `_matches`, on the payload of an `AbiEncoded`
    node: `none` to go on, or the status. Both sides are loaded as a word
    (`bytes32(..)`, zero-padded) and compared on the leading bytes. -/
def leadingCheck (data : Calldata) (payload : Slice) (cv : Bytes) : Option Nat :=
  if cv.length = 0 then none
  else if cv.length > 32 then some revert  -- `32 - length` underflows
  else if (payload.bytes data ++ zeros 32).take cv.length = cv then none
  else some sLeadingBytesNotAMatch

/-- `_matches` up to the children: the block they are found in, or the
    status. (`matchesBody`, with the leading-bytes check.) -/
def matchesHead (data : Calldata) (s : Slice) (c : Condition) : Nat ⊕ Slice :=
  if c.encoding = .AbiEncoded then
    match (if s.offset ≠ 0 then slicePayload data s 0 else some s) with
    | none => .inl sCalldataOverflow
    | some payload =>
      if c.leadingBytes > payload.length then .inl sCalldataOverflow
      else
        match leadingCheck data payload c.compValue with
        | some st => .inl st
        | none => .inr ⟨payload.offset + c.leadingBytes, payload.length - c.leadingBytes⟩
  else .inr s

/-! ## `evaluate` -/

/-- `uint8(compValue[k])`; out of range is a panic. -/
def cvAt (cv : Bytes) (k : Nat) : Option Nat := (cv[k]?).map (·.val)

/-- `_slice` compValue: `uint16(bytes2(compValue))` (zero-padded). -/
def shiftOf (cv : Bytes) : Nat := wordVal ((cv ++ zeros 2).take 2)

/-- The child of a `Slice` that `_slice` does not support, one that
    navigates: `operator > Pass && operator < Slice && operator != Empty`. -/
def navigates : Operator → Bool
  | .And | .Or | .Matches | .ArraySome | .ArrayEvery | .ArrayTailMatches
  | .ZipSome | .ZipEvery => true
  | _ => false

def zipLocsGo (data : Calldata) (n : Nat) (cv : Bytes) :
    List Condition → Slots → Nat → Option Nat → List (List Slice) →
      Nat ⊕ (List (List Slice) × Nat)
  | [], _, _, len, acc => .inr (acc, len.getD 0)
  | fd :: rest, sl, f, len, acc =>
    match cvAt cv f with
    | none => .inl revert
    | some k =>
      if k ≥ n then .inl revert else
      match elements data (sl.locations k) fd.inlineSize with
      | none => .inl sCalldataOverflow
      | some ls =>
        match len with
        | some m => if m ≠ ls.length then .inl sZippedArrayLengthMismatch
                    else zipLocsGo data n cv rest sl (f + 1) len (acc ++ [ls])
        | none => zipLocsGo data n cv rest sl (f + 1) (some ls.length) (acc ++ [ls])

/-- `_zipElements`: the elements of each plucked array, and their common
    length, or the status. -/
def zipLocs (data : Calldata) (n : Nat) (cv : Bytes) (fields : List Condition) (sl : Slots) :
    Nat ⊕ (List (List Slice) × Nat) :=
  zipLocsGo data n cv fields sl 0 none []

mutual
  /-- `_evaluate(dataSlice, inlineSize, condition, consumptions, context)`:
      `s` is `dataSlice`, `z` is `inlineSize`. -/
  def evalC (env : Env) (data : Calldata) (n : Nat) :
      Nat → Slice → Nat → Condition → List Consumption → Slots → Res
    | 0, _, _, _, _, sl => violation revert sl
    | fuel + 1, s, z, c, cons, sl =>
      match c.operator with
      | .Pass => ok cons sl
      | .Matches =>
        match matchesHead data s c with
        | .inl st => violation st sl
        | .inr body =>
          match children data body c with
          | none => violation sCalldataOverflow sl
          | some spans =>
            if c.children.length ≠ spans.length then violation sParameterNotAMatch sl
            else seqLoop env data n fuel (c.children.zip spans) cons sl
      | .And => seqLoop env data n fuel (c.children.map (·, s)) cons sl
      | .Or => orLoop env data n fuel c.children s cons sl
      | .Slice =>
        match cvAt c.compValue 2 with
        | none => violation revert sl
        | some sz =>
          let shift := shiftOf c.compValue
          match slicePayload data s z with
          | none => violation sCalldataOverflow sl
          | some payload =>
            if shift + sz > payload.length then violation sCalldataOverflow sl
            else
              match c.children with
              | [] => violation revert sl
              | ch :: _ =>
                if navigates ch.operator then violation revert sl
                else evalC env data n fuel ⟨payload.offset + shift, sz⟩ sz ch cons sl
      | .Pluck =>
        match input data s z c with
        | .overflow => violation sCalldataOverflow sl
        | v =>
          match cvAt c.compValue 0 with
          | none => violation revert sl
          | some k =>
            if k ≥ n then violation revert sl else
            ok cons ⟨fun j => if j = k then (match v with
                        | .etherValue => .word env.value
                        | v => v) else sl.values j,
                     fun j => if j = k then (pluckSpan data s z c).getD default
                       else sl.locations j⟩
      | .Empty => result (if data.length = 0 then sOk else sCalldataNotEmpty) cons sl
      | .ArraySome | .ArrayEvery =>
        match children data s c with
        | none => violation sCalldataOverflow sl
        | some spans =>
          match c.children with
          | [] => if spans = [] then
                    (if c.operator = .ArrayEvery then ok cons sl
                     else violation sNoArrayElementPasses sl)
                  else violation revert sl
          | ch :: _ =>
            if c.operator = .ArrayEvery then everyLoop env data n fuel ch spans cons sl
            else someLoop env data n fuel ch spans cons sl
      | .ArrayTailMatches =>
        match children data s c with
        | none => violation sCalldataOverflow sl
        | some spans =>
          if spans.length < c.children.length then violation sParameterNotAMatch sl
          else seqLoop env data n fuel
            (c.children.zip (spans.drop (spans.length - c.children.length))) cons sl
      | .ZipSome | .ZipEvery =>
        match c.children with
        | [] => violation revert sl
        | t :: _ =>
          match zipLocs data n c.compValue t.children sl with
          | .inl st => violation st sl
          | .inr (locss, len) =>
            zipLoop env data n fuel (c.operator = .ZipEvery) t.children locss len 0 cons cons sl
      | .EqualTo | .GreaterThan | .LessThan | .SignedIntGreaterThan | .SignedIntLessThan =>
        match input data s z c with
        | .overflow => violation sCalldataOverflow sl
        | v =>
          result (compare c.operator (inputB env v) (inputLength data s z c) c.compValue) cons sl
      | .Bitmask => result (bitmaskStatus (bitmask data s z c.compValue [])) cons sl
      | .WithinAllowance =>
        match input data s z c with
        | .overflow => violation sCalldataOverflow sl
        | v =>
          let amount := match inputB env v with
            | .w x => x
            | .h _ => 0
          let (st, cons') := allowance env cons amount c.compValue
          result st cons' sl
      | .CallWithinAllowance =>
        let (st, cons') := allowance env cons 1 c.compValue
        result st cons' sl
      | .WithinRatio => result (env.ratio c.compValue sl.values) cons sl
      | .Custom =>
        -- the ether value has no encoding: it is passed with a length of 0
        match (if c.encoding = .None then some ⟨s.offset, 0⟩ else operand data s z c) with
        | none => violation sCalldataOverflow sl
        | some op =>
          match env.customCall c.compValue op.offset op.length sl.values with
          | .inl st => violation st sl
          | .inr chs =>
            let (st, cons') := applyCharges env cons chs
            result st cons' sl
      | .EqualToAvatar => violation revert sl
  termination_by fuel _ _ _ _ _ => (fuel, 0, 0)

  /-- `_and`, `_matches`, `_arrayTailMatches`: in order, stop at the first
      failure. -/
  def seqLoop (env : Env) (data : Calldata) (n : Nat) (fuel : Nat) :
      List (Condition × Slice) → List Consumption → Slots → Res
    | [], cons, sl => ok cons sl
    | (c, l) :: rest, cons, sl =>
      let r := evalC env data n fuel l c.inlineSize c cons sl
      if r.status ≠ sOk then r else seqLoop env data n fuel rest r.cons r.slots
  termination_by xs _ _ => (fuel, 1, xs.length)

  /-- `_or`: from the same consumptions, stop at the first success. -/
  def orLoop (env : Env) (data : Calldata) (n : Nat) (fuel : Nat) :
      List Condition → Slice → List Consumption → Slots → Res
    | [], _, _, sl => violation sOrViolation sl
    | c :: rest, loc, cons, sl =>
      let r := evalC env data n fuel loc c.inlineSize c cons sl
      if r.status = sOk ∨ r.status = revert then r else orLoop env data n fuel rest loc cons r.slots
  termination_by xs _ _ _ => (fuel, 1, xs.length)

  /-- `_arrayIterator` for `ArrayEvery`. -/
  def everyLoop (env : Env) (data : Calldata) (n : Nat) (fuel : Nat) (c : Condition) :
      List Slice → List Consumption → Slots → Res
    | [], cons, sl => ok cons sl
    | l :: rest, cons, sl =>
      let r := evalC env data n fuel l c.inlineSize c cons sl
      if r.status = revert then r
      else if r.status ≠ sOk then { r with status := sNotEveryArrayElementPasses }
      else everyLoop env data n fuel c rest r.cons r.slots
  termination_by ls _ _ => (fuel, 1, ls.length)

  /-- `_arrayIterator` for `ArraySome`. -/
  def someLoop (env : Env) (data : Calldata) (n : Nat) (fuel : Nat) (c : Condition) :
      List Slice → List Consumption → Slots → Res
    | [], _, sl => violation sNoArrayElementPasses sl
    | l :: rest, cons, sl =>
      let r := evalC env data n fuel l c.inlineSize c cons sl
      if r.status = sOk ∨ r.status = revert then r else someLoop env data n fuel c rest cons r.slots
  termination_by ls _ _ => (fuel, 1, ls.length)

  /-- `_zipIterator`, from element `i` of `n`. `base` are the consumptions
      the Zip started with (each `ZipSome` element starts from them). -/
  def zipLoop (env : Env) (data : Calldata) (n : Nat) (fuel : Nat) (every : Bool) (fields : List Condition)
      (locss : List (List Slice)) : Nat → Nat → List Consumption → List Consumption → Slots → Res
    | 0, _, _, cons, sl => if every then ok cons sl else violation sNoZippedElementPasses sl
    | k + 1, i, base, cons, sl =>
      let r := seqLoop env data n fuel
        (fields.zip (locss.map fun ls => ls.getD i default)) (if every then cons else base) sl
      if r.status = revert then r
      else if every then
        if r.status ≠ sOk then { r with status := sNotEveryZippedElementPasses }
        else zipLoop env data n fuel every fields locss k (i + 1) base r.cons r.slots
      else if r.status = sOk then r
      else zipLoop env data n fuel every fields locss k (i + 1) base cons r.slots

  termination_by k _ _ _ _ => (fuel, 2, k)
end

mutual
  /-- Tree depth, enough fuel for `evalC`. -/
  def depth : Condition → Nat
    | ⟨_, _, cs, _, _, _⟩ => depthL cs + 1
  def depthL : List Condition → Nat
    | [] => 0
    | c :: cs => max (depth c) (depthL cs)
end

/-- `evaluate(data, root, consumptions, context)` with `maxPluck` slots. -/
def run (env : Env) (data : Calldata) (root : Condition) (maxPluck : Nat)
    (cons : List Consumption) : Res :=
  evalC env data maxPluck (depth root + 2) ⟨0, data.length⟩ root.inlineSize root cons Slots.empty

end Evaluate
