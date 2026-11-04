import DecoderFaithfulness.Roles

/-!
# `ConditionEvaluator.evaluate`, transcribed

Transcribed from `packages/evm/contracts` (branch `formal/abi-layer-a`):

* `core/evaluate/ConditionEvaluator.sol` → `evalC` and its loops
* `core/evaluate/WithinAllowanceChecker.sol`, `common/AllowanceConsumer.sol`
  → `allowance`, `consume`

It runs on the unpacked `Condition` the evaluator sees (what
`ConditionPacking.unpack` returns, `annotate` of the input tree), and uses
the decoder transcription for locations (`children`, `size`, `input`) and
`bitmaskCheck`. Differences from the Solidity:

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
  locations : Nat → Nat

def Slots.empty : Slots := ⟨fun _ => .word 0, fun _ => 0⟩

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
      .., location, size, consumptions, pluckedValues)`: a failure status,
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
/-- `_result`. -/
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

/-- The value `__input` returns (`Encoding.None` reads `context.value`). -/
def inputB (env : Env) : Input → B32
  | .etherValue => .w env.value
  | .word n => .w n
  | .hash pre => .h pre
  | .overflow => .w 0

/-- `bytes32(compValue)`, or its keccak256 if longer than 32 bytes. -/
def cvB (cv : Bytes) : B32 :=
  if cv.length > 32 then .h cv else .w (wordVal (key cv))

def toSigned (n : Nat) : Int := if n < 2 ^ 255 then n else (n : Int) - 2 ^ 256

/-- `__compare` and `__compareSigned` (which takes `bytes32(compValue)`,
    never its hash). -/
def compare (op : Operator) (v : B32) (cv : Bytes) : Nat :=
  match op with
  | .EqualTo => if v = cvB cv then sOk else sParameterNotAllowed
  | .GreaterThan =>
    match v, cvB cv with
    | .w a, .w b => if a > b then sOk else sParameterLessThanAllowed
    | _, _ => sParameterLessThanAllowed
  | .LessThan =>
    match v, cvB cv with
    | .w a, .w b => if a < b then sOk else sParameterGreaterThanAllowed
    | _, _ => sParameterGreaterThanAllowed
  | .SignedIntGreaterThan =>
    match v with
    | .w a => if toSigned a > toSigned (wordVal (key cv)) then sOk else sParameterLessThanAllowed
    | _ => sParameterLessThanAllowed
  | _ =>
    match v with
    | .w a => if toSigned a < toSigned (wordVal (key cv)) then sOk else sParameterGreaterThanAllowed
    | _ => sParameterGreaterThanAllowed

/-! ## `_matches`: leading bytes -/

/-- The leading-bytes check of `_matches`: `none` to go on, or the status. -/
def leadingCheck (data : Calldata) (loc : Nat) (cv : Bytes) : Option Nat :=
  if cv.length = 0 then none
  else if loc + cv.length > data.length then some sCalldataOverflow
  else if cv.length > 32 then some revert  -- `32 - length` underflows
  else if (data.drop loc).take cv.length = cv then none
  else some sLeadingBytesNotAMatch

/-! ## `evaluate` -/

/-- `uint8(compValue[k])`; out of range is a panic. -/
def cvAt (cv : Bytes) (k : Nat) : Option Nat := (cv[k]?).map (·.val)

/-- `AbiLocation.children` allocates `new uint256[](childCount)` before
    decoding; an array length above `2^64 - 1` panics there. (The decoder
    transcription returns `none`, an overflow, for it; both deny.) -/
def allocPanics (data : Calldata) (loc : Nat) (c : Condition) : Bool :=
  c.encoding = .Array ∧ ¬(loc + 32 > data.length) ∧ load data loc > 2 ^ 64 - 1

/-- `AbiLocation.children` with that panic: `.inl` revert. -/
def childrenE (data : Calldata) (loc : Nat) (c : Condition) : Nat ⊕ Option (List Nat) :=
  if allocPanics data loc c then .inl revert else .inr (children data loc c)

/-- `_slice` compValue: `uint16(bytes2(compValue))` (zero-padded). -/
def shiftOf (cv : Bytes) : Nat := wordVal ((cv ++ zeros 2).take 2)

def zipLocsGo (data : Calldata) (n : Nat) (cv : Bytes) :
    List Condition → Slots → Nat → Option Nat → List (List Nat) → Nat ⊕ (List (List Nat) × Nat)
  | [], _, _, len, acc => .inr (acc, len.getD 0)
  | fd :: rest, sl, f, len, acc =>
    match cvAt cv f with
    | none => .inl revert
    | some k =>
      if k ≥ n then .inl revert else
      match childrenE data (sl.locations k) (zipStub fd) with
      | .inl s => .inl s
      | .inr none => .inl sCalldataOverflow
      | .inr (some ls) =>
        match len with
        | some m => if m ≠ ls.length then .inl sZippedArrayLengthMismatch
                    else zipLocsGo data n cv rest sl (f + 1) len (acc ++ [ls])
        | none => zipLocsGo data n cv rest sl (f + 1) (some ls.length) (acc ++ [ls])

/-- `_zipLocations`: the element locations of each plucked array, and
    their common length, or the status. -/
def zipLocs (data : Calldata) (n : Nat) (cv : Bytes) (fields : List Condition) (sl : Slots) :
    Nat ⊕ (List (List Nat) × Nat) :=
  zipLocsGo data n cv fields sl 0 none []

mutual
  def evalC (env : Env) (data : Calldata) (n : Nat) : Nat → Nat → Condition → List Consumption → Slots → Res
    | 0, _, _, _, sl => violation revert sl
    | fuel + 1, loc, c, cons, sl =>
      match c.operator with
      | .Pass => ok cons sl
      | .Matches =>
        let loc := if loc > 0 ∧ c.encoding = .AbiEncoded then loc + 32 else loc
        match leadingCheck data loc c.compValue with
        | some s => violation s sl
        | none =>
          match childrenE data (loc + c.leadingBytes) c with
          | .inl s => violation s sl
          | .inr none => violation sCalldataOverflow sl
          | .inr (some locs) =>
            if c.children.length ≠ locs.length then violation sParameterNotAMatch sl
            else seqLoop env data n fuel (c.children.zip locs) cons sl
      | .And => seqLoop env data n fuel (c.children.map (·, loc)) cons sl
      | .Or => orLoop env data n fuel c.children loc cons sl
      | .Slice =>
        match cvAt c.compValue 2 with
        | none => violation revert sl
        | some sz =>
          let shift := shiftOf c.compValue
          if c.inlined = false ∧ loc + 32 > data.length then violation sCalldataOverflow sl
          else
            let length := if c.inlined then c.size else load data loc
            if shift + sz > length then violation sCalldataOverflow sl
            else
              match c.children with
              | [] => violation revert sl
              | ch :: _ =>
                evalC env data n fuel (loc + (if c.inlined then 0 else 32) + shift)
                  (ch.withSize sz) cons sl
      | .Pluck =>
        match input data loc c with
        | .overflow => violation sCalldataOverflow sl
        | v =>
          match cvAt c.compValue 0 with
          | none => violation revert sl
          | some k =>
            if k ≥ n then violation revert sl else
            ok cons ⟨fun j => if j = k then (match v with
                        | .etherValue => .word env.value
                        | v => v) else sl.values j,
                     fun j => if j = k then loc else sl.locations j⟩
      | .Empty => result (if data.length = 0 then sOk else sCalldataNotEmpty) cons sl
      | .ArraySome | .ArrayEvery =>
        match childrenE data loc c with
        | .inl s => violation s sl
        | .inr none => violation sCalldataOverflow sl
        | .inr (some locs) =>
          match c.children with
          | [] => if locs = [] then
                    (if c.operator = .ArrayEvery then ok cons sl
                     else violation sNoArrayElementPasses sl)
                  else violation revert sl
          | ch :: _ =>
            if c.operator = .ArrayEvery then everyLoop env data n fuel ch locs cons sl
            else someLoop env data n fuel ch locs cons sl
      | .ArrayTailMatches =>
        match childrenE data loc c with
        | .inl s => violation s sl
        | .inr none => violation sCalldataOverflow sl
        | .inr (some locs) =>
          if locs.length < c.children.length then violation sParameterNotAMatch sl
          else seqLoop env data n fuel (c.children.zip (locs.drop (locs.length - c.children.length)))
            cons sl
      | .ZipSome | .ZipEvery =>
        match c.children with
        | [] => violation revert sl
        | t :: _ =>
          match zipLocs data n c.compValue t.children sl with
          | .inl s => violation s sl
          | .inr (locss, len) =>
            zipLoop env data n fuel (c.operator = .ZipEvery) t.children locss len 0 cons cons sl
      | .EqualTo | .GreaterThan | .LessThan | .SignedIntGreaterThan | .SignedIntLessThan =>
        match input data loc c with
        | .overflow => violation sCalldataOverflow sl
        | v => result (compare c.operator (inputB env v) c.compValue) cons sl
      | .Bitmask =>
        result (bitmaskStatus (bitmaskCheck data loc c.compValue c.inlined c.size [])) cons sl
      | .WithinAllowance =>
        match input data loc c with
        | .overflow => violation sCalldataOverflow sl
        | v =>
          let amount := match inputB env v with
            | .w x => x
            | .h _ => 0
          let (s, cons') := allowance env cons amount c.compValue
          result s cons' sl
      | .CallWithinAllowance =>
        let (s, cons') := allowance env cons 1 c.compValue
        result s cons' sl
      | .WithinRatio => result (env.ratio c.compValue sl.values) cons sl
      | .Custom =>
        let sz := if c.size ≠ 0 then c.size else size data loc c
        match env.customCall c.compValue loc sz sl.values with
        | .inl s => violation s sl
        | .inr chs =>
          let (s, cons') := applyCharges env cons chs
          result s cons' sl
      | .EqualToAvatar => violation revert sl
  termination_by fuel _ _ _ _ => (fuel, 0, 0)

  /-- `_and`, `_matches`, `_arrayTailMatches`: in order, stop at the first
      failure. -/
  def seqLoop (env : Env) (data : Calldata) (n : Nat) (fuel : Nat) :
      List (Condition × Nat) → List Consumption → Slots → Res
    | [], cons, sl => ok cons sl
    | (c, l) :: rest, cons, sl =>
      let r := evalC env data n fuel l c cons sl
      if r.status ≠ sOk then r else seqLoop env data n fuel rest r.cons r.slots
  termination_by xs _ _ => (fuel, 1, xs.length)

  /-- `_or`: from the same consumptions, stop at the first success. -/
  def orLoop (env : Env) (data : Calldata) (n : Nat) (fuel : Nat) :
      List Condition → Nat → List Consumption → Slots → Res
    | [], _, _, sl => violation sOrViolation sl
    | c :: rest, loc, cons, sl =>
      let r := evalC env data n fuel loc c cons sl
      if r.status = sOk ∨ r.status = revert then r else orLoop env data n fuel rest loc cons r.slots
  termination_by xs _ _ _ => (fuel, 1, xs.length)

  /-- `_arrayIterator` for `ArrayEvery`. -/
  def everyLoop (env : Env) (data : Calldata) (n : Nat) (fuel : Nat) (c : Condition) :
      List Nat → List Consumption → Slots → Res
    | [], cons, sl => ok cons sl
    | l :: rest, cons, sl =>
      let r := evalC env data n fuel l c cons sl
      if r.status = revert then r
      else if r.status ≠ sOk then { r with status := sNotEveryArrayElementPasses }
      else everyLoop env data n fuel c rest r.cons r.slots
  termination_by ls _ _ => (fuel, 1, ls.length)

  /-- `_arrayIterator` for `ArraySome`. -/
  def someLoop (env : Env) (data : Calldata) (n : Nat) (fuel : Nat) (c : Condition) :
      List Nat → List Consumption → Slots → Res
    | [], _, sl => violation sNoArrayElementPasses sl
    | l :: rest, cons, sl =>
      let r := evalC env data n fuel l c cons sl
      if r.status = sOk ∨ r.status = revert then r else someLoop env data n fuel c rest cons r.slots
  termination_by ls _ _ => (fuel, 1, ls.length)

  /-- `_zipIterator`, from element `i` of `n`. `base` are the consumptions
      the Zip started with (each `ZipSome` element starts from them). -/
  def zipLoop (env : Env) (data : Calldata) (n : Nat) (fuel : Nat) (every : Bool) (fields : List Condition)
      (locss : List (List Nat)) : Nat → Nat → List Consumption → List Consumption → Slots → Res
    | 0, _, _, cons, sl => if every then ok cons sl else violation sNoZippedElementPasses sl
    | k + 1, i, base, cons, sl =>
      let r := seqLoop env data n fuel
        (fields.zip (locss.map fun ls => ls.getD i 0)) (if every then cons else base) sl
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
    | ⟨_, _, cs, _, _, _, _⟩ => depthL cs + 1
  def depthL : List Condition → Nat
    | [] => 0
    | c :: cs => max (depth c) (depthL cs)
end

/-- `evaluate(data, 0, root, consumptions, context)` with `maxPluck` slots. -/
def run (env : Env) (data : Calldata) (root : Condition) (maxPluck : Nat)
    (cons : List Consumption) : Res :=
  evalC env data maxPluck (depth root + 2) 0 root cons Slots.empty

end Evaluate
