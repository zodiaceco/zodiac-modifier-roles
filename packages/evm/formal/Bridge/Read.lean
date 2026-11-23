import Bridge.TypeDesc

/-!
# The contract's reading of calldata, as a normalization world

`readWorld avatar env data n` is `ConditionEvaluator.evaluate` on calldata
`data`, as a world for `Normalize.sem`. A value is where `evaluate` stands:
a slice, a `Slice` window (a slice whose length `_slice` gives the child as
`inlineSize`), or an element of a Zip (its fields' slices). Every operator
reads the node the evaluator runs for it, `D avatar c`: a `Matches` locates
its children with their own `inlineSize`, as `AbiLocation.children` does.
Nothing is assumed of the calldata or of how the tree relates to an ABI
type.
-/

namespace Bridge
open DecoderFaithfulness DecoderFaithfulness.Roles Normalize Evaluate

/-- Where `evaluate` stands. -/
inductive RV where
  /-- The value in a slice. -/
  | pos (loc : Slice)
  /-- A `Slice` window. -/
  | win (loc : Slice)
  /-- Element `i` of a Zip: the slices of its fields. -/
  | el (locs : List Slice)
  deriving Inhabited

def RV.loc : RV → Slice
  | .pos l => l
  | .win l => l
  | .el _ => default

section
variable (avatar : Bytes) (env : Env) (data : Calldata) (n : Nat)

/-- The `inlineSize` `_evaluate` is given for `c` at `v`: the node's own, or
    in a `Slice` window the size of the window. -/
def szAt (c : Cond) : RV → Nat
  | .win l => l.length
  | _ => (D avatar c).inlineSize

/-- `_matches` on a tuple or calldata: the children's slices, or `none`
    when it fails (leading bytes, overflow). An element of a Zip has its
    fields' slices. -/
def matchLocs (e : Nat) (cv : List Nat) (ch : List Cond) : RV → Option (List Slice)
  | .el locs => some locs
  | v =>
    let d := D avatar ⟨e, 5, cv, ch⟩
    match matchesHead data v.loc d with
    | .inl _ => none
    | .inr body =>
      match children data body d with
      | some locs => if ch.length = locs.length then some locs else none
      | none => none

/-- `_arrayIterator`, `_arrayTailMatches` and `Matches` on an array: the
    element slices, or `none`. -/
def arrLocs (d : Condition) (l : Slice) : Option (List Slice) := children data l d

/-- `_arrayIterator`: every element (`ArrayEvery`) or some element
    (`ArraySome`, each from the consumptions it started with) passes the
    child. Without a child, an empty array passes `ArrayEvery`. -/
def iterT (every : Bool) (d : Condition) (l : Slice) (ss : List (RV → T)) : T :=
  match arrLocs data d l with
  | none => failT
  | some locs =>
    if ss = [] then (if locs = [] ∧ every then passT else failT)
    else if every then seqT (locs.map fun l => (ss.headD fun _ => passT) (.pos l))
    else orT (locs.map fun l => (ss.headD fun _ => passT) (.pos l))

/-- `_arrayTailMatches`: the children on the last elements. -/
def tailT (d : Condition) (l : Slice) (ss : List (RV → T)) : T :=
  match arrLocs data d l with
  | none => failT
  | some locs =>
    if locs.length < ss.length then failT
    else seqT (List.zipWith (fun s l => s (.pos l)) ss (locs.drop (locs.length - ss.length)))

/-- `_matches` on an array. -/
def marrT (d : Condition) (l : Slice) (ss : List (RV → T)) : T :=
  match matchesHead data l d with
  | .inl _ => failT
  | .inr body =>
    match arrLocs data d body with
    | none => failT
    | some locs =>
      if ss.length ≠ locs.length then failT
      else seqT (List.zipWith (fun s l => s (.pos l)) ss locs)

/-- `_zipIterator` from the slots it starts with: every element (`ZipEvery`)
    or some element (`ZipSome`, each from the consumptions it started with)
    passes the tuple child. -/
def zipF (every : Bool) (cv : Bytes) (fields : List Condition) (kid : RV → T) (sl : Slots) : T :=
  match zipLocs data n cv fields sl with
  | .inl _ => failT
  | .inr (locss, len) =>
    if every then
      seqT ((List.range len).map fun i => kid (.el (locss.map fun ls => ls.getD i default)))
    else orT ((List.range len).map fun i => kid (.el (locss.map fun ls => ls.getD i default)))

/-- A Zip: the arrays are decoded in the slots' spans when it runs, with
    the Zip's own field types. -/
def zipT (every : Bool) (d : Condition) (kid : RV → T) : T :=
  match d.children with
  | [] => failT
  | t :: _ => fun sl cs => zipF data n every d.compValue t.children kid sl sl cs

/-- `_slice`: the child at the window. -/
def sliceT (d : Condition) (l : Slice) (z : Nat) (kid : RV → T) : T :=
  match cvAt d.compValue 2 with
  | none => failT
  | some sz =>
    match slicePayload data l z with
    | none => failT
    | some payload =>
      if shiftOf d.compValue + sz > payload.length then failT
      else kid (.win ⟨payload.offset + shiftOf d.compValue, sz⟩)

/-- `_pluck`. -/
def pluckT (d : Condition) (l : Slice) (z : Nat) : T := fun sl cs =>
  match input data l z d, cvAt d.compValue 0 with
  | .overflow, _ => (none, sl)
  | _, none => (none, sl)
  | x, some k =>
    if k ≥ n then (none, sl)
    else (some cs, writeSlot sl k (match x with
      | .etherValue => .word env.value
      | x => x) ((pluckSpan data l z d).getD default))

/-- The comparisons. -/
def cmpOk (d : Condition) (l : Slice) (z : Nat) : Bool :=
  match input data l z d with
  | .overflow => false
  | x => compare d.operator (inputB env x) (inputLength data l z d) d.compValue = sOk

/-- The charges of a custom checker. -/
def customCharges (d : Condition) (l : Slice) (z : Nat) (sl : Slots) :
    Option (List (Bytes × Nat)) :=
  match (if d.encoding = .None then some ⟨l.offset, 0⟩ else operand data l z d) with
  | none => none
  | some op =>
    match env.customCall d.compValue op.offset op.length sl.values with
    | .inl _ => none
    | .inr chs => some chs

/-- The charge of `WithinAllowance`. -/
def allowanceCharge (d : Condition) (l : Slice) (z : Nat) : Option (List (Bytes × Nat)) :=
  match input data l z d with
  | .overflow => none
  | x => (charge env d.compValue (amountOf env x)).map ([·])

/-- Every operator `Normalize.sem` leaves to the world, at node `c`. -/
def readExt (c : Cond) (ss : List (RV → T)) (v : RV) : T :=
  match c.op with
  | 4 => emptyT data
  | 5 => marrT data (D avatar c) v.loc ss
  | 6 => iterT data false (D avatar c) v.loc ss
  | 7 => iterT data true (D avatar c) v.loc ss
  | 8 => tailT data (D avatar c) v.loc ss
  | 10 => zipT data n false (D avatar c) (ss.headD fun _ => passT)
  | 11 => zipT data n true (D avatar c) (ss.headD fun _ => passT)
  | 13 => sliceT data (D avatar c) v.loc (szAt avatar c v) (ss.headD fun _ => passT)
  | 14 => pluckT env data n (D avatar c) v.loc (szAt avatar c v)
  | 15 | 16 | 17 | 18 | 19 | 20 =>
    checkT fun _ => cmpOk env data (D avatar c) v.loc (szAt avatar c v)
  | 21 => checkT fun _ =>
    bitmaskStatus (bitmask data v.loc (szAt avatar c v) (D avatar c).compValue []) = sOk
  | 22 => chargesT env.balance (customCharges env data (D avatar c) v.loc (szAt avatar c v))
  | 23 => checkT fun sl => env.ratio (D avatar c).compValue sl.values = sOk
  | 28 => chargesT env.balance fun _ =>
    allowanceCharge env data (D avatar c) v.loc (szAt avatar c v)
  | 30 => chargesT env.balance fun _ => (charge env (D avatar c).compValue 1).map ([·])
  | _ => failT

/-- **The contract's reading as a normalization world.** -/
def readWorld : World RV Slots CM where
  fields e cv ch v := ((matchLocs avatar data e cv ch v).getD []).map .pos
  dflt := .pos default
  gate e cv ch v := (matchLocs avatar data e cv ch v).isSome
  ext := readExt avatar env data n

end
end Bridge
