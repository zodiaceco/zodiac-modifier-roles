import Bridge.TypeDesc

/-!
# The contract's reading of calldata, as a normalization world

`readWorld avatar env data n` is `ConditionEvaluator.evaluate` on calldata
`data`, as a world for `Normalize.sem`. A value is where `evaluate` stands:
a location, a `Slice` window (the location and the window's size, which
`_slice` gives the child), or an element of a Zip (its fields' locations).
Every operator reads the node the evaluator runs for it, `D avatar c`: a
`Matches` locates its children with their own `inlined` and `size`, as
`AbiLocation.children` does. Nothing is assumed of the calldata or of how
the tree relates to an ABI type.
-/

namespace Bridge
open DecoderFaithfulness DecoderFaithfulness.Roles Normalize Evaluate

/-- Where `evaluate` stands. -/
inductive RV where
  /-- The value at a location. -/
  | pos (loc : Nat)
  /-- A `Slice` window at a location, of `sz` bytes. -/
  | win (loc sz : Nat)
  /-- Element `i` of a Zip: the locations of its fields. -/
  | el (locs : List Nat)
  deriving Inhabited

def RV.loc : RV → Nat
  | .pos l => l
  | .win l _ => l
  | .el _ => 0

section
variable (avatar : Bytes) (env : Env) (data : Calldata) (n : Nat)

/-- The node `evaluate` runs for `c` at `v`: in a `Slice` window, with the
    window's size (`_slice` sets `size` on its child). -/
def nodeAt (c : Cond) : RV → Condition
  | .win _ sz => (D avatar c).withSize sz
  | _ => D avatar c

/-- `_matches` on a tuple or calldata: the children's locations, or `none`
    when it fails (leading bytes, overflow). An element of a Zip has its
    fields' locations. -/
def matchLocs (e : Nat) (cv : List Nat) (ch : List Cond) : RV → Option (List Nat)
  | .el locs => some locs
  | v =>
    let d := D avatar ⟨e, 5, cv, ch⟩
    match leadingCheck data (adjust e v.loc) d.compValue with
    | some _ => none
    | none =>
      match childrenE data (adjust e v.loc + d.leadingBytes) d with
      | .inr (some locs) => if ch.length = locs.length then some locs else none
      | _ => none

/-- `_arrayIterator`, `_arrayTailMatches` and `Matches` on an array: the
    element locations, or `none`. -/
def arrLocs (d : Condition) (l : Nat) : Option (List Nat) :=
  match childrenE data l d with
  | .inr (some locs) => some locs
  | _ => none

/-- `_arrayIterator`: every element (`ArrayEvery`) or some element
    (`ArraySome`, each from the consumptions it started with) passes the
    child. Without a child, an empty array passes `ArrayEvery`. -/
def iterT (every : Bool) (d : Condition) (l : Nat) (ss : List (RV → T)) : T :=
  match arrLocs data d l with
  | none => failT
  | some locs =>
    if ss = [] then (if locs = [] ∧ every then passT else failT)
    else if every then seqT (locs.map fun l => (ss.headD fun _ => passT) (.pos l))
    else orT (locs.map fun l => (ss.headD fun _ => passT) (.pos l))

/-- `_arrayTailMatches`: the children on the last elements. -/
def tailT (d : Condition) (l : Nat) (ss : List (RV → T)) : T :=
  match arrLocs data d l with
  | none => failT
  | some locs =>
    if locs.length < ss.length then failT
    else seqT (List.zipWith (fun s l => s (.pos l)) ss (locs.drop (locs.length - ss.length)))

/-- `_matches` on an array. -/
def marrT (e : Nat) (d : Condition) (l : Nat) (ss : List (RV → T)) : T :=
  match leadingCheck data (adjust e l) d.compValue with
  | some _ => failT
  | none =>
    match arrLocs data d (adjust e l + d.leadingBytes) with
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
    if every then seqT ((List.range len).map fun i => kid (.el (locss.map fun ls => ls.getD i 0)))
    else orT ((List.range len).map fun i => kid (.el (locss.map fun ls => ls.getD i 0)))

/-- A Zip: the arrays are decoded at the slots' locations when it runs, with
    the Zip's own field types. -/
def zipT (every : Bool) (d : Condition) (kid : RV → T) : T :=
  match d.children with
  | [] => failT
  | t :: _ => fun sl cs => zipF data n every d.compValue t.children kid sl sl cs

/-- `_slice`: the child at the window. -/
def sliceT (d : Condition) (l : Nat) (kid : RV → T) : T :=
  match cvAt d.compValue 2 with
  | none => failT
  | some sz =>
    if d.inlined = false ∧ l + 32 > data.length then failT
    else if shiftOf d.compValue + sz > (if d.inlined then d.size else load data l) then failT
    else kid (.win (l + (if d.inlined then 0 else 32) + shiftOf d.compValue) sz)

/-- `_pluck`. -/
def pluckT (d : Condition) (l : Nat) : T := fun sl cs =>
  match input data l d, cvAt d.compValue 0 with
  | .overflow, _ => (none, sl)
  | _, none => (none, sl)
  | x, some k =>
    if k ≥ n then (none, sl)
    else (some cs, writeSlot sl k (match x with
      | .etherValue => .word env.value
      | x => x) l)

/-- The comparisons. -/
def cmpOk (d : Condition) (l : Nat) : Bool :=
  match input data l d with
  | .overflow => false
  | x => compare d.operator (inputB env x) d.compValue = sOk

/-- The charges of a custom checker. -/
def customCharges (d : Condition) (l : Nat) (sl : Slots) : Option (List (Bytes × Nat)) :=
  match env.customCall d.compValue l (if d.size ≠ 0 then d.size else size data l d) sl.values with
  | .inl _ => none
  | .inr chs => some chs

/-- The charge of `WithinAllowance`. -/
def allowanceCharge (d : Condition) (l : Nat) : Option (List (Bytes × Nat)) :=
  match input data l d with
  | .overflow => none
  | x => (charge env d.compValue (amountOf env x)).map ([·])

/-- Every operator `Normalize.sem` leaves to the world, at node `c`. -/
def readExt (c : Cond) (ss : List (RV → T)) (v : RV) : T :=
  match c.op with
  | 4 => emptyT data
  | 5 => marrT data c.enc (nodeAt avatar c v) v.loc ss
  | 6 => iterT data false (nodeAt avatar c v) v.loc ss
  | 7 => iterT data true (nodeAt avatar c v) v.loc ss
  | 8 => tailT data (nodeAt avatar c v) v.loc ss
  | 10 => zipT data n false (nodeAt avatar c v) (ss.headD fun _ => passT)
  | 11 => zipT data n true (nodeAt avatar c v) (ss.headD fun _ => passT)
  | 13 => sliceT data (nodeAt avatar c v) v.loc (ss.headD fun _ => passT)
  | 14 => pluckT env data n (nodeAt avatar c v) v.loc
  | 15 | 16 | 17 | 18 | 19 | 20 => checkT fun _ => cmpOk env data (nodeAt avatar c v) v.loc
  | 21 => checkT fun _ =>
    bitmaskStatus (bitmaskCheck data v.loc (nodeAt avatar c v).compValue (nodeAt avatar c v).inlined
      (nodeAt avatar c v).size []) = sOk
  | 22 => chargesT env.balance (customCharges env data (nodeAt avatar c v) v.loc)
  | 23 => checkT fun sl => env.ratio (nodeAt avatar c v).compValue sl.values = sOk
  | 28 => chargesT env.balance fun _ => allowanceCharge env data (nodeAt avatar c v) v.loc
  | 30 => chargesT env.balance fun _ => (charge env (nodeAt avatar c v).compValue 1).map ([·])
  | _ => failT

/-- **The contract's reading as a normalization world.** -/
def readWorld : World RV Slots CM where
  fields e cv ch v := ((matchLocs avatar data e cv ch v).getD []).map .pos
  dflt := .pos 0
  gate e cv ch v := (matchLocs avatar data e cv ch v).isSome
  ext := readExt avatar env data n

end
end Bridge
