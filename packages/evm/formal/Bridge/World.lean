import Evaluate.Model
import Normalize.Sound
import ConditionPacking.Model

/-!
# The contract's evaluator as a normalization world

`Normalize.sem` is defined over an abstract `World`. Here is the world the
contract is: `contractWorld avatar env data`, the operators of
`ConditionEvaluator.evaluate` on calldata `data`. A value is a pair of a
*layout* and a location: the layout is a `Condition` whose metadata
(encoding, `inlined`, `size`, `leadingBytes`, children) says how the value
is encoded, as the packer computes it for a tree that describes the value.
The world decodes children with the contract's own `AbiLocation` functions,
using that metadata instead of the condition's: so it does not depend on the
tree, which is what normalization needs.

`contractWorld_ok` proves the assumptions `World.Ok` of the normalization
proof for this world. What remains assumed is about the outside: a custom
checker's result is a function of what the contract passes it (`Env`).

`Adequacy.lean` shows the evaluator transcription computes this world's
meaning for every tree whose layout fits the value's.
-/

namespace Bridge
open DecoderFaithfulness DecoderFaithfulness.Roles Normalize Evaluate

/-! ## Consumptions as a map -/

/-- Allowance key ↦ (balance, consumed). The contract keeps a list in the
    order keys were first charged; `toMap` forgets the order. -/
abbrev CM := Bytes → Option (Nat × Nat)
def CM.set (m : CM) (k : Bytes) (x : Nat × Nat) : CM := fun k' => if k' = k then some x else m k'
/-- The entry of key `k`: tracked, or accrued (`bal k`) with nothing consumed. -/
def ent (bal : Bytes → Nat) (m : CM) (k : Bytes) : Nat × Nat := (m k).getD (bal k, 0)

/-- `AllowanceConsumer.consume` on the map. -/
def consumeM (bal : Bytes → Nat) (m : CM) (x : Bytes × Nat) : Option CM :=
  if x.2 > (ent bal m x.1).1 - (ent bal m x.1).2 then none
  else some (m.set x.1 ((ent bal m x.1).1, (ent bal m x.1).2 + x.2))

theorem ent_set_same (bal : Bytes → Nat) (m : CM) (k : Bytes) (x : Nat × Nat) :
    ent bal (m.set k x) k = x := by simp [ent, CM.set]
theorem ent_set_ne (bal : Bytes → Nat) (m : CM) {k k' : Bytes} (x : Nat × Nat) (h : k' ≠ k) :
    ent bal (m.set k x) k' = ent bal m k' := by simp [ent, CM.set, h]
theorem set_set_same (m : CM) (k : Bytes) (x y : Nat × Nat) : (m.set k x).set k y = m.set k y := by
  funext k'; by_cases h : k' = k <;> simp [CM.set, h]
theorem set_set_ne (m : CM) {k1 k2 : Bytes} (x y : Nat × Nat) (h : k1 ≠ k2) :
    (m.set k1 x).set k2 y = (m.set k2 y).set k1 x := by
  funext k'
  by_cases e1 : k' = k1 <;> by_cases e2 : k' = k2
  · subst e1; exact absurd e2 h
  · simp [CM.set, e1, h]
  · simp [CM.set, e2, h.symm]
  · simp [CM.set, e1, e2]

theorem consumeM_comm (bal : Bytes → Nat) (m : CM) (x y : Bytes × Nat) :
    (consumeM bal m x).bind (consumeM bal · y) = (consumeM bal m y).bind (consumeM bal · x) := by
  rcases x with ⟨k1, a⟩
  rcases y with ⟨k2, b⟩
  by_cases hk : k1 = k2
  · subst hk
    rcases h : ent bal m k1 with ⟨bb, cc⟩
    unfold consumeM
    simp only [h]
    by_cases h1 : a > bb - cc <;> by_cases h2 : b > bb - cc <;>
      simp only [h1, h2, ite_true, ite_false, Option.bind_none, Option.bind_some, ent_set_same] <;>
      first
        | rfl
        | (by_cases h3 : b > bb - (cc + a) <;> by_cases h4 : a > bb - (cc + b) <;>
             simp only [h3, h4, ite_true, ite_false, set_set_same] <;>
             first | omega | (congr 2; ext <;> simp <;> omega) | rfl)
        | (have : b > bb - (cc + a) := by omega
           simp [this])
        | (have : a > bb - (cc + b) := by omega
           simp [this])
  · unfold consumeM
    have hne : k2 ≠ k1 := fun h => hk h.symm
    by_cases h1 : a > (ent bal m k1).1 - (ent bal m k1).2 <;>
    by_cases h2 : b > (ent bal m k2).1 - (ent bal m k2).2 <;>
      simp [h1, h2, ent_set_ne _ _ _ hk, ent_set_ne _ _ _ hne, set_set_ne _ _ _ hk]

/-! ## The world -/

/-- SDK compValue bytes. -/
def toBytes (cv : List Nat) : Bytes := cv.map fun n => ⟨n % 256, Nat.mod_lt _ (by decide)⟩

/-- A value: its layout and its location. -/
abbrev Val' := Condition × Nat
abbrev T := Thunk Slots CM

def failT : T := fun sl _ => (none, sl)
def passK : Val' → T := fun _ => passT

/-- The layout of a `Slice` window: `size` bytes, read as a static word
    (`_slice` sets `size` on its child). -/
def winMeta (sz : Nat) : Condition := ⟨.Static, .Pass, [], true, sz, 0, []⟩

/-- `evaluate` moves the location of nested calldata past its length word. -/
def adjust (e : Nat) (l : Nat) : Nat := if l > 0 ∧ e = 5 then l + 32 else l

/-- `_matches` on a tuple or calldata: the children's locations (decoded with
    the layout's metadata), or `none` on an overflow. -/
def decodeAt (data : Calldata) (e : Nat) (m : Condition) (l : Nat) : Option (List Nat) :=
  match childrenE data (adjust e l + m.leadingBytes) m with
  | .inr (some locs) => some locs
  | _ => none

/-- The prefix the leading-bytes check compares (the compValue after the
    2-byte count for calldata). -/
def prefixOf (e : Nat) (cv : List Nat) : Bytes :=
  if e = 5 then (toBytes cv).drop 2 else toBytes cv

/-- The value `__input` reads. -/
def inputAt (data : Calldata) (e : Nat) (m : Condition) (l : Nat) : Input :=
  if e = 0 ∨ e = 6 then .etherValue else input data l m

/-- The compValue a comparison sees: `_transform` drops the first word of an
    `EqualTo` on a node that is not inlined; `EqualToAvatar` compares against
    the avatar. -/
def cmpValue (avatar : Bytes) (e o : Nat) (cv : List Nat) (m : Condition) : Bytes :=
  if o = 15 then avatar
  else if o = 16 ∧ ¬(e = 0 ∨ e = 6) ∧ m.inlined = false then (toBytes cv).drop 32
  else toBytes cv

def toOp (o : Nat) : Operator := if o = 15 then .EqualTo else (ConditionPacking.opOf? o).getD .Pass

/-- An allowance charge of `n` (scaled when the compValue has conversion
    parameters), or `none` when the conversion fails. -/
def charge (env : Env) (cv : Bytes) (n : Nat) : Option (Bytes × Nat) :=
  if cv.length = 32 then some (key cv, n)
  else if (env.scale cv n).1 = sOk then some (key cv, (env.scale cv n).2) else none

/-- The amount `__input` gives `WithinAllowance` (a hash only for values
    longer than a word, which Integrity excludes). -/
def amountOf (env : Env) : Input → Nat
  | .etherValue => env.value
  | .word n => n
  | _ => 0

/-- A thunk that charges `g sl` (fails on `none`). -/
def chargesT (bal : Bytes → Nat) (g : Slots → Option (List (Bytes × Nat))) : T :=
  fun sl cs => ((g sl).bind (applyL (consumeM bal) cs), sl)

/-- Size `Custom` passes: the layout's inline size, or `AbiLocation.size`. An
    ether value node gets `data.length + 1` (its size reads as overflowing). -/
def customSize (data : Calldata) (e : Nat) (m : Condition) (l : Nat) : Nat :=
  if e = 0 ∨ e = 6 then data.length + 1
  else if m.size ≠ 0 then m.size else size data l m

def writeSlot (sl : Slots) (k : Nat) (v : Input) (l : Nat) : Slots :=
  ⟨fun j => if j = k then v else sl.values j, fun j => if j = k then l else sl.locations j⟩

/-- A thunk that passes or fails on a condition of the slots. -/
def checkT (b : Slots → Bool) : T := fun sl cs => (if b sl then some cs else none, sl)

/-- The element layout of an array: its first child (`AbiLocation` uses
    `children[0]` for every element). -/
def tmpl (m : Condition) : Condition := m.children.headD default

/-- `Empty`. -/
def emptyT (data : Calldata) : T := checkT fun _ => data.length = 0

/-- `_arrayIterator`: every element (`ArrayEvery`) or some element
    (`ArraySome`, each from the same consumptions) passes `kid`. -/
def iterT (data : Calldata) (every : Bool) (e : Nat) (kid : Val' → T) (v : Val') : T :=
  if e ≠ 4 then failT else
  match childrenE data v.2 v.1 with
  | .inr (some locs) =>
    if every then seqT (locs.map fun l => kid (tmpl v.1, l))
    else orT (locs.map fun l => kid (tmpl v.1, l))
  | _ => failT

/-- `_arrayTailMatches`. -/
def tailT (data : Calldata) (e : Nat) (ss : List (Val' → T)) (v : Val') : T :=
  if e ≠ 4 then failT else
  match childrenE data v.2 v.1 with
  | .inr (some locs) =>
    if locs.length < ss.length then failT
    else seqT (List.zipWith (fun s l => s (tmpl v.1, l)) ss (locs.drop (locs.length - ss.length)))
  | _ => failT

/-- `Matches` on an array (tuples and calldata are `sem`'s own). -/
def matchesArrT (data : Calldata) (e : Nat) (cv : List Nat) (ss : List (Val' → T)) (v : Val') : T :=
  if e ≠ 4 then failT else
  match leadingCheck data v.2 (toBytes cv), childrenE data v.2 v.1 with
  | none, .inr (some locs) =>
    if ss.length ≠ locs.length then failT
    else seqT (List.zipWith (fun s l => s (tmpl v.1, l)) ss locs)
  | _, _ => failT

/-- `_slice`: the child at the window. -/
def sliceT (data : Calldata) (e : Nat) (cv : List Nat) (kid : Val' → T) (v : Val') : T :=
  if ¬(e = 1 ∨ e = 2) then failT else
  match cvAt (toBytes cv) 2 with
  | none => failT
  | some sz =>
    if v.1.inlined = false ∧ v.2 + 32 > data.length then failT
    else if shiftOf (toBytes cv) + sz > (if v.1.inlined then v.1.size else load data v.2) then failT
    else kid (winMeta sz, v.2 + (if v.1.inlined then 0 else 32) + shiftOf (toBytes cv))

/-- `_pluck`. -/
def pluckT (env : Env) (data : Calldata) (n e : Nat) (cv : List Nat) (v : Val') : T := fun sl cs =>
  match inputAt data e v.1 v.2, cvAt (toBytes cv) 0 with
  | .overflow, _ => (none, sl)
  | _, none => (none, sl)
  | x, some k =>
    if k ≥ n then (none, sl)
    else (some cs, writeSlot sl k (match x with
      | .etherValue => .word env.value
      | x => x) v.2)

/-- The comparisons. -/
def cmpOk (avatar : Bytes) (env : Env) (data : Calldata) (e o : Nat) (cv : List Nat) (v : Val') :
    Bool :=
  match inputAt data e v.1 v.2 with
  | .overflow => false
  | x => compare (toOp o) (inputB env x) (cmpValue avatar e o cv v.1) = sOk

/-- `BitmaskChecker.check`. -/
def bitmaskOk (data : Calldata) (cv : List Nat) (v : Val') : Bool :=
  bitmaskStatus (bitmaskCheck data v.2 (toBytes cv) v.1.inlined v.1.size []) = sOk

/-- The charges of a custom checker. -/
def customCharges (env : Env) (data : Calldata) (e : Nat) (cv : List Nat) (v : Val') (sl : Slots) :
    Option (List (Bytes × Nat)) :=
  match env.customCall (toBytes cv) v.2 (customSize data e v.1 v.2) sl.values with
  | .inl _ => none
  | .inr chs => some chs

/-- The charge of `WithinAllowance`. -/
def allowanceCharge (env : Env) (data : Calldata) (e : Nat) (cv : List Nat) (v : Val') :
    Option (List (Bytes × Nat)) :=
  match inputAt data e v.1 v.2 with
  | .overflow => none
  | x => (charge env (toBytes cv) (amountOf env x)).map ([·])

/-- Every operator `Normalize.sem` leaves to the world. -/
def extW (avatar : Bytes) (env : Env) (data : Calldata) (n : Nat) (e o : Nat) (cv : List Nat)
    (ss : List (Val' → T)) (v : Val') : T :=
  match o with
  | 4 => emptyT data
  | 5 => matchesArrT data e cv ss v
  | 6 => iterT data false e (ss.headD passK) v
  | 7 => iterT data true e (ss.headD passK) v
  | 8 => tailT data e ss v
  | 13 => sliceT data e cv (ss.headD passK) v
  | 14 => pluckT env data n e cv v
  | 15 | 16 | 17 | 18 | 19 | 20 => checkT fun _ => cmpOk avatar env data e o cv v
  | 21 => checkT fun _ => bitmaskOk data cv v
  | 22 => chargesT env.balance (customCharges env data e cv v)
  | 23 => checkT fun sl => env.ratio (toBytes cv) sl.values = sOk
  | 28 => chargesT env.balance fun _ => allowanceCharge env data e cv v
  | 30 => chargesT env.balance fun _ => (charge env (toBytes cv) 1).map ([·])
  | _ => failT

/-- The contract as a normalization world. -/
def contractWorld (avatar : Bytes) (env : Env) (data : Calldata) (n : Nat) : World Val' Slots CM where
  fields e v := match decodeAt data e v.1 v.2 with
    | some locs => v.1.children.zip locs
    | none => []
  dflt := (default, 0)
  gate e cv v := (leadingCheck data (adjust e v.2) (prefixOf e cv)).isNone &&
    (decodeAt data e v.1 v.2).isSome
  ext := extW avatar env data n

end Bridge
