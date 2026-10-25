import Evaluate.Model
import Normalize.Sound
import ConditionPacking.Model

/-!
# Shared definitions for the calldata proofs

Consumptions as a map (`CM`, charges commute: `consumeM_comm`), the thunk
helpers, and the SDK trees as the evaluator sees them: `D avatar c` is the
node `ConditionPacker`/`ConditionUnpacker` hand `evaluate` for tree `c`.
`TyEq`: two nodes are read as the same type by `AbiLocation.size` and
`__input`. `TD`: a type description (the children of a check on a whole
value).
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


/-- SDK compValue bytes. -/
def toBytes (cv : List Nat) : Bytes := cv.map fun n => ⟨n % 256, Nat.mod_lt _ (by decide)⟩

abbrev T := Thunk Slots CM

def failT : T := fun sl _ => (none, sl)

/-- `evaluate` moves the location of nested calldata past its length word. -/
def adjust (e : Nat) (l : Nat) : Nat := if l > 0 ∧ e = 5 then l + 32 else l

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

def writeSlot (sl : Slots) (k : Nat) (v : Input) (l : Nat) : Slots :=
  ⟨fun j => if j = k then v else sl.values j, fun j => if j = k then l else sl.locations j⟩

/-- A thunk that passes or fails on a condition of the slots. -/
def checkT (b : Slots → Bool) : T := fun sl cs => (if b sl then some cs else none, sl)

/-- The element layout of an array: its first child (`AbiLocation` uses
    `children[0]` for every element). -/
def tmpl (m : Condition) : Condition := m.children.headD default

/-- `Empty`. -/
def emptyT (data : Calldata) : T := checkT fun _ => data.length = 0

/-! ## SDK trees as the evaluator sees them -/

def encN (e : Nat) : Encoding := (ConditionPacking.encOf? e).getD .None
def opN (o : Nat) : Operator := if o = 15 then .EqualTo else (ConditionPacking.opOf? o).getD .Pass

/-- The compValue `_transform` and the unpacker leave: calldata gets `0x0004`
    when it has none and its 2-byte count is split off into
    `leadingBytes`; an `EqualTo` on a node that is not inlined loses its
    first word; `EqualToAvatar` compares against the avatar. -/
def cvOf (avatar : Bytes) (c : Cond) : Bytes :=
  if c.op = 15 then avatar
  else if c.enc = 5 then (if c.cv = [] then [0, 4] else toBytes c.cv).drop 2
  else if c.op = 16 ∧ isInl c = false then (toBytes c.cv).drop 32
  else toBytes c.cv

def lbOf (c : Cond) : Nat :=
  if c.enc = 5 then wordVal ((if c.cv = [] then [0, 4] else toBytes c.cv).take 2) else 0

mutual
  /-- The tree before `annotate` (as `ConditionPacking.rawTree` builds it). -/
  def toRoles (avatar : Bytes) : Cond → Condition
    | c@⟨e, o, _, ch⟩ => ⟨encN e, opN o, toRolesL avatar ch, false, 0, lbOf c, cvOf avatar c⟩
  def toRolesL (avatar : Bytes) : List Cond → List Condition
    | [] => []
    | x :: xs => toRoles avatar x :: toRolesL avatar xs
end

theorem toRolesL_eq (avatar : Bytes) (l : List Cond) : toRolesL avatar l = l.map (toRoles avatar) := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp [toRolesL, ih]

/-- The node the evaluator runs for `c`. -/
def D (avatar : Bytes) (c : Cond) : Condition := annotate (toRoles avatar c)

/-! ## Layouts -/

/-- `inlined` and `size`: all a parent's `AbiLocation.children` reads of a
    child. -/
def LayEq (d m : Condition) : Prop := d.inlined = m.inlined ∧ d.size = m.size

mutual
  /-- Same type: everything `AbiLocation.size` and `__input` read. They read
      no children of a word, `bytes` or nested calldata. -/
  inductive TyEq : Condition → Condition → Prop
    | mk {d m : Condition} : d.encoding = m.encoding → LayEq d m →
        (d.encoding ≠ .Static → d.encoding ≠ .Dynamic → d.encoding ≠ .AbiEncoded →
          TyEqL d.children m.children) → TyEq d m
  inductive TyEqL : List Condition → List Condition → Prop
    | nil : TyEqL [] []
    | cons {a b as bs} : TyEq a b → TyEqL as bs → TyEqL (a :: as) (b :: bs)
end

/-- The element layout of an array layout. -/
abbrev tmplOf (m : Condition) : Condition := tmpl m

/-- Operators of structural leaves (they read their own value). -/
def leafOp (o : Nat) : Bool :=
  o == 14 || (15 ≤ o && o ≤ 23) || o == 28 || o == 30

/-- Operators of non-structural leaves (ether value, or no calldata). -/
def nsOp (o : Nat) : Bool :=
  o == 0 || o == 4 || o == 14 || (15 ≤ o && o ≤ 20) || o == 22 || o == 23 || o == 28 || o == 30

/-- Non-structural subtrees that read no calldata location. -/
inductive NsOk : Cond → Prop
  | leaf {c : Cond} : (c.enc = 0 ∨ c.enc = 6) → c.ch = [] → nsOp c.op = true → NsOk c
  | logical {c : Cond} : (c.op = 1 ∨ c.op = 2) → c.enc = 0 → (∀ x ∈ c.ch, NsOk x) → NsOk c

/-- Nodes `normalize` leaves as they are: no `And`, `Or` or `Matches`, and
    arrays with at most one child (type descriptions, leaf checks, `Slice`
    windows). -/
inductive Plain : Cond → Prop
  | mk {c : Cond} : c.op ≠ 1 → c.op ≠ 2 → c.op ≠ 5 → (c.enc = 4 → c.ch.length ≤ 1) →
      (∀ x ∈ c.ch, Plain x) → Plain c

/-- `P` holds of every node. -/
inductive AllN (P : Cond → Prop) : Cond → Prop
  | mk {c : Cond} : P c → (∀ x ∈ c.ch, AllN P x) → AllN P c

/-- Encodings of a `Slice` window's nodes: a word, or no calldata. -/
def winEnc (c : Cond) : Prop := c.enc = 0 ∨ c.enc = 1 ∨ c.enc = 6

/-- The navigating operators (`isNavOp`), by SDK code. -/
def navOp (o : Nat) : Bool :=
  o == 1 || o == 2 || o == 5 || o == 6 || o == 7 || o == 8 || o == 10 || o == 11 || o == 13

/-- A type description, as the children of a check that reads its whole
    value are (the SDK check's `exactTy`): `AbiLocation.size` reads them
    through their encodings and sizes. Nodes that do not navigate, nested
    calldata (read as `bytes`, whatever sits below) and a `Slice` (a word or
    `bytes`; its window is a word). -/
inductive TD : Cond → Prop
  | abi {c : Cond} : c.enc = 5 → c.op ≠ 1 → c.op ≠ 2 → TD c
  | slice {c w : Cond} : c.op = 13 → (c.enc = 1 ∨ c.enc = 2) → c.ch = [w] →
      (c.enc = 1 → AllN winEnc w) → TD c
  | node {c : Cond} : navOp c.op = false → (c.enc = 1 ∨ c.enc = 2 ∨ c.enc = 3 ∨ c.enc = 4) →
      (∀ x ∈ c.ch, TD x) → TD c

/-- `d` is the node of `c`, up to its `size` (which `_slice` sets on its
    child). -/
def Node (avatar : Bytes) (c : Cond) (d : Condition) : Prop := d = { D avatar c with size := d.size }

/-- The slots the Pluck nodes of a subtree write. -/
def plucks : Cond → List Nat
  | ⟨_, o, cv, ch⟩ => (if o = 14 then [cv.headD 0 % 256] else []) ++ (ch.attach.flatMap fun ⟨x, _⟩ => plucks x)
termination_by c => sizeOf c
decreasing_by
  simp_wf
  have := List.sizeOf_lt_of_mem ‹_ ∈ ch›
  omega

/-- The subtree has a Zip. -/
def hasZip : Cond → Bool
  | ⟨_, o, _, ch⟩ => o == 10 || o == 11 || ch.attach.any fun ⟨x, _⟩ => hasZip x
termination_by c => sizeOf c
decreasing_by
  simp_wf
  have := List.sizeOf_lt_of_mem ‹_ ∈ ch›
  omega


/-- The contract's consumption list as a map (the first entry of a key; the
    contract never adds a second one). -/
def toMap (cons : List Consumption) : CM :=
  fun k => (cons.find? (·.key = k)).map fun e => (e.balance, e.consumed)

/-- How the contract's result corresponds to the world's: the same slots, and
    passing with the same consumptions (as a map), or failing without a
    revert. -/
def Rel (r : Res) (x : Option CM × Slots) : Prop :=
  r.slots = x.2 ∧ (if r.status = sOk then x.1 = some (toMap r.cons) else r.status ≠ revert ∧ x.1 = none)


end Bridge
