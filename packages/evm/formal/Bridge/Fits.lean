import Bridge.Ok
import DecoderFaithfulness.Meta

/-!
# Trees whose layout fits a value's

The SDK's trees (`Normalize.Cond`) become the `Condition` the evaluator
sees in two steps: `toRoles` (what `ConditionPacker._transform` and the
unpacker do to compValues and operators, as `ConditionPacking.rawTree`) and
`annotate` (the `inlined`/`size`/`leadingBytes` metadata). `D c` is that
node.

`Fits c d m`: the evaluator, running node `d` of tree `c` (`D c`, or `D c`
with the `size` a `Slice` gives its child), reads calldata as the layout
`m` says: every structural node has `m`'s `inlined` and `size`, containers
list their children as `m` does (a `Matches` on calldata or a dynamic tuple
may leave out trailing ones), and operators that read a whole value
(comparisons, `Custom`, `Pluck`) see exactly `m`'s type. Zips are not
covered.

`Decodable data m l`: decoding the calldata with layout `m` at `l` does not
overflow, all the way down.
-/

namespace Bridge
open DecoderFaithfulness DecoderFaithfulness.Roles Normalize Evaluate

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
  /-- Same type: everything `AbiLocation.size` and `__input` read. -/
  inductive TyEq : Condition → Condition → Prop
    | mk {d m : Condition} : d.encoding = m.encoding → LayEq d m →
        TyEqL d.children m.children → TyEq d m
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

/-- `d` is the node of `c`, up to its `size` (which `_slice` sets on its
    child). -/
def Node (avatar : Bytes) (c : Cond) (d : Condition) : Prop := d = { D avatar c with size := d.size }

section
variable (avatar : Bytes)

/-- A `Pass` type description of (a prefix of) layout `m`: containers list
    the first children of `m` (all of them for an inlined container), arrays
    one element template. -/
inductive PDesc : Cond → Condition → Prop
  | leaf {c m} : c.op = 0 → (c.enc = 1 ∨ c.enc = 2) → c.ch = [] → LayEq (D avatar c) m →
      isInl c = (D avatar c).inlined → PDesc c m
  | tup {c m} : c.op = 0 → (c.enc = 3 ∨ c.enc = 5) → (D avatar c).encoding = m.encoding →
      c.ch.length ≤ m.children.length →
      (∀ i (h : i < c.ch.length), PDesc c.ch[i] (m.children.getD i default)) →
      LayEq (D avatar c) m → isInl c = (D avatar c).inlined → PDesc c m
  | arr {c m x} : c.op = 0 → c.enc = 4 → c.ch = [x] → m.encoding = .Array → PDesc x (tmpl m) →
      LayEq (D avatar c) m → isInl c = (D avatar c).inlined → PDesc c m

inductive Fits : Cond → Condition → Condition → Prop
  | pass {c d m} : c.op = 0 → Node avatar c d → isStruct c = true → LayEq d m → Plain c →
      isInl c = (D avatar c).inlined → (d = D avatar c → PDesc avatar c m) → Fits c d m
  | ns {c d m} : isStruct c = false → NsOk c → d = D avatar c → Fits c d m
  | logical {c d m} : (c.op = 1 ∨ c.op = 2) → c.enc = 0 → isStruct c = true → d = D avatar c →
      LayEq d m → (∀ x ∈ c.ch, Fits x (D avatar x) m) → isInl c = (D avatar c).inlined →
      Fits c d m
  /-- `Matches` on a tuple or calldata: the first children of `m`. -/
  | tup {c d m} : c.op = 5 → (c.enc = 3 ∨ c.enc = 5) → d = D avatar c →
      d.encoding = m.encoding → LayEq d m → d.leadingBytes = m.leadingBytes →
      (∀ x ∈ c.ch, isStruct x = true) → c.ch.length ≤ m.children.length →
      (∀ i (h : i < c.ch.length), Fits c.ch[i] (D avatar c.ch[i]) (m.children.getD i default)) →
      isInl c = (D avatar c).inlined → Fits c d m
  /-- Array operators: every child at the element layout. -/
  | arr {c d m} : (c.op = 5 ∨ c.op = 6 ∨ c.op = 7 ∨ c.op = 8) → c.enc = 4 → d = D avatar c →
      m.encoding = .Array → LayEq d m → c.ch ≠ [] →
      (∀ x ∈ c.ch, isStruct x = true) → (∀ x ∈ c.ch, Fits x (D avatar x) (tmpl m)) →
      isInl c = (D avatar c).inlined → Fits c d m
  /-- `Slice`: the child reads the window. -/
  | slice {c d m x} : c.op = 13 → (c.enc = 1 ∨ c.enc = 2) → Node avatar c d → LayEq d m →
      c.ch = [x] → (∀ sz, Fits x { D avatar x with size := sz } (winMeta sz)) → Plain c →
      isInl c = (D avatar c).inlined → (c.enc = 1 → isInl c = true) → Fits c d m
  | leaf {c d m} : leafOp c.op = true → isStruct c = true → Node avatar c d → TyEq d m →
      c.enc ≠ 5 → (c.op = 16 → isInl c = m.inlined) → Plain c → isInl c = (D avatar c).inlined →
      (∀ i (h : i < c.ch.length), PDesc avatar c.ch[i] (m.children.getD i default)) →
      (c.enc = 4 → c.ch ≠ []) → (c.enc = 1 ∨ c.enc = 2 → c.ch = []) → c.enc ≤ 5 → Fits c d m

/-- `decodeAt` with the encoding taken from the layout. -/
def decodeL (data : Calldata) (m : Condition) (l : Nat) : Option (List Nat) :=
  decodeAt data (if m.encoding = .AbiEncoded then 5 else 3) m l

inductive Decodable (data : Calldata) : Condition → Nat → Prop
  | leaf {m l} : m.encoding ≠ .Tuple → m.encoding ≠ .AbiEncoded → m.encoding ≠ .Array →
      Decodable data m l
  | tup {m l} (locs : List Nat) : (m.encoding = .Tuple ∨ m.encoding = .AbiEncoded) →
      decodeL data m l = some locs →
      (∀ i (hi : i < locs.length), Decodable data (m.children.getD i default) locs[i]) →
      Decodable data m l
  | arr {m l} (locs : List Nat) : m.encoding = .Array → childrenE data l m = .inr (some locs) →
      (∀ l' ∈ locs, Decodable data (tmpl m) l') → Decodable data m l

end

/-- The compValues the evaluator could revert on are well formed: leading
    bytes of at most 32, a `Slice` size byte, a `Pluck` index below the
    number of slots `n`. -/
def CvOk (n : Nat) : Cond → Prop
  | ⟨e, o, cv, ch⟩ =>
    (o = 5 → (prefixOf e cv).length ≤ 32) ∧ (o = 13 → 3 ≤ cv.length) ∧
    (o = 14 → ∃ k ∈ cv.head?, k % 256 < n) ∧ ∀ x ∈ ch, CvOk n x
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
