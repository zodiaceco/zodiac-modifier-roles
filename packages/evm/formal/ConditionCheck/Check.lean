import DecoderFaithfulness

/-!
# A decidable structural check for condition trees

`checkCondition s c` is a function a client (the SDK) can run before storing
`c` with a `...Packed` setter, which skips `Integrity`. `Sound.lean` proves
that every tree it accepts satisfies the hypotheses of the decoder theorems
(`Desc`, `RootOK`, `ZipOK`) for every calldata of the tree's type.

The check computes the ABI type a structural node describes (`Ty`), and
classifies every other node as non-structural (`ns`) or as a Zip (`zip`).
`HasT s u t` says which values have type `t`.

`s` is the strictness flag of the decoder theorems. With `s = false` every
nested-calldata interpretation must hold, so a value has type `call lb ts`
only if it parses as such; variant `And`/`Or` nodes (children that are
different interpretations of one `bytes` value) are rejected. With
`s = true` variants are allowed, and a `bytes` value has every `call` type.
-/

namespace ConditionCheck
open DecoderFaithfulness DecoderFaithfulness.Roles

/-- The ABI type a structural node describes. `call lb ts`: nested calldata
    with `lb` leading bytes and argument types `ts`. -/
inductive Ty where
  | static
  | dynamic
  | tuple (ts : List Ty)
  | array (t : Ty)
  | call (lb : Nat) (ts : List Ty)
  deriving Inhabited

mutual
  def Ty.decEq : (a b : Ty) → Decidable (a = b)
    | .static, .static => isTrue rfl
    | .dynamic, .dynamic => isTrue rfl
    | .tuple as, .tuple bs =>
      match Ty.decEqList as bs with
      | isTrue h => isTrue (h ▸ rfl)
      | isFalse h => isFalse fun e => by cases e; exact h rfl
    | .array a, .array b =>
      match Ty.decEq a b with
      | isTrue h => isTrue (h ▸ rfl)
      | isFalse h => isFalse fun e => by cases e; exact h rfl
    | .call la as, .call lb bs =>
      if hl : la = lb then
        match Ty.decEqList as bs with
        | isTrue h => isTrue (hl ▸ h ▸ rfl)
        | isFalse h => isFalse fun e => by cases e; exact h rfl
      else isFalse fun e => by cases e; exact hl rfl
    | .static, .dynamic | .static, .tuple _ | .static, .array _ | .static, .call _ _
    | .dynamic, .static | .dynamic, .tuple _ | .dynamic, .array _ | .dynamic, .call _ _
    | .tuple _, .static | .tuple _, .dynamic | .tuple _, .array _ | .tuple _, .call _ _
    | .array _, .static | .array _, .dynamic | .array _, .tuple _ | .array _, .call _ _
    | .call _ _, .static | .call _ _, .dynamic | .call _ _, .tuple _ | .call _ _, .array _ =>
      isFalse fun e => by cases e

  def Ty.decEqList : (a b : List Ty) → Decidable (a = b)
    | [], [] => isTrue rfl
    | [], _ :: _ | _ :: _, [] => isFalse fun e => by cases e
    | a :: as, b :: bs =>
      match Ty.decEq a b, Ty.decEqList as bs with
      | isTrue h1, isTrue h2 => isTrue (h1 ▸ h2 ▸ rfl)
      | isFalse h, _ => isFalse fun e => by cases e; exact h rfl
      | _, isFalse h => isFalse fun e => by cases e; exact h rfl
end

instance : DecidableEq Ty := Ty.decEq

mutual
  def Ty.isStatic : Ty → Bool
    | .static => true
    | .tuple ts => Ty.allStatic ts
    | _ => false

  def Ty.allStatic : List Ty → Bool
    | [] => true
    | t :: ts => t.isStatic && Ty.allStatic ts
end

def Ty.isBytesLike : Ty → Bool
  | .dynamic | .call _ _ => true
  | _ => false

mutual
  /-- `u` has type `t`. -/
  def HasT (s : Bool) : Val → Ty → Prop
    | .word w, t => t = .static ∧ w.length = 32
    | .bytes _, t => t = .dynamic ∨ (s = true ∧ ∃ lb ts, t = .call lb ts)
    | .tuple vs, t => ∃ ts, t = .tuple ts ∧ HasTAll s vs ts
    | .array vs, t => ∃ t', t = .array t' ∧ HasTEach s vs t'
    | .call pre args, t => t = .dynamic ∨
        ∃ lb ts, t = .call lb ts ∧ ((pre.length = lb ∧ HasTAll s args ts) ∨ s = true)

  /-- Pointwise. -/
  def HasTAll (s : Bool) : List Val → List Ty → Prop
    | [], [] => True
    | v :: vs, t :: ts => HasT s v t ∧ HasTAll s vs ts
    | _, _ => False

  /-- Every element has type `t`. -/
  def HasTEach (s : Bool) : List Val → Ty → Prop
    | [], _ => True
    | v :: vs, t => HasT s v t ∧ HasTEach s vs t
end

/-- At the root the calldata itself must parse as the root's `call` type
    (there is no outer `bytes` to fall back on). -/
def Strict (s : Bool) (u : Val) : Ty → Prop
  | .call lb ts => ∃ pre args, u = .call pre args ∧ pre.length = lb ∧ HasTAll s args ts
  | _ => True

/-- What a node is. -/
inductive K where
  | ty (t : Ty)
  | ns
  | zip
  deriving DecidableEq, Inhabited

/-- All children structural: their types. -/
def allTy : List K → Option (List Ty)
  | [] => some []
  | .ty t :: ks => (allTy ks).map (t :: ·)
  | _ :: _ => none

/-- The type of the first structural child, if only non-structural children
    come before it (no Zip before the described child, `ZipsAfter`). -/
def firstTy : List K → Option Ty
  | [] => none
  | .ty t :: _ => some t
  | .ns :: ks => firstTy ks
  | .zip :: _ => none

/-- `k` is not structural, or has type `t`. -/
def K.fits (t : Ty) : K → Bool
  | .ty t' => t' == t
  | _ => true

/-- `k` is structural with a bytes-like type. -/
def K.bytesLikeTy : K → Bool
  | .ty t' => t'.isBytesLike
  | _ => false

/-- `k` is not structural, or has a bytes-like type. -/
def K.bytesLikeOk : K → Bool
  | .ty t' => t'.isBytesLike
  | _ => true

/-- Type of an `And`/`Or` with a structural child: all structural children
    have the same type, or (with `s = true`) all are bytes-like
    interpretations of one `bytes` value. -/
def logicalTy (s : Bool) (ks : List K) : Option Ty :=
  match firstTy ks with
  | none => none
  | some t0 =>
    if ks.all (K.fits t0) then some t0
    else if s && ks.all K.bytesLikeOk then some .dynamic
    else none

def logicalKind (s : Bool) (ks : List K) : Option K :=
  if ks.isEmpty then none
  else if ks.all (· == .ns) then some .ns
  else match logicalTy s ks with
    | none => none
    | some t => if ks.contains .zip && t.isStatic then none else some (.ty t)

def leafOk (cs : List Condition) (op : Operator) : Bool := cs.isEmpty && !isNavOp op

def sliceOk (op : Operator) (cs : List Condition) (cv : Bytes) (ks : List K) : Bool :=
  op == .Slice && decide (1 ≤ sliceSize cv) && decide (sliceSize cv ≤ 32) &&
    cs.map (·.encoding) == [.Static] && ks == [.ty .static]

def isArrayOp (op : Operator) : Bool :=
  op == .Matches || op == .ArraySome || op == .ArrayEvery || op == .ArrayTailMatches

/-- One node, given its children's kinds `ks`. -/
def classifyNode (s : Bool) (e : Encoding) (op : Operator) (cs : List Condition) (lb : Nat)
    (cv : Bytes) (ks : List K) : Option K :=
  match e with
  | .Static => if leafOk cs op || sliceOk op cs cv ks then some (.ty .static) else none
  | .Dynamic => if leafOk cs op || sliceOk op cs cv ks then some (.ty .dynamic) else none
  | .Tuple =>
    if !cs.isEmpty && (!isNavOp op || op == .Matches) then
      (allTy ks).map fun ts => .ty (.tuple ts)
    else none
  | .Array =>
    if !isNavOp op || isArrayOp op then
      match ks with
      | .ty t :: rest =>
        if rest.all (· == .ty t) then some (.ty (.array t))
        -- variant array (`s = true`): children are bytes-like interpretations
        else if s && ks.all K.bytesLikeTy then some (.ty (.array .dynamic))
        else none
      | _ => none
    else none
  | .AbiEncoded =>
    if !cs.isEmpty && (op == .Matches || op == .Pass) then
      (allTy ks).map fun ts => .ty (.call lb ts)
    else none
  | .None =>
    if op == .ZipSome || op == .ZipEvery then
      match ks with
      | [.ty (.tuple _)] => some .zip
      | _ => none
    else if leafOk cs op then some .ns
    else if op == .And || op == .Or then logicalKind s ks
    else none
  | .EtherValue => if leafOk cs op then some .ns else none

mutual
  /-- `none`: rejected. -/
  def classify (s : Bool) : Condition → Option K
    | ⟨e, op, cs, _, _, lb, cv⟩ => (classifyAll s cs).bind (classifyNode s e op cs lb cv)

  def classifyAll (s : Bool) : List Condition → Option (List K)
    | [] => some []
    | c :: cs => (classify s c).bind fun k => (classifyAll s cs).map (k :: ·)
end

mutual
  /-- The root is `AbiEncoded`, or an `And`/`Or` over such roots,
      non-structural nodes and Zips. -/
  def rootOk (s : Bool) : Condition → Bool
    | ⟨e, op, cs, _, _, _, _⟩ =>
      e == .AbiEncoded || (e == .None && (op == .And || op == .Or) && rootOkAll s cs)

  def rootOkAll (s : Bool) : List Condition → Bool
    | [] => true
    | c :: cs => (rootOk s c || classify s c == some .ns || classify s c == some .zip) &&
        rootOkAll s cs
end

/-- Every value of type `t1` has type `t2` (`hasT_compat`): equal types, a
    `dynamic` field over bytes-like elements, or (`s = true`) any two
    bytes-like types, as Integrity's `_isTypeCompatible`. -/
def tyCompat (s : Bool) (t1 t2 : Ty) : Bool :=
  t1 == t2 || (t2 == .dynamic && t1.isBytesLike) || (s && t1.isBytesLike && t2.isBytesLike)

/-- Every Pluck node that field `f` of Zip `z` may read (same slot index) is
    an `Array` whose element template has the field's type. -/
def zipFieldOk (s : Bool) (all : List Condition) (z : Condition) (f : Nat) : Bool :=
  all.all fun pk =>
    !(pk.operator == .Pluck && cvByte pk.compValue 0 == cvByte z.compValue f) ||
      (pk.encoding == .Array &&
        match classify s (pk.children.headD default), classify s ((zipFields z).getD f default) with
        | some (.ty t1), some (.ty t2) => tyCompat s t1 t2
        | _, _ => false)

def zipCheck (s : Bool) (root : Condition) : Bool :=
  (Example.nodes root).all fun z =>
    !(z.operator == .ZipSome || z.operator == .ZipEvery) ||
      (List.range (zipFields z).length).all (zipFieldOk s (Example.nodes root) z)

/-- The type of the calldata `root` describes, if the check passes. -/
def checkCondition (s : Bool) (root : Condition) : Option Ty :=
  match classify s root with
  | some (.ty t) => if rootOk s root && zipCheck s root then some t else none
  | _ => none

end ConditionCheck
