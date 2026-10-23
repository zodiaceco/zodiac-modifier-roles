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
    with `lb` leading bytes and argument types `ts`. An *open* tuple or call
    type (`o = true`, a `Matches` node) types the first fields only: the
    value may have more (only if the fields typed are not all static, else
    the tuple is inlined and its length fixed). -/
inductive Ty where
  | static
  | dynamic
  | tuple (ts : List Ty) (o : Bool)
  | array (t : Ty)
  | call (lb : Nat) (ts : List Ty) (o : Bool)
  deriving Inhabited, Repr

mutual
  def Ty.decEq : (a b : Ty) → Decidable (a = b)
    | .static, .static => isTrue rfl
    | .dynamic, .dynamic => isTrue rfl
    | .tuple as oa, .tuple bs ob =>
      if ho : oa = ob then
        match Ty.decEqList as bs with
        | isTrue h => isTrue (ho ▸ h ▸ rfl)
        | isFalse h => isFalse fun e => by cases e; exact h rfl
      else isFalse fun e => by cases e; exact ho rfl
    | .array a, .array b =>
      match Ty.decEq a b with
      | isTrue h => isTrue (h ▸ rfl)
      | isFalse h => isFalse fun e => by cases e; exact h rfl
    | .call la as oa, .call lb bs ob =>
      if hl : la = lb ∧ oa = ob then
        match Ty.decEqList as bs with
        | isTrue h => isTrue (hl.1 ▸ hl.2 ▸ h ▸ rfl)
        | isFalse h => isFalse fun e => by cases e; exact h rfl
      else isFalse fun e => by cases e; exact hl ⟨rfl, rfl⟩
    | .static, .dynamic | .static, .tuple _ _ | .static, .array _ | .static, .call _ _ _
    | .dynamic, .static | .dynamic, .tuple _ _ | .dynamic, .array _ | .dynamic, .call _ _ _
    | .tuple _ _, .static | .tuple _ _, .dynamic | .tuple _ _, .array _ | .tuple _ _, .call _ _ _
    | .array _, .static | .array _, .dynamic | .array _, .tuple _ _ | .array _, .call _ _ _
    | .call _ _ _, .static | .call _ _ _, .dynamic | .call _ _ _, .tuple _ _
    | .call _ _ _, .array _ =>
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
    | .tuple ts _ => Ty.allStatic ts
    | _ => false

  def Ty.allStatic : List Ty → Bool
    | [] => true
    | t :: ts => t.isStatic && Ty.allStatic ts
end

def Ty.isBytesLike : Ty → Bool
  | .dynamic | .call _ _ _ => true
  | _ => false

mutual
  /-- `u` has type `t`. -/
  def HasT (s : Bool) : Val → Ty → Prop
    | .word w, t => t = .static ∧ w.length = 32
    | .bytes _, t => t = .dynamic ∨ (s = true ∧ ∃ lb ts o, t = .call lb ts o)
    | .tuple vs, t => ∃ ts o, t = .tuple ts o ∧
        (if o then HasTPre s vs ts ∧ (ts.length < vs.length → Ty.allStatic ts = false)
         else HasTAll s vs ts)
    | .array vs, t => ∃ t', t = .array t' ∧ HasTEach s vs t'
    | .call pre args, t => t = .dynamic ∨
        ∃ lb ts o, t = .call lb ts o ∧
          ((pre.length = lb ∧ (if o then HasTPre s args ts else HasTAll s args ts)) ∨ s = true)

  /-- Pointwise. -/
  def HasTAll (s : Bool) : List Val → List Ty → Prop
    | [], [] => True
    | v :: vs, t :: ts => HasT s v t ∧ HasTAll s vs ts
    | _, _ => False

  /-- Pointwise on the first `ts.length` values (there may be more). -/
  def HasTPre (s : Bool) : List Val → List Ty → Prop
    | _, [] => True
    | v :: vs, t :: ts => HasT s v t ∧ HasTPre s vs ts
    | [], _ :: _ => False

  /-- Every element has type `t`. -/
  def HasTEach (s : Bool) : List Val → Ty → Prop
    | [], _ => True
    | v :: vs, t => HasT s v t ∧ HasTEach s vs t
end

/-- At the root the calldata itself must parse as the root's `call` type
    (there is no outer `bytes` to fall back on). -/
def Strict (s : Bool) (u : Val) : Ty → Prop
  | .call lb ts o => ∃ pre args, u = .call pre args ∧ pre.length = lb ∧
      (if o then HasTPre s args ts else HasTAll s args ts)
  | _ => True

mutual
  /-- `sub s t1 t2`: every value of type `t1` has type `t2` (`hasT_sub`).
      Equal types; a bytes-like type and `dynamic`; with `s = true` any two
      bytes-like types; and the prefix order of open tuple and call types:
      an open type of fewer fields contains the longer and the closed ones
      (as long as it is not static where the longer has more fields). -/
  def Ty.sub (s : Bool) : Ty → Ty → Bool
    | .static, .static => true
    | .dynamic, .dynamic => true
    | .tuple ts1 o1, .tuple ts2 o2 =>
      if o2 then
        decide (ts2.length ≤ ts1.length) && Ty.subPre s ts1 ts2 &&
          (!(decide (ts2.length < ts1.length) || o1) || !Ty.allStatic ts2)
      else !o1 && decide (ts1.length = ts2.length) && Ty.subPre s ts1 ts2
    | .array a, .array b => decide (a = b) || Ty.sub s a b
    | .call lb1 ts1 o1, .call lb2 ts2 o2 =>
      (decide (lb1 = lb2) &&
        (if o2 then decide (ts2.length ≤ ts1.length) && Ty.subPre s ts1 ts2
         else !o1 && decide (ts1.length = ts2.length) && Ty.subPre s ts1 ts2)) || s
    | .call _ _ _, .dynamic => true
    | .dynamic, .call _ _ _ => s
    | _, _ => false

  /-- Pointwise `sub` on the first `ts2.length` types. -/
  def Ty.subPre (s : Bool) : List Ty → List Ty → Bool
    | _, [] => true
    | t1 :: ts1, t2 :: ts2 => (decide (t1 = t2) || Ty.sub s t1 t2) && Ty.subPre s ts1 ts2
    | [], _ :: _ => false
end

/-- `t1` is `t2` or a subtype of it: every value of type `t1` has type `t2`. -/
def Ty.le (s : Bool) (t1 t2 : Ty) : Bool := decide (t1 = t2) || Ty.sub s t1 t2

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

/-- `k` is not structural, or a supertype of `t`. -/
def K.fits (s : Bool) (t : Ty) : K → Bool
  | .ty t' => Ty.le s t t'
  | _ => true

/-- `k` is structural with a bytes-like type. -/
def K.bytesLikeTy : K → Bool
  | .ty t' => t'.isBytesLike
  | _ => false

/-- `k` is not structural, or has a bytes-like type. -/
def K.bytesLikeOk : K → Bool
  | .ty t' => t'.isBytesLike
  | _ => true

/-- The structural types among `ks`. -/
def tysOf : List K → List Ty
  | [] => []
  | .ty t :: ks => t :: tysOf ks
  | _ :: ks => tysOf ks

/-- A type among `ts` that is a subtype of all of them: what all the checks
    of one value have in common (the most specific one). -/
def meetOf (s : Bool) (ks : List K) : Option Ty :=
  (tysOf ks).find? fun t => ks.all (K.fits s t)

/-- Type of an `And`/`Or` with a structural child: a structural child's type
    that all others contain (checks of a prefix of one tuple or call), or
    (with `s = true`) all are bytes-like interpretations of one `bytes`
    value. -/
def logicalTy (s : Bool) (ks : List K) : Option Ty :=
  match firstTy ks with
  | none => none
  | some _ =>
    match meetOf s ks with
    | some t => some t
    | none => if s && ks.all K.bytesLikeOk then some .dynamic else none

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

/-- One node, given its children's kinds `ks`. A container that reads its
    whole value (`EqualTo` on a tuple, ...) has a type description below it,
    no navigating node (`noNavAll`). -/
def classifyNode (s : Bool) (e : Encoding) (op : Operator) (cs : List Condition) (lb : Nat)
    (cv : Bytes) (ks : List K) : Option K :=
  match e with
  | .Static => if leafOk cs op || sliceOk op cs cv ks then some (.ty .static) else none
  | .Dynamic => if leafOk cs op || sliceOk op cs cv ks then some (.ty .dynamic) else none
  | .Tuple =>
    if !cs.isEmpty && ((!isNavOp op && noNavAll cs) || op == .Matches) then
      (allTy ks).map fun ts => .ty (.tuple ts (op == .Matches))
    else none
  | .Array =>
    if (!isNavOp op && noNavAll cs) || isArrayOp op then
      match ks with
      | .ty t :: rest =>
        -- the template `children[0]` reads every element: the most specific
        if rest.all (fun k => k != .ns && k != .zip && K.fits s t k) then some (.ty (.array t))
        -- variant array (`s = true`): children are bytes-like interpretations
        else if s && ks.all K.bytesLikeTy then some (.ty (.array .dynamic)) else none
      | _ => none
    else none
  | .AbiEncoded =>
    if !cs.isEmpty && (op == .Matches || (op == .Pass && noNavAll cs)) then
      (allTy ks).map fun ts => .ty (.call lb ts (op == .Matches))
    else none
  | .None =>
    if op == .ZipSome || op == .ZipEvery then
      match ks with
      | [.ty (.tuple _ _)] => some .zip
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

/-- Every value of type `t1` has type `t2` (`hasT_compat`): `Ty.le`. -/
def tyCompat (s : Bool) (t1 t2 : Ty) : Bool := Ty.le s t1 t2

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
