import ConditionCheck.Check
import ConditionPacking.Model
/-!
# The SDK's `normalizeCondition`, transcribed

A transcription of `packages/sdk/src/main/condition/normalize` (and the
helpers it uses from `typeTree.ts` and `conditionId.ts`). Conditions are the
SDK's nested trees: `enc` (`paramType`), `op` (`operator`), `cv` (`compValue`
bytes; absent = empty) and `ch` (`children`; absent = empty).

Where the TypeScript throws (an invariant, a missing type tree), the
transcription returns its input unchanged; the differential test skips inputs
on which the TypeScript throws.

Codes: encodings None 0, Static 1, Dynamic 2, Tuple 3, Array 4, AbiEncoded 5,
EtherValue 6; operators Pass 0, And 1, Or 2, Matches 5, ArraySome 6,
ZipSome 10, Pluck 14, Custom 22, WithinAllowance 28, CallWithinAllowance 30.
-/

namespace Normalize

structure Cond where
  enc : Nat
  op : Nat
  cv : List Nat
  ch : List Cond
  deriving Inhabited

mutual
  def Cond.decEq : (a b : Cond) → Decidable (a = b)
    | ⟨e1, o1, v1, c1⟩, ⟨e2, o2, v2, c2⟩ =>
      if h : e1 = e2 ∧ o1 = o2 ∧ v1 = v2 then
        match Cond.decEqList c1 c2 with
        | isTrue hc => isTrue (by obtain ⟨rfl, rfl, rfl⟩ := h; rw [hc])
        | isFalse hc => isFalse fun e => by cases e; exact hc rfl
      else isFalse fun e => by cases e; exact h ⟨rfl, rfl, rfl⟩

  def Cond.decEqList : (a b : List Cond) → Decidable (a = b)
    | [], [] => isTrue rfl
    | [], _ :: _ | _ :: _, [] => isFalse fun e => by cases e
    | a :: as, b :: bs =>
      match Cond.decEq a b, Cond.decEqList as bs with
      | isTrue h1, isTrue h2 => isTrue (h1 ▸ h2 ▸ rfl)
      | isFalse h, _ => isFalse fun e => by cases e; exact h rfl
      | _, isFalse h => isFalse fun e => by cases e; exact h rfl
end

instance : DecidableEq Cond := Cond.decEq

theorem ite_pos' {α} {c : Prop} [Decidable c] (h : c) (a b : α) : (if c then a else b) = a := by
  simp [h]
theorem ite_neg' {α} {c : Prop} [Decidable c] (h : ¬c) (a b : α) : (if c then a else b) = b := by
  simp [h]

theorem sizeOf_lt_of_mem {x c : Cond} (h : x ∈ c.ch) : sizeOf x < sizeOf c := by
  rcases c with ⟨e, o, v, ch⟩
  simp only at h
  have := List.sizeOf_lt_of_mem h
  simp only [Cond.mk.sizeOf_spec]
  omega

/-! ## Node kinds (`typeTree.ts`, `effects.ts`) -/

def isPass (c : Cond) : Bool := c.op == 0
def isLogical (c : Cond) : Bool := c.op == 1 || c.op == 2
def isComplex (c : Cond) : Bool := c.enc == 3 || c.enc == 4 || c.enc == 5

mutual
  /-- `isStructural`: the node reads a parameter (the contract's `TypeTree`). -/
  def isStruct : Cond → Bool
    | ⟨e, o, _, ch⟩ => if o == 1 || o == 2 then isStructL ch else !(e == 0 || e == 6)
  def isStructL : List Cond → Bool
    | [] => false
    | x :: xs => isStruct x || isStructL xs
end

mutual
  /-- `writesSlots`: the subtree has a `Pluck`. -/
  def writes : Cond → Bool
    | ⟨_, o, _, ch⟩ => o == 14 || writesL ch
  def writesL : List Cond → Bool
    | [] => false
    | x :: xs => writes x || writesL xs
end

mutual
  /-- `charges`: the subtree has an operator that can charge an allowance. -/
  def charges : Cond → Bool
    | ⟨_, o, _, ch⟩ => o == 22 || o == 28 || o == 30 || chargesL ch
  def chargesL : List Cond → Bool
    | [] => false
    | x :: xs => charges x || chargesL xs
end

mutual
  /-- `choosesCharge`: a choice node (`Or`, `ArraySome`, `ZipSome`) over charging branches. -/
  def chooses : Cond → Bool
    | ⟨e, o, v, ch⟩ => ((o == 2 || o == 6 || o == 10) && charges ⟨e, o, v, ch⟩) || choosesL ch
  def choosesL : List Cond → Bool
    | [] => false
    | x :: xs => chooses x || choosesL xs
end

theorem isStructL_eq (l : List Cond) : isStructL l = l.any isStruct := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp [isStructL, ih]
theorem writesL_eq (l : List Cond) : writesL l = l.any writes := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp [writesL, ih]
theorem chargesL_eq (l : List Cond) : chargesL l = l.any charges := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp [chargesL, ih]
theorem choosesL_eq (l : List Cond) : choosesL l = l.any chooses := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp [choosesL, ih]

theorem isStruct_mk (e o v ch) :
    isStruct ⟨e, o, v, ch⟩ = if o == 1 || o == 2 then ch.any isStruct else !(e == 0 || e == 6) := by
  rw [isStruct, isStructL_eq]
theorem writes_mk (e o v ch) : writes ⟨e, o, v, ch⟩ = (o == 14 || ch.any writes) := by
  rw [writes, writesL_eq]
theorem charges_mk (e o v ch) :
    charges ⟨e, o, v, ch⟩ = (o == 22 || o == 28 || o == 30 || ch.any charges) := by
  rw [charges, chargesL_eq]
theorem chooses_mk (e o v ch) :
    chooses ⟨e, o, v, ch⟩ =
      (((o == 2 || o == 6 || o == 10) && charges ⟨e, o, v, ch⟩) || ch.any chooses) := by
  rw [chooses, choosesL_eq]

theorem isStruct_eq (c : Cond) :
    isStruct c = if c.op == 1 || c.op == 2 then c.ch.any isStruct else !(c.enc == 0 || c.enc == 6) := by
  rcases c; exact isStruct_mk ..
theorem writes_eq (c : Cond) : writes c = (c.op == 14 || c.ch.any writes) := by
  rcases c; exact writes_mk ..
theorem charges_eq (c : Cond) :
    charges c = (c.op == 22 || c.op == 28 || c.op == 30 || c.ch.any charges) := by
  rcases c; exact charges_mk ..
theorem chooses_eq (c : Cond) :
    chooses c = (((c.op == 2 || c.op == 6 || c.op == 10) && charges c) || c.ch.any chooses) := by
  rcases c; exact chooses_mk ..

def canReorderAnd (cs : List Cond) : Bool :=
  !cs.any writes && ((cs.filter charges).length ≤ 1 || !cs.any chooses)

def canReorderOr (cs : List Cond) : Bool :=
  !cs.any fun c => writes c || charges c

mutual
  /-- `isInlined` (the contract's `Topology.isInlined`): no `Dynamic`,
      `Array` or `AbiEncoded` encoding in the subtree. -/
  def isInl : Cond → Bool
    | ⟨e, _, _, ch⟩ => !(e == 2 || e == 4 || e == 5) && isInlL ch
  def isInlL : List Cond → Bool
    | [] => true
    | x :: xs => isInl x && isInlL xs
end

/-! ## `flattenNestedBranches`, `dedupeChildren`, `unwrapSingleChild` -/

def flattenCh (op : Nat) (cs : List Cond) : List Cond :=
  cs.flatMap fun x => if x.op == op then x.ch else [x]

def flatten (c : Cond) : Cond :=
  if isLogical c then { c with ch := flattenCh c.op c.ch } else c

def dedupeL (isAnd : Bool) : List Cond → List Cond → List Cond
  | _, [] => []
  | seen, x :: xs =>
    if seen.contains x then
      if isAnd && charges x then x :: dedupeL isAnd seen xs else dedupeL isAnd seen xs
    else x :: dedupeL isAnd (x :: seen) xs

def dedupe (c : Cond) : Cond :=
  if isLogical c && !c.ch.any writes then { c with ch := dedupeL (c.op == 1) [] c.ch } else c

def unwrap (c : Cond) : Cond :=
  if isLogical c then
    match c.ch with
    | [x] => x
    | _ => c
  else c

/-! ## `pushDownOr` -/

/-- The merged `Or` at the hinge: `{ paramType: None, operator: Or, children }`. -/
def orNode (hs : List Cond) : Cond := ⟨0, 2, [], hs⟩

/-- `l.map((y, i) => i === h ? x : y)` -/
def replaceAt (l : List Cond) (h : Nat) (x : Cond) : List Cond :=
  if h < l.length then l.take h ++ x :: l.drop (h + 1) else l

mutual
  /-- An SDK condition as the raw tree the SDK check classifies (`nodeOf`
      in checkStored.ts), or `none` for an unknown code. -/
  def toCheck : Cond → Option DecoderFaithfulness.Roles.Condition
    | ⟨e, o, cv, ch⟩ =>
      match ConditionPacking.encOf? e, ConditionPacking.opOf? o, toCheckL ch with
      | some en, some op, some cs =>
        let bs : DecoderFaithfulness.Bytes := cv.map fun n => ⟨n % 256, Nat.mod_lt _ (by decide)⟩
        some ⟨en, op, cs, false, 0,
          if e = 5 then (if cv = [] then 4 else DecoderFaithfulness.wordVal (bs.take 2)) else 0,
          if e = 5 then bs.drop 2 else bs⟩
      | _, _, _ => none
  def toCheckL : List Cond → Option (List DecoderFaithfulness.Roles.Condition)
    | [] => some []
    | x :: xs => match toCheck x, toCheckL xs with
      | some c, some cs => some (c :: cs)
      | _, _ => none
end

/-- `compatibleSiblings` in `effects.ts` (`siblingsCompatible` in
    checkStored.ts): the SDK check accepts these as the children of one
    `And`/`Or` (`logicalTy`, strict flag `s = true`). The merged `Or` of
    `pushDownOr` must be such a node. -/
def sameType (hs : List Cond) : Bool :=
  match toCheckL hs with
  | some cs => match ConditionCheck.classifyAll true cs with
    | some ks => (ConditionCheck.logicalTy true ks).isSome
    | none => false
  | none => false

/-- `findMatchesHingeIndex` (with the equal-length rule). -/
def hingeM (first : Cond) (chs : List Cond) : Option Nat :=
  if first.ch.isEmpty || chs.any (·.ch.isEmpty) then none else
  if !chs.all (·.ch.length == first.ch.length) then none else
  match (List.range first.ch.length).filter
      (fun i => chs.any fun o => o.ch[i]! != first.ch[i]!) with
  | [i] => some i
  | _ => none

def mergeMatches (first : Cond) (chs : List Cond) : Option (List Cond) :=
  if !(first.enc == 3 || first.enc == 5) then none else
  if !chs.all (·.cv == first.cv) then none else
  if chs.any writes then none else
  match hingeM first chs with
  | none => none
  | some h =>
    if !(chs.map (·.ch[h]!)).all (fun x => isStruct x == isStruct (chs.map (·.ch[h]!)).head!) then none
    else if !sameType (chs.map (·.ch[h]!)) then none
    else if (chs.map (·.ch[h]!)).any charges then none
    else some (replaceAt first.ch h (orNode (chs.map (·.ch[h]!))))

/-- `commonChildrenIds`: in the first branch and every other one. -/
def common (chs : List Cond) (x : Cond) : Bool :=
  chs.head!.ch.contains x && chs.tail.all (·.ch.contains x)

/-- A branch's hinge: the position of its one child not in every branch. -/
def hingeOf (chs : List Cond) (o : Cond) : Nat :=
  o.ch.idxOf (o.ch.filter fun x => !common chs x).head!

/-- `findAndHingeIndices` succeeds: one unique child per branch, and the
    other children agree as multisets. -/
def hingeOk (chs : List Cond) : Bool :=
  chs.all (fun o => (o.ch.filter fun x => !common chs x).length == 1) &&
  chs.all fun o => (o.ch.eraseIdx (hingeOf chs o)).isPerm
    (chs.head!.ch.eraseIdx (hingeOf chs chs.head!))

def mergeAnd (first : Cond) (chs : List Cond) : Option (List Cond) :=
  if chs.any writes then none else
  if !chs.all (fun x => canReorderAnd x.ch) then none else
  if !hingeOk chs then none else
  if (chs.map fun o => o.ch[hingeOf chs o]!).any charges then none
  else if !sameType (chs.map fun o => o.ch[hingeOf chs o]!) then none
  else some (replaceAt first.ch (hingeOf chs first) (orNode (chs.map fun o => o.ch[hingeOf chs o]!)))

/-- The merged node, if the `Or` can be pushed down. -/
def pushStep (c : Cond) : Option Cond :=
  if c.op == 2 && 2 ≤ c.ch.length && c.ch.all (·.enc == c.ch.head!.enc) && !c.ch.any (·.enc == 4)
  then
    if c.ch.all (·.op == 5) then
      (mergeMatches c.ch.head! c.ch).map fun nch => { c.ch.head! with ch := nch }
    else if c.ch.all (·.op == 1) then
      (mergeAnd c.ch.head! c.ch).map fun nch => { c.ch.head! with ch := nch }
    else none
  else none

def pushDownOr (f : Cond → Cond) (c : Cond) : Cond :=
  match pushStep c with
  | some n => f n
  | none => c

/-! ## `sortBranchesCanonical`

The order: shorter `conditionId` first, then by its bytes. -/

mutual
  def nodeCount : Cond → Nat
    | ⟨_, _, _, ch⟩ => 1 + nodeCountL ch
  def nodeCountL : List Cond → Nat
    | [] => 0
    | x :: xs => nodeCount x + nodeCountL xs
end

/-- `flattenCondition`: breadth first, with parent indices. -/
def bfsGo : Nat → List (Cond × Nat) → Array (Nat × Cond) → Array (Nat × Cond)
  | 0, _, acc => acc
  | _, [], acc => acc
  | n + 1, (c, p) :: q, acc => bfsGo n (q ++ c.ch.map (·, acc.size)) (acc.push (p, c))

def hexDigit (n : Nat) : Char :=
  if n < 10 then Char.ofNat (48 + n) else Char.ofNat (87 + n)

def hexOf (bs : List Nat) : String :=
  "0x" ++ String.ofList (bs.flatMap fun b => [hexDigit (b / 16), hexDigit (b % 16)])

/-- `toBeHex(n, w)`: `w` bytes, big endian. -/
def beBytes (w n : Nat) : List Nat :=
  (List.range w).reverse.map fun i => n / 256 ^ i % 256

mutual
  /-- `conditionId`, pre-order: paramType (1 byte), operator (1), number of
  children (4), compValue length (4), compValue, then the children. -/
  def idBytes : Cond → List Nat
    | ⟨e, o, v, ch⟩ =>
      beBytes 1 e ++ beBytes 1 o ++ beBytes 4 ch.length ++ beBytes 4 v.length ++ v ++ idBytesL ch
  def idBytesL : List Cond → List Nat
    | [] => []
    | x :: xs => idBytes x ++ idBytesL xs
end

/-- Ids are lowercase hex, so for equal lengths the string order is the byte order. -/
def sortLe (a b : Cond) : Bool :=
  let ia := idBytes a
  let ib := idBytes b
  ia.length < ib.length || (ia.length == ib.length && !decide (ib < ia))

/-- A Zip child stays where it is: it must come after the child that
    describes the value (the logical node's size is its first child's that
    fits, and a Zip's size has nothing to do with the value). -/
def canReorder (c : Cond) : Bool :=
  (if c.op == 1 then canReorderAnd c.ch else canReorderOr c.ch) &&
    !c.ch.any (fun x => x.op == 10 || x.op == 11)

/-- Sorted, with the calldata (`AbiEncoded`) children first. -/
def sortCh (cs : List Cond) : List Cond :=
  (cs.mergeSort sortLe).filter (·.enc == 5) ++ (cs.mergeSort sortLe).filter (·.enc != 5)

def sortB (c : Cond) : Cond :=
  if isLogical c && canReorder c then { c with ch := sortCh c.ch } else c

/-! ## `normalizeCondition`

The TypeScript recursion is unbounded (`pushDownOr` normalizes the merged
node again); `fuel` bounds it, and out of fuel the input is returned. -/

/-- `Pluck` (14) and `Zip` (10, 11) subtrees are left as written. -/
def keepsAsWritten (c : Cond) : Bool := c.op == 14 || c.op == 10 || c.op == 11

def normalize : Nat → Cond → Cond
  | 0, c => c
  | n + 1, c =>
    if keepsAsWritten c then c else
    let c1 := { c with ch := c.ch.map (normalize n) }
    sortB (pushDownOr (normalize n) (unwrap (dedupe (flatten c1))))

end Normalize
