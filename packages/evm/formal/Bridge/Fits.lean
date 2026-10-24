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
(comparisons, `Custom`, `Pluck`) see exactly `m`'s type. At a variant
layout (`isVarLay`: the call types a `bytes` value may have, keyed by their
leading bytes) a call branch fits its candidate (`varAbi`) and a check on
the plain bytes fits `dynLay` (`varDyn`). A Zip's fields fit the element
layouts of the arrays it reads, `P k` for slot `k` (`zip`), and a Pluck
into a slot with a layout plucks a value of that layout.

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

section
variable (avatar : Bytes) (P : Nat → Option Condition)

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

/-- The layout of a plain `bytes` value. -/
def dynLay : Condition := ⟨.Dynamic, .Pass, [], false, 0, 0, []⟩

/-- No other candidate's key is a prefix of `k`'s or the other way round:
    calldata starts with at most one key. -/
def KeyUnique (m k : Condition) : Prop :=
  ∀ k' ∈ m.children, k' ≠ k → ¬ k'.compValue <+: k.compValue ∧ ¬ k.compValue <+: k'.compValue

inductive Fits : Cond → Condition → Condition → Prop
  | pass {c d m} : c.op = 0 → Node avatar c d → isStruct c = true → LayEq d m → Plain c →
      isInl c = (D avatar c).inlined → (d = D avatar c → PDesc avatar c m) → Fits c d m
  | ns {c d m} : isStruct c = false → NsOk c → d = D avatar c → (∀ k ∈ plucks c, P k = none) →
      Fits c d m
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
      (c.enc = 4 → c.ch ≠ []) → (c.enc = 1 ∨ c.enc = 2 → c.ch = []) → c.enc ≤ 5 →
      (c.op = 14 → ∀ ma, P (c.cv.headD 0 % 256) = some ma → ma = m) → Fits c d m
  /-- A call interpretation of a variant: it fits its candidate, the one
      keyed by its leading bytes. -/
  | varAbi {c d m k} : c.op = 5 → c.enc = 5 → d = D avatar c → isVarLay m = true → LayEq d m →
      k ∈ m.children → k.encoding = .AbiEncoded → k.compValue = prefixOf 5 c.cv →
      KeyUnique m k → Fits c (D avatar c) k → Fits c d m
  /-- A check of the plain `bytes` value of a variant. -/
  | varDyn {c d m} : isVarLay m = true → c.enc = 2 → LayEq d m → Fits c d dynLay → Fits c d m
  /-- A Zip over a tuple of fields: field `f` fits the element layout of the
      array plucked into the slot of compValue byte `f`. The value is not
      inlined (a Zip's own metadata has nothing to do with it, so a logical
      parent's would be wrong for an inlined value). -/
  | zip {c d m t} : (c.op = 10 ∨ c.op = 11) → c.enc = 0 → d = D avatar c → c.ch = [t] →
      m.inlined = false →
      t.op = 5 → t.enc = 3 → t.ch.length = c.cv.length → (∀ x ∈ t.ch, isStruct x = true) →
      (∀ k ∈ c.cv, (P (k % 256)).isSome) →
      (∀ f ma, P (c.cv.getD f 0 % 256) = some ma → ma.encoding = .Array) →
      (∀ f (h : f < t.ch.length) ma, P (c.cv.getD f 0 % 256) = some ma →
        Fits t.ch[f] (D avatar t.ch[f]) (tmpl ma)) →
      Fits c d m
  /-- An `And`/`Or` of Zips and checks that read no calldata (normalization
      merges `Or` branches that differ in a Zip into one). -/
  | zipLogical {c d m} : (c.op = 1 ∨ c.op = 2) → c.enc = 0 → isStruct c = false → hasZip c = true →
      d = D avatar c → m.inlined = false → (∀ x ∈ c.ch, Fits x (D avatar x) m) → Fits c d m

theorem Fits.dyn_op {c : Cond} {d m : Condition} (h : Fits avatar P c d m) :
    c.enc = 2 → c.op ≠ 1 ∧ c.op ≠ 2 := by
  induction h with
  | pass hop _ _ _ _ _ _ => intro; omega
  | ns hs hns _ _ => intro; rcases hns with ⟨h, _, _⟩ | ⟨_, h, _⟩ <;> omega
  | logical _ h _ _ _ _ _ => intro; omega
  | tup _ h _ _ _ _ _ _ _ _ => intro; omega
  | arr _ h _ _ _ _ _ _ _ => intro; omega
  | slice hop _ _ _ _ _ _ _ _ => intro; omega
  | leaf hop _ _ _ _ _ _ _ _ _ _ _ _ =>
    intro
    unfold leafOp at hop; simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true,
      decide_eq_true_eq] at hop; omega
  | varAbi _ h _ _ _ _ _ _ _ _ => intro; omega
  | varDyn _ _ _ _ ih => exact ih
  | zip h _ _ _ _ _ _ _ _ _ _ _ _ => intro; omega
  | zipLogical h _ _ _ _ _ _ _ => intro; omega

/-- `decodeAt` with the encoding taken from the layout. -/
def decodeL (data : Calldata) (m : Condition) (l : Nat) : Option (List Nat) :=
  decodeAt data (if m.encoding = .AbiEncoded then 5 else 3) m l

inductive Decodable (data : Calldata) : Condition → Nat → Prop
  | leaf {m l} : m.encoding ≠ .Tuple → m.encoding ≠ .AbiEncoded → m.encoding ≠ .Array →
      isVarLay m = false → Decodable data m l
  /-- A variant: the calldata decodes as the candidate whose key it starts
      with (the other branches fail on their leading bytes). -/
  | var {m l} : isVarLay m = true →
      (∀ k ∈ m.children, (leadingCheck data (adjust 5 l) k.compValue).isNone = true →
        Decodable data k l) → Decodable data m l
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
    (o = 14 → ∃ k ∈ cv.head?, k % 256 < n) ∧ (o = 10 ∨ o = 11 → ∀ k ∈ cv, k % 256 < n) ∧
    ∀ x ∈ ch, CvOk n x
  termination_by c => sizeOf c
  decreasing_by
    simp_wf
    have := List.sizeOf_lt_of_mem ‹_ ∈ ch›
    omega

/-! ## Pluck slots a Zip reads

`za c A` transcribes Integrity's `_validatePluckAssignments` for Zips: the
slots written once `c` passes, starting from slots `A`, or `none` if a Zip
may read a slot no Pluck wrote (`WithinRatio` is not checked: it reads a
slot's value, which the world reads as the contract does). -/

mutual
  def za : Cond → (Nat → Bool) → Option (Nat → Bool)
    | ⟨_, o, cv, ch⟩, A =>
      if o = 14 then some fun j => j == cv.headD 0 % 256 || A j
      else if o = 10 ∨ o = 11 then
        if (zipKeys cv).all A then (zaFields ch A).map fun A' => if o = 10 then A' else A else none
      else if o = 2 then zaOr ch A
      else if o = 6 ∨ o = 7 then (zaFirst ch A).map fun A' => if o = 6 then A' else A
      else if o = 1 ∨ o = 5 ∨ o = 8 then zaSeq ch A
      else if o = 13 then zaFirst ch A
      else some A
  def zaSeq : List Cond → (Nat → Bool) → Option (Nat → Bool)
    | [], A => some A
    | c :: cs, A => (za c A).bind (zaSeq cs)
  def zaOr : List Cond → (Nat → Bool) → Option (Nat → Bool)
    | [], _ => some fun _ => false
    | [c], A => za c A
    | c :: c' :: cs, A => (za c A).bind fun a => (zaOr (c' :: cs) A).map fun b j => a j && b j
  def zaFirst : List Cond → (Nat → Bool) → Option (Nat → Bool)
    | [], A => some A
    | c :: _, A => za c A
  def zaFields : List Cond → (Nat → Bool) → Option (Nat → Bool)
    | [], A => some A
    | ⟨_, _, _, fs⟩ :: _, A => zaSeq fs A
end

/-- The slots in `A` hold locations that decode as their layouts. -/
def Inv (data : Calldata) (P : Nat → Option Condition) (A : Nat → Bool) (sl : Slots) : Prop :=
  ∀ k ma, A k = true → P k = some ma → Decodable data ma (sl.locations k)

/-- Every slot location written between `sl` and `sl'` decodes as its layout. -/
def WV (data : Calldata) (P : Nat → Option Condition) (sl sl' : Slots) : Prop :=
  ∀ k ma, P k = some ma → sl'.locations k ≠ sl.locations k → Decodable data ma (sl'.locations k)

theorem WV.refl (data : Calldata) (P : Nat → Option Condition) (sl : Slots) : WV data P sl sl :=
  fun _ _ _ h => absurd rfl h

theorem WV.trans {data : Calldata} {P : Nat → Option Condition} {s1 s2 s3 : Slots}
    (h1 : WV data P s1 s2) (h2 : WV data P s2 s3) : WV data P s1 s3 := by
  intro k ma hp hne
  by_cases h : s3.locations k = s2.locations k
  · rw [h] at hne ⊢; exact h1 k ma hp hne
  · exact h2 k ma hp h

theorem Inv.wv {data : Calldata} {P : Nat → Option Condition} {A : Nat → Bool} {sl sl' : Slots}
    (h : Inv data P A sl) (hw : WV data P sl sl') : Inv data P A sl' := by
  intro k ma hA hp
  by_cases he : sl'.locations k = sl.locations k
  · rw [he]; exact h k ma hA hp
  · exact hw k ma hp he

theorem Inv.mono {data : Calldata} {P : Nat → Option Condition} {A B : Nat → Bool} {sl : Slots}
    (h : Inv data P A sl) (hs : ∀ k, B k = true → A k = true) : Inv data P B sl :=
  fun k ma hB hp => h k ma (hs k hB) hp

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
