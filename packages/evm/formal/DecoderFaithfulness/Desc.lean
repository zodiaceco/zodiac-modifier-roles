import DecoderFaithfulness.Spec
import DecoderFaithfulness.Roles

/-!
# Linking condition trees to values

`Desc s c u`: the raw (pre-pack) condition node `c` describes the value `u`.
These are the hypotheses of the theorems. They follow the structural rules
`Integrity.enforce` imposes; a looser `Desc` would make the theorems
stronger.

* Containers (`Tuple`, `Array`, `AbiEncoded`) need structural children.
* `Tuple` / `AbiEncoded` children describe the fields / arguments pointwise.
* `Array` children: `children[0]` is the layout template for every element
  (as `AbiLocation` uses it); child `i` describes element `i` (for
  `Matches`), and the last children describe the last elements (for
  `ArrayTailMatches`). Variant arrays (different interpretations per
  element) are therefore covered.
* `And` / `Or`: every structural child describes the same value (or is an
  interpretation that does not hold, see below); other children are
  non-structural (`NonStruct`). Children of variant nodes may be different
  interpretations of the same `bytes` value.
* `Slice` on a static word or on a bytes value, with nested slices below.
* `Zip*` is out of scope (no constructor admits it).

**Interpretations that do not hold.** A bytes-like child (`Dynamic`,
`AbiEncoded`, or a logical node over such) may sit at a bytes value it does
not describe, e.g. the `approve(...)` branch of `Or[transfer(...),
approve(...)]` on a `transfer` call. With `s = true` this is allowed
(`DescS.stray`); the theorems then only promise that Roles is at the right
`bytes` value, and nothing about navigation inside that child (that is
malformed-calldata territory). With `s = false` every interpretation must
hold, and the theorems give the full guarantee everywhere.
-/

namespace DecoderFaithfulness
open Roles

/-- Operators that make `evaluate` move to another location or are out of
    scope (`Zip*`). -/
def isNavOp : Operator → Bool
  | .And | .Or | .Matches | .ArraySome | .ArrayEvery | .ArrayTailMatches
  | .Slice | .ZipSome | .ZipEvery => true
  | _ => false

/-- Values encoded as `bytes`: plain bytes, or nested calldata. -/
def IsBytesLike : Val → Prop
  | .bytes _ => True
  | .call _ _ => True
  | _ => False

/-- The bytes a `Slice` indexes into: the word of a static value, the content
    (without length word and padding) of a bytes value. -/
def content : Val → Bytes
  | .word w => w
  | .bytes b => b
  | .call pre args => pre ++ encTuple args
  | _ => []

/-- `size` bytes starting at `shift`. -/
def window (bs : Bytes) (shift size : Nat) : Bytes := (bs.drop shift).take size

/-- `small` is a contiguous part of `big`. -/
def IsWindow (small big : Bytes) : Prop :=
  ∃ i, i + small.length ≤ big.length ∧ small = (big.drop i).take small.length

/-- Non-structural node: `None`/`EtherValue` leaves that never read calldata
    locations, and logical nodes over such leaves. -/
inductive NonStruct : Condition → Prop
  | leaf {c : Condition} :
      (c.encoding = .None ∨ c.encoding = .EtherValue) → c.children = [] →
      isNavOp c.operator = false → NonStruct c
  | logical {c : Condition} :
      c.encoding = .None → (c.operator = .And ∨ c.operator = .Or) →
      (∀ ch, ch ∈ c.children → NonStruct ch) → NonStruct c

mutual
  /-- Bytes-like node: decodes its location as a length-prefixed value. -/
  inductive BytesLike : Condition → Prop
    | dyn {c : Condition} : c.encoding = .Dynamic → BytesLike c
    | abi {c : Condition} : c.encoding = .AbiEncoded → BytesLike c
    | logical {c : Condition} (ch0 : Condition) :
        c.encoding = .None → (c.operator = .And ∨ c.operator = .Or) →
        ch0 ∈ c.children → BytesLike ch0 → (∀ ch, ch ∈ c.children → BytesLikeN ch) →
        BytesLike c

  inductive BytesLikeN : Condition → Prop
    | bl {c} : BytesLike c → BytesLikeN c
    | ns {c} : NonStruct c → BytesLikeN c
end

mutual
  /-- Admissible root: the top-level calldata has no length word, so only
      `AbiEncoded` nodes (possibly under `And`/`Or`) may describe it. -/
  inductive RootOK : Condition → Prop
    | abi {c : Condition} : c.encoding = .AbiEncoded → RootOK c
    | logical {c : Condition} :
        c.encoding = .None → (c.operator = .And ∨ c.operator = .Or) →
        (∀ ch, ch ∈ c.children → RootOKN ch) → RootOK c

  inductive RootOKN : Condition → Prop
    | ok {c} : RootOK c → RootOKN c
    | ns {c} : NonStruct c → RootOKN c
end

/-- Child of a `Slice`: a static leaf, or another `Slice` on a static value. -/
inductive Win : Condition → Prop
  | leaf {c : Condition} :
      c.encoding = .Static → c.children = [] → isNavOp c.operator = false → Win c
  | slice {c ch : Condition} :
      c.encoding = .Static → c.operator = .Slice → c.children = [ch] →
      1 ≤ sliceSize c.compValue → sliceSize c.compValue ≤ 32 → Win ch → Win c

mutual
  inductive Desc (s : Bool) : Condition → Val → Prop
    | word {c : Condition} {w : Bytes} :
        c.encoding = .Static → c.children = [] → isNavOp c.operator = false →
        w.length = 32 → Desc s c (.word w)
    | bytes {c : Condition} {u : Val} :
        c.encoding = .Dynamic → c.children = [] → isNavOp c.operator = false →
        IsBytesLike u → Desc s c u
    | sliceWord {c ch : Condition} {w : Bytes} :
        c.encoding = .Static → c.operator = .Slice → c.children = [ch] →
        1 ≤ sliceSize c.compValue → sliceSize c.compValue ≤ 32 → Win ch →
        w.length = 32 → Desc s c (.word w)
    | sliceBytes {c ch : Condition} {u : Val} :
        c.encoding = .Dynamic → c.operator = .Slice → c.children = [ch] →
        1 ≤ sliceSize c.compValue → sliceSize c.compValue ≤ 32 → Win ch →
        IsBytesLike u → Desc s c u
    | tuple {c : Condition} {vs : List Val} :
        c.encoding = .Tuple → vs ≠ [] → DescAll s c.children vs →
        (isNavOp c.operator = false ∨ c.operator = .Matches) →
        Desc s c (.tuple vs)
    | array {c : Condition} {vs : List Val} (c0 : Condition) (cs : List Condition) :
        c.encoding = .Array → c.children = c0 :: cs →
        (∀ v, v ∈ vs → DescS s c0 v) →
        (∀ i (hi : i < c.children.length) (hv : i < vs.length),
          DescS s c.children[i] vs[i]) →
        (∀ j (hj : j < c.children.length) (hk : c.children.length ≤ vs.length),
          DescS s c.children[j] (vs[vs.length - c.children.length + j]'(by omega))) →
        (isNavOp c.operator = false ∨ c.operator = .Matches ∨ c.operator = .ArraySome ∨
          c.operator = .ArrayEvery ∨ c.operator = .ArrayTailMatches) →
        Desc s c (.array vs)
    | call {c : Condition} {pre : Bytes} {args : List Val} :
        c.encoding = .AbiEncoded → c.leadingBytes = pre.length → args ≠ [] →
        DescAll s c.children args →
        (c.operator = .Matches ∨ c.operator = .Pass) →
        Desc s c (.call pre args)
    | logical {c : Condition} {u : Val} (ch0 : Condition) :
        c.encoding = .None → (c.operator = .And ∨ c.operator = .Or) →
        ch0 ∈ c.children → DescS s ch0 u →
        (∀ ch, ch ∈ c.children → DescSN s ch u) →
        Desc s c u

  inductive DescAll (s : Bool) : List Condition → List Val → Prop
    | nil : DescAll s [] []
    | cons {c cs v vs} : DescS s c v → DescAll s cs vs → DescAll s (c :: cs) (v :: vs)

  /-- A structural child at a value: describes it, or (with `s = true`) is a
      bytes-like interpretation of a bytes value that need not hold. -/
  inductive DescS (s : Bool) : Condition → Val → Prop
    | desc {c u} : Desc s c u → DescS s c u
    | stray {c u} : s = true → BytesLike c → IsBytesLike u → DescS s c u

  /-- Child of a logical node: structural, or non-structural. -/
  inductive DescSN (s : Bool) : Condition → Val → Prop
    | ds {c u} : DescS s c u → DescSN s c u
    | ns {c u} : NonStruct c → DescSN s c u
end

/-! ## Byte placement -/

/-- `bs` sits in `data` at byte position `l`. -/
def At (data : Bytes) (l : Nat) (bs : Bytes) : Prop :=
  (data.drop l).take bs.length = bs ∧ l + bs.length ≤ data.length

/-- Where Roles expects a value's encoding at location `l`. Nested calldata
    (`call`) at `l > 0` is a length-prefixed `bytes` value; at `l = 0` it is
    the top-level calldata itself, with no length word (`evaluate` adds 32
    to the location of `AbiEncoded` nodes only when `location > 0`). -/
def Placed (data : Bytes) (l : Nat) : Val → Prop
  | .call pre args =>
      (l = 0 ∧ At data 0 (pre ++ encTuple args)) ∨ (0 < l ∧ At data l (enc (.call pre args)))
  | u => At data l (enc u)

/-- The value `__input` should produce for a value whose encoding is `bs`
    (every modeled encoding is at least 32 bytes). -/
def expectInput (bs : Bytes) : Input :=
  if bs.length = 32 then .word (wordVal bs) else .hash bs

end DecoderFaithfulness
