import DecoderFaithfulness.Spec

/-!
# EIP-712 — reference specification

Transcribed from EIP-712 ("Typed structured data hashing and signing",
https://eips.ethereum.org/EIPS/eip-712), sections "Definition of typed
structured data", "Definition of `encodeType`", "Definition of
`encodeData`", "Definition of `hashStruct`" and "Specification of the
`eth_signTypedData` JSON RPC". It knows nothing of the ABI or of Roles.

`keccak256` is a parameter `K`. No theorem assumes anything of it, except
where a statement says so.

Spec text, abridged, for what is modeled:

* `encode(domainSeparator, message) = "\x19\x01" ‖ domainSeparator ‖ hashStruct(message)`,
  with `domainSeparator = hashStruct(eip712Domain)`.
* `hashStruct(s) = keccak256(typeHash ‖ encodeData(s))`,
  `typeHash = keccak256(encodeType(typeOf(s)))`.
* `encodeType`: `name ‖ "(" ‖ member₁ ‖ "," ‖ member₂ ‖ … ‖ ")"`, each member
  `type ‖ " " ‖ name`. "If the struct type references other struct types (and
  these in turn reference even more struct types), then the set of
  referenced struct types is collected, sorted by name and appended to the
  encoding."
* `encodeData(s) = enc(value₁) ‖ enc(value₂) ‖ … ‖ enc(valueₙ)`, each 32 bytes:
  - atomic values: "Boolean `false` and `true` are encoded as `uint256`
    values `0` and `1`. Addresses are encoded as `uint160`. Integer values
    are sign-extended to 256-bit and encoded in big endian order. `bytes1` to
    `bytes31` are … zero-padded at the end to `bytes32`."
  - "The dynamic values `bytes` and `string` are encoded as a `keccak256`
    hash of their contents."
  - "The array values are encoded as the `keccak256` hash of the
    concatenated `encodeData` of their contents (i.e. the encoding of
    `SomeType[5]` is identical to that of a struct containing five members
    of type `SomeType`)."
  - "The struct values are encoded recursively as `hashStruct(value)`."

An atomic value is represented by its 32-byte encoding: `Atom.Canon a w`
says `w` is the encoding of some value of type `a` (the image of the rules
above). A `string` is represented by its UTF-8 bytes.
-/

namespace EIP712
open DecoderFaithfulness

/-- Atomic types: `uint<M>`, `int<M>`, `address`, `bool`, `bytes<M>`. -/
inductive Atom where
  | uint (bits : Nat)
  | int (bits : Nat)
  | address
  | bool
  | fbytes (n : Nat)
  deriving DecidableEq, Repr, Inhabited

/-- Member types: atomic, `bytes`, `string`, a struct by name, `T[]`, `T[n]`. -/
inductive Ty where
  | atom (a : Atom)
  | bytes
  | string
  | struct (name : String)
  | array (t : Ty)
  | fixed (t : Ty) (n : Nat)
  deriving DecidableEq, Repr, Inhabited

structure Field where
  name : String
  ty : Ty
  deriving DecidableEq, Repr, Inhabited

/-- Struct definitions, by name. -/
abbrev Defs := List (String × List Field)

def fieldsOf (defs : Defs) (s : String) : List Field := (defs.lookup s).getD []

/-- The 32-byte words that encode a value of an atomic type. -/
def Atom.Canon : Atom → Bytes → Prop
  | .uint bits, w => w.length = 32 ∧ wordVal w < 2 ^ bits
  | .int bits, w => w.length = 32 ∧
      (wordVal w < 2 ^ (bits - 1) ∨ 2 ^ 256 - 2 ^ (bits - 1) ≤ wordVal w)
  | .address, w => w.length = 32 ∧ wordVal w < 2 ^ 160
  | .bool, w => w.length = 32 ∧ wordVal w < 2
  | .fbytes n, w => w.length = 32 ∧ w.drop n = zeros (32 - n)

/-- Values: an atomic value's encoding, the content of `bytes` / `string`,
    or the members of a struct / elements of an array, in order. -/
inductive V where
  | atom (w : Bytes)
  | dyn (b : Bytes)
  | list (vs : List V)
  deriving Inhabited

mutual
  /-- `v` is a value of type `t`. -/
  inductive HasTy (defs : Defs) : Ty → V → Prop
    | atom {a w} : a.Canon w → HasTy defs (.atom a) (.atom w)
    | bytes {b} : HasTy defs .bytes (.dyn b)
    | string {b} : HasTy defs .string (.dyn b)
    | struct {s vs} : defs.lookup s ≠ none →
        HasTys defs ((fieldsOf defs s).map (·.ty)) vs → HasTy defs (.struct s) (.list vs)
    | array {t vs} : HasSame defs t vs → HasTy defs (.array t) (.list vs)
    | fixed {t n vs} : vs.length = n → HasSame defs t vs → HasTy defs (.fixed t n) (.list vs)

  /-- Member `i` has type `ts[i]`. -/
  inductive HasTys (defs : Defs) : List Ty → List V → Prop
    | nil : HasTys defs [] []
    | cons {t ts v vs} : HasTy defs t v → HasTys defs ts vs → HasTys defs (t :: ts) (v :: vs)

  /-- Every element has type `t`. -/
  inductive HasSame (defs : Defs) : Ty → List V → Prop
    | nil {t} : HasSame defs t []
    | cons {t v vs} : HasTy defs t v → HasSame defs t vs → HasSame defs t (v :: vs)
end

/-! ## `encodeType` and `typeHash` -/

def Atom.str : Atom → String
  | .uint b => "uint" ++ toString b
  | .int b => "int" ++ toString b
  | .address => "address"
  | .bool => "bool"
  | .fbytes n => "bytes" ++ toString n

def Ty.str : Ty → String
  | .atom a => a.str
  | .bytes => "bytes"
  | .string => "string"
  | .struct s => s
  | .array t => t.str ++ "[]"
  | .fixed t n => t.str ++ "[" ++ toString n ++ "]"

/-- The struct a member type references (through any arrays). -/
def Ty.structName : Ty → Option String
  | .struct s => some s
  | .array t => t.structName
  | .fixed t _ => t.structName
  | _ => none

/-- `name ‖ "(" ‖ type₁ " " name₁ ‖ "," ‖ … ‖ ")"`. -/
def structStr (defs : Defs) (s : String) : String :=
  s ++ "(" ++ ",".intercalate ((fieldsOf defs s).map fun f => f.ty.str ++ " " ++ f.name) ++ ")"

/-- Structs `s` references directly. -/
def refs (defs : Defs) (s : String) : List String :=
  (fieldsOf defs s).filterMap (·.ty.structName)

/-- Structs reachable from `seen` (`fuel` rounds; `defs.length + 1` reach
    every one, each round adds a new name or stops). -/
def closure (defs : Defs) : Nat → List String → List String
  | 0, seen => seen
  | n + 1, seen =>
    let next := (seen ++ seen.flatMap (refs defs)).eraseDups
    if next.length = seen.length then seen else closure defs n next

/-- The struct types `s` references, directly or not, without `s` itself. -/
def deps (defs : Defs) (s : String) : List String :=
  (closure defs (defs.length + 1) [s]).filter (· ≠ s)

/-- `encodeType`: the struct, then its dependencies sorted by name. -/
def encodeType (defs : Defs) (s : String) : String :=
  structStr defs s ++
    String.join (((deps defs s).mergeSort fun a b => decide (a < b)).map (structStr defs))

def utf8 (s : String) : Bytes := s.toUTF8.toList.map fun b => ⟨b.toNat % 256, Nat.mod_lt _ (by decide)⟩

def typeHash (K : Bytes → Bytes) (defs : Defs) (s : String) : Bytes := K (utf8 (encodeType defs s))

/-! ## `encodeData` and `hashStruct`

`encV t v` is the 32-byte `enc(v)` of a member of type `t`; for a struct it
is `hashStruct`. -/

mutual
  def encV (K : Bytes → Bytes) (defs : Defs) : Ty → V → Bytes
    | _, .atom w => w
    | _, .dyn b => K b
    | .struct s, .list vs =>
        K (typeHash K defs s ++ encFields K defs ((fieldsOf defs s).map (·.ty)) vs)
    | .array t, .list vs => K (encSame K defs t vs)
    | .fixed t _, .list vs => K (encSame K defs t vs)
    | _, .list _ => []

  /-- `encodeData`: `enc(value₁) ‖ … ‖ enc(valueₙ)`. -/
  def encFields (K : Bytes → Bytes) (defs : Defs) : List Ty → List V → Bytes
    | t :: ts, v :: vs => encV K defs t v ++ encFields K defs ts vs
    | _, _ => []

  /-- The concatenated encodings of an array's elements. -/
  def encSame (K : Bytes → Bytes) (defs : Defs) (t : Ty) : List V → Bytes
    | [] => []
    | v :: vs => encV K defs t v ++ encSame K defs t vs
end

/-- `hashStruct(s)` for a value `v` of struct type `s`. -/
def hashStruct (K : Bytes → Bytes) (defs : Defs) (s : String) (v : V) : Bytes :=
  encV K defs (.struct s) v

/-- `"\x19\x01" ‖ domainSeparator ‖ hashStruct(message)`, hashed: the digest
    that gets signed. -/
def digest (K : Bytes → Bytes) (defs : Defs) (primary : String) (domain message : V) : Bytes :=
  K ([0x19, 0x01] ++ hashStruct K defs "EIP712Domain" domain ++ hashStruct K defs primary message)

/-! ## The ABI view of a value

The SDK sends a struct as the ABI encoding of its members (a tuple block),
and an array `T[n]` as the tuple `(T, …, T)`, which the ABI encodes like
`T[n]`. -/

mutual
  def abiOf (defs : Defs) : Ty → V → Val
    | _, .atom w => .word w
    | _, .dyn b => .bytes b
    | .struct s, .list vs => .tuple (abiFields defs ((fieldsOf defs s).map (·.ty)) vs)
    | .array t, .list vs => .array (abiSame defs t vs)
    | .fixed t _, .list vs => .tuple (abiSame defs t vs)
    | _, .list _ => .tuple []

  def abiFields (defs : Defs) : List Ty → List V → List Val
    | t :: ts, v :: vs => abiOf defs t v :: abiFields defs ts vs
    | _, _ => []

  def abiSame (defs : Defs) (t : Ty) : List V → List Val
    | [] => []
    | v :: vs => abiOf defs t v :: abiSame defs t vs
end

end EIP712
