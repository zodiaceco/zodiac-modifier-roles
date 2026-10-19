import AbiLayerA.Bytes

/-!
# Solidity ABI encoding — reference specification

Transcribed from the "Formal Specification of the Encoding" section of the
Solidity ABI spec (https://docs.soliditylang.org/en/latest/abi-spec.html).
This file knows nothing about Roles: no calldata walking, no offsets read
back, no Roles metadata. It only builds bytes from values.

Spec text, abridged, for the cases modeled here:

* static `T` occupying one word (`uint<M>`, `int<M>`, `address`, `bool`,
  `bytes<M>`, ...): `enc(X)` is a 32-byte word. Its internal layout (left or
  right padding, sign extension) is type-specific and irrelevant to locating
  data, so a static word value is modeled as "any 32 bytes".
* `bytes` of length `k`: `enc(X) = enc(k) pad_right(X)`, padded with zero
  bytes to a multiple of 32. `string` is `enc(enc_utf8(X))`, i.e. the same.
* `(T1,...,Tk)`: `enc(X) = head(X(1)) ... head(X(k)) tail(X(1)) ... tail(X(k))`
  where for static `Ti`: `head(X(i)) = enc(X(i))`, `tail(X(i)) = ""`, and for
  dynamic `Ti`:
  `head(X(i)) = enc(len(head(X(1)) ... head(X(k)) tail(X(1)) ... tail(X(i-1))))`,
  `tail(X(i)) = enc(X(i))`.
* `T[]` with `k` elements: `enc(X) = enc(k) enc((X[0], ..., X[k-1]))`.
* `T[k]`: encoded exactly like the tuple `(T, ..., T)`. Covered by `tuple`.
* A type is dynamic iff it is `bytes`, `string`, `T[]`, `T[k]` with dynamic
  `T`, or a tuple with a dynamic component.

One non-ABI convenience is added: `call pre args`, a `bytes` value whose
content is `pre ++ enc(args)` (nested calldata: a selector or other prefix
followed by ABI-encoded arguments). Its encoding is by definition the `bytes`
encoding of that content, so it adds no new encoding rule.

Values are untyped: whether a value fits a function signature is expressed
on the Roles side, by the condition tree that describes it (`Desc.lean`).
-/

namespace AbiLayerA

inductive Val where
  | word (w : Bytes)
  | bytes (b : Bytes)
  | tuple (vs : List Val)
  | array (vs : List Val)
  | call (pre : Bytes) (args : List Val)
  deriving Inhabited

mutual
  def Val.isStatic : Val → Bool
    | .word _ => true
    | .bytes _ => false
    | .tuple vs => Val.allStatic vs
    | .array _ => false
    | .call _ _ => false

  def Val.allStatic : List Val → Bool
    | [] => true
    | v :: vs => v.isStatic && Val.allStatic vs
end

/-- `enc(k) pad_right(X)` for a byte string `X`. -/
def encBytes (b : Bytes) : Bytes :=
  word b.length ++ b ++ zeros (ceil32 b.length - b.length)

mutual
  /-- `enc(X)`. -/
  def enc : Val → Bytes
    | .word w => w
    | .bytes b => encBytes b
    | .tuple vs => (encParts vs (headLen vs)).1 ++ (encParts vs (headLen vs)).2
    | .array vs =>
        word vs.length ++ (encParts vs (headLen vs)).1 ++ (encParts vs (headLen vs)).2
    | .call pre args =>
        encBytes (pre ++ (encParts args (headLen args)).1 ++ (encParts args (headLen args)).2)

  /-- `len(head(X(1)) ... head(X(k)))`: static components contribute their
      encoding, dynamic ones a 32-byte offset word. -/
  def headLen : List Val → Nat
    | [] => 0
    | v :: vs => (if v.isStatic then (enc v).length else 32) + headLen vs

  /-- `(head(X(i)) ... head(X(k)), tail(X(i)) ... tail(X(k)))`, where `off`
      is `len(head(X(1)) ... head(X(k)) tail(X(1)) ... tail(X(i-1)))`. -/
  def encParts : List Val → Nat → Bytes × Bytes
    | [], _ => ([], [])
    | v :: vs, off =>
        if v.isStatic then
          (enc v ++ (encParts vs off).1, (encParts vs off).2)
        else
          (word off ++ (encParts vs (off + (enc v).length)).1,
           enc v ++ (encParts vs (off + (enc v).length)).2)
end

/-- `enc((X(1), ..., X(k)))`. -/
def encTuple (vs : List Val) : Bytes :=
  (encParts vs (headLen vs)).1 ++ (encParts vs (headLen vs)).2

theorem enc_tuple (vs : List Val) : enc (.tuple vs) = encTuple vs := by
  simp [enc, encTuple]

theorem enc_array (vs : List Val) : enc (.array vs) = word vs.length ++ encTuple vs := by
  simp [enc, encTuple]

theorem enc_call (pre : Bytes) (args : List Val) :
    enc (.call pre args) = encBytes (pre ++ encTuple args) := by
  simp [enc, encTuple, List.append_assoc]

/-! ## Sub-values

`u.sub p` follows a path of component indices: tuple field `i`, array
element `i`, or argument `i` of nested calldata. -/

def Val.sub : Val → List Nat → Option Val
  | v, [] => some v
  | .tuple vs, i :: p => match vs[i]? with
    | some u => u.sub p
    | none => none
  | .array vs, i :: p => match vs[i]? with
    | some u => u.sub p
    | none => none
  | .call _ args, i :: p => match args[i]? with
    | some u => u.sub p
    | none => none
  | _, _ :: _ => none

end AbiLayerA
