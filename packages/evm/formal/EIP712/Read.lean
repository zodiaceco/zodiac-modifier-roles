import EIP712.Encoder
import EIP712.Spec

/-!
# What the encoder reads

`readV data fuel t loc` walks `data` exactly as `hashField` does (same
locations, same checks, same reverts) and returns the value it finds there
instead of hashing it: the word of a `Static` node, the content of a
`Dynamic` node, the members / elements of a `Tuple` / `Array` node.

`Lay K defs ty t`: `t` is the type tree the SDK sends for EIP-712 type `ty`
(`toAbiTypes`, after `_toTree`): a struct is a `Tuple` with its `typeHash`,
`T[n]` a `Tuple` of `n` copies without one, `T[]` an `Array`, atomic types
`Static`, `bytes` / `string` `Dynamic`. A recursive struct has no `Lay`
(its tree would be infinite).
-/

namespace EIP712
open DecoderFaithfulness DecoderFaithfulness.Roles

/-- `_hashField`'s walk, returning the value read. -/
def readV (data : Bytes) : Nat → TN → Nat → Option V
  | 0, _, _ => none
  | fuel + 1, t, location =>
    if t.encoding = .Static then (wordAt data location).map .atom
    else if t.encoding = .Dynamic then
      match wordAt data location with
      | none => none
      | some w =>
        let left := location + 32
        let right := left + wordVal w
        if right > data.length then none else some (.dyn ((data.drop left).take (right - left)))
    else if t.encoding = .Array then
      match wordAt data location with
      | none => none
      | some w =>
        if true ∧ t.children.length ≠ 1 then none
        else (blockLoop data (readV data fuel) t.children true (location + 32) (wordVal w) 0 0).map .list
    else if t.encoding = .Tuple then
      if false ∧ t.children.length ≠ 1 then none
      else (blockLoop data (readV data fuel) t.children false location t.children.length 0 0).map .list
    else none

mutual
  inductive Lay (K : Bytes → Bytes) (defs : Defs) : Ty → TN → Prop
    | atom {a th} : Lay K defs (.atom a) ⟨.Static, [], th⟩
    | bytes {th} : Lay K defs .bytes ⟨.Dynamic, [], th⟩
    | string {th} : Lay K defs .string ⟨.Dynamic, [], th⟩
    | struct {s ls} : defs.lookup s ≠ none →
        LayL K defs ((fieldsOf defs s).map (·.ty)) ls → ls ≠ [] →
        typeHash K defs s ≠ zeros 32 →
        Lay K defs (.struct s) ⟨.Tuple, ls, typeHash K defs s⟩
    | array {t l} : Lay K defs t l → Lay K defs (.array t) ⟨.Array, [l], zeros 32⟩
    | fixed {t n l} : 0 < n → Lay K defs t l →
        Lay K defs (.fixed t n) ⟨.Tuple, List.replicate n l, zeros 32⟩

  inductive LayL (K : Bytes → Bytes) (defs : Defs) : List Ty → List TN → Prop
    | nil : LayL K defs [] []
    | cons {t ts l ls} : Lay K defs t l → LayL K defs ts ls → LayL K defs (t :: ts) (l :: ls)
end

end EIP712
