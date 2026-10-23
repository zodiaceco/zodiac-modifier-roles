import ConditionCheck.Sound
import ConditionPacking.Main

/-!
# From the stored buffer to the operands

Chains the three proofs for a client that stores a flat condition array `fs`
with a `...Packed` setter (no Integrity on-chain):

1. `fs` is `Packable` and the check accepts the tree it describes
   (`ConditionPacking.rawTree`);
2. `pack_roundtrip`: the tree `unpack` returns from the stored buffer is
   `annotate (rawTree fs 0)`;
3. `checked_input` (`checkCondition_sound` + `decoder_input`): on every
   well-typed calldata, every node `evaluate` reaches in that tree that reads
   `__input` reads the spec encoding of its value.
-/

namespace ConditionCheck
open DecoderFaithfulness DecoderFaithfulness.Roles

theorem stored_input {s : Bool} {fs : List ConditionPacking.Flat} (hP : ConditionPacking.Packable fs)
    (avatar : Bytes) (junk junk' : ConditionPacking.Mem) {lb : Nat} {ts : List Ty} {o : Bool}
    (h : checkCondition s (ConditionPacking.rawTree avatar fs 0) = some (.call lb ts o))
    {tree : Condition} {maxPluck : Nat}
    (hu : ConditionPacking.unpack avatar
      (ConditionPacking.bufMem (ConditionPacking.pack junk fs) junk') = some (tree, maxPluck))
    {pre : Bytes} {args : List Val} (hpre : pre.length = lb)
    (hargs : if o then HasTPre s args ts else HasTAll s args ts)
    (suffix : Bytes) (hlen : (calldata pre args suffix).length < 2 ^ 255)
    {p : List Nat} {d : Condition} {l : Nat}
    (hv : Eval (calldata pre args suffix) tree p d l)
    (hop : readsInput d.operator = true) :
    (∃ u, (Val.call pre args).sub p = some u ∧
      input (calldata pre args suffix) l d = expectInput (enc u)) ∨
    (∃ u bs, (Val.call pre args).sub p = some u ∧ IsWindow bs (content u) ∧
      input (calldata pre args suffix) l d = .word (wordVal bs)) ∨
    input (calldata pre args suffix) l d = .etherValue ∨
    InStray s (calldata pre args suffix) (.call pre args) p d l := by
  rw [ConditionPacking.pack_roundtrip avatar junk junk' fs hP] at hu
  simp only [Option.some.injEq, Prod.mk.injEq] at hu
  obtain ⟨rfl, -⟩ := hu
  exact checked_input h hpre hargs suffix hlen hv hop

end ConditionCheck
