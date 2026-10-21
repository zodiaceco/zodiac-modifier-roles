import ConditionCheck.Sound

/-!
# Examples

The decoder proof's example trees pass the check (so `checkCondition_sound`
applies to them), and the Zip-as-positional-child shape from the Integrity
backlog (item 1, a bypass that Integrity accepts) is rejected.
-/

namespace ConditionCheck.Examples
open ConditionCheck DecoderFaithfulness DecoderFaithfulness.Roles DecoderFaithfulness.Example

/-- `f(uint256 amount, bytes memo)`, both `EqualTo`: strict. -/
example : checkCondition false root = some (.call 4 [.static, .dynamic]) := by decide +kernel

/-- A variant `Or` (two interpretations of `bytes data`) and a `Slice`:
    accepted only with `s = true`, where `data` gets the type `dynamic`. -/
example : checkCondition false root2 = none := by decide +kernel
example : checkCondition true root2 = some (.call 4 [.dynamic, .static]) := by decide +kernel

/-- `And[Matches[Pluck a, Pluck b], ZipEvery[(EqualTo, Pass)]]`. -/
example : checkCondition false root3 =
    some (.call 4 [.array .static, .array .static]) := by decide +kernel

/-- Backlog item 1: `f(uint256[] a, uint256[] b, uint256 c)` with
    `Matches[Pluck a, Pluck b, Zip, EqualTo(c)]`. Integrity accepts it and
    `evaluate` reads `c` from `a`; the check rejects it, because a Zip may
    only be the child of an `And`/`Or`. -/
def zipInMatches : Condition :=
  node .AbiEncoded .Matches [pluckA, pluckB, zipNode, node .Static .EqualTo []] 4

example : checkCondition false zipInMatches = none := by decide +kernel
example : checkCondition true zipInMatches = none := by decide +kernel

end ConditionCheck.Examples
