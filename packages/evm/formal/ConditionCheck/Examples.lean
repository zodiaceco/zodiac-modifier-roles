import ConditionCheck.Sound

/-!
# Examples

The decoder proof's example trees pass the check (so `checkCondition_sound`
applies to them), and the Zip-as-positional-child shape from the Integrity
backlog (item 1, a bypass that Integrity accepts) is rejected.
-/

namespace ConditionCheck.Examples
open ConditionCheck DecoderFaithfulness DecoderFaithfulness.Roles DecoderFaithfulness.Example

/-- `f(uint256 amount, bytes memo)`, both `EqualTo`: strict. A `Matches`
    root has an open type: the calldata may have more arguments. -/
example : checkCondition false root = some (.call 4 [.static, .dynamic] true) := by decide +kernel

/-- An `Or` of two interpretations of `bytes data` and a `Slice`. The
    interpretations (`(uint)` and `(uint, uint)`, same leading bytes) are
    prefixes of one call type, so even with `s = false` the tree is
    accepted: `data` must parse as the longer one, which both read
    correctly. -/
example : checkCondition false root2 =
    some (.call 4 [.call 4 [.static, .static] true, .static] true) := by decide +kernel
example : checkCondition true root2 =
    some (.call 4 [.call 4 [.static] true, .static] true) := by decide +kernel

/-- `And[Matches[Pluck a, Pluck b], ZipEvery[(EqualTo, Pass)]]`. -/
example : checkCondition false root3 =
    some (.call 4 [.array .static, .array .static] true) := by decide +kernel

/-- Backlog item 1: `f(uint256[] a, uint256[] b, uint256 c)` with
    `Matches[Pluck a, Pluck b, Zip, EqualTo(c)]`. Integrity accepts it and
    `evaluate` reads `c` from `a`; the check rejects it, because a Zip may
    only be the child of an `And`/`Or`. -/
def zipInMatches : Condition :=
  node .AbiEncoded .Matches [pluckA, pluckB, zipNode, node .Static .EqualTo []] 4

example : checkCondition false zipInMatches = none := by decide +kernel
example : checkCondition true zipInMatches = none := by decide +kernel

end ConditionCheck.Examples
