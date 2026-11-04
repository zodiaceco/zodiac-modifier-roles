# Target decoding: does the target see what Roles checked?

Roles reads calldata with its own walker (`AbiLocation`); the target
contract decodes the same bytes with solc's ABI decoder. Decoder
faithfulness proves Roles reads the right bytes on *canonically* encoded
calldata. This library is about every encoding the target accepts:
tails in any order, with gaps, shared or pointing anywhere, dirty
padding, trailing bytes.

```
cd packages/evm/formal
lake build TargetDecode
```

## What is proven

| Theorem                        | Statement                                                                                                                                                                                                       |
| ------------------------------ | --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `LP.det` (`Loose.lean`)        | **A value is determined by its location and shape.** `LP data l u` says following offsets from `l` (as a decoder does, with no assumption on the layout) reads `u`; two such values of one ABI shape are equal. |
| `canon_LP` (`Canon.lean`)      | The spec encoding is one of these layouts: a value whose spec encoding sits at `l` is read there.                                                                                                              |
| `region_det`                   | **A region holding the spec encoding of `v` is read as `v`**, whatever the rest of the calldata holds. For `EqualTo` on a dynamic value (Roles hashes the bytes it measured at the value's location): if they equal the pinned encoding, the target decoded exactly the pinned value. |
| `decodeCall_LP` (`Decoder.lean`) | **What solc accepts is loosely placed.** `decode` transcribes solc's parameter decoder (ABI coder v2, `memory` parameters): head and bounds checks, offsets up to `2^64 - 1`, length words, per-type word validation. When it accepts, each argument is `LP`-placed with its type's shape. |
| `decodeCall_LPCall` (`Walk.lean`) | What solc's decoder accepts is the calldata of a call in this sense (`LPCall`). |
| `target_locations` (`Walk.lean`) | **Roles' walker on any such layout.** The setting of decoder faithfulness (a tree that describes the call, Integrity's Zip rules), but the calldata is anything `LPCall` accepts. Every node the evaluator visits, Zip jumps included, is one of: a node describing component `u` (same index path) at the location the target reads `u` from; below a `Slice`, a window of the bytes the target decodes for `u`; non-structural; or (only with `s = true`, `InStrayL`) inside a variant branch that does not fit the `bytes` value it is evaluated on, where the branch itself is reached where the target reads that value; nothing more is promised below it. Soundness only: where Roles' `children` succeeds it is right; it may fail on layouts the target accepts (a tail at or before its head slot), which only makes Roles stricter. |
| `target_input` | **Comparison operands.** For a visited `EqualTo`, `GreaterThan`, `LessThan`, signed comparison, `WithinAllowance` or `Pluck`: on a static component the operand is exactly its spec encoding (or Roles reports overflow); on any component, **if the operand equals the spec operand of a value `v` of the component's shape, the target decoded `v`**. "Of the component's shape" is a hypothesis (`HasSh` of the same shape for `u` and `v`): encode `v` with the parameter's type. On a dynamic component the operand is a hash, modelled by its preimage (`expectInput_inj`), so this step trusts keccak256 collision resistance. So an `EqualTo` whose compValue is the spec encoding of `v` passes only when the target decoded `v`. Below a `Slice`: a window of the bytes the target decodes. |
| `target_bitmask` | `BitmaskChecker.check` returns `bitmaskSpec` of the bytes the target decodes: the word, the content of a `bytes` value (for nested calldata, the raw `bytes` the target receives), or a window of them below a `Slice`. |
| `ex_LPCall` | Non-vacuity: `f(bytes, bytes)` with the tails in reverse order satisfies the hypothesis, and is not the spec encoding. |
| `ex_full` (`NonVacuity.lean`) | Non-vacuity of the whole chain: on that layout solc's decoder model accepts, a strict (`s = false`) tree describes the arguments, the evaluator visits the second leaf at its tail, and `target_input` applies to it. |

All on Lean's standard axioms.

The full guarantee is for trees without variants, or checked with
`s = false` (`InStrayL.strict`). The SDK's check defaults to `s = true`,
which allows variants; for those, nodes inside a branch that does not fit
get only case (iv).

Below a `Slice`, the theorems give *some* window of the decoded bytes
(`IsWindow`), not which one. That it is `[shift, shift + size)` is tested
(the Slice end-to-end tests in `test/formal/lean-model.spec.ts`).

## Trusted base

- The transcriptions: solc's parameter decoder (`Decoder.lean`) and Roles'
  walker (shared with decoder faithfulness, `Roles.lean`). Both are tested
  (below, and `test/formal/lean-model.spec.ts`).
- keccak256 collision resistance, for `target_input` on dynamic values:
  Roles compares hashes, the model compares their preimages
  (`expectInput_inj`).
- The decoder faithfulness hypotheses (`Desc`, `RootOK`, `ZipOK`), as there.
- The Lean 4.35 kernel.

## Tested

`test/formal/integrity-gaps.spec.ts`, `GAP_TARGET=<n>` (needs the Lean
driver and the solc binary Hardhat caches; `GAP_SOLC` overrides its path):

- Random signatures (words of every width, `bytes`, tuples, arrays,
  nested calldata) and values, encoded in random valid but non-canonical
  layouts: tails reordered, gapped, shared; dirty padding; trailing words;
  offsets into the head; sometimes dirty narrow words; nested calldata
  laid out loosely as well; a quarter of the inputs malformed (large or
  off-by-one words, cuts, bit flips).
- Random conditions, a third of them with state that crosses nodes:
  Plucks of 2-3 arrays and a `ZipSome`/`ZipEvery` over them, or Plucks of
  two amounts (parameters or the ether value) and a `WithinRatio` whose
  bounds sit at their actual ratio.
- Trees take the SDK path: `checkAndPack` gates them (about a sixth are
  rejected), Roles evaluates the packed buffer. Integrity is not involved.
- A generated contract with two functions per signature (`calldata` and
  `memory` parameters) returns `abi.encode` of what it decoded, compiled
  with the legacy and the via-IR pipeline. Nested calldata goes to a
  second function of the same contract (its receiver), which decodes it
  the same way; its result replaces the nested calldata.
- **The decoder model is solc's.** The driver's `sd` query runs `decode`
  on the same calldata. It must give the same result as both `memory`
  builds, accept or reject. `calldata` parameters accept more: solc
  compares their nested offsets as signed numbers and adds them with
  wraparound, so a "negative" offset points backwards. Roles never
  follows such an offset (it fails closed), so this does not reach the
  agreement below.
- **Agreement.** Roles evaluates the crafted calldata (Integrity, pack,
  unpack, evaluate, with allowances and ether value) and the canonical
  calldata the target re-encoded. Whenever Roles passes the crafted
  calldata and the target accepts it, the canonical calldata must pass
  too, with the same allowance consumptions, or with consumptions some
  choice of `Or` branches gives (see below; tried by moving each branch
  of each `Or` to the front). Otherwise the case is a bypass: Roles let
  through values it rejects when they are encoded plainly.

Results: 10 seeds of 1,500 cases, four target builds each: no bypass.
Per seed, 190 to 215 calls pass Roles and are accepted by the target, among
them 23 to 49 with a Zip, 39 to 59 with a `WithinRatio` and 55 to 68 with
nested calldata. In all of them the target decoded values Roles accepts
canonically, with the same consumptions except once each in seeds 2, 4, 6
and 10, where the crafted calldata took another `Or` branch (below). 7 to
15 per seed are refused by Roles but accepted canonically (Roles is
stricter: a tail at or before its head slot, a dynamic value with dirty
padding compared by `EqualTo`). The Lean decoder agrees with both `memory`
builds on every case; `calldata` builds accept a few more, all with
backward offsets.

An earlier version (10 seeds, Integrity instead of the SDK check, no
Plucks, Zips or nested calldata) found the same: no bypass, two `Or`
branch choices.

## Finding: the caller can choose the `Or` branch

`Or` takes its first passing branch, and its allowance charges. A branch
fails when Roles reads a non-canonical layout more strictly than the
target (for example `EqualTo` on `bytes` with non-zero padding: Roles
compares the padded region, solc ignores padding). So the caller can make
an earlier branch fail and a later one apply, on values for which the
earlier branch holds. No operator negates, so the later branch's own
checks still hold for the decoded values: what the caller gains is the
choice among the branches that pass, and so which allowances are
charged. Found by the fuzz in `Or[And[charge K, EqualTo(bytes)], Bitmask]`:
the crafted calldata passed without charging `K`.

This needs non-standard encoding crafted on purpose, so only an
adversarial role member can do it; standard-encoded calls always take the
first passing branch. Documented in the `Or` section of
`packages/docs/content/general/conditions.mdx`: when branches overlap,
don't rely on an earlier branch's allowance being charged.

## Findings

- **Variant mode was vacuous.** A review of the theorem statements found
  that case (iv) (`InStrayL`) only required *some* bytes-like condition and
  *some* bytes value. So with `s = true` `target_locations`, `target_input`
  and `target_bitmask` held without their hypotheses. Case (iv) now
  requires a node of the tree that does not describe the bytes value, which
  the walk from the root reaches where the target reads that value, by the
  same index path; `d` is reached from it. `ReachedL` takes the top node's
  location (`root 0` in the theorems).

## Not covered (yet)

- **Combining the checks.** The theorems are per node: every check Roles
  makes is a check on what the target decodes, and passes only if it
  passes for those values (operators never negate). That the evaluator as
  a whole then passes the canonical calldata too, with some choice of
  `Or` branches, is the fuzz above (Plucks, Zips, `WithinRatio` and nested
  calldata included), not a theorem: a proof would relate two whole
  evaluations, with Pluck slots surviving failed branches and a
  nondeterministic `Or`, for little beyond the per-node argument. The
  branch choice is the finding above.
- **Targets with `calldata` parameters following a "negative" offset.**
  `decode` models solc's `memory` decoder; the `calldata` decoder also
  follows offsets that wrap around (above). Roles never follows such an
  offset, so it fails closed when it checks that component; the theorems
  just do not apply to such calldata.
- **compValues that are not spec encodings.** `target_input` concludes
  from "the operand is the spec encoding of `v`". The SDK writes spec
  encodings; a hand-made compValue with, say, dirty padding pins nothing.
- Nested calldata: proven (`LP` covers it) and fuzzed (decoded by a solc
  receiver), but the Lean decoder model does not decode it; the theorems
  assume whoever decodes it follows offsets. The decoder model never
  returns `.call` values, so the chain from `decodeCall_LPCall` to the
  `target_*` theorems does not apply to trees with nested `AbiEncoded`
  calldata; for those the theorems take `LPCall` as a hypothesis.
- Targets not compiled by solc (Vyper, hand-written decoders) and
  fallback functions that decode by hand.
- Custom checkers: they receive `(location, size)` of the raw bytes, not
  the decoded value; on a non-canonical layout these bytes need not be a
  spec encoding.
