/**
 * Packs a flat condition array into the buffer the `...Packed` setters take
 * (`allowTargetPacked`, `allowFunctionPacked`, `allowFunctionGloballyPacked`).
 *
 * This transcribes `packSpec (transform fs)` from
 * packages/evm/formal/ConditionPacking: for every array that is `Packable`
 * (checked by `packableB`, part of `checkStored`), `ConditionPacker.pack`
 * produces exactly these bytes (`packBuffer_eq`), and `ConditionUnpacker`
 * returns the input tree (`pack_roundtrip`). Layout:
 *
 *   header      3 bytes  nodeCount << 8 | maxPluckValue
 *   nodes       4 bytes per node, BFS order:
 *                 encoding (3 bits) | operator (5) | childCount (10) |
 *                 inlinedSize (13) | hasCompValue (1)
 *   compValues  for each node with a compValue: length (2 bytes), bytes
 *
 * compValues are first rewritten as `ConditionPacker._transform` does:
 * `AbiEncoded` without one gets `0x0004`, and `EqualTo` on a node that is not
 * inlined drops its first word (the offset of `abi.encode`).
 *
 * Tested byte for byte against the Lean model of the packer and against
 * `ConditionPacker.pack` (packages/evm/test/formal/sdk-check.spec.ts).
 */
import {
  type ConditionFlatInput,
  type FlatNode,
  type Verdict,
  at,
  checkStored,
  childBounds,
  inlinedSizeFlat,
  isInlinedFlat,
  packableB,
  toFlatNodes,
  transformCv,
  Op,
} from "./checkStored"

const be = (n: number, k: number): number[] =>
  Array.from({ length: k }, (_, i) => Math.floor(n / 256 ** (k - 1 - i)) % 256)

/** The packed node word (`packedNode`). Fits in 32 bits for packable arrays. */
const nodeWord = (fs: readonly FlatNode[], i: number): number => {
  const f = at(fs, i)
  const inlinedSize = isInlinedFlat(fs, i) ? inlinedSizeFlat(fs, i) : 0
  return (
    f.paramType * 2 ** 29 +
    f.operator * 2 ** 24 +
    childBounds(fs, i)[1] * 2 ** 14 +
    inlinedSize * 2 +
    (f.compValue.length > 0 ? 1 : 0)
  )
}

/**
 * The packed buffer for `fs`. Throws if `fs` is not packable (the packer's
 * output would not decode to `fs`); use `checkAndPack` to also run the full
 * `checkStored`.
 */
export const packConditions = (fs: readonly FlatNode[]): Uint8Array => {
  if (!packableB(fs)) throw new Error("condition array is not packable")
  const g: FlatNode[] = fs.map((f, i) => ({
    ...f,
    compValue: transformCv(fs, i, f),
  }))
  const maxPluck = g.reduce(
    (acc, f) =>
      f.operator === Op.Pluck ? Math.max(acc, (f.compValue[0] ?? 0) + 1) : acc,
    0
  )
  const out: number[] = [...be(g.length * 256 + maxPluck, 3)]
  for (let i = 0; i < g.length; i++) out.push(...be(nodeWord(g, i), 4))
  for (const f of g) {
    if (f.compValue.length > 0)
      out.push(...be(f.compValue.length, 2), ...f.compValue)
  }
  return Uint8Array.from(out)
}

const toHex = (b: Uint8Array): `0x${string}` =>
  `0x${Array.from(b, (x) => x.toString(16).padStart(2, "0")).join("")}`

/**
 * Runs `checkStored` and packs. Returns the verdict and the buffer (hex) to
 * pass to a `...Packed` setter, or throws if the array is rejected.
 */
export const checkAndPack = (
  flat: readonly ConditionFlatInput[],
  s = true
): { verdict: Verdict; packed: `0x${string}` } => {
  const fs = toFlatNodes(flat)
  const verdict = checkStored(fs, s)
  if (verdict === undefined) {
    throw new Error("condition rejected by checkStored")
  }
  return { verdict, packed: toHex(packConditions(fs)) }
}
