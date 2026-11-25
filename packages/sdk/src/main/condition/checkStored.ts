/**
 * The check to run on a flat condition array before storing it with one of
 * the `...Packed` setters (`allowTargetPacked`, `allowFunctionPacked`,
 * `allowFunctionGloballyPacked`), which skip `Integrity` on-chain.
 *
 * It applies the rules of packages/evm/specs/integrity.md: an accepted
 * array is packed and unpacked unchanged, never reads an unwritten Pluck
 * slot, and is read by `evaluate` at the ABI spec location of every
 * parameter. integrityCases.test.ts runs the cases of that spec against it.
 *
 * Comments cite the rules of that spec by id, in its four sections: layout
 * (L1-L5, `packableB`), operators (O1-O19, `opsOk`), types (T1-T7,
 * `classifyNode` and `Checker`) and Pluck slots (P1-P5, `opsOk` and
 * `assigned`).
 *
 * Operators and encodings are taken as their numeric codes (`Operator.sol`,
 * `Encoding` in `Condition.sol`), including the v3 ones (`Pluck`, `ZipSome`,
 * `ZipEvery`, `EtherValue`, `CallWithinAllowance`).
 */

// ---------------------------------------------------------------------------
// Codes
// ---------------------------------------------------------------------------

export const Enc = {
  None: 0,
  Static: 1,
  Dynamic: 2,
  Tuple: 3,
  Array: 4,
  AbiEncoded: 5,
  EtherValue: 6,
} as const

export const Op = {
  Pass: 0,
  And: 1,
  Or: 2,
  Empty: 4,
  Matches: 5,
  ArraySome: 6,
  ArrayEvery: 7,
  ArrayTailMatches: 8,
  ZipSome: 10,
  ZipEvery: 11,
  Slice: 13,
  Pluck: 14,
  EqualToAvatar: 15,
  EqualTo: 16,
  GreaterThan: 17,
  LessThan: 18,
  SignedIntGreaterThan: 19,
  SignedIntLessThan: 20,
  Bitmask: 21,
  Custom: 22,
  WithinRatio: 23,
  WithinAllowance: 28,
  CallWithinAllowance: 30,
} as const

const OP_CODES = new Set<number>(Object.values(Op))

// ---------------------------------------------------------------------------
// Inputs
// ---------------------------------------------------------------------------

/** One `ConditionFlat` entry, compValue as bytes. */
export interface FlatNode {
  parent: number
  paramType: number
  operator: number
  compValue: Uint8Array
}

/** A `ConditionFlat` entry as the SDK builds it (compValue as hex). */
export interface ConditionFlatInput {
  parent: number
  paramType: number
  operator: number
  compValue?: string
}

const hexToBytes = (hex: string | undefined): Uint8Array => {
  const h = (hex ?? "0x").replace(/^0x/, "")
  if (h.length % 2 !== 0 || !/^[0-9a-fA-F]*$/.test(h)) {
    throw new Error(`invalid compValue: ${hex}`)
  }
  const out = new Uint8Array(h.length / 2)
  for (let i = 0; i < out.length; i++) {
    out[i] = parseInt(h.slice(2 * i, 2 * i + 2), 16)
  }
  return out
}

export const toFlatNodes = (flat: readonly ConditionFlatInput[]): FlatNode[] =>
  flat.map((f) => ({
    parent: f.parent,
    paramType: f.paramType,
    operator: f.operator,
    compValue: hexToBytes(f.compValue),
  }))

// ---------------------------------------------------------------------------
// Types (`Ty`, `K`)
// ---------------------------------------------------------------------------

/**
 * The ABI type a node describes (T1). An open tuple (`o`: a `Matches` whose
 * fields are not all static, T2) types the first fields only: the value may
 * have more. A call type is always open.
 */
export type Ty =
  | { k: "static" }
  | { k: "dynamic" }
  | { k: "tuple"; ts: Ty[]; o: boolean }
  | { k: "array"; t: Ty }
  | { k: "call"; lb: number; ts: Ty[]; o: boolean }

const STATIC: Ty = { k: "static" }
const DYNAMIC: Ty = { k: "dynamic" }

/** Canonical string, for equality. */
export const tyKey = (t: Ty): string => {
  switch (t.k) {
    case "static":
      return "S"
    case "dynamic":
      return "D"
    case "tuple":
      return `T(${[...t.ts.map(tyKey), ...(t.o ? [".."] : [])].join(",")})`
    case "array":
      return `A(${tyKey(t.t)})`
    case "call":
      return `C${t.lb}(${[...t.ts.map(tyKey), ...(t.o ? [".."] : [])].join(",")})`
  }
}

const tyEq = (a: Ty, b: Ty) => tyKey(a) === tyKey(b)

const isStatic = (t: Ty): boolean =>
  t.k === "static" || (t.k === "tuple" && t.ts.every(isStatic))

const isBytesLike = (t: Ty): boolean => t.k === "dynamic" || t.k === "call"

/** T5: type `a` fits type `b`. */
const fits = (a: Ty, b: Ty): boolean => {
  if (a.k === "static" && b.k === "static") return true
  // a call type is interchangeable with bytes (T2)
  if (isBytesLike(a) && isBytesLike(b)) return true
  if (a.k === "array" && b.k === "array") return fits(a.t, b.t)
  if (a.k === "tuple" && b.k === "tuple") {
    const prefix = b.ts.every((t, i) => i < a.ts.length && fits(a.ts[i], t))
    return b.o
      ? b.ts.length <= a.ts.length && prefix
      : !a.o && a.ts.length === b.ts.length && prefix
  }
  return false
}

/** T1: a type, or no type (`ns`): the node reads no calldata where it sits. */
type K = { k: "ty"; t: Ty } | { k: "ns" }

const kEq = (a: K, b: K) =>
  a.k === b.k && (a.k !== "ty" || tyEq(a.t, (b as { t: Ty }).t))

// ---------------------------------------------------------------------------
// The tree
// ---------------------------------------------------------------------------

interface Node {
  encoding: number
  operator: number
  children: Node[]
  leadingBytes: number
  compValue: Uint8Array
}

const DEFAULT_NODE: Node = {
  encoding: Enc.None,
  operator: Op.Pass,
  children: [],
  leadingBytes: 0,
  compValue: new Uint8Array(0),
}

const DEFAULT_FLAT: FlatNode = {
  parent: 0,
  paramType: Enc.None,
  operator: Op.Pass,
  compValue: new Uint8Array(0),
}

const cvByte = (cv: Uint8Array, k: number): number => cv[k] ?? 0

const wordVal = (bs: Uint8Array): number => {
  // only used on at most 4 bytes
  let v = 0
  for (const b of bs) v = v * 256 + b
  return v
}

const range = (n: number) => Array.from({ length: n }, (_, i) => i)

// ---------------------------------------------------------------------------
// Children, inlined and inlined size on the flat array
// ---------------------------------------------------------------------------

export const at = (fs: readonly FlatNode[], i: number): FlatNode =>
  fs[i] ?? DEFAULT_FLAT

/** `childBounds`: `[childStart, childCount]`. */
export const childBounds = (
  fs: readonly FlatNode[],
  index: number
): [number, number] => {
  let start = 0
  let count = 0
  for (let j = index + 1; j < fs.length; j++) {
    const parent = fs[j].parent
    if (parent === index) {
      if (count === 0) start = j
      count++
    } else if (parent > index) break
  }
  return [start, count]
}

const isZipOp = (op: number) => op === Op.ZipSome || op === Op.ZipEvery

/** L5: the node is inlined. */
export const isInlinedFlat = (
  fs: readonly FlatNode[],
  index: number
): boolean => {
  const { paramType: encoding, operator } = at(fs, index)
  // a Zip is not a value where it sits
  if (isZipOp(operator)) return false
  if (
    encoding === Enc.Dynamic ||
    encoding === Enc.Array ||
    encoding === Enc.AbiEncoded
  ) {
    return false
  }
  const [start, count] = childBounds(fs, index)
  // a Zip child is evaluated at the arrays in its slots: not counted
  return range(count).every(
    (i) => isZipOp(at(fs, start + i).operator) || isInlinedFlat(fs, start + i)
  )
}

/** L5: the size of an inlined node. */
export const inlinedSizeFlat = (
  fs: readonly FlatNode[],
  index: number
): number => {
  const { paramType: encoding, operator } = at(fs, index)
  if (isZipOp(operator)) return 0
  if (encoding === Enc.Static) return 32
  const [start, count] = childBounds(fs, index)
  const sizes = range(count).map((i) => inlinedSizeFlat(fs, start + i))
  const isNone = encoding === Enc.None
  let total = 0
  for (const childSize of sizes) {
    if (isNone && childSize > 0) return childSize
    total += childSize
  }
  return total
}

/** The children of node `i`: later nodes whose parent is `i`. */
const kids = (fs: readonly FlatNode[], i: number): number[] =>
  range(fs.length).filter((j) => i < j && at(fs, j).parent === i)

/** `ConditionPacker._transform` on one node. */
export const transformCv = (
  fs: readonly FlatNode[],
  i: number,
  f: FlatNode
): Uint8Array => {
  const cv =
    f.paramType === Enc.AbiEncoded && f.compValue.length === 0
      ? Uint8Array.from([0, 4])
      : f.compValue
  return f.operator === Op.EqualTo && !isInlinedFlat(fs, i) ? cv.slice(32) : cv
}

/** `rawTree (zeros 32) fs i`. */
const rawTree = (fs: readonly FlatNode[], i: number): Node => {
  const f = at(fs, i)
  const cv = transformCv(fs, i, f)
  return {
    encoding: f.paramType,
    operator: f.operator,
    children: kids(fs, i).map((j) => rawTree(fs, j)),
    leadingBytes: f.paramType === Enc.AbiEncoded ? wordVal(cv.slice(0, 2)) : 0,
    compValue:
      f.operator === Op.EqualToAvatar
        ? new Uint8Array(32)
        : f.paramType === Enc.AbiEncoded
          ? cv.slice(2)
          : cv,
  }
}

// ---------------------------------------------------------------------------
// 1. Layout (L1-L5). `packableB`: the array fits the packed format
// ---------------------------------------------------------------------------

export const packableB = (fs: readonly FlatNode[]): boolean => {
  const n = fs.length
  // L1
  if (!(0 < n && n <= 65535)) return false
  return range(n).every((j) => {
    const f = at(fs, j)
    const inl = isInlinedFlat(fs, j)
    return (
      // L2: the root has parent 0, every other parent comes first, and
      // parents do not decrease
      (0 < j ? f.parent < j : f.parent === 0) &&
      (!(0 < j && j + 1 < n) || f.parent <= at(fs, j + 1).parent) &&
      // L4
      f.compValue.length <= 65535 &&
      childBounds(fs, j)[1] <= 1023 &&
      // L5
      (!inl || inlinedSizeFlat(fs, j) <= 8191) &&
      // What the packer reads of a compValue. Implied by O8, O11 and O4;
      // here because `packConditions` runs `packableB` alone
      (f.operator !== Op.Pluck ||
        (f.compValue.length > 0 && cvByte(f.compValue, 0) <= 254)) &&
      (!(f.operator === Op.EqualTo && !inl) || 32 <= f.compValue.length) &&
      (f.paramType !== Enc.AbiEncoded ||
        (f.compValue.length !== 1 && f.operator !== Op.EqualTo))
    )
  })
}

// ---------------------------------------------------------------------------
// 2. Operators (O1-O19). `opsOk`: the rules of each operator, and P1
// ---------------------------------------------------------------------------

const findPluck = (fs: readonly FlatNode[], k: number): number | undefined =>
  range(fs.length).find(
    (i) =>
      at(fs, i).operator === Op.Pluck && cvByte(at(fs, i).compValue, 0) === k
  )

const adapterBlob = (cv: Uint8Array, off: number): number | undefined => {
  const len = cvByte(cv, off)
  if (len !== 0 && len < 20) return undefined
  if (off + 1 + len > cv.length) return undefined
  return off + 1 + len
}

/** O15: the compValue of a WithinRatio. */
const withinRatioCvOk = (cv: Uint8Array): boolean => {
  const len = cv.length
  const first = len > 12 ? adapterBlob(cv, 12) : 12
  const blobs =
    first === undefined
      ? undefined
      : len > first
        ? adapterBlob(cv, first)
        : first
  if (!(12 <= len && len <= 65535 && blobs === len)) return false
  if (!(cvByte(cv, 1) <= 27 && cvByte(cv, 3) <= 27)) return false
  const minR = wordVal(cv.slice(4, 8))
  const maxR = wordVal(cv.slice(8, 12))
  return (
    !(minR === 0 && maxR === 0) && (minR === 0 || maxR === 0 || minR <= maxR)
  )
}

const opOk = (fs: readonly FlatNode[], j: number): boolean => {
  const f = at(fs, j)
  const e = f.paramType
  const cv = f.compValue
  const len = cv.length
  const cc = childBounds(fs, j)[1]
  const ch0 = kids(fs, j)[0] ?? 0
  // O18 (a Pass or Custom on None: the cases below and `classifyNode`)
  const leafRule =
    !(
      ((e === Enc.Static || e === Enc.Dynamic || e === Enc.EtherValue) &&
        f.operator !== Op.Slice) ||
      (e === Enc.AbiEncoded && f.operator === Op.Pass)
    ) || cc === 0
  const pluckEnc = (k: number, ok: (e: number) => boolean) => {
    const i = findPluck(fs, k)
    return i === undefined || ok(at(fs, i).paramType)
  }
  const wordLike = (e: number) => e === Enc.Static || e === Enc.EtherValue
  if (!leafRule) return false
  switch (f.operator) {
    case Op.Pass: // O1
      return len === 0
    case Op.And:
    case Op.Or: // O2
      return e === Enc.None && len === 0 && cc >= 1
    case Op.Empty: // O3
      return e === Enc.None && len === 0 && cc === 0
    case Op.Matches: {
      // O4
      if (!(e === Enc.Tuple || e === Enc.Array || e === Enc.AbiEncoded))
        return false
      if (e !== Enc.AbiEncoded) return len === 0
      const lb = cvByte(cv, 0) * 256 + cvByte(cv, 1)
      return len === 0 || len === 2 || (len === 2 + lb && lb <= 32)
    }
    case Op.ArraySome:
    case Op.ArrayEvery: // O5
      return e === Enc.Array && len === 0 && cc === 1
    case Op.ArrayTailMatches: // O6
      return e === Enc.Array && len === 0
    case Op.ZipSome:
    case Op.ZipEvery: // O7
      return (
        e === Enc.None &&
        len >= 1 &&
        cc === 1 &&
        at(fs, ch0).paramType === Enc.Tuple &&
        at(fs, ch0).operator === Op.Matches &&
        childBounds(fs, ch0)[1] === len &&
        // a slot may repeat: its array is zipped with itself
        range(len).every((k) => {
          const i = findPluck(fs, cvByte(cv, k))
          return i !== undefined && at(fs, i).paramType === Enc.Array
        })
      )
    case Op.Slice: // O9 (that the child is a leaf: `sliceOk`)
      return (
        (e === Enc.Static || e === Enc.Dynamic) &&
        len === 3 &&
        1 <= cvByte(cv, 2) &&
        cvByte(cv, 2) <= 32 &&
        cc === 1 &&
        at(fs, ch0).paramType === Enc.Static
      )
    case Op.Pluck: // O8
      return (
        (e === Enc.Static || e === Enc.EtherValue || e === Enc.Array) &&
        len === 1 &&
        cvByte(cv, 0) !== 255
      )
    case Op.EqualToAvatar: // O10
      return e === Enc.Static && len === 0
    case Op.EqualTo: // O11
      switch (e) {
        case Enc.Static:
        case Enc.EtherValue:
          return len === 32
        case Enc.Dynamic:
          return 64 <= len && len <= 65535
        case Enc.Tuple:
        case Enc.Array:
          // a static tuple's encoding has exactly its size: a longer
          // compValue would be hashed and compared with a word the caller
          // chooses
          return isInlinedFlat(fs, j)
            ? len === inlinedSizeFlat(fs, j)
            : 64 <= len && len <= 65535
        default:
          return false
      }
    case Op.GreaterThan:
    case Op.LessThan:
    case Op.SignedIntGreaterThan:
    case Op.SignedIntLessThan: // O12
      return wordLike(e) && len === 32
    case Op.Bitmask: // O13
      return (
        (e === Enc.Static || e === Enc.Dynamic) &&
        4 <= len &&
        len <= 65535 &&
        len % 2 === 0
      )
    case Op.Custom: // O14
      return (
        // on None the adapter is given no operand, and the node no children
        // (O18)
        ((e === Enc.None && cc === 0) ||
          e === Enc.Static ||
          e === Enc.Dynamic ||
          e === Enc.Tuple ||
          e === Enc.Array ||
          e === Enc.EtherValue) &&
        20 <= len &&
        len <= 65535
      )
    case Op.WithinRatio: // O15
      return (
        e === Enc.None &&
        withinRatioCvOk(cv) &&
        cc === 0 &&
        pluckEnc(cvByte(cv, 0), wordLike) &&
        pluckEnc(cvByte(cv, 2), wordLike)
      )
    case Op.WithinAllowance: // O16
      return (
        wordLike(e) &&
        len <= 65535 &&
        (len === 32 || len === 34 || 54 <= len) &&
        (len <= 32 || (cvByte(cv, 32) <= 27 && cvByte(cv, 33) <= 27))
      )
    case Op.CallWithinAllowance: // O17
      return e === Enc.None && len === 32 && cc === 0
    default:
      // O19
      return false
  }
}

export const opsOk = (fs: readonly FlatNode[]): boolean =>
  range(fs.length).every((j) => opOk(fs, j)) &&
  // P1: no two Plucks name the same slot
  range(fs.length).every((i) =>
    range(fs.length).every(
      (i2) =>
        i2 <= i ||
        at(fs, i).operator !== Op.Pluck ||
        at(fs, i2).operator !== Op.Pluck ||
        cvByte(at(fs, i).compValue, 0) !== cvByte(at(fs, i2).compValue, 0)
    )
  )

// ---------------------------------------------------------------------------
// 4. Pluck slots (P2-P5). `assigned`: slots are written before they are read
// ---------------------------------------------------------------------------

type Slots = ReadonlySet<number>

/** The set a node returns given the set `A` it receives, or `undefined`. */
const assigned = (c: Node, A: Slots): Slots | undefined => {
  const op = c.operator
  const cv = c.compValue
  const cs = c.children
  // P2
  if (op === Op.Pluck) return new Set([...A, cvByte(cv, 0)])
  // P3
  if (op === Op.WithinRatio) {
    return A.has(cvByte(cv, 0)) && A.has(cvByte(cv, 2)) ? A : undefined
  }
  if (op === Op.ZipSome || op === Op.ZipEvery) {
    // P3
    if (!range(cv.length).every((i) => A.has(cvByte(cv, i)))) return undefined
    // P4, as are the cases that follow
    const fields = (cs[0] ?? DEFAULT_NODE).children
    const r = assignedSeq(fields, A)
    return r === undefined ? undefined : op === Op.ZipSome ? r : A
  }
  if (op === Op.Or) return assignedOr(cs, A)
  if (op === Op.ArraySome || op === Op.ArrayEvery) {
    const r = assigned(cs[0] ?? DEFAULT_NODE, A)
    return r === undefined ? undefined : op === Op.ArraySome ? r : A
  }
  if (op === Op.And || op === Op.Matches || op === Op.ArrayTailMatches) {
    return assignedSeq(cs, A)
  }
  if (op === Op.Slice) return cs.length === 0 ? A : assigned(cs[0], A)
  // P5
  return A
}

const assignedSeq = (cs: readonly Node[], A: Slots): Slots | undefined => {
  let cur: Slots | undefined = A
  for (const c of cs) {
    cur = assigned(c, cur)
    if (cur === undefined) return undefined
  }
  return cur
}

const assignedOr = (cs: readonly Node[], A: Slots): Slots | undefined => {
  if (cs.length === 0) return new Set()
  let acc: Slots | undefined
  for (const c of cs) {
    const a = assigned(c, A)
    if (a === undefined) return undefined
    acc = acc === undefined ? a : new Set([...acc].filter((k) => a.has(k)))
  }
  return acc
}

// ---------------------------------------------------------------------------
// 3. Types (T1-T7). `classify`, `checkCondition`: the type of every node
// ---------------------------------------------------------------------------

/** The navigating operators (see the spec's terms). */
const NAV_OPS = new Set<number>([
  Op.And,
  Op.Or,
  Op.Matches,
  Op.ArraySome,
  Op.ArrayEvery,
  Op.ArrayTailMatches,
  Op.Slice,
  Op.ZipSome,
  Op.ZipEvery,
])
const isNavOp = (op: number) => NAV_OPS.has(op)
const isArrayOp = (op: number) =>
  op === Op.Matches ||
  op === Op.ArraySome ||
  op === Op.ArrayEvery ||
  op === Op.ArrayTailMatches

const leafOk = (cs: readonly Node[], op: number) =>
  cs.length === 0 && !isNavOp(op)

const sliceSize = (cv: Uint8Array) => cvByte(cv, 2)

/** O9: a `Slice` over one `Static` leaf whose operator does not navigate. */
const sliceOk = (
  op: number,
  cs: readonly Node[],
  cv: Uint8Array,
  ks: readonly K[]
) =>
  op === Op.Slice &&
  1 <= sliceSize(cv) &&
  sliceSize(cv) <= 32 &&
  cs.length === 1 &&
  cs[0].encoding === Enc.Static &&
  leafOk(cs[0].children, cs[0].operator) &&
  ks.length === 1 &&
  kEq(ks[0], { k: "ty", t: STATIC })

const allTy = (ks: readonly K[]): Ty[] | undefined =>
  ks.every((k) => k.k === "ty") ? ks.map((k) => (k as { t: Ty }).t) : undefined

const fitsKind = (t: Ty, k: K) => k.k !== "ty" || fits(t, k.t)

/** T3, T4: the first child type that fits the type of every typed child. */
const meetOf = (ks: readonly K[]): Ty | undefined => {
  for (const k of ks)
    if (k.k === "ty" && ks.every((k2) => fitsKind(k.t, k2))) return k.t
  return undefined
}

/** T2: an exact node, a Pass whose children are all exact. */
const exactTy = (c: Node): boolean =>
  c.operator === Op.Pass && c.children.every(exactTy)

/** T4: the kind of a logical node. */
const logicalKind = (ks: readonly K[]): K | undefined => {
  if (ks.length === 0) return undefined
  if (ks.every((k) => k.k === "ns")) return { k: "ns" }
  const t = meetOf(ks)
  if (t === undefined) return undefined
  return { k: "ty", t }
}

/** T1: the kind of a node, given the kinds `ks` of its children. */
const classifyNode = (
  e: number,
  op: number,
  cs: readonly Node[],
  lb: number,
  cv: Uint8Array,
  ks: readonly K[]
): K | undefined => {
  switch (e) {
    case Enc.Static:
      return leafOk(cs, op) || sliceOk(op, cs, cv, ks)
        ? { k: "ty", t: STATIC }
        : undefined
    case Enc.Dynamic:
      return leafOk(cs, op) || sliceOk(op, cs, cv, ks)
        ? { k: "ty", t: DYNAMIC }
        : undefined
    case Enc.Tuple: {
      // T2: at least one child; below an operator that does not navigate,
      // exact children only
      if (
        !(
          cs.length > 0 &&
          ((!isNavOp(op) && cs.every(exactTy)) || op === Op.Matches)
        )
      )
        return undefined
      // T2: no child without a type
      const ts = allTy(ks)
      // T2: open if a Matches that is not static
      const o = op === Op.Matches && !(ts ?? []).every(isStatic)
      return ts && { k: "ty", t: { k: "tuple", ts, o } }
    }
    case Enc.Array: {
      // T2: below an operator that does not navigate, one exact child
      if (
        !(
          (!isNavOp(op) && cs.length === 1 && cs.every(exactTy)) ||
          isArrayOp(op)
        )
      )
        return undefined
      // T2: at least one child, none without a type
      if (ks.length === 0 || !ks.every((k) => k.k === "ty")) return undefined
      // T3
      const t = meetOf(ks)
      return t && { k: "ty", t: { k: "array", t } }
    }
    case Enc.AbiEncoded: {
      // O18: a Pass has no children. T2: a call is interchangeable with bytes
      if (op === Op.Pass) {
        return cs.length === 0 ? { k: "ty", t: DYNAMIC } : undefined
      }
      // T2: a Matches may list no parameters, none without a type
      if (op !== Op.Matches) return undefined
      const ts = allTy(ks)
      return ts && { k: "ty", t: { k: "call", lb, ts, o: true } }
    }
    case Enc.None:
      // T1: a Zip reads the arrays in its slots, nothing where it sits
      if (isZipOp(op)) {
        return ks.length === 1 && ks[0].k === "ty" && ks[0].t.k === "tuple"
          ? { k: "ns" }
          : undefined
      }
      // T1, O18
      if (leafOk(cs, op)) return { k: "ns" }
      if (op === Op.And || op === Op.Or) return logicalKind(ks)
      return undefined
    case Enc.EtherValue:
      return leafOk(cs, op) ? { k: "ns" } : undefined
    default:
      return undefined
  }
}

/** An SDK condition (as `normalizeCondition` handles it). */
export interface ConditionInput {
  paramType: number
  operator: number
  compValue?: string
  children?: readonly ConditionInput[]
}

/** The raw tree of an SDK condition. */
const nodeOf = (c: ConditionInput): Node => {
  const cv = hexToBytes(c.compValue)
  const abi = c.paramType === Enc.AbiEncoded
  return {
    encoding: c.paramType,
    operator: c.operator,
    children: (c.children ?? []).map(nodeOf),
    leadingBytes: abi ? (cv.length === 0 ? 4 : wordVal(cv.slice(0, 2))) : 0,
    compValue: abi ? cv.slice(2) : cv,
  }
}

/**
 * The children of a merged `Or` (`normalizeCondition`'s push-down): every
 * one describes a parameter of exactly the same type, so the merged node
 * reads the value as each branch did.
 */
export const siblingsSameType = (cs: readonly ConditionInput[]): boolean => {
  // unknown codes have no raw tree
  const known = (c: ConditionInput): boolean =>
    Number.isInteger(c.paramType) &&
    0 <= c.paramType &&
    c.paramType <= 6 &&
    OP_CODES.has(c.operator) &&
    (c.children ?? []).every(known)
  if (!cs.every(known)) return false
  const checker = new Checker()
  const ts: Ty[] = []
  for (const c of cs) {
    let k: K | undefined
    try {
      k = checker.classify(nodeOf(c))
    } catch {
      return false
    }
    if (k === undefined || k.k !== "ty") return false
    ts.push(k.t)
  }
  return ts.length > 0 && ts.every((t) => tyEq(t, ts[0]))
}

class Checker {
  private memo = new Map<Node, K | undefined>()

  classify(c: Node): K | undefined {
    if (this.memo.has(c)) return this.memo.get(c)
    const ks: K[] = []
    let r: K | undefined
    let ok = true
    for (const ch of c.children) {
      const k = this.classify(ch)
      if (k === undefined) {
        ok = false
        break
      }
      ks.push(k)
    }
    if (ok) {
      r = classifyNode(
        c.encoding,
        c.operator,
        c.children,
        c.leadingBytes,
        c.compValue,
        ks
      )
    }
    this.memo.set(c, r)
    return r
  }

  /** T6 */
  rootOk(c: Node): boolean {
    return (
      c.encoding === Enc.AbiEncoded ||
      (c.encoding === Enc.None &&
        (c.operator === Op.And || c.operator === Op.Or) &&
        c.children.every((ch) => {
          const k = this.classify(ch)
          return this.rootOk(ch) || k?.k === "ns"
        }))
    )
  }

  /** T7 */
  zipCheck(root: Node): boolean {
    const all = nodes(root)
    return all.every((z) => {
      if (!(z.operator === Op.ZipSome || z.operator === Op.ZipEvery))
        return true
      const fields = (z.children[0] ?? DEFAULT_NODE).children
      return range(fields.length).every((f) =>
        all.every((pk) => {
          if (
            !(
              pk.operator === Op.Pluck &&
              cvByte(pk.compValue, 0) === cvByte(z.compValue, f)
            )
          ) {
            return true
          }
          if (pk.encoding !== Enc.Array) return false
          const k1 = this.classify(pk.children[0] ?? DEFAULT_NODE)
          const k2 = this.classify(fields[f] ?? DEFAULT_NODE)
          return k1?.k === "ty" && k2?.k === "ty" && fits(k1.t, k2.t)
        })
      )
    })
  }

  checkCondition(root: Node): Ty | undefined {
    const k = this.classify(root)
    if (k?.k !== "ty") return undefined
    return this.rootOk(root) && this.zipCheck(root) ? k.t : undefined
  }
}

const nodes = (c: Node): Node[] => [c, ...c.children.flatMap(nodes)]

// ---------------------------------------------------------------------------
// `checkStored`
// ---------------------------------------------------------------------------

export type Verdict =
  /** The root describes calldata of this type. */
  | { kind: "typed"; type: Ty }
  /** The root reads no calldata (e.g. only `EtherValue` checks). */
  | { kind: "noCalldata" }

/**
 * Returns the verdict if `fs` may be stored with a `...Packed` setter, or
 * `undefined`.
 */
export const checkStored = (fs: readonly FlatNode[]): Verdict | undefined => {
  // L3, O19: known codes. A fractional or negative parent would attach the
  // node nowhere, and the check would skip it
  const nat = (x: number) => Number.isInteger(x) && x >= 0
  if (
    !fs.every(
      (f) =>
        nat(f.parent) &&
        nat(f.paramType) &&
        f.paramType <= 6 &&
        OP_CODES.has(f.operator)
    )
  ) {
    return undefined
  }
  if (!packableB(fs) || !opsOk(fs)) return undefined
  const tree = rawTree(fs, 0)
  if (assigned(tree, new Set()) === undefined) return undefined
  const checker = new Checker()
  const t = checker.checkCondition(tree)
  if (t !== undefined) return { kind: "typed", type: t }
  return checker.classify(tree)?.k === "ns" ? { kind: "noCalldata" } : undefined
}

/** `checkStored` on `ConditionFlat` entries with hex compValues. */
export const checkStoredConditions = (
  flat: readonly ConditionFlatInput[]
): Verdict | undefined => checkStored(toFlatNodes(flat))
