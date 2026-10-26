/**
 * Splits off the outermost array dimension: `T[2][]` is a dynamic array of
 * `T[2]`, so `type` is `T[2]` and `fixedLength` is 0 (ABI and EIP-712 read
 * dimensions right to left).
 */
export function parseType(type: string) {
  const isAtomic = isAtomicType(type)
  const isDynamic = isDynamicType(type)
  const isStruct = isStructType(type)
  const isArray = isArrayType(type)
  const outer = type.match(/^(.*)\[(\d*)\]$/)

  return {
    type: isArray && outer ? outer[1] : type,
    isAtomic,
    isDynamic,
    isStruct,
    isArray,
    fixedLength: isArray && outer && outer[2] !== "" ? Number(outer[2]) : 0,
  }
}

/** The element type with every array dimension removed: `T[2][]` → `T`. */
export function baseType(type: string): string {
  return type.split("[")[0]
}

export function isNativeType(type: string): boolean {
  return isAtomicType(type) || isDynamicType(type)
}

export function isReferenceType(type: string): boolean {
  return isArrayType(type) || isStructType(type)
}

export function isAtomicType(type: string): boolean {
  return ATOMIC_TYPES[type] || false
}

export function isDynamicType(type: string): boolean {
  return DYNAMIC_TYPES[type] || false
}

export function isArrayType(type: string): boolean {
  return type.includes("[")
}

export function isStructType(type: string): boolean {
  return !isAtomicType(type) && !isDynamicType(type) && !isArrayType(type)
}

// EIP-712 atomic types: `uint<M>` / `int<M>` for M = 8, 16, ..., 256,
// `bytes<N>` for N = 1..32, `address` and `bool`.
const ATOMIC_TYPES: Record<string, boolean> = Object.fromEntries(
  [
    "bool",
    "address",
    ...Array.from({ length: 32 }, (_, i) => `int${8 * (i + 1)}`),
    ...Array.from({ length: 32 }, (_, i) => `uint${8 * (i + 1)}`),
    ...Array.from({ length: 32 }, (_, i) => `bytes${i + 1}`),
  ].map((type) => [type, true])
)

const DYNAMIC_TYPES: Record<string, boolean> = {
  string: true,
  bytes: true,
}
