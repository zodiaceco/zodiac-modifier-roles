import { chains } from "./chains"

export type ChainId = keyof typeof chains

export enum ExecutionOptions {
  None = 0,
  Send = 1,
  DelegateCall = 2,
  Both = 3,
}

export enum Clearance {
  None = 0,
  Target = 1,
  Function = 2,
}

export enum Encoding {
  None = 0,
  Static = 1,
  Dynamic = 2,
  Tuple = 3,
  Array = 4,
  AbiEncoded = 5,
  /** The transaction's ether value (`msg.value`); read as `None` on-chain. */
  EtherValue = 6,
}

export enum Operator {
  // 00:    EMPTY EXPRESSION (default, always passes)
  //          paramType: Static / Dynamic / Tuple / Array
  //          ❓ children (only for paramType: Tuple / Array to describe their structure)
  //          🚫 compValue
  Pass = 0,
  // ------------------------------------------------------------
  // 01-03: LOGICAL EXPRESSIONS
  //          paramType: None
  //          ✅ children
  //          🚫 compValue
  And = 1,
  Or = 2,
  // ------------------------------------------------------------
  // 04:    EMPTY CHECK (passes if data.length == 0)
  //          paramType: None
  //          🚫 children
  //          🚫 compValue
  Empty = 4,
  // ------------------------------------------------------------
  // 05-12: COMPLEX EXPRESSIONS
  //          paramType: AbiEncoded / Tuple / Array,
  //          ✅ children
  //          🚫 compValue (exception AbiEncoded.Matches uses compValue to define leading bytes)
  Matches = 5,
  ArraySome = 6,
  ArrayEvery = 7,
  ArrayTailMatches = 8,
  // ------------------------------------------------------------
  // 10-11: ZIP EXPRESSIONS
  //          paramType: None
  //          ✅ children (exactly one Tuple child, its children are the fields)
  //          ✅ compValue (one byte per field: the Pluck slot of the array zipped into it)
  ZipSome = 10,
  ZipEvery = 11,
  // ------------------------------------------------------------
  // 13-14: EXTRACTION EXPRESSIONS
  //          paramType: Dynamic
  //          ❓ children (at most one child, must resolve to Static)
  //          ✅ compValue (3 bytes: 2 bytes shift + 1 byte size, 1-32)
  Slice = 13,
  //          paramType: Static / EtherValue / Array
  //          ❓ children (Array: describe the element type)
  //          ✅ compValue (1 byte: the slot, 0-254)
  Pluck = 14,
  // ------------------------------------------------------------
  // 15:    SPECIAL COMPARISON (without compValue)
  //          paramType: Static
  //          🚫 children
  //          🚫 compValue
  EqualToAvatar = 15,
  // ------------------------------------------------------------
  // 16-31: COMPARISON EXPRESSIONS
  //          paramType: Static / Dynamic / Tuple / Array
  //          ❓ children (only for paramType: Tuple / Array to describe their structure)
  //          ✅ compValue
  EqualTo = 16, // paramType: Static / Dynamic / Tuple / Array
  GreaterThan = 17, // paramType: Static
  LessThan = 18, // paramType: Static
  SignedIntGreaterThan = 19, // paramType: Static
  SignedIntLessThan = 20, // paramType: Static
  Bitmask = 21, // paramType: Static / Dynamic
  Custom = 22, // paramType: Static / Dynamic / Tuple / Array
  WithinRatio = 23, // paramType: None
  WithinAllowance = 28, // paramType: Static
  CallWithinAllowance = 30, // paramType: None
}

export enum Status {
  Ok,
  /** Or condition not met */
  OrViolation,
  /** Parameter value is not equal to allowed */
  ParameterNotAllowed,
  /** Parameter value less than allowed */
  ParameterLessThanAllowed,
  /** Parameter value greater than maximum allowed by role */
  ParameterGreaterThanAllowed,
  /** Parameter value does not match */
  ParameterNotAMatch,
  /** Array elements do not meet allowed criteria for every element */
  NotEveryArrayElementPasses,
  /** Array elements do not meet allowed criteria for at least one element */
  NoArrayElementPasses,
  /** Bitmask exceeded value length */
  BitmaskOverflow,
  /** Bitmask not an allowed value */
  BitmaskNotAllowed,
  CustomConditionViolation,
  CustomConditionNotAContract,
  CustomConditionReverted,
  CustomConditionInvalidResult,
  PricingAdapterNotAContract,
  PricingAdapterReverted,
  PricingAdapterInvalidResult,
  PricingAdapterZeroPrice,
  AllowanceExceeded,
  /** No longer emitted: full-precision comparison reports AllowanceExceeded instead. Kept to preserve status codes. */
  AllowanceValueOverflow,
  /** Payload overflow found by Checker */
  CalldataOverflow,
  RatioBelowMin,
  RatioAboveMax,
  /** Calldata is not empty when it should be */
  CalldataNotEmpty,
  /** Leading bytes do not match expected value */
  LeadingBytesNotAMatch,
  /** Zipped arrays have different lengths */
  ZippedArrayLengthMismatch,
  /** No zipped element pair passes */
  NoZippedElementPasses,
  /** Not every zipped element pair passes */
  NotEveryZippedElementPasses,
}

export interface Role {
  key: `0x${string}`
  members: `0x${string}`[]
  targets: Target[]
  annotations: Annotation[]
  lastUpdate: number
}

export interface Target {
  address: `0x${string}`
  clearance: Clearance
  executionOptions: ExecutionOptions
  functions: Function[]
}

export interface Function {
  selector: `0x${string}`
  executionOptions: ExecutionOptions
  wildcarded: boolean
  condition?: Condition
}

export interface Condition {
  paramType: Encoding
  operator: Operator
  compValue?: `0x${string}`
  children?: readonly Condition[]
}

export interface Allowance {
  key: `0x${string}`
  refill: bigint
  maxRefill: bigint
  period: bigint
  balance: bigint
  timestamp: bigint
}

export interface Annotation {
  /** The URI serves as ID for the annotation. An http get request will be made to fetch the targeted permissions. */
  uri: string
  /** The OpenAPI schema that describes the API endpoint at uri. */
  schema: string
}

export interface RolesModifier {
  address: `0x${string}`
  owner: `0x${string}`
  avatar: `0x${string}`
  target: `0x${string}`
  roles: Role[]
  allowances: Allowance[]
  multiSendAddresses: `0x${string}`[]
}
