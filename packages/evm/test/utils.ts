import assert from "node:assert/strict";
import { encodePacked, isAddressEqual, parseEventLogs } from "viem";
import type { Abi, Address, Hex } from "viem";
import type { NetworkConnection } from "hardhat/types/network";
import type { GetContractReturnType } from "@nomicfoundation/hardhat-viem/types";
import type { ArtifactMap } from "hardhat/types/artifacts";

export type RolesContract = GetContractReturnType<ArtifactMap["Roles"]["abi"]>;

export type ConditionFlat = {
  parent: number;
  paramType: number;
  operator: number;
  compValue: Hex;
};

export const maxUint64 = 2n ** 64n - 1n;
export const maxUint128 = 2n ** 128n - 1n;

export interface MetaTransaction {
  to: Address;
  value: bigint | number;
  data: Hex;
  operation: number;
}

export enum Encoding {
  None = 0,
  Static,
  Dynamic,
  Tuple,
  Array,
  AbiEncoded,
  /* Entries bellow get aliased to None */
  EtherValue,
}

export enum Operator {
  // 00:    EMPTY EXPRESSION (default, always passes)
  //          paramType: Static / Dynamic / Tuple / Array
  //          ❓ children (only for paramType: Tuple / Array to describe their structure)
  //          🚫 compValue
  /* 00: */ Pass = 0,
  // ------------------------------------------------------------
  // 01-03: LOGICAL EXPRESSIONS
  //          paramType: None
  //          ✅ children
  //          🚫 compValue
  /* 01: */ And,
  /* 02: */ Or,
  /* 03: */ _Placeholder03,
  /* 04: */ Empty,
  // ------------------------------------------------------------
  // 05-12: COMPLEX EXPRESSIONS
  //          paramType: AbiEncoded / Tuple / Array,
  //          ✅ children
  //          🚫 compValue
  /* 05: */ Matches,
  /* 06: */ ArraySome,
  /* 07: */ ArrayEvery,
  /* 08: */ ArrayTailMatches,
  /* 09: */ _Placeholder09,
  /* 10: */ ZipSome, // paramType: None, compValue: 2 bytes (two pluck indexes)
  /* 11: */ ZipEvery, // paramType: None, compValue: 2 bytes (two pluck indexes)
  /* 12: */ _Placeholder12,
  // ------------------------------------------------------------
  // 13-14: EXTRACTION EXPRESSIONS
  //          ❓ children (at most one child, must resolve to Static)
  //          ✅ compValue
  /* 13: */ Slice, // paramType: Static / Dynamic, compValue: 3 bytes (2 bytes shift + 1 byte size, 1-32)
  /* 14: */ Pluck, // paramType: Static / EtherValue, compValue: 1 byte (index into pluckedValues, 0-255)
  // ------------------------------------------------------------
  // 15:    SPECIAL COMPARISON (without compValue)
  //          paramType: Static
  //          🚫 children
  //          🚫 compValue
  /* 15: */ EqualToAvatar,
  // ------------------------------------------------------------
  // 16-31: COMPARISON EXPRESSIONS
  //          paramType: Static / Dynamic / Tuple / Array / EtherValue
  //          ❓ children (only for paramType: Tuple / Array to describe their structure)
  //          ✅ compValue
  /* 16: */ EqualTo, // paramType: Static / Dynamic / Tuple / Array / EtherValue
  /* 17: */ GreaterThan, // paramType: Static / EtherValue
  /* 18: */ LessThan, // paramType: Static / EtherValue
  /* 19: */ SignedIntGreaterThan, // paramType: Static / EtherValue
  /* 20: */ SignedIntLessThan, // paramType: Static / EtherValue
  /* 21: */ Bitmask, // paramType: Static / Dynamic
  /* 22: */ Custom, // paramType: Static / Dynamic / Tuple / Array / EtherValue
  /* 23: */ WithinRatio, // paramType: None
  /* 24: */ _Placeholder24,
  /* 25: */ _Placeholder25,
  /* 26: */ _Placeholder26,
  /* 27: */ _Placeholder27,
  /* 28: */ WithinAllowance, // paramType: Static / EtherValue
  /* 29: */ _Placeholder29,
  /* 30: */ CallWithinAllowance, // paramType: None
  /* 31: */ _Placeholder31,
}

export enum ExecutionOptions {
  None = 0,
  Send,
  DelegateCall,
  Both,
}

export enum ConditionViolationStatus {
  Ok,
  /// Or condition not met
  OrViolation,
  /// Parameter value is not equal to allowed
  ParameterNotAllowed,
  /// Parameter value less than allowed
  ParameterLessThanAllowed,
  /// Parameter value greater than maximum allowed by role
  ParameterGreaterThanAllowed,
  /// Parameter value does not match
  ParameterNotAMatch,
  /// Array elements do not meet allowed criteria for every element
  NotEveryArrayElementPasses,
  /// Array elements do not meet allowed criteria for at least one element
  NoArrayElementPasses,
  /// Bitmask exceeded value length
  BitmaskOverflow,
  /// Bitmask not an allowed value
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
  AllowanceValueOverflow,
  // A Payload overflow was found by the Checker flow
  CalldataOverflow,
  RatioBelowMin,
  RatioAboveMax,
  // Calldata is not empty when it should be
  CalldataNotEmpty,
  // Leading bytes do not match expected value
  LeadingBytesNotAMatch,
  // Zipped arrays have different lengths
  ZippedArrayLengthMismatch,
  // No zipped element pair passes
  NoZippedElementPasses,
  // Not every zipped element pair passes
  NotEveryZippedElementPasses,
}

export const encodeMultisendPayload = (txs: MetaTransaction[]): Hex => {
  return ("0x" +
    txs
      .map((tx) =>
        encodePacked(
          ["uint8", "address", "uint256", "uint256", "bytes"],
          [
            tx.operation,
            tx.to,
            BigInt(tx.value),
            BigInt((tx.data.length - 2) / 2),
            tx.data,
          ],
        ).slice(2),
      )
      .join("")) as Hex;
};

interface Condition {
  paramType: Encoding;
  operator?: Operator;
  compValue?: string;
  children?: Condition[];
}

export function flattenCondition(root: Condition): ConditionFlat[] {
  let queue = [{ node: root, parent: 0 }];
  let result: ConditionFlat[] = [];

  for (let bfsOrder = 0; queue.length > 0; bfsOrder++) {
    const entry = queue.shift();
    assert.ok(entry);

    const { node, parent } = entry;

    result = [
      ...result,
      {
        parent,
        operator: node.operator || Operator.Pass,
        paramType: node.paramType,
        compValue: (node.compValue || "0x") as Hex,
      },
    ];

    queue = [
      ...queue,
      ...(node.children || []).map((child) => ({
        node: child,
        parent: bfsOrder,
      })),
    ];
  }

  return result;
}

/**
 * Packs conditions into bytes format for allowTarget/allowFunction.
 * Returns "0x" for empty conditions (the contract will use Pass condition).
 */
export async function packConditions(
  roles: RolesContract,
  conditions: ConditionFlat[],
): Promise<Hex> {
  if (conditions.length === 0) return "0x";
  return roles.read.packConditions([conditions]);
}

export function extractRevertData(error: unknown): Hex | undefined {
  let dataReason: Hex | undefined;
  let current: unknown = error;
  while (current && typeof current === "object") {
    const err = current as { data?: unknown; cause?: unknown };
    if (typeof err.data === "string" && err.data.startsWith("0x")) {
      dataReason = err.data as Hex;
    } else if (
      err.data &&
      typeof err.data === "object" &&
      "data" in err.data &&
      typeof (err.data as { data?: unknown }).data === "string" &&
      (err.data as { data: string }).data.startsWith("0x")
    ) {
      dataReason = (err.data as { data: string }).data as Hex;
    }
    current = err.cause;
  }
  return dataReason;
}

export async function assertRevertedWithoutReason(
  promise: Promise<unknown>,
): Promise<void> {
  try {
    await promise;
  } catch (error) {
    const data = extractRevertData(error);
    assert.equal(
      data,
      "0x",
      `Expected revert without reason (0x), got ${data ?? String(error)}`,
    );
    return;
  }
  assert.fail("Expected call to revert without reason, but it succeeded");
}

/** Asserts that the transaction emitted no `eventName` from `contract`. */
export async function assertNotEmitted(
  viem: NetworkConnection["viem"],
  txHash: Hex | Promise<Hex>,
  contract: { address: Address; abi: Abi },
  eventName: string,
): Promise<void> {
  const hash = await txHash;
  const publicClient = await viem.getPublicClient();
  const receipt = await publicClient.waitForTransactionReceipt({ hash });
  const logs = parseEventLogs({
    abi: contract.abi,
    eventName,
    logs: receipt.logs.filter((l) =>
      isAddressEqual(l.address, contract.address),
    ),
  });
  assert.equal(logs.length, 0, `Expected ${eventName} not to be emitted`);
}
