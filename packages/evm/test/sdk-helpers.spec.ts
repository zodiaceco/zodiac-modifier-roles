/**
 * SDK condition helpers against the contract: what `c.calldataMatches`,
 * `c.bitmask` and `c.gte` build is accepted by `allowFunction` (Integrity)
 * and evaluates as the helper describes.
 */
import { after, describe, it } from "node:test";
import { network } from "hardhat";
import { anyValue } from "@nomicfoundation/hardhat-viem-assertions/predicates";
import { encodeFunctionData, parseAbi } from "viem";
import type { Hex } from "viem";

import { createSetup } from "./setup.js";
import { ConditionViolationStatus, flattenCondition } from "./utils.js";

import { calldataMatches } from "../../sdk/src/main/target/authoring/c/matches.js";
import {
  bitmask,
  gte,
} from "../../sdk/src/main/target/authoring/c/comparison.js";
import { encodeKey } from "../../sdk/src/main/keys.js";

const connection = await network.create();
const { viem, networkHelpers } = connection;
const { loadFixture } = networkHelpers;
const { setupFn } = createSetup(connection);
const setupDynamicParam = setupFn("function fn(bytes)");

const bytes = "bytes" as any;

describe("SDK helpers on Roles", () => {
  after(async () => {
    await connection.close();
  });

  it("checks the selector of a nested call without parameters (4 bytes)", async () => {
    const { roles, allowFunction, invoke } =
      await loadFixture(setupDynamicParam);
    const condition = calldataMatches(
      [
        calldataMatches({
          targetAddress: "0x0000000000000000000000000000000000000001",
          selector: "0x12345678",
        }),
      ],
      ["bytes"],
    )();
    await allowFunction(flattenCondition(condition as any));

    await invoke("0x12345678");
    await viem.assertions.revertWithCustomError(
      invoke("0x12345679"),
      roles,
      "ConditionViolation",
    );
  });

  it("a mask padded to 15 bytes (v2 format) rejects the same 4 bytes", async () => {
    const { roles, allowFunction, invoke } =
      await loadFixture(setupDynamicParam);
    const z = "00".repeat(11);
    await allowFunction(
      flattenCondition({
        paramType: 5,
        operator: 5,
        children: [
          {
            paramType: 2,
            operator: 21,
            compValue: `0x0000ffffffff${z}12345678${z}`,
          },
        ],
      } as any),
    );
    await viem.assertions.revertWithCustomErrorWithArgs(
      invoke("0x12345678"),
      roles,
      "ConditionViolation",
      [ConditionViolationStatus.BitmaskOverflow, 1n, anyValue],
    );
  });

  it("selector and call allowance on a call without parameters", async () => {
    const { roles, allowFunction, invoke } =
      await loadFixture(setupDynamicParam);
    const key = encodeKey("calls") as Hex;
    await roles.write.setAllowance([key, 1n, 0n, 0n, 0n, 0n]);
    const condition = calldataMatches(
      [
        calldataMatches([], [], {
          selector: "0x12345678",
          callWithinAllowance: "calls",
        }),
      ],
      ["bytes"],
    )();
    await allowFunction(flattenCondition(condition as any));

    await viem.assertions.revertWithCustomError(
      invoke("0x12345679"),
      roles,
      "ConditionViolation",
    );
    await invoke("0x12345678");
    // the one call the allowance permits is used up
    await viem.assertions.revertWithCustomError(
      invoke("0x12345678"),
      roles,
      "ConditionViolation",
    );
  });

  it("a bitmask longer than 15 bytes", async () => {
    const { roles, allowFunction, invoke } =
      await loadFixture(setupDynamicParam);
    const prefix = "0x" + "ab".repeat(20);
    await allowFunction(
      flattenCondition({
        paramType: 5,
        operator: 5,
        children: [
          bitmask({ mask: "0x" + "ff".repeat(20), value: prefix })(bytes),
        ],
      } as any),
    );
    await invoke((prefix + "cdcd") as Hex);
    await viem.assertions.revertWithCustomError(
      invoke(("0x" + "ab".repeat(19) + "ac") as Hex),
      roles,
      "ConditionViolation",
    );
  });

  it("gte at the minimum is a Pass the contract accepts", async () => {
    const { allowFunction, invoke } = await loadFixture(setupDynamicParam);
    const innerAbi = parseAbi(["function g(uint256)"]);
    const condition = calldataMatches(
      [calldataMatches([gte(0)], ["uint256"])],
      ["bytes"],
    )();
    await allowFunction(flattenCondition(condition as any));
    await invoke(
      encodeFunctionData({ abi: innerAbi, functionName: "g", args: [0n] }),
    );
  });
});
