/**
 * SDK condition helpers against the contract: what `c.calldataMatches`,
 * `c.bitmask` and `c.gte` build is accepted by `allowFunction` (Integrity)
 * and evaluates as the helper describes.
 */
import { expect } from "chai";
import { Interface, ParamType } from "ethers";
import { network } from "hardhat";

import { createSetup } from "./setup.js";
import { anyValue } from "@nomicfoundation/hardhat-ethers-chai-matchers/withArgs";
import { ConditionViolationStatus, flattenCondition } from "./utils.js";

import { calldataMatches } from "../../sdk/src/main/target/authoring/c/matches.js";
import {
  bitmask,
  gte,
} from "../../sdk/src/main/target/authoring/c/comparison.js";
import { encodeKey } from "../../sdk/src/main/keys.js";

const connection = await network.create();
const { ethers, networkHelpers } = connection;
const { loadFixture } = networkHelpers;
const { setupDynamicParam } = createSetup(connection);

const bytes = ParamType.from("bytes");

describe("SDK helpers on Roles", () => {
  after(async () => {
    await connection.close();
  });

  it("checks the selector of a nested call without parameters (4 bytes)", async () => {
    const { allowFunction, invoke } = await loadFixture(setupDynamicParam);
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

    await expect(invoke("0x12345678")).to.not.be.revert(ethers);
    await expect(invoke("0x12345679")).to.be.revert(ethers);
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
    await expect(invoke("0x12345678"))
      .to.be.revertedWithCustomError(roles, "ConditionViolation")
      .withArgs(ConditionViolationStatus.BitmaskOverflow, 1, anyValue);
  });

  it("selector and call allowance on a call without parameters", async () => {
    const { roles, allowFunction, invoke } =
      await loadFixture(setupDynamicParam);
    const key = encodeKey("calls");
    await roles.setAllowance(key, 1, 0, 0, 0, 0);
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

    await expect(invoke("0x12345679")).to.be.revert(ethers);
    await expect(invoke("0x12345678")).to.not.be.revert(ethers);
    // the one call the allowance permits is used up
    await expect(invoke("0x12345678")).to.be.revert(ethers);
  });

  it("a bitmask longer than 15 bytes", async () => {
    const { allowFunction, invoke } = await loadFixture(setupDynamicParam);
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
    await expect(invoke(prefix + "cdcd")).to.not.be.revert(ethers);
    await expect(invoke("0x" + "ab".repeat(19) + "ac")).to.be.revert(ethers);
  });

  it("gte at the minimum is a Pass the contract accepts", async () => {
    const { allowFunction, invoke } = await loadFixture(setupDynamicParam);
    const inner = new Interface(["function g(uint256)"]);
    const condition = calldataMatches(
      [calldataMatches([gte(0)], ["uint256"])],
      ["bytes"],
    )();
    await allowFunction(flattenCondition(condition as any));
    await expect(invoke(inner.encodeFunctionData("g", [0]))).to.not.be.revert(
      ethers,
    );
  });
});
