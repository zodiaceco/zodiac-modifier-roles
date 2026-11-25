import assert from "node:assert/strict";
import { randomBytes } from "node:crypto";
import { after, describe, it } from "node:test";
import {
  encodeAbiParameters,
  parseAbiParameters,
  parseEventLogs,
  toHex,
  type Hex,
} from "viem";
import { network } from "hardhat";

import {
  Encoding,
  Operator,
  ConditionViolationStatus,
  flattenCondition,
} from "../utils.js";
import { createSetup } from "../setup.js";

const connection = await network.create();
const { viem, networkHelpers } = connection;
const { loadFixture, time } = networkHelpers;
const { setupTestContract, setupFn } = createSetup(connection);
const setupNoParam = setupFn("function fn()");
const setupOneParam = setupFn("function fn(uint256)");
const setupTwoParams = setupFn("function fn(uint256, uint256)");

const callWithinAllowance = (key: Hex) => ({
  paramType: Encoding.None,
  operator: Operator.CallWithinAllowance,
  compValue: key,
});
const equalTo = (value: bigint) => ({
  paramType: Encoding.Static,
  operator: Operator.EqualTo,
  compValue: encodeAbiParameters(parseAbiParameters("uint256"), [value]),
});
const randomKey = () => toHex(randomBytes(32));

describe("Operator - CallWithinAllowance", () => {
  after(async () => {
    await connection.close();
  });

  describe("as the root condition", () => {
    it("charges one per call until the balance runs out", async () => {
      const { roles, allowFunction, invoke } = await loadFixture(setupNoParam);
      const key = randomKey();
      await roles.write.setAllowance([key, 2n, 0n, 0n, 0n, 0n]);
      await allowFunction(flattenCondition(callWithinAllowance(key)));

      await viem.assertions.emitWithArgs(invoke(), roles, "ConsumeAllowance", [
        key,
        1n,
        1n,
      ]);
      await viem.assertions.emitWithArgs(invoke(), roles, "ConsumeAllowance", [
        key,
        1n,
        0n,
      ]);
      // the root node, and no payload: offset 0
      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke(),
        roles,
        "ConditionViolation",
        [ConditionViolationStatus.AllowanceExceeded, 0n, 0n],
      );
    });

    it("charges a pending refill, then refuses until the next one", async () => {
      const { roles, allowFunction, invoke } = await loadFixture(setupNoParam);
      const key = randomKey();
      // balance 0; one refill of 1 is due
      await roles.write.setAllowance([
        key,
        0n,
        0n,
        1n,
        1000n,
        BigInt(await time.latest()) - 1010n,
      ]);
      await allowFunction(flattenCondition(callWithinAllowance(key)));

      await viem.assertions.emitWithArgs(invoke(), roles, "ConsumeAllowance", [
        key,
        1n,
        0n,
      ]);
      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke(),
        roles,
        "ConditionViolation",
        [ConditionViolationStatus.AllowanceExceeded, 0n, 0n],
      );
    });

    it("on a whole target, charges calls with empty calldata too", async () => {
      const { roles, member, testContractAddress, allowTarget } =
        await loadFixture(setupTestContract);
      const key = randomKey();
      await roles.write.setAllowance([key, 2n, 0n, 0n, 0n, 0n]);
      await allowTarget(flattenCondition(callWithinAllowance(key)));
      const exec = (data: Hex) =>
        roles.write.execTransactionFromModule(
          [testContractAddress, 0n, data, 0],
          { account: member.account },
        );

      await viem.assertions.emitWithArgs(
        exec("0x"),
        roles,
        "ConsumeAllowance",
        [key, 1n, 1n],
      );
      await viem.assertions.emitWithArgs(
        exec("0x12345678"),
        roles,
        "ConsumeAllowance",
        [key, 1n, 0n],
      );
      await viem.assertions.revertWithCustomErrorWithArgs(
        exec("0x"),
        roles,
        "ConditionViolation",
        [ConditionViolationStatus.AllowanceExceeded, 0n, 0n],
      );
    });
  });

  describe("in logical combinations", () => {
    it("charges after the rest of an And passes", async () => {
      const { roles, allowFunction, invoke } = await loadFixture(setupOneParam);
      const key = randomKey();
      await roles.write.setAllowance([key, 1n, 0n, 0n, 0n, 0n]);
      await allowFunction(
        flattenCondition({
          paramType: Encoding.None,
          operator: Operator.And,
          children: [
            {
              paramType: Encoding.AbiEncoded,
              operator: Operator.Matches,
              children: [equalTo(42n)],
            },
            callWithinAllowance(key),
          ],
        }),
      );

      // And[0] -> Matches[1], CallWithinAllowance[2] -> EqualTo[3]
      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke(999n),
        roles,
        "ConditionViolation",
        [ConditionViolationStatus.ParameterNotAllowed, 3n, 4n],
      );
      await viem.assertions.emitWithArgs(
        invoke(42n),
        roles,
        "ConsumeAllowance",
        [key, 1n, 0n],
      );
      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke(42n),
        roles,
        "ConditionViolation",
        [ConditionViolationStatus.AllowanceExceeded, 2n, 0n],
      );
    });

    it("charges only the allowance of the Or branch that passes", async () => {
      const { roles, allowFunction, invoke } = await loadFixture(setupOneParam);
      const [key100, key200] = [randomKey(), randomKey()];
      await roles.write.setAllowance([key100, 1n, 0n, 0n, 0n, 0n]);
      await roles.write.setAllowance([key200, 1n, 0n, 0n, 0n, 0n]);
      const branch = (value: bigint, key: Hex) => ({
        paramType: Encoding.None,
        operator: Operator.And,
        children: [
          {
            paramType: Encoding.AbiEncoded,
            operator: Operator.Matches,
            children: [equalTo(value)],
          },
          callWithinAllowance(key),
        ],
      });
      await allowFunction(
        flattenCondition({
          paramType: Encoding.None,
          operator: Operator.Or,
          children: [branch(100n, key100), branch(200n, key200)],
        }),
      );

      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke(9999n),
        roles,
        "ConditionViolation",
        [ConditionViolationStatus.OrViolation, 0n, 0n],
      );

      // 200's branch passes: its allowance is charged, 100's is left alone
      await viem.assertions.emitWithArgs(
        invoke(200n),
        roles,
        "ConsumeAllowance",
        [key200, 1n, 0n],
      );
      assert.equal((await roles.read.allowances([key100]))[3], 1n);
      // 200's is used up, and 100's balance does not stand in for it
      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke(200n),
        roles,
        "ConditionViolation",
        [ConditionViolationStatus.OrViolation, 0n, 0n],
      );

      await viem.assertions.emitWithArgs(
        invoke(100n),
        roles,
        "ConsumeAllowance",
        [key100, 1n, 0n],
      );
      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke(100n),
        roles,
        "ConditionViolation",
        [ConditionViolationStatus.OrViolation, 0n, 0n],
      );
    });

    it("does not charge an Or branch that fails after it", async () => {
      const { roles, allowFunction, invoke } = await loadFixture(setupOneParam);
      const key = randomKey();
      await roles.write.setAllowance([key, 1n, 0n, 0n, 0n, 0n]);
      await allowFunction(
        flattenCondition({
          paramType: Encoding.None,
          operator: Operator.Or,
          children: [
            {
              // charges first, then fails for anything but 100
              paramType: Encoding.None,
              operator: Operator.And,
              children: [
                callWithinAllowance(key),
                {
                  paramType: Encoding.AbiEncoded,
                  operator: Operator.Matches,
                  children: [equalTo(100n)],
                },
              ],
            },
            {
              paramType: Encoding.AbiEncoded,
              operator: Operator.Matches,
              children: [
                { paramType: Encoding.Static, operator: Operator.Pass },
              ],
            },
          ],
        }),
      );

      const publicClient = await viem.getPublicClient();
      const hash = await invoke(999n);
      const receipt = await publicClient.waitForTransactionReceipt({ hash });
      const logs = parseEventLogs({
        abi: roles.abi,
        eventName: "ConsumeAllowance",
        logs: receipt.logs,
      });
      assert.equal(logs.length, 0);
      assert.equal((await roles.read.allowances([key]))[3], 1n);
      await viem.assertions.emitWithArgs(
        invoke(100n),
        roles,
        "ConsumeAllowance",
        [key, 1n, 0n],
      );
    });

    it("charges twice when it appears twice in an And", async () => {
      const { roles, allowFunction, invoke } = await loadFixture(setupNoParam);
      const key = randomKey();
      await roles.write.setAllowance([key, 3n, 0n, 0n, 0n, 0n]);
      await allowFunction(
        flattenCondition({
          paramType: Encoding.None,
          operator: Operator.And,
          children: [callWithinAllowance(key), callWithinAllowance(key)],
        }),
      );

      await viem.assertions.emitWithArgs(invoke(), roles, "ConsumeAllowance", [
        key,
        2n,
        1n,
      ]);
      // one left: the second charge fails
      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke(),
        roles,
        "ConditionViolation",
        [ConditionViolationStatus.AllowanceExceeded, 2n, 0n],
      );
    });

    it("charges the same allowance as a WithinAllowance on a parameter", async () => {
      const { roles, allowFunction, invoke } = await loadFixture(setupOneParam);
      const key = randomKey();
      await roles.write.setAllowance([key, 10n, 0n, 0n, 0n, 0n]);
      await allowFunction(
        flattenCondition({
          paramType: Encoding.None,
          operator: Operator.And,
          children: [
            {
              paramType: Encoding.AbiEncoded,
              operator: Operator.Matches,
              children: [
                {
                  paramType: Encoding.Static,
                  operator: Operator.WithinAllowance,
                  compValue: key,
                },
              ],
            },
            callWithinAllowance(key),
          ],
        }),
      );

      // 5 for the parameter, 1 for the call
      await viem.assertions.emitWithArgs(
        invoke(5n),
        roles,
        "ConsumeAllowance",
        [key, 6n, 4n],
      );
      // the parameter takes all 4: none left for the call
      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke(4n),
        roles,
        "ConditionViolation",
        [ConditionViolationStatus.AllowanceExceeded, 2n, 0n],
      );
    });

    it("as a tuple field inside And, charges once the field matches", async () => {
      const { roles, allowFunction, invoke } =
        await loadFixture(setupTwoParams);
      const key = randomKey();
      await roles.write.setAllowance([key, 1n, 0n, 0n, 0n, 0n]);
      // Matches[0] -> Pass[1], And[2] -> EqualTo[3], CallWithinAllowance[4]
      await allowFunction(
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            { paramType: Encoding.Static, operator: Operator.Pass },
            {
              paramType: Encoding.None,
              operator: Operator.And,
              children: [equalTo(42n), callWithinAllowance(key)],
            },
          ],
        }),
      );

      // the second parameter's word starts at 4 + 32
      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke(100n, 999n),
        roles,
        "ConditionViolation",
        [ConditionViolationStatus.ParameterNotAllowed, 3n, 36n],
      );
      await viem.assertions.emitWithArgs(
        invoke(100n, 42n),
        roles,
        "ConsumeAllowance",
        [key, 1n, 0n],
      );
      // nested in the field, it reports the field's offset (at the root, 0)
      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke(200n, 42n),
        roles,
        "ConditionViolation",
        [ConditionViolationStatus.AllowanceExceeded, 4n, 36n],
      );
    });
  });
});
