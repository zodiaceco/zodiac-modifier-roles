import assert from "node:assert/strict";
import { randomBytes } from "node:crypto";
import { after, describe, it } from "node:test";
import { anyValue } from "@nomicfoundation/hardhat-viem-assertions/predicates";
import {
  encodeAbiParameters,
  encodeFunctionData,
  encodePacked,
  parseAbi,
  parseAbiParameters,
  parseEther,
  parseUnits,
  toFunctionSelector,
  toHex,
  zeroAddress,
  type Account,
  type Address,
  type Hex,
} from "viem";

import { network } from "hardhat";

import {
  Encoding,
  ExecutionOptions,
  Operator,
  ConditionViolationStatus,
  packConditions,
  type RolesContract,
} from "../utils.js";
import { createSetup } from "../setup.js";

const connection = await network.create();
const { viem, networkHelpers } = connection;
const { loadFixture, time } = networkHelpers;
const { setupTestContract, setupFn } = createSetup(connection);
const setupOneParam = setupFn("function fn(uint256)");
const setupTwoParams = setupFn("function fn(uint256, uint256)");

describe("Operator - WithinAllowance", () => {
  after(async () => {
    await connection.close();
  });

  function setAllowance(
    roles: RolesContract,
    allowanceKey: Hex,
    {
      balance,
      maxRefill,
      refill,
      period,
      timestamp,
    }: {
      balance: bigint | number;
      maxRefill?: bigint | number;
      refill: bigint | number;
      period: bigint | number;
      timestamp: bigint | number;
    },
    account?: Address | Account,
  ) {
    return roles.write.setAllowance(
      [
        allowanceKey,
        BigInt(balance),
        BigInt(maxRefill ?? 0),
        BigInt(refill),
        BigInt(period),
        BigInt(timestamp),
      ],
      account ? { account } : undefined,
    );
  }

  describe("WithinAllowance - Check", () => {
    it("passes a check with enough balance available and no refill (interval = 0)", async () => {
      const { owner, roles, allowFunction, invoke } =
        await loadFixture(setupOneParam);

      const allowanceKey =
        "0x0000000000000000000000000000000000000000000000000000000000000001";

      await setAllowance(
        roles,
        allowanceKey,
        {
          balance: 1000,
          period: 0,
          refill: 0,
          timestamp: 0,
        },
        owner.account,
      );

      await allowFunction([
        {
          parent: 0,
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          compValue: "0x",
        },
        {
          parent: 0,
          paramType: Encoding.Static,
          operator: Operator.WithinAllowance,
          compValue: encodeAbiParameters(parseAbiParameters("bytes32"), [
            allowanceKey,
          ]),
        },
      ]);

      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke(1001n),
        roles,
        "ConditionViolation",
        [
          ConditionViolationStatus.AllowanceExceeded,
          1n, // WithinAllowance node
          anyValue,
        ],
      );

      await invoke(1000n);
      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke(1n),
        roles,
        "ConditionViolation",
        [
          ConditionViolationStatus.AllowanceExceeded,
          1n, // WithinAllowance node
          anyValue,
        ],
      );
    });
    it("passes a check with only from balance and refill configured", async () => {
      const { roles, owner, allowFunction, invoke } =
        await loadFixture(setupOneParam);

      const allowanceKey = toHex(randomBytes(32));

      await allowFunction([
        {
          parent: 0,
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          compValue: "0x",
        },
        {
          parent: 0,
          paramType: Encoding.Static,
          operator: Operator.WithinAllowance,
          compValue: encodeAbiParameters(parseAbiParameters("bytes32"), [
            allowanceKey,
          ]),
        },
      ]);

      const timestamp = await time.latest();
      await setAllowance(
        roles,
        allowanceKey,
        {
          balance: 333,
          period: 1000,
          refill: 100,
          timestamp: timestamp,
        },
        owner.account,
      );

      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke(334n),
        roles,
        "ConditionViolation",
        [
          ConditionViolationStatus.AllowanceExceeded,
          1n, // WithinAllowance node
          anyValue,
        ],
      );
      await invoke(333n);
      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke(1n),
        roles,
        "ConditionViolation",
        [
          ConditionViolationStatus.AllowanceExceeded,
          1n, // WithinAllowance node
          anyValue,
        ],
      );
    });
    it("passes a check balance from available+refill", async () => {
      const { roles, owner, allowFunction, invoke } =
        await loadFixture(setupOneParam);

      const allowanceKey = toHex(randomBytes(32));

      await allowFunction([
        {
          parent: 0,
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          compValue: "0x",
        },
        {
          parent: 0,
          paramType: Encoding.Static,
          operator: Operator.WithinAllowance,
          compValue: encodeAbiParameters(parseAbiParameters("bytes32"), [
            allowanceKey,
          ]),
        },
      ]);

      const timestamp = await time.latest();
      await setAllowance(
        roles,
        allowanceKey,
        {
          balance: 250,
          period: 500,
          refill: 100,
          timestamp: timestamp - 750,
        },
        owner.account,
      );

      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke(351n),
        roles,
        "ConditionViolation",
        [
          ConditionViolationStatus.AllowanceExceeded,
          1n, // WithinAllowance node
          anyValue,
        ],
      );

      await invoke(350n);
      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke(1n),
        roles,
        "ConditionViolation",
        [
          ConditionViolationStatus.AllowanceExceeded,
          1n, // WithinAllowance node
          anyValue,
        ],
      );
    });
    it("fails a check, with some balance and not enough elapsed for next refill", async () => {
      const { owner, roles, allowFunction, invoke } =
        await loadFixture(setupOneParam);
      const allowanceKey = toHex(randomBytes(32));

      await allowFunction([
        {
          parent: 0,
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          compValue: "0x",
        },
        {
          parent: 0,
          paramType: Encoding.Static,
          operator: Operator.WithinAllowance,
          compValue: encodeAbiParameters(parseAbiParameters("bytes32"), [
            allowanceKey,
          ]),
        },
      ]);

      const timestamp = await time.latest();
      await setAllowance(
        roles,
        allowanceKey,
        {
          balance: 250,
          period: 1000,
          refill: 100,
          timestamp: timestamp - 50,
        },
        owner.account,
      );

      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke(251n),
        roles,
        "ConditionViolation",
        [
          ConditionViolationStatus.AllowanceExceeded,
          1n, // WithinAllowance node
          anyValue,
        ],
      );

      await invoke(250n);
      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke(1n),
        roles,
        "ConditionViolation",
        [
          ConditionViolationStatus.AllowanceExceeded,
          1n, // WithinAllowance node
          anyValue,
        ],
      );
    });
    it("passes a check with balance from refill and bellow maxRefill", async () => {
      const { owner, roles, allowFunction, invoke } =
        await loadFixture(setupOneParam);

      const interval = 10000;
      const allowanceKey = toHex(randomBytes(32));

      await allowFunction([
        {
          parent: 0,
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          compValue: "0x",
        },
        {
          parent: 0,
          paramType: Encoding.Static,
          operator: Operator.WithinAllowance,
          compValue: encodeAbiParameters(parseAbiParameters("bytes32"), [
            allowanceKey,
          ]),
        },
      ]);

      const timestamp = await time.latest();
      await setAllowance(
        roles,
        allowanceKey,
        {
          balance: 0,
          maxRefill: 1000,
          period: interval,
          refill: 9999999,
          timestamp: timestamp - interval * 10,
        },
        owner.account,
      );

      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke(1001n),
        roles,
        "ConditionViolation",
        [
          ConditionViolationStatus.AllowanceExceeded,
          1n, // WithinAllowance node
          anyValue,
        ],
      );

      await invoke(1000n);
    });
    it("fails a check with balance from refill but capped by maxRefill", async () => {
      const { owner, roles, allowFunction, invoke } =
        await loadFixture(setupOneParam);

      const allowanceKey = toHex(randomBytes(32));
      await allowFunction([
        {
          parent: 0,
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          compValue: "0x",
        },
        {
          parent: 0,
          paramType: Encoding.Static,
          operator: Operator.WithinAllowance,
          compValue: encodeAbiParameters(parseAbiParameters("bytes32"), [
            allowanceKey,
          ]),
        },
      ]);

      const timestamp = await time.latest();
      await setAllowance(
        roles,
        allowanceKey,
        {
          balance: 0,
          maxRefill: 9000,
          period: 1000,
          refill: 10000,
          timestamp: timestamp - 5000,
        },
        owner.account,
      );

      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke(9001n),
        roles,
        "ConditionViolation",
        [
          ConditionViolationStatus.AllowanceExceeded,
          1n, // WithinAllowance node
          anyValue,
        ],
      );

      await invoke(9000n);
    });
    it("fails a check with AllowanceExceeded when value exceeds uint128 max", async () => {
      const { owner, roles, allowFunction, invoke } =
        await loadFixture(setupOneParam);

      const allowanceKey = toHex(randomBytes(32));

      await setAllowance(
        roles,
        allowanceKey,
        {
          balance: 1000,
          period: 0,
          refill: 0,
          timestamp: 0,
        },
        owner.account,
      );

      await allowFunction([
        {
          parent: 0,
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          compValue: "0x",
        },
        {
          parent: 0,
          paramType: Encoding.Static,
          operator: Operator.WithinAllowance,
          compValue: encodeAbiParameters(parseAbiParameters("bytes32"), [
            allowanceKey,
          ]),
        },
      ]);

      // uint128 max + 1: no longer a dedicated AllowanceValueOverflow, since
      // full-precision comparison classifies it as exceeding any balance
      const exceedsUint128 = 2n ** 128n;

      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke(exceedsUint128),
        roles,
        "ConditionViolation",
        [
          ConditionViolationStatus.AllowanceExceeded,
          1n, // WithinAllowance node
          anyValue,
        ],
      );
    });
  });

  describe("WithinAllowance - Consumption", () => {
    it("Consumes balance, even with multiple references to same allowance", async () => {
      const { owner, roles, invoke, allowFunction } =
        await loadFixture(setupTwoParams);

      const allowanceKey =
        "0x0000000000000000000000000000000000000000000000000000000000000001";

      await allowFunction([
        {
          parent: 0,
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          compValue: "0x",
        },
        {
          parent: 0,
          paramType: Encoding.Static,
          operator: Operator.WithinAllowance,
          compValue: encodeAbiParameters(parseAbiParameters("bytes32"), [
            allowanceKey,
          ]),
        },
        {
          parent: 0,
          paramType: Encoding.Static,
          operator: Operator.WithinAllowance,
          compValue: encodeAbiParameters(parseAbiParameters("bytes32"), [
            allowanceKey,
          ]),
        },
      ]);

      await setAllowance(
        roles,
        allowanceKey,
        {
          balance: 3000,
          period: 0,
          refill: 0,
          timestamp: 0,
        },
        owner.account,
      );

      let [balance] = await roles.read.accruedAllowance([allowanceKey]);
      assert.equal(balance, 3000n);

      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke(3001n, 3001n),
        roles,
        "ConditionViolation",
        [
          ConditionViolationStatus.AllowanceExceeded,
          1n, // First WithinAllowance node
          anyValue,
        ],
      );
      [balance] = await roles.read.accruedAllowance([allowanceKey]);
      assert.equal(balance, 3000n);

      await invoke(1500n, 1500n);
      [balance] = await roles.read.accruedAllowance([allowanceKey]);
      assert.equal(balance, 0n);
    });
    it("Consumes from different allowances in same transaction", async () => {
      const { owner, roles, invoke, allowFunction } =
        await loadFixture(setupTwoParams);

      const allowanceKey1 = toHex(randomBytes(32));
      const allowanceKey2 = toHex(randomBytes(32));

      await allowFunction([
        {
          parent: 0,
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          compValue: "0x",
        },
        {
          parent: 0,
          paramType: Encoding.Static,
          operator: Operator.WithinAllowance,
          compValue: encodeAbiParameters(parseAbiParameters("bytes32"), [
            allowanceKey1,
          ]),
        },
        {
          parent: 0,
          paramType: Encoding.Static,
          operator: Operator.WithinAllowance,
          compValue: encodeAbiParameters(parseAbiParameters("bytes32"), [
            allowanceKey2,
          ]),
        },
      ]);

      await setAllowance(
        roles,
        allowanceKey1,
        {
          balance: 1000,
          period: 0,
          refill: 0,
          timestamp: 0,
        },
        owner.account,
      );

      await setAllowance(
        roles,
        allowanceKey2,
        {
          balance: 2000,
          period: 0,
          refill: 0,
          timestamp: 0,
        },
        owner.account,
      );

      // Both allowances consumed independently
      await invoke(500n, 1000n);

      const [balance1] = await roles.read.accruedAllowance([allowanceKey1]);
      const [balance2] = await roles.read.accruedAllowance([allowanceKey2]);
      assert.equal(balance1, 500n);
      assert.equal(balance2, 1000n);
    });
    it("Fails, when multiple parameters referencing the same limit overspend", async () => {
      const { owner, roles, invoke, allowFunction } =
        await loadFixture(setupTwoParams);
      const allowanceKey = toHex(randomBytes(32));

      await allowFunction([
        {
          parent: 0,
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          compValue: "0x",
        },
        {
          parent: 0,
          paramType: Encoding.Static,
          operator: Operator.WithinAllowance,
          compValue: encodeAbiParameters(parseAbiParameters("bytes32"), [
            allowanceKey,
          ]),
        },
        {
          parent: 0,
          paramType: Encoding.Static,
          operator: Operator.WithinAllowance,
          compValue: encodeAbiParameters(parseAbiParameters("bytes32"), [
            allowanceKey,
          ]),
        },
      ]);

      await setAllowance(
        roles,
        allowanceKey,
        {
          balance: 3000,
          period: 0,
          refill: 0,
          timestamp: 0,
        },
        owner.account,
      );

      let [balance] = await roles.read.accruedAllowance([allowanceKey]);
      assert.equal(balance, 3000n);

      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke(3000n, 1n),
        roles,
        "ConditionViolation",
        [
          ConditionViolationStatus.AllowanceExceeded,
          2n, // Second WithinAllowance node (first consumes 3000, second fails with 1)
          anyValue,
        ],
      );
      [balance] = await roles.read.accruedAllowance([allowanceKey]);
      assert.equal(balance, 3000n);
    });
    it("Updates timestamp", async () => {
      const { owner, roles, invoke, allowFunction } =
        await loadFixture(setupOneParam);

      const interval = 600;
      const allowanceKey = toHex(randomBytes(32));

      await allowFunction([
        {
          parent: 0,
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          compValue: "0x",
        },
        {
          parent: 0,
          paramType: Encoding.Static,
          operator: Operator.WithinAllowance,
          compValue: encodeAbiParameters(parseAbiParameters("bytes32"), [
            allowanceKey,
          ]),
        },
      ]);

      await setAllowance(
        roles,
        allowanceKey,
        {
          balance: 100,
          period: BigInt(interval),
          refill: 0,
          timestamp: 1,
        },
        owner.account,
      );

      // Use allowances() for raw storage timestamp checks
      let [, , , balance, allowanceTimestamp] = await roles.read.allowances([
        allowanceKey,
      ]);
      assert.equal(balance, 100n);
      assert.equal(allowanceTimestamp, 1n);

      await invoke(0n);
      const now = BigInt(await time.latest());

      [, , , , allowanceTimestamp] = await roles.read.allowances([
        allowanceKey,
      ]);
      assert.ok(allowanceTimestamp > 1n);
      const timeDifference = now - allowanceTimestamp;
      assert.ok(timeDifference <= BigInt(interval * 2));
    });
    it("Does not updates timestamp if interval is zero", async () => {
      const { owner, roles, invoke, allowFunction } =
        await loadFixture(setupOneParam);
      const allowanceKey = toHex(randomBytes(32));
      await allowFunction([
        {
          parent: 0,
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          compValue: "0x",
        },
        {
          parent: 0,
          paramType: Encoding.Static,
          operator: Operator.WithinAllowance,
          compValue: encodeAbiParameters(parseAbiParameters("bytes32"), [
            allowanceKey,
          ]),
        },
      ]);
      await setAllowance(
        roles,
        allowanceKey,
        {
          balance: 1,
          period: 0,
          refill: 0,
          timestamp: 123,
        },
        owner.account,
      );

      await invoke(0n);

      // Use allowances() for raw storage timestamp checks
      const [, , , , allowanceTimestamp] = await roles.read.allowances([
        allowanceKey,
      ]);
      assert.equal(allowanceTimestamp, 123n);
    });
    it("Updates timestamp from past timestamp", async () => {
      const { owner, roles, invoke, allowFunction } =
        await loadFixture(setupOneParam);

      const interval = 600;

      const allowanceKey = toHex(randomBytes(32));

      await allowFunction([
        {
          parent: 0,
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          compValue: "0x",
        },
        {
          parent: 0,
          paramType: Encoding.Static,
          operator: Operator.WithinAllowance,
          compValue: encodeAbiParameters(parseAbiParameters("bytes32"), [
            allowanceKey,
          ]),
        },
      ]);

      const timestamp = BigInt(await time.latest()) - 2400n;
      await setAllowance(
        roles,
        allowanceKey,
        {
          balance: 1,
          period: interval,
          refill: 0,
          timestamp: timestamp,
        },
        owner.account,
      );

      // Use allowances() for raw storage timestamp checks
      let [, , , , allowanceTimestamp] = await roles.read.allowances([
        allowanceKey,
      ]);
      assert.equal(allowanceTimestamp, timestamp);

      await invoke(0n);

      [, , , , allowanceTimestamp] = await roles.read.allowances([
        allowanceKey,
      ]);
      assert.ok(allowanceTimestamp > timestamp);
    });
    it("Does not update timestamp from future timestamp", async () => {
      const { owner, roles, invoke, allowFunction } =
        await loadFixture(setupOneParam);

      const interval = 600;
      const allowanceKey = toHex(randomBytes(32));
      await allowFunction([
        {
          parent: 0,
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          compValue: "0x",
        },
        {
          parent: 0,
          paramType: Encoding.Static,
          operator: Operator.WithinAllowance,
          compValue: encodeAbiParameters(parseAbiParameters("bytes32"), [
            allowanceKey,
          ]),
        },
      ]);
      const timestamp = BigInt(await time.latest()) + 1200n;
      await setAllowance(
        roles,
        allowanceKey,
        {
          balance: 1,
          period: interval,
          refill: 0,
          timestamp: timestamp,
        },
        owner.account,
      );

      // Use allowances() for raw storage timestamp checks
      let [, , , , allowanceTimestamp] = await roles.read.allowances([
        allowanceKey,
      ]);
      assert.equal(allowanceTimestamp, timestamp);

      await invoke(0n);

      [, , , , allowanceTimestamp] = await roles.read.allowances([
        allowanceKey,
      ]);
      assert.equal(allowanceTimestamp, timestamp);
    });
  });

  describe("WithinAllowance - Decimal Conversion (no price adapter)", () => {
    function encodeDecimalsOnly({
      allowanceKey,
      targetDecimals,
      sourceDecimals,
    }: {
      allowanceKey: Hex;
      targetDecimals: number;
      sourceDecimals: number;
    }): Hex {
      return encodePacked(
        ["bytes32", "uint8", "uint8"],
        [allowanceKey, targetDecimals, sourceDecimals],
      );
    }

    const allowanceKey = toHex(randomBytes(32));

    /**
     * Real-world scenario: Stablecoin swap USDC → DAI
     *
     * - USDC: 6 decimals
     * - DAI: 18 decimals
     * - Allowance tracked in DAI decimals (18)
     */
    it("USDC (6 dec) → DAI (18 dec): tracks allowance correctly", async () => {
      const { owner, roles, allowFunction, invoke } =
        await loadFixture(setupOneParam);

      // Allowance: 1000 DAI (18 decimals)
      await setAllowance(
        roles,
        allowanceKey,
        {
          balance: 1000n * 10n ** 18n,
          period: 0,
          refill: 0,
          timestamp: 0,
        },
        owner.account,
      );

      await allowFunction([
        {
          parent: 0,
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          compValue: "0x",
        },
        {
          parent: 0,
          paramType: Encoding.Static,
          operator: Operator.WithinAllowance,
          compValue: encodeDecimalsOnly({
            allowanceKey,
            targetDecimals: 18, // DAI
            sourceDecimals: 6, // USDC
          }),
        },
      ]);

      // Spend 500 USDC (6 dec) → converts to 500 DAI (18 dec)
      await invoke(500n * 10n ** 6n);

      const [balance] = await roles.read.accruedAllowance([allowanceKey]);
      assert.equal(balance, 500n * 10n ** 18n); // 500 DAI remaining
    });

    it("USDC (6 dec) → DAI (18 dec): reverts when exceeding allowance", async () => {
      const { owner, roles, allowFunction, invoke } =
        await loadFixture(setupOneParam);

      // Allowance: 100 DAI
      await setAllowance(
        roles,
        allowanceKey,
        {
          balance: 100n * 10n ** 18n,
          period: 0,
          refill: 0,
          timestamp: 0,
        },
        owner.account,
      );

      await allowFunction([
        {
          parent: 0,
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          compValue: "0x",
        },
        {
          parent: 0,
          paramType: Encoding.Static,
          operator: Operator.WithinAllowance,
          compValue: encodeDecimalsOnly({
            allowanceKey,
            targetDecimals: 18,
            sourceDecimals: 6,
          }),
        },
      ]);

      // Try to spend 101 USDC → exceeds 100 DAI allowance
      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke(101n * 10n ** 6n),
        roles,
        "ConditionViolation",
        [
          ConditionViolationStatus.AllowanceExceeded,
          1n, // WithinAllowance node
          anyValue,
        ],
      );
    });

    /**
     * Reverse direction: DAI → USDC (scaling down)
     */
    it("DAI (18 dec) → USDC (6 dec): scales down correctly", async () => {
      const { owner, roles, allowFunction, invoke } =
        await loadFixture(setupOneParam);

      // Allowance: 1000 USDC (6 decimals)
      await setAllowance(
        roles,
        allowanceKey,
        {
          balance: 1000n * 10n ** 6n,
          period: 0,
          refill: 0,
          timestamp: 0,
        },
        owner.account,
      );

      await allowFunction([
        {
          parent: 0,
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          compValue: "0x",
        },
        {
          parent: 0,
          paramType: Encoding.Static,
          operator: Operator.WithinAllowance,
          compValue: encodeDecimalsOnly({
            allowanceKey,
            targetDecimals: 6, // USDC
            sourceDecimals: 18, // DAI
          }),
        },
      ]);

      // Spend 500 DAI (18 dec) → converts to 500 USDC (6 dec)
      await invoke(500n * 10n ** 18n);

      const [balance] = await roles.read.accruedAllowance([allowanceKey]);
      assert.equal(balance, 500n * 10n ** 6n); // 500 USDC remaining
    });

    it("should cumulatively charge dust-sized calls", async () => {
      const { owner, roles, allowFunction, invoke } =
        await loadFixture(setupOneParam);

      await setAllowance(
        roles,
        allowanceKey,
        {
          balance: 10n,
          period: 0,
          refill: 0,
          timestamp: 0,
        },
        owner.account,
      );

      await allowFunction([
        {
          parent: 0,
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          compValue: "0x",
        },
        {
          parent: 0,
          paramType: Encoding.Static,
          operator: Operator.WithinAllowance,
          compValue: encodeDecimalsOnly({
            allowanceKey,
            targetDecimals: 6,
            sourceDecimals: 18,
          }),
        },
      ]);

      const dust = parseUnits("0.0000009", 18);
      await invoke(dust); // consumed 0.9
      await invoke(dust); // consumed 1.8
      await invoke(dust); // consumed 2.7
      await invoke(dust); // consumed 3.6

      const [balance] = await roles.read.accruedAllowance([allowanceKey]);
      // Expected behavior: split calls should at least as much as the same as an aggregated call.
      assert.ok(balance <= 10n - 4n);
    });

    it("sub-unit dust consumes exactly 1 in target precision", async () => {
      const { owner, roles, allowFunction, invoke } =
        await loadFixture(setupOneParam);

      // 100 USDC allowance (6 decimals)
      await setAllowance(
        roles,
        allowanceKey,
        {
          balance: 100n * 10n ** 5n,
          period: 0,
          refill: 0,
          timestamp: 0,
        },
        owner.account,
      );

      await allowFunction([
        {
          parent: 0,
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          compValue: "0x",
        },
        {
          parent: 0,
          paramType: Encoding.Static,
          operator: Operator.WithinAllowance,
          compValue: encodeDecimalsOnly({
            allowanceKey,
            targetDecimals: 5,
            sourceDecimals: 18,
          }),
        },
      ]);

      // 1 wei – far below 1 micro-unit (10^12 wei)
      await invoke(1n);

      const [balance] = await roles.read.accruedAllowance([allowanceKey]);
      // consumed exactly 0.000001 USDC (1 in 6 dec precision)
      assert.equal(balance, parseUnits("99.99999", 5));
    });

    it("zero value consumes nothing", async () => {
      const { owner, roles, allowFunction, invoke } =
        await loadFixture(setupOneParam);

      await setAllowance(
        roles,
        allowanceKey,
        {
          balance: parseUnits("100", 6),
          period: 0,
          refill: 0,
          timestamp: 0,
        },
        owner.account,
      );

      await allowFunction([
        {
          parent: 0,
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          compValue: "0x",
        },
        {
          parent: 0,
          paramType: Encoding.Static,
          operator: Operator.WithinAllowance,
          compValue: encodeDecimalsOnly({
            allowanceKey,
            targetDecimals: 6,
            sourceDecimals: 18,
          }),
        },
      ]);

      await invoke(0n);

      const [balance] = await roles.read.accruedAllowance([allowanceKey]);
      assert.equal(balance, parseUnits("100", 6));
    });
  });

  describe("WithinAllowance - Price Adapter", () => {
    function encodeAllowanceCompValue({
      allowanceKey,
      targetDecimals = 0,
      sourceDecimals = 0,
      adapter = zeroAddress,
    }: {
      allowanceKey: Hex;
      targetDecimals?: number;
      sourceDecimals?: number;
      adapter?: Address;
    }): Hex {
      return encodePacked(
        ["bytes32", "uint8", "uint8", "address"],
        [allowanceKey, targetDecimals, sourceDecimals, adapter],
      );
    }

    const allowanceKey =
      "0x0000000000000000000000000000000000000000000000000000000000000001";

    it("price-converted dust rounds up and consumes 1 in target precision", async () => {
      const { owner, roles, allowFunction, invoke } =
        await loadFixture(setupOneParam);

      /*
       * Spend: 1 source unit (0 decimals). Price: 0.5, encoded as 5e17 with
       * 18 decimals. Allowance: 2 target units (0 decimals).
       *
       * Each spend converts to 1 * 5e17 / 1e18 = 0.5 target units and must
       * consume ceil(0.5) = 1: balance goes 2 → 1 → 0, then reverts.
       * Floored, it would consume 0 and let unlimited dust spends through.
       */
      const adapter = await viem.deployContract("MockPricing", [
        5n * 10n ** 17n,
      ]); // 0.5x

      await setAllowance(
        roles,
        allowanceKey,
        {
          balance: 2,
          period: 0,
          refill: 0,
          timestamp: 0,
        },
        owner.account,
      );

      await allowFunction([
        {
          parent: 0,
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          compValue: "0x",
        },
        {
          parent: 0,
          paramType: Encoding.Static,
          operator: Operator.WithinAllowance,
          compValue: encodeAllowanceCompValue({
            allowanceKey,
            adapter: adapter.address,
          }),
        },
      ]);

      assert.equal((await roles.read.accruedAllowance([allowanceKey]))[0], 2n);
      // each spend converts to 0.5, and consumes ceil(0.5) = 1, never 0
      await invoke(1n);
      assert.equal((await roles.read.accruedAllowance([allowanceKey]))[0], 1n);
      await invoke(1n);
      assert.equal((await roles.read.accruedAllowance([allowanceKey]))[0], 0n);

      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke(1n),
        roles,
        "ConditionViolation",
        [ConditionViolationStatus.AllowanceExceeded, 1n, anyValue],
      );
    });

    it("accumulates conversion truncation against the allowance", async () => {
      const { owner, roles, allowFunction, invoke } =
        await loadFixture(setupOneParam);

      const adapter = await viem.deployContract("MockPricing", [
        15n * 10n ** 17n,
      ]); // 1.5x

      await setAllowance(
        roles,
        allowanceKey,
        {
          balance: 3,
          period: 0,
          refill: 0,
          timestamp: 0,
        },
        owner.account,
      );

      await allowFunction([
        {
          parent: 0,
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          compValue: "0x",
        },
        {
          parent: 0,
          paramType: Encoding.Static,
          operator: Operator.WithinAllowance,
          compValue: encodeAllowanceCompValue({
            allowanceKey,
            adapter: adapter.address,
          }),
        },
      ]);

      // One input unit is worth 1.5 allowance units, so it consumes 2.
      await invoke(1n);
      assert.equal((await roles.read.accruedAllowance([allowanceKey]))[0], 1n);

      // A second input needs another 2 units and cannot spend the remaining 1.
      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke(1n),
        roles,
        "ConditionViolation",
        [ConditionViolationStatus.AllowanceExceeded, 1n, anyValue],
      );
    });

    // base=12, param=6: scale up by 10^6
    // 1000 units (6 dec) → converted = 1000e6 * 1e18 * 1e12 / 1e24 = 1000e12 (12 dec)
    it("param(6) → base(12): consumes correctly", async () => {
      const { owner, roles, allowFunction, invoke } =
        await loadFixture(setupOneParam);

      const adapter = await viem.deployContract("MockPricing", [10n ** 18n]); // 1:1 price

      await setAllowance(
        roles,
        allowanceKey,
        {
          balance: 2000n * 10n ** 12n, // 2000 units in 12 decimals
          period: 0,
          refill: 0,
          timestamp: 0,
        },
        owner.account,
      );

      await allowFunction([
        {
          parent: 0,
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          compValue: "0x",
        },
        {
          parent: 0,
          paramType: Encoding.Static,
          operator: Operator.WithinAllowance,
          compValue: encodeAllowanceCompValue({
            allowanceKey,
            adapter: adapter.address,
            targetDecimals: 12,
            sourceDecimals: 6,
          }),
        },
      ]);

      // spend 1000 (6 dec) → 1000e12 (12 dec)
      await invoke(1000n * 10n ** 6n);

      const [balance] = await roles.read.accruedAllowance([allowanceKey]);
      // sent in 1000 in 6 decimals, but it consumed in 12 decimals
      assert.equal(balance, 1000n * 10n ** 12n);
    });

    it("param(6) → base(12): reverts on overconsume", async () => {
      const { owner, roles, allowFunction, invoke } =
        await loadFixture(setupOneParam);

      const adapter = await viem.deployContract("MockPricing", [10n ** 18n]);

      await setAllowance(
        roles,
        allowanceKey,
        {
          balance: 1000n * 10n ** 12n, // exactly 1000 units (12 dec)
          period: 0,
          refill: 0,
          timestamp: 0,
        },
        owner.account,
      );

      await allowFunction([
        {
          parent: 0,
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          compValue: "0x",
        },
        {
          parent: 0,
          paramType: Encoding.Static,
          operator: Operator.WithinAllowance,
          compValue: encodeAllowanceCompValue({
            allowanceKey,
            adapter: adapter.address,
            targetDecimals: 12,
            sourceDecimals: 6,
          }),
        },
      ]);

      // 1001 (6 dec) → 1001e12 (12 dec) > 1000e12
      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke(1001n * 10n ** 6n),
        roles,
        "ConditionViolation",
        [
          ConditionViolationStatus.AllowanceExceeded,
          1n, // WithinAllowance node
          anyValue,
        ],
      );
    });

    // base=18, param=6: scale up by 10^12
    it("param(6) → base(18): consumes correctly", async () => {
      const { owner, roles, allowFunction, invoke } =
        await loadFixture(setupOneParam);

      const adapter = await viem.deployContract("MockPricing", [10n ** 18n]);

      await setAllowance(
        roles,
        allowanceKey,
        {
          balance: 2000n * 10n ** 18n,
          period: 0,
          refill: 0,
          timestamp: 0,
        },
        owner.account,
      );

      await allowFunction([
        {
          parent: 0,
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          compValue: "0x",
        },
        {
          parent: 0,
          paramType: Encoding.Static,
          operator: Operator.WithinAllowance,
          compValue: encodeAllowanceCompValue({
            allowanceKey,
            adapter: adapter.address,
            targetDecimals: 18,
            sourceDecimals: 6,
          }),
        },
      ]);

      // spend 1000 (6 dec) → 1000e18 (18 dec)
      await invoke(1000n * 10n ** 6n);

      const [balance] = await roles.read.accruedAllowance([allowanceKey]);
      assert.equal(balance, 1000n * 10n ** 18n);
    });

    it("param(6) → base(18): reverts on overconsume", async () => {
      const { owner, roles, allowFunction, invoke } =
        await loadFixture(setupOneParam);

      const adapter = await viem.deployContract("MockPricing", [10n ** 18n]);

      await setAllowance(
        roles,
        allowanceKey,
        {
          balance: 1000n * 10n ** 18n,
          period: 0,
          refill: 0,
          timestamp: 0,
        },
        owner.account,
      );

      await allowFunction([
        {
          parent: 0,
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          compValue: "0x",
        },
        {
          parent: 0,
          paramType: Encoding.Static,
          operator: Operator.WithinAllowance,
          compValue: encodeAllowanceCompValue({
            allowanceKey,
            adapter: adapter.address,
            targetDecimals: 18,
            sourceDecimals: 6,
          }),
        },
      ]);

      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke(1001n * 10n ** 6n),
        roles,
        "ConditionViolation",
        [
          ConditionViolationStatus.AllowanceExceeded,
          1n, // WithinAllowance node
          anyValue,
        ],
      );
    });

    // base=6, param=12: scale down by 10^6
    it("param(12) → base(6): consumes correctly", async () => {
      const { owner, roles, allowFunction, invoke } =
        await loadFixture(setupOneParam);

      const adapter = await viem.deployContract("MockPricing", [10n ** 18n]);

      await setAllowance(
        roles,
        allowanceKey,
        {
          balance: 900n * 10n ** 6n, // 900 units (6 dec)
          period: 0,
          refill: 0,
          timestamp: 0,
        },
        owner.account,
      );

      await allowFunction([
        {
          parent: 0,
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          compValue: "0x",
        },
        {
          parent: 0,
          paramType: Encoding.Static,
          operator: Operator.WithinAllowance,
          compValue: encodeAllowanceCompValue({
            allowanceKey,
            adapter: adapter.address,
            targetDecimals: 6,
            sourceDecimals: 12,
          }),
        },
      ]);

      // spend 1000 (12 dec) → 1000 * 1e6 / 1e6 = 1000 (6 dec) ... wait
      // formula: value * price * 10^base / 10^(18 + param)
      // = 1000e12 * 1e18 * 1e6 / 1e30 = 1000e36 / 1e30 = 1000e6
      await invoke(500n * 10n ** 12n);

      const [balance] = await roles.read.accruedAllowance([allowanceKey]);
      assert.equal(balance, 400n * 10n ** 6n);
    });

    it("param(12) → base(6): reverts on overconsume", async () => {
      const { owner, roles, allowFunction, invoke } =
        await loadFixture(setupOneParam);

      const adapter = await viem.deployContract("MockPricing", [10n ** 18n]);

      await setAllowance(
        roles,
        allowanceKey,
        {
          balance: 1000n * 10n ** 6n,
          period: 0,
          refill: 0,
          timestamp: 0,
        },
        owner.account,
      );

      await allowFunction([
        {
          parent: 0,
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          compValue: "0x",
        },
        {
          parent: 0,
          paramType: Encoding.Static,
          operator: Operator.WithinAllowance,
          compValue: encodeAllowanceCompValue({
            allowanceKey,
            adapter: adapter.address,
            targetDecimals: 6,
            sourceDecimals: 12,
          }),
        },
      ]);

      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke(1001n * 10n ** 12n),
        roles,
        "ConditionViolation",
        [
          ConditionViolationStatus.AllowanceExceeded,
          1n, // WithinAllowance node
          anyValue,
        ],
      );
    });

    // base=12, param=18: scale down by 10^6
    it("param(18) → base(12): consumes correctly", async () => {
      const { owner, roles, allowFunction, invoke } =
        await loadFixture(setupOneParam);

      const adapter = await viem.deployContract("MockPricing", [10n ** 18n]);

      await setAllowance(
        roles,
        allowanceKey,
        {
          balance: 2000n * 10n ** 12n,
          period: 0,
          refill: 0,
          timestamp: 0,
        },
        owner.account,
      );

      await allowFunction([
        {
          parent: 0,
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          compValue: "0x",
        },
        {
          parent: 0,
          paramType: Encoding.Static,
          operator: Operator.WithinAllowance,
          compValue: encodeAllowanceCompValue({
            allowanceKey,
            adapter: adapter.address,
            targetDecimals: 12,
            sourceDecimals: 18,
          }),
        },
      ]);

      // 1000e18 * 1e18 * 1e12 / 1e36 = 1000e12
      await invoke(1000n * 10n ** 18n);

      const [balance] = await roles.read.accruedAllowance([allowanceKey]);
      assert.equal(balance, 1000n * 10n ** 12n);
    });

    it("param(18) → base(12): reverts on overconsume", async () => {
      const { owner, roles, allowFunction, invoke } =
        await loadFixture(setupOneParam);

      const adapter = await viem.deployContract("MockPricing", [10n ** 18n]);

      await setAllowance(
        roles,
        allowanceKey,
        {
          balance: 1000n * 10n ** 12n,
          period: 0,
          refill: 0,
          timestamp: 0,
        },
        owner.account,
      );

      await allowFunction([
        {
          parent: 0,
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          compValue: "0x",
        },
        {
          parent: 0,
          paramType: Encoding.Static,
          operator: Operator.WithinAllowance,
          compValue: encodeAllowanceCompValue({
            allowanceKey,
            adapter: adapter.address,
            targetDecimals: 12,
            sourceDecimals: 18,
          }),
        },
      ]);

      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke(1001n * 10n ** 18n),
        roles,
        "ConditionViolation",
        [
          ConditionViolationStatus.AllowanceExceeded,
          1n, // WithinAllowance node
          anyValue,
        ],
      );
    });

    // DAI (18 dec) spending against USDC (6 dec) allowance
    it("spend DAI(18) → base USDC(6)", async () => {
      const { owner, roles, allowFunction, invoke } =
        await loadFixture(setupOneParam);

      // DAI/USDC price = 1e18 (1:1)
      const adapter = await viem.deployContract("MockPricing", [10n ** 18n]);

      await setAllowance(
        roles,
        allowanceKey,
        {
          balance: 1000n * 10n ** 6n, // 1000 USDC
          period: 0,
          refill: 0,
          timestamp: 0,
        },
        owner.account,
      );

      await allowFunction([
        {
          parent: 0,
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          compValue: "0x",
        },
        {
          parent: 0,
          paramType: Encoding.Static,
          operator: Operator.WithinAllowance,
          compValue: encodeAllowanceCompValue({
            allowanceKey,
            adapter: adapter.address,
            targetDecimals: 6,
            sourceDecimals: 18,
          }),
        },
      ]);

      // spend 500 DAI (18 dec) → 500 USDC (6 dec)
      await invoke(500n * 10n ** 18n);

      const [balance] = await roles.read.accruedAllowance([allowanceKey]);
      assert.equal(balance, 500n * 10n ** 6n);
    });

    // USDC (6 dec) spending against DAI (18 dec) allowance
    it("spend USDC(6) → base DAI(18)", async () => {
      const { owner, roles, allowFunction, invoke } =
        await loadFixture(setupOneParam);

      const adapter = await viem.deployContract("MockPricing", [10n ** 18n]);

      await setAllowance(
        roles,
        allowanceKey,
        {
          balance: 1000n * 10n ** 18n, // 1000 DAI
          period: 0,
          refill: 0,
          timestamp: 0,
        },
        owner.account,
      );

      await allowFunction([
        {
          parent: 0,
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          compValue: "0x",
        },
        {
          parent: 0,
          paramType: Encoding.Static,
          operator: Operator.WithinAllowance,
          compValue: encodeAllowanceCompValue({
            allowanceKey,
            adapter: adapter.address,
            targetDecimals: 18,
            sourceDecimals: 6,
          }),
        },
      ]);

      // spend 500 USDC (6 dec) → 500 DAI (18 dec)
      await invoke(500n * 10n ** 6n);

      const [balance] = await roles.read.accruedAllowance([allowanceKey]);
      assert.equal(balance, 500n * 10n ** 18n);
    });

    // Multi-asset: USDC(6), DAI(18), ETH(18) all convert to USDC(6) base allowance
    it("multi-asset (USDC + DAI + ETH) → base USDC(6)", async () => {
      const { owner, roles, invoke, allowFunction } =
        await loadFixture(setupTwoParams);

      const usdcAdapter = await viem.deployContract("MockPricing", [
        10n ** 18n,
      ]); // 1:1
      const ethAdapter = await viem.deployContract("MockPricing", [
        2000n * 10n ** 18n,
      ]); // 1 ETH = 2000 USDC

      await setAllowance(
        roles,
        allowanceKey,
        {
          balance: 5000n * 10n ** 6n, // 5000 USDC
          period: 0,
          refill: 0,
          timestamp: 0,
        },
        owner.account,
      );

      await allowFunction([
        {
          parent: 0,
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          compValue: "0x",
        },
        {
          parent: 0,
          paramType: Encoding.Static,
          operator: Operator.WithinAllowance,
          compValue: encodeAllowanceCompValue({
            allowanceKey,
            adapter: usdcAdapter.address,
            targetDecimals: 6,
            sourceDecimals: 6,
          }),
        },
        {
          parent: 0,
          paramType: Encoding.Static,
          operator: Operator.WithinAllowance,
          compValue: encodeAllowanceCompValue({
            allowanceKey,
            adapter: ethAdapter.address,
            targetDecimals: 6,
            sourceDecimals: 18,
          }),
        },
      ]);

      // spend 1000 USDC + 1 ETH (2000 USDC) = 3000 USDC total
      await invoke(1000n * 10n ** 6n, 1n * 10n ** 18n);

      let [balance] = await roles.read.accruedAllowance([allowanceKey]);
      assert.equal(balance, 2000n * 10n ** 6n); // 5000 - 3000 = 2000

      // spend remaining: 0 USDC + 1 ETH = 2000 USDC
      await invoke(0n, 1n * 10n ** 18n);

      [balance] = await roles.read.accruedAllowance([allowanceKey]);
      assert.equal(balance, 0n);

      // any more reverts
      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke(1n, 0n),
        roles,
        "ConditionViolation",
        [
          ConditionViolationStatus.AllowanceExceeded,
          1n, // First WithinAllowance node
          anyValue,
        ],
      );
    });

    it("preserves decimal precision when scaling down (18 → 6)", async () => {
      const { owner, roles, allowFunction, invoke } =
        await loadFixture(setupOneParam);

      const adapter = await viem.deployContract("MockPricing", [10n ** 18n]); // 1:1 price

      // 1.123456789123456789 in 18 decimals
      const valueInParamDecimals = 1123456789123456789n;
      // Expected: 1.123457 in 6 decimals (rounds up after 6 decimals)
      const valueInAccrueDecimals = 1123457n;

      await setAllowance(
        roles,
        allowanceKey,
        {
          balance: valueInAccrueDecimals,
          period: 0,
          refill: 0,
          timestamp: 0,
        },
        owner.account,
      );

      await allowFunction([
        {
          parent: 0,
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          compValue: "0x",
        },
        {
          parent: 0,
          paramType: Encoding.Static,
          operator: Operator.WithinAllowance,
          compValue: encodeAllowanceCompValue({
            allowanceKey,
            adapter: adapter.address,
            targetDecimals: 6,
            sourceDecimals: 18,
          }),
        },
      ]);

      let [balance] = await roles.read.accruedAllowance([allowanceKey]);
      assert.equal(balance, valueInAccrueDecimals);

      await invoke(valueInParamDecimals);

      [balance] = await roles.read.accruedAllowance([allowanceKey]);
      assert.equal(balance, 0n);
    });

    it("preserves decimal precision when scaling up (6 → 18)", async () => {
      const { owner, roles, allowFunction, invoke } =
        await loadFixture(setupOneParam);

      const adapter = await viem.deployContract("MockPricing", [10n ** 18n]); // 1:1 price

      // 1.123456 in 6 decimals
      const valueInParamDecimals = 1123456n;
      // Expected: 1.123456000000000000 in 18 decimals
      const valueInAccrueDecimals = 1123456000000000000n;

      await setAllowance(
        roles,
        allowanceKey,
        {
          balance: valueInAccrueDecimals,
          period: 0,
          refill: 0,
          timestamp: 0,
        },
        owner.account,
      );

      await allowFunction([
        {
          parent: 0,
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          compValue: "0x",
        },
        {
          parent: 0,
          paramType: Encoding.Static,
          operator: Operator.WithinAllowance,
          compValue: encodeAllowanceCompValue({
            allowanceKey,
            adapter: adapter.address,
            targetDecimals: 18,
            sourceDecimals: 6,
          }),
        },
      ]);

      let [balance] = await roles.read.accruedAllowance([allowanceKey]);
      assert.equal(balance, valueInAccrueDecimals);

      await invoke(valueInParamDecimals);

      [balance] = await roles.read.accruedAllowance([allowanceKey]);
      assert.equal(balance, 0n);
    });
  });

  describe("parameterized adapter", () => {
    const allowanceKey =
      "0x0000000000000000000000000000000000000000000000000000000000000001";

    it("adapter receives encoded params from compValue", async () => {
      const { owner, roles, allowFunction, invoke } =
        await loadFixture(setupOneParam);

      // Adapter that requires specific params, reverts otherwise
      const adapter = await viem.deployContract("MockPricingParameterized");

      const params = "0xdeadbeef";
      await adapter.write.setPrice([params, 2n * 10n ** 18n]); // 2x multiplier

      await setAllowance(
        roles,
        allowanceKey,
        {
          balance: 2000n,
          period: 0,
          refill: 0,
          timestamp: 0,
        },
        owner.account,
      );

      // compValue: allowanceKey(32) + baseDecimals(1) + paramDecimals(1) + adapter(20) + params(4)
      const compValue = encodePacked(
        ["bytes32", "uint8", "uint8", "address", "bytes"],
        [allowanceKey, 0, 0, adapter.address, params],
      );

      // wrong params → adapter reverts, we check it is extracting and passing correctly
      const wrongCompValue = encodePacked(
        ["bytes32", "uint8", "uint8", "address", "bytes"],
        [allowanceKey, 0, 0, adapter.address, "0xcafebabe"],
      );
      await allowFunction([
        {
          parent: 0,
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          compValue: "0x",
        },
        {
          parent: 0,
          paramType: Encoding.Static,
          operator: Operator.WithinAllowance,
          compValue: wrongCompValue,
        },
      ]);
      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke(500n),
        roles,
        "ConditionViolation",
        [ConditionViolationStatus.PricingAdapterReverted, 1n, anyValue],
      );

      // correct params → works
      await allowFunction([
        {
          parent: 0,
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          compValue: "0x",
        },
        {
          parent: 0,
          paramType: Encoding.Static,
          operator: Operator.WithinAllowance,
          compValue,
        },
      ]);

      // value=500, price=2x → consumed=1000, within 2000 balance
      await invoke(500n);

      const [balance] = await roles.read.accruedAllowance([allowanceKey]);
      assert.equal(balance, 1000n); // 2000 - 1000

      // value=600 → consumed=1200, total=2200 > 2000 → fail
      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke(600n),
        roles,
        "ConditionViolation",
        [ConditionViolationStatus.AllowanceExceeded, 1n, anyValue],
      );
    });

    it("adapter receives empty params when compValue has no trailing bytes", async () => {
      const { owner, roles, allowFunction, invoke } =
        await loadFixture(setupOneParam);

      // Adapter that requires empty params, reverts if non-empty
      const adapter = await viem.deployContract("MockPricingEmptyParams", [
        10n ** 18n,
      ]); // 1:1 price

      await setAllowance(
        roles,
        allowanceKey,
        {
          balance: 1000n,
          period: 0,
          refill: 0,
          timestamp: 0,
        },
        owner.account,
      );

      // counterfactual: non-empty params → adapter reverts
      const wrongCompValue = encodePacked(
        ["bytes32", "uint8", "uint8", "address", "bytes"],
        [allowanceKey, 0, 0, adapter.address, "0xdeadbeef"],
      );
      await allowFunction([
        {
          parent: 0,
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          compValue: "0x",
        },
        {
          parent: 0,
          paramType: Encoding.Static,
          operator: Operator.WithinAllowance,
          compValue: wrongCompValue,
        },
      ]);
      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke(500n),
        roles,
        "ConditionViolation",
        [ConditionViolationStatus.PricingAdapterReverted, 1n, anyValue],
      );

      // correct: exactly 54 bytes (no trailing params)
      const compValue = encodePacked(
        ["bytes32", "uint8", "uint8", "address"],
        [allowanceKey, 0, 0, adapter.address],
      );
      await allowFunction([
        {
          parent: 0,
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          compValue: "0x",
        },
        {
          parent: 0,
          paramType: Encoding.Static,
          operator: Operator.WithinAllowance,
          compValue,
        },
      ]);

      // 1:1 price, value=500 → consumed=500
      await invoke(500n);
      const [balance] = await roles.read.accruedAllowance([allowanceKey]);
      assert.equal(balance, 500n);
    });
  });

  describe("adapter call safety", () => {
    function encodeAllowanceCompValue({
      allowanceKey,
      targetDecimals = 0,
      sourceDecimals = 0,
      adapter = zeroAddress,
    }: {
      allowanceKey: Hex;
      targetDecimals?: number;
      sourceDecimals?: number;
      adapter?: Address;
    }): Hex {
      return encodePacked(
        ["bytes32", "uint8", "uint8", "address"],
        [allowanceKey, targetDecimals, sourceDecimals, adapter],
      );
    }

    const allowanceKey = toHex(randomBytes(32));

    it("reverts with PricingAdapterNotAContract when adapter not deployed", async () => {
      const { owner, roles, allowFunction, invoke } =
        await loadFixture(setupOneParam);

      const [, , randomEOA] = await viem.getWalletClients();

      await setAllowance(
        roles,
        allowanceKey,
        {
          balance: 1000,
          period: 0,
          refill: 0,
          timestamp: 0,
        },
        owner.account,
      );

      await allowFunction([
        {
          parent: 0,
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          compValue: "0x",
        },
        {
          parent: 0,
          paramType: Encoding.Static,
          operator: Operator.WithinAllowance,
          compValue: encodeAllowanceCompValue({
            allowanceKey,
            adapter: randomEOA.account.address,
            targetDecimals: 18,
            sourceDecimals: 6,
          }),
        },
      ]);

      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke(1000n),
        roles,
        "ConditionViolation",
        [
          ConditionViolationStatus.PricingAdapterNotAContract,
          1n, // WithinAllowance node
          anyValue,
        ],
      );
    });

    it("reverts with PricingAdapterReverted when adapter has no getPrice function", async () => {
      const { owner, roles, allowFunction, invoke } =
        await loadFixture(setupOneParam);

      const noInterfaceAdapter = await viem.deployContract(
        "MockPricingNoInterface",
      );

      await setAllowance(
        roles,
        allowanceKey,
        {
          balance: 1000,
          period: 0,
          refill: 0,
          timestamp: 0,
        },
        owner.account,
      );

      await allowFunction([
        {
          parent: 0,
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          compValue: "0x",
        },
        {
          parent: 0,
          paramType: Encoding.Static,
          operator: Operator.WithinAllowance,
          compValue: encodeAllowanceCompValue({
            allowanceKey,
            adapter: noInterfaceAdapter.address,
            targetDecimals: 18,
            sourceDecimals: 6,
          }),
        },
      ]);

      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke(1000n),
        roles,
        "ConditionViolation",
        [
          ConditionViolationStatus.PricingAdapterReverted,
          1n, // WithinAllowance node
          anyValue,
        ],
      );
    });

    it("reverts with PricingAdapterReverted when adapter reverts", async () => {
      const { owner, roles, allowFunction, invoke } =
        await loadFixture(setupOneParam);

      const revertingAdapter = await viem.deployContract(
        "MockPricingReverting",
      );

      await setAllowance(
        roles,
        allowanceKey,
        {
          balance: 1000,
          period: 0,
          refill: 0,
          timestamp: 0,
        },
        owner.account,
      );

      await allowFunction([
        {
          parent: 0,
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          compValue: "0x",
        },
        {
          parent: 0,
          paramType: Encoding.Static,
          operator: Operator.WithinAllowance,
          compValue: encodeAllowanceCompValue({
            allowanceKey,
            adapter: revertingAdapter.address,
            targetDecimals: 18,
            sourceDecimals: 6,
          }),
        },
      ]);

      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke(1000n),
        roles,
        "ConditionViolation",
        [
          ConditionViolationStatus.PricingAdapterReverted,
          1n, // WithinAllowance node
          anyValue,
        ],
      );
    });

    it("reverts with PricingAdapterInvalidResult when adapter returns wrong type", async () => {
      const { owner, roles, allowFunction, invoke } =
        await loadFixture(setupOneParam);

      const wrongReturnAdapter = await viem.deployContract(
        "MockPricingWrongReturn",
      );

      await setAllowance(
        roles,
        allowanceKey,
        {
          balance: 1000,
          period: 0,
          refill: 0,
          timestamp: 0,
        },
        owner.account,
      );

      await allowFunction([
        {
          parent: 0,
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          compValue: "0x",
        },
        {
          parent: 0,
          paramType: Encoding.Static,
          operator: Operator.WithinAllowance,
          compValue: encodeAllowanceCompValue({
            allowanceKey,
            adapter: wrongReturnAdapter.address,
            targetDecimals: 18,
            sourceDecimals: 6,
          }),
        },
      ]);

      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke(1000n),
        roles,
        "ConditionViolation",
        [
          ConditionViolationStatus.PricingAdapterInvalidResult,
          1n, // WithinAllowance node
          anyValue,
        ],
      );
    });

    it("reverts with PricingAdapterZeroPrice when adapter returns zero", async () => {
      const { owner, roles, allowFunction, invoke } =
        await loadFixture(setupOneParam);

      const zeroAdapter = await viem.deployContract("MockPricing", [0n]);

      await setAllowance(
        roles,
        allowanceKey,
        {
          balance: 1000,
          period: 0,
          refill: 0,
          timestamp: 0,
        },
        owner.account,
      );

      await allowFunction([
        {
          parent: 0,
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          compValue: "0x",
        },
        {
          parent: 0,
          paramType: Encoding.Static,
          operator: Operator.WithinAllowance,
          compValue: encodeAllowanceCompValue({
            allowanceKey,
            adapter: zeroAdapter.address,
            targetDecimals: 18,
            sourceDecimals: 6,
          }),
        },
      ]);

      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke(1000n),
        roles,
        "ConditionViolation",
        [
          ConditionViolationStatus.PricingAdapterZeroPrice,
          1n, // WithinAllowance node
          anyValue,
        ],
      );
    });
  });

  describe("WithinAllowance - from EtherValue", () => {
    it("enforces ether allowance from transaction.value", async () => {
      const { roleKey, owner, member, roles, testContract } =
        await loadFixture(setupTestContract);

      // Fund the avatar
      const avatarAddress = await roles.read.avatar();
      await owner.sendTransaction({
        to: avatarAddress,
        value: parseEther("1"),
      });

      const allowanceKey =
        "0x0000000000000000000000000000000000000000000000000000000000000001";

      await setAllowance(
        roles,
        allowanceKey,
        {
          balance: 10000,
          period: 0,
          refill: 0,
          timestamp: 0,
        },
        owner.account,
      );

      const abi = parseAbi(["function oneParamStatic(uint256)"]);
      const selector = toFunctionSelector(abi[0]);

      // Static param passes, EtherValue checks allowance
      const packed = await packConditions(roles, [
        {
          parent: 0,
          paramType: Encoding.None,
          operator: Operator.And,
          compValue: "0x",
        },
        {
          parent: 0,
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          compValue: "0x",
        },
        {
          parent: 0,
          paramType: Encoding.EtherValue,
          operator: Operator.WithinAllowance,
          compValue: encodeAbiParameters(parseAbiParameters("bytes32"), [
            allowanceKey,
          ]),
        },
        {
          parent: 1,
          paramType: Encoding.Static,
          operator: Operator.Pass,
          compValue: "0x",
        },
      ]);
      await roles.write.allowFunctionPacked([
        roleKey,
        testContract.address,
        selector,
        packed,
        ExecutionOptions.Send,
      ]);

      async function invoke(value: bigint, param: bigint) {
        return roles.write.execTransactionFromModule(
          [
            testContract.address,
            value,
            encodeFunctionData({
              abi,
              functionName: "oneParamStatic",
              args: [param],
            }),
            0,
          ],
          { account: member.account },
        );
      }

      // Exceeds allowance
      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke(10001n, 123n),
        roles,
        "ConditionViolation",
        [
          ConditionViolationStatus.AllowanceExceeded,
          2n, // WithinAllowance node: And[0] -> Matches[1], WithinAllowance[2]
          anyValue,
        ],
      );

      // Within allowance
      await invoke(5000n, 456n);
      assert.equal(
        (await roles.read.accruedAllowance([allowanceKey]))[0],
        5000n,
      );

      // Exhaust remaining
      await invoke(5000n, 789n);
      assert.equal((await roles.read.accruedAllowance([allowanceKey]))[0], 0n);

      // Now fails
      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke(1n, 999n),
        roles,
        "ConditionViolation",
        [
          ConditionViolationStatus.AllowanceExceeded,
          2n, // WithinAllowance node: And[0] -> Matches[1], WithinAllowance[2]
          anyValue,
        ],
      );
    });
  });

  describe("violation context", () => {
    it("reports the violating node index", async () => {
      const { owner, roles, allowFunction, invoke } =
        await loadFixture(setupOneParam);

      const allowanceKey = toHex(randomBytes(32));

      await setAllowance(
        roles,
        allowanceKey,
        {
          balance: 100,
          period: 0,
          refill: 0,
          timestamp: 0,
        },
        owner.account,
      );

      await allowFunction([
        {
          parent: 0,
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          compValue: "0x",
        },
        {
          parent: 0,
          paramType: Encoding.Static,
          operator: Operator.WithinAllowance,
          compValue: encodeAbiParameters(parseAbiParameters("bytes32"), [
            allowanceKey,
          ]),
        },
      ]);

      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke(101n),
        roles,
        "ConditionViolation",
        [
          ConditionViolationStatus.AllowanceExceeded,
          1n, // WithinAllowance node at BFS index 1
          anyValue,
        ],
      );
    });

    it("reports the calldata range of the violation", async () => {
      const { owner, roles, allowFunction, invoke } =
        await loadFixture(setupOneParam);

      const allowanceKey = toHex(randomBytes(32));

      await setAllowance(
        roles,
        allowanceKey,
        {
          balance: 100,
          period: 0,
          refill: 0,
          timestamp: 0,
        },
        owner.account,
      );

      await allowFunction([
        {
          parent: 0,
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          compValue: "0x",
        },
        {
          parent: 0,
          paramType: Encoding.Static,
          operator: Operator.WithinAllowance,
          compValue: encodeAbiParameters(parseAbiParameters("bytes32"), [
            allowanceKey,
          ]),
        },
      ]);

      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke(101n),
        roles,
        "ConditionViolation",
        [
          ConditionViolationStatus.AllowanceExceeded,
          anyValue,
          4n, // calldataOffset: parameter starts at byte 4
        ],
      );
    });
  });
});
