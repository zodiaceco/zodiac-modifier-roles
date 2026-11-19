import { expect } from "chai";
import { anyValue } from "@nomicfoundation/hardhat-ethers-chai-matchers/withArgs";

import {
  AbiCoder,
  hexlify,
  Interface,
  parseEther,
  parseUnits,
  randomBytes,
  solidityPacked,
} from "ethers";
import type { BigNumberish } from "ethers";

const defaultAbiCoder = AbiCoder.defaultAbiCoder();

import { network } from "hardhat";

import {
  Encoding,
  ExecutionOptions,
  Operator,
  ConditionViolationStatus,
  packConditions,
} from "../utils.js";
import { createSetup } from "../setup.js";

import type { Roles } from "../../typechain-types/index.js";

const connection = await network.create();
const { ethers, networkHelpers } = connection;
const { loadFixture, time } = networkHelpers;
const { setupTestContract, setupOneParam, setupTwoParams } =
  createSetup(connection);

describe("Operator - WithinAllowance", async () => {
  after(async () => {
    await connection.close();
  });

  function setAllowance(
    roles: Roles,
    allowanceKey: string,
    {
      balance,
      maxRefill,
      refill,
      period,
      timestamp,
    }: {
      balance: BigNumberish;
      maxRefill?: BigNumberish;
      refill: BigNumberish;
      period: BigNumberish;
      timestamp: BigNumberish;
    },
  ) {
    return roles.setAllowance(
      allowanceKey,
      balance,
      maxRefill || 0,
      refill,
      period,
      timestamp,
    );
  }

  describe("WithinAllowance - Check", () => {
    it("passes a check with enough balance available and no refill (interval = 0)", async () => {
      const { owner, roles, allowFunction, invoke } =
        await loadFixture(setupOneParam);

      const allowanceKey =
        "0x0000000000000000000000000000000000000000000000000000000000000001";

      await setAllowance(await roles.connect(owner), allowanceKey, {
        balance: 1000,
        period: 0,
        refill: 0,
        timestamp: 0,
      });

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
          compValue: defaultAbiCoder.encode(["bytes32"], [allowanceKey]),
        },
      ]);

      await expect(invoke(1001))
        .to.be.revertedWithCustomError(roles, `ConditionViolation`)
        .withArgs(
          ConditionViolationStatus.AllowanceExceeded,
          1, // WithinAllowance node
          anyValue,
        );

      await expect(invoke(1000)).to.not.be.revert(ethers);
      await expect(invoke(1))
        .to.be.revertedWithCustomError(roles, `ConditionViolation`)
        .withArgs(
          ConditionViolationStatus.AllowanceExceeded,
          1, // WithinAllowance node
          anyValue,
        );
    });
    it("passes a check with only from balance and refill configured", async () => {
      const { roles, owner, allowFunction, invoke } =
        await loadFixture(setupOneParam);

      const allowanceKey = hexlify(randomBytes(32));

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
          compValue: defaultAbiCoder.encode(["bytes32"], [allowanceKey]),
        },
      ]);

      const timestamp = await time.latest();
      await setAllowance(await roles.connect(owner), allowanceKey, {
        balance: 333,
        period: 1000,
        refill: 100,
        timestamp: timestamp,
      });

      await expect(invoke(334))
        .to.be.revertedWithCustomError(roles, `ConditionViolation`)
        .withArgs(
          ConditionViolationStatus.AllowanceExceeded,
          1, // WithinAllowance node
          anyValue,
        );
      await expect(invoke(333)).to.not.be.revert(ethers);
      await expect(invoke(1))
        .to.be.revertedWithCustomError(roles, `ConditionViolation`)
        .withArgs(
          ConditionViolationStatus.AllowanceExceeded,
          1, // WithinAllowance node
          anyValue,
        );
    });
    it("passes a check balance from available+refill", async () => {
      const { roles, owner, allowFunction, invoke } =
        await loadFixture(setupOneParam);

      const allowanceKey = hexlify(randomBytes(32));

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
          compValue: defaultAbiCoder.encode(["bytes32"], [allowanceKey]),
        },
      ]);

      const timestamp = await time.latest();
      await setAllowance(await roles.connect(owner), allowanceKey, {
        balance: 250,
        period: 500,
        refill: 100,
        timestamp: timestamp - 750,
      });

      await expect(invoke(351))
        .to.be.revertedWithCustomError(roles, `ConditionViolation`)
        .withArgs(
          ConditionViolationStatus.AllowanceExceeded,
          1, // WithinAllowance node
          anyValue,
        );

      await expect(invoke(350)).to.not.be.revert(ethers);
      await expect(invoke(1))
        .to.be.revertedWithCustomError(roles, `ConditionViolation`)
        .withArgs(
          ConditionViolationStatus.AllowanceExceeded,
          1, // WithinAllowance node
          anyValue,
        );
    });
    it("fails a check, with some balance and not enough elapsed for next refill", async () => {
      const { owner, roles, allowFunction, invoke } =
        await loadFixture(setupOneParam);
      const allowanceKey = hexlify(randomBytes(32));

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
          compValue: defaultAbiCoder.encode(["bytes32"], [allowanceKey]),
        },
      ]);

      const timestamp = await time.latest();
      await setAllowance(await roles.connect(owner), allowanceKey, {
        balance: 250,
        period: 1000,
        refill: 100,
        timestamp: timestamp - 50,
      });

      await expect(invoke(251))
        .to.be.revertedWithCustomError(roles, `ConditionViolation`)
        .withArgs(
          ConditionViolationStatus.AllowanceExceeded,
          1, // WithinAllowance node
          anyValue,
        );

      await expect(invoke(250)).to.not.be.revert(ethers);
      await expect(invoke(1))
        .to.be.revertedWithCustomError(roles, `ConditionViolation`)
        .withArgs(
          ConditionViolationStatus.AllowanceExceeded,
          1, // WithinAllowance node
          anyValue,
        );
    });
    it("passes a check with balance from refill and bellow maxRefill", async () => {
      const { owner, roles, allowFunction, invoke } =
        await loadFixture(setupOneParam);

      const interval = 10000;
      const allowanceKey = hexlify(randomBytes(32));

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
          compValue: defaultAbiCoder.encode(["bytes32"], [allowanceKey]),
        },
      ]);

      const timestamp = await time.latest();
      await setAllowance(await roles.connect(owner), allowanceKey, {
        balance: 0,
        maxRefill: 1000,
        period: interval,
        refill: 9999999,
        timestamp: timestamp - interval * 10,
      });

      await expect(invoke(1001))
        .to.be.revertedWithCustomError(roles, `ConditionViolation`)
        .withArgs(
          ConditionViolationStatus.AllowanceExceeded,
          1, // WithinAllowance node
          anyValue,
        );

      await expect(invoke(1000)).to.not.be.revert(ethers);
    });
    it("fails a check with balance from refill but capped by maxRefill", async () => {
      const { owner, roles, allowFunction, invoke } =
        await loadFixture(setupOneParam);

      const allowanceKey = hexlify(randomBytes(32));
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
          compValue: defaultAbiCoder.encode(["bytes32"], [allowanceKey]),
        },
      ]);

      const timestamp = await time.latest();
      await setAllowance(await roles.connect(owner), allowanceKey, {
        balance: 0,
        maxRefill: 9000,
        period: 1000,
        refill: 10000,
        timestamp: timestamp - 5000,
      });

      await expect(invoke(9001))
        .to.be.revertedWithCustomError(roles, `ConditionViolation`)
        .withArgs(
          ConditionViolationStatus.AllowanceExceeded,
          1, // WithinAllowance node
          anyValue,
        );

      await expect(invoke(9000)).to.not.be.revert(ethers);
    });
    it("fails a check with AllowanceExceeded when value exceeds uint128 max", async () => {
      const { owner, roles, allowFunction, invoke } =
        await loadFixture(setupOneParam);

      const allowanceKey = hexlify(randomBytes(32));

      await setAllowance(await roles.connect(owner), allowanceKey, {
        balance: 1000,
        period: 0,
        refill: 0,
        timestamp: 0,
      });

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
          compValue: defaultAbiCoder.encode(["bytes32"], [allowanceKey]),
        },
      ]);

      // uint128 max + 1: no longer a dedicated AllowanceValueOverflow, since
      // full-precision comparison classifies it as exceeding any balance
      const exceedsUint128 = 2n ** 128n;

      await expect(invoke(exceedsUint128))
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(
          ConditionViolationStatus.AllowanceExceeded,
          1, // WithinAllowance node
          anyValue,
        );
    });
  });

  describe("WithinAllowance - Consumption", async () => {
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
          compValue: defaultAbiCoder.encode(["bytes32"], [allowanceKey]),
        },
        {
          parent: 0,
          paramType: Encoding.Static,
          operator: Operator.WithinAllowance,
          compValue: defaultAbiCoder.encode(["bytes32"], [allowanceKey]),
        },
      ]);

      await setAllowance(await roles.connect(owner), allowanceKey, {
        balance: 3000,
        period: 0,
        refill: 0,
        timestamp: 0,
      });

      let allowance = await roles.accruedAllowance(allowanceKey);
      expect(allowance.balance).to.equal(3000);

      await expect(invoke(3001, 3001))
        .to.be.revertedWithCustomError(roles, `ConditionViolation`)
        .withArgs(
          ConditionViolationStatus.AllowanceExceeded,
          1, // First WithinAllowance node
          anyValue,
        );
      allowance = await roles.accruedAllowance(allowanceKey);
      expect(allowance.balance).to.equal(3000);

      await expect(invoke(1500, 1500)).to.not.be.revert(ethers);
      allowance = await roles.accruedAllowance(allowanceKey);
      expect(allowance.balance).to.equal(0);
    });
    it("Consumes from different allowances in same transaction", async () => {
      const { owner, roles, invoke, allowFunction } =
        await loadFixture(setupTwoParams);

      const allowanceKey1 = hexlify(randomBytes(32));
      const allowanceKey2 = hexlify(randomBytes(32));

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
          compValue: defaultAbiCoder.encode(["bytes32"], [allowanceKey1]),
        },
        {
          parent: 0,
          paramType: Encoding.Static,
          operator: Operator.WithinAllowance,
          compValue: defaultAbiCoder.encode(["bytes32"], [allowanceKey2]),
        },
      ]);

      await setAllowance(await roles.connect(owner), allowanceKey1, {
        balance: 1000,
        period: 0,
        refill: 0,
        timestamp: 0,
      });

      await setAllowance(await roles.connect(owner), allowanceKey2, {
        balance: 2000,
        period: 0,
        refill: 0,
        timestamp: 0,
      });

      // Both allowances consumed independently
      await expect(invoke(500, 1000)).to.not.be.revert(ethers);

      const allowance1 = await roles.accruedAllowance(allowanceKey1);
      const allowance2 = await roles.accruedAllowance(allowanceKey2);
      expect(allowance1.balance).to.equal(500);
      expect(allowance2.balance).to.equal(1000);
    });
    it("Fails, when multiple parameters referencing the same limit overspend", async () => {
      const { owner, roles, invoke, allowFunction } =
        await loadFixture(setupTwoParams);
      const allowanceKey = hexlify(randomBytes(32));

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
          compValue: defaultAbiCoder.encode(["bytes32"], [allowanceKey]),
        },
        {
          parent: 0,
          paramType: Encoding.Static,
          operator: Operator.WithinAllowance,
          compValue: defaultAbiCoder.encode(["bytes32"], [allowanceKey]),
        },
      ]);

      await setAllowance(await roles.connect(owner), allowanceKey, {
        balance: 3000,
        period: 0,
        refill: 0,
        timestamp: 0,
      });

      let allowance = await roles.accruedAllowance(allowanceKey);
      expect(allowance.balance).to.equal(3000);

      await expect(invoke(3000, 1))
        .to.be.revertedWithCustomError(roles, `ConditionViolation`)
        .withArgs(
          ConditionViolationStatus.AllowanceExceeded,
          2, // Second WithinAllowance node (first consumes 3000, second fails with 1)
          anyValue,
        );
      allowance = await roles.accruedAllowance(allowanceKey);
      expect(allowance.balance).to.equal(3000);
    });
    it("Updates timestamp", async () => {
      const { owner, roles, invoke, allowFunction } =
        await loadFixture(setupOneParam);

      const interval = 600;
      const allowanceKey = hexlify(randomBytes(32));

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
          compValue: defaultAbiCoder.encode(["bytes32"], [allowanceKey]),
        },
      ]);

      await setAllowance(await roles.connect(owner), allowanceKey, {
        balance: 100,
        period: BigInt(interval),
        refill: 0,
        timestamp: 1,
      });

      // Use allowances() for raw storage timestamp checks
      let allowance = await roles.allowances(allowanceKey);
      expect(allowance.balance).to.equal(100);
      expect(allowance.timestamp).to.equal(1);

      await expect(invoke(0)).to.not.be.revert(ethers);
      const now = BigInt(await time.latest());

      allowance = await roles.allowances(allowanceKey);
      expect(allowance.timestamp).to.be.gt(1);
      const timeDifference = now - allowance.timestamp;
      expect(timeDifference).to.be.lte(interval * 2);
    });
    it("Does not updates timestamp if interval is zero", async () => {
      const { owner, roles, invoke, allowFunction } =
        await loadFixture(setupOneParam);
      const allowanceKey = hexlify(randomBytes(32));
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
          compValue: defaultAbiCoder.encode(["bytes32"], [allowanceKey]),
        },
      ]);
      await setAllowance(await roles.connect(owner), allowanceKey, {
        balance: 1,
        period: 0,
        refill: 0,
        timestamp: 123,
      });

      await expect(invoke(0)).to.not.be.revert(ethers);

      // Use allowances() for raw storage timestamp checks
      const allowance = await roles.allowances(allowanceKey);
      expect(allowance.timestamp).to.equal(123);
    });
    it("Updates timestamp from past timestamp", async () => {
      const { owner, roles, invoke, allowFunction } =
        await loadFixture(setupOneParam);

      const interval = 600;

      const allowanceKey = hexlify(randomBytes(32));

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
          compValue: defaultAbiCoder.encode(["bytes32"], [allowanceKey]),
        },
      ]);

      const timestamp = (await time.latest()) - 2400;
      await setAllowance(await roles.connect(owner), allowanceKey, {
        balance: 1,
        period: interval,
        refill: 0,
        timestamp: timestamp,
      });

      // Use allowances() for raw storage timestamp checks
      let allowance = await roles.allowances(allowanceKey);
      expect(allowance.timestamp).to.equal(timestamp);

      await expect(invoke(0)).to.not.be.revert(ethers);

      allowance = await roles.allowances(allowanceKey);
      expect(allowance.timestamp).to.be.greaterThan(timestamp);
    });
    it("Does not update timestamp from future timestamp", async () => {
      const { owner, roles, invoke, allowFunction } =
        await loadFixture(setupOneParam);

      const interval = 600;
      const allowanceKey = hexlify(randomBytes(32));
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
          compValue: defaultAbiCoder.encode(["bytes32"], [allowanceKey]),
        },
      ]);
      const timestamp = (await time.latest()) + 1200;
      await setAllowance(await roles.connect(owner), allowanceKey, {
        balance: 1,
        period: interval,
        refill: 0,
        timestamp: timestamp,
      });

      // Use allowances() for raw storage timestamp checks
      let allowance = await roles.allowances(allowanceKey);
      expect(allowance.timestamp).to.equal(timestamp);

      await expect(invoke(0)).to.not.be.revert(ethers);

      allowance = await roles.allowances(allowanceKey);
      expect(allowance.timestamp).to.equal(timestamp);
    });
  });

  describe("WithinAllowance - Decimal Conversion (no price adapter)", () => {
    function encodeDecimalsOnly({
      allowanceKey,
      targetDecimals,
      sourceDecimals,
    }: {
      allowanceKey: string;
      targetDecimals: number;
      sourceDecimals: number;
    }): string {
      return solidityPacked(
        ["bytes32", "uint8", "uint8"],
        [allowanceKey, targetDecimals, sourceDecimals],
      );
    }

    const allowanceKey = hexlify(randomBytes(32));

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
      await setAllowance(await roles.connect(owner), allowanceKey, {
        balance: 1000n * 10n ** 18n,
        period: 0,
        refill: 0,
        timestamp: 0,
      });

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
      await expect(invoke(500n * 10n ** 6n)).to.not.be.revert(ethers);

      const allowance = await roles.accruedAllowance(allowanceKey);
      expect(allowance.balance).to.equal(500n * 10n ** 18n); // 500 DAI remaining
    });

    it("USDC (6 dec) → DAI (18 dec): reverts when exceeding allowance", async () => {
      const { owner, roles, allowFunction, invoke } =
        await loadFixture(setupOneParam);

      // Allowance: 100 DAI
      await setAllowance(await roles.connect(owner), allowanceKey, {
        balance: 100n * 10n ** 18n,
        period: 0,
        refill: 0,
        timestamp: 0,
      });

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
      await expect(invoke(101n * 10n ** 6n))
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(
          ConditionViolationStatus.AllowanceExceeded,
          1, // WithinAllowance node
          anyValue,
        );
    });

    /**
     * Reverse direction: DAI → USDC (scaling down)
     */
    it("DAI (18 dec) → USDC (6 dec): scales down correctly", async () => {
      const { owner, roles, allowFunction, invoke } =
        await loadFixture(setupOneParam);

      // Allowance: 1000 USDC (6 decimals)
      await setAllowance(await roles.connect(owner), allowanceKey, {
        balance: 1000n * 10n ** 6n,
        period: 0,
        refill: 0,
        timestamp: 0,
      });

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
      await expect(invoke(500n * 10n ** 18n)).to.not.be.revert(ethers);

      const allowance = await roles.accruedAllowance(allowanceKey);
      expect(allowance.balance).to.equal(500n * 10n ** 6n); // 500 USDC remaining
    });

    it("should cumulatively charge dust-sized calls", async () => {
      const { owner, roles, allowFunction, invoke } =
        await loadFixture(setupOneParam);

      await setAllowance(await roles.connect(owner), allowanceKey, {
        balance: 10n,
        period: 0,
        refill: 0,
        timestamp: 0,
      });

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
      await expect(invoke(dust)).to.not.be.revert(ethers); // consumed 0.9
      await expect(invoke(dust)).to.not.be.revert(ethers); // consumed 1.8
      await expect(invoke(dust)).to.not.be.revert(ethers); // consumed 2.7
      await expect(invoke(dust)).to.not.be.revert(ethers); // consumed 3.6

      const allowance = await roles.accruedAllowance(allowanceKey);
      // Expected behavior: split calls should at least as much as the same as an aggregated call.
      expect(allowance.balance).to.be.lessThanOrEqual(10n - 4n);
    });

    it("sub-unit dust consumes exactly 1 in target precision", async () => {
      const { owner, roles, allowFunction, invoke } =
        await loadFixture(setupOneParam);

      // 100 USDC allowance (6 decimals)
      await setAllowance(await roles.connect(owner), allowanceKey, {
        balance: 100 * 10 ** 5,
        period: 0,
        refill: 0,
        timestamp: 0,
      });

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
      await expect(invoke(1n)).to.not.be.revert(ethers);

      const allowance = await roles.accruedAllowance(allowanceKey);
      // consumed exactly 0.000001 USDC (1 in 6 dec precision)
      expect(allowance.balance).to.equal(parseUnits("99.99999", 5));
    });

    it("zero value consumes nothing", async () => {
      const { owner, roles, allowFunction, invoke } =
        await loadFixture(setupOneParam);

      await setAllowance(await roles.connect(owner), allowanceKey, {
        balance: parseUnits("100", 6),
        period: 0,
        refill: 0,
        timestamp: 0,
      });

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

      await expect(invoke(0n)).to.not.be.revert(ethers);

      const allowance = await roles.accruedAllowance(allowanceKey);
      expect(allowance.balance).to.equal(parseUnits("100", 6));
    });
  });

  describe("WithinAllowance - Price Adapter", () => {
    function encodeAllowanceCompValue({
      allowanceKey,
      targetDecimals = 0,
      sourceDecimals = 0,
      adapter = "0x0000000000000000000000000000000000000000",
    }: {
      allowanceKey: string;
      targetDecimals?: number;
      sourceDecimals?: number;
      adapter?: string;
    }): string {
      return solidityPacked(
        ["bytes32", "uint8", "uint8", "address"],
        [allowanceKey, targetDecimals, sourceDecimals, adapter],
      );
    }

    const allowanceKey =
      "0x0000000000000000000000000000000000000000000000000000000000000001";

    it("price-converted dust rounds up and consumes 1 in target precision", async () => {
      const { owner, roles, allowFunction, invoke } =
        await loadFixture(setupOneParam);

      const MockPricing = await ethers.getContractFactory("MockPricing");

      /*
       * Spend: 1 source unit (0 decimals). Price: 0.5, encoded as 5e17 with
       * 18 decimals. Allowance: 2 target units (0 decimals).
       *
       * Each spend converts to 1 * 5e17 / 1e18 = 0.5 target units and must
       * consume ceil(0.5) = 1: balance goes 2 → 1 → 0, then reverts.
       * Floored, it would consume 0 and let unlimited dust spends through.
       */
      const adapter = await MockPricing.deploy(5n * 10n ** 17n); // 0.5x

      await setAllowance(await roles.connect(owner), allowanceKey, {
        balance: 2,
        period: 0,
        refill: 0,
        timestamp: 0,
      });

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
            adapter: await adapter.getAddress(),
          }),
        },
      ]);

      expect((await roles.accruedAllowance(allowanceKey)).balance).to.equal(2);
      // each spend converts to 0.5, and consumes ceil(0.5) = 1, never 0
      await expect(invoke(1)).to.not.be.revert(ethers);
      expect((await roles.accruedAllowance(allowanceKey)).balance).to.equal(1);
      await expect(invoke(1)).to.not.be.revert(ethers);
      expect((await roles.accruedAllowance(allowanceKey)).balance).to.equal(0);

      await expect(invoke(1))
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(ConditionViolationStatus.AllowanceExceeded, 1, anyValue);
    });

    it("accumulates conversion truncation against the allowance", async () => {
      const { owner, roles, allowFunction, invoke } =
        await loadFixture(setupOneParam);

      const MockPricing = await ethers.getContractFactory("MockPricing");
      const adapter = await MockPricing.deploy(15n * 10n ** 17n); // 1.5x

      await setAllowance(await roles.connect(owner), allowanceKey, {
        balance: 3,
        period: 0,
        refill: 0,
        timestamp: 0,
      });

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
            adapter: await adapter.getAddress(),
          }),
        },
      ]);

      // One input unit is worth 1.5 allowance units, so it consumes 2.
      await expect(invoke(1)).to.not.be.revert(ethers);
      expect((await roles.accruedAllowance(allowanceKey)).balance).to.equal(1);

      // A second input needs another 2 units and cannot spend the remaining 1.
      await expect(invoke(1))
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(ConditionViolationStatus.AllowanceExceeded, 1, anyValue);
    });

    // base=12, param=6: scale up by 10^6
    // 1000 units (6 dec) → converted = 1000e6 * 1e18 * 1e12 / 1e24 = 1000e12 (12 dec)
    it("param(6) → base(12): consumes correctly", async () => {
      const { owner, roles, allowFunction, invoke } =
        await loadFixture(setupOneParam);

      const MockPricing = await ethers.getContractFactory("MockPricing");
      const adapter = await MockPricing.deploy(10n ** 18n); // 1:1 price

      await setAllowance(await roles.connect(owner), allowanceKey, {
        balance: 2000n * 10n ** 12n, // 2000 units in 12 decimals
        period: 0,
        refill: 0,
        timestamp: 0,
      });

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
            adapter: await adapter.getAddress(),
            targetDecimals: 12,
            sourceDecimals: 6,
          }),
        },
      ]);

      // spend 1000 (6 dec) → 1000e12 (12 dec)
      await expect(invoke(1000n * 10n ** 6n)).to.not.be.revert(ethers);

      const allowance = await roles.accruedAllowance(allowanceKey);
      // sent in 1000 in 6 decimals, but it consumed in 12 decimals
      expect(allowance.balance).to.equal(1000n * 10n ** 12n);
    });

    it("param(6) → base(12): reverts on overconsume", async () => {
      const { owner, roles, allowFunction, invoke } =
        await loadFixture(setupOneParam);

      const MockPricing = await ethers.getContractFactory("MockPricing");
      const adapter = await MockPricing.deploy(10n ** 18n);

      await setAllowance(await roles.connect(owner), allowanceKey, {
        balance: 1000n * 10n ** 12n, // exactly 1000 units (12 dec)
        period: 0,
        refill: 0,
        timestamp: 0,
      });

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
            adapter: await adapter.getAddress(),
            targetDecimals: 12,
            sourceDecimals: 6,
          }),
        },
      ]);

      // 1001 (6 dec) → 1001e12 (12 dec) > 1000e12
      await expect(invoke(1001n * 10n ** 6n))
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(
          ConditionViolationStatus.AllowanceExceeded,
          1, // WithinAllowance node
          anyValue,
        );
    });

    // base=18, param=6: scale up by 10^12
    it("param(6) → base(18): consumes correctly", async () => {
      const { owner, roles, allowFunction, invoke } =
        await loadFixture(setupOneParam);

      const MockPricing = await ethers.getContractFactory("MockPricing");
      const adapter = await MockPricing.deploy(10n ** 18n);

      await setAllowance(await roles.connect(owner), allowanceKey, {
        balance: 2000n * 10n ** 18n,
        period: 0,
        refill: 0,
        timestamp: 0,
      });

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
            adapter: await adapter.getAddress(),
            targetDecimals: 18,
            sourceDecimals: 6,
          }),
        },
      ]);

      // spend 1000 (6 dec) → 1000e18 (18 dec)
      await expect(invoke(1000n * 10n ** 6n)).to.not.be.revert(ethers);

      const allowance = await roles.accruedAllowance(allowanceKey);
      expect(allowance.balance).to.equal(1000n * 10n ** 18n);
    });

    it("param(6) → base(18): reverts on overconsume", async () => {
      const { owner, roles, allowFunction, invoke } =
        await loadFixture(setupOneParam);

      const MockPricing = await ethers.getContractFactory("MockPricing");
      const adapter = await MockPricing.deploy(10n ** 18n);

      await setAllowance(await roles.connect(owner), allowanceKey, {
        balance: 1000n * 10n ** 18n,
        period: 0,
        refill: 0,
        timestamp: 0,
      });

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
            adapter: await adapter.getAddress(),
            targetDecimals: 18,
            sourceDecimals: 6,
          }),
        },
      ]);

      await expect(invoke(1001n * 10n ** 6n))
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(
          ConditionViolationStatus.AllowanceExceeded,
          1, // WithinAllowance node
          anyValue,
        );
    });

    // base=6, param=12: scale down by 10^6
    it("param(12) → base(6): consumes correctly", async () => {
      const { owner, roles, allowFunction, invoke } =
        await loadFixture(setupOneParam);

      const MockPricing = await ethers.getContractFactory("MockPricing");
      const adapter = await MockPricing.deploy(10n ** 18n);

      await setAllowance(await roles.connect(owner), allowanceKey, {
        balance: 900n * 10n ** 6n, // 900 units (6 dec)
        period: 0,
        refill: 0,
        timestamp: 0,
      });

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
            adapter: await adapter.getAddress(),
            targetDecimals: 6,
            sourceDecimals: 12,
          }),
        },
      ]);

      // spend 1000 (12 dec) → 1000 * 1e6 / 1e6 = 1000 (6 dec) ... wait
      // formula: value * price * 10^base / 10^(18 + param)
      // = 1000e12 * 1e18 * 1e6 / 1e30 = 1000e36 / 1e30 = 1000e6
      await expect(invoke(500n * 10n ** 12n)).to.not.be.revert(ethers);

      const allowance = await roles.accruedAllowance(allowanceKey);
      expect(allowance.balance).to.equal(400n * 10n ** 6n);
    });

    it("param(12) → base(6): reverts on overconsume", async () => {
      const { owner, roles, allowFunction, invoke } =
        await loadFixture(setupOneParam);

      const MockPricing = await ethers.getContractFactory("MockPricing");
      const adapter = await MockPricing.deploy(10n ** 18n);

      await setAllowance(await roles.connect(owner), allowanceKey, {
        balance: 1000n * 10n ** 6n,
        period: 0,
        refill: 0,
        timestamp: 0,
      });

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
            adapter: await adapter.getAddress(),
            targetDecimals: 6,
            sourceDecimals: 12,
          }),
        },
      ]);

      await expect(invoke(1001n * 10n ** 12n))
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(
          ConditionViolationStatus.AllowanceExceeded,
          1, // WithinAllowance node
          anyValue,
        );
    });

    // base=12, param=18: scale down by 10^6
    it("param(18) → base(12): consumes correctly", async () => {
      const { owner, roles, allowFunction, invoke } =
        await loadFixture(setupOneParam);

      const MockPricing = await ethers.getContractFactory("MockPricing");
      const adapter = await MockPricing.deploy(10n ** 18n);

      await setAllowance(await roles.connect(owner), allowanceKey, {
        balance: 2000n * 10n ** 12n,
        period: 0,
        refill: 0,
        timestamp: 0,
      });

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
            adapter: await adapter.getAddress(),
            targetDecimals: 12,
            sourceDecimals: 18,
          }),
        },
      ]);

      // 1000e18 * 1e18 * 1e12 / 1e36 = 1000e12
      await expect(invoke(1000n * 10n ** 18n)).to.not.be.revert(ethers);

      const allowance = await roles.accruedAllowance(allowanceKey);
      expect(allowance.balance).to.equal(1000n * 10n ** 12n);
    });

    it("param(18) → base(12): reverts on overconsume", async () => {
      const { owner, roles, allowFunction, invoke } =
        await loadFixture(setupOneParam);

      const MockPricing = await ethers.getContractFactory("MockPricing");
      const adapter = await MockPricing.deploy(10n ** 18n);

      await setAllowance(await roles.connect(owner), allowanceKey, {
        balance: 1000n * 10n ** 12n,
        period: 0,
        refill: 0,
        timestamp: 0,
      });

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
            adapter: await adapter.getAddress(),
            targetDecimals: 12,
            sourceDecimals: 18,
          }),
        },
      ]);

      await expect(invoke(1001n * 10n ** 18n))
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(
          ConditionViolationStatus.AllowanceExceeded,
          1, // WithinAllowance node
          anyValue,
        );
    });

    // DAI (18 dec) spending against USDC (6 dec) allowance
    it("spend DAI(18) → base USDC(6)", async () => {
      const { owner, roles, allowFunction, invoke } =
        await loadFixture(setupOneParam);

      const MockPricing = await ethers.getContractFactory("MockPricing");
      // DAI/USDC price = 1e18 (1:1)
      const adapter = await MockPricing.deploy(10n ** 18n);

      await setAllowance(await roles.connect(owner), allowanceKey, {
        balance: 1000n * 10n ** 6n, // 1000 USDC
        period: 0,
        refill: 0,
        timestamp: 0,
      });

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
            adapter: await adapter.getAddress(),
            targetDecimals: 6,
            sourceDecimals: 18,
          }),
        },
      ]);

      // spend 500 DAI (18 dec) → 500 USDC (6 dec)
      await expect(invoke(500n * 10n ** 18n)).to.not.be.revert(ethers);

      const allowance = await roles.accruedAllowance(allowanceKey);
      expect(allowance.balance).to.equal(500n * 10n ** 6n);
    });

    // USDC (6 dec) spending against DAI (18 dec) allowance
    it("spend USDC(6) → base DAI(18)", async () => {
      const { owner, roles, allowFunction, invoke } =
        await loadFixture(setupOneParam);

      const MockPricing = await ethers.getContractFactory("MockPricing");
      const adapter = await MockPricing.deploy(10n ** 18n);

      await setAllowance(await roles.connect(owner), allowanceKey, {
        balance: 1000n * 10n ** 18n, // 1000 DAI
        period: 0,
        refill: 0,
        timestamp: 0,
      });

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
            adapter: await adapter.getAddress(),
            targetDecimals: 18,
            sourceDecimals: 6,
          }),
        },
      ]);

      // spend 500 USDC (6 dec) → 500 DAI (18 dec)
      await expect(invoke(500n * 10n ** 6n)).to.not.be.revert(ethers);

      const allowance = await roles.accruedAllowance(allowanceKey);
      expect(allowance.balance).to.equal(500n * 10n ** 18n);
    });

    // Multi-asset: USDC(6), DAI(18), ETH(18) all convert to USDC(6) base allowance
    it("multi-asset (USDC + DAI + ETH) → base USDC(6)", async () => {
      const { owner, roles, invoke, allowFunction } =
        await loadFixture(setupTwoParams);

      const MockPricing = await ethers.getContractFactory("MockPricing");
      const usdcAdapter = await MockPricing.deploy(10n ** 18n); // 1:1
      const ethAdapter = await MockPricing.deploy(2000n * 10n ** 18n); // 1 ETH = 2000 USDC

      await setAllowance(await roles.connect(owner), allowanceKey, {
        balance: 5000n * 10n ** 6n, // 5000 USDC
        period: 0,
        refill: 0,
        timestamp: 0,
      });

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
            adapter: await usdcAdapter.getAddress(),
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
            adapter: await ethAdapter.getAddress(),
            targetDecimals: 6,
            sourceDecimals: 18,
          }),
        },
      ]);

      // spend 1000 USDC + 1 ETH (2000 USDC) = 3000 USDC total
      await expect(invoke(1000n * 10n ** 6n, 1n * 10n ** 18n)).to.not.be.revert(
        ethers,
      );

      let allowance = await roles.accruedAllowance(allowanceKey);
      expect(allowance.balance).to.equal(2000n * 10n ** 6n); // 5000 - 3000 = 2000

      // spend remaining: 0 USDC + 1 ETH = 2000 USDC
      await expect(invoke(0, 1n * 10n ** 18n)).to.not.be.revert(ethers);

      allowance = await roles.accruedAllowance(allowanceKey);
      expect(allowance.balance).to.equal(0);

      // any more reverts
      await expect(invoke(1, 0))
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(
          ConditionViolationStatus.AllowanceExceeded,
          1, // First WithinAllowance node
          anyValue,
        );
    });

    it("preserves decimal precision when scaling down (18 → 6)", async () => {
      const { owner, roles, allowFunction, invoke } =
        await loadFixture(setupOneParam);

      const MockPricing = await ethers.getContractFactory("MockPricing");
      const adapter = await MockPricing.deploy(10n ** 18n); // 1:1 price

      // 1.123456789123456789 in 18 decimals
      const valueInParamDecimals = 1123456789123456789n;
      // Expected: 1.123457 in 6 decimals (rounds up after 6 decimals)
      const valueInAccrueDecimals = 1123457n;

      await setAllowance(await roles.connect(owner), allowanceKey, {
        balance: valueInAccrueDecimals,
        period: 0,
        refill: 0,
        timestamp: 0,
      });

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
            adapter: await adapter.getAddress(),
            targetDecimals: 6,
            sourceDecimals: 18,
          }),
        },
      ]);

      let allowance = await roles.accruedAllowance(allowanceKey);
      expect(allowance.balance).to.equal(valueInAccrueDecimals);

      await expect(invoke(valueInParamDecimals)).to.not.be.revert(ethers);

      allowance = await roles.accruedAllowance(allowanceKey);
      expect(allowance.balance).to.equal(0);
    });

    it("preserves decimal precision when scaling up (6 → 18)", async () => {
      const { owner, roles, allowFunction, invoke } =
        await loadFixture(setupOneParam);

      const MockPricing = await ethers.getContractFactory("MockPricing");
      const adapter = await MockPricing.deploy(10n ** 18n); // 1:1 price

      // 1.123456 in 6 decimals
      const valueInParamDecimals = 1123456n;
      // Expected: 1.123456000000000000 in 18 decimals
      const valueInAccrueDecimals = 1123456000000000000n;

      await setAllowance(await roles.connect(owner), allowanceKey, {
        balance: valueInAccrueDecimals,
        period: 0,
        refill: 0,
        timestamp: 0,
      });

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
            adapter: await adapter.getAddress(),
            targetDecimals: 18,
            sourceDecimals: 6,
          }),
        },
      ]);

      let allowance = await roles.accruedAllowance(allowanceKey);
      expect(allowance.balance).to.equal(valueInAccrueDecimals);

      await expect(invoke(valueInParamDecimals)).to.not.be.revert(ethers);

      allowance = await roles.accruedAllowance(allowanceKey);
      expect(allowance.balance).to.equal(0);
    });
  });

  describe("parameterized adapter", () => {
    const allowanceKey =
      "0x0000000000000000000000000000000000000000000000000000000000000001";

    it("adapter receives encoded params from compValue", async () => {
      const { owner, roles, allowFunction, invoke } =
        await loadFixture(setupOneParam);

      // Adapter that requires specific params, reverts otherwise
      const adapter = await (
        await ethers.getContractFactory("MockPricingParameterized")
      ).deploy();

      const params = "0xdeadbeef";
      await adapter.setPrice(params, 2n * 10n ** 18n); // 2x multiplier

      await setAllowance(await roles.connect(owner), allowanceKey, {
        balance: 2000n,
        period: 0,
        refill: 0,
        timestamp: 0,
      });

      // compValue: allowanceKey(32) + baseDecimals(1) + paramDecimals(1) + adapter(20) + params(4)
      const compValue = solidityPacked(
        ["bytes32", "uint8", "uint8", "address", "bytes"],
        [allowanceKey, 0, 0, await adapter.getAddress(), params],
      );

      // wrong params → adapter reverts, we check it is extracting and passing correctly
      const wrongCompValue = solidityPacked(
        ["bytes32", "uint8", "uint8", "address", "bytes"],
        [allowanceKey, 0, 0, await adapter.getAddress(), "0xcafebabe"],
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
      await expect(invoke(500))
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(ConditionViolationStatus.PricingAdapterReverted, 1, anyValue);

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
      await expect(invoke(500)).to.not.be.revert(ethers);

      const allowance = await roles.accruedAllowance(allowanceKey);
      expect(allowance.balance).to.equal(1000n); // 2000 - 1000

      // value=600 → consumed=1200, total=2200 > 2000 → fail
      await expect(invoke(600))
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(ConditionViolationStatus.AllowanceExceeded, 1, anyValue);
    });

    it("adapter receives empty params when compValue has no trailing bytes", async () => {
      const { owner, roles, allowFunction, invoke } =
        await loadFixture(setupOneParam);

      // Adapter that requires empty params, reverts if non-empty
      const adapter = await (
        await ethers.getContractFactory("MockPricingEmptyParams")
      ).deploy(10n ** 18n); // 1:1 price

      await setAllowance(await roles.connect(owner), allowanceKey, {
        balance: 1000n,
        period: 0,
        refill: 0,
        timestamp: 0,
      });

      // counterfactual: non-empty params → adapter reverts
      const wrongCompValue = solidityPacked(
        ["bytes32", "uint8", "uint8", "address", "bytes"],
        [allowanceKey, 0, 0, await adapter.getAddress(), "0xdeadbeef"],
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
      await expect(invoke(500))
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(ConditionViolationStatus.PricingAdapterReverted, 1, anyValue);

      // correct: exactly 54 bytes (no trailing params)
      const compValue = solidityPacked(
        ["bytes32", "uint8", "uint8", "address"],
        [allowanceKey, 0, 0, await adapter.getAddress()],
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
      await expect(invoke(500)).to.not.be.revert(ethers);
      const allowance = await roles.accruedAllowance(allowanceKey);
      expect(allowance.balance).to.equal(500n);
    });
  });

  describe("adapter call safety", () => {
    function encodeAllowanceCompValue({
      allowanceKey,
      targetDecimals = 0,
      sourceDecimals = 0,
      adapter = "0x0000000000000000000000000000000000000000",
    }: {
      allowanceKey: string;
      targetDecimals?: number;
      sourceDecimals?: number;
      adapter?: string;
    }): string {
      return solidityPacked(
        ["bytes32", "uint8", "uint8", "address"],
        [allowanceKey, targetDecimals, sourceDecimals, adapter],
      );
    }

    const allowanceKey = hexlify(randomBytes(32));

    it("reverts with PricingAdapterNotAContract when adapter not deployed", async () => {
      const { owner, roles, allowFunction, invoke } =
        await loadFixture(setupOneParam);

      const [, , randomEOA] = await ethers.getSigners();

      await setAllowance(await roles.connect(owner), allowanceKey, {
        balance: 1000,
        period: 0,
        refill: 0,
        timestamp: 0,
      });

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
            adapter: randomEOA.address,
            targetDecimals: 18,
            sourceDecimals: 6,
          }),
        },
      ]);

      await expect(invoke(1000))
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(
          ConditionViolationStatus.PricingAdapterNotAContract,
          1, // WithinAllowance node
          anyValue,
        );
    });

    it("reverts with PricingAdapterReverted when adapter has no getPrice function", async () => {
      const { owner, roles, allowFunction, invoke } =
        await loadFixture(setupOneParam);

      const MockPricingNoInterface = await ethers.getContractFactory(
        "MockPricingNoInterface",
      );
      const noInterfaceAdapter = await MockPricingNoInterface.deploy();

      await setAllowance(await roles.connect(owner), allowanceKey, {
        balance: 1000,
        period: 0,
        refill: 0,
        timestamp: 0,
      });

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
            adapter: await noInterfaceAdapter.getAddress(),
            targetDecimals: 18,
            sourceDecimals: 6,
          }),
        },
      ]);

      await expect(invoke(1000))
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(
          ConditionViolationStatus.PricingAdapterReverted,
          1, // WithinAllowance node
          anyValue,
        );
    });

    it("reverts with PricingAdapterReverted when adapter reverts", async () => {
      const { owner, roles, allowFunction, invoke } =
        await loadFixture(setupOneParam);

      const MockPricingReverting = await ethers.getContractFactory(
        "MockPricingReverting",
      );
      const revertingAdapter = await MockPricingReverting.deploy();

      await setAllowance(await roles.connect(owner), allowanceKey, {
        balance: 1000,
        period: 0,
        refill: 0,
        timestamp: 0,
      });

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
            adapter: await revertingAdapter.getAddress(),
            targetDecimals: 18,
            sourceDecimals: 6,
          }),
        },
      ]);

      await expect(invoke(1000))
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(
          ConditionViolationStatus.PricingAdapterReverted,
          1, // WithinAllowance node
          anyValue,
        );
    });

    it("reverts with PricingAdapterInvalidResult when adapter returns wrong type", async () => {
      const { owner, roles, allowFunction, invoke } =
        await loadFixture(setupOneParam);

      const MockPricingWrongReturn = await ethers.getContractFactory(
        "MockPricingWrongReturn",
      );
      const wrongReturnAdapter = await MockPricingWrongReturn.deploy();

      await setAllowance(await roles.connect(owner), allowanceKey, {
        balance: 1000,
        period: 0,
        refill: 0,
        timestamp: 0,
      });

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
            adapter: await wrongReturnAdapter.getAddress(),
            targetDecimals: 18,
            sourceDecimals: 6,
          }),
        },
      ]);

      await expect(invoke(1000))
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(
          ConditionViolationStatus.PricingAdapterInvalidResult,
          1, // WithinAllowance node
          anyValue,
        );
    });

    it("reverts with PricingAdapterZeroPrice when adapter returns zero", async () => {
      const { owner, roles, allowFunction, invoke } =
        await loadFixture(setupOneParam);

      const MockPricing = await ethers.getContractFactory("MockPricing");
      const zeroAdapter = await MockPricing.deploy(0);

      await setAllowance(await roles.connect(owner), allowanceKey, {
        balance: 1000,
        period: 0,
        refill: 0,
        timestamp: 0,
      });

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
            adapter: await zeroAdapter.getAddress(),
            targetDecimals: 18,
            sourceDecimals: 6,
          }),
        },
      ]);

      await expect(invoke(1000))
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(
          ConditionViolationStatus.PricingAdapterZeroPrice,
          1, // WithinAllowance node
          anyValue,
        );
    });
  });

  describe("WithinAllowance - from EtherValue", () => {
    it("enforces ether allowance from transaction.value", async () => {
      const { roleKey, owner, member, roles, testContract } =
        await loadFixture(setupTestContract);

      // Fund the avatar
      const avatarAddress = await roles.avatar();
      await owner.sendTransaction({
        to: avatarAddress,
        value: parseEther("1"),
      });

      const allowanceKey =
        "0x0000000000000000000000000000000000000000000000000000000000000001";

      await setAllowance(await roles.connect(owner), allowanceKey, {
        balance: 10000,
        period: 0,
        refill: 0,
        timestamp: 0,
      });

      const iface = new Interface(["function oneParamStatic(uint256)"]);
      const selector = iface.getFunction("oneParamStatic")!.selector;

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
          compValue: defaultAbiCoder.encode(["bytes32"], [allowanceKey]),
        },
        {
          parent: 1,
          paramType: Encoding.Static,
          operator: Operator.Pass,
          compValue: "0x",
        },
      ]);
      await roles.allowFunctionPacked(
        roleKey,
        await testContract.getAddress(),
        selector,
        packed,
        ExecutionOptions.Send,
      );

      async function invoke(value: bigint, param: bigint) {
        return roles
          .connect(member)
          .execTransactionFromModule(
            await testContract.getAddress(),
            value,
            iface.encodeFunctionData("oneParamStatic", [param]),
            0,
          );
      }

      // Exceeds allowance
      await expect(invoke(10001n, 123n))
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(
          ConditionViolationStatus.AllowanceExceeded,
          2, // WithinAllowance node: And[0] -> Matches[1], WithinAllowance[2]
          anyValue,
        );

      // Within allowance
      await expect(invoke(5000n, 456n)).to.not.be.revert(ethers);
      expect((await roles.accruedAllowance(allowanceKey)).balance).to.equal(
        5000,
      );

      // Exhaust remaining
      await expect(invoke(5000n, 789n)).to.not.be.revert(ethers);
      expect((await roles.accruedAllowance(allowanceKey)).balance).to.equal(0);

      // Now fails
      await expect(invoke(1n, 999n))
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(
          ConditionViolationStatus.AllowanceExceeded,
          2, // WithinAllowance node: And[0] -> Matches[1], WithinAllowance[2]
          anyValue,
        );
    });
  });

  describe("violation context", () => {
    it("reports the violating node index", async () => {
      const { owner, roles, allowFunction, invoke } =
        await loadFixture(setupOneParam);

      const allowanceKey = hexlify(randomBytes(32));

      await setAllowance(await roles.connect(owner), allowanceKey, {
        balance: 100,
        period: 0,
        refill: 0,
        timestamp: 0,
      });

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
          compValue: defaultAbiCoder.encode(["bytes32"], [allowanceKey]),
        },
      ]);

      await expect(invoke(101))
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(
          ConditionViolationStatus.AllowanceExceeded,
          1, // WithinAllowance node at BFS index 1
          anyValue,
        );
    });

    it("reports the calldata range of the violation", async () => {
      const { owner, roles, allowFunction, invoke } =
        await loadFixture(setupOneParam);

      const allowanceKey = hexlify(randomBytes(32));

      await setAllowance(await roles.connect(owner), allowanceKey, {
        balance: 100,
        period: 0,
        refill: 0,
        timestamp: 0,
      });

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
          compValue: defaultAbiCoder.encode(["bytes32"], [allowanceKey]),
        },
      ]);

      await expect(invoke(101))
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(
          ConditionViolationStatus.AllowanceExceeded,
          anyValue,
          4, // payloadLocation: parameter starts at byte 4
        );
    });
  });

  describe("integrity", () => {
    describe("encoding", () => {
      it("reverts UnsuitableParameterType for invalid encodings", async () => {
        const { roles } = await loadFixture(setupTestContract);

        const allowanceKey = hexlify(randomBytes(32));

        for (const encoding of [
          Encoding.None,
          Encoding.AbiEncoded,
          Encoding.Array,
          Encoding.Dynamic,
          Encoding.Tuple,
        ]) {
          await expect(
            packConditions(roles, [
              {
                parent: 0,
                paramType: encoding,
                operator: Operator.WithinAllowance,
                compValue: allowanceKey,
              },
            ]),
          ).to.be.revertedWithCustomError(roles, "UnsuitableParameterType");
        }
      });

      it("accepts Static and EtherValue encodings", async () => {
        const { roles } = await loadFixture(setupTestContract);

        const allowanceKey = hexlify(randomBytes(32));

        // Should succeed without reverting: on a parameter of a call
        await roles.packConditions([
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
            compValue: allowanceKey,
          },
        ]);
        // and on the ether value, which reads no calldata and may be the root
        await roles.packConditions([
          {
            parent: 0,
            paramType: Encoding.EtherValue,
            operator: Operator.WithinAllowance,
            compValue: allowanceKey,
          },
        ]);
      });
    });

    describe("compValue", () => {
      it("reverts UnsuitableCompValue when compValue is not 32, 34, or 54 bytes", async () => {
        const { roles } = await loadFixture(setupTestContract);

        await expect(
          packConditions(roles, [
            {
              parent: 0,
              paramType: Encoding.Static,
              operator: Operator.WithinAllowance,
              compValue: "0x" + "ab".repeat(31), // 31 bytes
            },
          ]),
        ).to.be.revertedWithCustomError(roles, "UnsuitableCompValue");
      });

      it("accepts compValue longer than 54 bytes (with adapter params)", async () => {
        const { roles } = await loadFixture(setupTestContract);

        const allowanceKey = hexlify(randomBytes(32));
        // 54 bytes + 4 bytes trailing params
        const compValue = solidityPacked(
          ["bytes32", "uint8", "uint8", "address", "bytes"],
          [
            allowanceKey,
            18,
            6,
            "0x0000000000000000000000000000000000000001",
            "0xdeadbeef",
          ],
        );

        // Should succeed without reverting
        await roles.packConditions([
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
      });

      it("reverts UnsuitableCompValue when compValue is 33 bytes", async () => {
        const { roles } = await loadFixture(setupTestContract);

        await expect(
          packConditions(roles, [
            {
              parent: 0,
              paramType: Encoding.Static,
              operator: Operator.WithinAllowance,
              compValue: "0x" + "ab".repeat(33), // 33 bytes
            },
          ]),
        ).to.be.revertedWithCustomError(roles, "UnsuitableCompValue");
      });

      it("reverts AllowanceDecimalsExceedMax when targetDecimals > 27", async () => {
        const { roles } = await loadFixture(setupTestContract);

        const allowanceKey = hexlify(randomBytes(32));
        // 34-byte compValue: allowanceKey(32) + targetDecimals(1) + sourceDecimals(1)
        const compValue = solidityPacked(
          ["bytes32", "uint8", "uint8"],
          [allowanceKey, 28, 18], // targetDecimals = 28 (> 27)
        );

        await expect(
          packConditions(roles, [
            {
              parent: 0,
              paramType: Encoding.Static,
              operator: Operator.WithinAllowance,
              compValue,
            },
          ]),
        ).to.be.revertedWithCustomError(roles, "AllowanceDecimalsExceedMax");
      });

      it("reverts AllowanceDecimalsExceedMax when sourceDecimals > 27", async () => {
        const { roles } = await loadFixture(setupTestContract);

        const allowanceKey = hexlify(randomBytes(32));
        // 34-byte compValue: allowanceKey(32) + targetDecimals(1) + sourceDecimals(1)
        const compValue = solidityPacked(
          ["bytes32", "uint8", "uint8"],
          [allowanceKey, 18, 28], // sourceDecimals = 28 (> 27)
        );

        await expect(
          packConditions(roles, [
            {
              parent: 0,
              paramType: Encoding.Static,
              operator: Operator.WithinAllowance,
              compValue,
            },
          ]),
        ).to.be.revertedWithCustomError(roles, "AllowanceDecimalsExceedMax");
      });

      it("accepts decimals at boundary (27)", async () => {
        const { roles } = await loadFixture(setupTestContract);

        const allowanceKey = hexlify(randomBytes(32));
        // 34-byte compValue with decimals at max allowed value
        const compValue = solidityPacked(
          ["bytes32", "uint8", "uint8"],
          [allowanceKey, 27, 27], // both at max allowed
        );

        // Should succeed without reverting
        await roles.packConditions([
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
      });
    });

    it("reverts LeafNodeCannotHaveChildren when WithinAllowance has children", async () => {
      const { roles } = await loadFixture(setupTestContract);

      const allowanceKey = hexlify(randomBytes(32));

      await expect(
        packConditions(roles, [
          {
            parent: 0,
            paramType: Encoding.Static,
            operator: Operator.WithinAllowance,
            compValue: allowanceKey,
          },
          {
            parent: 0,
            paramType: Encoding.Static,
            operator: Operator.Pass,
            compValue: "0x",
          },
        ]),
      ).to.be.revertedWithCustomError(roles, "LeafNodeCannotHaveChildren");
    });
  });
});
