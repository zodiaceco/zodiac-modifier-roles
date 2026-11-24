import assert from "node:assert/strict";
import { after, describe, it } from "node:test";
import { network } from "hardhat";
import {
  encodeFunctionData,
  isAddressEqual,
  keccak256,
  parseAbi,
  parseEventLogs,
  toBytes,
  toFunctionSelector,
} from "viem";
import type { Address, Hex } from "viem";

import {
  Encoding,
  ExecutionOptions,
  Operator,
  encodeMultisendPayload,
  packConditions,
  maxUint64,
  maxUint128,
  assertNotEmitted,
} from "./utils.js";
import { createSetup } from "./setup.js";

const connection = await network.create();
const { viem, networkHelpers } = connection;
const { loadFixture, time } = networkHelpers;
const { deployRolesMod, deployMultiSend } = createSetup(connection);

const abi = parseAbi([
  "function oneParamStatic(uint256)",
  "function twoParamsStatic(uint256, uint256)",
  "function fnThatMaybeReverts(uint256, bool)",
]);

const selectors = {
  oneParamStatic: toFunctionSelector("oneParamStatic(uint256)"),
  twoParamsStatic: toFunctionSelector("twoParamsStatic(uint256, uint256)"),
  fnThatMaybeReverts: toFunctionSelector("fnThatMaybeReverts(uint256, bool)"),
} as const;

type FnName = keyof typeof selectors;

/**
 * AllowanceTracking tests
 *
 * Scope: Allowance Accounting.
 *
 * This file verifies:
 * - Accrual (`_accrue`): how refills accumulate over elapsed periods, read
 *   through `accruedAllowance`.
 * - Settlement (`_consume`): what an execution writes back to storage, read
 *   raw through `allowances` (balance and accrual point written, refill
 *   configuration untouched), and the `ConsumeAllowance` events.
 *
 * Configuring allowances (`setAllowance`, `updateAllowance`) is tested in
 * `setup.spec.ts`; threading consumption through the Evaluator, in
 * `authorization.spec.ts` and `operators/`.
 */
describe("AllowanceTracking", () => {
  after(async () => {
    await connection.close();
  });

  async function setup() {
    const [owner, member] = await viem.getWalletClients();

    const avatar = await viem.deployContract("TestAvatar");
    const avatarAddress = avatar.address;

    const roles = await deployRolesMod(
      owner.account.address,
      avatarAddress,
      avatarAddress,
    );

    const testContract = await viem.deployContract("TestContract");
    const testContractAddress = testContract.address;

    const ROLE_KEY = keccak256(toBytes("TEST_ROLE"));
    const ALLOWANCE_KEY = keccak256(toBytes("TEST_ALLOWANCE"));

    await roles.write.grantRole([member.account.address, ROLE_KEY, 0n, 0n, 0n]);
    await roles.write.setDefaultRole([member.account.address, ROLE_KEY]);
    await roles.write.scopeTarget([ROLE_KEY, testContractAddress]);

    /** Lets the role call `fn` on the test contract with each parameter
     *  within the allowance at the same position (`null`: unconstrained). */
    const allowWithin = async (fn: FnName, keys: (Hex | null)[]) =>
      roles.write.allowFunctionPacked([
        ROLE_KEY,
        testContractAddress,
        selectors[fn],
        await packConditions(roles, [
          {
            parent: 0,
            paramType: Encoding.AbiEncoded,
            operator: Operator.Matches,
            compValue: "0x",
          },
          ...keys.map((key) => ({
            parent: 0,
            paramType: Encoding.Static,
            operator: key ? Operator.WithinAllowance : Operator.Pass,
            compValue: key ?? ("0x" as Hex),
          })),
        ]),
        ExecutionOptions.None,
      ]);

    /** The member calls the test contract. */
    const exec = (fn: FnName, args: readonly (bigint | boolean)[]) =>
      roles.write.execTransactionFromModule(
        [
          testContractAddress,
          0n,
          encodeFunctionData({ abi, functionName: fn, args: args as never }),
          0,
        ],
        { account: member.account },
      );

    /** The allowance as stored, not as accrued on read. */
    const stored = async (key: Hex) => {
      const [refill, maxRefill, period, balance, timestamp] =
        await roles.read.allowances([key]);
      return { refill, maxRefill, period, balance, timestamp };
    };

    return {
      roles,
      owner,
      member,
      avatarAddress,
      testContractAddress,
      ROLE_KEY,
      ALLOWANCE_KEY,
      allowWithin,
      exec,
      stored,
    };
  }

  /** `setup`, plus MultiSend and its unwrapper. */
  async function setupBatch() {
    const base = await setup();

    const { multisend } = await deployMultiSend(base.roles);
    const multisendAddress = multisend.address;

    /** The member delegatecalls MultiSend with `txs`. */
    const execBatch = (txs: { to: Address; data: Hex }[]) =>
      base.roles.write.execTransactionFromModule(
        [
          multisendAddress,
          0n,
          encodeFunctionData({
            abi: multisend.abi,
            functionName: "multiSend",
            args: [
              encodeMultisendPayload(
                txs.map((tx) => ({ ...tx, value: 0n, operation: 0 })),
              ),
            ],
          }),
          1,
        ],
        { account: base.member.account },
      );

    return { ...base, execBatch };
  }

  describe("Accrual", () => {
    it("never refills when period is 0", async () => {
      const { roles, ALLOWANCE_KEY, stored } = await loadFixture(setup);

      await roles.write.setAllowance([
        ALLOWANCE_KEY,
        500n,
        10000n,
        100n,
        0n,
        0n,
      ]);
      const { timestamp } = await stored(ALLOWANCE_KEY);
      await time.increase(9000);

      assert.deepEqual(await roles.read.accruedAllowance([ALLOWANCE_KEY]), [
        500n,
        timestamp,
      ]);
    });

    it("does not accrue before one full period, at period - 1", async () => {
      const { roles, ALLOWANCE_KEY, stored } = await loadFixture(setup);

      await roles.write.setAllowance([
        ALLOWANCE_KEY,
        500n,
        10000n,
        100n,
        600n,
        0n,
      ]);
      const { timestamp } = await stored(ALLOWANCE_KEY);
      await time.increaseTo(timestamp + 599n);

      assert.deepEqual(await roles.read.accruedAllowance([ALLOWANCE_KEY]), [
        500n,
        timestamp,
      ]);
    });

    it("accrues one refill after exactly one period", async () => {
      const { roles, ALLOWANCE_KEY, stored } = await loadFixture(setup);

      await roles.write.setAllowance([
        ALLOWANCE_KEY,
        500n,
        10000n,
        100n,
        600n,
        0n,
      ]);
      const { timestamp } = await stored(ALLOWANCE_KEY);
      await time.increaseTo(timestamp + 600n);

      assert.deepEqual(await roles.read.accruedAllowance([ALLOWANCE_KEY]), [
        600n,
        timestamp + 600n,
      ]);
    });

    it("accrues one refill per full period, advancing by full periods only", async () => {
      const { roles, ALLOWANCE_KEY, stored } = await loadFixture(setup);

      await roles.write.setAllowance([
        ALLOWANCE_KEY,
        500n,
        10000n,
        100n,
        600n,
        0n,
      ]);
      const { timestamp } = await stored(ALLOWANCE_KEY);
      // 3.5 periods
      await time.increaseTo(timestamp + 2100n);

      assert.deepEqual(await roles.read.accruedAllowance([ALLOWANCE_KEY]), [
        800n,
        timestamp + 1800n,
      ]);
    });

    it("advances the timestamp with zero refill", async () => {
      const { roles, ALLOWANCE_KEY, stored } = await loadFixture(setup);

      await roles.write.setAllowance([
        ALLOWANCE_KEY,
        500n,
        10000n,
        0n,
        600n,
        0n,
      ]);
      const { timestamp } = await stored(ALLOWANCE_KEY);
      await time.increaseTo(timestamp + 3000n);

      assert.deepEqual(await roles.read.accruedAllowance([ALLOWANCE_KEY]), [
        500n,
        timestamp + 3000n,
      ]);
    });

    it("does not accrue at the configured timestamp", async () => {
      const { roles, ALLOWANCE_KEY } = await loadFixture(setup);

      const timestamp = BigInt(await time.latest()) + 100n;
      await roles.write.setAllowance([
        ALLOWANCE_KEY,
        500n,
        10000n,
        100n,
        1n,
        timestamp,
      ]);
      await time.increaseTo(timestamp);

      assert.deepEqual(await roles.read.accruedAllowance([ALLOWANCE_KEY]), [
        500n,
        timestamp,
      ]);
    });

    it("accrues from a future timestamp only once it has passed", async () => {
      const { roles, ALLOWANCE_KEY } = await loadFixture(setup);

      const timestamp = BigInt(await time.latest()) + 10000n;
      await roles.write.setAllowance([
        ALLOWANCE_KEY,
        500n,
        10000n,
        100n,
        600n,
        timestamp,
      ]);

      // many periods after setting, but before the timestamp
      await time.increaseTo(timestamp - 1n);
      assert.deepEqual(await roles.read.accruedAllowance([ALLOWANCE_KEY]), [
        500n,
        timestamp,
      ]);

      await time.increaseTo(timestamp + 600n);
      assert.deepEqual(await roles.read.accruedAllowance([ALLOWANCE_KEY]), [
        600n,
        timestamp + 600n,
      ]);
    });

    it("does not overflow when the timestamp is uint64 max", async () => {
      const { roles, ALLOWANCE_KEY } = await loadFixture(setup);

      await roles.write.setAllowance([
        ALLOWANCE_KEY,
        500n,
        1000n,
        100n,
        600n,
        maxUint64,
      ]);

      assert.deepEqual(await roles.read.accruedAllowance([ALLOWANCE_KEY]), [
        500n,
        maxUint64,
      ]);
    });

    describe("maxRefill cap", () => {
      it("caps the balance at maxRefill after many periods", async () => {
        const { roles, ALLOWANCE_KEY, stored } = await loadFixture(setup);

        await roles.write.setAllowance([
          ALLOWANCE_KEY,
          500n,
          1000n,
          100n,
          600n,
          0n,
        ]);
        const { timestamp } = await stored(ALLOWANCE_KEY);
        // uncapped: 1500
        await time.increaseTo(timestamp + 6000n);

        assert.deepEqual(await roles.read.accruedAllowance([ALLOWANCE_KEY]), [
          1000n,
          timestamp + 6000n,
        ]);
      });

      it("reaches maxRefill exactly", async () => {
        const { roles, ALLOWANCE_KEY, stored } = await loadFixture(setup);

        await roles.write.setAllowance([
          ALLOWANCE_KEY,
          800n,
          1000n,
          100n,
          600n,
          0n,
        ]);
        const { timestamp } = await stored(ALLOWANCE_KEY);

        await time.increaseTo(timestamp + 600n);
        assert.equal(
          (await roles.read.accruedAllowance([ALLOWANCE_KEY]))[0],
          900n,
        );
        await time.increaseTo(timestamp + 1200n);
        assert.equal(
          (await roles.read.accruedAllowance([ALLOWANCE_KEY]))[0],
          1000n,
        );
      });

      it("discards the part of a refill above maxRefill", async () => {
        const { roles, ALLOWANCE_KEY, stored } = await loadFixture(setup);

        await roles.write.setAllowance([
          ALLOWANCE_KEY,
          900n,
          1000n,
          100n,
          600n,
          0n,
        ]);
        const { timestamp } = await stored(ALLOWANCE_KEY);
        // uncapped: 1100
        await time.increaseTo(timestamp + 1200n);

        assert.equal(
          (await roles.read.accruedAllowance([ALLOWANCE_KEY]))[0],
          1000n,
        );
      });

      it("caps without overflowing when refills exceed uint128", async () => {
        const { roles, ALLOWANCE_KEY, stored } = await loadFixture(setup);

        await roles.write.setAllowance([
          ALLOWANCE_KEY,
          0n,
          maxUint128,
          maxUint128,
          600n,
          0n,
        ]);
        const { timestamp } = await stored(ALLOWANCE_KEY);
        await time.increaseTo(timestamp + 1200n);

        assert.equal(
          (await roles.read.accruedAllowance([ALLOWANCE_KEY]))[0],
          maxUint128,
        );
      });

      it("advances the timestamp with the balance at the cap", async () => {
        const { roles, ALLOWANCE_KEY, stored } = await loadFixture(setup);

        await roles.write.setAllowance([
          ALLOWANCE_KEY,
          1000n,
          1000n,
          100n,
          600n,
          0n,
        ]);
        const { timestamp } = await stored(ALLOWANCE_KEY);
        await time.increaseTo(timestamp + 3000n);

        assert.deepEqual(await roles.read.accruedAllowance([ALLOWANCE_KEY]), [
          1000n,
          timestamp + 3000n,
        ]);
      });

      it("keeps a balance set above maxRefill, advancing the timestamp", async () => {
        const { roles, ALLOWANCE_KEY, stored } = await loadFixture(setup);

        await roles.write.setAllowance([
          ALLOWANCE_KEY,
          1500n,
          1000n,
          100n,
          600n,
          0n,
        ]);
        const { timestamp } = await stored(ALLOWANCE_KEY);
        await time.increaseTo(timestamp + 3000n);

        assert.deepEqual(await roles.read.accruedAllowance([ALLOWANCE_KEY]), [
          1500n,
          timestamp + 3000n,
        ]);
      });
    });
  });

  describe("Settlement", () => {
    it("stores the accrued balance minus consumption and the last full period, keeping the configuration", async () => {
      const { roles, ALLOWANCE_KEY, allowWithin, exec, stored } =
        await loadFixture(setup);

      await roles.write.setAllowance([
        ALLOWANCE_KEY,
        500n,
        5000n,
        100n,
        600n,
        0n,
      ]);
      const { timestamp } = await stored(ALLOWANCE_KEY);
      await allowWithin("oneParamStatic", [ALLOWANCE_KEY]);

      // 3.5 periods: accrues 800, consumes 150
      await time.setNextBlockTimestamp(timestamp + 2100n);
      await viem.assertions.emitWithArgs(
        exec("oneParamStatic", [150n]),
        roles,
        "ConsumeAllowance",
        [ALLOWANCE_KEY, 150n, 650n],
      );

      assert.deepEqual(await stored(ALLOWANCE_KEY), {
        refill: 100n,
        maxRefill: 5000n,
        period: 600n,
        balance: 650n,
        // the half period still counts towards the next refill
        timestamp: timestamp + 1800n,
      });
      await time.increaseTo(timestamp + 2400n);
      assert.deepEqual(await roles.read.accruedAllowance([ALLOWANCE_KEY]), [
        750n,
        timestamp + 2400n,
      ]);
    });

    it("with period 0, only deducts, leaving the timestamp", async () => {
      const { roles, ALLOWANCE_KEY, allowWithin, exec, stored } =
        await loadFixture(setup);

      await roles.write.setAllowance([ALLOWANCE_KEY, 1000n, 0n, 0n, 0n, 0n]);
      const before = await stored(ALLOWANCE_KEY);
      await allowWithin("oneParamStatic", [ALLOWANCE_KEY]);

      await exec("oneParamStatic", [100n]);
      await time.increase(10000);
      await exec("oneParamStatic", [100n]);

      assert.deepEqual(await stored(ALLOWANCE_KEY), {
        ...before,
        balance: 800n,
      });
    });

    it("consumes from a balance set above maxRefill, uncapped, storing the elapsed period", async () => {
      const { roles, ALLOWANCE_KEY, allowWithin, exec, stored } =
        await loadFixture(setup);

      await roles.write.setAllowance([
        ALLOWANCE_KEY,
        1300n,
        1000n,
        100n,
        3600n,
        0n,
      ]);
      const before = await stored(ALLOWANCE_KEY);
      await allowWithin("oneParamStatic", [ALLOWANCE_KEY]);

      // one period later: 1300 is not capped down to 1000 before deducting
      await time.setNextBlockTimestamp(before.timestamp + 3600n);
      await viem.assertions.emitWithArgs(
        exec("oneParamStatic", [1200n]),
        roles,
        "ConsumeAllowance",
        [ALLOWANCE_KEY, 1200n, 100n],
      );
      assert.deepEqual(await stored(ALLOWANCE_KEY), {
        ...before,
        balance: 100n,
        timestamp: before.timestamp + 3600n,
      });
    });

    it("settles each allowance once, with the batch's total consumption of it", async () => {
      const {
        roles,
        testContractAddress,
        ALLOWANCE_KEY,
        allowWithin,
        execBatch,
        stored,
      } = await loadFixture(setupBatch);
      const OTHER_KEY = keccak256(toBytes("OTHER_ALLOWANCE"));

      await roles.write.setAllowance([ALLOWANCE_KEY, 1000n, 0n, 0n, 0n, 0n]);
      await roles.write.setAllowance([OTHER_KEY, 500n, 0n, 0n, 0n, 0n]);
      await allowWithin("oneParamStatic", [ALLOWANCE_KEY]);
      await allowWithin("twoParamsStatic", [ALLOWANCE_KEY, OTHER_KEY]);

      const hash = await execBatch([
        {
          to: testContractAddress,
          data: encodeFunctionData({
            abi,
            functionName: "oneParamStatic",
            args: [30n],
          }),
        },
        {
          to: testContractAddress,
          data: encodeFunctionData({
            abi,
            functionName: "twoParamsStatic",
            args: [50n, 20n],
          }),
        },
      ]);
      const publicClient = await viem.getPublicClient();
      const receipt = await publicClient.waitForTransactionReceipt({ hash });

      const consumed = parseEventLogs({
        abi: roles.abi,
        eventName: "ConsumeAllowance",
        logs: receipt.logs.filter((l) =>
          isAddressEqual(l.address, roles.address),
        ),
      }).map((l) => [l.args.allowanceKey, l.args.consumed, l.args.newBalance]);
      assert.deepEqual(consumed, [
        [ALLOWANCE_KEY, 80n, 920n],
        [OTHER_KEY, 20n, 480n],
      ]);
      assert.equal((await stored(ALLOWANCE_KEY)).balance, 920n);
      assert.equal((await stored(OTHER_KEY)).balance, 480n);
    });

    it("does not emit ConsumeAllowance without a WithinAllowance condition", async () => {
      const { roles, ROLE_KEY, testContractAddress, exec } =
        await loadFixture(setup);

      await roles.write.allowTargetPacked([
        ROLE_KEY,
        testContractAddress,
        "0x",
        ExecutionOptions.None,
      ]);

      await assertNotEmitted(
        viem,
        exec("oneParamStatic", [100n]),
        roles,
        "ConsumeAllowance",
      );
    });

    it("writes nothing when the executed call fails, after elapsed periods", async () => {
      const { roles, ALLOWANCE_KEY, allowWithin, exec, stored } =
        await loadFixture(setup);

      await roles.write.setAllowance([
        ALLOWANCE_KEY,
        500n,
        5000n,
        100n,
        600n,
        0n,
      ]);
      const before = await stored(ALLOWANCE_KEY);
      await allowWithin("fnThatMaybeReverts", [ALLOWANCE_KEY, null]);

      await time.setNextBlockTimestamp(before.timestamp + 2100n);
      await assertNotEmitted(
        viem,
        exec("fnThatMaybeReverts", [100n, true]),
        roles,
        "ConsumeAllowance",
      );

      // neither the consumption nor the accrual is written
      assert.deepEqual(await stored(ALLOWANCE_KEY), before);
    });

    describe("against storage as the executed call left it", () => {
      /** A batch that consumes 100 of the allowance, then has the avatar
       *  (made the owner) call Roles with `data`; mined at `timestamp`. */
      async function consumeThenCall(
        fixture: Awaited<ReturnType<typeof setupBatch>>,
        data: Hex,
        timestamp?: bigint,
      ) {
        const {
          roles,
          owner,
          avatarAddress,
          testContractAddress,
          ROLE_KEY,
          allowWithin,
          execBatch,
        } = fixture;
        await allowWithin("oneParamStatic", [fixture.ALLOWANCE_KEY]);
        await roles.write.allowTargetPacked([
          ROLE_KEY,
          roles.address,
          "0x",
          ExecutionOptions.None,
        ]);
        await roles.write.transferOwnership([avatarAddress], {
          account: owner.account,
        });

        if (timestamp !== undefined)
          await time.setNextBlockTimestamp(timestamp);
        return execBatch([
          {
            to: testContractAddress,
            data: encodeFunctionData({
              abi,
              functionName: "oneParamStatic",
              args: [100n],
            }),
          },
          { to: roles.address, data },
        ]);
      }

      it("deducts from a balance the call raised", async () => {
        const fixture = await loadFixture(setupBatch);
        const { roles, ALLOWANCE_KEY, stored } = fixture;
        await roles.write.setAllowance([ALLOWANCE_KEY, 1000n, 0n, 0n, 0n, 0n]);

        await viem.assertions.emitWithArgs(
          consumeThenCall(
            fixture,
            encodeFunctionData({
              abi: roles.abi,
              functionName: "setAllowance",
              args: [ALLOWANCE_KEY, 5000n, 0n, 0n, 0n, 0n],
            }),
          ),
          roles,
          "ConsumeAllowance",
          [ALLOWANCE_KEY, 100n, 4900n],
        );
        assert.equal((await stored(ALLOWANCE_KEY)).balance, 4900n);
      });

      it("reverts AllowanceExceeded when the call lowered the balance below the consumption", async () => {
        const fixture = await loadFixture(setupBatch);
        const { roles, ALLOWANCE_KEY } = fixture;
        await roles.write.setAllowance([ALLOWANCE_KEY, 1000n, 0n, 0n, 0n, 0n]);

        await viem.assertions.revertWithCustomErrorWithArgs(
          consumeThenCall(
            fixture,
            encodeFunctionData({
              abi: roles.abi,
              functionName: "setAllowance",
              args: [ALLOWANCE_KEY, 50n, 0n, 0n, 0n, 0n],
            }),
          ),
          roles,
          "AllowanceExceeded",
          [ALLOWANCE_KEY],
        );
      });

      it("reverts AllowanceExceeded when the call disabled the refill the consumption relied on", async () => {
        const fixture = await loadFixture(setupBatch);
        const { roles, ALLOWANCE_KEY, stored } = fixture;
        // nothing stored; one period accrues 100, which is consumed
        await roles.write.setAllowance([ALLOWANCE_KEY, 0n, 0n, 100n, 600n, 0n]);
        const { timestamp } = await stored(ALLOWANCE_KEY);

        await viem.assertions.revertWithCustomErrorWithArgs(
          consumeThenCall(
            fixture,
            encodeFunctionData({
              abi: roles.abi,
              functionName: "updateAllowance",
              args: [ALLOWANCE_KEY, 0n, 100n, 0n],
            }),
            timestamp + 600n,
          ),
          roles,
          "AllowanceExceeded",
          [ALLOWANCE_KEY],
        );
      });
    });
  });
});
