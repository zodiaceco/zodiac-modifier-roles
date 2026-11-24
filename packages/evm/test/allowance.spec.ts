import { expect } from "chai";
import { Interface } from "ethers";
import { network } from "hardhat";

import {
  Encoding,
  ExecutionOptions,
  Operator,
  encodeMultisendPayload,
  packConditions,
  maxUint64,
  maxUint128,
} from "./utils.js";
import { createSetup } from "./setup.js";

const connection = await network.create();
const { ethers, networkHelpers } = connection;
const { loadFixture, time } = networkHelpers;
const { deployRolesMod, deployMultiSend } = createSetup(connection);

const iface = new Interface([
  "function oneParamStatic(uint256)",
  "function twoParamsStatic(uint256, uint256)",
  "function fnThatMaybeReverts(uint256, bool)",
]);

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
    const [owner, member] = await ethers.getSigners();

    const Avatar = await ethers.getContractFactory("TestAvatar");
    const avatar = await Avatar.deploy();
    const avatarAddress = await avatar.getAddress();

    const roles = await deployRolesMod(
      owner.address,
      avatarAddress,
      avatarAddress,
    );

    const TestContract = await ethers.getContractFactory("TestContract");
    const testContract = await TestContract.deploy();
    const testContractAddress = await testContract.getAddress();

    const ROLE_KEY = ethers.id("TEST_ROLE");
    const ALLOWANCE_KEY = ethers.id("TEST_ALLOWANCE");

    await roles.grantRole(member.address, ROLE_KEY, 0, 0, 0);
    await roles.setDefaultRole(member.address, ROLE_KEY);
    await roles.scopeTarget(ROLE_KEY, testContractAddress);

    /** Lets the role call `fn` on the test contract with each parameter
     *  within the allowance at the same position (`null`: unconstrained). */
    const allowWithin = async (fn: string, keys: (string | null)[]) =>
      roles.allowFunctionPacked(
        ROLE_KEY,
        testContractAddress,
        iface.getFunction(fn)!.selector,
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
            compValue: key ?? "0x",
          })),
        ]),
        ExecutionOptions.None,
      );

    /** The member calls the test contract. */
    const exec = (fn: string, args: unknown[]) =>
      roles
        .connect(member)
        .execTransactionFromModule(
          testContractAddress,
          0,
          iface.encodeFunctionData(fn, args),
          0,
        );

    /** The allowance as stored, not as accrued on read. */
    const stored = async (key: string) => {
      const { refill, maxRefill, period, balance, timestamp } =
        await roles.allowances(key);
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
    const multisendAddress = await multisend.getAddress();

    /** The member delegatecalls MultiSend with `txs`. */
    const execBatch = (txs: { to: string; data: string }[]) =>
      base.roles
        .connect(base.member)
        .execTransactionFromModule(
          multisendAddress,
          0,
          multisend.interface.encodeFunctionData("multiSend", [
            encodeMultisendPayload(
              txs.map((tx) => ({ ...tx, value: 0, operation: 0 })),
            ),
          ]),
          1,
        );

    return { ...base, execBatch };
  }

  describe("Accrual", () => {
    it("never refills when period is 0", async () => {
      const { roles, ALLOWANCE_KEY, stored } = await loadFixture(setup);

      await roles.setAllowance(ALLOWANCE_KEY, 500, 10000, 100, 0, 0);
      const { timestamp } = await stored(ALLOWANCE_KEY);
      await time.increase(9000);

      expect(await roles.accruedAllowance(ALLOWANCE_KEY)).to.deep.equal([
        500n,
        timestamp,
      ]);
    });

    it("does not accrue before one full period, at period - 1", async () => {
      const { roles, ALLOWANCE_KEY, stored } = await loadFixture(setup);

      await roles.setAllowance(ALLOWANCE_KEY, 500, 10000, 100, 600, 0);
      const { timestamp } = await stored(ALLOWANCE_KEY);
      await time.increaseTo(timestamp + 599n);

      expect(await roles.accruedAllowance(ALLOWANCE_KEY)).to.deep.equal([
        500n,
        timestamp,
      ]);
    });

    it("accrues one refill after exactly one period", async () => {
      const { roles, ALLOWANCE_KEY, stored } = await loadFixture(setup);

      await roles.setAllowance(ALLOWANCE_KEY, 500, 10000, 100, 600, 0);
      const { timestamp } = await stored(ALLOWANCE_KEY);
      await time.increaseTo(timestamp + 600n);

      expect(await roles.accruedAllowance(ALLOWANCE_KEY)).to.deep.equal([
        600n,
        timestamp + 600n,
      ]);
    });

    it("accrues one refill per full period, advancing by full periods only", async () => {
      const { roles, ALLOWANCE_KEY, stored } = await loadFixture(setup);

      await roles.setAllowance(ALLOWANCE_KEY, 500, 10000, 100, 600, 0);
      const { timestamp } = await stored(ALLOWANCE_KEY);
      // 3.5 periods
      await time.increaseTo(timestamp + 2100n);

      expect(await roles.accruedAllowance(ALLOWANCE_KEY)).to.deep.equal([
        800n,
        timestamp + 1800n,
      ]);
    });

    it("advances the timestamp with zero refill", async () => {
      const { roles, ALLOWANCE_KEY, stored } = await loadFixture(setup);

      await roles.setAllowance(ALLOWANCE_KEY, 500, 10000, 0, 600, 0);
      const { timestamp } = await stored(ALLOWANCE_KEY);
      await time.increaseTo(timestamp + 3000n);

      expect(await roles.accruedAllowance(ALLOWANCE_KEY)).to.deep.equal([
        500n,
        timestamp + 3000n,
      ]);
    });

    it("does not accrue at the configured timestamp", async () => {
      const { roles, ALLOWANCE_KEY } = await loadFixture(setup);

      const timestamp = BigInt(await time.latest()) + 100n;
      await roles.setAllowance(ALLOWANCE_KEY, 500, 10000, 100, 1, timestamp);
      await time.increaseTo(timestamp);

      expect(await roles.accruedAllowance(ALLOWANCE_KEY)).to.deep.equal([
        500n,
        timestamp,
      ]);
    });

    it("accrues from a future timestamp only once it has passed", async () => {
      const { roles, ALLOWANCE_KEY } = await loadFixture(setup);

      const timestamp = BigInt(await time.latest()) + 10000n;
      await roles.setAllowance(ALLOWANCE_KEY, 500, 10000, 100, 600, timestamp);

      // many periods after setting, but before the timestamp
      await time.increaseTo(timestamp - 1n);
      expect(await roles.accruedAllowance(ALLOWANCE_KEY)).to.deep.equal([
        500n,
        timestamp,
      ]);

      await time.increaseTo(timestamp + 600n);
      expect(await roles.accruedAllowance(ALLOWANCE_KEY)).to.deep.equal([
        600n,
        timestamp + 600n,
      ]);
    });

    it("does not overflow when the timestamp is uint64 max", async () => {
      const { roles, ALLOWANCE_KEY } = await loadFixture(setup);

      await roles.setAllowance(ALLOWANCE_KEY, 500, 1000, 100, 600, maxUint64);

      expect(await roles.accruedAllowance(ALLOWANCE_KEY)).to.deep.equal([
        500n,
        maxUint64,
      ]);
    });

    describe("maxRefill cap", () => {
      it("caps the balance at maxRefill after many periods", async () => {
        const { roles, ALLOWANCE_KEY, stored } = await loadFixture(setup);

        await roles.setAllowance(ALLOWANCE_KEY, 500, 1000, 100, 600, 0);
        const { timestamp } = await stored(ALLOWANCE_KEY);
        // uncapped: 1500
        await time.increaseTo(timestamp + 6000n);

        expect(await roles.accruedAllowance(ALLOWANCE_KEY)).to.deep.equal([
          1000n,
          timestamp + 6000n,
        ]);
      });

      it("reaches maxRefill exactly", async () => {
        const { roles, ALLOWANCE_KEY, stored } = await loadFixture(setup);

        await roles.setAllowance(ALLOWANCE_KEY, 800, 1000, 100, 600, 0);
        const { timestamp } = await stored(ALLOWANCE_KEY);

        await time.increaseTo(timestamp + 600n);
        expect((await roles.accruedAllowance(ALLOWANCE_KEY)).balance).to.equal(
          900,
        );
        await time.increaseTo(timestamp + 1200n);
        expect((await roles.accruedAllowance(ALLOWANCE_KEY)).balance).to.equal(
          1000,
        );
      });

      it("discards the part of a refill above maxRefill", async () => {
        const { roles, ALLOWANCE_KEY, stored } = await loadFixture(setup);

        await roles.setAllowance(ALLOWANCE_KEY, 900, 1000, 100, 600, 0);
        const { timestamp } = await stored(ALLOWANCE_KEY);
        // uncapped: 1100
        await time.increaseTo(timestamp + 1200n);

        expect((await roles.accruedAllowance(ALLOWANCE_KEY)).balance).to.equal(
          1000,
        );
      });

      it("caps without overflowing when refills exceed uint128", async () => {
        const { roles, ALLOWANCE_KEY, stored } = await loadFixture(setup);

        await roles.setAllowance(
          ALLOWANCE_KEY,
          0,
          maxUint128,
          maxUint128,
          600,
          0,
        );
        const { timestamp } = await stored(ALLOWANCE_KEY);
        await time.increaseTo(timestamp + 1200n);

        expect((await roles.accruedAllowance(ALLOWANCE_KEY)).balance).to.equal(
          maxUint128,
        );
      });

      it("advances the timestamp with the balance at the cap", async () => {
        const { roles, ALLOWANCE_KEY, stored } = await loadFixture(setup);

        await roles.setAllowance(ALLOWANCE_KEY, 1000, 1000, 100, 600, 0);
        const { timestamp } = await stored(ALLOWANCE_KEY);
        await time.increaseTo(timestamp + 3000n);

        expect(await roles.accruedAllowance(ALLOWANCE_KEY)).to.deep.equal([
          1000n,
          timestamp + 3000n,
        ]);
      });

      it("keeps a balance set above maxRefill, advancing the timestamp", async () => {
        const { roles, ALLOWANCE_KEY, stored } = await loadFixture(setup);

        await roles.setAllowance(ALLOWANCE_KEY, 1500, 1000, 100, 600, 0);
        const { timestamp } = await stored(ALLOWANCE_KEY);
        await time.increaseTo(timestamp + 3000n);

        expect(await roles.accruedAllowance(ALLOWANCE_KEY)).to.deep.equal([
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

      await roles.setAllowance(ALLOWANCE_KEY, 500, 5000, 100, 600, 0);
      const { timestamp } = await stored(ALLOWANCE_KEY);
      await allowWithin("oneParamStatic", [ALLOWANCE_KEY]);

      // 3.5 periods: accrues 800, consumes 150
      await time.setNextBlockTimestamp(timestamp + 2100n);
      await expect(exec("oneParamStatic", [150]))
        .to.emit(roles, "ConsumeAllowance")
        .withArgs(ALLOWANCE_KEY, 150, 650);

      expect(await stored(ALLOWANCE_KEY)).to.deep.equal({
        refill: 100n,
        maxRefill: 5000n,
        period: 600n,
        balance: 650n,
        // the half period still counts towards the next refill
        timestamp: timestamp + 1800n,
      });
      await time.increaseTo(timestamp + 2400n);
      expect(await roles.accruedAllowance(ALLOWANCE_KEY)).to.deep.equal([
        750n,
        timestamp + 2400n,
      ]);
    });

    it("with period 0, only deducts, leaving the timestamp", async () => {
      const { roles, ALLOWANCE_KEY, allowWithin, exec, stored } =
        await loadFixture(setup);

      await roles.setAllowance(ALLOWANCE_KEY, 1000, 0, 0, 0, 0);
      const before = await stored(ALLOWANCE_KEY);
      await allowWithin("oneParamStatic", [ALLOWANCE_KEY]);

      await exec("oneParamStatic", [100]);
      await time.increase(10000);
      await exec("oneParamStatic", [100]);

      expect(await stored(ALLOWANCE_KEY)).to.deep.equal({
        ...before,
        balance: 800n,
      });
    });

    it("consumes from a balance set above maxRefill, uncapped, storing the elapsed period", async () => {
      const { roles, ALLOWANCE_KEY, allowWithin, exec, stored } =
        await loadFixture(setup);

      await roles.setAllowance(ALLOWANCE_KEY, 1300, 1000, 100, 3600, 0);
      const before = await stored(ALLOWANCE_KEY);
      await allowWithin("oneParamStatic", [ALLOWANCE_KEY]);

      // one period later: 1300 is not capped down to 1000 before deducting
      await time.setNextBlockTimestamp(before.timestamp + 3600n);
      await expect(exec("oneParamStatic", [1200]))
        .to.emit(roles, "ConsumeAllowance")
        .withArgs(ALLOWANCE_KEY, 1200, 100);
      expect(await stored(ALLOWANCE_KEY)).to.deep.equal({
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
      const OTHER_KEY = ethers.id("OTHER_ALLOWANCE");

      await roles.setAllowance(ALLOWANCE_KEY, 1000, 0, 0, 0, 0);
      await roles.setAllowance(OTHER_KEY, 500, 0, 0, 0, 0);
      await allowWithin("oneParamStatic", [ALLOWANCE_KEY]);
      await allowWithin("twoParamsStatic", [ALLOWANCE_KEY, OTHER_KEY]);

      const receipt = await (
        await execBatch([
          {
            to: testContractAddress,
            data: iface.encodeFunctionData("oneParamStatic", [30]),
          },
          {
            to: testContractAddress,
            data: iface.encodeFunctionData("twoParamsStatic", [50, 20]),
          },
        ])
      ).wait();

      const rolesAddress = await roles.getAddress();
      const consumed = receipt!.logs
        .filter((l) => l.address === rolesAddress)
        .map((l) => roles.interface.parseLog(l))
        .filter((p) => p?.name === "ConsumeAllowance")
        .map((p) => [...p!.args]);
      expect(consumed).to.deep.equal([
        [ALLOWANCE_KEY, 80n, 920n],
        [OTHER_KEY, 20n, 480n],
      ]);
      expect((await stored(ALLOWANCE_KEY)).balance).to.equal(920);
      expect((await stored(OTHER_KEY)).balance).to.equal(480);
    });

    it("does not emit ConsumeAllowance without a WithinAllowance condition", async () => {
      const { roles, ROLE_KEY, testContractAddress, exec } =
        await loadFixture(setup);

      await roles.allowTargetPacked(
        ROLE_KEY,
        testContractAddress,
        "0x",
        ExecutionOptions.None,
      );

      await expect(exec("oneParamStatic", [100])).to.not.emit(
        roles,
        "ConsumeAllowance",
      );
    });

    it("writes nothing when the executed call fails, after elapsed periods", async () => {
      const { roles, ALLOWANCE_KEY, allowWithin, exec, stored } =
        await loadFixture(setup);

      await roles.setAllowance(ALLOWANCE_KEY, 500, 5000, 100, 600, 0);
      const before = await stored(ALLOWANCE_KEY);
      await allowWithin("fnThatMaybeReverts", [ALLOWANCE_KEY, null]);

      await time.setNextBlockTimestamp(before.timestamp + 2100n);
      await expect(exec("fnThatMaybeReverts", [100, true])).to.not.emit(
        roles,
        "ConsumeAllowance",
      );

      // neither the consumption nor the accrual is written
      expect(await stored(ALLOWANCE_KEY)).to.deep.equal(before);
    });

    describe("against storage as the executed call left it", () => {
      /** A batch that consumes 100 of the allowance, then has the avatar
       *  (made the owner) call Roles with `data`; mined at `timestamp`. */
      async function consumeThenCall(
        fixture: Awaited<ReturnType<typeof setupBatch>>,
        data: string,
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
        await roles.allowTargetPacked(
          ROLE_KEY,
          await roles.getAddress(),
          "0x",
          ExecutionOptions.None,
        );
        await roles.connect(owner).transferOwnership(avatarAddress);

        if (timestamp !== undefined)
          await time.setNextBlockTimestamp(timestamp);
        return execBatch([
          {
            to: testContractAddress,
            data: iface.encodeFunctionData("oneParamStatic", [100]),
          },
          { to: await roles.getAddress(), data },
        ]);
      }

      it("deducts from a balance the call raised", async () => {
        const fixture = await loadFixture(setupBatch);
        const { roles, ALLOWANCE_KEY, stored } = fixture;
        await roles.setAllowance(ALLOWANCE_KEY, 1000, 0, 0, 0, 0);

        await expect(
          consumeThenCall(
            fixture,
            roles.interface.encodeFunctionData("setAllowance", [
              ALLOWANCE_KEY,
              5000,
              0,
              0,
              0,
              0,
            ]),
          ),
        )
          .to.emit(roles, "ConsumeAllowance")
          .withArgs(ALLOWANCE_KEY, 100, 4900);
        expect((await stored(ALLOWANCE_KEY)).balance).to.equal(4900);
      });

      it("reverts AllowanceExceeded when the call lowered the balance below the consumption", async () => {
        const fixture = await loadFixture(setupBatch);
        const { roles, ALLOWANCE_KEY } = fixture;
        await roles.setAllowance(ALLOWANCE_KEY, 1000, 0, 0, 0, 0);

        await expect(
          consumeThenCall(
            fixture,
            roles.interface.encodeFunctionData("setAllowance", [
              ALLOWANCE_KEY,
              50,
              0,
              0,
              0,
              0,
            ]),
          ),
        )
          .to.be.revertedWithCustomError(roles, "AllowanceExceeded")
          .withArgs(ALLOWANCE_KEY);
      });

      it("reverts AllowanceExceeded when the call disabled the refill the consumption relied on", async () => {
        const fixture = await loadFixture(setupBatch);
        const { roles, ALLOWANCE_KEY, stored } = fixture;
        // nothing stored; one period accrues 100, which is consumed
        await roles.setAllowance(ALLOWANCE_KEY, 0, 0, 100, 600, 0);
        const { timestamp } = await stored(ALLOWANCE_KEY);

        await expect(
          consumeThenCall(
            fixture,
            roles.interface.encodeFunctionData("updateAllowance", [
              ALLOWANCE_KEY,
              0,
              100,
              0,
            ]),
            timestamp + 600n,
          ),
        )
          .to.be.revertedWithCustomError(roles, "AllowanceExceeded")
          .withArgs(ALLOWANCE_KEY);
      });
    });
  });
});
