import assert from "node:assert/strict";
import { randomBytes } from "node:crypto";
import { after, describe, it } from "node:test";
import { network } from "hardhat";
import {
  encodeFunctionData,
  getAddress,
  isAddressEqual,
  parseAbi,
  parseEventLogs,
  toHex,
  zeroHash,
} from "viem";
import type { Address, Hex } from "viem";

import { createSetup } from "./setup.js";
import {
  encodeMultisendPayload,
  maxUint64,
  maxUint128,
  type RolesContract,
  assertNotEmitted,
} from "./utils.js";

const connection = await network.create();
const { viem, networkHelpers } = connection;
const { loadFixture, time } = networkHelpers;
const { deployRolesMod, deployMultiSend } = createSetup(connection);

/**
 * Membership tests
 *
 * Scope: Module Authentication & Access Control.
 *
 * This file verifies the mechanism for validating a module's role membership:
 * - Role Assignment: confirming the module holds the specified role.
 * - Validity Window: Enforcing start and end timestamps for the role.
 * - Usage Accounting: Decrementing usage counters for finite roles and handling expiration.
 * - State Updates: Verifying that usage state is correctly updated in storage.
 */

const abi = parseAbi(["function doNothing()"]);

describe("Membership", () => {
  after(async () => {
    await connection.close();
  });

  async function setup() {
    const [owner, member, other] = await viem.getWalletClients();

    const avatar = await viem.deployContract("TestAvatar");
    const avatarAddress = avatar.address;

    const roles = await deployRolesMod(
      owner.account.address,
      avatarAddress,
      avatarAddress,
    );

    const testContract = await viem.deployContract("TestContract");
    const testContractAddress = testContract.address;

    const ROLE_KEY = toHex(randomBytes(32));

    return {
      roles,
      avatar,
      avatarAddress,
      owner,
      member,
      other,
      testContract,
      testContractAddress,
      ROLE_KEY,
    };
  }

  describe("_authenticate", () => {
    it("reverts when caller is not an enabled module", async () => {
      const { roles, other, testContractAddress } = await loadFixture(setup);

      // other is not an enabled module
      await viem.assertions.revertWithCustomError(
        roles.write.execTransactionFromModule(
          [testContractAddress, 0n, "0x", 0],
          {
            account: other.account,
          },
        ),
        roles,
        "NotAuthorized",
      );
    });

    it("reverts NoMembership when module has no membership for role", async () => {
      const { roles, member, testContractAddress, ROLE_KEY } =
        await loadFixture(setup);

      await roles.write.enableModule([member.account.address]);
      await roles.write.setDefaultRole([member.account.address, ROLE_KEY]);

      await viem.assertions.revertWithCustomError(
        roles.write.execTransactionFromModule(
          [testContractAddress, 0n, "0x", 0],
          {
            account: member.account,
          },
        ),
        roles,
        "NoMembership",
      );
    });

    it("reverts NoMembership after membership has been revoked", async () => {
      const { roles, member, testContractAddress, ROLE_KEY } =
        await loadFixture(setup);

      await roles.write.grantRole([
        member.account.address,
        ROLE_KEY,
        0n,
        0n,
        0n,
      ]);
      await roles.write.setDefaultRole([member.account.address, ROLE_KEY]);
      await roles.write.allowTargetPacked([
        ROLE_KEY,
        testContractAddress,
        "0x",
        0,
      ]);

      await roles.write.execTransactionFromModule(
        [testContractAddress, 0n, "0x", 0],
        { account: member.account },
      );

      await roles.write.revokeRole([member.account.address, ROLE_KEY]);

      await viem.assertions.revertWithCustomError(
        roles.write.execTransactionFromModule(
          [testContractAddress, 0n, "0x", 0],
          {
            account: member.account,
          },
        ),
        roles,
        "NoMembership",
      );
    });

    it("rejects zero role even if membership storage is non-zero", async () => {
      const { roles, member, testContractAddress } = await loadFixture(setup);

      const ZERO_ROLE = zeroHash;

      await roles.write.grantRole([
        member.account.address,
        ZERO_ROLE,
        0n,
        0n,
        0n,
      ]);

      await viem.assertions.revertWithCustomError(
        roles.write.execTransactionWithRole(
          [testContractAddress, 0n, "0x", 0, ZERO_ROLE],
          { account: member.account },
        ),
        roles,
        "NoMembership",
      );
    });

    describe("validity window", () => {
      it("reverts MembershipNotYetValid before start timestamp", async () => {
        const { roles, member, testContractAddress, ROLE_KEY } =
          await loadFixture(setup);

        const futureStart = BigInt(await time.latest()) + 3600n;

        await roles.write.grantRole([
          member.account.address,
          ROLE_KEY,
          futureStart,
          0n,
          0n,
        ]);
        await roles.write.setDefaultRole([member.account.address, ROLE_KEY]);
        await roles.write.allowTargetPacked([
          ROLE_KEY,
          testContractAddress,
          "0x",
          0,
        ]);

        await viem.assertions.revertWithCustomError(
          roles.write.execTransactionFromModule(
            [testContractAddress, 0n, "0x", 0],
            { account: member.account },
          ),
          roles,
          "MembershipNotYetValid",
        );
      });

      it("succeeds at exactly start timestamp (boundary)", async () => {
        const { roles, member, testContractAddress, ROLE_KEY } =
          await loadFixture(setup);

        const start = BigInt(await time.latest()) + 100n;

        await roles.write.grantRole([
          member.account.address,
          ROLE_KEY,
          start,
          0n,
          0n,
        ]);
        await roles.write.setDefaultRole([member.account.address, ROLE_KEY]);
        await roles.write.allowTargetPacked([
          ROLE_KEY,
          testContractAddress,
          "0x",
          0,
        ]);

        await time.increaseTo(start);

        await roles.write.execTransactionFromModule(
          [testContractAddress, 0n, "0x", 0],
          { account: member.account },
        );
      });

      it("succeeds when within valid window", async () => {
        const { roles, member, testContractAddress, ROLE_KEY } =
          await loadFixture(setup);

        const now = BigInt(await time.latest());
        const start = now - 100n;
        const end = now + 3600n;

        await roles.write.grantRole([
          member.account.address,
          ROLE_KEY,
          start,
          end,
          0n,
        ]);
        await roles.write.setDefaultRole([member.account.address, ROLE_KEY]);
        await roles.write.allowTargetPacked([
          ROLE_KEY,
          testContractAddress,
          "0x",
          0,
        ]);

        await roles.write.execTransactionFromModule(
          [testContractAddress, 0n, "0x", 0],
          { account: member.account },
        );
      });

      it("succeeds at exactly end timestamp (boundary)", async () => {
        const { roles, member, testContractAddress, ROLE_KEY } =
          await loadFixture(setup);

        const end = BigInt(await time.latest()) + 100n;

        await roles.write.grantRole([
          member.account.address,
          ROLE_KEY,
          0n,
          end,
          0n,
        ]);
        await roles.write.setDefaultRole([member.account.address, ROLE_KEY]);
        await roles.write.allowTargetPacked([
          ROLE_KEY,
          testContractAddress,
          "0x",
          0,
        ]);

        await time.setNextBlockTimestamp(end);

        await roles.write.execTransactionFromModule(
          [testContractAddress, 0n, "0x", 0],
          { account: member.account },
        );
      });

      it("never validates a window that ends before it starts", async () => {
        const { roles, member, testContractAddress, ROLE_KEY } =
          await loadFixture(setup);

        const now = BigInt(await time.latest());
        const [start, end] = [now + 100n, now + 50n];
        await roles.write.grantRole([
          member.account.address,
          ROLE_KEY,
          start,
          end,
          0n,
        ]);
        await roles.write.setDefaultRole([member.account.address, ROLE_KEY]);
        await roles.write.allowTargetPacked([
          ROLE_KEY,
          testContractAddress,
          "0x",
          0,
        ]);
        const exec = () =>
          roles.write.execTransactionFromModule(
            [testContractAddress, 0n, "0x", 0],
            { account: member.account },
          );

        await viem.assertions.revertWithCustomError(
          exec(),
          roles,
          "MembershipNotYetValid",
        );
        assert.equal(
          (
            await roles.read.membershipOf([member.account.address, ROLE_KEY])
          )[0],
          false,
        );

        await time.setNextBlockTimestamp(start);
        await viem.assertions.revertWithCustomError(
          exec(),
          roles,
          "MembershipExpired",
        );
        assert.equal(
          (
            await roles.read.membershipOf([member.account.address, ROLE_KEY])
          )[0],
          false,
        );
      });

      it("reverts MembershipExpired after end timestamp", async () => {
        const { roles, member, testContractAddress, ROLE_KEY } =
          await loadFixture(setup);

        const end = BigInt(await time.latest()) + 100n;

        await roles.write.grantRole([
          member.account.address,
          ROLE_KEY,
          0n,
          end,
          0n,
        ]);
        await roles.write.setDefaultRole([member.account.address, ROLE_KEY]);
        await roles.write.allowTargetPacked([
          ROLE_KEY,
          testContractAddress,
          "0x",
          0,
        ]);

        await time.increaseTo(end + 1n);

        await viem.assertions.revertWithCustomError(
          roles.write.execTransactionFromModule(
            [testContractAddress, 0n, "0x", 0],
            { account: member.account },
          ),
          roles,
          "MembershipExpired",
        );
      });
    });

    describe("usage accounting", () => {
      /** The membership events Roles emitted in the receipt, in order:
       *  `grant n`, `update n` (`n` uses left) and `revoke`. */
      const membershipEvents = async (roles: RolesContract, hash: Hex) => {
        const publicClient = await viem.getPublicClient();
        const receipt = await publicClient.waitForTransactionReceipt({ hash });
        return parseEventLogs({
          abi: roles.abi,
          logs: receipt.logs.filter((log) =>
            isAddressEqual(log.address, roles.address),
          ),
        }).flatMap((event) =>
          event.eventName === "RevokeRole"
            ? ["revoke"]
            : event.eventName === "GrantRole"
              ? [`grant ${event.args.usesLeft}`]
              : event.eventName === "UpdateRole"
                ? [`update ${event.args.usesLeft}`]
                : [],
        );
      };

      it("never uses up an unlimited membership", async () => {
        const { roles, member, testContractAddress, ROLE_KEY } =
          await loadFixture(setup);

        await roles.write.grantRole([
          member.account.address,
          ROLE_KEY,
          0n,
          0n,
          0n,
        ]);
        await roles.write.setDefaultRole([member.account.address, ROLE_KEY]);
        await roles.write.allowTargetPacked([
          ROLE_KEY,
          testContractAddress,
          "0x",
          0,
        ]);

        for (let i = 0; i < 3; i++) {
          const hash = await roles.write.execTransactionFromModule(
            [testContractAddress, 0n, "0x", 0],
            { account: member.account },
          );
          await assertNotEmitted(viem, hash, roles, "UpdateRole");
          await assertNotEmitted(viem, hash, roles, "RevokeRole");
        }
        assert.equal(
          (
            await roles.read.membershipOf([member.account.address, ROLE_KEY])
          )[3],
          maxUint128,
        );
      });

      it("counts down a finite membership, keeping its window, then revokes it", async () => {
        const { roles, member, testContractAddress, ROLE_KEY } =
          await loadFixture(setup);

        const now = BigInt(await time.latest());
        const [start, end] = [now - 100n, now + 10000n];
        await roles.write.grantRole([
          member.account.address,
          ROLE_KEY,
          start,
          end,
          3n,
        ]);
        await roles.write.setDefaultRole([member.account.address, ROLE_KEY]);
        await roles.write.allowTargetPacked([
          ROLE_KEY,
          testContractAddress,
          "0x",
          0,
        ]);
        const exec = () =>
          roles.write.execTransactionFromModule(
            [testContractAddress, 0n, "0x", 0],
            { account: member.account },
          );

        await viem.assertions.emitWithArgs(exec(), roles, "UpdateRole", [
          ROLE_KEY,
          member.account.address,
          start,
          end,
          2n,
        ]);
        await viem.assertions.emitWithArgs(exec(), roles, "UpdateRole", [
          ROLE_KEY,
          member.account.address,
          start,
          end,
          1n,
        ]);
        const revokeHash = await exec();
        await viem.assertions.emitWithArgs(revokeHash, roles, "RevokeRole", [
          ROLE_KEY,
          member.account.address,
        ]);
        await assertNotEmitted(viem, revokeHash, roles, "UpdateRole");

        assert.deepEqual(
          await roles.read.membershipOf([member.account.address, ROLE_KEY]),
          [false, 0n, 0n, 0n],
        );
        await viem.assertions.revertWithCustomError(
          exec(),
          roles,
          "NoMembership",
        );
      });

      describe("batches", () => {
        /** A MultiSend batch of `n` calls to the test contract, unwrapped. */
        async function setupBatch(n: number) {
          const fixture = await setup();
          const { roles, testContractAddress } = fixture;
          const { multisend } = await deployMultiSend(roles);
          const batch = encodeFunctionData({
            abi: multisend.abi,
            functionName: "multiSend",
            args: [
              encodeMultisendPayload(
                Array.from({ length: n }, () => ({
                  to: testContractAddress,
                  value: 0n,
                  data: encodeFunctionData({ abi, functionName: "doNothing" }),
                  operation: 0,
                })),
              ),
            ],
          });
          return {
            ...fixture,
            multisendAddress: multisend.address,
            batch,
          };
        }
        const setupBatchOf3 = () => setupBatch(3);

        it("a batch is one use, whatever its number of calls", async () => {
          const {
            roles,
            member,
            testContractAddress,
            multisendAddress,
            batch,
            ROLE_KEY,
          } = await loadFixture(setupBatchOf3);
          await roles.write.grantRole([
            member.account.address,
            ROLE_KEY,
            0n,
            0n,
            3n,
          ]);
          await roles.write.allowTargetPacked([
            ROLE_KEY,
            testContractAddress,
            "0x",
            0,
          ]);

          const hash = await roles.write.execTransactionWithRole(
            [multisendAddress, 0n, batch, 1, ROLE_KEY],
            { account: member.account },
          );

          assert.deepEqual(await membershipEvents(roles, hash), ["update 2"]);
          assert.equal(
            (
              await roles.read.membershipOf([member.account.address, ROLE_KEY])
            )[3],
            2n,
          );
        });

        it("the last use covers a whole batch, then revokes", async () => {
          const {
            roles,
            member,
            testContractAddress,
            multisendAddress,
            batch,
            ROLE_KEY,
          } = await loadFixture(setupBatchOf3);
          await roles.write.grantRole([
            member.account.address,
            ROLE_KEY,
            0n,
            0n,
            1n,
          ]);
          await roles.write.allowTargetPacked([
            ROLE_KEY,
            testContractAddress,
            "0x",
            0,
          ]);

          const hash = await roles.write.execTransactionWithRole(
            [multisendAddress, 0n, batch, 1, ROLE_KEY],
            { account: member.account },
          );

          assert.deepEqual(await membershipEvents(roles, hash), ["revoke"]);
          await viem.assertions.revertWithCustomError(
            roles.write.execTransactionWithRole(
              [multisendAddress, 0n, batch, 1, ROLE_KEY],
              { account: member.account },
            ),
            roles,
            "NoMembership",
          );
        });

        it("a refused batch uses nothing", async () => {
          const { roles, member, multisendAddress, batch, ROLE_KEY } =
            await loadFixture(setupBatchOf3);
          // the role has no permission on the batch's target
          await roles.write.grantRole([
            member.account.address,
            ROLE_KEY,
            0n,
            0n,
            2n,
          ]);

          await viem.assertions.revertWithCustomError(
            roles.write.execTransactionWithRole(
              [multisendAddress, 0n, batch, 1, ROLE_KEY],
              { account: member.account },
            ),
            roles,
            "TransactionNotAllowed",
          );
          assert.equal(
            (
              await roles.read.membershipOf([member.account.address, ROLE_KEY])
            )[3],
            2n,
          );
        });
      });

      describe("settles the membership as the executed call left it", () => {
        /** The member may call Roles itself, which the avatar now owns: an
         *  executed call can change the member's own membership. */
        async function setupSelfManaged() {
          const fixture = await setup();
          const {
            roles,
            member,
            avatarAddress,
            testContractAddress,
            ROLE_KEY,
          } = fixture;
          await roles.write.setDefaultRole([member.account.address, ROLE_KEY]);
          await roles.write.allowTargetPacked([
            ROLE_KEY,
            roles.address,
            "0x",
            0,
          ]);
          await roles.write.allowTargetPacked([
            ROLE_KEY,
            testContractAddress,
            "0x",
            0,
          ]);
          await roles.write.transferOwnership([avatarAddress]);
          return fixture;
        }

        type Window = [start: bigint, end: bigint, uses: bigint];
        const CASES: {
          what: string;
          before: (now: bigint) => Window;
          // a new membership granted during execution, or a revocation
          during: (now: bigint) => Window | "revoke";
          events: (now: bigint) => string[];
          after: (now: bigint) => [boolean, bigint, bigint, bigint];
        }[] = [
          {
            what: "revoked",
            before: () => [0n, 0n, 3n],
            during: () => "revoke",
            events: () => ["revoke"],
            after: () => [false, 0n, 0n, 0n],
          },
          {
            what: "revoked on its last use (one RevokeRole)",
            before: () => [0n, 0n, 1n],
            during: () => "revoke",
            events: () => ["revoke"],
            after: () => [false, 0n, 0n, 0n],
          },
          {
            what: "upgraded from finite to unlimited",
            before: () => [0n, 0n, 2n],
            during: () => [0n, 0n, 0n],
            events: () => [`grant ${maxUint128}`],
            after: () => [true, 0n, maxUint64, maxUint128],
          },
          {
            what: "replaced by another finite membership",
            before: (now) => [0n, now + 1000n, 3n],
            during: (now) => [now - 50n, now + 5000n, 5n],
            events: () => ["grant 5", "update 4"],
            after: (now) => [true, now - 50n, now + 5000n, 4n],
          },
          {
            what: "downgraded from unlimited to 2 uses",
            before: () => [0n, 0n, 0n],
            during: () => [0n, 0n, 2n],
            events: () => ["grant 2", "update 1"],
            after: () => [true, 0n, maxUint64, 1n],
          },
          {
            what: "downgraded from unlimited to 1 use",
            before: () => [0n, 0n, 0n],
            during: () => [0n, 0n, 1n],
            events: () => ["grant 1", "revoke"],
            after: () => [false, 0n, 0n, 0n],
          },
          {
            what: "reduced from 3 uses to 1",
            before: () => [0n, 0n, 3n],
            during: () => [0n, 0n, 1n],
            events: () => ["grant 1", "revoke"],
            after: () => [false, 0n, 0n, 0n],
          },
        ];

        for (const { what, before, during, events, after } of CASES)
          it(`when ${what}`, async () => {
            const { roles, avatar, member, ROLE_KEY } =
              await loadFixture(setupSelfManaged);
            const now = BigInt(await time.latest());
            // the avatar owns Roles now: it grants as the owner
            await avatar.write.exec([
              roles.address,
              0n,
              encodeFunctionData({
                abi: roles.abi,
                functionName: "grantRole",
                args: [member.account.address, ROLE_KEY, ...before(now)],
              }),
              0,
            ]);

            const change = during(now);
            const data =
              change === "revoke"
                ? encodeFunctionData({
                    abi: roles.abi,
                    functionName: "revokeRole",
                    args: [member.account.address, ROLE_KEY],
                  })
                : encodeFunctionData({
                    abi: roles.abi,
                    functionName: "grantRole",
                    args: [member.account.address, ROLE_KEY, ...change],
                  });
            const hash = await roles.write.execTransactionFromModule(
              [roles.address, 0n, data, 0],
              { account: member.account },
            );

            assert.deepEqual(await membershipEvents(roles, hash), events(now));
            assert.deepEqual(
              await roles.read.membershipOf([member.account.address, ROLE_KEY]),
              after(now),
            );
          });

        it("when the module renounced it", async () => {
          const {
            roles,
            avatar,
            avatarAddress,
            testContractAddress,
            ROLE_KEY,
          } = await loadFixture(setup);
          // the avatar is the module: the renouncement comes from it
          await roles.write.grantRole([avatarAddress, ROLE_KEY, 0n, 0n, 3n]);
          await roles.write.setDefaultRole([avatarAddress, ROLE_KEY]);
          await roles.write.allowTargetPacked([
            ROLE_KEY,
            roles.address,
            "0x",
            0,
          ]);
          await roles.write.allowTargetPacked([
            ROLE_KEY,
            testContractAddress,
            "0x",
            0,
          ]);
          const asModule = (to: Address, data: Hex) =>
            avatar.write.exec([
              roles.address,
              0n,
              encodeFunctionData({
                abi: roles.abi,
                functionName: "execTransactionFromModule",
                args: [to, 0n, data, 0],
              }),
              0,
            ]);

          const hash = await asModule(
            roles.address,
            encodeFunctionData({
              abi: roles.abi,
              functionName: "renounceRole",
              args: [ROLE_KEY],
            }),
          );
          await viem.assertions.emitWithArgs(hash, roles, "RevokeRole", [
            ROLE_KEY,
            avatarAddress,
          ]);
          await assertNotEmitted(viem, hash, roles, "UpdateRole");

          assert.deepEqual(
            await roles.read.membershipOf([avatarAddress, ROLE_KEY]),
            [false, 0n, 0n, 0n],
          );
          await viem.assertions.revertWithCustomError(
            asModule(testContractAddress, "0x"),
            roles,
            "NoMembership",
          );
        });
      });
    });
  });

  describe("membership active", () => {
    it("returns false for zero role key", async () => {
      const { roles, member } = await loadFixture(setup);

      assert.equal(
        (await roles.read.membershipOf([member.account.address, zeroHash]))[0],
        false,
      );
    });

    it("returns false when module has no membership", async () => {
      const { roles, member, ROLE_KEY } = await loadFixture(setup);

      assert.equal(
        (await roles.read.membershipOf([member.account.address, ROLE_KEY]))[0],
        false,
      );
    });

    it("returns true for active unlimited membership", async () => {
      const { roles, member, ROLE_KEY } = await loadFixture(setup);

      await roles.write.grantRole([
        member.account.address,
        ROLE_KEY,
        0n,
        0n,
        0n,
      ]);

      assert.equal(
        (await roles.read.membershipOf([member.account.address, ROLE_KEY]))[0],
        true,
      );
    });

    it("returns true for active finite membership", async () => {
      const { roles, member, ROLE_KEY } = await loadFixture(setup);

      await roles.write.grantRole([
        member.account.address,
        ROLE_KEY,
        0n,
        0n,
        5n,
      ]);

      assert.equal(
        (await roles.read.membershipOf([member.account.address, ROLE_KEY]))[0],
        true,
      );
    });

    it("returns false after membership is revoked", async () => {
      const { roles, member, ROLE_KEY } = await loadFixture(setup);

      await roles.write.grantRole([
        member.account.address,
        ROLE_KEY,
        0n,
        0n,
        0n,
      ]);
      assert.equal(
        (await roles.read.membershipOf([member.account.address, ROLE_KEY]))[0],
        true,
      );

      await roles.write.revokeRole([member.account.address, ROLE_KEY]);
      assert.equal(
        (await roles.read.membershipOf([member.account.address, ROLE_KEY]))[0],
        false,
      );
    });

    it("returns false before start timestamp", async () => {
      const { roles, member, ROLE_KEY } = await loadFixture(setup);

      const futureStart = BigInt(await time.latest()) + 3600n;
      await roles.write.grantRole([
        member.account.address,
        ROLE_KEY,
        futureStart,
        0n,
        0n,
      ]);

      assert.equal(
        (await roles.read.membershipOf([member.account.address, ROLE_KEY]))[0],
        false,
      );
    });

    it("returns true at exactly start timestamp", async () => {
      const { roles, member, ROLE_KEY } = await loadFixture(setup);

      const start = BigInt(await time.latest()) + 100n;
      await roles.write.grantRole([
        member.account.address,
        ROLE_KEY,
        start,
        0n,
        0n,
      ]);

      await time.increaseTo(start);

      assert.equal(
        (await roles.read.membershipOf([member.account.address, ROLE_KEY]))[0],
        true,
      );
    });

    it("returns false after end timestamp", async () => {
      const { roles, member, ROLE_KEY } = await loadFixture(setup);

      const end = BigInt(await time.latest()) + 100n;
      await roles.write.grantRole([
        member.account.address,
        ROLE_KEY,
        0n,
        end,
        0n,
      ]);

      await time.increaseTo(end + 1n);

      assert.equal(
        (await roles.read.membershipOf([member.account.address, ROLE_KEY]))[0],
        false,
      );
    });

    it("returns true at exactly end timestamp", async () => {
      const { roles, member, ROLE_KEY } = await loadFixture(setup);

      const end = BigInt(await time.latest()) + 100n;
      await roles.write.grantRole([
        member.account.address,
        ROLE_KEY,
        0n,
        end,
        0n,
      ]);

      await time.increaseTo(end);

      assert.equal(
        (await roles.read.membershipOf([member.account.address, ROLE_KEY]))[0],
        true,
      );
    });

    it("callable by anyone, not just modules", async () => {
      const { roles, member, other, ROLE_KEY } = await loadFixture(setup);

      await roles.write.grantRole([
        member.account.address,
        ROLE_KEY,
        0n,
        0n,
        0n,
      ]);

      // other is not a module but can still read membership
      assert.equal(
        (
          await roles.read.membershipOf([member.account.address, ROLE_KEY], {
            account: other.account,
          })
        )[0],
        true,
      );
    });

    it("returns false for a member whose module was disabled, which cannot execute, keeping its fields", async () => {
      const { roles, member, testContractAddress, ROLE_KEY } =
        await loadFixture(setup);

      await roles.write.grantRole([
        member.account.address,
        ROLE_KEY,
        0n,
        0n,
        3n,
      ]);
      await roles.write.allowTargetPacked([
        ROLE_KEY,
        testContractAddress,
        "0x",
        0,
      ]);
      await roles.write.disableModule([
        getAddress("0x0000000000000000000000000000000000000001"),
        member.account.address,
      ]);

      assert.deepEqual(
        await roles.read.membershipOf([member.account.address, ROLE_KEY]),
        [false, 0n, maxUint64, 3n],
      );
      await viem.assertions.revertWithCustomError(
        roles.write.execTransactionWithRole(
          [testContractAddress, 0n, "0x", 0, ROLE_KEY],
          { account: member.account },
        ),
        roles,
        "NotAuthorized",
      );
    });
  });

  describe("membership fields", () => {
    it("returns zeros when there is no membership", async () => {
      const { roles, member, ROLE_KEY } = await loadFixture(setup);

      assert.deepEqual(
        await roles.read.membershipOf([member.account.address, ROLE_KEY]),
        [false, 0n, 0n, 0n],
      );
    });

    it("returns start, end and uses left as stored", async () => {
      const { roles, member, ROLE_KEY } = await loadFixture(setup);

      await roles.write.grantRole([
        member.account.address,
        ROLE_KEY,
        10n,
        20n,
        3n,
      ]);
      assert.deepEqual(
        await roles.read.membershipOf([member.account.address, ROLE_KEY]),
        [false, 10n, 20n, 3n],
      );

      await roles.write.grantRole([
        member.account.address,
        ROLE_KEY,
        0n,
        0n,
        0n,
      ]);
      assert.deepEqual(
        await roles.read.membershipOf([member.account.address, ROLE_KEY]),
        [true, 0n, maxUint64, maxUint128],
      );
    });
  });
});
