import { expect } from "chai";
import { Interface } from "ethers";
import type { ContractTransactionReceipt } from "ethers";
import { network } from "hardhat";

import { createSetup } from "./setup.js";
import type { Roles } from "../typechain-types/contracts/Roles.js";
import { encodeMultisendPayload, maxUint64, maxUint128 } from "./utils.js";

const connection = await network.create();
const { ethers, networkHelpers } = connection;
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

const iface = new Interface(["function doNothing()"]);

describe("Membership", () => {
  after(async () => {
    await connection.close();
  });

  async function setup() {
    const [owner, member, other] = await ethers.getSigners();

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

    const ROLE_KEY = ethers.hexlify(ethers.randomBytes(32));

    return {
      roles: roles.connect(owner),
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
      await expect(
        roles
          .connect(other)
          .execTransactionFromModule(testContractAddress, 0, "0x", 0),
      ).to.be.revertedWithCustomError(roles, "NotAuthorized");
    });

    it("reverts NoMembership when module has no membership for role", async () => {
      const { roles, member, testContractAddress, ROLE_KEY } =
        await loadFixture(setup);

      await roles.enableModule(member.address);
      await roles.setDefaultRole(member.address, ROLE_KEY);

      await expect(
        roles
          .connect(member)
          .execTransactionFromModule(testContractAddress, 0, "0x", 0),
      ).to.be.revertedWithCustomError(roles, "NoMembership");
    });

    it("reverts NoMembership after membership has been revoked", async () => {
      const { roles, member, testContractAddress, ROLE_KEY } =
        await loadFixture(setup);

      await roles.grantRole(member.address, ROLE_KEY, 0, 0, 0);
      await roles.setDefaultRole(member.address, ROLE_KEY);
      await roles.allowTargetPacked(ROLE_KEY, testContractAddress, "0x", 0);

      await expect(
        roles
          .connect(member)
          .execTransactionFromModule(testContractAddress, 0, "0x", 0),
      ).to.not.be.revert(ethers);

      await roles.revokeRole(member.address, ROLE_KEY);

      await expect(
        roles
          .connect(member)
          .execTransactionFromModule(testContractAddress, 0, "0x", 0),
      ).to.be.revertedWithCustomError(roles, "NoMembership");
    });

    it("rejects zero role even if membership storage is non-zero", async () => {
      const { roles, member, testContractAddress } = await loadFixture(setup);

      const ZERO_ROLE = ethers.ZeroHash;

      await roles.grantRole(member.address, ZERO_ROLE, 0, 0, 0);

      await expect(
        roles
          .connect(member)
          .execTransactionWithRole(testContractAddress, 0, "0x", 0, ZERO_ROLE),
      ).to.be.revertedWithCustomError(roles, "NoMembership");
    });

    describe("validity window", () => {
      it("reverts MembershipNotYetValid before start timestamp", async () => {
        const { roles, member, testContractAddress, ROLE_KEY } =
          await loadFixture(setup);

        const futureStart = (await time.latest()) + 3600;

        await roles.grantRole(member.address, ROLE_KEY, futureStart, 0, 0);
        await roles.setDefaultRole(member.address, ROLE_KEY);
        await roles.allowTargetPacked(ROLE_KEY, testContractAddress, "0x", 0);

        await expect(
          roles
            .connect(member)
            .execTransactionFromModule(testContractAddress, 0, "0x", 0),
        ).to.be.revertedWithCustomError(roles, "MembershipNotYetValid");
      });

      it("succeeds at exactly start timestamp (boundary)", async () => {
        const { roles, member, testContractAddress, ROLE_KEY } =
          await loadFixture(setup);

        const start = (await time.latest()) + 100;

        await roles.grantRole(member.address, ROLE_KEY, start, 0, 0);
        await roles.setDefaultRole(member.address, ROLE_KEY);
        await roles.allowTargetPacked(ROLE_KEY, testContractAddress, "0x", 0);

        await time.increaseTo(start);

        await expect(
          roles
            .connect(member)
            .execTransactionFromModule(testContractAddress, 0, "0x", 0),
        ).to.not.be.revert(ethers);
      });

      it("succeeds when within valid window", async () => {
        const { roles, member, testContractAddress, ROLE_KEY } =
          await loadFixture(setup);

        const now = await time.latest();
        const start = now - 100;
        const end = now + 3600;

        await roles.grantRole(member.address, ROLE_KEY, start, end, 0);
        await roles.setDefaultRole(member.address, ROLE_KEY);
        await roles.allowTargetPacked(ROLE_KEY, testContractAddress, "0x", 0);

        await expect(
          roles
            .connect(member)
            .execTransactionFromModule(testContractAddress, 0, "0x", 0),
        ).to.not.be.revert(ethers);
      });

      it("succeeds at exactly end timestamp (boundary)", async () => {
        const { roles, member, testContractAddress, ROLE_KEY } =
          await loadFixture(setup);

        const end = (await time.latest()) + 100;

        await roles.grantRole(member.address, ROLE_KEY, 0, end, 0);
        await roles.setDefaultRole(member.address, ROLE_KEY);
        await roles.allowTargetPacked(ROLE_KEY, testContractAddress, "0x", 0);

        await time.setNextBlockTimestamp(end);

        await expect(
          roles
            .connect(member)
            .execTransactionFromModule(testContractAddress, 0, "0x", 0),
        ).to.not.be.revert(ethers);
      });

      it("never validates a window that ends before it starts", async () => {
        const { roles, member, testContractAddress, ROLE_KEY } =
          await loadFixture(setup);

        const now = await time.latest();
        const [start, end] = [now + 100, now + 50];
        await roles.grantRole(member.address, ROLE_KEY, start, end, 0);
        await roles.setDefaultRole(member.address, ROLE_KEY);
        await roles.allowTargetPacked(ROLE_KEY, testContractAddress, "0x", 0);
        const exec = () =>
          roles
            .connect(member)
            .execTransactionFromModule(testContractAddress, 0, "0x", 0);

        await expect(exec()).to.be.revertedWithCustomError(
          roles,
          "MembershipNotYetValid",
        );
        expect((await roles.membershipOf(member.address, ROLE_KEY)).active).to
          .be.false;

        await time.setNextBlockTimestamp(start);
        await expect(exec()).to.be.revertedWithCustomError(
          roles,
          "MembershipExpired",
        );
        expect((await roles.membershipOf(member.address, ROLE_KEY)).active).to
          .be.false;
      });

      it("reverts MembershipExpired after end timestamp", async () => {
        const { roles, member, testContractAddress, ROLE_KEY } =
          await loadFixture(setup);

        const end = (await time.latest()) + 100;

        await roles.grantRole(member.address, ROLE_KEY, 0, end, 0);
        await roles.setDefaultRole(member.address, ROLE_KEY);
        await roles.allowTargetPacked(ROLE_KEY, testContractAddress, "0x", 0);

        await time.increaseTo(end + 1);

        await expect(
          roles
            .connect(member)
            .execTransactionFromModule(testContractAddress, 0, "0x", 0),
        ).to.be.revertedWithCustomError(roles, "MembershipExpired");
      });
    });

    describe("usage accounting", () => {
      /** The membership events Roles emitted in the receipt, in order:
       *  `grant n`, `update n` (`n` uses left) and `revoke`. */
      const membershipEvents = async (
        roles: Roles,
        receipt: ContractTransactionReceipt | null,
      ) => {
        const rolesAddress = await roles.getAddress();
        return receipt!.logs
          .filter((log) => log.address === rolesAddress)
          .map((log) => roles.interface.parseLog(log))
          .flatMap((event) =>
            event?.name === "RevokeRole"
              ? ["revoke"]
              : event?.name === "GrantRole"
                ? [`grant ${event.args[4]}`]
                : event?.name === "UpdateRole"
                  ? [`update ${event.args[4]}`]
                  : [],
          );
      };

      it("never uses up an unlimited membership", async () => {
        const { roles, member, testContractAddress, ROLE_KEY } =
          await loadFixture(setup);

        await roles.grantRole(member.address, ROLE_KEY, 0, 0, 0);
        await roles.setDefaultRole(member.address, ROLE_KEY);
        await roles.allowTargetPacked(ROLE_KEY, testContractAddress, "0x", 0);

        for (let i = 0; i < 3; i++)
          await expect(
            roles
              .connect(member)
              .execTransactionFromModule(testContractAddress, 0, "0x", 0),
          )
            .to.not.emit(roles, "UpdateRole")
            .and.not.to.emit(roles, "RevokeRole");
        expect(
          (await roles.membershipOf(member.address, ROLE_KEY)).usesLeft,
        ).to.equal(maxUint128);
      });

      it("counts down a finite membership, keeping its window, then revokes it", async () => {
        const { roles, member, testContractAddress, ROLE_KEY } =
          await loadFixture(setup);

        const now = await time.latest();
        const [start, end] = [now - 100, now + 10000];
        await roles.grantRole(member.address, ROLE_KEY, start, end, 3);
        await roles.setDefaultRole(member.address, ROLE_KEY);
        await roles.allowTargetPacked(ROLE_KEY, testContractAddress, "0x", 0);
        const exec = () =>
          roles
            .connect(member)
            .execTransactionFromModule(testContractAddress, 0, "0x", 0);

        await expect(exec())
          .to.emit(roles, "UpdateRole")
          .withArgs(ROLE_KEY, member.address, start, end, 2);
        await expect(exec())
          .to.emit(roles, "UpdateRole")
          .withArgs(ROLE_KEY, member.address, start, end, 1);
        await expect(exec())
          .to.emit(roles, "RevokeRole")
          .withArgs(ROLE_KEY, member.address)
          .and.not.to.emit(roles, "UpdateRole");

        expect(
          await roles.membershipOf(member.address, ROLE_KEY),
        ).to.deep.equal([false, 0n, 0n, 0n]);
        await expect(exec()).to.be.revertedWithCustomError(
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
          const batch = multisend.interface.encodeFunctionData("multiSend", [
            encodeMultisendPayload(
              Array.from({ length: n }, () => ({
                to: testContractAddress,
                value: 0,
                data: iface.encodeFunctionData("doNothing"),
                operation: 0,
              })),
            ),
          ]);
          return {
            ...fixture,
            multisendAddress: await multisend.getAddress(),
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
          await roles.grantRole(member.address, ROLE_KEY, 0, 0, 3);
          await roles.allowTargetPacked(ROLE_KEY, testContractAddress, "0x", 0);

          const receipt = await (
            await roles
              .connect(member)
              .execTransactionWithRole(multisendAddress, 0, batch, 1, ROLE_KEY)
          ).wait();

          expect(await membershipEvents(roles, receipt)).to.deep.equal([
            "update 2",
          ]);
          expect(
            (await roles.membershipOf(member.address, ROLE_KEY)).usesLeft,
          ).to.equal(2n);
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
          await roles.grantRole(member.address, ROLE_KEY, 0, 0, 1);
          await roles.allowTargetPacked(ROLE_KEY, testContractAddress, "0x", 0);

          const receipt = await (
            await roles
              .connect(member)
              .execTransactionWithRole(multisendAddress, 0, batch, 1, ROLE_KEY)
          ).wait();

          expect(await membershipEvents(roles, receipt)).to.deep.equal([
            "revoke",
          ]);
          await expect(
            roles
              .connect(member)
              .execTransactionWithRole(multisendAddress, 0, batch, 1, ROLE_KEY),
          ).to.be.revertedWithCustomError(roles, "NoMembership");
        });

        it("a refused batch uses nothing", async () => {
          const { roles, member, multisendAddress, batch, ROLE_KEY } =
            await loadFixture(setupBatchOf3);
          // the role has no permission on the batch's target
          await roles.grantRole(member.address, ROLE_KEY, 0, 0, 2);

          await expect(
            roles
              .connect(member)
              .execTransactionWithRole(multisendAddress, 0, batch, 1, ROLE_KEY),
          ).to.be.revertedWithCustomError(roles, "TransactionNotAllowed");
          expect(
            (await roles.membershipOf(member.address, ROLE_KEY)).usesLeft,
          ).to.equal(2n);
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
          await roles.setDefaultRole(member.address, ROLE_KEY);
          await roles.allowTargetPacked(
            ROLE_KEY,
            await roles.getAddress(),
            "0x",
            0,
          );
          await roles.allowTargetPacked(ROLE_KEY, testContractAddress, "0x", 0);
          await roles.transferOwnership(avatarAddress);
          return fixture;
        }

        type Window = [start: number, end: number, uses: number];
        const CASES: {
          what: string;
          before: (now: number) => Window;
          // a new membership granted during execution, or a revocation
          during: (now: number) => Window | "revoke";
          events: (now: number) => string[];
          after: (now: number) => [boolean, bigint, bigint, bigint];
        }[] = [
          {
            what: "revoked",
            before: () => [0, 0, 3],
            during: () => "revoke",
            events: () => ["revoke"],
            after: () => [false, 0n, 0n, 0n],
          },
          {
            what: "revoked on its last use (one RevokeRole)",
            before: () => [0, 0, 1],
            during: () => "revoke",
            events: () => ["revoke"],
            after: () => [false, 0n, 0n, 0n],
          },
          {
            what: "upgraded from finite to unlimited",
            before: () => [0, 0, 2],
            during: () => [0, 0, 0],
            events: () => [`grant ${maxUint128}`],
            after: () => [true, 0n, maxUint64, maxUint128],
          },
          {
            what: "replaced by another finite membership",
            before: (now) => [0, now + 1000, 3],
            during: (now) => [now - 50, now + 5000, 5],
            events: () => ["grant 5", "update 4"],
            after: (now) => [true, BigInt(now - 50), BigInt(now + 5000), 4n],
          },
          {
            what: "downgraded from unlimited to 2 uses",
            before: () => [0, 0, 0],
            during: () => [0, 0, 2],
            events: () => ["grant 2", "update 1"],
            after: () => [true, 0n, maxUint64, 1n],
          },
          {
            what: "downgraded from unlimited to 1 use",
            before: () => [0, 0, 0],
            during: () => [0, 0, 1],
            events: () => ["grant 1", "revoke"],
            after: () => [false, 0n, 0n, 0n],
          },
          {
            what: "reduced from 3 uses to 1",
            before: () => [0, 0, 3],
            during: () => [0, 0, 1],
            events: () => ["grant 1", "revoke"],
            after: () => [false, 0n, 0n, 0n],
          },
        ];

        for (const { what, before, during, events, after } of CASES)
          it(`when ${what}`, async () => {
            const { roles, avatar, member, ROLE_KEY } =
              await loadFixture(setupSelfManaged);
            const now = await time.latest();
            // the avatar owns Roles now: it grants as the owner
            await avatar.exec(
              await roles.getAddress(),
              0,
              roles.interface.encodeFunctionData("grantRole", [
                member.address,
                ROLE_KEY,
                ...before(now),
              ]),
              0,
            );

            const change = during(now);
            const data =
              change === "revoke"
                ? roles.interface.encodeFunctionData("revokeRole", [
                    member.address,
                    ROLE_KEY,
                  ])
                : roles.interface.encodeFunctionData("grantRole", [
                    member.address,
                    ROLE_KEY,
                    ...change,
                  ]);
            const receipt = await (
              await roles
                .connect(member)
                .execTransactionFromModule(await roles.getAddress(), 0, data, 0)
            ).wait();

            expect(await membershipEvents(roles, receipt)).to.deep.equal(
              events(now),
            );
            expect(
              await roles.membershipOf(member.address, ROLE_KEY),
            ).to.deep.equal(after(now));
          });

        it("when the module renounced it", async () => {
          const {
            roles,
            avatar,
            avatarAddress,
            testContractAddress,
            ROLE_KEY,
          } = await loadFixture(setup);
          const rolesAddress = await roles.getAddress();
          // the avatar is the module: the renouncement comes from it
          await roles.grantRole(avatarAddress, ROLE_KEY, 0, 0, 3);
          await roles.setDefaultRole(avatarAddress, ROLE_KEY);
          await roles.allowTargetPacked(ROLE_KEY, rolesAddress, "0x", 0);
          await roles.allowTargetPacked(ROLE_KEY, testContractAddress, "0x", 0);
          const asModule = (to: string, data: string) =>
            avatar.exec(
              rolesAddress,
              0,
              roles.interface.encodeFunctionData("execTransactionFromModule", [
                to,
                0,
                data,
                0,
              ]),
              0,
            );

          await expect(
            asModule(
              rolesAddress,
              roles.interface.encodeFunctionData("renounceRole", [ROLE_KEY]),
            ),
          )
            .to.emit(roles, "RevokeRole")
            .withArgs(ROLE_KEY, avatarAddress)
            .and.to.not.emit(roles, "UpdateRole");

          expect(
            await roles.membershipOf(avatarAddress, ROLE_KEY),
          ).to.deep.equal([false, 0n, 0n, 0n]);
          await expect(
            asModule(testContractAddress, "0x"),
          ).to.be.revertedWithCustomError(roles, "NoMembership");
        });
      });
    });
  });

  describe("membership active", () => {
    it("returns false for zero role key", async () => {
      const { roles, member } = await loadFixture(setup);

      expect((await roles.membershipOf(member.address, ethers.ZeroHash)).active)
        .to.be.false;
    });

    it("returns false when module has no membership", async () => {
      const { roles, member, ROLE_KEY } = await loadFixture(setup);

      expect((await roles.membershipOf(member.address, ROLE_KEY)).active).to.be
        .false;
    });

    it("returns true for active unlimited membership", async () => {
      const { roles, member, ROLE_KEY } = await loadFixture(setup);

      await roles.grantRole(member.address, ROLE_KEY, 0, 0, 0);

      expect((await roles.membershipOf(member.address, ROLE_KEY)).active).to.be
        .true;
    });

    it("returns true for active finite membership", async () => {
      const { roles, member, ROLE_KEY } = await loadFixture(setup);

      await roles.grantRole(member.address, ROLE_KEY, 0, 0, 5);

      expect((await roles.membershipOf(member.address, ROLE_KEY)).active).to.be
        .true;
    });

    it("returns false after membership is revoked", async () => {
      const { roles, member, ROLE_KEY } = await loadFixture(setup);

      await roles.grantRole(member.address, ROLE_KEY, 0, 0, 0);
      expect((await roles.membershipOf(member.address, ROLE_KEY)).active).to.be
        .true;

      await roles.revokeRole(member.address, ROLE_KEY);
      expect((await roles.membershipOf(member.address, ROLE_KEY)).active).to.be
        .false;
    });

    it("returns false before start timestamp", async () => {
      const { roles, member, ROLE_KEY } = await loadFixture(setup);

      const futureStart = (await time.latest()) + 3600;
      await roles.grantRole(member.address, ROLE_KEY, futureStart, 0, 0);

      expect((await roles.membershipOf(member.address, ROLE_KEY)).active).to.be
        .false;
    });

    it("returns true at exactly start timestamp", async () => {
      const { roles, member, ROLE_KEY } = await loadFixture(setup);

      const start = (await time.latest()) + 100;
      await roles.grantRole(member.address, ROLE_KEY, start, 0, 0);

      await time.increaseTo(start);

      expect((await roles.membershipOf(member.address, ROLE_KEY)).active).to.be
        .true;
    });

    it("returns false after end timestamp", async () => {
      const { roles, member, ROLE_KEY } = await loadFixture(setup);

      const end = (await time.latest()) + 100;
      await roles.grantRole(member.address, ROLE_KEY, 0, end, 0);

      await time.increaseTo(end + 1);

      expect((await roles.membershipOf(member.address, ROLE_KEY)).active).to.be
        .false;
    });

    it("returns true at exactly end timestamp", async () => {
      const { roles, member, ROLE_KEY } = await loadFixture(setup);

      const end = (await time.latest()) + 100;
      await roles.grantRole(member.address, ROLE_KEY, 0, end, 0);

      await time.increaseTo(end);

      expect((await roles.membershipOf(member.address, ROLE_KEY)).active).to.be
        .true;
    });

    it("callable by anyone, not just modules", async () => {
      const { roles, member, other, ROLE_KEY } = await loadFixture(setup);

      await roles.grantRole(member.address, ROLE_KEY, 0, 0, 0);

      // other is not a module but can still read membership
      expect(
        (await roles.connect(other).membershipOf(member.address, ROLE_KEY))
          .active,
      ).to.be.true;
    });

    it("returns false for a member whose module was disabled, which cannot execute, keeping its fields", async () => {
      const { roles, member, testContractAddress, ROLE_KEY } =
        await loadFixture(setup);

      await roles.grantRole(member.address, ROLE_KEY, 0, 0, 3);
      await roles.allowTargetPacked(ROLE_KEY, testContractAddress, "0x", 0);
      await roles.disableModule(
        "0x0000000000000000000000000000000000000001",
        member.address,
      );

      expect(await roles.membershipOf(member.address, ROLE_KEY)).to.deep.equal([
        false,
        0n,
        maxUint64,
        3n,
      ]);
      await expect(
        roles
          .connect(member)
          .execTransactionWithRole(testContractAddress, 0, "0x", 0, ROLE_KEY),
      ).to.be.revertedWithCustomError(roles, "NotAuthorized");
    });
  });

  describe("membership fields", () => {
    it("returns zeros when there is no membership", async () => {
      const { roles, member, ROLE_KEY } = await loadFixture(setup);

      expect(await roles.membershipOf(member.address, ROLE_KEY)).to.deep.equal([
        false,
        0n,
        0n,
        0n,
      ]);
    });

    it("returns start, end and uses left as stored", async () => {
      const { roles, member, ROLE_KEY } = await loadFixture(setup);

      await roles.grantRole(member.address, ROLE_KEY, 10, 20, 3);
      expect(await roles.membershipOf(member.address, ROLE_KEY)).to.deep.equal([
        false,
        10n,
        20n,
        3n,
      ]);

      await roles.grantRole(member.address, ROLE_KEY, 0, 0, 0);
      expect(await roles.membershipOf(member.address, ROLE_KEY)).to.deep.equal([
        true,
        0n,
        maxUint64,
        maxUint128,
      ]);
    });
  });
});
