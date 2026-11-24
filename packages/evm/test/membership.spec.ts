import { expect } from "chai";
import { Interface } from "ethers";
import { network } from "hardhat";

import { createSetup } from "./setup.js";

const connection = await network.create();
const { ethers, networkHelpers, provider } = connection;
const { loadFixture, time } = networkHelpers;
const { deployRolesMod } = createSetup(connection);

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

const maxUint64 = 2n ** 64n - 1n;
const maxUint128 = 2n ** 128n - 1n;

const iface = new Interface([
  "function doNothing()",
  "function fnThatReverts()",
]);

describe("Membership", () => {
  after(async () => {
    await connection.close();
  });

  async function setup() {
    const [owner, member, , , other] = await ethers.getSigners();

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

      // owner is NOT enabled as a module
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
      describe("unlimited uses", () => {
        it("does not decrement for unlimited uses", async () => {
          const { roles, member, testContractAddress, ROLE_KEY } =
            await loadFixture(setup);

          await roles.grantRole(member.address, ROLE_KEY, 0, 0, 0);
          await roles.setDefaultRole(member.address, ROLE_KEY);
          await roles.allowTargetPacked(ROLE_KEY, testContractAddress, "0x", 0);

          // Execute multiple times - all should succeed
          for (let i = 0; i < 5; i++) {
            await expect(
              roles
                .connect(member)
                .execTransactionFromModule(testContractAddress, 0, "0x", 0),
            ).to.not.be.revert(ethers);
          }
        });

        it("does not emit UpdateRole for unlimited uses", async () => {
          const { roles, member, testContractAddress, ROLE_KEY } =
            await loadFixture(setup);

          await roles.grantRole(member.address, ROLE_KEY, 0, 0, 0);
          await roles.setDefaultRole(member.address, ROLE_KEY);
          await roles.allowTargetPacked(ROLE_KEY, testContractAddress, "0x", 0);

          await expect(
            roles
              .connect(member)
              .execTransactionFromModule(testContractAddress, 0, "0x", 0),
          ).to.not.emit(roles, "UpdateRole");
        });

        it("does not emit RevokeRole for unlimited uses", async () => {
          const { roles, member, testContractAddress, ROLE_KEY } =
            await loadFixture(setup);

          await roles.grantRole(member.address, ROLE_KEY, 0, 0, 0);
          await roles.setDefaultRole(member.address, ROLE_KEY);
          await roles.allowTargetPacked(ROLE_KEY, testContractAddress, "0x", 0);

          await expect(
            roles
              .connect(member)
              .execTransactionFromModule(testContractAddress, 0, "0x", 0),
          ).to.not.emit(roles, "RevokeRole");
        });
      });

      describe("finite uses", () => {
        it("decrements usesLeft on successful execution", async () => {
          const { roles, member, testContractAddress, ROLE_KEY } =
            await loadFixture(setup);

          await roles.grantRole(member.address, ROLE_KEY, 0, 0, 3);
          await roles.setDefaultRole(member.address, ROLE_KEY);
          await roles.allowTargetPacked(ROLE_KEY, testContractAddress, "0x", 0);

          await expect(
            roles
              .connect(member)
              .execTransactionFromModule(testContractAddress, 0, "0x", 0),
          )
            .to.emit(roles, "UpdateRole")
            .withArgs(ROLE_KEY, member.address, 0, maxUint64, 2);
        });

        it("preserves start/end timestamps after decrement", async () => {
          const { roles, member, testContractAddress, ROLE_KEY } =
            await loadFixture(setup);

          const now = await time.latest();
          const start = now - 100;
          const end = now + 10000;

          await roles.grantRole(member.address, ROLE_KEY, start, end, 5);
          await roles.setDefaultRole(member.address, ROLE_KEY);
          await roles.allowTargetPacked(ROLE_KEY, testContractAddress, "0x", 0);

          await expect(
            roles
              .connect(member)
              .execTransactionFromModule(testContractAddress, 0, "0x", 0),
          )
            .to.emit(roles, "UpdateRole")
            .withArgs(ROLE_KEY, member.address, start, end, 4);
        });

        it("does not decrement on failed inner execution", async () => {
          const { roles, member, testContractAddress, ROLE_KEY } =
            await loadFixture(setup);

          await roles.grantRole(member.address, ROLE_KEY, 0, 0, 2);
          await roles.setDefaultRole(member.address, ROLE_KEY);
          await roles.allowTargetPacked(ROLE_KEY, testContractAddress, "0x", 0);

          const revertingData = iface.encodeFunctionData("fnThatReverts");

          // Execute failing call - should not emit UpdateRole (no decrement)
          await expect(
            roles
              .connect(member)
              .execTransactionFromModule(
                testContractAddress,
                0,
                revertingData,
                0,
              ),
          ).to.not.emit(roles, "UpdateRole");

          // First successful call should show 2 -> 1 (proving failed call didn't decrement)
          await expect(
            roles
              .connect(member)
              .execTransactionFromModule(testContractAddress, 0, "0x", 0),
          )
            .to.emit(roles, "UpdateRole")
            .withArgs(ROLE_KEY, member.address, 0, maxUint64, 1);
        });

        it("emits UpdateRole with decremented usesLeft", async () => {
          const { roles, member, testContractAddress, ROLE_KEY } =
            await loadFixture(setup);

          await roles.grantRole(member.address, ROLE_KEY, 0, 0, 5);
          await roles.setDefaultRole(member.address, ROLE_KEY);
          await roles.allowTargetPacked(ROLE_KEY, testContractAddress, "0x", 0);

          // First decrement: 5 -> 4
          await expect(
            roles
              .connect(member)
              .execTransactionFromModule(testContractAddress, 0, "0x", 0),
          )
            .to.emit(roles, "UpdateRole")
            .withArgs(ROLE_KEY, member.address, 0, maxUint64, 4);

          // Second decrement: 4 -> 3
          await expect(
            roles
              .connect(member)
              .execTransactionFromModule(testContractAddress, 0, "0x", 0),
          )
            .to.emit(roles, "UpdateRole")
            .withArgs(ROLE_KEY, member.address, 0, maxUint64, 3);
        });
      });

      describe("exhaustion", () => {
        it("revokes membership when usesLeft reaches 0", async () => {
          const { roles, member, testContractAddress, ROLE_KEY } =
            await loadFixture(setup);

          await roles.grantRole(member.address, ROLE_KEY, 0, 0, 1);
          await roles.setDefaultRole(member.address, ROLE_KEY);
          await roles.allowTargetPacked(ROLE_KEY, testContractAddress, "0x", 0);

          // Use the one use
          await expect(
            roles
              .connect(member)
              .execTransactionFromModule(testContractAddress, 0, "0x", 0),
          ).to.not.be.revert(ethers);

          // Next should fail - membership revoked
          await expect(
            roles
              .connect(member)
              .execTransactionFromModule(testContractAddress, 0, "0x", 0),
          ).to.be.revertedWithCustomError(roles, "NoMembership");
        });

        it("emits RevokeRole when usesLeft reaches 0", async () => {
          const { roles, member, testContractAddress, ROLE_KEY } =
            await loadFixture(setup);

          await roles.grantRole(member.address, ROLE_KEY, 0, 0, 1);
          await roles.setDefaultRole(member.address, ROLE_KEY);
          await roles.allowTargetPacked(ROLE_KEY, testContractAddress, "0x", 0);

          await expect(
            roles
              .connect(member)
              .execTransactionFromModule(testContractAddress, 0, "0x", 0),
          )
            .to.emit(roles, "RevokeRole")
            .withArgs(ROLE_KEY, member.address);
        });

        it("reverts NoMembership on subsequent call after exhaustion", async () => {
          const { roles, member, testContractAddress, ROLE_KEY } =
            await loadFixture(setup);

          await roles.grantRole(member.address, ROLE_KEY, 0, 0, 2);
          await roles.setDefaultRole(member.address, ROLE_KEY);
          await roles.allowTargetPacked(ROLE_KEY, testContractAddress, "0x", 0);

          // Use both uses
          await expect(
            roles
              .connect(member)
              .execTransactionFromModule(testContractAddress, 0, "0x", 0),
          ).to.not.be.revert(ethers);
          await expect(
            roles
              .connect(member)
              .execTransactionFromModule(testContractAddress, 0, "0x", 0),
          ).to.not.be.revert(ethers);

          // Subsequent call should fail
          await expect(
            roles
              .connect(member)
              .execTransactionFromModule(testContractAddress, 0, "0x", 0),
          ).to.be.revertedWithCustomError(roles, "NoMembership");
        });
      });

      describe("membership modified during execution", () => {
        it("does not resurrect membership revoked during execution", async () => {
          const {
            avatar,
            avatarAddress,
            member,
            testContractAddress,
            ROLE_KEY,
          } = await loadFixture(setup);

          const roles = await deployRolesMod(
            avatarAddress,
            avatarAddress,
            avatarAddress,
          );
          const rolesAddress = await roles.getAddress();

          await avatar.exec(
            rolesAddress,
            0,
            roles.interface.encodeFunctionData("grantRole", [
              member.address,
              ROLE_KEY,
              0,
              0,
              3,
            ]),
            0,
          );
          await avatar.exec(
            rolesAddress,
            0,
            roles.interface.encodeFunctionData("setDefaultRole", [
              member.address,
              ROLE_KEY,
            ]),
            0,
          );
          await avatar.exec(
            rolesAddress,
            0,
            roles.interface.encodeFunctionData("allowTargetPacked", [
              ROLE_KEY,
              rolesAddress,
              "0x",
              0,
            ]),
            0,
          );
          await avatar.exec(
            rolesAddress,
            0,
            roles.interface.encodeFunctionData("allowTargetPacked", [
              ROLE_KEY,
              testContractAddress,
              "0x",
              0,
            ]),
            0,
          );

          const revokeData = roles.interface.encodeFunctionData("revokeRole", [
            member.address,
            ROLE_KEY,
          ]);

          await expect(
            roles
              .connect(member)
              .execTransactionFromModule(rolesAddress, 0, revokeData, 0),
          )
            .to.emit(roles, "RevokeRole")
            .withArgs(ROLE_KEY, member.address)
            .and.to.not.emit(roles, "UpdateRole");

          expect((await roles.membershipOf(member.address, ROLE_KEY)).active).to
            .be.false;

          await expect(
            roles
              .connect(member)
              .execTransactionFromModule(testContractAddress, 0, "0x", 0),
          ).to.be.revertedWithCustomError(roles, "NoMembership");
        });

        it("does not emit duplicate RevokeRole when last use is revoked during execution", async () => {
          const { avatar, avatarAddress, member, ROLE_KEY } =
            await loadFixture(setup);

          const roles = await deployRolesMod(
            avatarAddress,
            avatarAddress,
            avatarAddress,
          );
          const rolesAddress = await roles.getAddress();

          await avatar.exec(
            rolesAddress,
            0,
            roles.interface.encodeFunctionData("grantRole", [
              member.address,
              ROLE_KEY,
              0,
              0,
              1,
            ]),
            0,
          );
          await avatar.exec(
            rolesAddress,
            0,
            roles.interface.encodeFunctionData("setDefaultRole", [
              member.address,
              ROLE_KEY,
            ]),
            0,
          );
          await avatar.exec(
            rolesAddress,
            0,
            roles.interface.encodeFunctionData("allowTargetPacked", [
              ROLE_KEY,
              rolesAddress,
              "0x",
              0,
            ]),
            0,
          );

          const revokeData = roles.interface.encodeFunctionData("revokeRole", [
            member.address,
            ROLE_KEY,
          ]);

          const tx = await roles
            .connect(member)
            .execTransactionFromModule(rolesAddress, 0, revokeData, 0);
          const receipt = await tx.wait();
          const revokeEvents = receipt!.logs
            .map((log) => {
              try {
                return roles.interface.parseLog(log);
              } catch {
                return null;
              }
            })
            .filter((parsed) => parsed?.name === "RevokeRole");

          expect(revokeEvents).to.have.lengthOf(1);
          expect((await roles.membershipOf(member.address, ROLE_KEY)).active).to
            .be.false;
        });

        it("does not resurrect membership renounced during execution", async () => {
          const {
            roles,
            avatar,
            avatarAddress,
            testContractAddress,
            ROLE_KEY,
          } = await loadFixture(setup);
          const rolesAddress = await roles.getAddress();

          await roles.grantRole(avatarAddress, ROLE_KEY, 0, 0, 3);
          await roles.setDefaultRole(avatarAddress, ROLE_KEY);
          await roles.allowTargetPacked(ROLE_KEY, rolesAddress, "0x", 0);
          await roles.allowTargetPacked(ROLE_KEY, testContractAddress, "0x", 0);

          const renounceData = roles.interface.encodeFunctionData(
            "renounceRole",
            [ROLE_KEY],
          );
          const execData = roles.interface.encodeFunctionData(
            "execTransactionFromModule",
            [rolesAddress, 0, renounceData, 0],
          );

          await expect(avatar.exec(rolesAddress, 0, execData, 0))
            .to.emit(roles, "RevokeRole")
            .withArgs(ROLE_KEY, avatarAddress)
            .and.to.not.emit(roles, "UpdateRole");

          expect((await roles.membershipOf(avatarAddress, ROLE_KEY)).active).to
            .be.false;

          const followUpExec = roles.interface.encodeFunctionData(
            "execTransactionFromModule",
            [testContractAddress, 0, "0x", 0],
          );
          await expect(
            avatar.exec(rolesAddress, 0, followUpExec, 0),
          ).to.be.revertedWithCustomError(roles, "NoMembership");
        });

        it("does not overwrite an upgrade to unlimited uses during execution", async () => {
          const {
            avatar,
            avatarAddress,
            member,
            testContractAddress,
            ROLE_KEY,
          } = await loadFixture(setup);

          const roles = await deployRolesMod(
            avatarAddress,
            avatarAddress,
            avatarAddress,
          );
          const rolesAddress = await roles.getAddress();

          await avatar.exec(
            rolesAddress,
            0,
            roles.interface.encodeFunctionData("grantRole", [
              member.address,
              ROLE_KEY,
              0,
              0,
              2,
            ]),
            0,
          );
          await avatar.exec(
            rolesAddress,
            0,
            roles.interface.encodeFunctionData("setDefaultRole", [
              member.address,
              ROLE_KEY,
            ]),
            0,
          );
          await avatar.exec(
            rolesAddress,
            0,
            roles.interface.encodeFunctionData("allowTargetPacked", [
              ROLE_KEY,
              rolesAddress,
              "0x",
              0,
            ]),
            0,
          );
          await avatar.exec(
            rolesAddress,
            0,
            roles.interface.encodeFunctionData("allowTargetPacked", [
              ROLE_KEY,
              testContractAddress,
              "0x",
              0,
            ]),
            0,
          );

          const upgradeData = roles.interface.encodeFunctionData("grantRole", [
            member.address,
            ROLE_KEY,
            0,
            0,
            0,
          ]);

          await expect(
            roles
              .connect(member)
              .execTransactionFromModule(rolesAddress, 0, upgradeData, 0),
          ).to.not.emit(roles, "UpdateRole");

          // Should now be unlimited: more than 2 follow-up calls succeed
          for (let i = 0; i < 3; i++) {
            await expect(
              roles
                .connect(member)
                .execTransactionFromModule(testContractAddress, 0, "0x", 0),
            ).to.not.emit(roles, "UpdateRole");
          }
          expect((await roles.membershipOf(member.address, ROLE_KEY)).active).to
            .be.true;
        });

        it("decrements updated finite membership instead of writing stale pre-execution state", async () => {
          const { avatar, avatarAddress, member, ROLE_KEY } =
            await loadFixture(setup);

          const roles = await deployRolesMod(
            avatarAddress,
            avatarAddress,
            avatarAddress,
          );
          const rolesAddress = await roles.getAddress();

          const now = await time.latest();
          const oldEnd = now + 1000;
          const newStart = now - 50;
          const newEnd = now + 5000;

          await avatar.exec(
            rolesAddress,
            0,
            roles.interface.encodeFunctionData("grantRole", [
              member.address,
              ROLE_KEY,
              0,
              oldEnd,
              3,
            ]),
            0,
          );
          await avatar.exec(
            rolesAddress,
            0,
            roles.interface.encodeFunctionData("setDefaultRole", [
              member.address,
              ROLE_KEY,
            ]),
            0,
          );
          await avatar.exec(
            rolesAddress,
            0,
            roles.interface.encodeFunctionData("allowTargetPacked", [
              ROLE_KEY,
              rolesAddress,
              "0x",
              0,
            ]),
            0,
          );

          const updateData = roles.interface.encodeFunctionData("grantRole", [
            member.address,
            ROLE_KEY,
            newStart,
            newEnd,
            5,
          ]);

          await expect(
            roles
              .connect(member)
              .execTransactionFromModule(rolesAddress, 0, updateData, 0),
          )
            .to.emit(roles, "UpdateRole")
            .withArgs(ROLE_KEY, member.address, newStart, newEnd, 4);
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

      await time.setNextBlockTimestamp(end);
      // Mine a block so time.latest() reflects the new timestamp
      await provider.request({ method: "evm_mine" });

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

    it("returns false for a member whose module was disabled", async () => {
      const { roles, member, ROLE_KEY } = await loadFixture(setup);

      await roles.grantRole(member.address, ROLE_KEY, 0, 0, 0);
      await roles.disableModule(
        "0x0000000000000000000000000000000000000001",
        member.address,
      );

      expect((await roles.membershipOf(member.address, ROLE_KEY)).active).to.be
        .false;
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
