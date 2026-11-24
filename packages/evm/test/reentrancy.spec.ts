import { expect } from "chai";
import { network } from "hardhat";

import { ExecutionOptions } from "./utils.js";
import { createSetup } from "./setup.js";

const connection = await network.create();
const { ethers, networkHelpers } = connection;
const { loadFixture } = networkHelpers;
const { deployRolesMod } = createSetup(connection);

/**
 * Reentrancy tests
 *
 * Scope: Reentrancy Protection.
 *
 * This file verifies that every execution entry point in the module is non-reentrant.
 * It ensures that the module prevents nested calls back into itself during an active transaction, protecting against reentrancy attacks.
 */

describe("Reentrancy", () => {
  after(async () => {
    await connection.close();
  });

  async function setup() {
    const [owner, invoker] = await ethers.getSigners();

    const Avatar = await ethers.getContractFactory("TestAvatar");
    const avatar = await Avatar.deploy();
    const avatarAddress = await avatar.getAddress();

    const roles = await deployRolesMod(
      owner.address,
      avatarAddress,
      avatarAddress,
    );

    // Enable invoker as module so it can call execTransactionWithRole
    await roles.connect(owner).enableModule(invoker.address);

    return {
      roles,
      owner,
      invoker,
    };
  }

  it("blocks reentrant call - doNothing is never executed", async () => {
    const { roles, invoker } = await loadFixture(setup);

    const roleKey = ethers.hexlify(ethers.randomBytes(32));

    const ReentrancyChecker =
      await ethers.getContractFactory("ReentrancyChecker");
    const checker = await ReentrancyChecker.deploy(
      await roles.getAddress(),
      roleKey,
    );
    const checkerAddress = await checker.getAddress();

    // Setup: grant role to invoker
    await roles.grantRole(invoker.address, roleKey, 0, 0, 0);

    // Setup: enable checker as module and grant same role so it can callback
    await roles.enableModule(checkerAddress);
    await roles.grantRole(checkerAddress, roleKey, 0, 0, 0);

    await roles.allowTargetPacked(
      roleKey,
      checkerAddress,
      "0x",
      ExecutionOptions.None,
    );

    await roles
      .connect(invoker)
      .execTransactionWithRole(
        checkerAddress,
        0,
        checker.interface.encodeFunctionData("attack"),
        0,
        roleKey,
      );

    // Verify attack() was executed
    expect(await checker.attackCalled()).to.equal(true);

    // Verify the reentrant call was caught with Reentrancy error
    expect(await checker.caughtReentrancy()).to.equal(true);

    // Verify that doNothing was NOT called (reentrancy was blocked)
    expect(await checker.doNothingCalled()).to.equal(false);
  });
});
