import { expect } from "chai";
import type { Interface } from "ethers";
import { network } from "hardhat";

import { ExecutionOptions, maxUint64 } from "./utils.js";
import { createSetup } from "./setup.js";
import { ENTRYPOINTS, encodeEntrypoint } from "./roleTx.js";
import type { Entrypoint } from "./roleTx.js";

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
 * From inside a call executed through any of the four entry points, a call back into
 * any of the four reverts with `Reentrancy`, even though the caller is an enabled
 * member module whose call would otherwise be authorized. The guard is released
 * afterwards.
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
    const rolesAddress = await roles.getAddress();

    const ReentrancyChecker =
      await ethers.getContractFactory("ReentrancyChecker");
    const checker = await ReentrancyChecker.deploy(rolesAddress);
    const checkerAddress = await checker.getAddress();

    const roleKey = ethers.hexlify(ethers.randomBytes(32));

    // invoker (the signer) and checker (which sends and relays every call):
    // members with a default role (granting enables them as modules), so
    // that only the reentrancy guard stops the checker's call
    for (const module of [invoker.address, checkerAddress]) {
      await roles.grantRole(module, roleKey, 0, 0, 0);
      await roles.setDefaultRole(module, roleKey);
    }
    await roles.allowTargetPacked(
      roleKey,
      checkerAddress,
      "0x",
      ExecutionOptions.None,
    );

    /** Calldata for `entrypoint`, to call `data` on the checker; the signed
     *  one is signed by the invoker, an enabled member module. */
    const encode = (entrypoint: Entrypoint, data: string) =>
      encodeEntrypoint(
        roles,
        entrypoint,
        { to: checkerAddress, data, roleKey },
        invoker,
      );

    /** A call that only passes once the guard is released. */
    const probe = () =>
      encode(
        "execTransactionWithRole",
        checker.interface.encodeFunctionData("probe"),
      );

    return { roles, checker, invoker, roleKey, encode, probe };
  }

  // The guard is transient storage, which clears at the end of every
  // transaction: whether an entrypoint releases it shows only within the same
  // transaction, so `callTwice` probes right after the outer call.

  for (const outer of ENTRYPOINTS)
    for (const inner of ENTRYPOINTS)
      it(`blocks ${inner} from inside ${outer}, then releases`, async () => {
        const { roles, checker, encode, probe } = await loadFixture(setup);

        await checker.setReentry(
          await encode(
            inner,
            checker.interface.encodeFunctionData("doNothing"),
          ),
        );
        await checker.callTwice(
          await encode(outer, checker.interface.encodeFunctionData("attack")),
          await probe(),
        );

        expect(await checker.attackCalled()).to.equal(true);
        expect(await checker.reentered()).to.equal(false);
        expect(await checker.reentryResult()).to.equal(
          roles.interface.getError("Reentrancy")!.selector,
        );
        expect(await checker.doNothingCalled()).to.equal(false);

        expect(await checker.secondSucceeded()).to.equal(true);
        expect(await checker.probeCalled()).to.equal(true);
      });

  // The target catches the refused reentry and returns normally: the outer
  // execution settles as usual, and the blocked call left nothing behind.
  for (const outer of ENTRYPOINTS)
    it(`${outer} settles normally when the target catches the refused reentry`, async () => {
      const { roles, checker, invoker, roleKey, encode } =
        await loadFixture(setup);
      // the outer call is attributed to its signer, or else its sender
      const module =
        outer === "execTransactionWithRoleSigned"
          ? invoker.address
          : await checker.getAddress();
      await roles.grantRole(module, roleKey, 0, 0, 3);
      await checker.setReentry(
        await encode(
          "execTransactionWithRole",
          checker.interface.encodeFunctionData("doNothing"),
        ),
      );

      await expect(
        checker.callTwice(
          await encode(outer, checker.interface.encodeFunctionData("attack")),
          "0x",
        ),
      )
        .to.emit(roles, "UpdateRole")
        .withArgs(roleKey, module, 0, maxUint64, 2);
      expect(await checker.reentryResult()).to.equal(
        roles.interface.getError("Reentrancy")!.selector,
      );
      expect(await checker.doNothingCalled()).to.equal(false);
      expect((await roles.membershipOf(module, roleKey)).usesLeft).to.equal(2);
    });

  // The IAvatar entrypoints return false, without reverting, when the call
  // fails: nothing rolls the guard back, so the entrypoint must release it.
  for (const outer of [
    "execTransactionFromModule",
    "execTransactionFromModuleReturnData",
  ] as const)
    it(`${outer} releases the guard when the call fails`, async () => {
      const { roles, checker, encode, probe } = await loadFixture(setup);

      await checker.callTwice(
        await encode(outer, checker.interface.encodeFunctionData("fail")),
        await probe(),
      );

      // it returned success = false
      const [success] = (roles.interface as Interface).decodeFunctionResult(
        outer,
        await checker.firstResult(),
      );
      expect(success).to.equal(false);
      expect(await checker.secondSucceeded()).to.equal(true);
      expect(await checker.probeCalled()).to.equal(true);
    });
});
