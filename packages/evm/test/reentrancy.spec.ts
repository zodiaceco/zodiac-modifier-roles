import assert from "node:assert/strict";
import { randomBytes } from "node:crypto";
import { after, describe, it } from "node:test";
import { network } from "hardhat";
import {
  decodeFunctionResult,
  encodeFunctionData,
  toFunctionSelector,
  toHex,
} from "viem";
import type { Hex } from "viem";

import { ExecutionOptions, maxUint64 } from "./utils.js";
import { createSetup } from "./setup.js";
import { ENTRYPOINTS, encodeEntrypoint } from "./roleTx.js";
import type { Entrypoint } from "./roleTx.js";

const connection = await network.create();
const { viem, networkHelpers } = connection;
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
    const [owner, invoker] = await viem.getWalletClients();

    const avatar = await viem.deployContract("TestAvatar");
    const roles = await deployRolesMod(
      owner.account.address,
      avatar.address,
      avatar.address,
    );
    const checker = await viem.deployContract("ReentrancyChecker", [
      roles.address,
    ]);
    const roleKey = toHex(randomBytes(32));

    // invoker (the signer) and checker (which sends and relays every call):
    // members with a default role (granting enables them as modules), so
    // that only the reentrancy guard stops the checker's call
    for (const module of [invoker.account.address, checker.address]) {
      await roles.write.grantRole([module, roleKey, 0n, 0n, 0n]);
      await roles.write.setDefaultRole([module, roleKey]);
    }
    await roles.write.allowTargetPacked([
      roleKey,
      checker.address,
      "0x",
      ExecutionOptions.None,
    ]);

    /** Calldata for `entrypoint`, to call `data` on the checker; the signed
     *  one is signed by the invoker, an enabled member module. */
    const encode = (entrypoint: Entrypoint, data: Hex) =>
      encodeEntrypoint(
        roles,
        entrypoint,
        { to: checker.address, data, roleKey },
        invoker,
      );

    /** A call that only passes once the guard is released. */
    const probe = () =>
      encode(
        "execTransactionWithRole",
        encodeFunctionData({ abi: checker.abi, functionName: "probe" }),
      );

    return { roles, checker, invoker, roleKey, encode, probe };
  }

  // The guard is transient storage, which clears at the end of every
  // transaction: whether an entrypoint releases it shows only within the same
  // transaction, so `callTwice` probes right after the outer call.

  for (const outer of ENTRYPOINTS)
    for (const inner of ENTRYPOINTS)
      it(`blocks ${inner} from inside ${outer}, then releases`, async () => {
        const { checker, encode, probe } = await loadFixture(setup);

        await checker.write.setReentry([
          await encode(
            inner,
            encodeFunctionData({ abi: checker.abi, functionName: "doNothing" }),
          ),
        ]);
        await checker.write.callTwice([
          await encode(
            outer,
            encodeFunctionData({ abi: checker.abi, functionName: "attack" }),
          ),
          await probe(),
        ]);

        assert.equal(await checker.read.attackCalled(), true);
        assert.equal(await checker.read.reentered(), false);
        assert.equal(
          await checker.read.reentryResult(),
          toFunctionSelector("Reentrancy()"),
        );
        assert.equal(await checker.read.doNothingCalled(), false);

        assert.equal(await checker.read.secondSucceeded(), true);
        assert.equal(await checker.read.probeCalled(), true);
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
          ? invoker.account.address
          : checker.address;
      await roles.write.grantRole([module, roleKey, 0n, 0n, 3n]);
      await checker.write.setReentry([
        await encode(
          "execTransactionWithRole",
          encodeFunctionData({ abi: checker.abi, functionName: "doNothing" }),
        ),
      ]);

      await viem.assertions.emitWithArgs(
        checker.write.callTwice([
          await encode(
            outer,
            encodeFunctionData({ abi: checker.abi, functionName: "attack" }),
          ),
          "0x",
        ]),
        roles,
        "UpdateRole",
        [roleKey, module, 0n, maxUint64, 2n],
      );
      assert.equal(
        await checker.read.reentryResult(),
        toFunctionSelector("Reentrancy()"),
      );
      assert.equal(await checker.read.doNothingCalled(), false);
      const [, , , usesLeft] = await roles.read.membershipOf([module, roleKey]);
      assert.equal(usesLeft, 2n);
    });

  // The IAvatar entrypoints return false, without reverting, when the call
  // fails: nothing rolls the guard back, so the entrypoint must release it.
  for (const outer of [
    "execTransactionFromModule",
    "execTransactionFromModuleReturnData",
  ] as const)
    it(`${outer} releases the guard when the call fails`, async () => {
      const { roles, checker, encode, probe } = await loadFixture(setup);

      await checker.write.callTwice([
        await encode(
          outer,
          encodeFunctionData({ abi: checker.abi, functionName: "fail" }),
        ),
        await probe(),
      ]);

      // it returned success = false
      const decoded = decodeFunctionResult({
        abi: roles.abi,
        functionName: outer,
        data: await checker.read.firstResult(),
      });
      const success = Array.isArray(decoded) ? decoded[0] : decoded;
      assert.equal(success, false);
      assert.equal(await checker.read.secondSucceeded(), true);
      assert.equal(await checker.read.probeCalled(), true);
    });
});
