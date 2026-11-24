import assert from "node:assert/strict";
import { randomBytes } from "node:crypto";
import { after, describe, it } from "node:test";
import { network } from "hardhat";
import {
  decodeFunctionResult,
  encodeErrorResult,
  encodeFunctionData,
  hashTypedData,
  keccak256,
  parseAbi,
  toBytes,
  toFunctionSelector,
  toHex,
  zeroHash,
} from "viem";
import type { Hex } from "viem";

import {
  Encoding,
  ExecutionOptions,
  Operator,
  packConditions,
  maxUint64,
  assertNotEmitted,
} from "./utils.js";
import { createSetup } from "./setup.js";
import {
  ENTRYPOINTS,
  NO_DEADLINE,
  ROLE_TX_TYPES,
  encodeEntrypoint,
} from "./roleTx.js";
import type { Entrypoint, RoleTx } from "./roleTx.js";

const connection = await network.create();
const { viem, networkHelpers } = connection;
const { loadFixture, time } = networkHelpers;
const { deployRolesMod } = createSetup(connection);

const abi = parseAbi([
  "function fnThatMaybeReverts(uint256, bool) returns (uint256)",
  "function revertWith(bytes)",
  "function anything()",
]);

/**
 * Execution Mechanics tests
 *
 * Scope: Transaction Execution Lifecycle.
 *
 * This file verifies the behavior of the module's execution entry points:
 * - Return Values: Ensuring success/failure flags and return data are propagated correctly.
 * - Error Handling: Verifying that failed inner transactions result in the expected outcome
 *   (success=false on IAvatar entrypoints; bubbling inner revert data on Roles-native entrypoints).
 * - State Persistence: Confirming that side-effects (e.g., allowance consumption, consumed digests)
 *   are committed on success and discarded on failure.
 *
 * Covers `execTransactionFromModule`, `execTransactionFromModuleReturnData`,
 * `execTransactionWithRole`, and `execTransactionWithRoleSigned`.
 */

describe("Execution Mechanics", () => {
  after(async () => {
    await connection.close();
  });

  async function setup() {
    const [owner, invoker] = await viem.getWalletClients();

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

    // Grant role (which enables the invoker as a module)
    await roles.write.grantRole([
      invoker.account.address,
      ROLE_KEY,
      0n,
      0n,
      0n,
    ]);

    // Set as default role (for FromModule calls)
    await roles.write.setDefaultRole([invoker.account.address, ROLE_KEY]);

    // Set initial allowance: 1000
    await roles.write.setAllowance([ALLOWANCE_KEY, 1000n, 0n, 0n, 0n, 0n]);

    // Scope target
    await roles.write.scopeTarget([ROLE_KEY, testContractAddress]);

    // Allow the test function: fnThatMaybeReverts(uint256, bool)
    // We attach a WithinAllowance condition to track consumption.
    const packed = await packConditions(roles, [
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
        compValue: ALLOWANCE_KEY,
      },
      {
        parent: 0,
        paramType: Encoding.Static,
        operator: Operator.Pass,
        compValue: "0x",
      },
    ]);
    await roles.write.allowFunctionPacked([
      ROLE_KEY,
      testContractAddress,
      toFunctionSelector("fnThatMaybeReverts(uint256, bool)"),
      packed,
      ExecutionOptions.None,
    ]);
    await roles.write.allowFunctionPacked([
      ROLE_KEY,
      testContractAddress,
      toFunctionSelector("revertWith(bytes)"),
      "0x",
      ExecutionOptions.None,
    ]);
    // a function that may send value and be delegatecalled
    await roles.write.allowFunctionPacked([
      ROLE_KEY,
      testContractAddress,
      toFunctionSelector("anything()"),
      "0x",
      ExecutionOptions.Both,
    ]);
    await owner.sendTransaction({ to: avatarAddress, value: 1000n });

    return {
      roles,
      owner,
      invoker,
      avatarAddress,
      testContract,
      testContractAddress,
      ROLE_KEY,
      ALLOWANCE_KEY,
    };
  }

  describe("execTransactionFromModule", () => {
    it("returns success=true and persists consumption on successful execution", async () => {
      const { roles, invoker, testContractAddress, ALLOWANCE_KEY } =
        await loadFixture(setup);

      // Consumes 100
      const calldata = encodeFunctionData({
        abi,
        functionName: "fnThatMaybeReverts",
        args: [100n, false],
      });

      const { result: success } =
        await roles.simulate.execTransactionFromModule(
          [testContractAddress, 0n, calldata, 0],
          { account: invoker.account.address },
        );

      assert.equal(success, true);

      await roles.write.execTransactionFromModule(
        [testContractAddress, 0n, calldata, 0],
        { account: invoker.account },
      );

      // Verify persistence: 1000 - 100 = 900
      const [balance] = await roles.read.accruedAllowance([ALLOWANCE_KEY]);
      assert.equal(balance, 900n);
    });

    it("returns success=false and does not persist consumption on failed inner execution", async () => {
      const { roles, invoker, testContractAddress, ALLOWANCE_KEY } =
        await loadFixture(setup);

      // Consumes 100 but reverts
      const calldata = encodeFunctionData({
        abi,
        functionName: "fnThatMaybeReverts",
        args: [100n, true],
      });

      const { result: success } =
        await roles.simulate.execTransactionFromModule(
          [testContractAddress, 0n, calldata, 0],
          { account: invoker.account.address },
        );

      assert.equal(success, false);

      await roles.write.execTransactionFromModule(
        [testContractAddress, 0n, calldata, 0],
        { account: invoker.account },
      );

      // Verify rollback: 1000 (unchanged)
      const [balance] = await roles.read.accruedAllowance([ALLOWANCE_KEY]);
      assert.equal(balance, 1000n);
    });
  });

  describe("execTransactionFromModuleReturnData", () => {
    it("returns success=true, returnData, and persists consumption on successful execution", async () => {
      const { roles, invoker, testContractAddress, ALLOWANCE_KEY } =
        await loadFixture(setup);

      const calldata = encodeFunctionData({
        abi,
        functionName: "fnThatMaybeReverts",
        args: [100n, false],
      });

      const {
        result: [success, returnData],
      } = await roles.simulate.execTransactionFromModuleReturnData(
        [testContractAddress, 0n, calldata, 0],
        { account: invoker.account.address },
      );

      assert.equal(success, true);
      assert.equal(
        decodeFunctionResult({
          abi,
          functionName: "fnThatMaybeReverts",
          data: returnData,
        }),
        100n,
      );

      await roles.write.execTransactionFromModuleReturnData(
        [testContractAddress, 0n, calldata, 0],
        { account: invoker.account },
      );

      const [balance] = await roles.read.accruedAllowance([ALLOWANCE_KEY]);
      assert.equal(balance, 900n);
    });

    it("returns success=false, revert data, and does not persist consumption on failed inner execution", async () => {
      const { roles, invoker, testContractAddress, ALLOWANCE_KEY } =
        await loadFixture(setup);

      const calldata = encodeFunctionData({
        abi,
        functionName: "fnThatMaybeReverts",
        args: [100n, true],
      });

      const {
        result: [success, returnData],
      } = await roles.simulate.execTransactionFromModuleReturnData(
        [testContractAddress, 0n, calldata, 0],
        { account: invoker.account.address },
      );

      assert.equal(success, false);
      assert.equal(returnData, toFunctionSelector("AnError()"));

      await roles.write.execTransactionFromModuleReturnData(
        [testContractAddress, 0n, calldata, 0],
        { account: invoker.account },
      );

      const [balance] = await roles.read.accruedAllowance([ALLOWANCE_KEY]);
      assert.equal(balance, 1000n);
    });
  });

  describe("execTransactionWithRole", () => {
    it("succeeds, returns returnData, and persists consumption when using correct role", async () => {
      const { roles, invoker, testContractAddress, ROLE_KEY, ALLOWANCE_KEY } =
        await loadFixture(setup);
      const calldata = encodeFunctionData({
        abi,
        functionName: "fnThatMaybeReverts",
        args: [100n, false],
      });

      const { result: returnData } =
        await roles.simulate.execTransactionWithRole(
          [testContractAddress, 0n, calldata, 0, ROLE_KEY],
          { account: invoker.account.address },
        );

      assert.equal(
        decodeFunctionResult({
          abi,
          functionName: "fnThatMaybeReverts",
          data: returnData,
        }),
        100n,
      );

      await roles.write.execTransactionWithRole(
        [testContractAddress, 0n, calldata, 0, ROLE_KEY],
        { account: invoker.account },
      );

      const [balance] = await roles.read.accruedAllowance([ALLOWANCE_KEY]);
      assert.equal(balance, 900n);
    });

    it("reverts when using unassigned role", async () => {
      const { roles, invoker, testContractAddress } = await loadFixture(setup);
      const calldata = encodeFunctionData({
        abi,
        functionName: "fnThatMaybeReverts",
        args: [100n, false],
      });
      const BAD_ROLE = keccak256(toBytes("BAD_ROLE"));

      await viem.assertions.revertWithCustomError(
        roles.write.execTransactionWithRole(
          [testContractAddress, 0n, calldata, 0, BAD_ROLE],
          { account: invoker.account },
        ),
        roles,
        "NoMembership",
      );
    });

    it("reverts with ModuleTransactionFailed carrying the inner error and does not persist consumption on failed inner execution", async () => {
      const {
        roles,
        invoker,
        testContract,
        testContractAddress,
        ROLE_KEY,
        ALLOWANCE_KEY,
      } = await loadFixture(setup);
      const calldata = encodeFunctionData({
        abi,
        functionName: "fnThatMaybeReverts",
        args: [100n, true],
      });

      await viem.assertions.revertWithCustomErrorWithArgs(
        roles.write.execTransactionWithRole(
          [testContractAddress, 0n, calldata, 0, ROLE_KEY],
          { account: invoker.account },
        ),
        roles,
        "ModuleTransactionFailed",
        [encodeErrorResult({ abi: testContract.abi, errorName: "AnError" })],
      );

      const [balance] = await roles.read.accruedAllowance([ALLOWANCE_KEY]);
      assert.equal(balance, 1000n);
    });

    it("reverts with empty ModuleTransactionFailed when inner execution reverts without data", async () => {
      const { roles, invoker, testContractAddress, ROLE_KEY } =
        await loadFixture(setup);
      const calldata = encodeFunctionData({
        abi,
        functionName: "revertWith",
        args: ["0x"],
      });

      await viem.assertions.revertWithCustomErrorWithArgs(
        roles.write.execTransactionWithRole(
          [testContractAddress, 0n, calldata, 0, ROLE_KEY],
          { account: invoker.account },
        ),
        roles,
        "ModuleTransactionFailed",
        ["0x"],
      );
    });

    for (const [what, revertData] of [
      [
        "a custom error with arguments",
        encodeErrorResult({
          abi: parseAbi(["error AnErrorWithArgs(uint256, string)"]),
          errorName: "AnErrorWithArgs",
          args: [42n, "a reason longer than one word, to span two"],
        }),
      ],
      [
        "a revert string",
        encodeErrorResult({
          abi: parseAbi(["error Error(string)"]),
          errorName: "Error",
          args: ["a revert string longer than one 32-byte word"],
        }),
      ],
    ] as const)
      it(`carries ${what} in ModuleTransactionFailed verbatim`, async () => {
        const { roles, invoker, testContractAddress, ROLE_KEY } =
          await loadFixture(setup);
        const calldata = encodeFunctionData({
          abi,
          functionName: "revertWith",
          args: [revertData],
        });

        await viem.assertions.revertWithCustomErrorWithArgs(
          roles.write.execTransactionWithRole(
            [testContractAddress, 0n, calldata, 0, ROLE_KEY],
            { account: invoker.account },
          ),
          roles,
          "ModuleTransactionFailed",
          [revertData],
        );
      });
  });

  // The signed entrypoint's fixture, which the tests across entrypoints
  // share: a relayer sends what the invoker signs.
  async function signedSetup() {
    const fixture = await setup();
    const [, , relayer, stranger] = await viem.getWalletClients();
    // another role of the invoker that would authorize the same call
    const OTHER_ROLE = keccak256(toBytes("OTHER_ROLE"));
    await fixture.roles.write.grantRole([
      fixture.invoker.account.address,
      OTHER_ROLE,
      0n,
      0n,
      0n,
    ]);
    await fixture.roles.write.allowTargetPacked([
      OTHER_ROLE,
      fixture.testContractAddress,
      "0x",
      ExecutionOptions.None,
    ]);
    return { ...fixture, relayer, stranger, OTHER_ROLE };
  }
  type Fixture = Awaited<ReturnType<typeof signedSetup>>;

  /** A RoleTx spending 100 of the allowance, as `overrides` change it,
   *  signed by `signer`. */
  async function signedTx(
    fixture: Fixture,
    overrides: Partial<RoleTx> = {},
    signer: Fixture["invoker"] = fixture.invoker,
  ) {
    const { roles, testContractAddress, ROLE_KEY } = fixture;
    const domain = {
      chainId: await signer.getChainId(),
      verifyingContract: roles.address,
    };
    const roleTx: RoleTx = {
      to: testContractAddress,
      value: 0n,
      data: encodeFunctionData({
        abi,
        functionName: "fnThatMaybeReverts",
        args: [100n, false],
      }),
      operation: 0,
      roleKey: ROLE_KEY,
      salt: toHex(randomBytes(32)),
      deadline: NO_DEADLINE,
      ...overrides,
    };
    return {
      roleTx,
      hash: hashTypedData({
        domain,
        types: ROLE_TX_TYPES,
        primaryType: "RoleTx",
        message: roleTx,
      }),
      signature: await signer.signTypedData({
        account: signer.account,
        domain,
        types: ROLE_TX_TYPES,
        primaryType: "RoleTx",
        message: roleTx,
      }),
    };
  }

  describe("execTransactionWithRoleSigned", () => {
    it("executes, returns returnData, and persists consumption when signed by an enabled module", async () => {
      const fixture = await loadFixture(signedSetup);
      const { roles, relayer, ALLOWANCE_KEY } = fixture;
      const { roleTx, hash, signature } = await signedTx(fixture);

      const { result: returnData } =
        await roles.simulate.execTransactionWithRoleSigned(
          [roleTx, signature],
          { account: relayer.account.address },
        );
      assert.equal(
        decodeFunctionResult({
          abi,
          functionName: "fnThatMaybeReverts",
          data: returnData,
        }),
        100n,
      );

      await viem.assertions.emitWithArgs(
        roles.write.execTransactionWithRoleSigned([roleTx, signature], {
          account: relayer.account,
        }),
        roles,
        "HashExecuted",
        [hash],
      );
      assert.equal(
        (await roles.read.accruedAllowance([ALLOWANCE_KEY]))[0],
        900n,
      );
    });

    it("reverts NotAuthorized when signer is not an enabled module", async () => {
      const fixture = await loadFixture(signedSetup);
      const { roles, relayer } = fixture;
      const { roleTx, signature } = await signedTx(fixture, {}, relayer);

      await viem.assertions.revertWithCustomError(
        roles.write.execTransactionWithRoleSigned([roleTx, signature], {
          account: relayer.account,
        }),
        roles,
        "NotAuthorized",
      );
    });

    it("reverts HashAlreadyConsumed when the same signature is replayed", async () => {
      const fixture = await loadFixture(signedSetup);
      const { roles, relayer } = fixture;
      const { roleTx, hash, signature } = await signedTx(fixture);

      await roles.write.execTransactionWithRoleSigned([roleTx, signature], {
        account: relayer.account,
      });
      await viem.assertions.revertWithCustomErrorWithArgs(
        roles.write.execTransactionWithRoleSigned([roleTx, signature], {
          account: relayer.account,
        }),
        roles,
        "HashAlreadyConsumed",
        [hash],
      );
    });

    describe("binds the signature to every field and the instance", () => {
      // the signature no longer recovers to the invoker: NotAuthorized,
      // before any membership or permission is looked at
      const TAMPERED: Record<string, (f: Fixture) => Partial<RoleTx>> = {
        to: (f) => ({ to: f.avatarAddress }),
        value: () => ({ value: 1n }),
        data: () => ({
          data: encodeFunctionData({
            abi,
            functionName: "fnThatMaybeReverts",
            args: [1n, false],
          }),
        }),
        operation: () => ({ operation: 1 }),
        roleKey: (f) => ({ roleKey: f.OTHER_ROLE }),
        salt: () => ({ salt: toHex(randomBytes(32)) }),
        deadline: () => ({ deadline: NO_DEADLINE - 1n }),
      };

      for (const [field, tamper] of Object.entries(TAMPERED))
        it(`rejects a changed ${field}, then executes what was signed`, async () => {
          const fixture = await loadFixture(signedSetup);
          const { roles, invoker, relayer } = fixture;
          const { roleTx, hash, signature } = await signedTx(fixture);

          await viem.assertions.revertWithCustomError(
            roles.write.execTransactionWithRoleSigned(
              [{ ...roleTx, ...tamper(fixture) }, signature],
              { account: relayer.account },
            ),
            roles,
            "NotAuthorized",
          );

          await roles.write.execTransactionWithRoleSigned([roleTx, signature], {
            account: relayer.account,
          });
          assert.equal(
            await roles.read.consumed([invoker.account.address, hash]),
            true,
          );
        });

      it("rejects a signature for another Roles instance (verifyingContract)", async () => {
        const fixture = await loadFixture(signedSetup);
        const {
          owner,
          invoker,
          relayer,
          avatarAddress,
          testContractAddress,
          ROLE_KEY,
        } = fixture;
        // the same invoker, membership and permission on a second instance
        const other = await deployRolesMod(
          owner.account.address,
          avatarAddress,
          avatarAddress,
        );
        await other.write.grantRole([
          invoker.account.address,
          ROLE_KEY,
          0n,
          0n,
          0n,
        ]);
        await other.write.allowTargetPacked([
          ROLE_KEY,
          testContractAddress,
          "0x",
          ExecutionOptions.None,
        ]);
        const { roleTx, signature } = await signedTx(fixture);

        await viem.assertions.revertWithCustomError(
          other.write.execTransactionWithRoleSigned([roleTx, signature], {
            account: relayer.account,
          }),
          other,
          "NotAuthorized",
        );
      });
    });

    it("reverts with ModuleTransactionFailed and rolls back digest consumption on failed inner execution", async () => {
      const fixture = await loadFixture(signedSetup);
      const { roles, invoker, relayer, testContract, ALLOWANCE_KEY } = fixture;

      for (const [data, revertData] of [
        [
          encodeFunctionData({
            abi,
            functionName: "fnThatMaybeReverts",
            args: [100n, true],
          }),
          encodeErrorResult({ abi: testContract.abi, errorName: "AnError" }),
        ],
        [
          encodeFunctionData({
            abi,
            functionName: "revertWith",
            args: ["0x"],
          }),
          "0x" as Hex,
        ],
      ] as const) {
        const { roleTx, hash, signature } = await signedTx(fixture, { data });

        await viem.assertions.revertWithCustomErrorWithArgs(
          roles.write.execTransactionWithRoleSigned([roleTx, signature], {
            account: relayer.account,
          }),
          roles,
          "ModuleTransactionFailed",
          [revertData],
        );
        assert.equal(
          await roles.read.consumed([invoker.account.address, hash]),
          false,
        );
      }
      assert.equal(
        (await roles.read.accruedAllowance([ALLOWANCE_KEY]))[0],
        1000n,
      );
    });

    describe("deadline", () => {
      it("executes at the deadline, and after it reverts SignatureExpired leaving the digest unconsumed", async () => {
        const fixture = await loadFixture(signedSetup);
        const { roles, invoker, relayer } = fixture;
        const deadline = BigInt(await time.latest()) + 100n;
        const onTime = await signedTx(fixture, { deadline });
        const late = await signedTx(fixture, { deadline });

        await time.setNextBlockTimestamp(deadline);
        await roles.write.execTransactionWithRoleSigned(
          [onTime.roleTx, onTime.signature],
          { account: relayer.account },
        );

        await time.setNextBlockTimestamp(deadline + 1n);
        await viem.assertions.revertWithCustomError(
          roles.write.execTransactionWithRoleSigned(
            [late.roleTx, late.signature],
            { account: relayer.account },
          ),
          roles,
          "SignatureExpired",
        );
        assert.equal(
          await roles.read.consumed([invoker.account.address, late.hash]),
          false,
        );
      });

      it("treats deadline 0 as always expired", async () => {
        const fixture = await loadFixture(signedSetup);
        const { roles, relayer } = fixture;
        const { roleTx, signature } = await signedTx(fixture, { deadline: 0n });

        await viem.assertions.revertWithCustomError(
          roles.write.execTransactionWithRoleSigned([roleTx, signature], {
            account: relayer.account,
          }),
          roles,
          "SignatureExpired",
        );
      });

      // The signature is checked first (moduleOnlySigned), then the
      // deadline, then the membership.
      const PRECEDENCE: {
        expired: string;
        error: "NotAuthorized" | "HashAlreadyConsumed" | "SignatureExpired";
        arrange: (f: Fixture) => Promise<{
          signer: Fixture["invoker"];
          beforeSending?: (hash: Hex) => Promise<Hex>;
        }>;
      }[] = [
        {
          expired: "signed by a non-module",
          error: "NotAuthorized",
          arrange: async ({ relayer }) => ({ signer: relayer }),
        },
        {
          expired: "whose digest was invalidated",
          error: "HashAlreadyConsumed",
          arrange: async ({ roles, invoker }) => ({
            signer: invoker,
            beforeSending: (hash) =>
              roles.write.invalidate([hash], { account: invoker.account }),
          }),
        },
        {
          expired: "signed by an enabled module without a membership",
          error: "SignatureExpired",
          arrange: async ({ roles, stranger }) => {
            await roles.write.enableModule([stranger.account.address]);
            return { signer: stranger };
          },
        },
      ];

      for (const { expired, error, arrange } of PRECEDENCE)
        it(`reverts ${error} on an expired signature ${expired}`, async () => {
          const fixture = await loadFixture(signedSetup);
          const { roles, relayer } = fixture;
          const { signer, beforeSending } = await arrange(fixture);
          const { roleTx, hash, signature } = await signedTx(
            fixture,
            { deadline: 0n },
            signer,
          );
          await beforeSending?.(hash);

          await viem.assertions.revertWithCustomError(
            roles.write.execTransactionWithRoleSigned([roleTx, signature], {
              account: relayer.account,
            }),
            roles,
            error,
          );
        });
    });

    describe("invalidate", () => {
      it("an invalidated digest cannot be executed, and nothing runs", async () => {
        const fixture = await loadFixture(signedSetup);
        const { roles, invoker, relayer, ALLOWANCE_KEY } = fixture;
        const { roleTx, hash, signature } = await signedTx(fixture);

        await viem.assertions.emitWithArgs(
          roles.write.invalidate([hash], { account: invoker.account }),
          roles,
          "HashInvalidated",
          [hash],
        );
        assert.equal(
          await roles.read.consumed([invoker.account.address, hash]),
          true,
        );

        await viem.assertions.revertWithCustomErrorWithArgs(
          roles.write.execTransactionWithRoleSigned([roleTx, signature], {
            account: relayer.account,
          }),
          roles,
          "HashAlreadyConsumed",
          [hash],
        );
        assert.equal(
          (await roles.read.accruedAllowance([ALLOWANCE_KEY]))[0],
          1000n,
        );
      });

      it("is keyed by the caller: invalidating another signer's digest does nothing", async () => {
        const fixture = await loadFixture(signedSetup);
        const { roles, invoker, relayer, ALLOWANCE_KEY } = fixture;
        const { roleTx, hash, signature } = await signedTx(fixture);

        // anyone may call it (the relayer is not a module), for itself only
        await roles.write.invalidate([hash], { account: relayer.account });
        assert.equal(
          await roles.read.consumed([relayer.account.address, hash]),
          true,
        );
        assert.equal(
          await roles.read.consumed([invoker.account.address, hash]),
          false,
        );

        await roles.write.execTransactionWithRoleSigned([roleTx, signature], {
          account: relayer.account,
        });
        assert.equal(
          await roles.read.consumed([invoker.account.address, hash]),
          true,
        );
        assert.equal(
          (await roles.read.accruedAllowance([ALLOWANCE_KEY]))[0],
          900n,
        );
      });

      it("cancels a refused signature that would pass later", async () => {
        const fixture = await loadFixture(signedSetup);
        const { roles, owner, invoker, relayer, ALLOWANCE_KEY } = fixture;
        await roles.write.setAllowance([ALLOWANCE_KEY, 50n, 0n, 0n, 0n, 0n], {
          account: owner.account,
        });
        const cancelled = await signedTx(fixture);
        const kept = await signedTx(fixture);

        // refused (over the allowance): the digests stay unconsumed
        for (const { roleTx, hash, signature } of [cancelled, kept]) {
          await viem.assertions.revertWithCustomError(
            roles.write.execTransactionWithRoleSigned([roleTx, signature], {
              account: relayer.account,
            }),
            roles,
            "ConditionViolation",
          );
          assert.equal(
            await roles.read.consumed([invoker.account.address, hash]),
            false,
          );
        }

        await roles.write.invalidate([cancelled.hash], {
          account: invoker.account,
        });
        await roles.write.setAllowance([ALLOWANCE_KEY, 1000n, 0n, 0n, 0n, 0n], {
          account: owner.account,
        });

        await viem.assertions.revertWithCustomError(
          roles.write.execTransactionWithRoleSigned(
            [cancelled.roleTx, cancelled.signature],
            { account: relayer.account },
          ),
          roles,
          "HashAlreadyConsumed",
        );
        // the one not invalidated now passes
        await roles.write.execTransactionWithRoleSigned(
          [kept.roleTx, kept.signature],
          { account: relayer.account },
        );
        assert.equal(
          (await roles.read.accruedAllowance([ALLOWANCE_KEY]))[0],
          900n,
        );
      });
    });
  });

  describe("across entrypoints", () => {
    /** The invoker calls the test contract through `entrypoint`; the
     *  signed one it signs, and the relayer sends. */
    async function send(
      fixture: Fixture,
      entrypoint: Entrypoint,
      data: Hex,
      value = 0n,
      operation = 0,
    ) {
      const { roles, invoker, relayer, testContractAddress, ROLE_KEY } =
        fixture;
      const sender =
        entrypoint === "execTransactionWithRoleSigned" ? relayer : invoker;
      return sender.sendTransaction({
        to: roles.address,
        data: await encodeEntrypoint(
          roles,
          entrypoint,
          {
            to: testContractAddress,
            value,
            data,
            operation,
            roleKey: ROLE_KEY,
          },
          invoker,
        ),
      });
    }

    for (const entrypoint of ENTRYPOINTS) {
      it(`${entrypoint} sends the value it is given`, async () => {
        const fixture = await loadFixture(signedSetup);
        const { testContract, testContractAddress } = fixture;

        await viem.assertions.emitWithArgs(
          send(
            fixture,
            entrypoint,
            encodeFunctionData({ abi, functionName: "anything" }),
            7n,
          ),
          testContract,
          "Invoked",
          [toFunctionSelector("anything()")],
        );
        const publicClient = await viem.getPublicClient();
        assert.equal(
          await publicClient.getBalance({ address: testContractAddress }),
          7n,
        );
      });

      it(`${entrypoint} delegatecalls when asked`, async () => {
        const fixture = await loadFixture(signedSetup);
        const { testContract, avatarAddress } = fixture;

        // the target's code runs in the avatar: the event comes from it
        const hash = await send(
          fixture,
          entrypoint,
          encodeFunctionData({ abi, functionName: "anything" }),
          0n,
          1,
        );
        const avatarTestContract = await viem.getContractAt(
          "TestContract",
          avatarAddress,
        );
        await viem.assertions.emit(hash, avatarTestContract, "Invoked");
        await assertNotEmitted(viem, hash, testContract, "Invoked");
      });

      it(`${entrypoint} keeps a membership's last use when the call fails`, async () => {
        const fixture = await loadFixture(signedSetup);
        const { roles, invoker, ROLE_KEY } = fixture;
        await roles.write.grantRole([
          invoker.account.address,
          ROLE_KEY,
          0n,
          0n,
          1n,
        ]);
        const failing = encodeFunctionData({
          abi,
          functionName: "fnThatMaybeReverts",
          args: [100n, true],
        });

        if (entrypoint.startsWith("execTransactionFromModule")) {
          // returns false: nothing to roll back, nothing settled
          const hash = await send(fixture, entrypoint, failing);
          await assertNotEmitted(viem, hash, roles, "RevokeRole");
          await assertNotEmitted(viem, hash, roles, "UpdateRole");
        } else {
          await viem.assertions.revertWithCustomError(
            send(fixture, entrypoint, failing),
            roles,
            "ModuleTransactionFailed",
          );
        }

        assert.deepEqual(
          await roles.read.membershipOf([invoker.account.address, ROLE_KEY]),
          [true, 0n, maxUint64, 1n],
        );
      });
    }
  });

  describe("default role", () => {
    it("reverts NoDefaultRole on both IAvatar entrypoints when none is set", async () => {
      const { roles, invoker, testContractAddress } = await loadFixture(setup);
      const calldata = encodeFunctionData({
        abi,
        functionName: "fnThatMaybeReverts",
        args: [100n, false],
      });
      await roles.write.setDefaultRole([invoker.account.address, zeroHash]);

      await viem.assertions.revertWithCustomError(
        roles.write.execTransactionFromModule(
          [testContractAddress, 0n, calldata, 0],
          { account: invoker.account },
        ),
        roles,
        "NoDefaultRole",
      );
      await viem.assertions.revertWithCustomError(
        roles.write.execTransactionFromModuleReturnData(
          [testContractAddress, 0n, calldata, 0],
          { account: invoker.account },
        ),
        roles,
        "NoDefaultRole",
      );
    });
  });
});
