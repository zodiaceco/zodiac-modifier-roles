import { expect } from "chai";
import { Interface, TypedDataEncoder, hexlify, randomBytes } from "ethers";
import { network } from "hardhat";

import {
  Encoding,
  ExecutionOptions,
  Operator,
  packConditions,
  maxUint64,
} from "./utils.js";
import { createSetup } from "./setup.js";
import {
  ENTRYPOINTS,
  NO_DEADLINE,
  ROLE_TX_TYPES,
  encodeEntrypoint,
} from "./roleTx.js";
import type { Entrypoint } from "./roleTx.js";

const connection = await network.create();
const { ethers, networkHelpers } = connection;
const { loadFixture, time } = networkHelpers;
const { deployRolesMod } = createSetup(connection);

const iface = new Interface([
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
    const [owner, invoker] = await ethers.getSigners();

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

    // Grant role (which enables the invoker as a module)
    await roles.grantRole(invoker.address, ROLE_KEY, 0, 0, 0);

    // Set as default role (for FromModule calls)
    await roles.setDefaultRole(invoker.address, ROLE_KEY);

    // Set initial allowance: 1000
    await roles.setAllowance(ALLOWANCE_KEY, 1000, 0, 0, 0, 0);

    // Scope target
    await roles.scopeTarget(ROLE_KEY, testContractAddress);

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
    await roles.allowFunctionPacked(
      ROLE_KEY,
      testContractAddress,
      iface.getFunction("fnThatMaybeReverts")!.selector,
      packed,
      ExecutionOptions.None,
    );
    await roles.allowFunctionPacked(
      ROLE_KEY,
      testContractAddress,
      iface.getFunction("revertWith")!.selector,
      "0x",
      ExecutionOptions.None,
    );
    // a function that may send value and be delegatecalled
    await roles.allowFunctionPacked(
      ROLE_KEY,
      testContractAddress,
      iface.getFunction("anything")!.selector,
      "0x",
      ExecutionOptions.Both,
    );
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
      const calldata = iface.encodeFunctionData("fnThatMaybeReverts", [
        100,
        false,
      ]);

      const success = await roles
        .connect(invoker)
        .execTransactionFromModule.staticCall(
          testContractAddress,
          0,
          calldata,
          0,
        );

      expect(success).to.be.true;

      await roles
        .connect(invoker)
        .execTransactionFromModule(testContractAddress, 0, calldata, 0);

      // Verify persistence: 1000 - 100 = 900
      const { balance } = await roles.accruedAllowance(ALLOWANCE_KEY);
      expect(balance).to.equal(900);
    });

    it("returns success=false and does not persist consumption on failed inner execution", async () => {
      const { roles, invoker, testContractAddress, ALLOWANCE_KEY } =
        await loadFixture(setup);

      // Consumes 100 but reverts
      const calldata = iface.encodeFunctionData("fnThatMaybeReverts", [
        100,
        true,
      ]);

      const success = await roles
        .connect(invoker)
        .execTransactionFromModule.staticCall(
          testContractAddress,
          0,
          calldata,
          0,
        );

      expect(success).to.be.false;

      await roles
        .connect(invoker)
        .execTransactionFromModule(testContractAddress, 0, calldata, 0);

      // Verify rollback: 1000 (unchanged)
      const { balance } = await roles.accruedAllowance(ALLOWANCE_KEY);
      expect(balance).to.equal(1000);
    });
  });

  describe("execTransactionFromModuleReturnData", () => {
    it("returns success=true, returnData, and persists consumption on successful execution", async () => {
      const { roles, invoker, testContractAddress, ALLOWANCE_KEY } =
        await loadFixture(setup);

      const calldata = iface.encodeFunctionData("fnThatMaybeReverts", [
        100,
        false,
      ]);

      const [success, returnData] = await roles
        .connect(invoker)
        .execTransactionFromModuleReturnData.staticCall(
          testContractAddress,
          0,
          calldata,
          0,
        );

      expect(success).to.be.true;
      expect(
        iface.decodeFunctionResult("fnThatMaybeReverts", returnData)[0],
      ).to.equal(100n);

      await roles
        .connect(invoker)
        .execTransactionFromModuleReturnData(
          testContractAddress,
          0,
          calldata,
          0,
        );

      const { balance } = await roles.accruedAllowance(ALLOWANCE_KEY);
      expect(balance).to.equal(900);
    });

    it("returns success=false, revert data, and does not persist consumption on failed inner execution", async () => {
      const {
        roles,
        invoker,
        testContract,
        testContractAddress,
        ALLOWANCE_KEY,
      } = await loadFixture(setup);

      const calldata = iface.encodeFunctionData("fnThatMaybeReverts", [
        100,
        true,
      ]);

      const [success, returnData] = await roles
        .connect(invoker)
        .execTransactionFromModuleReturnData.staticCall(
          testContractAddress,
          0,
          calldata,
          0,
        );

      expect(success).to.be.false;
      expect(returnData).to.equal(
        testContract.interface.getError("AnError")!.selector,
      );

      await roles
        .connect(invoker)
        .execTransactionFromModuleReturnData(
          testContractAddress,
          0,
          calldata,
          0,
        );

      const { balance } = await roles.accruedAllowance(ALLOWANCE_KEY);
      expect(balance).to.equal(1000);
    });
  });

  describe("execTransactionWithRole", () => {
    it("succeeds, returns returnData, and persists consumption when using correct role", async () => {
      const { roles, invoker, testContractAddress, ROLE_KEY, ALLOWANCE_KEY } =
        await loadFixture(setup);
      const calldata = iface.encodeFunctionData("fnThatMaybeReverts", [
        100,
        false,
      ]);

      const returnData = await roles
        .connect(invoker)
        .execTransactionWithRole.staticCall(
          testContractAddress,
          0,
          calldata,
          0,
          ROLE_KEY,
        );

      expect(
        iface.decodeFunctionResult("fnThatMaybeReverts", returnData)[0],
      ).to.equal(100n);

      await roles
        .connect(invoker)
        .execTransactionWithRole(testContractAddress, 0, calldata, 0, ROLE_KEY);

      const { balance } = await roles.accruedAllowance(ALLOWANCE_KEY);
      expect(balance).to.equal(900);
    });

    it("reverts when using unassigned role", async () => {
      const { roles, invoker, testContractAddress } = await loadFixture(setup);
      const calldata = iface.encodeFunctionData("fnThatMaybeReverts", [
        100,
        false,
      ]);
      const BAD_ROLE = ethers.id("BAD_ROLE");

      await expect(
        roles
          .connect(invoker)
          .execTransactionWithRole(
            testContractAddress,
            0,
            calldata,
            0,
            BAD_ROLE,
          ),
      ).to.be.revertedWithCustomError(roles, "NoMembership");
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
      const calldata = iface.encodeFunctionData("fnThatMaybeReverts", [
        100,
        true,
      ]);

      await expect(
        roles
          .connect(invoker)
          .execTransactionWithRole(
            testContractAddress,
            0,
            calldata,
            0,
            ROLE_KEY,
          ),
      )
        .to.be.revertedWithCustomError(roles, "ModuleTransactionFailed")
        .withArgs(testContract.interface.encodeErrorResult("AnError"));

      const { balance } = await roles.accruedAllowance(ALLOWANCE_KEY);
      expect(balance).to.equal(1000);
    });

    it("reverts with empty ModuleTransactionFailed when inner execution reverts without data", async () => {
      const { roles, invoker, testContractAddress, ROLE_KEY } =
        await loadFixture(setup);
      const calldata = iface.encodeFunctionData("revertWith", ["0x"]);

      await expect(
        roles
          .connect(invoker)
          .execTransactionWithRole(
            testContractAddress,
            0,
            calldata,
            0,
            ROLE_KEY,
          ),
      )
        .to.be.revertedWithCustomError(roles, "ModuleTransactionFailed")
        .withArgs("0x");
    });

    for (const [what, revertData] of [
      [
        "a custom error with arguments",
        new Interface([
          "error AnErrorWithArgs(uint256, string)",
        ]).encodeErrorResult("AnErrorWithArgs", [
          42,
          "a reason longer than one word, to span two",
        ]),
      ],
      [
        "a revert string",
        new Interface(["error Error(string)"]).encodeErrorResult("Error", [
          "a revert string longer than one 32-byte word",
        ]),
      ],
    ])
      it(`carries ${what} in ModuleTransactionFailed verbatim`, async () => {
        const { roles, invoker, testContractAddress, ROLE_KEY } =
          await loadFixture(setup);
        const calldata = iface.encodeFunctionData("revertWith", [revertData]);

        await expect(
          roles
            .connect(invoker)
            .execTransactionWithRole(
              testContractAddress,
              0,
              calldata,
              0,
              ROLE_KEY,
            ),
        )
          .to.be.revertedWithCustomError(roles, "ModuleTransactionFailed")
          .withArgs(revertData);
      });
  });

  // The signed entrypoint's fixture, which the tests across entrypoints
  // share: a relayer sends what the invoker signs.
  async function signedSetup() {
    const fixture = await setup();
    const [, , relayer, stranger] = await ethers.getSigners();
    // another role of the invoker that would authorize the same call
    const OTHER_ROLE = ethers.id("OTHER_ROLE");
    await fixture.roles.grantRole(fixture.invoker.address, OTHER_ROLE, 0, 0, 0);
    await fixture.roles.allowTargetPacked(
      OTHER_ROLE,
      fixture.testContractAddress,
      "0x",
      ExecutionOptions.None,
    );
    return { ...fixture, relayer, stranger, OTHER_ROLE };
  }
  type Fixture = Awaited<ReturnType<typeof signedSetup>>;

  /** A RoleTx spending 100 of the allowance, as `overrides` change it,
   *  signed by `signer`. */
  async function signedTx(
    fixture: Fixture,
    overrides: Record<string, unknown> = {},
    signer: Fixture["invoker"] = fixture.invoker,
  ) {
    const { roles, testContractAddress, ROLE_KEY } = fixture;
    const domain = {
      chainId: (await ethers.provider.getNetwork()).chainId,
      verifyingContract: await roles.getAddress(),
    };
    const roleTx = {
      to: testContractAddress,
      value: 0,
      data: iface.encodeFunctionData("fnThatMaybeReverts", [100, false]),
      operation: 0,
      roleKey: ROLE_KEY,
      salt: hexlify(randomBytes(32)),
      deadline: NO_DEADLINE,
      ...overrides,
    };
    return {
      roleTx,
      hash: TypedDataEncoder.hash(domain, ROLE_TX_TYPES, roleTx),
      signature: await signer.signTypedData(domain, ROLE_TX_TYPES, roleTx),
    };
  }

  describe("execTransactionWithRoleSigned", () => {
    it("executes, returns returnData, and persists consumption when signed by an enabled module", async () => {
      const fixture = await loadFixture(signedSetup);
      const { roles, relayer, ALLOWANCE_KEY } = fixture;
      const { roleTx, hash, signature } = await signedTx(fixture);

      const returnData = await roles
        .connect(relayer)
        .execTransactionWithRoleSigned.staticCall(roleTx, signature);
      expect(
        iface.decodeFunctionResult("fnThatMaybeReverts", returnData)[0],
      ).to.equal(100n);

      await expect(
        roles.connect(relayer).execTransactionWithRoleSigned(roleTx, signature),
      )
        .to.emit(roles, "HashExecuted")
        .withArgs(hash);
      expect((await roles.accruedAllowance(ALLOWANCE_KEY)).balance).to.equal(
        900,
      );
    });

    it("reverts NotAuthorized when signer is not an enabled module", async () => {
      const fixture = await loadFixture(signedSetup);
      const { roles, relayer } = fixture;
      const { roleTx, signature } = await signedTx(fixture, {}, relayer);

      await expect(
        roles.connect(relayer).execTransactionWithRoleSigned(roleTx, signature),
      ).to.be.revertedWithCustomError(roles, "NotAuthorized");
    });

    it("reverts HashAlreadyConsumed when the same signature is replayed", async () => {
      const fixture = await loadFixture(signedSetup);
      const { roles, relayer } = fixture;
      const { roleTx, hash, signature } = await signedTx(fixture);

      await roles
        .connect(relayer)
        .execTransactionWithRoleSigned(roleTx, signature);
      await expect(
        roles.connect(relayer).execTransactionWithRoleSigned(roleTx, signature),
      )
        .to.be.revertedWithCustomError(roles, "HashAlreadyConsumed")
        .withArgs(hash);
    });

    describe("binds the signature to every field and the instance", () => {
      // the signature no longer recovers to the invoker: NotAuthorized,
      // before any membership or permission is looked at
      const TAMPERED: Record<string, (f: Fixture) => Record<string, unknown>> =
        {
          to: (f) => ({ to: f.avatarAddress }),
          value: () => ({ value: 1 }),
          data: () => ({
            data: iface.encodeFunctionData("fnThatMaybeReverts", [1, false]),
          }),
          operation: () => ({ operation: 1 }),
          roleKey: (f) => ({ roleKey: f.OTHER_ROLE }),
          salt: () => ({ salt: hexlify(randomBytes(32)) }),
          deadline: () => ({ deadline: NO_DEADLINE - 1n }),
        };

      for (const [field, tamper] of Object.entries(TAMPERED))
        it(`rejects a changed ${field}, then executes what was signed`, async () => {
          const fixture = await loadFixture(signedSetup);
          const { roles, invoker, relayer } = fixture;
          const { roleTx, hash, signature } = await signedTx(fixture);

          await expect(
            roles
              .connect(relayer)
              .execTransactionWithRoleSigned(
                { ...roleTx, ...tamper(fixture) },
                signature,
              ),
          ).to.be.revertedWithCustomError(roles, "NotAuthorized");

          await roles
            .connect(relayer)
            .execTransactionWithRoleSigned(roleTx, signature);
          expect(await roles.consumed(invoker.address, hash)).to.equal(true);
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
          owner.address,
          avatarAddress,
          avatarAddress,
        );
        await other.grantRole(invoker.address, ROLE_KEY, 0, 0, 0);
        await other.allowTargetPacked(
          ROLE_KEY,
          testContractAddress,
          "0x",
          ExecutionOptions.None,
        );
        const { roleTx, signature } = await signedTx(fixture);

        await expect(
          other
            .connect(relayer)
            .execTransactionWithRoleSigned(roleTx, signature),
        ).to.be.revertedWithCustomError(other, "NotAuthorized");
      });
    });

    it("reverts with ModuleTransactionFailed and rolls back digest consumption on failed inner execution", async () => {
      const fixture = await loadFixture(signedSetup);
      const { roles, invoker, relayer, testContract, ALLOWANCE_KEY } = fixture;

      for (const [data, revertData] of [
        [
          iface.encodeFunctionData("fnThatMaybeReverts", [100, true]),
          testContract.interface.encodeErrorResult("AnError"),
        ],
        [iface.encodeFunctionData("revertWith", ["0x"]), "0x"],
      ]) {
        const { roleTx, hash, signature } = await signedTx(fixture, { data });

        await expect(
          roles
            .connect(relayer)
            .execTransactionWithRoleSigned(roleTx, signature),
        )
          .to.be.revertedWithCustomError(roles, "ModuleTransactionFailed")
          .withArgs(revertData);
        expect(await roles.consumed(invoker.address, hash)).to.equal(false);
      }
      expect((await roles.accruedAllowance(ALLOWANCE_KEY)).balance).to.equal(
        1000,
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
        await roles
          .connect(relayer)
          .execTransactionWithRoleSigned(onTime.roleTx, onTime.signature);

        await time.setNextBlockTimestamp(deadline + 1n);
        await expect(
          roles
            .connect(relayer)
            .execTransactionWithRoleSigned(late.roleTx, late.signature),
        ).to.be.revertedWithCustomError(roles, "SignatureExpired");
        expect(await roles.consumed(invoker.address, late.hash)).to.equal(
          false,
        );
      });

      it("treats deadline 0 as always expired", async () => {
        const fixture = await loadFixture(signedSetup);
        const { roles, relayer } = fixture;
        const { roleTx, signature } = await signedTx(fixture, { deadline: 0 });

        await expect(
          roles
            .connect(relayer)
            .execTransactionWithRoleSigned(roleTx, signature),
        ).to.be.revertedWithCustomError(roles, "SignatureExpired");
      });

      // The signature is checked first (moduleOnlySigned), then the
      // deadline, then the membership.
      const PRECEDENCE: {
        expired: string;
        error: string;
        arrange: (f: Fixture) => Promise<{
          signer: Fixture["invoker"];
          beforeSending?: (hash: string) => any;
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
            beforeSending: (hash) => roles.connect(invoker).invalidate(hash),
          }),
        },
        {
          expired: "signed by an enabled module without a membership",
          error: "SignatureExpired",
          arrange: async ({ roles, stranger }) => {
            await roles.enableModule(stranger.address);
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
            { deadline: 0 },
            signer,
          );
          await beforeSending?.(hash);

          await expect(
            roles
              .connect(relayer)
              .execTransactionWithRoleSigned(roleTx, signature),
          ).to.be.revertedWithCustomError(roles, error);
        });
    });

    describe("invalidate", () => {
      it("an invalidated digest cannot be executed, and nothing runs", async () => {
        const fixture = await loadFixture(signedSetup);
        const { roles, invoker, relayer, ALLOWANCE_KEY } = fixture;
        const { roleTx, hash, signature } = await signedTx(fixture);

        await expect(roles.connect(invoker).invalidate(hash))
          .to.emit(roles, "HashInvalidated")
          .withArgs(hash);
        expect(await roles.consumed(invoker.address, hash)).to.equal(true);

        await expect(
          roles
            .connect(relayer)
            .execTransactionWithRoleSigned(roleTx, signature),
        )
          .to.be.revertedWithCustomError(roles, "HashAlreadyConsumed")
          .withArgs(hash);
        expect((await roles.accruedAllowance(ALLOWANCE_KEY)).balance).to.equal(
          1000,
        );
      });

      it("is keyed by the caller: invalidating another signer's digest does nothing", async () => {
        const fixture = await loadFixture(signedSetup);
        const { roles, invoker, relayer, ALLOWANCE_KEY } = fixture;
        const { roleTx, hash, signature } = await signedTx(fixture);

        // anyone may call it (the relayer is not a module), for itself only
        await roles.connect(relayer).invalidate(hash);
        expect(await roles.consumed(relayer.address, hash)).to.equal(true);
        expect(await roles.consumed(invoker.address, hash)).to.equal(false);

        await roles
          .connect(relayer)
          .execTransactionWithRoleSigned(roleTx, signature);
        expect(await roles.consumed(invoker.address, hash)).to.equal(true);
        expect((await roles.accruedAllowance(ALLOWANCE_KEY)).balance).to.equal(
          900,
        );
      });

      it("cancels a refused signature that would pass later", async () => {
        const fixture = await loadFixture(signedSetup);
        const { roles, owner, invoker, relayer, ALLOWANCE_KEY } = fixture;
        await roles.connect(owner).setAllowance(ALLOWANCE_KEY, 50, 0, 0, 0, 0);
        const cancelled = await signedTx(fixture);
        const kept = await signedTx(fixture);

        // refused (over the allowance): the digests stay unconsumed
        for (const { roleTx, hash, signature } of [cancelled, kept]) {
          await expect(
            roles
              .connect(relayer)
              .execTransactionWithRoleSigned(roleTx, signature),
          ).to.be.revertedWithCustomError(roles, "ConditionViolation");
          expect(await roles.consumed(invoker.address, hash)).to.equal(false);
        }

        await roles.connect(invoker).invalidate(cancelled.hash);
        await roles
          .connect(owner)
          .setAllowance(ALLOWANCE_KEY, 1000, 0, 0, 0, 0);

        await expect(
          roles
            .connect(relayer)
            .execTransactionWithRoleSigned(
              cancelled.roleTx,
              cancelled.signature,
            ),
        ).to.be.revertedWithCustomError(roles, "HashAlreadyConsumed");
        // the one not invalidated now passes
        await roles
          .connect(relayer)
          .execTransactionWithRoleSigned(kept.roleTx, kept.signature);
        expect((await roles.accruedAllowance(ALLOWANCE_KEY)).balance).to.equal(
          900,
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
      data: string,
      value = 0n,
      operation = 0,
    ) {
      const { roles, invoker, relayer, testContractAddress, ROLE_KEY } =
        fixture;
      const sender =
        entrypoint === "execTransactionWithRoleSigned" ? relayer : invoker;
      return sender.sendTransaction({
        to: await roles.getAddress(),
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

        await expect(
          send(fixture, entrypoint, iface.encodeFunctionData("anything"), 7n),
        )
          .to.emit(testContract, "Invoked")
          .withArgs(iface.getFunction("anything")!.selector);
        expect(await ethers.provider.getBalance(testContractAddress)).to.equal(
          7n,
        );
      });

      it(`${entrypoint} delegatecalls when asked`, async () => {
        const fixture = await loadFixture(signedSetup);
        const { testContract, avatarAddress } = fixture;

        // the target's code runs in the avatar: the event comes from it
        await expect(
          send(
            fixture,
            entrypoint,
            iface.encodeFunctionData("anything"),
            0n,
            1,
          ),
        )
          .to.emit(testContract.attach(avatarAddress), "Invoked")
          .and.not.to.emit(testContract, "Invoked");
      });

      it(`${entrypoint} keeps a membership's last use when the call fails`, async () => {
        const fixture = await loadFixture(signedSetup);
        const { roles, invoker, ROLE_KEY } = fixture;
        await roles.grantRole(invoker.address, ROLE_KEY, 0, 0, 1);
        const failing = iface.encodeFunctionData("fnThatMaybeReverts", [
          100,
          true,
        ]);

        if (entrypoint.startsWith("execTransactionFromModule"))
          // returns false: nothing to roll back, nothing settled
          await expect(send(fixture, entrypoint, failing))
            .to.not.emit(roles, "RevokeRole")
            .and.not.to.emit(roles, "UpdateRole");
        else
          await expect(
            send(fixture, entrypoint, failing),
          ).to.be.revertedWithCustomError(roles, "ModuleTransactionFailed");

        expect(
          await roles.membershipOf(invoker.address, ROLE_KEY),
        ).to.deep.equal([true, 0n, maxUint64, 1n]);
      });
    }
  });

  describe("default role", () => {
    it("reverts NoDefaultRole on both IAvatar entrypoints when none is set", async () => {
      const { roles, invoker, testContractAddress } = await loadFixture(setup);
      const calldata = iface.encodeFunctionData("fnThatMaybeReverts", [
        100,
        false,
      ]);
      await roles.setDefaultRole(invoker.address, ethers.ZeroHash);

      await expect(
        roles
          .connect(invoker)
          .execTransactionFromModule(testContractAddress, 0, calldata, 0),
      ).to.be.revertedWithCustomError(roles, "NoDefaultRole");
      await expect(
        roles
          .connect(invoker)
          .execTransactionFromModuleReturnData(
            testContractAddress,
            0,
            calldata,
            0,
          ),
      ).to.be.revertedWithCustomError(roles, "NoDefaultRole");
    });
  });
});
