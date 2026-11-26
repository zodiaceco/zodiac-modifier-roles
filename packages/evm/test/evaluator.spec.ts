import assert from "node:assert/strict";
import { randomBytes } from "node:crypto";
import { after, describe, it } from "node:test";
import { network } from "hardhat";
import {
  encodeFunctionData,
  getAddress,
  isAddressEqual,
  keccak256,
  parseAbi,
  parseEther,
  toBytes,
  toFunctionSelector,
  toHex,
  zeroAddress,
  zeroHash,
} from "viem";
import type { Hex } from "viem";

import {
  assertRevertedWithoutReason,
  type ConditionFlat,
  ConditionViolationStatus,
  Encoding,
  ExecutionOptions,
  flattenCondition,
  Operator,
} from "./utils.js";
import { createSetup } from "./setup.js";
import { ENTRYPOINTS, NO_DEADLINE, encodeEntrypoint } from "./roleTx.js";
import type { Entrypoint } from "./roleTx.js";

const connection = await network.create();
const { viem, networkHelpers } = connection;
const { loadFixture, time } = networkHelpers;
const { deployEvaluator, deployRolesMod } = createSetup(connection);

const abi = parseAbi([
  "function doNothing()",
  "function oneParamStatic(uint256)",
  "function fn(address)",
]);

describe("Core / Evaluator split", () => {
  after(async () => {
    await connection.close();
  });

  async function setup() {
    const [owner, member, nonMember, relayer] = await viem.getWalletClients();

    const avatar = await viem.deployContract("TestAvatar");
    const avatarAddress = avatar.address;

    const testContract = await viem.deployContract("TestContract");
    const testContractAddress = testContract.address;

    const evaluator = await deployEvaluator();
    const evaluatorAddress = evaluator.address;

    const roles = await deployRolesMod(
      owner.account.address,
      avatarAddress,
      avatarAddress,
      evaluatorAddress,
    );

    const roleKey = toHex(randomBytes(32));

    await roles.write.grantRole([member.account.address, roleKey, 0n, 0n, 0n], {
      account: owner.account,
    });
    await roles.write.setDefaultRole([member.account.address, roleKey], {
      account: owner.account,
    });
    await roles.write.scopeTarget([roleKey, testContractAddress], {
      account: owner.account,
    });

    return {
      owner,
      member,
      nonMember,
      relayer,
      avatar,
      avatarAddress,
      testContract,
      testContractAddress,
      evaluator,
      evaluatorAddress,
      roles,
      roleKey,
    };
  }

  describe("evaluator configuration & hot-swapping", () => {
    it("sets the initial evaluator during deployment and emits SetEvaluator", async () => {
      const { owner, avatarAddress, evaluatorAddress } =
        await loadFixture(setup);

      const { contract: roles, deploymentTransaction } =
        await viem.sendDeploymentTransaction("Roles", [
          owner.account.address,
          avatarAddress,
          avatarAddress,
          evaluatorAddress,
        ]);

      assert.equal(
        getAddress(await roles.read.evaluator()),
        getAddress(evaluatorAddress),
      );
      await viem.assertions.emitWithArgs(
        deploymentTransaction.hash,
        roles,
        "SetEvaluator",
        [evaluatorAddress],
      );
    });

    it("reverts ZeroAddressNotAllowed if initial evaluator is address(0)", async () => {
      const { roles, owner, avatarAddress } = await loadFixture(setup);

      await viem.assertions.revertWithCustomError(
        deployRolesMod(
          owner.account.address,
          avatarAddress,
          avatarAddress,
          zeroAddress,
        ) as Promise<any>,
        roles,
        "ZeroAddressNotAllowed",
      );
    });

    it("swaps the evaluator, emitting SetEvaluator, and rejects the zero address", async () => {
      const { roles, owner } = await loadFixture(setup);

      const alt = await deployEvaluator();
      const altAddress = alt.address;

      await viem.assertions.revertWithCustomError(
        roles.write.setEvaluator([zeroAddress], { account: owner.account }),
        roles,
        "ZeroAddressNotAllowed",
      );

      await viem.assertions.emitWithArgs(
        roles.write.setEvaluator([altAddress], { account: owner.account }),
        roles,
        "SetEvaluator",
        [altAddress],
      );

      assert.equal(
        getAddress(await roles.read.evaluator()),
        getAddress(altAddress),
      );
    });

    it("swaps evaluator on an existing mod with no redeploy and preserves all state", async () => {
      const {
        roles,
        owner,
        member,
        testContractAddress,
        roleKey,
        evaluatorAddress,
      } = await loadFixture(setup);

      const selector = toFunctionSelector("oneParamStatic(uint256)");
      const allowanceKey = keccak256(toBytes("HOT_SWAP_ALLOWANCE"));

      await roles.write.setAllowance([allowanceKey, 100n, 0n, 0n, 0n, 0n]);
      await roles.write.allowFunction([
        roleKey,
        testContractAddress,
        selector,
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.Static,
              operator: Operator.WithinAllowance,
              compValue: allowanceKey,
            },
          ],
        }),
        ExecutionOptions.None,
      ]);

      // Works with initial evaluator and consumes 40
      await roles.write.execTransactionFromModule(
        [
          testContractAddress,
          0n,
          encodeFunctionData({
            abi,
            functionName: "oneParamStatic",
            args: [40n],
          }),
          0,
        ],
        { account: member.account },
      );
      assert.equal((await roles.read.allowances([allowanceKey]))[3], 60n);

      // Swap to always-deny evaluator: same permission now fails without redeploying Core
      const deny = await viem.deployContract("TestAlwaysDenyEvaluator");
      await roles.write.setEvaluator([deny.address], {
        account: owner.account,
      });

      await viem.assertions.revertWithCustomErrorWithArgs(
        roles.write.execTransactionFromModule(
          [
            testContractAddress,
            0n,
            encodeFunctionData({
              abi,
              functionName: "oneParamStatic",
              args: [10n],
            }),
            0,
          ],
          { account: member.account },
        ),
        roles,
        "ConditionViolation",
        [ConditionViolationStatus.ParameterNotAllowed, 7n, 4n],
      );

      // Swap back to a freshly deployed real Evaluator: membership, permission, and allowance balance (60) remain intact
      const fresh = await deployEvaluator();
      assert.ok(!isAddressEqual(fresh.address, evaluatorAddress));
      await roles.write.setEvaluator([fresh.address], {
        account: owner.account,
      });

      // 70 > remaining 60 fails
      await viem.assertions.revertWithCustomError(
        roles.write.execTransactionFromModule(
          [
            testContractAddress,
            0n,
            encodeFunctionData({
              abi,
              functionName: "oneParamStatic",
              args: [70n],
            }),
            0,
          ],
          { account: member.account },
        ),
        roles,
        "ConditionViolation",
      );

      // 60 <= remaining 60 succeeds
      await roles.write.execTransactionFromModule(
        [
          testContractAddress,
          0n,
          encodeFunctionData({
            abi,
            functionName: "oneParamStatic",
            args: [60n],
          }),
          0,
        ],
        { account: member.account },
      );
      assert.equal((await roles.read.allowances([allowanceKey]))[3], 0n);
    });

    it("reverts EvaluatorNotAContract if evaluator has no code", async () => {
      const { roles, owner, member, nonMember, testContractAddress, roleKey } =
        await loadFixture(setup);

      await roles.write.allowTargetPacked([
        roleKey,
        testContractAddress,
        "0x",
        ExecutionOptions.None,
      ]);
      await roles.write.setEvaluator([nonMember.account.address], {
        account: owner.account,
      });

      await viem.assertions.revertWithCustomErrorWithArgs(
        roles.write.execTransactionFromModule(
          [
            testContractAddress,
            0n,
            encodeFunctionData({ abi, functionName: "doNothing" }),
            0,
          ],
          { account: member.account },
        ),
        roles,
        "EvaluatorNotAContract",
        [nonMember.account.address],
      );

      await assertRevertedWithoutReason(
        roles.read.packConditions([
          [
            {
              parent: 0,
              paramType: Encoding.None,
              operator: Operator.Pass,
              compValue: "0x",
            },
          ],
        ]),
      );
    });

    describe("validated setters pack through the Evaluator, *Packed setters bypass it", () => {
      async function setupWithRevertingEvaluator() {
        const ctx = await setup();
        const reverting = await viem.deployContract("TestRevertingEvaluator");
        await ctx.roles.write.setEvaluator([reverting.address], {
          account: ctx.owner.account,
        });
        return { ...ctx, reverting };
      }

      const selector = toFunctionSelector("doNothing()");
      type Ctx = Awaited<ReturnType<typeof setupWithRevertingEvaluator>>;
      type Conditions = ConditionFlat[];

      const VALIDATED: Record<
        string,
        (c: Ctx, conditions: Conditions) => Promise<Hex>
      > = {
        packConditions: ({ roles }, conditions) =>
          roles.read.packConditions([conditions]),
        allowTarget: ({ roles, roleKey, testContractAddress }, conditions) =>
          roles.write.allowTarget([
            roleKey,
            testContractAddress,
            conditions,
            ExecutionOptions.None,
          ]),
        allowFunction: ({ roles, roleKey, testContractAddress }, conditions) =>
          roles.write.allowFunction([
            roleKey,
            testContractAddress,
            selector,
            conditions,
            ExecutionOptions.None,
          ]),
        allowFunctionGlobally: ({ roles, roleKey }, conditions) =>
          roles.write.allowFunctionGlobally([roleKey, selector, conditions]),
      };

      // any bytes: a *Packed setter stores them without calling the
      // Evaluator. Each is listed with its arguments, which are also those
      // of the event it emits.
      const BUFFER = "0x00" as const;
      const PACKED = [
        {
          name: "allowTargetPacked",
          run: ({ roles, roleKey, testContractAddress }: Ctx) => {
            const args = [
              roleKey,
              testContractAddress,
              BUFFER,
              ExecutionOptions.None,
            ] as const;
            return viem.assertions.emitWithArgs(
              roles.write.allowTargetPacked([...args]),
              roles,
              "AllowTarget",
              [...args],
            );
          },
        },
        {
          name: "allowFunctionPacked",
          run: ({ roles, roleKey, testContractAddress }: Ctx) => {
            const args = [
              roleKey,
              testContractAddress,
              selector,
              BUFFER,
              ExecutionOptions.None,
            ] as const;
            return viem.assertions.emitWithArgs(
              roles.write.allowFunctionPacked([...args]),
              roles,
              "AllowFunction",
              [...args],
            );
          },
        },
        {
          name: "allowFunctionGloballyPacked",
          run: ({ roles, roleKey }: Ctx) => {
            const args = [roleKey, selector, BUFFER] as const;
            return viem.assertions.emitWithArgs(
              roles.write.allowFunctionGloballyPacked([...args]),
              roles,
              "AllowFunctionGlobally",
              [...args],
            );
          },
        },
      ] as const;

      for (const [name, call] of Object.entries(VALIDATED))
        it(`${name} packs conditions through the Evaluator, and none without calling it`, async () => {
          const ctx = await loadFixture(setupWithRevertingEvaluator);

          await viem.assertions.revertWithCustomError(
            call(
              ctx,
              flattenCondition({
                paramType: Encoding.None,
                operator: Operator.Pass,
              }),
            ),
            ctx.reverting,
            "IntentionalEvaluatorRevert",
          );
          // empty conditions skip packing: stored (or returned) as empty
          const result = await call(ctx, []);
          if (name === "packConditions") assert.equal(result, "0x");
        });

      for (const { name, run } of PACKED)
        it(`${name} stores the buffer without calling the Evaluator`, async () => {
          const ctx = await loadFixture(setupWithRevertingEvaluator);

          // the buffer is emitted as given, not as an Evaluator packed it
          await run(ctx);
        });
    });
  });

  describe("authentication, independent of the Evaluator", () => {
    async function setupWithAlwaysAllowEvaluator() {
      const ctx = await setup();
      const alwaysAllow = await viem.deployContract("TestAlwaysAllowEvaluator");
      await ctx.roles.write.setEvaluator([alwaysAllow.address], {
        account: ctx.owner.account,
      });

      await ctx.roles.write.allowTargetPacked([
        ctx.roleKey,
        ctx.testContractAddress,
        "0x",
        ExecutionOptions.Both,
      ]);

      return { ...ctx, alwaysAllow };
    }
    type Ctx = Awaited<ReturnType<typeof setupWithAlwaysAllowEvaluator>>;

    /** `module` calls the test contract through `entrypoint`; the signed one
     *  it signs, and the relayer sends. */
    async function execThrough(
      { roles, relayer, roleKey, testContractAddress: to }: Ctx,
      entrypoint: Entrypoint,
      module: Ctx["member"],
      deadline = NO_DEADLINE,
    ) {
      const sender =
        entrypoint === "execTransactionWithRoleSigned" ? relayer : module;
      return sender.sendTransaction({
        to: roles.address,
        data: await encodeEntrypoint(
          roles,
          entrypoint,
          {
            to,
            data: encodeFunctionData({ abi, functionName: "doNothing" }),
            roleKey,
            deadline,
          },
          module,
        ),
      });
    }

    const REJECTIONS: {
      who: string;
      error:
        | "NotAuthorized"
        | "NoMembership"
        | "NoDefaultRole"
        | "SignatureExpired";
      entrypoints: readonly Entrypoint[];
      arrange: (
        ctx: Ctx,
      ) => Promise<{ module: Ctx["member"]; deadline?: bigint }>;
    }[] = [
      {
        who: "a caller that is not an enabled module",
        error: "NotAuthorized",
        entrypoints: ENTRYPOINTS,
        arrange: async ({ nonMember }) => ({ module: nonMember }),
      },
      {
        who: "an enabled module without a membership",
        error: "NoMembership",
        entrypoints: ENTRYPOINTS,
        arrange: async ({ roles, nonMember, roleKey }) => {
          await roles.write.enableModule([nonMember.account.address]);
          await roles.write.setDefaultRole([
            nonMember.account.address,
            roleKey,
          ]);
          return { module: nonMember };
        },
      },
      {
        who: "a member without a default role",
        error: "NoDefaultRole",
        entrypoints: [
          "execTransactionFromModule",
          "execTransactionFromModuleReturnData",
        ],
        arrange: async ({ roles, member }) => {
          await roles.write.setDefaultRole([member.account.address, zeroHash]);
          return { module: member };
        },
      },
      {
        who: "a member's signature past its deadline",
        error: "SignatureExpired",
        entrypoints: ["execTransactionWithRoleSigned"],
        arrange: async ({ member }) => ({
          module: member,
          deadline: BigInt(await time.latest()),
        }),
      },
    ];

    for (const entrypoint of ENTRYPOINTS)
      it(`lets a member through ${entrypoint} (the control)`, async () => {
        const ctx = await loadFixture(setupWithAlwaysAllowEvaluator);

        await execThrough(ctx, entrypoint, ctx.member);
      });

    for (const { who, error, entrypoints, arrange } of REJECTIONS)
      for (const entrypoint of entrypoints)
        it(`rejects ${who} on ${entrypoint} with ${error}`, async () => {
          const ctx = await loadFixture(setupWithAlwaysAllowEvaluator);
          const { module, deadline } = await arrange(ctx);

          await viem.assertions.revertWithCustomError(
            execThrough(ctx, entrypoint, module, deadline),
            ctx.roles,
            error,
          );
        });

    it("enforces zero role, validity window, and finite uses", async () => {
      const { roles, owner, nonMember, testContractAddress, roleKey } =
        await loadFixture(setupWithAlwaysAllowEvaluator);

      const data = encodeFunctionData({ abi, functionName: "doNothing" });
      const exec = (role: Hex) =>
        roles.write.execTransactionWithRole(
          [testContractAddress, 0n, data, 0, role],
          { account: nonMember.account },
        );

      // Zero role is always rejected
      await roles.write.grantRole(
        [nonMember.account.address, zeroHash, 0n, 0n, 0n],
        { account: owner.account },
      );
      await viem.assertions.revertWithCustomError(
        exec(zeroHash),
        roles,
        "NoMembership",
      );

      // Future start timestamp rejected
      const now = BigInt(await time.latest());
      await roles.write.grantRole(
        [nonMember.account.address, roleKey, now + 1000n, now + 2000n, 1n],
        { account: owner.account },
      );
      await viem.assertions.revertWithCustomError(
        exec(roleKey),
        roles,
        "MembershipNotYetValid",
      );

      // Advance into window: 1 use succeeds, 2nd call rejected
      await time.increaseTo(now + 1000n);
      await exec(roleKey);
      await viem.assertions.revertWithCustomError(
        exec(roleKey),
        roles,
        "NoMembership",
      );

      // Expired membership rejected
      await roles.write.grantRole(
        [nonMember.account.address, roleKey, now, now + 1500n, 0n],
        { account: owner.account },
      );
      await time.increaseTo(now + 1501n);
      await viem.assertions.revertWithCustomError(
        exec(roleKey),
        roles,
        "MembershipExpired",
      );
    });
  });

  describe("Core invariants independent of Evaluator", () => {
    it("enforces scopeConfig lookup, ExecutionOptions, and short calldata even with always-allow Evaluator", async () => {
      const { roles, owner, member, avatar, testContractAddress, roleKey } =
        await loadFixture(setup);

      const alwaysAllow = await viem.deployContract("TestAlwaysAllowEvaluator");
      await roles.write.setEvaluator([alwaysAllow.address], {
        account: owner.account,
      });

      // Unpermitted selector still reverts TransactionNotAllowed
      await viem.assertions.revertWithCustomError(
        roles.write.execTransactionFromModule(
          [
            testContractAddress,
            0n,
            encodeFunctionData({ abi, functionName: "doNothing" }),
            0,
          ],
          { account: member.account },
        ),
        roles,
        "TransactionNotAllowed",
      );

      // Allow target with ExecutionOptions.None
      await roles.write.allowTargetPacked([
        roleKey,
        testContractAddress,
        "0x",
        ExecutionOptions.None,
      ]);

      // 1-3 byte calldata still reverts FunctionSignatureTooShort
      await viem.assertions.revertWithCustomError(
        roles.write.execTransactionFromModule(
          [testContractAddress, 0n, "0x1234", 0],
          { account: member.account },
        ),
        roles,
        "FunctionSignatureTooShort",
      );

      // ETH value still reverts SendNotAllowed
      await owner.sendTransaction({
        to: avatar.address,
        value: parseEther("1"),
      });
      await viem.assertions.revertWithCustomError(
        roles.write.execTransactionFromModule(
          [testContractAddress, parseEther("0.1"), "0x", 0],
          { account: member.account },
        ),
        roles,
        "SendNotAllowed",
      );

      // DelegateCall still reverts DelegateCallNotAllowed
      await viem.assertions.revertWithCustomError(
        roles.write.execTransactionFromModule(
          [testContractAddress, 0n, "0x", 1],
          { account: member.account },
        ),
        roles,
        "DelegateCallNotAllowed",
      );
    });

    it("invokes Evaluator via STATICCALL so a state-mutating Evaluator reverts", async () => {
      const { roles, owner, member, testContractAddress, roleKey } =
        await loadFixture(setup);

      const mutating = await viem.deployContract("TestMutatingEvaluator");
      await roles.write.setEvaluator([mutating.address], {
        account: owner.account,
      });
      await roles.write.allowTargetPacked([
        roleKey,
        testContractAddress,
        "0x",
        ExecutionOptions.None,
      ]);

      await viem.assertions.revert(
        roles.write.execTransactionFromModule(
          [
            testContractAddress,
            0n,
            encodeFunctionData({ abi, functionName: "doNothing" }),
            0,
          ],
          { account: member.account },
        ),
      );

      assert.equal(await mutating.read.counter(), 0n);
    });

    it("propagates Evaluator reverts and rejects malformed return data", async () => {
      const { roles, owner, member, testContractAddress, roleKey } =
        await loadFixture(setup);

      await roles.write.allowTargetPacked([
        roleKey,
        testContractAddress,
        "0x",
        ExecutionOptions.None,
      ]);

      const reverting = await viem.deployContract("TestRevertingEvaluator");
      await roles.write.setEvaluator([reverting.address], {
        account: owner.account,
      });

      await viem.assertions.revertWithCustomError(
        roles.write.execTransactionFromModule(
          [
            testContractAddress,
            0n,
            encodeFunctionData({ abi, functionName: "doNothing" }),
            0,
          ],
          { account: member.account },
        ),
        reverting,
        "IntentionalEvaluatorRevert",
      );

      const malformed = await viem.deployContract(
        "TestMalformedReturnEvaluator",
      );
      await roles.write.setEvaluator([malformed.address], {
        account: owner.account,
      });

      await viem.assertions.revert(
        roles.write.execTransactionFromModule(
          [
            testContractAddress,
            0n,
            encodeFunctionData({ abi, functionName: "doNothing" }),
            0,
          ],
          { account: member.account },
        ),
      );
    });

    describe("a forging Evaluator", () => {
      async function setupWithForgingEvaluator() {
        const ctx = await setup();
        const forging = await viem.deployContract(
          "TestForgingConsumptionEvaluator",
        );
        await ctx.roles.write.setEvaluator([forging.address], {
          account: ctx.owner.account,
        });
        await ctx.roles.write.allowTargetPacked([
          ctx.roleKey,
          ctx.testContractAddress,
          "0x",
          ExecutionOptions.None,
        ]);

        const allowanceKey = keccak256(toBytes("FORGE_TEST"));
        // refills 10 every 600s
        await ctx.roles.write.setAllowance([
          allowanceKey,
          100n,
          1000n,
          10n,
          600n,
          0n,
        ]);

        const exec = () =>
          ctx.roles.write.execTransactionFromModule(
            [
              ctx.testContractAddress,
              0n,
              encodeFunctionData({ abi, functionName: "doNothing" }),
              0,
            ],
            { account: ctx.member.account },
          );

        return { ...ctx, forging, allowanceKey, exec };
      }

      it("cannot set the balance or timestamp settlement stores", async () => {
        const { roles, forging, allowanceKey, exec } = await loadFixture(
          setupWithForgingEvaluator,
        );
        const before = await roles.read.allowances([allowanceKey]);

        await forging.write.setForged([
          [{ allowanceKey, balance: 999999n, consumed: 5n, timestamp: 12345n }],
        ]);
        // two periods later: Core accrues 120 itself, from storage
        await time.setNextBlockTimestamp(before[4] + 1200n);
        await viem.assertions.emitWithArgs(exec(), roles, "ConsumeAllowance", [
          allowanceKey,
          5n,
          115n,
        ]);

        assert.deepEqual(await roles.read.allowances([allowanceKey]), [
          10n,
          1000n,
          600n,
          115n,
          before[4] + 1200n,
        ]);
      });

      const OVERSPENDS = {
        "a consumption above the stored balance, whatever balance it claims": (
          allowanceKey: Hex,
        ) => [
          { allowanceKey, balance: 999999n, consumed: 101n, timestamp: 0n },
        ],
        "entries for one key that together exceed its balance": (
          allowanceKey: Hex,
        ) => [
          { allowanceKey, balance: 100n, consumed: 60n, timestamp: 0n },
          { allowanceKey, balance: 100n, consumed: 60n, timestamp: 0n },
        ],
        "a consumption of an allowance never set": () => [
          {
            allowanceKey: keccak256(toBytes("NEVER_SET")),
            balance: 999999n,
            consumed: 1n,
            timestamp: 0n,
          },
        ],
      };

      for (const [what, forged] of Object.entries(OVERSPENDS))
        it(`reverts AllowanceExceeded on ${what}`, async () => {
          const { roles, forging, allowanceKey, exec } = await loadFixture(
            setupWithForgingEvaluator,
          );
          const before = await roles.read.allowances([allowanceKey]);
          const consumptions = forged(allowanceKey);

          await forging.write.setForged([consumptions]);
          await viem.assertions.revertWithCustomErrorWithArgs(
            exec(),
            roles,
            "AllowanceExceeded",
            [consumptions[consumptions.length - 1].allowanceKey],
          );
          assert.deepEqual(await roles.read.allowances([allowanceKey]), before);
        });
    });

    it("handles unknown uint8 Status, Operator, and Encoding values from a future Evaluator without Panic(0x21)", async () => {
      const { roles, evaluator, owner, member, testContractAddress, roleKey } =
        await loadFixture(setup);

      // Current Evaluator bounds-checks raw uint8 values cleanly (not Panic 0x21)
      await viem.assertions.revertWithCustomErrorWithArgs(
        roles.read.packConditions([
          [
            {
              parent: 0,
              paramType: 99,
              operator: Operator.Pass,
              compValue: "0x",
            },
          ],
        ]),
        evaluator,
        "UnsuitableParameterType",
        [0n],
      );

      await viem.assertions.revertWithCustomErrorWithArgs(
        roles.read.packConditions([
          [
            {
              parent: 0,
              paramType: Encoding.None,
              operator: 99,
              compValue: "0x",
            },
          ],
        ]),
        evaluator,
        "UnsupportedOperator",
        [0n],
      );

      // Install a future Evaluator that accepts new Encoding/Operator codes
      // and returns a new Status code (200)
      const future = await viem.deployContract("TestFutureEvaluator");
      await roles.write.setEvaluator([future.address], {
        account: owner.account,
      });

      const futureConditions: ConditionFlat[] = [
        {
          parent: 0,
          paramType: 99,
          operator: 200,
          compValue: "0x",
        },
      ];
      assert.equal(
        await roles.read.packConditions([futureConditions]),
        "0x63c8",
      );

      await roles.write.allowTarget([
        roleKey,
        testContractAddress,
        futureConditions,
        ExecutionOptions.None,
      ]);

      await viem.assertions.revertWithCustomErrorWithArgs(
        roles.write.execTransactionFromModule(
          [
            testContractAddress,
            0n,
            encodeFunctionData({ abi, functionName: "doNothing" }),
            0,
          ],
          { account: member.account },
        ),
        roles,
        "ConditionViolation",
        [200, 3n, 36n],
      );
    });
  });

  describe("shared stateless Evaluator across multiple Core instances", () => {
    it("isolates avatar and allowance state per Core when sharing one Evaluator", async () => {
      const { owner, member, testContractAddress, evaluatorAddress } =
        await loadFixture(setup);

      const avatar1 = await viem.deployContract("TestAvatar");
      const avatar2 = await viem.deployContract("TestAvatar");
      const avatar1Address = avatar1.address;
      const avatar2Address = avatar2.address;

      const roles1 = await deployRolesMod(
        owner.account.address,
        avatar1Address,
        avatar1Address,
        evaluatorAddress,
      );
      const roles2 = await deployRolesMod(
        owner.account.address,
        avatar2Address,
        avatar2Address,
        evaluatorAddress,
      );

      const roleKey = keccak256(toBytes("SHARED_ROLE"));
      const allowanceKey = keccak256(toBytes("SHARED_ALLOWANCE"));
      const fnAddrSelector = toFunctionSelector("fn(address)");
      const fnUintSelector = toFunctionSelector("oneParamStatic(uint256)");

      for (const mod of [roles1, roles2]) {
        await mod.write.grantRole(
          [member.account.address, roleKey, 0n, 0n, 0n],
          { account: owner.account },
        );
        await mod.write.setDefaultRole([member.account.address, roleKey], {
          account: owner.account,
        });
        await mod.write.scopeTarget([roleKey, testContractAddress], {
          account: owner.account,
        });
        await mod.write.allowFunction(
          [
            roleKey,
            testContractAddress,
            fnAddrSelector,
            flattenCondition({
              paramType: Encoding.AbiEncoded,
              operator: Operator.Matches,
              children: [
                {
                  paramType: Encoding.Static,
                  operator: Operator.EqualToAvatar,
                },
              ],
            }),
            ExecutionOptions.None,
          ],
          { account: owner.account },
        );
        await mod.write.allowFunction(
          [
            roleKey,
            testContractAddress,
            fnUintSelector,
            flattenCondition({
              paramType: Encoding.AbiEncoded,
              operator: Operator.Matches,
              children: [
                {
                  paramType: Encoding.Static,
                  operator: Operator.WithinAllowance,
                  compValue: allowanceKey,
                },
              ],
            }),
            ExecutionOptions.None,
          ],
          { account: owner.account },
        );
      }

      // Different allowance balances on roles1 (50) and roles2 (200)
      await roles1.write.setAllowance([allowanceKey, 50n, 0n, 0n, 0n, 0n], {
        account: owner.account,
      });
      await roles2.write.setAllowance([allowanceKey, 200n, 0n, 0n, 0n, 0n], {
        account: owner.account,
      });

      // EqualToAvatar checks each Core's own avatar
      await roles1.write.execTransactionFromModule(
        [
          testContractAddress,
          0n,
          encodeFunctionData({
            abi,
            functionName: "fn",
            args: [avatar1Address],
          }),
          0,
        ],
        { account: member.account },
      );
      await viem.assertions.revertWithCustomError(
        roles1.write.execTransactionFromModule(
          [
            testContractAddress,
            0n,
            encodeFunctionData({
              abi,
              functionName: "fn",
              args: [avatar2Address],
            }),
            0,
          ],
          { account: member.account },
        ),
        roles1,
        "ConditionViolation",
      );

      await roles2.write.execTransactionFromModule(
        [
          testContractAddress,
          0n,
          encodeFunctionData({
            abi,
            functionName: "fn",
            args: [avatar2Address],
          }),
          0,
        ],
        { account: member.account },
      );
      await viem.assertions.revertWithCustomError(
        roles2.write.execTransactionFromModule(
          [
            testContractAddress,
            0n,
            encodeFunctionData({
              abi,
              functionName: "fn",
              args: [avatar1Address],
            }),
            0,
          ],
          { account: member.account },
        ),
        roles2,
        "ConditionViolation",
      );

      // WithinAllowance reads and settles each Core's own allowance balance
      await viem.assertions.revertWithCustomError(
        roles1.write.execTransactionFromModule(
          [
            testContractAddress,
            0n,
            encodeFunctionData({
              abi,
              functionName: "oneParamStatic",
              args: [100n],
            }),
            0,
          ],
          { account: member.account },
        ),
        roles1,
        "ConditionViolation",
      );

      await roles2.write.execTransactionFromModule(
        [
          testContractAddress,
          0n,
          encodeFunctionData({
            abi,
            functionName: "oneParamStatic",
            args: [100n],
          }),
          0,
        ],
        { account: member.account },
      );

      assert.equal((await roles1.read.allowances([allowanceKey]))[3], 50n);
      assert.equal((await roles2.read.allowances([allowanceKey]))[3], 100n);
    });
  });
});
