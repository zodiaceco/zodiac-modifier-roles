import { expect } from "chai";
import { hexlify, Interface, randomBytes, ZeroAddress, ZeroHash } from "ethers";
import { network } from "hardhat";

import {
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
const { ethers, networkHelpers } = connection;
const { loadFixture, time } = networkHelpers;
const { deployEvaluator, deployRolesMod } = createSetup(connection);

const iface = new Interface([
  "function doNothing()",
  "function oneParamStatic(uint256)",
  "function fn(address)",
]);

describe("Core / Evaluator split", () => {
  after(async () => {
    await connection.close();
  });

  async function setup() {
    const [owner, member, nonMember, relayer] = await ethers.getSigners();

    const Avatar = await ethers.getContractFactory("TestAvatar");
    const avatar = await Avatar.deploy();
    const avatarAddress = await avatar.getAddress();

    const TestContract = await ethers.getContractFactory("TestContract");
    const testContract = await TestContract.deploy();
    const testContractAddress = await testContract.getAddress();

    const evaluator = await deployEvaluator();
    const evaluatorAddress = await evaluator.getAddress();

    const roles = await deployRolesMod(
      owner.address,
      avatarAddress,
      avatarAddress,
      evaluatorAddress,
    );

    const roleKey = hexlify(randomBytes(32));

    await roles.connect(owner).grantRole(member.address, roleKey, 0, 0, 0);
    await roles.connect(owner).setDefaultRole(member.address, roleKey);
    await roles.connect(owner).scopeTarget(roleKey, testContractAddress);

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
      roles: roles.connect(owner),
      roleKey,
    };
  }

  describe("evaluator configuration & hot-swapping", () => {
    it("sets the initial evaluator during deployment and emits SetEvaluator", async () => {
      const { owner, avatarAddress, evaluatorAddress } =
        await loadFixture(setup);

      const roles = await deployRolesMod(
        owner.address,
        avatarAddress,
        avatarAddress,
        evaluatorAddress,
      );

      expect(await roles.evaluator()).to.equal(evaluatorAddress);
      await expect(roles.deploymentTransaction())
        .to.emit(roles, "SetEvaluator")
        .withArgs(evaluatorAddress);
    });

    it("reverts ZeroAddressNotAllowed if initial evaluator is address(0)", async () => {
      const { owner, avatarAddress } = await loadFixture(setup);

      await expect(
        deployRolesMod(
          owner.address,
          avatarAddress,
          avatarAddress,
          ZeroAddress,
        ),
      ).to.be.revertedWithCustomError(
        await ethers.getContractFactory("Roles"),
        "ZeroAddressNotAllowed",
      );
    });

    it("swaps the evaluator, emitting SetEvaluator, and rejects the zero address", async () => {
      const { roles, owner } = await loadFixture(setup);

      const alt = await deployEvaluator();
      const altAddress = await alt.getAddress();

      await expect(
        roles.connect(owner).setEvaluator(ZeroAddress),
      ).to.be.revertedWithCustomError(roles, "ZeroAddressNotAllowed");

      await expect(roles.connect(owner).setEvaluator(altAddress))
        .to.emit(roles, "SetEvaluator")
        .withArgs(altAddress);

      expect(await roles.evaluator()).to.equal(altAddress);
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

      const selector = iface.getFunction("oneParamStatic")!.selector;
      const allowanceKey = ethers.id("HOT_SWAP_ALLOWANCE");

      await roles.setAllowance(allowanceKey, 100, 0, 0, 0, 0);
      await roles.allowFunction(
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
      );

      // Works with initial evaluator and consumes 40
      await roles
        .connect(member)
        .execTransactionFromModule(
          testContractAddress,
          0,
          iface.encodeFunctionData("oneParamStatic", [40]),
          0,
        );
      expect((await roles.allowances(allowanceKey)).balance).to.equal(60);

      // Swap to always-deny evaluator: same permission now fails without redeploying Core
      const Deny = await ethers.getContractFactory("TestAlwaysDenyEvaluator");
      const deny = await Deny.deploy();
      await roles.connect(owner).setEvaluator(await deny.getAddress());

      await expect(
        roles
          .connect(member)
          .execTransactionFromModule(
            testContractAddress,
            0,
            iface.encodeFunctionData("oneParamStatic", [10]),
            0,
          ),
      )
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(ConditionViolationStatus.ParameterNotAllowed, 7, 4);

      // Swap back to a freshly deployed real Evaluator: membership, permission, and allowance balance (60) remain intact
      const fresh = await deployEvaluator();
      expect(await fresh.getAddress()).to.not.equal(evaluatorAddress);
      await roles.connect(owner).setEvaluator(await fresh.getAddress());

      // 70 > remaining 60 fails
      await expect(
        roles
          .connect(member)
          .execTransactionFromModule(
            testContractAddress,
            0,
            iface.encodeFunctionData("oneParamStatic", [70]),
            0,
          ),
      ).to.be.revertedWithCustomError(roles, "ConditionViolation");

      // 60 <= remaining 60 succeeds
      await roles
        .connect(member)
        .execTransactionFromModule(
          testContractAddress,
          0,
          iface.encodeFunctionData("oneParamStatic", [60]),
          0,
        );
      expect((await roles.allowances(allowanceKey)).balance).to.equal(0);
    });

    it("reverts EvaluatorNotAContract if evaluator has no code", async () => {
      const { roles, owner, member, nonMember, testContractAddress, roleKey } =
        await loadFixture(setup);

      await roles.allowTargetPacked(
        roleKey,
        testContractAddress,
        "0x",
        ExecutionOptions.None,
      );
      await roles.connect(owner).setEvaluator(nonMember.address);

      await expect(
        roles
          .connect(member)
          .execTransactionFromModule(
            testContractAddress,
            0,
            iface.encodeFunctionData("doNothing"),
            0,
          ),
      )
        .to.be.revertedWithCustomError(roles, "EvaluatorNotAContract")
        .withArgs(nonMember.address);

      await expect(
        roles.packConditions([
          {
            parent: 0,
            paramType: Encoding.None,
            operator: Operator.Pass,
            compValue: "0x",
          },
        ]),
      ).to.be.revertedWithoutReason(ethers);
    });

    describe("validated setters pack through the Evaluator, *Packed setters bypass it", () => {
      async function setupWithRevertingEvaluator() {
        const ctx = await setup();
        const Reverting = await ethers.getContractFactory(
          "TestRevertingEvaluator",
        );
        const reverting = await Reverting.deploy();
        await ctx.roles
          .connect(ctx.owner)
          .setEvaluator(await reverting.getAddress());
        return { ...ctx, reverting };
      }

      const selector = iface.getFunction("doNothing")!.selector;
      type Ctx = Awaited<ReturnType<typeof setupWithRevertingEvaluator>>;
      type Conditions = ReturnType<typeof flattenCondition>;

      const VALIDATED: Record<string, (c: Ctx, conditions: Conditions) => any> =
        {
          packConditions: ({ roles }, conditions) =>
            roles.packConditions(conditions),
          allowTarget: ({ roles, roleKey, testContractAddress }, conditions) =>
            roles.allowTarget(
              roleKey,
              testContractAddress,
              conditions,
              ExecutionOptions.None,
            ),
          allowFunction: (
            { roles, roleKey, testContractAddress },
            conditions,
          ) =>
            roles.allowFunction(
              roleKey,
              testContractAddress,
              selector,
              conditions,
              ExecutionOptions.None,
            ),
          allowFunctionGlobally: ({ roles, roleKey }, conditions) =>
            roles.allowFunctionGlobally(roleKey, selector, conditions),
        };

      // any bytes: a *Packed setter stores them without calling the
      // Evaluator. Each is listed with its arguments, which are also those
      // of the event it emits.
      const BUFFER = "0x00";
      const PACKED = {
        allowTargetPacked: ({ roleKey, testContractAddress }: Ctx) =>
          [
            roleKey,
            testContractAddress,
            BUFFER,
            ExecutionOptions.None,
          ] as const,
        allowFunctionPacked: ({ roleKey, testContractAddress }: Ctx) =>
          [
            roleKey,
            testContractAddress,
            selector,
            BUFFER,
            ExecutionOptions.None,
          ] as const,
        allowFunctionGloballyPacked: ({ roleKey }: Ctx) =>
          [roleKey, selector, BUFFER] as const,
      };
      const EVENTS = {
        allowTargetPacked: "AllowTarget",
        allowFunctionPacked: "AllowFunction",
        allowFunctionGloballyPacked: "AllowFunctionGlobally",
      } as const;

      for (const [name, call] of Object.entries(VALIDATED))
        it(`${name} packs conditions through the Evaluator, and none without calling it`, async () => {
          const ctx = await loadFixture(setupWithRevertingEvaluator);

          await expect(
            call(
              ctx,
              flattenCondition({
                paramType: Encoding.None,
                operator: Operator.Pass,
              }),
            ),
          ).to.be.revertedWithCustomError(
            ctx.reverting,
            "IntentionalEvaluatorRevert",
          );
          // empty conditions skip packing: stored (or returned) as empty
          const result = await call(ctx, []);
          if (name === "packConditions") expect(result).to.equal("0x");
        });

      for (const name of Object.keys(PACKED) as (keyof typeof PACKED)[])
        it(`${name} stores the buffer without calling the Evaluator`, async () => {
          const ctx = await loadFixture(setupWithRevertingEvaluator);
          const args = PACKED[name](ctx);

          // the buffer is emitted as given, not as an Evaluator packed it
          await expect((ctx.roles[name] as any)(...args))
            .to.emit(ctx.roles, EVENTS[name])
            .withArgs(...args);
        });
    });
  });

  describe("authentication, independent of the Evaluator", () => {
    async function setupWithAlwaysAllowEvaluator() {
      const ctx = await setup();
      const AlwaysAllow = await ethers.getContractFactory(
        "TestAlwaysAllowEvaluator",
      );
      const alwaysAllow = await AlwaysAllow.deploy();
      await ctx.roles
        .connect(ctx.owner)
        .setEvaluator(await alwaysAllow.getAddress());

      await ctx.roles.allowTargetPacked(
        ctx.roleKey,
        ctx.testContractAddress,
        "0x",
        ExecutionOptions.Both,
      );

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
        to: await roles.getAddress(),
        data: await encodeEntrypoint(
          roles,
          entrypoint,
          {
            to,
            data: iface.encodeFunctionData("doNothing"),
            roleKey,
            deadline,
          },
          module,
        ),
      });
    }

    const REJECTIONS: {
      who: string;
      error: string;
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
          await roles.enableModule(nonMember.address);
          await roles.setDefaultRole(nonMember.address, roleKey);
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
          await roles.setDefaultRole(member.address, ZeroHash);
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

        await expect(execThrough(ctx, entrypoint, ctx.member)).to.not.be.revert(
          ethers,
        );
      });

    for (const { who, error, entrypoints, arrange } of REJECTIONS)
      for (const entrypoint of entrypoints)
        it(`rejects ${who} on ${entrypoint} with ${error}`, async () => {
          const ctx = await loadFixture(setupWithAlwaysAllowEvaluator);
          const { module, deadline } = await arrange(ctx);

          await expect(
            execThrough(ctx, entrypoint, module, deadline),
          ).to.be.revertedWithCustomError(ctx.roles, error);
        });

    it("enforces zero role, validity window, and finite uses", async () => {
      const { roles, owner, nonMember, testContractAddress, roleKey } =
        await loadFixture(setupWithAlwaysAllowEvaluator);

      const data = iface.encodeFunctionData("doNothing");
      const exec = (role: string) =>
        roles
          .connect(nonMember)
          .execTransactionWithRole(testContractAddress, 0, data, 0, role);

      // Zero role is always rejected
      await roles
        .connect(owner)
        .grantRole(nonMember.address, ZeroHash, 0, 0, 0);
      await expect(exec(ZeroHash)).to.be.revertedWithCustomError(
        roles,
        "NoMembership",
      );

      // Future start timestamp rejected
      const now = await time.latest();
      await roles
        .connect(owner)
        .grantRole(nonMember.address, roleKey, now + 1000, now + 2000, 1);
      await expect(exec(roleKey)).to.be.revertedWithCustomError(
        roles,
        "MembershipNotYetValid",
      );

      // Advance into window: 1 use succeeds, 2nd call rejected
      await time.increaseTo(now + 1000);
      await exec(roleKey);
      await expect(exec(roleKey)).to.be.revertedWithCustomError(
        roles,
        "NoMembership",
      );

      // Expired membership rejected
      await roles
        .connect(owner)
        .grantRole(nonMember.address, roleKey, now, now + 1500, 0);
      await time.increaseTo(now + 1501);
      await expect(exec(roleKey)).to.be.revertedWithCustomError(
        roles,
        "MembershipExpired",
      );
    });
  });

  describe("Core invariants independent of Evaluator", () => {
    it("enforces scopeConfig lookup, ExecutionOptions, and short calldata even with always-allow Evaluator", async () => {
      const { roles, owner, member, avatar, testContractAddress, roleKey } =
        await loadFixture(setup);

      const AlwaysAllow = await ethers.getContractFactory(
        "TestAlwaysAllowEvaluator",
      );
      const alwaysAllow = await AlwaysAllow.deploy();
      await roles.connect(owner).setEvaluator(await alwaysAllow.getAddress());

      // Unpermitted selector still reverts TransactionNotAllowed
      await expect(
        roles
          .connect(member)
          .execTransactionFromModule(
            testContractAddress,
            0,
            iface.encodeFunctionData("doNothing"),
            0,
          ),
      ).to.be.revertedWithCustomError(roles, "TransactionNotAllowed");

      // Allow target with ExecutionOptions.None
      await roles.allowTargetPacked(
        roleKey,
        testContractAddress,
        "0x",
        ExecutionOptions.None,
      );

      // 1-3 byte calldata still reverts FunctionSignatureTooShort
      await expect(
        roles
          .connect(member)
          .execTransactionFromModule(testContractAddress, 0, "0x1234", 0),
      ).to.be.revertedWithCustomError(roles, "FunctionSignatureTooShort");

      // ETH value still reverts SendNotAllowed
      await owner.sendTransaction({
        to: await avatar.getAddress(),
        value: ethers.parseEther("1"),
      });
      await expect(
        roles
          .connect(member)
          .execTransactionFromModule(
            testContractAddress,
            ethers.parseEther("0.1"),
            "0x",
            0,
          ),
      ).to.be.revertedWithCustomError(roles, "SendNotAllowed");

      // DelegateCall still reverts DelegateCallNotAllowed
      await expect(
        roles
          .connect(member)
          .execTransactionFromModule(testContractAddress, 0, "0x", 1),
      ).to.be.revertedWithCustomError(roles, "DelegateCallNotAllowed");
    });

    it("invokes Evaluator via STATICCALL so a state-mutating Evaluator reverts", async () => {
      const { roles, owner, member, testContractAddress, roleKey } =
        await loadFixture(setup);

      const Mutating = await ethers.getContractFactory("TestMutatingEvaluator");
      const mutating = await Mutating.deploy();
      await roles.connect(owner).setEvaluator(await mutating.getAddress());
      await roles.allowTargetPacked(
        roleKey,
        testContractAddress,
        "0x",
        ExecutionOptions.None,
      );

      await expect(
        roles
          .connect(member)
          .execTransactionFromModule(
            testContractAddress,
            0,
            iface.encodeFunctionData("doNothing"),
            0,
          ),
      ).to.be.revert(ethers);

      expect(await mutating.counter()).to.equal(0);
    });

    it("propagates Evaluator reverts and rejects malformed return data", async () => {
      const { roles, owner, member, testContractAddress, roleKey } =
        await loadFixture(setup);

      await roles.allowTargetPacked(
        roleKey,
        testContractAddress,
        "0x",
        ExecutionOptions.None,
      );

      const Reverting = await ethers.getContractFactory(
        "TestRevertingEvaluator",
      );
      const reverting = await Reverting.deploy();
      await roles.connect(owner).setEvaluator(await reverting.getAddress());

      await expect(
        roles
          .connect(member)
          .execTransactionFromModule(
            testContractAddress,
            0,
            iface.encodeFunctionData("doNothing"),
            0,
          ),
      ).to.be.revertedWithCustomError(reverting, "IntentionalEvaluatorRevert");

      const Malformed = await ethers.getContractFactory(
        "TestMalformedReturnEvaluator",
      );
      const malformed = await Malformed.deploy();
      await roles.connect(owner).setEvaluator(await malformed.getAddress());

      await expect(
        roles
          .connect(member)
          .execTransactionFromModule(
            testContractAddress,
            0,
            iface.encodeFunctionData("doNothing"),
            0,
          ),
      ).to.be.revert(ethers);
    });

    describe("a forging Evaluator", () => {
      async function setupWithForgingEvaluator() {
        const ctx = await setup();
        const Forging = await ethers.getContractFactory(
          "TestForgingConsumptionEvaluator",
        );
        const forging = await Forging.deploy();
        await ctx.roles
          .connect(ctx.owner)
          .setEvaluator(await forging.getAddress());
        await ctx.roles.allowTargetPacked(
          ctx.roleKey,
          ctx.testContractAddress,
          "0x",
          ExecutionOptions.None,
        );

        const allowanceKey = ethers.id("FORGE_TEST");
        // refills 10 every 600s
        await ctx.roles.setAllowance(allowanceKey, 100, 1000, 10, 600, 0);

        const exec = () =>
          ctx.roles
            .connect(ctx.member)
            .execTransactionFromModule(
              ctx.testContractAddress,
              0,
              iface.encodeFunctionData("doNothing"),
              0,
            );

        return { ...ctx, forging, allowanceKey, exec };
      }

      it("cannot set the balance or timestamp settlement stores", async () => {
        const { roles, forging, allowanceKey, exec } = await loadFixture(
          setupWithForgingEvaluator,
        );
        const before = await roles.allowances(allowanceKey);

        await forging.setForged([
          { allowanceKey, balance: 999999n, consumed: 5n, timestamp: 12345n },
        ]);
        // two periods later: Core accrues 120 itself, from storage
        await time.setNextBlockTimestamp(before.timestamp + 1200n);
        await expect(exec())
          .to.emit(roles, "ConsumeAllowance")
          .withArgs(allowanceKey, 5, 115);

        expect(await roles.allowances(allowanceKey)).to.deep.equal([
          10n,
          1000n,
          600n,
          115n,
          before.timestamp + 1200n,
        ]);
      });

      const OVERSPENDS = {
        "a consumption above the stored balance, whatever balance it claims": (
          allowanceKey: string,
        ) => [
          { allowanceKey, balance: 999999n, consumed: 101n, timestamp: 0n },
        ],
        "entries for one key that together exceed its balance": (
          allowanceKey: string,
        ) => [
          { allowanceKey, balance: 100n, consumed: 60n, timestamp: 0n },
          { allowanceKey, balance: 100n, consumed: 60n, timestamp: 0n },
        ],
        "a consumption of an allowance never set": () => [
          {
            allowanceKey: ethers.id("NEVER_SET"),
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
          const before = await roles.allowances(allowanceKey);
          const consumptions = forged(allowanceKey);

          await forging.setForged(consumptions);
          await expect(exec())
            .to.be.revertedWithCustomError(roles, "AllowanceExceeded")
            .withArgs(consumptions[consumptions.length - 1].allowanceKey);
          expect(await roles.allowances(allowanceKey)).to.deep.equal(before);
        });
    });

    it("handles unknown uint8 Status, Operator, and Encoding values from a future Evaluator without Panic(0x21)", async () => {
      const { roles, evaluator, owner, member, testContractAddress, roleKey } =
        await loadFixture(setup);

      // Current Evaluator bounds-checks raw uint8 values cleanly (not Panic 0x21)
      await expect(
        roles.packConditions([
          {
            parent: 0,
            paramType: 99,
            operator: Operator.Pass,
            compValue: "0x",
          },
        ]),
      )
        .to.be.revertedWithCustomError(evaluator, "UnsuitableParameterType")
        .withArgs(0);

      await expect(
        roles.packConditions([
          {
            parent: 0,
            paramType: Encoding.None,
            operator: 99,
            compValue: "0x",
          },
        ]),
      )
        .to.be.revertedWithCustomError(evaluator, "UnsupportedOperator")
        .withArgs(0);

      // Install a future Evaluator that accepts new Encoding/Operator codes
      // and returns a new Status code (200)
      const Future = await ethers.getContractFactory("TestFutureEvaluator");
      const future = await Future.deploy();
      await roles.connect(owner).setEvaluator(await future.getAddress());

      const futureConditions = [
        {
          parent: 0,
          paramType: 99,
          operator: 200,
          compValue: "0x",
        },
      ];

      expect(await roles.packConditions(futureConditions)).to.equal("0x63c8");

      await expect(
        roles.allowTarget(
          roleKey,
          testContractAddress,
          futureConditions,
          ExecutionOptions.None,
        ),
      ).to.not.be.revert(ethers);

      await expect(
        roles
          .connect(member)
          .execTransactionFromModule(
            testContractAddress,
            0,
            iface.encodeFunctionData("doNothing"),
            0,
          ),
      )
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(200, 3, 36);
    });
  });

  describe("shared stateless Evaluator across multiple Core instances", () => {
    it("isolates avatar and allowance state per Core when sharing one Evaluator", async () => {
      const { owner, member, testContractAddress, evaluatorAddress } =
        await loadFixture(setup);

      const Avatar = await ethers.getContractFactory("TestAvatar");
      const avatar1 = await Avatar.deploy();
      const avatar2 = await Avatar.deploy();
      const avatar1Address = await avatar1.getAddress();
      const avatar2Address = await avatar2.getAddress();

      const roles1 = await deployRolesMod(
        owner.address,
        avatar1Address,
        avatar1Address,
        evaluatorAddress,
      );
      const roles2 = await deployRolesMod(
        owner.address,
        avatar2Address,
        avatar2Address,
        evaluatorAddress,
      );

      const roleKey = ethers.id("SHARED_ROLE");
      const allowanceKey = ethers.id("SHARED_ALLOWANCE");
      const fnAddrSelector = iface.getFunction("fn")!.selector;
      const fnUintSelector = iface.getFunction("oneParamStatic")!.selector;

      for (const mod of [roles1, roles2]) {
        await mod.connect(owner).grantRole(member.address, roleKey, 0, 0, 0);
        await mod.connect(owner).setDefaultRole(member.address, roleKey);
        await mod.connect(owner).scopeTarget(roleKey, testContractAddress);
        await mod.connect(owner).allowFunction(
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
        );
        await mod.connect(owner).allowFunction(
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
        );
      }

      // Different allowance balances on roles1 (50) and roles2 (200)
      await roles1.connect(owner).setAllowance(allowanceKey, 50, 0, 0, 0, 0);
      await roles2.connect(owner).setAllowance(allowanceKey, 200, 0, 0, 0, 0);

      // EqualToAvatar checks each Core's own avatar
      await roles1
        .connect(member)
        .execTransactionFromModule(
          testContractAddress,
          0,
          iface.encodeFunctionData("fn", [avatar1Address]),
          0,
        );
      await expect(
        roles1
          .connect(member)
          .execTransactionFromModule(
            testContractAddress,
            0,
            iface.encodeFunctionData("fn", [avatar2Address]),
            0,
          ),
      ).to.be.revertedWithCustomError(roles1, "ConditionViolation");

      await roles2
        .connect(member)
        .execTransactionFromModule(
          testContractAddress,
          0,
          iface.encodeFunctionData("fn", [avatar2Address]),
          0,
        );
      await expect(
        roles2
          .connect(member)
          .execTransactionFromModule(
            testContractAddress,
            0,
            iface.encodeFunctionData("fn", [avatar1Address]),
            0,
          ),
      ).to.be.revertedWithCustomError(roles2, "ConditionViolation");

      // WithinAllowance reads and settles each Core's own allowance balance
      await expect(
        roles1
          .connect(member)
          .execTransactionFromModule(
            testContractAddress,
            0,
            iface.encodeFunctionData("oneParamStatic", [100]),
            0,
          ),
      ).to.be.revertedWithCustomError(roles1, "ConditionViolation");

      await roles2
        .connect(member)
        .execTransactionFromModule(
          testContractAddress,
          0,
          iface.encodeFunctionData("oneParamStatic", [100]),
          0,
        );

      expect((await roles1.allowances(allowanceKey)).balance).to.equal(50);
      expect((await roles2.allowances(allowanceKey)).balance).to.equal(100);
    });
  });
});
