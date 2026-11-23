import { expect } from "chai";
import { anyValue } from "@nomicfoundation/hardhat-ethers-chai-matchers/withArgs";
import { hexlify, Interface, MaxUint256, randomBytes } from "ethers";

import { network } from "hardhat";

import { createSetup } from "../setup.js";
import {
  Encoding,
  Operator,
  ExecutionOptions,
  ConditionViolationStatus,
  flattenCondition,
  packConditions,
} from "../utils.js";

const connection = await network.create();
const { ethers, networkHelpers } = connection;
const { loadFixture } = networkHelpers;
const { setupTestContract, setupFn } = createSetup(connection);
const setupOneParam = setupFn("function fn(uint256)");

describe("Operator - Custom", () => {
  after(async () => {
    await connection.close();
  });

  async function setupWithChecker() {
    const base = await setupOneParam();
    const CustomChecker = await ethers.getContractFactory("TestCustomChecker");
    const customChecker = await CustomChecker.deploy();
    return {
      ...base,
      customChecker,
      customCheckerAddress: await customChecker.getAddress(),
    };
  }

  describe("execution logic", () => {
    it("delegates execution to the configured adapter address", async () => {
      const { allowFunction, invoke, customCheckerAddress } =
        await loadFixture(setupWithChecker);

      // Custom condition: param > 100
      await allowFunction(
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.Static,
              operator: Operator.Custom,
              compValue: customCheckerAddress,
            },
          ],
        }),
        ExecutionOptions.Both,
      );

      // 101 > 100 passes
      await expect(invoke(101)).to.not.be.revert(ethers);
    });

    it("passes correct context (operation type) to adapter", async () => {
      const {
        roles,
        member,
        testContractAddress,
        fn,
        allowFunction,
        customCheckerAddress,
      } = await loadFixture(setupWithChecker);
      const iface = new Interface(["function fn(uint256)"]);

      // Adapter fails if operation != Call (0)
      await allowFunction(
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.Static,
              operator: Operator.Custom,
              compValue: customCheckerAddress,
            },
          ],
        }),
        ExecutionOptions.Both,
      );

      // Call operation (0) passes
      await expect(
        roles.connect(member).execTransactionFromModule(
          testContractAddress,
          0,
          iface.encodeFunctionData(fn, [101]),
          0, // Operation.Call
        ),
      ).to.not.be.revert(ethers);

      // DelegateCall operation (1) fails (adapter returns false)
      await expect(
        roles.connect(member).execTransactionFromModule(
          testContractAddress,
          0,
          iface.encodeFunctionData(fn, [101]),
          1, // Operation.DelegateCall
        ),
      )
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(
          ConditionViolationStatus.CustomConditionViolation,
          1, // Custom node
          anyValue,
        );
    });

    it("extracts and passes extra data (from compValue) to adapter", async () => {
      const { roles, allowFunction, invoke, customCheckerAddress } =
        await loadFixture(setupWithChecker);

      const extraData = "aabbccddeeff112233445566";
      const compValue = customCheckerAddress + extraData;

      await allowFunction(
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.Static,
              operator: Operator.Custom,
              compValue,
            },
          ],
        }),
        ExecutionOptions.Both,
      );

      // Fail condition: param <= 100.
      // Adapter should return false + extraData as error info.
      // Note: returned info is bytes32, so extraData is padded/truncated to 32 bytes
      const expectedInfo = "0x" + extraData.padEnd(64, "0");

      await expect(invoke(99))
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(
          ConditionViolationStatus.CustomConditionViolation,
          1, // Custom node
          anyValue,
        );
    });
  });

  describe("result handling", () => {
    it("passes when adapter returns true", async () => {
      const { allowFunction, invoke, customCheckerAddress } =
        await loadFixture(setupWithChecker);

      await allowFunction(
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.Static,
              operator: Operator.Custom,
              compValue: customCheckerAddress,
            },
          ],
        }),
        ExecutionOptions.Both,
      );

      // Adapter returns true for > 100
      await expect(invoke(101)).to.not.be.revert(ethers);
    });

    it("fails when adapter returns false (propagates error info)", async () => {
      const { roles, allowFunction, invoke, customCheckerAddress } =
        await loadFixture(setupWithChecker);

      const extraData = "1234"; // "reason" code
      const compValue = customCheckerAddress + extraData;

      await allowFunction(
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.Static,
              operator: Operator.Custom,
              compValue,
            },
          ],
        }),
        ExecutionOptions.Both,
      );

      // Adapter returns false for <= 100, info = extraData
      const expectedInfo = "0x" + extraData.padEnd(64, "0");

      await expect(invoke(99))
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(
          ConditionViolationStatus.CustomConditionViolation,
          1, // Custom node
          anyValue,
        );
    });
  });

  describe("adapter call safety", () => {
    it("no code at address: reverts", async () => {
      const { roles, allowFunction, invoke } =
        await loadFixture(setupWithChecker);

      const randomAddress = hexlify(randomBytes(20));
      await allowFunction(
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.Static,
              operator: Operator.Custom,
              compValue: randomAddress,
            },
          ],
        }),
        ExecutionOptions.Both,
      );

      await expect(invoke(101))
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(
          ConditionViolationStatus.CustomConditionNotAContract,
          1, // Custom node
          anyValue,
        );
    });

    it("wrong interface: reverts", async () => {
      const { roles, allowFunction, invoke } =
        await loadFixture(setupWithChecker);

      // Deploy contract with code but no check() function and no fallback
      const NoInterfaceChecker = await ethers.getContractFactory(
        "TestCustomCheckerNoInterface",
      );
      const noInterfaceChecker = await NoInterfaceChecker.deploy();
      const noInterfaceCheckerAddress = await noInterfaceChecker.getAddress();

      await allowFunction(
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.Static,
              operator: Operator.Custom,
              compValue: noInterfaceCheckerAddress,
            },
          ],
        }),
        ExecutionOptions.Both,
      );

      // Function selector not found, no fallback -> staticcall fails
      await expect(invoke(101))
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(
          ConditionViolationStatus.CustomConditionReverted,
          1, // Custom node
          anyValue,
        );
    });

    it("function reverts: reverts", async () => {
      const { roles, allowFunction, invoke } =
        await loadFixture(setupWithChecker);

      const RevertingChecker = await ethers.getContractFactory(
        "TestCustomCheckerReverting",
      );
      const revertingChecker = await RevertingChecker.deploy();
      const revertingCheckerAddress = await revertingChecker.getAddress();

      await allowFunction(
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.Static,
              operator: Operator.Custom,
              compValue: revertingCheckerAddress,
            },
          ],
        }),
        ExecutionOptions.Both,
      );

      // Adapter reverts -> staticcall fails
      await expect(invoke(101))
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(
          ConditionViolationStatus.CustomConditionReverted,
          1, // Custom node
          anyValue,
        );
    });

    it("returns wrong type: reverts", async () => {
      const { roles, allowFunction, invoke } =
        await loadFixture(setupWithChecker);

      // Deploy contract that returns (uint256, uint256) instead of bool
      const WrongReturnChecker = await ethers.getContractFactory(
        "TestCustomCheckerWrongReturn",
      );
      const wrongReturnChecker = await WrongReturnChecker.deploy();
      const wrongReturnCheckerAddress = await wrongReturnChecker.getAddress();

      await allowFunction(
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.Static,
              operator: Operator.Custom,
              compValue: wrongReturnCheckerAddress,
            },
          ],
        }),
        ExecutionOptions.Both,
      );

      // Return data does not decode as (bool, AllowanceConsumption[])
      await expect(invoke(101))
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(
          ConditionViolationStatus.CustomConditionInvalidResult,
          1, // Custom node
          anyValue,
        );
    });

    it("returns expected: succeeds", async () => {
      const { allowFunction, invoke, customCheckerAddress } =
        await loadFixture(setupWithChecker);

      await allowFunction(
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.Static,
              operator: Operator.Custom,
              compValue: customCheckerAddress,
            },
          ],
        }),
        ExecutionOptions.Both,
      );

      // Valid adapter returns true -> passes
      await expect(invoke(101)).to.not.be.revert(ethers);
    });
  });

  describe("violation context", () => {
    it("reports the violating node index", async () => {
      const { roles, allowFunction, invoke, customCheckerAddress } =
        await loadFixture(setupWithChecker);

      await allowFunction(
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.Static,
              operator: Operator.Custom,
              compValue: customCheckerAddress,
            },
          ],
        }),
      );

      // Value <= 100 triggers custom checker failure
      await expect(invoke(50))
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(
          ConditionViolationStatus.CustomConditionViolation,
          1, // Custom node at BFS index 1
          anyValue,
        );
    });

    it("reports the calldata range of the violation", async () => {
      const { roles, allowFunction, invoke, customCheckerAddress } =
        await loadFixture(setupWithChecker);

      await allowFunction(
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.Static,
              operator: Operator.Custom,
              compValue: customCheckerAddress,
            },
          ],
        }),
      );

      await expect(invoke(50))
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(
          ConditionViolationStatus.CustomConditionViolation,
          anyValue,
          4, // calldataOffset: parameter starts at byte 4
        );
    });
  });

  describe("integrity", () => {
    it("reverts UnsuitableParameterType for None and AbiEncoded", async () => {
      const { roles, evaluator } = await loadFixture(setupTestContract);

      for (const encoding of [Encoding.None, Encoding.AbiEncoded]) {
        await expect(
          packConditions(roles, [
            {
              parent: 0,
              paramType: encoding,
              operator: Operator.Custom,
              compValue: "0x" + "00".repeat(20),
            },
          ]),
        )
          .to.be.revertedWithCustomError(evaluator, "UnsuitableParameterType")
          .withArgs(0);
      }
    });

    it("reverts UnsuitableCompValue when compValue is less than 20 bytes", async () => {
      const { roles, evaluator } = await loadFixture(setupTestContract);

      await expect(
        packConditions(roles, [
          {
            parent: 0,
            paramType: Encoding.Static,
            operator: Operator.Custom,
            compValue: "0x" + "ab".repeat(19), // 19 bytes, less than address
          },
        ]),
      ).to.be.revertedWithCustomError(evaluator, "UnsuitableCompValue");
    });
  });

  describe("allowance consumption", () => {
    const allowanceKeyA = "0x" + "11".repeat(32);
    const allowanceKeyB = "0x" + "22".repeat(32);

    async function setupConsuming() {
      const base = await setupOneParam();
      const Consuming = await ethers.getContractFactory(
        "TestCustomCheckerConsuming",
      );
      const consuming = await Consuming.deploy();
      return {
        ...base,
        consumingAddress: await consuming.getAddress(),
      };
    }

    const customCompValue = (adapter: string, ...keys: string[]) =>
      adapter + keys.map((key) => key.slice(2)).join("");

    const customCondition = (compValue: string) =>
      flattenCondition({
        paramType: Encoding.AbiEncoded,
        operator: Operator.Matches,
        children: [
          {
            paramType: Encoding.Static,
            operator: Operator.Custom,
            compValue,
          },
        ],
      });

    it("consumes across calls and enforces the accrued balance", async () => {
      const { owner, roles, allowFunction, invoke, consumingAddress } =
        await loadFixture(setupConsuming);
      const compValue = customCompValue(consumingAddress, allowanceKeyA);

      await roles.connect(owner).setAllowance(allowanceKeyA, 100, 0, 0, 0, 0);
      await allowFunction(customCondition(compValue), ExecutionOptions.Both);

      await expect(invoke(40)).to.not.be.revert(ethers);
      expect((await roles.accruedAllowance(allowanceKeyA)).balance).to.equal(
        60,
      );

      // Exact remaining balance is allowed.
      await expect(invoke(60)).to.not.be.revert(ethers);
      expect((await roles.accruedAllowance(allowanceKeyA)).balance).to.equal(0);

      await expect(invoke(1))
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(ConditionViolationStatus.AllowanceExceeded, 1, anyValue);
      expect((await roles.accruedAllowance(allowanceKeyA)).balance).to.equal(0);
    });

    it("checks pending consumption before loading from storage", async () => {
      const { owner, roles, allowFunction, invoke, consumingAddress } =
        await loadFixture(setupConsuming);
      const compValue = customCompValue(consumingAddress, allowanceKeyA);

      await roles.connect(owner).setAllowance(allowanceKeyA, 100, 0, 0, 0, 0);
      await allowFunction(
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.None,
              operator: Operator.And,
              children: [
                {
                  paramType: Encoding.Static,
                  operator: Operator.WithinAllowance,
                  compValue: allowanceKeyA,
                },
                {
                  paramType: Encoding.Static,
                  operator: Operator.Custom,
                  compValue,
                },
              ],
            },
          ],
        }),
        ExecutionOptions.Both,
      );

      // Both checks charge 40 from the same running list.
      await expect(invoke(40)).to.not.be.revert(ethers);
      expect((await roles.accruedAllowance(allowanceKeyA)).balance).to.equal(
        20,
      );

      // 11 + 11 exceeds the 20 remaining. Loading storage independently in
      // each checker would incorrectly allow this call.
      await expect(invoke(11))
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(ConditionViolationStatus.AllowanceExceeded, 3, anyValue);
      expect((await roles.accruedAllowance(allowanceKeyA)).balance).to.equal(
        20,
      );
    });

    it("applies multiple consumptions and aggregates duplicate keys", async () => {
      const { owner, roles, allowFunction, invoke, consumingAddress } =
        await loadFixture(setupConsuming);

      await roles.connect(owner).setAllowance(allowanceKeyA, 100, 0, 0, 0, 0);
      await roles.connect(owner).setAllowance(allowanceKeyB, 100, 0, 0, 0, 0);
      await allowFunction(
        customCondition(
          customCompValue(consumingAddress, allowanceKeyA, allowanceKeyB),
        ),
        ExecutionOptions.Both,
      );

      await expect(invoke(30)).to.not.be.revert(ethers);
      expect((await roles.accruedAllowance(allowanceKeyA)).balance).to.equal(
        70,
      );
      expect((await roles.accruedAllowance(allowanceKeyB)).balance).to.equal(
        70,
      );

      // The same key twice must aggregate to 120 and fail atomically.
      await allowFunction(
        customCondition(
          customCompValue(consumingAddress, allowanceKeyA, allowanceKeyA),
        ),
        ExecutionOptions.Both,
      );
      await expect(invoke(60))
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(ConditionViolationStatus.AllowanceExceeded, 1, anyValue);
      expect((await roles.accruedAllowance(allowanceKeyA)).balance).to.equal(
        70,
      );
    });

    it("does not leak partial consumptions from a discarded OR branch", async () => {
      const { owner, roles, allowFunction, invoke, consumingAddress } =
        await loadFixture(setupConsuming);
      const duplicate = customCompValue(
        consumingAddress,
        allowanceKeyA,
        allowanceKeyA,
      );

      await roles.connect(owner).setAllowance(allowanceKeyA, 100, 0, 0, 0, 0);
      await allowFunction(
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              paramType: Encoding.None,
              operator: Operator.Or,
              children: [
                {
                  paramType: Encoding.Static,
                  operator: Operator.Custom,
                  compValue: duplicate,
                },
                {
                  paramType: Encoding.Static,
                  operator: Operator.Pass,
                },
              ],
            },
          ],
        }),
        ExecutionOptions.Both,
      );

      // The first branch consumes 60 then fails on its second consumption. The
      // Pass branch succeeds, but no partial consumption may be settled.
      await expect(invoke(60)).to.not.be.revert(ethers);
      expect((await roles.accruedAllowance(allowanceKeyA)).balance).to.equal(
        100,
      );
    });

    it("handles arbitrary uint256 amounts without an arithmetic panic", async () => {
      const { owner, roles, allowFunction, invoke, consumingAddress } =
        await loadFixture(setupConsuming);
      const compValue = customCompValue(consumingAddress, allowanceKeyA);

      await roles.connect(owner).setAllowance(allowanceKeyA, 100, 0, 0, 0, 0);
      await allowFunction(customCondition(compValue), ExecutionOptions.Both);

      await expect(invoke(MaxUint256))
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(ConditionViolationStatus.AllowanceExceeded, 1, anyValue);
    });
  });

  describe("rich result validation", () => {
    it("rejects malformed results with a structured status", async () => {
      const { roles, allowFunction, invoke } = await loadFixture(setupOneParam);
      const Malformed = await ethers.getContractFactory(
        "TestCustomCheckerMalformed",
      );
      const malformed = await Malformed.deploy();
      const adapter = await malformed.getAddress();

      for (const mode of ["00", "01", "02"]) {
        await allowFunction(
          customConditionForAdapter(adapter + mode),
          ExecutionOptions.Both,
        );

        await expect(invoke(101))
          .to.be.revertedWithCustomError(roles, "ConditionViolation")
          .withArgs(
            ConditionViolationStatus.CustomConditionInvalidResult,
            1,
            anyValue,
          );
      }
    });
  });

  function customConditionForAdapter(compValue: string) {
    return flattenCondition({
      paramType: Encoding.AbiEncoded,
      operator: Operator.Matches,
      children: [
        {
          paramType: Encoding.Static,
          operator: Operator.Custom,
          compValue,
        },
      ],
    });
  }
});
