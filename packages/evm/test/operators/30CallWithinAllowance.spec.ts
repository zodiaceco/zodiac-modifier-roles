import { expect } from "chai";
import { AbiCoder, hexlify, randomBytes } from "ethers";
import { network } from "hardhat";

import {
  Encoding,
  Operator,
  ConditionViolationStatus,
  flattenCondition,
  packConditions,
} from "../utils.js";
import { createSetup } from "../setup.js";

const abi = AbiCoder.defaultAbiCoder();

const connection = await network.create();
const { ethers, networkHelpers } = connection;
const { loadFixture, time } = networkHelpers;
const { setupTestContract, setupFn } = createSetup(connection);
const setupNoParam = setupFn("function fn()");
const setupOneParam = setupFn("function fn(uint256)");
const setupTwoParams = setupFn("function fn(uint256, uint256)");

const callWithinAllowance = (key: string) => ({
  paramType: Encoding.None,
  operator: Operator.CallWithinAllowance,
  compValue: key,
});
const equalTo = (value: number) => ({
  paramType: Encoding.Static,
  operator: Operator.EqualTo,
  compValue: abi.encode(["uint256"], [value]),
});
const randomKey = () => hexlify(randomBytes(32));

describe("Operator - CallWithinAllowance", async () => {
  after(async () => {
    await connection.close();
  });

  describe("as the root condition", () => {
    it("charges one per call until the balance runs out", async () => {
      const { roles, allowFunction, invoke } = await loadFixture(setupNoParam);
      const key = randomKey();
      await roles.setAllowance(key, 2, 0, 0, 0, 0);
      await allowFunction(flattenCondition(callWithinAllowance(key)));

      await expect(invoke())
        .to.emit(roles, "ConsumeAllowance")
        .withArgs(key, 1, 1);
      await expect(invoke())
        .to.emit(roles, "ConsumeAllowance")
        .withArgs(key, 1, 0);
      // the root node, and no payload: offset 0
      await expect(invoke())
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(ConditionViolationStatus.AllowanceExceeded, 0, 0);
    });

    it("charges a pending refill, then refuses until the next one", async () => {
      const { roles, allowFunction, invoke } = await loadFixture(setupNoParam);
      const key = randomKey();
      // balance 0; one refill of 1 is due
      await roles.setAllowance(
        key,
        0,
        0,
        1,
        1000,
        (await time.latest()) - 1010,
      );
      await allowFunction(flattenCondition(callWithinAllowance(key)));

      await expect(invoke())
        .to.emit(roles, "ConsumeAllowance")
        .withArgs(key, 1, 0);
      await expect(invoke())
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(ConditionViolationStatus.AllowanceExceeded, 0, 0);
    });

    it("on a whole target, charges calls with empty calldata too", async () => {
      const { roles, member, testContractAddress, allowTarget } =
        await loadFixture(setupTestContract);
      const key = randomKey();
      await roles.setAllowance(key, 2, 0, 0, 0, 0);
      await allowTarget(flattenCondition(callWithinAllowance(key)));
      const exec = (data: string) =>
        roles
          .connect(member)
          .execTransactionFromModule(testContractAddress, 0, data, 0);

      await expect(exec("0x"))
        .to.emit(roles, "ConsumeAllowance")
        .withArgs(key, 1, 1);
      await expect(exec("0x12345678"))
        .to.emit(roles, "ConsumeAllowance")
        .withArgs(key, 1, 0);
      await expect(exec("0x"))
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(ConditionViolationStatus.AllowanceExceeded, 0, 0);
    });
  });

  describe("in logical combinations", () => {
    it("charges after the rest of an And passes", async () => {
      const { roles, allowFunction, invoke } = await loadFixture(setupOneParam);
      const key = randomKey();
      await roles.setAllowance(key, 1, 0, 0, 0, 0);
      await allowFunction(
        flattenCondition({
          paramType: Encoding.None,
          operator: Operator.And,
          children: [
            {
              paramType: Encoding.AbiEncoded,
              operator: Operator.Matches,
              children: [equalTo(42)],
            },
            callWithinAllowance(key),
          ],
        }),
      );

      // And[0] -> Matches[1], CallWithinAllowance[2] -> EqualTo[3]
      await expect(invoke(999))
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(ConditionViolationStatus.ParameterNotAllowed, 3, 4);
      await expect(invoke(42))
        .to.emit(roles, "ConsumeAllowance")
        .withArgs(key, 1, 0);
      await expect(invoke(42))
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(ConditionViolationStatus.AllowanceExceeded, 2, 0);
    });

    it("charges only the allowance of the Or branch that passes", async () => {
      const { roles, allowFunction, invoke } = await loadFixture(setupOneParam);
      const [key100, key200] = [randomKey(), randomKey()];
      await roles.setAllowance(key100, 1, 0, 0, 0, 0);
      await roles.setAllowance(key200, 1, 0, 0, 0, 0);
      const branch = (value: number, key: string) => ({
        paramType: Encoding.None,
        operator: Operator.And,
        children: [
          {
            paramType: Encoding.AbiEncoded,
            operator: Operator.Matches,
            children: [equalTo(value)],
          },
          callWithinAllowance(key),
        ],
      });
      await allowFunction(
        flattenCondition({
          paramType: Encoding.None,
          operator: Operator.Or,
          children: [branch(100, key100), branch(200, key200)],
        }),
      );

      await expect(invoke(9999))
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(ConditionViolationStatus.OrViolation, 0, 0);

      // 200's branch passes: its allowance is charged, 100's is left alone
      await expect(invoke(200))
        .to.emit(roles, "ConsumeAllowance")
        .withArgs(key200, 1, 0);
      expect((await roles.allowances(key100)).balance).to.equal(1);
      // 200's is used up, and 100's balance does not stand in for it
      await expect(invoke(200))
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(ConditionViolationStatus.OrViolation, 0, 0);

      await expect(invoke(100))
        .to.emit(roles, "ConsumeAllowance")
        .withArgs(key100, 1, 0);
      await expect(invoke(100))
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(ConditionViolationStatus.OrViolation, 0, 0);
    });

    it("does not charge an Or branch that fails after it", async () => {
      const { roles, allowFunction, invoke } = await loadFixture(setupOneParam);
      const key = randomKey();
      await roles.setAllowance(key, 1, 0, 0, 0, 0);
      await allowFunction(
        flattenCondition({
          paramType: Encoding.None,
          operator: Operator.Or,
          children: [
            {
              // charges first, then fails for anything but 100
              paramType: Encoding.None,
              operator: Operator.And,
              children: [
                callWithinAllowance(key),
                {
                  paramType: Encoding.AbiEncoded,
                  operator: Operator.Matches,
                  children: [equalTo(100)],
                },
              ],
            },
            {
              paramType: Encoding.AbiEncoded,
              operator: Operator.Matches,
              children: [
                { paramType: Encoding.Static, operator: Operator.Pass },
              ],
            },
          ],
        }),
      );

      await expect(invoke(999)).to.not.emit(roles, "ConsumeAllowance");
      expect((await roles.allowances(key)).balance).to.equal(1);
      await expect(invoke(100))
        .to.emit(roles, "ConsumeAllowance")
        .withArgs(key, 1, 0);
    });

    it("charges twice when it appears twice in an And", async () => {
      const { roles, allowFunction, invoke } = await loadFixture(setupNoParam);
      const key = randomKey();
      await roles.setAllowance(key, 3, 0, 0, 0, 0);
      await allowFunction(
        flattenCondition({
          paramType: Encoding.None,
          operator: Operator.And,
          children: [callWithinAllowance(key), callWithinAllowance(key)],
        }),
      );

      await expect(invoke())
        .to.emit(roles, "ConsumeAllowance")
        .withArgs(key, 2, 1);
      // one left: the second charge fails
      await expect(invoke())
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(ConditionViolationStatus.AllowanceExceeded, 2, 0);
    });

    it("charges the same allowance as a WithinAllowance on a parameter", async () => {
      const { roles, allowFunction, invoke } = await loadFixture(setupOneParam);
      const key = randomKey();
      await roles.setAllowance(key, 10, 0, 0, 0, 0);
      await allowFunction(
        flattenCondition({
          paramType: Encoding.None,
          operator: Operator.And,
          children: [
            {
              paramType: Encoding.AbiEncoded,
              operator: Operator.Matches,
              children: [
                {
                  paramType: Encoding.Static,
                  operator: Operator.WithinAllowance,
                  compValue: key,
                },
              ],
            },
            callWithinAllowance(key),
          ],
        }),
      );

      // 5 for the parameter, 1 for the call
      await expect(invoke(5))
        .to.emit(roles, "ConsumeAllowance")
        .withArgs(key, 6, 4);
      // the parameter takes all 4: none left for the call
      await expect(invoke(4))
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(ConditionViolationStatus.AllowanceExceeded, 2, 0);
    });

    it("as a tuple field inside And, charges once the field matches", async () => {
      const { roles, allowFunction, invoke } =
        await loadFixture(setupTwoParams);
      const key = randomKey();
      await roles.setAllowance(key, 1, 0, 0, 0, 0);
      // Matches[0] -> Pass[1], And[2] -> EqualTo[3], CallWithinAllowance[4]
      await allowFunction(
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            { paramType: Encoding.Static, operator: Operator.Pass },
            {
              paramType: Encoding.None,
              operator: Operator.And,
              children: [equalTo(42), callWithinAllowance(key)],
            },
          ],
        }),
      );

      // the second parameter's word starts at 4 + 32
      await expect(invoke(100, 999))
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(ConditionViolationStatus.ParameterNotAllowed, 3, 36);
      await expect(invoke(100, 42))
        .to.emit(roles, "ConsumeAllowance")
        .withArgs(key, 1, 0);
      // nested in the field, it reports the field's offset (at the root, 0)
      await expect(invoke(200, 42))
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(ConditionViolationStatus.AllowanceExceeded, 4, 36);
    });
  });

  describe("integrity", () => {
    it("reverts UnsuitableParameterType for any encoding but None", async () => {
      const { roles, evaluator } = await loadFixture(setupTestContract);

      for (const encoding of [
        Encoding.Static,
        Encoding.Dynamic,
        Encoding.Tuple,
        Encoding.Array,
        Encoding.AbiEncoded,
        Encoding.EtherValue,
      ])
        await expect(
          packConditions(
            roles,
            flattenCondition({
              ...callWithinAllowance(randomKey()),
              paramType: encoding,
            }),
          ),
        ).to.be.revertedWithCustomError(evaluator, "UnsuitableParameterType");
    });

    for (const size of [0, 31, 33])
      it(`reverts UnsuitableCompValue for a ${size}-byte compValue`, async () => {
        const { roles, evaluator } = await loadFixture(setupTestContract);

        await expect(
          packConditions(
            roles,
            flattenCondition(callWithinAllowance(hexlify(randomBytes(size)))),
          ),
        ).to.be.revertedWithCustomError(evaluator, "UnsuitableCompValue");
      });

    it("reverts LeafNodeCannotHaveChildren when it has children", async () => {
      const { roles, evaluator } = await loadFixture(setupTestContract);

      await expect(
        packConditions(roles, [
          { parent: 0, ...callWithinAllowance(randomKey()) },
          {
            parent: 0,
            paramType: Encoding.Static,
            operator: Operator.Pass,
            compValue: "0x",
          },
        ]),
      ).to.be.revertedWithCustomError(evaluator, "LeafNodeCannotHaveChildren");
    });
  });
});
