import { expect } from "chai";
import { anyValue } from "@nomicfoundation/hardhat-ethers-chai-matchers/withArgs";
import { AbiCoder } from "ethers";

import { network } from "hardhat";

import { createSetup } from "../setup.js";
import {
  Encoding,
  Operator,
  ExecutionOptions,
  ConditionViolationStatus,
  flattenCondition,
} from "../utils.js";

const abiCoder = AbiCoder.defaultAbiCoder();

const connection = await network.create();
const { ethers, networkHelpers } = connection;
const { loadFixture } = networkHelpers;
const {
  setupTwoArrayParams,
  setupThreeArrayParams,
  setupTwoTupleArrayParams,
  setupTestContract,
} = createSetup(connection);

function pluckArray(index: number) {
  return {
    paramType: Encoding.Array,
    operator: Operator.Pluck,
    compValue: "0x" + index.toString(16).padStart(2, "0"),
    children: [{ paramType: Encoding.Static, operator: Operator.Pass }],
  };
}

function pluckTupleArray(index: number) {
  return {
    paramType: Encoding.Array,
    operator: Operator.Pluck,
    compValue: "0x" + index.toString(16).padStart(2, "0"),
    children: [
      {
        paramType: Encoding.Tuple,
        operator: Operator.Pass,
        children: [
          { paramType: Encoding.Static, operator: Operator.Pass },
          { paramType: Encoding.Static, operator: Operator.Pass },
        ],
      },
    ],
  };
}

function encodeCompValue(...indices: number[]) {
  return "0x" + indices.map((i) => i.toString(16).padStart(2, "0")).join("");
}

function setupThreeBytesArrayParams() {
  return setupThreeArrayParams("bytes");
}

function setupThreeDefaultArrayParams() {
  return setupThreeArrayParams();
}

describe("Operator - Zip (ZipSome & ZipEvery)", () => {
  after(async () => {
    await connection.close();
  });

  it("fails when arrays have different lengths", async () => {
    const { roles, allowFunction, invoke } =
      await loadFixture(setupTwoArrayParams);

    await allowFunction(
      flattenCondition({
        paramType: Encoding.None,
        operator: Operator.And,
        children: [
          {
            paramType: Encoding.AbiEncoded,
            operator: Operator.Matches,
            children: [pluckArray(0), pluckArray(1)],
          },
          {
            paramType: Encoding.None,
            operator: Operator.ZipEvery,
            compValue: encodeCompValue(0, 1),
            children: [
              {
                paramType: Encoding.Tuple,
                operator: Operator.Matches,
                children: [
                  { paramType: Encoding.Static, operator: Operator.Pass },
                  { paramType: Encoding.Static, operator: Operator.Pass },
                ],
              },
            ],
          },
        ],
      }),
      ExecutionOptions.Both,
    );

    await expect(invoke([1, 2, 3], [1, 2]))
      .to.be.revertedWithCustomError(roles, "ConditionViolation")
      .withArgs(
        ConditionViolationStatus.ZippedArrayLengthMismatch,
        anyValue,
        anyValue,
      );
  });

  it("evaluates arrays of tuples with nested navigation", async () => {
    const { roles, allowFunction, invoke } = await loadFixture(
      setupTwoTupleArrayParams,
    );

    // Pluck two (uint256,uint256)[] arrays, zip them, require first fields equal
    await allowFunction(
      flattenCondition({
        paramType: Encoding.None,
        operator: Operator.And,
        children: [
          {
            paramType: Encoding.AbiEncoded,
            operator: Operator.Matches,
            children: [pluckTupleArray(0), pluckTupleArray(1)],
          },
          {
            paramType: Encoding.None,
            operator: Operator.ZipEvery,
            compValue: encodeCompValue(0, 1),
            children: [
              {
                paramType: Encoding.Tuple,
                operator: Operator.Matches,
                children: [
                  {
                    paramType: Encoding.Tuple,
                    operator: Operator.Matches,
                    children: [
                      {
                        paramType: Encoding.Static,
                        operator: Operator.EqualTo,
                        compValue: abiCoder.encode(["uint256"], [100]),
                      },
                      { paramType: Encoding.Static, operator: Operator.Pass },
                    ],
                  },
                  {
                    paramType: Encoding.Tuple,
                    operator: Operator.Pass,
                    children: [
                      { paramType: Encoding.Static, operator: Operator.Pass },
                      { paramType: Encoding.Static, operator: Operator.Pass },
                    ],
                  },
                ],
              },
            ],
          },
        ],
      }),
      ExecutionOptions.Both,
    );

    // First field of left tuple must be 100
    await expect(invoke([[100, 1]], [[200, 2]])).to.not.be.revert(ethers);

    await expect(invoke([[99, 1]], [[200, 2]]))
      .to.be.revertedWithCustomError(roles, "ConditionViolation")
      .withArgs(
        ConditionViolationStatus.NotEveryZippedElementPasses,
        anyValue,
        anyValue,
      );
  });

  it("passes with single element arrays", async () => {
    const { roles, allowFunction, invoke } =
      await loadFixture(setupTwoArrayParams);

    await allowFunction(
      flattenCondition({
        paramType: Encoding.None,
        operator: Operator.And,
        children: [
          {
            paramType: Encoding.AbiEncoded,
            operator: Operator.Matches,
            children: [pluckArray(0), pluckArray(1)],
          },
          {
            paramType: Encoding.None,
            operator: Operator.ZipEvery,
            compValue: encodeCompValue(0, 1),
            children: [
              {
                paramType: Encoding.Tuple,
                operator: Operator.Matches,
                children: [
                  {
                    paramType: Encoding.Static,
                    operator: Operator.EqualTo,
                    compValue: abiCoder.encode(["uint256"], [42]),
                  },
                  { paramType: Encoding.Static, operator: Operator.Pass },
                ],
              },
            ],
          },
        ],
      }),
      ExecutionOptions.Both,
    );

    await expect(invoke([42], [100])).to.not.be.revert(ethers);

    await expect(invoke([100], [42]))
      .to.be.revertedWithCustomError(roles, "ConditionViolation")
      .withArgs(
        ConditionViolationStatus.NotEveryZippedElementPasses,
        anyValue,
        anyValue,
      );
  });

  it("fails with single element arrays", async () => {
    const { roles, allowFunction, invoke } =
      await loadFixture(setupTwoArrayParams);

    await allowFunction(
      flattenCondition({
        paramType: Encoding.None,
        operator: Operator.And,
        children: [
          {
            paramType: Encoding.AbiEncoded,
            operator: Operator.Matches,
            children: [pluckArray(0), pluckArray(1)],
          },
          {
            paramType: Encoding.None,
            operator: Operator.ZipEvery,
            compValue: encodeCompValue(0, 1),
            children: [
              {
                paramType: Encoding.Tuple,
                operator: Operator.Matches,
                children: [
                  {
                    paramType: Encoding.Static,
                    operator: Operator.EqualTo,
                    compValue: abiCoder.encode(["uint256"], [42]),
                  },
                  { paramType: Encoding.Static, operator: Operator.Pass },
                ],
              },
            ],
          },
        ],
      }),
      ExecutionOptions.Both,
    );

    await expect(invoke([99], [100]))
      .to.be.revertedWithCustomError(roles, "ConditionViolation")
      .withArgs(
        ConditionViolationStatus.NotEveryZippedElementPasses,
        anyValue,
        anyValue,
      );
  });

  it("zips three arrays", async () => {
    const { roles, allowFunction, invoke } = await loadFixture(
      setupThreeDefaultArrayParams,
    );

    await allowFunction(
      flattenCondition({
        paramType: Encoding.None,
        operator: Operator.And,
        children: [
          {
            paramType: Encoding.AbiEncoded,
            operator: Operator.Matches,
            children: [pluckArray(0), pluckArray(1), pluckArray(2)],
          },
          {
            paramType: Encoding.None,
            operator: Operator.ZipSome,
            compValue: encodeCompValue(0, 1, 2),
            children: [
              {
                paramType: Encoding.Tuple,
                operator: Operator.Matches,
                children: [
                  {
                    paramType: Encoding.Static,
                    operator: Operator.EqualTo,
                    compValue: abiCoder.encode(["uint256"], [1]),
                  },
                  {
                    paramType: Encoding.Static,
                    operator: Operator.EqualTo,
                    compValue: abiCoder.encode(["uint256"], [2]),
                  },
                  {
                    paramType: Encoding.Static,
                    operator: Operator.EqualTo,
                    compValue: abiCoder.encode(["uint256"], [3]),
                  },
                ],
              },
            ],
          },
        ],
      }),
      ExecutionOptions.Both,
    );

    await expect(invoke([3, 1, 9], [4, 2, 9], [5, 3, 9])).to.not.be.revert(
      ethers,
    );
    await expect(invoke([3, 1, 9], [4, 2, 9], [5, 0, 9]))
      .to.be.revertedWithCustomError(roles, "ConditionViolation")
      .withArgs(
        ConditionViolationStatus.NoZippedElementPasses,
        anyValue,
        anyValue,
      );
  });

  it("supports variant on the nth pluck", async () => {
    const { roles, allowFunction, invoke } = await loadFixture(
      setupThreeBytesArrayParams,
    );

    // First pluck is bytes[] (Dynamic elements), second pluck is variant
    // array with children of different type trees (Dynamic, AbiEncoded(Static, Static))
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
                paramType: Encoding.Array,
                operator: Operator.Pluck,
                compValue: "0x00",
                children: [
                  { paramType: Encoding.Dynamic, operator: Operator.Pass },
                ],
              },
              {
                paramType: Encoding.Array,
                operator: Operator.Pluck,
                compValue: "0x01",
                children: [
                  { paramType: Encoding.Dynamic, operator: Operator.Pass },
                  {
                    paramType: Encoding.AbiEncoded,
                    operator: Operator.Pass,
                    children: [
                      { paramType: Encoding.Static, operator: Operator.Pass },
                      { paramType: Encoding.Static, operator: Operator.Pass },
                    ],
                  },
                ],
              },
              {
                paramType: Encoding.Array,
                operator: Operator.Pass,
                children: [
                  { paramType: Encoding.Dynamic, operator: Operator.Pass },
                ],
              },
            ],
          },
          {
            paramType: Encoding.None,
            operator: Operator.ZipEvery,
            compValue: encodeCompValue(0, 1),
            children: [
              {
                paramType: Encoding.Tuple,
                operator: Operator.Matches,
                children: [
                  { paramType: Encoding.Dynamic, operator: Operator.Pass },
                  {
                    paramType: Encoding.Dynamic,
                    operator: Operator.EqualTo,
                    compValue: abiCoder.encode(["bytes"], ["0xdeadbeef"]),
                  },
                ],
              },
            ],
          },
        ],
      }),
      ExecutionOptions.Both,
    );

    await expect(
      invoke(["0xaa", "0xbb"], ["0xdeadbeef", "0xdeadbeef"], ["0x", "0x"]),
    ).to.not.be.revert(ethers);
    await expect(
      invoke(["0xaa", "0xbb"], ["0xdeadbeef", "0xcafebabe"], ["0x", "0x"]),
    )
      .to.be.revertedWithCustomError(roles, "ConditionViolation")
      .withArgs(
        ConditionViolationStatus.NotEveryZippedElementPasses,
        anyValue,
        anyValue,
      );
  });

  it("supports variant on the nth field", async () => {
    const { roles, allowFunction, invoke } = await loadFixture(
      setupThreeBytesArrayParams,
    );

    const targetBytes = "0xdeadbeef";

    // Plucked arrays are bytes[] (Dynamic elements). Zip tuple second field
    // is an Or variant on the field itself: AbiEncoded(Static, Static) or Dynamic EqualTo
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
                paramType: Encoding.Array,
                operator: Operator.Pluck,
                compValue: "0x00",
                children: [
                  { paramType: Encoding.Dynamic, operator: Operator.Pass },
                ],
              },
              {
                paramType: Encoding.Array,
                operator: Operator.Pluck,
                compValue: "0x01",
                children: [
                  { paramType: Encoding.Dynamic, operator: Operator.Pass },
                ],
              },
              {
                paramType: Encoding.Array,
                operator: Operator.Pass,
                children: [
                  { paramType: Encoding.Dynamic, operator: Operator.Pass },
                ],
              },
            ],
          },
          {
            paramType: Encoding.None,
            operator: Operator.ZipSome,
            compValue: encodeCompValue(0, 1),
            children: [
              {
                paramType: Encoding.Tuple,
                operator: Operator.Matches,
                children: [
                  { paramType: Encoding.Dynamic, operator: Operator.Pass },
                  {
                    paramType: Encoding.None,
                    operator: Operator.Or,
                    children: [
                      {
                        paramType: Encoding.AbiEncoded,
                        operator: Operator.Matches,
                        children: [
                          {
                            paramType: Encoding.Static,
                            operator: Operator.EqualTo,
                            compValue: abiCoder.encode(["uint256"], [1]),
                          },
                          {
                            paramType: Encoding.Static,
                            operator: Operator.EqualTo,
                            compValue: abiCoder.encode(["uint256"], [2]),
                          },
                        ],
                      },
                      {
                        paramType: Encoding.Dynamic,
                        operator: Operator.EqualTo,
                        compValue: abiCoder.encode(["bytes"], [targetBytes]),
                      },
                    ],
                  },
                ],
              },
            ],
          },
        ],
      }),
      ExecutionOptions.Both,
    );

    // Passes via second Or branch: right element equals targetBytes
    await expect(invoke(["0xaa"], [targetBytes], ["0x"])).to.not.be.revert(
      ethers,
    );

    // Fails: right element doesn't match either branch
    await expect(invoke(["0xaa"], ["0xcafebabe"], ["0x"]))
      .to.be.revertedWithCustomError(roles, "ConditionViolation")
      .withArgs(
        ConditionViolationStatus.NoZippedElementPasses,
        anyValue,
        anyValue,
      );
  });

  describe("ZipSome", () => {
    it("passes when at least one position matches", async () => {
      const { roles, allowFunction, invoke } =
        await loadFixture(setupTwoArrayParams);

      await allowFunction(
        flattenCondition({
          paramType: Encoding.None,
          operator: Operator.And,
          children: [
            {
              paramType: Encoding.AbiEncoded,
              operator: Operator.Matches,
              children: [pluckArray(0), pluckArray(1)],
            },
            {
              paramType: Encoding.None,
              operator: Operator.ZipSome,
              compValue: encodeCompValue(0, 1),
              children: [
                {
                  paramType: Encoding.Tuple,
                  operator: Operator.Matches,
                  children: [
                    {
                      paramType: Encoding.Static,
                      operator: Operator.EqualTo,
                      compValue: abiCoder.encode(["uint256"], [42]),
                    },
                    { paramType: Encoding.Static, operator: Operator.Pass },
                  ],
                },
              ],
            },
          ],
        }),
        ExecutionOptions.Both,
      );

      // Second position matches (left == 42)
      await expect(invoke([1, 42, 3], [10, 20, 30])).to.not.be.revert(ethers);

      // reversed arrays fail (no position has left == 42)
      await expect(invoke([10, 20, 30], [1, 42, 3]))
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(
          ConditionViolationStatus.NoZippedElementPasses,
          anyValue,
          anyValue,
        );
    });

    it("fails when no position matches", async () => {
      const { roles, allowFunction, invoke } =
        await loadFixture(setupTwoArrayParams);

      await allowFunction(
        flattenCondition({
          paramType: Encoding.None,
          operator: Operator.And,
          children: [
            {
              paramType: Encoding.AbiEncoded,
              operator: Operator.Matches,
              children: [pluckArray(0), pluckArray(1)],
            },
            {
              paramType: Encoding.None,
              operator: Operator.ZipSome,
              compValue: encodeCompValue(0, 1),
              children: [
                {
                  paramType: Encoding.Tuple,
                  operator: Operator.Matches,
                  children: [
                    {
                      paramType: Encoding.Static,
                      operator: Operator.EqualTo,
                      compValue: abiCoder.encode(["uint256"], [42]),
                    },
                    { paramType: Encoding.Static, operator: Operator.Pass },
                  ],
                },
              ],
            },
          ],
        }),
        ExecutionOptions.Both,
      );

      await expect(invoke([1, 2, 3], [10, 20, 30]))
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(
          ConditionViolationStatus.NoZippedElementPasses,
          anyValue,
          anyValue,
        );
    });

    it("fails when both arrays are empty", async () => {
      const { roles, allowFunction, invoke } =
        await loadFixture(setupTwoArrayParams);

      await allowFunction(
        flattenCondition({
          paramType: Encoding.None,
          operator: Operator.And,
          children: [
            {
              paramType: Encoding.AbiEncoded,
              operator: Operator.Matches,
              children: [pluckArray(0), pluckArray(1)],
            },
            {
              paramType: Encoding.None,
              operator: Operator.ZipSome,
              compValue: encodeCompValue(0, 1),
              children: [
                {
                  paramType: Encoding.Tuple,
                  operator: Operator.Matches,
                  children: [
                    { paramType: Encoding.Static, operator: Operator.Pass },
                    { paramType: Encoding.Static, operator: Operator.Pass },
                  ],
                },
              ],
            },
          ],
        }),
        ExecutionOptions.Both,
      );

      await expect(invoke([], []))
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(
          ConditionViolationStatus.NoZippedElementPasses,
          anyValue,
          anyValue,
        );
    });
  });

  describe("ZipEvery", () => {
    it("passes when all positions match", async () => {
      const { allowFunction, invoke } = await loadFixture(setupTwoArrayParams);

      await allowFunction(
        flattenCondition({
          paramType: Encoding.None,
          operator: Operator.And,
          children: [
            {
              paramType: Encoding.AbiEncoded,
              operator: Operator.Matches,
              children: [pluckArray(0), pluckArray(1)],
            },
            {
              paramType: Encoding.None,
              operator: Operator.ZipEvery,
              compValue: encodeCompValue(0, 1),
              children: [
                {
                  paramType: Encoding.Tuple,
                  operator: Operator.Matches,
                  children: [
                    {
                      paramType: Encoding.Static,
                      operator: Operator.GreaterThan,
                      compValue: abiCoder.encode(["uint256"], [0]),
                    },
                    { paramType: Encoding.Static, operator: Operator.Pass },
                  ],
                },
              ],
            },
          ],
        }),
        ExecutionOptions.Both,
      );

      await expect(invoke([1, 2, 3], [10, 20, 30])).to.not.be.revert(ethers);
    });

    it("fails when all positions mismatch", async () => {
      const { roles, allowFunction, invoke } =
        await loadFixture(setupTwoArrayParams);

      await allowFunction(
        flattenCondition({
          paramType: Encoding.None,
          operator: Operator.And,
          children: [
            {
              paramType: Encoding.AbiEncoded,
              operator: Operator.Matches,
              children: [pluckArray(0), pluckArray(1)],
            },
            {
              paramType: Encoding.None,
              operator: Operator.ZipEvery,
              compValue: encodeCompValue(0, 1),
              children: [
                {
                  paramType: Encoding.Tuple,
                  operator: Operator.Matches,
                  children: [
                    {
                      paramType: Encoding.Static,
                      operator: Operator.EqualTo,
                      compValue: abiCoder.encode(["uint256"], [42]),
                    },
                    { paramType: Encoding.Static, operator: Operator.Pass },
                  ],
                },
              ],
            },
          ],
        }),
        ExecutionOptions.Both,
      );

      // First position fails (left != 42)
      await expect(invoke([42, 2], [10, 20]))
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(
          ConditionViolationStatus.NotEveryZippedElementPasses,
          anyValue,
          anyValue,
        );
    });

    it("passes when both arrays are empty (vacuously true)", async () => {
      const { allowFunction, invoke } = await loadFixture(setupTwoArrayParams);

      await allowFunction(
        flattenCondition({
          paramType: Encoding.None,
          operator: Operator.And,
          children: [
            {
              paramType: Encoding.AbiEncoded,
              operator: Operator.Matches,
              children: [pluckArray(0), pluckArray(1)],
            },
            {
              paramType: Encoding.None,
              operator: Operator.ZipEvery,
              compValue: encodeCompValue(0, 1),
              children: [
                {
                  paramType: Encoding.Tuple,
                  operator: Operator.Matches,
                  children: [
                    {
                      paramType: Encoding.Static,
                      operator: Operator.EqualTo,
                      compValue: abiCoder.encode(["uint256"], [42]),
                    },
                    { paramType: Encoding.Static, operator: Operator.Pass },
                  ],
                },
              ],
            },
          ],
        }),
        ExecutionOptions.Both,
      );

      await expect(invoke([], [])).to.not.be.revert(ethers);
    });
  });

  describe("integrity", () => {
    it("reverts UnsuitableParameterType for non-None encoding", async () => {
      const { roles, allowTarget } = await loadFixture(setupTestContract);

      for (const encoding of [
        Encoding.Static,
        Encoding.Dynamic,
        Encoding.Tuple,
        Encoding.Array,
        Encoding.AbiEncoded,
      ]) {
        await expect(
          allowTarget([
            {
              parent: 0,
              paramType: encoding,
              operator: Operator.ZipSome,
              compValue: "0x0001",
            },
          ]),
        ).to.be.revertedWithCustomError(roles, "UnsuitableParameterType");
      }
    });

    it("reverts UnsuitableCompValue when compValue is shorter than 2 bytes", async () => {
      const { roles, allowTarget } = await loadFixture(setupTestContract);

      // 0 bytes
      await expect(
        allowTarget([
          {
            parent: 0,
            paramType: Encoding.None,
            operator: Operator.ZipSome,
            compValue: "0x",
          },
        ]),
      ).to.be.revertedWithCustomError(roles, "UnsuitableCompValue");

      // 1 byte
      await expect(
        allowTarget([
          {
            parent: 0,
            paramType: Encoding.None,
            operator: Operator.ZipSome,
            compValue: "0x00",
          },
        ]),
      ).to.be.revertedWithCustomError(roles, "UnsuitableCompValue");
    });

    it("reverts UnsuitableCompValue when compValue length does not match tuple field count", async () => {
      const { roles, allowTarget } = await loadFixture(setupTestContract);

      // compValue has 2 bytes but tuple has 3 fields
      await expect(
        allowTarget(
          flattenCondition({
            paramType: Encoding.None,
            operator: Operator.And,
            children: [
              {
                paramType: Encoding.AbiEncoded,
                operator: Operator.Matches,
                children: [pluckArray(0), pluckArray(1), pluckArray(2)],
              },
              {
                paramType: Encoding.None,
                operator: Operator.ZipEvery,
                compValue: encodeCompValue(0, 1),
                children: [
                  {
                    paramType: Encoding.Tuple,
                    operator: Operator.Matches,
                    children: [
                      { paramType: Encoding.Static, operator: Operator.Pass },
                      { paramType: Encoding.Static, operator: Operator.Pass },
                      { paramType: Encoding.Static, operator: Operator.Pass },
                    ],
                  },
                ],
              },
            ],
          }),
        ),
      ).to.be.revertedWithCustomError(roles, "UnsuitableCompValue");
    });

    it("reverts UnsuitableCompValue when pluck indices repeat", async () => {
      const { roles, allowTarget } = await loadFixture(setupTestContract);

      await expect(
        allowTarget(
          flattenCondition({
            paramType: Encoding.None,
            operator: Operator.And,
            children: [
              {
                paramType: Encoding.AbiEncoded,
                operator: Operator.Matches,
                children: [pluckArray(0), pluckArray(1)],
              },
              {
                paramType: Encoding.None,
                operator: Operator.ZipEvery,
                compValue: encodeCompValue(0, 0),
                children: [
                  {
                    paramType: Encoding.Tuple,
                    operator: Operator.Matches,
                    children: [
                      { paramType: Encoding.Static, operator: Operator.Pass },
                      { paramType: Encoding.Static, operator: Operator.Pass },
                    ],
                  },
                ],
              },
            ],
          }),
        ),
      ).to.be.revertedWithCustomError(roles, "UnsuitableCompValue");
    });

    it("reverts UnsuitableCompValue when pluck index not found", async () => {
      const { roles, allowTarget } = await loadFixture(setupTestContract);

      // Reference pluck index 5 which doesn't exist
      await expect(
        allowTarget(
          flattenCondition({
            paramType: Encoding.None,
            operator: Operator.And,
            children: [
              {
                paramType: Encoding.AbiEncoded,
                operator: Operator.Matches,
                children: [pluckArray(0), pluckArray(1)],
              },
              {
                paramType: Encoding.None,
                operator: Operator.ZipEvery,
                compValue: encodeCompValue(0, 5),
                children: [
                  {
                    paramType: Encoding.Tuple,
                    operator: Operator.Matches,
                    children: [
                      { paramType: Encoding.Static, operator: Operator.Pass },
                      { paramType: Encoding.Static, operator: Operator.Pass },
                    ],
                  },
                ],
              },
            ],
          }),
        ),
      ).to.be.revertedWithCustomError(roles, "UnsuitableCompValue");
    });

    it("reverts UnsuitableCompValue when pluck is not Array encoding", async () => {
      const { roles, allowTarget } = await loadFixture(setupTestContract);

      // Pluck index 1 is Static, not Array
      await expect(
        allowTarget(
          flattenCondition({
            paramType: Encoding.None,
            operator: Operator.And,
            children: [
              {
                paramType: Encoding.AbiEncoded,
                operator: Operator.Matches,
                children: [
                  pluckArray(0),
                  {
                    paramType: Encoding.Static,
                    operator: Operator.Pluck,
                    compValue: "0x01",
                  },
                ],
              },
              {
                paramType: Encoding.None,
                operator: Operator.ZipEvery,
                compValue: encodeCompValue(0, 1),
                children: [
                  {
                    paramType: Encoding.Tuple,
                    operator: Operator.Matches,
                    children: [
                      { paramType: Encoding.Static, operator: Operator.Pass },
                      { paramType: Encoding.Static, operator: Operator.Pass },
                    ],
                  },
                ],
              },
            ],
          }),
        ),
      ).to.be.revertedWithCustomError(roles, "UnsuitableCompValue");
    });

    it("reverts UnsuitableChildTypeTree when child does not resolve to a Tuple", async () => {
      const { roles, allowTarget } = await loadFixture(setupTestContract);

      await expect(
        allowTarget(
          flattenCondition({
            paramType: Encoding.None,
            operator: Operator.And,
            children: [
              {
                paramType: Encoding.AbiEncoded,
                operator: Operator.Matches,
                children: [pluckArray(0), pluckArray(1)],
              },
              {
                paramType: Encoding.None,
                operator: Operator.ZipEvery,
                compValue: encodeCompValue(0, 1),
                children: [
                  {
                    paramType: Encoding.Static,
                    operator: Operator.Pass,
                  },
                ],
              },
            ],
          }),
        ),
      ).to.be.revertedWithCustomError(roles, "UnsuitableChildTypeTree");
    });

    it("reverts UnsuitableChildTypeTree when field type does not match pluck array element type", async () => {
      const { roles, allowTarget } = await loadFixture(setupTestContract);

      // Pluck 0 has Static elements, but zip tuple field 0 is Tuple
      await expect(
        allowTarget(
          flattenCondition({
            paramType: Encoding.None,
            operator: Operator.And,
            children: [
              {
                paramType: Encoding.AbiEncoded,
                operator: Operator.Matches,
                children: [pluckArray(0), pluckArray(1)],
              },
              {
                paramType: Encoding.None,
                operator: Operator.ZipEvery,
                compValue: encodeCompValue(0, 1),
                children: [
                  {
                    paramType: Encoding.Tuple,
                    operator: Operator.Matches,
                    children: [
                      {
                        paramType: Encoding.Tuple,
                        operator: Operator.Pass,
                        children: [
                          {
                            paramType: Encoding.Static,
                            operator: Operator.Pass,
                          },
                        ],
                      },
                      { paramType: Encoding.Static, operator: Operator.Pass },
                    ],
                  },
                ],
              },
            ],
          }),
        ),
      ).to.be.revertedWithCustomError(roles, "UnsuitableChildTypeTree");
    });

    it("reverts UnsupportedOperator when descendant uses Pluck", async () => {
      const { roles, allowTarget } = await loadFixture(setupTestContract);

      await expect(
        allowTarget(
          flattenCondition({
            paramType: Encoding.None,
            operator: Operator.And,
            children: [
              {
                paramType: Encoding.AbiEncoded,
                operator: Operator.Matches,
                children: [pluckArray(0), pluckArray(1)],
              },
              {
                paramType: Encoding.None,
                operator: Operator.ZipEvery,
                compValue: encodeCompValue(0, 1),
                children: [
                  {
                    paramType: Encoding.Tuple,
                    operator: Operator.Matches,
                    children: [
                      {
                        paramType: Encoding.Static,
                        operator: Operator.Pluck,
                        compValue: "0x02",
                      },
                      { paramType: Encoding.Static, operator: Operator.Pass },
                    ],
                  },
                ],
              },
            ],
          }),
        ),
      ).to.be.revertedWithCustomError(roles, "UnsupportedOperator");
    });

    it("reverts UnsuitableChildCount when tuple child has a non-structural child", async () => {
      const { roles, allowTarget } = await loadFixture(setupTestContract);

      // Every field of the Tuple is evaluated at an element of the array in
      // its slot, so a field that reads no calldata has no place in it.
      await expect(
        allowTarget(
          flattenCondition({
            paramType: Encoding.None,
            operator: Operator.And,
            children: [
              {
                paramType: Encoding.AbiEncoded,
                operator: Operator.Matches,
                children: [pluckArray(0), pluckArray(1)],
              },
              {
                paramType: Encoding.None,
                operator: Operator.ZipEvery,
                compValue: encodeCompValue(0, 1),
                children: [
                  {
                    paramType: Encoding.Tuple,
                    operator: Operator.Pass,
                    children: [
                      { paramType: Encoding.Static, operator: Operator.Pass },
                      { paramType: Encoding.None, operator: Operator.Pass },
                    ],
                  },
                ],
              },
            ],
          }),
        ),
      ).to.be.revertedWithCustomError(roles, "UnsuitableChildCount");
    });
  });
});
