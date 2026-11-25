import { after, describe, it } from "node:test";
import { anyValue } from "@nomicfoundation/hardhat-viem-assertions/predicates";
import { network } from "hardhat";
import { encodeAbiParameters, parseAbiParameters } from "viem";

import { createSetup } from "../setup.js";
import {
  Encoding,
  Operator,
  ExecutionOptions,
  ConditionViolationStatus,
  flattenCondition,
} from "../utils.js";

const connection = await network.create();
const { viem, networkHelpers } = connection;
const { loadFixture } = networkHelpers;
const { setupTestContract, setupFn } = createSetup(connection);
const setupTwoArrayParams = setupFn("function fn(uint256[], uint256[])");
const setupThreeBytesArrayParams = setupFn(
  "function fn(bytes[], bytes[], bytes[])",
);
const setupThreeDefaultArrayParams = setupFn(
  "function fn(uint256[], uint256[], uint256[])",
);
const setupTwoTupleArrayParams = setupFn(
  "function fn((uint256, uint256)[], (uint256, uint256)[])",
);

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

    await viem.assertions.revertWithCustomErrorWithArgs(
      invoke([1, 2, 3], [1, 2]),
      roles,
      "ConditionViolation",
      [ConditionViolationStatus.ZippedArrayLengthMismatch, anyValue, anyValue],
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
                        compValue: encodeAbiParameters(
                          parseAbiParameters("uint256"),
                          [100n],
                        ),
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
    await invoke([[100, 1]], [[200, 2]]);

    await viem.assertions.revertWithCustomErrorWithArgs(
      invoke([[99, 1]], [[200, 2]]),
      roles,
      "ConditionViolation",
      [
        ConditionViolationStatus.NotEveryZippedElementPasses,
        anyValue,
        anyValue,
      ],
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
                    compValue: encodeAbiParameters(
                      parseAbiParameters("uint256"),
                      [42n],
                    ),
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

    await invoke([42], [100]);

    await viem.assertions.revertWithCustomErrorWithArgs(
      invoke([100], [42]),
      roles,
      "ConditionViolation",
      [
        ConditionViolationStatus.NotEveryZippedElementPasses,
        anyValue,
        anyValue,
      ],
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
                    compValue: encodeAbiParameters(
                      parseAbiParameters("uint256"),
                      [42n],
                    ),
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

    await viem.assertions.revertWithCustomErrorWithArgs(
      invoke([99], [100]),
      roles,
      "ConditionViolation",
      [
        ConditionViolationStatus.NotEveryZippedElementPasses,
        anyValue,
        anyValue,
      ],
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
                    compValue: encodeAbiParameters(
                      parseAbiParameters("uint256"),
                      [1n],
                    ),
                  },
                  {
                    paramType: Encoding.Static,
                    operator: Operator.EqualTo,
                    compValue: encodeAbiParameters(
                      parseAbiParameters("uint256"),
                      [2n],
                    ),
                  },
                  {
                    paramType: Encoding.Static,
                    operator: Operator.EqualTo,
                    compValue: encodeAbiParameters(
                      parseAbiParameters("uint256"),
                      [3n],
                    ),
                  },
                ],
              },
            ],
          },
        ],
      }),
      ExecutionOptions.Both,
    );

    await invoke([3, 1, 9], [4, 2, 9], [5, 3, 9]);
    await viem.assertions.revertWithCustomErrorWithArgs(
      invoke([3, 1, 9], [4, 2, 9], [5, 0, 9]),
      roles,
      "ConditionViolation",
      [ConditionViolationStatus.NoZippedElementPasses, anyValue, anyValue],
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
                    compValue: encodeAbiParameters(
                      parseAbiParameters("bytes"),
                      ["0xdeadbeef"],
                    ),
                  },
                ],
              },
            ],
          },
        ],
      }),
      ExecutionOptions.Both,
    );

    await invoke(["0xaa", "0xbb"], ["0xdeadbeef", "0xdeadbeef"], ["0x", "0x"]);
    await viem.assertions.revertWithCustomErrorWithArgs(
      invoke(["0xaa", "0xbb"], ["0xdeadbeef", "0xcafebabe"], ["0x", "0x"]),
      roles,
      "ConditionViolation",
      [
        ConditionViolationStatus.NotEveryZippedElementPasses,
        anyValue,
        anyValue,
      ],
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
                            compValue: encodeAbiParameters(
                              parseAbiParameters("uint256"),
                              [1n],
                            ),
                          },
                          {
                            paramType: Encoding.Static,
                            operator: Operator.EqualTo,
                            compValue: encodeAbiParameters(
                              parseAbiParameters("uint256"),
                              [2n],
                            ),
                          },
                        ],
                      },
                      {
                        paramType: Encoding.Dynamic,
                        operator: Operator.EqualTo,
                        compValue: encodeAbiParameters(
                          parseAbiParameters("bytes"),
                          [targetBytes],
                        ),
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
    await invoke(["0xaa"], [targetBytes], ["0x"]);

    // Fails: right element doesn't match either branch
    await viem.assertions.revertWithCustomErrorWithArgs(
      invoke(["0xaa"], ["0xcafebabe"], ["0x"]),
      roles,
      "ConditionViolation",
      [ConditionViolationStatus.NoZippedElementPasses, anyValue, anyValue],
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
                      compValue: encodeAbiParameters(
                        parseAbiParameters("uint256"),
                        [42n],
                      ),
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
      await invoke([1, 42, 3], [10, 20, 30]);

      // reversed arrays fail (no position has left == 42)
      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke([10, 20, 30], [1, 42, 3]),
        roles,
        "ConditionViolation",
        [ConditionViolationStatus.NoZippedElementPasses, anyValue, anyValue],
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
                      compValue: encodeAbiParameters(
                        parseAbiParameters("uint256"),
                        [42n],
                      ),
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

      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke([1, 2, 3], [10, 20, 30]),
        roles,
        "ConditionViolation",
        [ConditionViolationStatus.NoZippedElementPasses, anyValue, anyValue],
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

      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke([], []),
        roles,
        "ConditionViolation",
        [ConditionViolationStatus.NoZippedElementPasses, anyValue, anyValue],
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
                      compValue: encodeAbiParameters(
                        parseAbiParameters("uint256"),
                        [0n],
                      ),
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

      await invoke([1, 2, 3], [10, 20, 30]);
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
                      compValue: encodeAbiParameters(
                        parseAbiParameters("uint256"),
                        [42n],
                      ),
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
      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke([42, 2], [10, 20]),
        roles,
        "ConditionViolation",
        [
          ConditionViolationStatus.NotEveryZippedElementPasses,
          anyValue,
          anyValue,
        ],
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
                      compValue: encodeAbiParameters(
                        parseAbiParameters("uint256"),
                        [42n],
                      ),
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

      await invoke([], []);
    });
  });
});
