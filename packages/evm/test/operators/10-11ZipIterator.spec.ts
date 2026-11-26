import { after, describe, it } from "node:test";
import { anyValue } from "@nomicfoundation/hardhat-viem-assertions/predicates";
import { network } from "hardhat";
import { encodeAbiParameters, encodePacked, parseAbiParameters } from "viem";

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
const { setupFn } = createSetup(connection);
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
const setupTwoNestedArrayParams = setupFn(
  "function fn(uint256[][], uint256[][])",
);
const setupOneArray = setupFn("function fn(uint256[])");
const setupOneArrayOneWord = setupFn("function fn(uint256[], uint256)");
const setupTwoArraysOneWord = setupFn(
  "function fn(uint256[], uint256[], uint256)",
);
const setupTwoArraysTwoWords = setupFn(
  "function fn(uint256[], uint256[], uint256, uint256)",
);
const setupTwoBytesArraysTwoWords = setupFn(
  "function fn(bytes[], bytes[], uint256, uint256)",
);

type Condition = Parameters<typeof flattenCondition>[0];

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

function pluckWord(index: number) {
  return {
    paramType: Encoding.Static,
    operator: Operator.Pluck,
    compValue: encodeCompValue(index),
  };
}

function eq(value: bigint) {
  return {
    paramType: Encoding.Static,
    operator: Operator.EqualTo,
    compValue: encodeAbiParameters(parseAbiParameters("uint256"), [value]),
  };
}

// The Tuple child of a Zip: one field per zipped array
function fields(...children: Condition[]) {
  return { paramType: Encoding.Tuple, operator: Operator.Matches, children };
}

function and(...children: Condition[]) {
  return { paramType: Encoding.None, operator: Operator.And, children };
}

// relative / reference, both read from slots, bounds in bps
function ratio(reference: number, relative: number, min: number, max: number) {
  return {
    paramType: Encoding.None,
    operator: Operator.WithinRatio,
    compValue: encodePacked(
      ["uint8", "uint8", "uint8", "uint8", "uint32", "uint32"],
      [reference, 0, relative, 0, min, max],
    ),
  };
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

  describe("with other checks", () => {
    it("sits before the word it is next to, without shifting later parameters", async () => {
      const { roles, allowFunction, invoke } = await loadFixture(
        setupTwoArraysTwoWords,
      );

      await allowFunction(
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            pluckArray(0),
            pluckArray(1),
            {
              paramType: Encoding.None,
              operator: Operator.And,
              children: [
                {
                  paramType: Encoding.None,
                  operator: Operator.ZipEvery,
                  compValue: encodeCompValue(0, 1),
                  children: [
                    fields(
                      { paramType: Encoding.Static, operator: Operator.Pass },
                      { paramType: Encoding.Static, operator: Operator.Pass },
                    ),
                  ],
                },
                eq(1n),
              ],
            },
            eq(2n),
          ],
        }),
        ExecutionOptions.Both,
      );

      await invoke([1], [1], 1, 2);

      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke([1], [1], 1, 3),
        roles,
        "ConditionViolation",
        [ConditionViolationStatus.ParameterNotAllowed, anyValue, anyValue],
      );
    });

    it("zips bytes arrays next to a word, without shifting later parameters", async () => {
      const { roles, allowFunction, invoke } = await loadFixture(
        setupTwoBytesArraysTwoWords,
      );

      const pluckBytesArray = (index: number) => ({
        ...pluckArray(index),
        children: [{ paramType: Encoding.Dynamic, operator: Operator.Pass }],
      });

      await allowFunction(
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            pluckBytesArray(0),
            pluckBytesArray(1),
            {
              paramType: Encoding.None,
              operator: Operator.And,
              children: [
                eq(1n),
                {
                  paramType: Encoding.None,
                  operator: Operator.ZipEvery,
                  compValue: encodeCompValue(0, 1),
                  children: [
                    fields(
                      { paramType: Encoding.Dynamic, operator: Operator.Pass },
                      { paramType: Encoding.Dynamic, operator: Operator.Pass },
                    ),
                  ],
                },
              ],
            },
            eq(2n),
          ],
        }),
        ExecutionOptions.Both,
      );

      await invoke(["0x01"], ["0x02"], 1, 2);

      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke(["0x01"], ["0x02"], 1, 3),
        roles,
        "ConditionViolation",
        [ConditionViolationStatus.ParameterNotAllowed, anyValue, anyValue],
      );
    });

    it("branches between two Zips in an Or", async () => {
      const { roles, allowFunction, invoke } =
        await loadFixture(setupTwoArrayParams);

      const zipSome = (value: bigint) => ({
        paramType: Encoding.None,
        operator: Operator.ZipSome,
        compValue: encodeCompValue(0, 1),
        children: [fields(eq(value), eq(value))],
      });

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
              operator: Operator.Or,
              children: [zipSome(1n), zipSome(2n)],
            },
          ],
        }),
        ExecutionOptions.Both,
      );

      await invoke([9, 2], [9, 2]);

      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke([9, 2], [9, 3]),
        roles,
        "ConditionViolation",
        [ConditionViolationStatus.OrViolation, anyValue, anyValue],
      );
    });
  });

  describe("plucking from the fields", () => {
    const calldata = (...children: Condition[]) => ({
      paramType: Encoding.AbiEncoded,
      operator: Operator.Matches,
      children,
    });
    const zip = (
      operator: Operator,
      slots: [number, number],
      left: Condition,
      right: Condition,
    ) => ({
      paramType: Encoding.None,
      operator,
      compValue: encodeCompValue(...slots),
      children: [fields(left, right)],
    });

    it("compares the two sides of every pair", async () => {
      const { roles, allowFunction, invoke } =
        await loadFixture(setupTwoArrayParams);

      // every right[i] is within 10% of left[i]
      await allowFunction(
        flattenCondition(
          and(
            calldata(pluckArray(0), pluckArray(1)),
            zip(
              Operator.ZipEvery,
              [0, 1],
              pluckWord(2),
              and(pluckWord(3), ratio(2, 3, 9000, 11000)),
            ),
          ),
        ),
        ExecutionOptions.Both,
      );

      // 95/100 and 210/200 are both within 10%
      await invoke([100, 200], [95, 210]);

      // step 0 passes, step 1 does not: 100/200 is 50%
      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke([100, 200], [95, 100]),
        roles,
        "ConditionViolation",
        [
          ConditionViolationStatus.NotEveryZippedElementPasses,
          anyValue,
          anyValue,
        ],
      );
    });

    it("compares every pair with a word plucked outside the Zip", async () => {
      const { roles, allowFunction, invoke } = await loadFixture(
        setupTwoArraysOneWord,
      );

      // every left[i] is at most half of the third parameter
      await allowFunction(
        flattenCondition(
          and(
            calldata(pluckArray(0), pluckArray(1), pluckWord(2)),
            zip(
              Operator.ZipEvery,
              [0, 1],
              and(pluckWord(3), ratio(2, 3, 0, 5000)),
              { paramType: Encoding.Static, operator: Operator.Pass },
            ),
          ),
        ),
        ExecutionOptions.Both,
      );

      // 10/100 and 50/100
      await invoke([10, 50], [0, 0], 100);

      // 60/100 is above half
      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke([10, 60], [0, 0], 100),
        roles,
        "ConditionViolation",
        [
          ConditionViolationStatus.NotEveryZippedElementPasses,
          anyValue,
          anyValue,
        ],
      );
    });

    it("compares members of paired structs", async () => {
      const { roles, allowFunction, invoke } = await loadFixture(
        setupTwoTupleArrayParams,
      );

      const member = (...children: Condition[]) => ({
        paramType: Encoding.Tuple,
        operator: Operator.Matches,
        children,
      });

      // (id, amount) on both sides: same id, amount within 10%
      await allowFunction(
        flattenCondition(
          and(
            calldata(pluckTupleArray(0), pluckTupleArray(1)),
            zip(
              Operator.ZipEvery,
              [0, 1],
              member(pluckWord(2), pluckWord(3)),
              member(
                and(pluckWord(4), ratio(2, 4, 10000, 10000)),
                and(pluckWord(5), ratio(3, 5, 9000, 11000)),
              ),
            ),
          ),
        ),
        ExecutionOptions.Both,
      );

      await invoke(
        [
          [7, 100],
          [8, 200],
        ],
        [
          [7, 95],
          [8, 210],
        ],
      );

      // the second pair has different ids
      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke(
          [
            [7, 100],
            [8, 200],
          ],
          [
            [7, 95],
            [9, 210],
          ],
        ),
        roles,
        "ConditionViolation",
        [
          ConditionViolationStatus.NotEveryZippedElementPasses,
          anyValue,
          anyValue,
        ],
      );

      // the second pair has amounts 50% apart
      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke(
          [
            [7, 100],
            [8, 200],
          ],
          [
            [7, 95],
            [8, 100],
          ],
        ),
        roles,
        "ConditionViolation",
        [
          ConditionViolationStatus.NotEveryZippedElementPasses,
          anyValue,
          anyValue,
        ],
      );
    });

    it("zips the arrays it plucks, in a Zip of arrays of arrays", async () => {
      const { roles, allowFunction, invoke } = await loadFixture(
        setupTwoNestedArrayParams,
      );

      const pluckNestedArray = (index: number) => ({
        paramType: Encoding.Array,
        operator: Operator.Pluck,
        compValue: encodeCompValue(index),
        children: [
          {
            paramType: Encoding.Array,
            operator: Operator.Pass,
            children: [{ paramType: Encoding.Static, operator: Operator.Pass }],
          },
        ],
      });

      // the outer Zip plucks left[i] and right[i], the inner one pairs
      // them: every right[i][j] equals left[i][j]
      await allowFunction(
        flattenCondition(
          and(
            calldata(pluckNestedArray(0), pluckNestedArray(1)),
            zip(
              Operator.ZipEvery,
              [0, 1],
              pluckArray(2),
              and(
                pluckArray(3),
                zip(
                  Operator.ZipEvery,
                  [2, 3],
                  pluckWord(4),
                  and(pluckWord(5), ratio(4, 5, 10000, 10000)),
                ),
              ),
            ),
          ),
        ),
        ExecutionOptions.Both,
      );

      await invoke([[1, 2], [3]], [[1, 2], [3]]);

      // right[1][0] differs
      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke([[1, 2], [3]], [[1, 2], [4]]),
        roles,
        "ConditionViolation",
        [
          ConditionViolationStatus.NotEveryZippedElementPasses,
          anyValue,
          anyValue,
        ],
      );

      // right[0] is shorter than left[0]
      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke([[1, 2], [3]], [[1], [3]]),
        roles,
        "ConditionViolation",
        [
          ConditionViolationStatus.NotEveryZippedElementPasses,
          anyValue,
          anyValue,
        ],
      );
    });

    it("keeps what the passing ZipSome step plucked, for a check after the Zip", async () => {
      const { roles, allowFunction, invoke } = await loadFixture(
        setupTwoArraysOneWord,
      );

      // the left of the pair whose right is 1 equals the third parameter
      await allowFunction(
        flattenCondition(
          and(
            calldata(pluckArray(0), pluckArray(1), pluckWord(2)),
            zip(Operator.ZipSome, [0, 1], pluckWord(3), eq(1n)),
            ratio(2, 3, 10000, 10000),
          ),
        ),
        ExecutionOptions.Both,
      );

      // step 1 passes (right is 1) and plucks 7 on the left
      await invoke([5, 7], [0, 1], 7);

      // step 0 plucked 5 before it failed: step 1 overwrites it
      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke([5, 7], [0, 1], 5),
        roles,
        "ConditionViolation",
        [ConditionViolationStatus.RatioAboveMax, anyValue, anyValue],
      );
    });
  });

  describe("slots", () => {
    const compare = (operator: Operator, value: bigint) => ({
      ...eq(value),
      operator,
    });

    it("zips a single array, against a word that comes after it", async () => {
      const { roles, allowFunction, invoke } = await loadFixture(
        setupOneArrayOneWord,
      );

      // every element is at most half of the second parameter, which is
      // plucked after the array: an ArrayEvery would run before it
      await allowFunction(
        flattenCondition(
          and(
            {
              paramType: Encoding.AbiEncoded,
              operator: Operator.Matches,
              children: [pluckArray(0), pluckWord(1)],
            },
            {
              paramType: Encoding.None,
              operator: Operator.ZipEvery,
              compValue: encodeCompValue(0),
              children: [fields(and(pluckWord(2), ratio(1, 2, 0, 5000)))],
            },
          ),
        ),
        ExecutionOptions.Both,
      );

      await invoke([10, 50], 100);

      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke([10, 60], 100),
        roles,
        "ConditionViolation",
        [
          ConditionViolationStatus.NotEveryZippedElementPasses,
          anyValue,
          anyValue,
        ],
      );
    });

    it("zips an array with itself", async () => {
      const { roles, allowFunction, invoke } =
        await loadFixture(setupOneArray);

      // both fields see the same element: every element is above 1 and
      // below 10
      await allowFunction(
        flattenCondition(
          and(
            {
              paramType: Encoding.AbiEncoded,
              operator: Operator.Matches,
              children: [pluckArray(0)],
            },
            {
              paramType: Encoding.None,
              operator: Operator.ZipEvery,
              compValue: encodeCompValue(0, 0),
              children: [
                fields(
                  compare(Operator.GreaterThan, 1n),
                  compare(Operator.LessThan, 10n),
                ),
              ],
            },
          ),
        ),
        ExecutionOptions.Both,
      );

      await invoke([2, 3]);

      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke([2, 30]),
        roles,
        "ConditionViolation",
        [
          ConditionViolationStatus.NotEveryZippedElementPasses,
          anyValue,
          anyValue,
        ],
      );
    });
  });
});
