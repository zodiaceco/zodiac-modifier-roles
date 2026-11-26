import { after, describe, it } from "node:test";
import { anyValue } from "@nomicfoundation/hardhat-viem-assertions/predicates";
import {
  encodeAbiParameters,
  encodeFunctionData,
  encodePacked,
  maxUint256,
  parseAbi,
  parseAbiParameters,
  toFunctionSelector,
  zeroAddress,
  type Address,
  type Hex,
} from "viem";

import { network } from "hardhat";

import { createSetup } from "../setup.js";
import {
  Encoding,
  flattenCondition,
  Operator,
  ExecutionOptions,
  ConditionViolationStatus,
  packConditions,
} from "../utils.js";

function pluck(index: number) {
  return {
    paramType: Encoding.Static,
    operator: Operator.Pluck,
    compValue: "0x" + index.toString(16).padStart(2, "0"),
  };
}

// Helper to create correct structure: Matches only has structural children (plucks),
// WithinRatio is a sibling in an And wrapper
function matchesWithRatio(
  plucks: ReturnType<typeof pluck>[],
  withinRatioCompValue: Hex,
) {
  return {
    paramType: Encoding.None,
    operator: Operator.And,
    children: [
      {
        paramType: Encoding.AbiEncoded,
        operator: Operator.Matches,
        children: plucks,
      },
      {
        paramType: Encoding.None,
        operator: Operator.WithinRatio,
        compValue: withinRatioCompValue,
      },
    ],
  };
}

const connection = await network.create();
const { viem, networkHelpers } = connection;
const { loadFixture } = networkHelpers;
const { setupTestContract, setupFn } = createSetup(connection);
const setupTwoParams = setupFn("function fn(uint256, uint256)");

after(async () => {
  await connection.close();
});

describe("Operator - WithinRatio", () => {
  describe("Core Functionality", () => {
    describe("ratio bounds", () => {
      describe("maxRatio", () => {
        it("passes when ratio equals maxRatio (boundary)", async () => {
          const { allowFunction, invoke } = await loadFixture(setupTwoParams);

          // Swapped: param0→relative, param1→reference
          const compValue = encodeWithinRatioCompValue({
            referencePluckIndex: 7,
            referenceDecimals: 0,
            relativePluckIndex: 3,
            relativeDecimals: 0,
            minRatio: 0,
            maxRatio: 9500, // 95%
          });

          await allowFunction(
            flattenCondition(matchesWithRatio([pluck(3), pluck(7)], compValue)),
          );

          // invoke(relative, reference): Ratio = 950/1000 = 95% == maxRatio → pass
          await invoke(950n, 1000n);
        });

        it("passes when ratio is below maxRatio", async () => {
          const { allowFunction, invoke } = await loadFixture(setupTwoParams);

          const compValue = encodeWithinRatioCompValue({
            referencePluckIndex: 5,
            referenceDecimals: 0,
            relativePluckIndex: 2,
            relativeDecimals: 0,
            minRatio: 0,
            maxRatio: 9500,
          });

          await allowFunction(
            flattenCondition(matchesWithRatio([pluck(5), pluck(2)], compValue)),
          );

          // Ratio = 800/1000 = 80% < 95% → pass
          await invoke(1000n, 800n);
        });

        it("reverts with RatioAboveMax when ratio exceeds maxRatio", async () => {
          const { roles, allowFunction, invoke } =
            await loadFixture(setupTwoParams);

          // Swapped order: relative plucked before reference
          const compValue = encodeWithinRatioCompValue({
            referencePluckIndex: 4,
            referenceDecimals: 0,
            relativePluckIndex: 12,
            relativeDecimals: 0,
            minRatio: 0,
            maxRatio: 9500,
          });

          await allowFunction(
            flattenCondition(
              matchesWithRatio([pluck(12), pluck(4)], compValue),
            ),
          );

          // invoke(relative, reference) since param0→relative, param1→reference
          // Ratio = 951/1000 = 95.1% > 95% → fail
          await viem.assertions.revertWithCustomErrorWithArgs(
            invoke(951n, 1000n),
            roles,
            "ConditionViolation",
            [
              ConditionViolationStatus.RatioAboveMax,
              2n, // WithinRatio node
              anyValue,
            ],
          );
        });

        it("skips check when maxRatio is 0 (no upper bound)", async () => {
          const { allowFunction, invoke } = await loadFixture(setupTwoParams);

          const compValue = encodeWithinRatioCompValue({
            referencePluckIndex: 8,
            referenceDecimals: 0,
            relativePluckIndex: 15,
            relativeDecimals: 0,
            minRatio: 1000, // 10% lower bound (at least one bound required)
            maxRatio: 0, // no upper bound
          });

          await allowFunction(
            flattenCondition(
              matchesWithRatio([pluck(8), pluck(15)], compValue),
            ),
          );

          // Ratio = 5000/1000 = 500% → pass (no upper bound, above 10% min)
          await invoke(1000n, 5000n);
        });
      });

      describe("minRatio", () => {
        it("passes when ratio equals minRatio (boundary)", async () => {
          const { allowFunction, invoke } = await loadFixture(setupTwoParams);

          // Swapped: param0→relative, param1→reference
          const compValue = encodeWithinRatioCompValue({
            referencePluckIndex: 20,
            referenceDecimals: 0,
            relativePluckIndex: 10,
            relativeDecimals: 0,
            minRatio: 9000, // 90%
            maxRatio: 0,
          });

          await allowFunction(
            flattenCondition(
              matchesWithRatio([pluck(10), pluck(20)], compValue),
            ),
          );

          // invoke(relative, reference): Ratio = 900/1000 = 90% == minRatio → pass
          await invoke(900n, 1000n);
        });

        it("passes when ratio is above minRatio", async () => {
          const { allowFunction, invoke } = await loadFixture(setupTwoParams);

          // Swapped order: relative plucked before reference
          const compValue = encodeWithinRatioCompValue({
            referencePluckIndex: 6,
            referenceDecimals: 0,
            relativePluckIndex: 1,
            relativeDecimals: 0,
            minRatio: 9000,
            maxRatio: 0,
          });

          await allowFunction(
            flattenCondition(matchesWithRatio([pluck(1), pluck(6)], compValue)),
          );

          // Ratio = 950/1000 = 95% > 90% → pass
          await invoke(950n, 1000n);
        });

        it("reverts with RatioBelowMin when ratio is below minRatio", async () => {
          const { roles, allowFunction, invoke } =
            await loadFixture(setupTwoParams);

          const compValue = encodeWithinRatioCompValue({
            referencePluckIndex: 25,
            referenceDecimals: 0,
            relativePluckIndex: 30,
            relativeDecimals: 0,
            minRatio: 9000,
            maxRatio: 0,
          });

          await allowFunction(
            flattenCondition(
              matchesWithRatio([pluck(25), pluck(30)], compValue),
            ),
          );

          // Ratio = 850/1000 = 85% < 90% → fail
          await viem.assertions.revertWithCustomErrorWithArgs(
            invoke(1000n, 850n),
            roles,
            "ConditionViolation",
            [
              ConditionViolationStatus.RatioBelowMin,
              2n, // WithinRatio node
              anyValue,
            ],
          );
        });

        it("skips check when minRatio is 0 (no lower bound)", async () => {
          const { allowFunction, invoke } = await loadFixture(setupTwoParams);

          // Swapped: param0→pluckedValues[50]=relative, param1→pluckedValues[100]=reference
          const compValue = encodeWithinRatioCompValue({
            referencePluckIndex: 100,
            referenceDecimals: 0,
            relativePluckIndex: 50,
            relativeDecimals: 0,
            minRatio: 0, // no lower bound
            maxRatio: 10000,
          });

          await allowFunction(
            flattenCondition(
              matchesWithRatio([pluck(50), pluck(100)], compValue),
            ),
          );

          // invoke(relative, reference) → ratio = 10/1000 = 1% → pass (no lower bound)
          await invoke(10n, 1000n);
        });
      });
    });

    describe("decimal normalization", () => {
      it("normalizes when reference has more decimals (with relative adapter)", async () => {
        const { roles, allowFunction, invoke } =
          await loadFixture(setupTwoParams);

        // param0→relative (USDC), param1→reference (ETH)
        // Reference: 18 decimals (ETH), Relative: 6 decimals (USDC)
        // Relative adapter: 1 USDC = 0.0005 ETH (price in 18 decimals)
        const usdcEthAdapter = await viem.deployContract("MockPricing", [
          5n * 10n ** 14n,
        ]); // 0.0005 ETH

        const compValue = encodeWithinRatioCompValue({
          relativeAdapter: usdcEthAdapter.address,
          referencePluckIndex: 9,
          referenceDecimals: 18,
          relativePluckIndex: 14,
          relativeDecimals: 6,
          minRatio: 9900,
          maxRatio: 10100,
        });

        await allowFunction(
          flattenCondition(matchesWithRatio([pluck(14), pluck(9)], compValue)),
        );

        // invoke(relative, reference)
        // Reference: 1 ETH (18 decimals)
        // Relative: 2000 USDC (6 decimals) × 0.0005 = 1 ETH equivalent
        // Ratio = 100%
        await invoke(2000n * 10n ** 6n, 1n * 10n ** 18n);

        // Relative: 1980 USDC × 0.0005 = 0.99 ETH → 99% (boundary)
        await invoke(1980n * 10n ** 6n, 1n * 10n ** 18n);

        // Relative: 1970 USDC × 0.0005 = 0.985 ETH → 98.5% < 99%
        await viem.assertions.revertWithCustomErrorWithArgs(
          invoke(1970n * 10n ** 6n, 1n * 10n ** 18n),
          roles,
          "ConditionViolation",
          [
            ConditionViolationStatus.RatioBelowMin,
            2n, // WithinRatio node
            anyValue,
          ],
        );
      });

      it("normalizes when relative has more decimals (with reference adapter)", async () => {
        const { roles, allowFunction, invoke } =
          await loadFixture(setupTwoParams);

        // Swapped: param0→pluckedValues[11]=relative, param1→pluckedValues[22]=reference
        // Reference: 8 decimals (WBTC), Relative: 18 decimals (ETH)
        // Reference adapter: 1 WBTC = 75 ETH (price in 18 decimals)
        const wbtcEthAdapter = await viem.deployContract("MockPricing", [
          75n * 10n ** 18n,
        ]);

        const compValue = encodeWithinRatioCompValue({
          referenceAdapter: wbtcEthAdapter.address,
          referencePluckIndex: 22,
          referenceDecimals: 8,
          relativePluckIndex: 11,
          relativeDecimals: 18,
          minRatio: 9900,
          maxRatio: 10100,
        });

        await allowFunction(
          flattenCondition(matchesWithRatio([pluck(11), pluck(22)], compValue)),
        );

        // invoke(relative, reference)
        // Reference: 1 WBTC (8 decimals) × 75 = 75 ETH equivalent
        // Relative: 75 ETH (18 decimals)
        // Ratio = 100%
        await invoke(75n * 10n ** 18n, 1n * 10n ** 8n);

        // Relative: 74.25 ETH → 99%
        await invoke(7425n * 10n ** 16n, 1n * 10n ** 8n);

        // Relative: 76.01 ETH → 101.3% > 101%
        await viem.assertions.revertWithCustomErrorWithArgs(
          invoke(7601n * 10n ** 16n, 1n * 10n ** 8n),
          roles,
          "ConditionViolation",
          [
            ConditionViolationStatus.RatioAboveMax,
            2n, // WithinRatio node
            anyValue,
          ],
        );
      });

      it("handles maximum decimal difference with adapters (6 vs 27 decimals)", async () => {
        const { roles, allowFunction, invoke } =
          await loadFixture(setupTwoParams);

        // Reference: USDC (6 decimals), Relative: ExoticToken (27 decimals)
        // Reference adapter: 1 USDC = 1 USD (stable)
        // Relative adapter: 1 ExoticToken = 0.5 USD
        const usdcUsdAdapter = await viem.deployContract("MockPricing", [
          1n * 10n ** 18n,
        ]);
        const exoticUsdAdapter = await viem.deployContract("MockPricing", [
          5n * 10n ** 17n,
        ]); // 0.5 USD

        const compValue = encodeWithinRatioCompValue({
          referenceAdapter: usdcUsdAdapter.address,
          relativeAdapter: exoticUsdAdapter.address,
          referencePluckIndex: 77,
          referenceDecimals: 6,
          relativePluckIndex: 88,
          relativeDecimals: 27,
          minRatio: 9900,
          maxRatio: 10100,
        });

        await allowFunction(
          flattenCondition(matchesWithRatio([pluck(77), pluck(88)], compValue)),
        );

        // Reference: 1000 USDC × 1 = 1000 USD
        // Relative: 2000 ExoticToken × 0.5 = 1000 USD
        // Ratio = 100%
        await invoke(1000n * 10n ** 6n, 2000n * 10n ** 27n);

        // Relative: 2020 ExoticToken × 0.5 = 1010 USD → 101%
        await invoke(1000n * 10n ** 6n, 2020n * 10n ** 27n);

        // Relative: 2030 ExoticToken × 0.5 = 1015 USD → 101.5% > 101%
        await viem.assertions.revertWithCustomErrorWithArgs(
          invoke(1000n * 10n ** 6n, 2030n * 10n ** 27n),
          roles,
          "ConditionViolation",
          [
            ConditionViolationStatus.RatioAboveMax,
            2n, // WithinRatio node
            anyValue,
          ],
        );
      });
    });

    describe("price adapters", () => {
      it("applies single adapter to reference amount", async () => {
        const { roles, allowFunction, invoke } =
          await loadFixture(setupTwoParams);

        // Swapped: param0→relative (USD), param1→reference (token)
        // Reference adapter: 1 token = 2000 USD
        const refAdapter = await viem.deployContract("MockPricing", [
          2000n * 10n ** 18n,
        ]);

        const compValue = encodeWithinRatioCompValue({
          referenceAdapter: refAdapter.address,
          referencePluckIndex: 44,
          referenceDecimals: 18,
          relativePluckIndex: 33,
          relativeDecimals: 18,
          minRatio: 9900, // 99%
          maxRatio: 10100, // 101%
        });

        await allowFunction(
          flattenCondition(matchesWithRatio([pluck(33), pluck(44)], compValue)),
        );

        // invoke(relative, reference)
        // Reference: 10 tokens × 2000 = 20,000 USD
        // Relative: 20,000 USD × 1 = 20,000 USD
        // Ratio = 100%
        await invoke(20000n * 10n ** 18n, 10n * 10n ** 18n);

        // Relative: 19,700 USD → Ratio = 98.5% < 99%
        await viem.assertions.revertWithCustomErrorWithArgs(
          invoke(19700n * 10n ** 18n, 10n * 10n ** 18n),
          roles,
          "ConditionViolation",
          [
            ConditionViolationStatus.RatioBelowMin,
            2n, // WithinRatio node
            anyValue,
          ],
        );
      });

      it("applies single adapter to relative amount", async () => {
        const { roles, allowFunction, invoke } =
          await loadFixture(setupTwoParams);

        // Relative adapter: 1 token = 150,000 USD
        const relAdapter = await viem.deployContract("MockPricing", [
          150000n * 10n ** 18n,
        ]);

        // Swapped order: relative plucked before reference
        const compValue = encodeWithinRatioCompValue({
          relativeAdapter: relAdapter.address,
          referencePluckIndex: 55,
          referenceDecimals: 18,
          relativePluckIndex: 17,
          relativeDecimals: 8, // WBTC uses 8 decimals
          minRatio: 9900,
          maxRatio: 10100,
        });

        await allowFunction(
          flattenCondition(matchesWithRatio([pluck(17), pluck(55)], compValue)),
        );

        // invoke(relative, reference) since param0→relative, param1→reference
        // Relative: 0.3 WBTC × 150,000 = 45,000 USD
        // Reference: 45,000 USD × 1 = 45,000 USD
        // Ratio = 100%
        await invoke(3n * 10n ** 7n, 45000n * 10n ** 18n);

        // Relative: 0.297 WBTC × 150,000 = 44,550 USD → Ratio = 99%
        await invoke(297n * 10n ** 5n, 45000n * 10n ** 18n);

        // Relative: 0.2967 WBTC → Ratio ≈ 98.9% < 99%
        await viem.assertions.revertWithCustomErrorWithArgs(
          invoke(2967n * 10n ** 4n, 45000n * 10n ** 18n),
          roles,
          "ConditionViolation",
          [
            ConditionViolationStatus.RatioBelowMin,
            2n, // WithinRatio node
            anyValue,
          ],
        );
      });

      it("applies adapters to both amounts (cross-asset)", async () => {
        const { roles, allowFunction, invoke } =
          await loadFixture(setupTwoParams);

        // ETH/USD: 1 ETH = 2000 USD
        // BTC/USD: 1 BTC = 150,000 USD
        const ethUsdAdapter = await viem.deployContract("MockPricing", [
          2000n * 10n ** 18n,
        ]);
        const btcUsdAdapter = await viem.deployContract("MockPricing", [
          150000n * 10n ** 18n,
        ]);

        const compValue = encodeWithinRatioCompValue({
          referenceAdapter: ethUsdAdapter.address,
          relativeAdapter: btcUsdAdapter.address,
          referencePluckIndex: 200,
          referenceDecimals: 18, // ETH
          relativePluckIndex: 150,
          relativeDecimals: 8, // BTC
          minRatio: 9950,
          maxRatio: 10050,
        });

        await allowFunction(
          flattenCondition(
            matchesWithRatio([pluck(200), pluck(150)], compValue),
          ),
        );

        // Reference: 22.5 ETH × 2000 = 45,000 USD
        // Relative: 0.3 BTC × 150,000 = 45,000 USD
        // Ratio = 100%
        await invoke(225n * 10n ** 17n, 3n * 10n ** 7n);

        // Relative: 0.2985 BTC → Ratio = 99.5%
        await invoke(225n * 10n ** 17n, 2985n * 10n ** 4n);

        // Relative: 0.30225 BTC → Ratio = 100.75% > 100.5%
        await viem.assertions.revertWithCustomErrorWithArgs(
          invoke(225n * 10n ** 17n, 30225n * 10n ** 4n),
          roles,
          "ConditionViolation",
          [
            ConditionViolationStatus.RatioAboveMax,
            2n, // WithinRatio node
            anyValue,
          ],
        );
      });

      it("applies reference adapter only (33-byte compValue)", async () => {
        const { allowFunction, invoke } = await loadFixture(setupTwoParams);

        // Reference adapter: 1 token = 2000 USD, no relative adapter
        const refAdapter = await viem.deployContract("MockPricing", [
          2000n * 10n ** 18n,
        ]);

        // 33-byte encoding: base(12) + refLen(1) + refAdapter(20)
        const compValue = encodePacked(
          [
            "uint8",
            "uint8",
            "uint8",
            "uint8",
            "uint32",
            "uint32",
            "uint8",
            "address",
          ],
          [
            44, // referencePluckIndex
            18, // referenceDecimals
            33, // relativePluckIndex
            18, // relativeDecimals
            9900, // minRatio (99%)
            10100, // maxRatio (101%)
            20, // refBlobLen (address only, no params)
            refAdapter.address,
          ],
        );

        await allowFunction(
          flattenCondition(matchesWithRatio([pluck(33), pluck(44)], compValue)),
        );

        // Reference: 10 tokens × 2000 = 20,000 USD
        // Relative: 20,000 USD × 1 (no adapter) = 20,000 USD
        // Ratio = 100%
        await invoke(20000n * 10n ** 18n, 10n * 10n ** 18n);
      });

      it("applies relative adapter only (54-byte compValue)", async () => {
        const { allowFunction, invoke } = await loadFixture(setupTwoParams);

        // Relative adapter only: 1 WBTC = 150,000 USD
        const relAdapter = await viem.deployContract("MockPricing", [
          150000n * 10n ** 18n,
        ]);

        // 54-byte encoding: base(12) + refLen(1) + refAdapter(20) + relLen(1) + relAdapter(20)
        const compValue = encodePacked(
          [
            "uint8",
            "uint8",
            "uint8",
            "uint8",
            "uint32",
            "uint32",
            "uint8",
            "address",
            "uint8",
            "address",
          ],
          [
            55, // referencePluckIndex (USD)
            18, // referenceDecimals
            17, // relativePluckIndex (WBTC)
            8, // relativeDecimals
            9900, // minRatio
            10100, // maxRatio
            20, // refBlobLen (address only, no params)
            zeroAddress, // no reference adapter
            20, // relBlobLen (address only, no params)
            relAdapter.address,
          ],
        );

        await allowFunction(
          flattenCondition(matchesWithRatio([pluck(17), pluck(55)], compValue)),
        );

        // Reference: 45,000 USD × 1 (no adapter) = 45,000 USD
        // Relative: 0.3 WBTC × 150,000 = 45,000 USD
        // Ratio = 100%
        await invoke(3n * 10n ** 7n, 45000n * 10n ** 18n);
      });
    });

    describe("conversion precision", () => {
      it("rejects an above-max ratio before adapter conversion truncates a tiny amount", async () => {
        const { roles, allowFunction, invoke } =
          await loadFixture(setupTwoParams);

        // We set the price to 1.999999999999999999, making the real ratio
        // ~200%, and configure maxRatio at 100%. The check should reject, but
        // converting each side separately truncates 1.999... to 1, so it sees
        // 100% and wrongly accepts.

        const relativeAdapter = await viem.deployContract("MockPricing", [
          2n * 10n ** 18n - 1n,
        ]);

        const compValue = encodeWithinRatioCompValue({
          relativeAdapter: relativeAdapter.address,
          referencePluckIndex: 2,
          referenceDecimals: 0,
          relativePluckIndex: 1,
          relativeDecimals: 0,
          minRatio: 0,
          maxRatio: 10000,
        });

        await allowFunction(
          flattenCondition(matchesWithRatio([pluck(1), pluck(2)], compValue)),
        );

        // Real ratio ~200% vs maxRatio 100% → must revert with RatioAboveMax
        await viem.assertions.revertWithCustomErrorWithArgs(
          invoke(1n, 1n),
          roles,
          "ConditionViolation",
          [
            ConditionViolationStatus.RatioAboveMax,
            2n, // WithinRatio node
            anyValue,
          ],
        );
      });

      it("rejects a ratio less than one bps above max", async () => {
        const { roles, allowFunction, invoke } =
          await loadFixture(setupTwoParams);

        const compValue = encodeWithinRatioCompValue({
          referencePluckIndex: 2,
          referenceDecimals: 0,
          relativePluckIndex: 1,
          relativeDecimals: 0,
          minRatio: 0,
          maxRatio: 10000,
        });

        await allowFunction(
          flattenCondition(matchesWithRatio([pluck(1), pluck(2)], compValue)),
        );

        // Real ratio 10002/10001 ≈ 100.00999...% — above max by less than one
        // bps. A rounded-down ratio would floor to exactly 100% and wrongly
        // accept.
        await viem.assertions.revertWithCustomErrorWithArgs(
          invoke(10002n, 10001n),
          roles,
          "ConditionViolation",
          [
            ConditionViolationStatus.RatioAboveMax,
            2n, // WithinRatio node
            anyValue,
          ],
        );
      });

      it("accepts a ratio less than one bps below max", async () => {
        const { roles, allowFunction, invoke } =
          await loadFixture(setupTwoParams);

        const compValue = encodeWithinRatioCompValue({
          referencePluckIndex: 2,
          referenceDecimals: 0,
          relativePluckIndex: 1,
          relativeDecimals: 0,
          minRatio: 0,
          maxRatio: 10000,
        });

        await allowFunction(
          flattenCondition(matchesWithRatio([pluck(1), pluck(2)], compValue)),
        );

        // Real ratio 10000/10001 is below the max, despite its ceiled bps
        // representation being exactly 10000.
        await invoke(10000n, 10001n);

        // reversing the amounts puts the ratio just above max.
        await viem.assertions.revertWithCustomErrorWithArgs(
          invoke(10001n, 10000n),
          roles,
          "ConditionViolation",
          [
            ConditionViolationStatus.RatioAboveMax,
            2n, // WithinRatio node
            anyValue,
          ],
        );
      });

      it("rejects a ratio less than one bps below min", async () => {
        const { roles, allowFunction, invoke } =
          await loadFixture(setupTwoParams);

        const compValue = encodeWithinRatioCompValue({
          referencePluckIndex: 2,
          referenceDecimals: 0,
          relativePluckIndex: 1,
          relativeDecimals: 0,
          minRatio: 10000,
          maxRatio: 0,
        });

        await allowFunction(
          flattenCondition(matchesWithRatio([pluck(1), pluck(2)], compValue)),
        );

        // Real ratio 99999/100000 is below the min by one tenth of a bps.
        await viem.assertions.revertWithCustomErrorWithArgs(
          invoke(99999n, 100000n),
          roles,
          "ConditionViolation",
          [
            ConditionViolationStatus.RatioBelowMin,
            2n, // WithinRatio node
            anyValue,
          ],
        );
      });

      it("handles extreme values, failing closed beyond uint256 headroom", async () => {
        const { allowFunction, invoke } = await loadFixture(setupTwoParams);

        const compValue = encodeWithinRatioCompValue({
          referencePluckIndex: 2,
          referenceDecimals: 0,
          relativePluckIndex: 1,
          relativeDecimals: 0,
          minRatio: 9000,
          maxRatio: 11000,
        });

        await allowFunction(
          flattenCondition(matchesWithRatio([pluck(1), pluck(2)], compValue)),
        );

        // Equal extreme values → ratio exactly 100%
        await invoke(10n ** 50n, 10n ** 50n);

        // Beyond the supported magnitude the cross products overflow and the
        // check reverts rather than wrapping around
        await viem.assertions.revert(invoke(maxUint256, maxUint256));
      });
    });

    describe("zero reference", () => {
      it("reverts with RatioAboveMax when reference is zero and relative is not", async () => {
        const { roles, allowFunction, invoke } =
          await loadFixture(setupTwoParams);

        const compValue = encodeWithinRatioCompValue({
          referencePluckIndex: 2,
          referenceDecimals: 0,
          relativePluckIndex: 1,
          relativeDecimals: 0,
          minRatio: 0,
          maxRatio: 10000,
        });

        await allowFunction(
          flattenCondition(matchesWithRatio([pluck(1), pluck(2)], compValue)),
        );

        // Any nonzero relative amount exceeds a max bound on a zero reference
        await viem.assertions.revertWithCustomErrorWithArgs(
          invoke(1n, 0n),
          roles,
          "ConditionViolation",
          [
            ConditionViolationStatus.RatioAboveMax,
            2n, // WithinRatio node
            anyValue,
          ],
        );
      });

      it("passes when both amounts are zero", async () => {
        const { allowFunction, invoke } = await loadFixture(setupTwoParams);

        const compValue = encodeWithinRatioCompValue({
          referencePluckIndex: 2,
          referenceDecimals: 0,
          relativePluckIndex: 1,
          relativeDecimals: 0,
          minRatio: 9000,
          maxRatio: 11000,
        });

        await allowFunction(
          flattenCondition(matchesWithRatio([pluck(1), pluck(2)], compValue)),
        );

        await invoke(0n, 0n);
      });

      it("passes a zero reference when only a min bound is set", async () => {
        const { allowFunction, invoke } = await loadFixture(setupTwoParams);

        const compValue = encodeWithinRatioCompValue({
          referencePluckIndex: 2,
          referenceDecimals: 0,
          relativePluckIndex: 1,
          relativeDecimals: 0,
          minRatio: 1000,
          maxRatio: 0,
        });

        await allowFunction(
          flattenCondition(matchesWithRatio([pluck(1), pluck(2)], compValue)),
        );

        // min bound is vacuous against a zero reference
        await invoke(5n, 0n);
      });
    });

    describe("adapter call safety", () => {
      it("reverts with PricingAdapterNotAContract when reference adapter not deployed", async () => {
        const { roles, allowFunction, invoke } =
          await loadFixture(setupTwoParams);

        const [, , randomEOA] = await viem.getWalletClients();

        const compValue = encodeWithinRatioCompValue({
          referenceAdapter: randomEOA.account.address,
          referencePluckIndex: 41,
          referenceDecimals: 18,
          relativePluckIndex: 82,
          relativeDecimals: 18,
          minRatio: 9000,
          maxRatio: 11000,
        });

        await allowFunction(
          flattenCondition(matchesWithRatio([pluck(41), pluck(82)], compValue)),
        );

        await viem.assertions.revertWithCustomErrorWithArgs(
          invoke(1000n, 1000n),
          roles,
          "ConditionViolation",
          [
            ConditionViolationStatus.PricingAdapterNotAContract,
            2n, // WithinRatio node
            anyValue,
          ],
        );
      });

      it("reverts with PricingAdapterNotAContract when relative adapter not deployed", async () => {
        const { roles, allowFunction, invoke } =
          await loadFixture(setupTwoParams);

        const [, , randomEOA] = await viem.getWalletClients();

        // Swapped order: relative plucked before reference
        const compValue = encodeWithinRatioCompValue({
          relativeAdapter: randomEOA.account.address,
          referencePluckIndex: 99,
          referenceDecimals: 18,
          relativePluckIndex: 13,
          relativeDecimals: 18,
          minRatio: 9000,
          maxRatio: 11000,
        });

        await allowFunction(
          flattenCondition(matchesWithRatio([pluck(13), pluck(99)], compValue)),
        );

        await viem.assertions.revertWithCustomErrorWithArgs(
          invoke(1000n, 1000n),
          roles,
          "ConditionViolation",
          [
            ConditionViolationStatus.PricingAdapterNotAContract,
            2n, // WithinRatio node
            anyValue,
          ],
        );
      });

      it("reverts with PricingAdapterReverted when adapter has no getPrice function", async () => {
        const { roles, allowFunction, invoke } =
          await loadFixture(setupTwoParams);

        const noInterfaceAdapter = await viem.deployContract(
          "MockPricingNoInterface",
        );

        const compValue = encodeWithinRatioCompValue({
          referenceAdapter: noInterfaceAdapter.address,
          referencePluckIndex: 63,
          referenceDecimals: 18,
          relativePluckIndex: 27,
          relativeDecimals: 18,
          minRatio: 9000,
          maxRatio: 11000,
        });

        await allowFunction(
          flattenCondition(matchesWithRatio([pluck(63), pluck(27)], compValue)),
        );

        await viem.assertions.revertWithCustomErrorWithArgs(
          invoke(1000n, 1000n),
          roles,
          "ConditionViolation",
          [
            ConditionViolationStatus.PricingAdapterReverted,
            2n, // WithinRatio node
            anyValue,
          ],
        );
      });

      it("reverts with PricingAdapterReverted when adapter reverts", async () => {
        const { roles, allowFunction, invoke } =
          await loadFixture(setupTwoParams);

        const revertingAdapter = await viem.deployContract(
          "MockPricingReverting",
        );

        // Swapped order: relative plucked before reference
        const compValue = encodeWithinRatioCompValue({
          referenceAdapter: revertingAdapter.address,
          referencePluckIndex: 180,
          referenceDecimals: 18,
          relativePluckIndex: 45,
          relativeDecimals: 18,
          minRatio: 9000,
          maxRatio: 11000,
        });

        await allowFunction(
          flattenCondition(
            matchesWithRatio([pluck(45), pluck(180)], compValue),
          ),
        );

        await viem.assertions.revertWithCustomErrorWithArgs(
          invoke(1000n, 1000n),
          roles,
          "ConditionViolation",
          [
            ConditionViolationStatus.PricingAdapterReverted,
            2n, // WithinRatio node
            anyValue,
          ],
        );
      });

      it("reverts with PricingAdapterInvalidResult when adapter returns wrong type", async () => {
        const { roles, allowFunction, invoke } =
          await loadFixture(setupTwoParams);

        const wrongReturnAdapter = await viem.deployContract(
          "MockPricingWrongReturn",
        );

        const compValue = encodeWithinRatioCompValue({
          referenceAdapter: wrongReturnAdapter.address,
          referencePluckIndex: 72,
          referenceDecimals: 18,
          relativePluckIndex: 108,
          relativeDecimals: 18,
          minRatio: 9000,
          maxRatio: 11000,
        });

        await allowFunction(
          flattenCondition(
            matchesWithRatio([pluck(72), pluck(108)], compValue),
          ),
        );

        await viem.assertions.revertWithCustomErrorWithArgs(
          invoke(1000n, 1000n),
          roles,
          "ConditionViolation",
          [
            ConditionViolationStatus.PricingAdapterInvalidResult,
            2n, // WithinRatio node
            anyValue,
          ],
        );
      });

      it("reverts with PricingAdapterZeroPrice when adapter returns zero", async () => {
        const { roles, allowFunction, invoke } =
          await loadFixture(setupTwoParams);

        const zeroAdapter = await viem.deployContract("MockPricing", [0n]);

        // Swapped order: relative plucked before reference
        const compValue = encodeWithinRatioCompValue({
          referenceAdapter: zeroAdapter.address,
          referencePluckIndex: 56,
          referenceDecimals: 18,
          relativePluckIndex: 23,
          relativeDecimals: 18,
          minRatio: 9000,
          maxRatio: 11000,
        });

        await allowFunction(
          flattenCondition(matchesWithRatio([pluck(23), pluck(56)], compValue)),
        );

        await viem.assertions.revertWithCustomErrorWithArgs(
          invoke(1000n, 1000n),
          roles,
          "ConditionViolation",
          [
            ConditionViolationStatus.PricingAdapterZeroPrice,
            2n, // WithinRatio node
            anyValue,
          ],
        );
      });
    });
  });

  describe("parameterized adapters", () => {
    it("ref with params, rel with params", async () => {
      const { roles, allowFunction, invoke } =
        await loadFixture(setupTwoParams);

      const refAdapter = await viem.deployContract("MockPricingParameterized");
      const relAdapter = await viem.deployContract("MockPricingParameterized");

      const refParams = "0xaaaa";
      const relParams = "0xbbbbcccc";

      await refAdapter.write.setPrice([refParams, 2000n * 10n ** 18n]);
      await relAdapter.write.setPrice([relParams, 1n * 10n ** 18n]);

      // counterfactual: wrong rel params → adapter reverts
      const wrongCompValue = encodeWithinRatioCompValue({
        referencePluckIndex: 3,
        referenceDecimals: 0,
        relativePluckIndex: 7,
        relativeDecimals: 0,
        minRatio: 9000,
        maxRatio: 11000,
        referenceAdapter: refAdapter.address,
        relativeAdapter: relAdapter.address,
        referenceParams: refParams,
        relativeParams: "0xffff",
      });
      await allowFunction(
        flattenCondition(
          matchesWithRatio([pluck(3), pluck(7)], wrongCompValue),
        ),
      );
      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke(1n, 2000n),
        roles,
        "ConditionViolation",
        [ConditionViolationStatus.PricingAdapterReverted, 2n, anyValue],
      );

      // correct params
      const compValue = encodeWithinRatioCompValue({
        referencePluckIndex: 3,
        referenceDecimals: 0,
        relativePluckIndex: 7,
        relativeDecimals: 0,
        minRatio: 9000,
        maxRatio: 11000,
        referenceAdapter: refAdapter.address,
        relativeAdapter: relAdapter.address,
        referenceParams: refParams,
        relativeParams: relParams,
      });
      await allowFunction(
        flattenCondition(matchesWithRatio([pluck(3), pluck(7)], compValue)),
      );

      // ref=1 * 2000 = 2000, rel=2000 * 1 = 2000, ratio=10000 (100%) → pass
      await invoke(1n, 2000n);

      // ref=1 * 2000 = 2000, rel=1600 * 1 = 1600, ratio=8000 (80%) < 90% → fail
      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke(1n, 1600n),
        roles,
        "ConditionViolation",
        [ConditionViolationStatus.RatioBelowMin, 2n, anyValue],
      );
    });

    it("ref with adapter no params, rel with params", async () => {
      const { roles, allowFunction, invoke } =
        await loadFixture(setupTwoParams);

      const relAdapter = await viem.deployContract("MockPricingParameterized");
      const relParams = "0xdeadbeef";
      await relAdapter.write.setPrice([relParams, 3n * 10n ** 18n]); // 3x

      // ref adapter requires empty params
      const refAdapter = await viem.deployContract("MockPricingEmptyParams", [
        2n * 10n ** 18n,
      ]); // 2x

      // counterfactual: wrong rel params → adapter reverts
      const wrongCompValue = encodeWithinRatioCompValue({
        referencePluckIndex: 3,
        referenceDecimals: 0,
        relativePluckIndex: 7,
        relativeDecimals: 0,
        minRatio: 9000,
        maxRatio: 11000,
        referenceAdapter: refAdapter.address,
        relativeAdapter: relAdapter.address,
        relativeParams: "0xcafebabe",
      });
      await allowFunction(
        flattenCondition(
          matchesWithRatio([pluck(3), pluck(7)], wrongCompValue),
        ),
      );
      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke(100n, 60n),
        roles,
        "ConditionViolation",
        [ConditionViolationStatus.PricingAdapterReverted, 2n, anyValue],
      );

      // correct params
      const compValue = encodeWithinRatioCompValue({
        referencePluckIndex: 3,
        referenceDecimals: 0,
        relativePluckIndex: 7,
        relativeDecimals: 0,
        minRatio: 9000,
        maxRatio: 11000,
        referenceAdapter: refAdapter.address,
        relativeAdapter: relAdapter.address,
        relativeParams: relParams,
      });
      await allowFunction(
        flattenCondition(matchesWithRatio([pluck(3), pluck(7)], compValue)),
      );

      // ref=100 * 2 = 200, rel=60 * 3 = 180, ratio=9000 (90%) → pass
      await invoke(100n, 60n);
    });

    it("ref without adapter, rel with params", async () => {
      const { roles, allowFunction, invoke } =
        await loadFixture(setupTwoParams);

      const relAdapter = await viem.deployContract("MockPricingParameterized");
      const relParams = "0xdeadbeef";
      await relAdapter.write.setPrice([relParams, 2n * 10n ** 18n]); // 2x

      // counterfactual: wrong rel params → adapter reverts
      const wrongCompValue = encodeWithinRatioCompValue({
        referencePluckIndex: 3,
        referenceDecimals: 0,
        relativePluckIndex: 7,
        relativeDecimals: 0,
        minRatio: 9000,
        maxRatio: 11000,
        relativeAdapter: relAdapter.address,
        relativeParams: "0xcafebabe",
      });
      await allowFunction(
        flattenCondition(
          matchesWithRatio([pluck(3), pluck(7)], wrongCompValue),
        ),
      );
      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke(1000n, 500n),
        roles,
        "ConditionViolation",
        [ConditionViolationStatus.PricingAdapterReverted, 2n, anyValue],
      );

      // correct params, ref blobLen=0 (no adapter)
      const compValue = encodeWithinRatioCompValue({
        referencePluckIndex: 3,
        referenceDecimals: 0,
        relativePluckIndex: 7,
        relativeDecimals: 0,
        minRatio: 9000,
        maxRatio: 11000,
        relativeAdapter: relAdapter.address,
        relativeParams: relParams,
      });
      await allowFunction(
        flattenCondition(matchesWithRatio([pluck(3), pluck(7)], compValue)),
      );

      // ref=1000 * 1 = 1000, rel=500 * 2 = 1000, ratio=10000 → pass
      await invoke(1000n, 500n);
    });
  });

  describe("Real-World Scenarios", () => {
    it("ETH/USD swap - validates output within slippage tolerance", async () => {
      const { roles, allowFunction, invoke } =
        await loadFixture(setupTwoParams);

      // ETH/USD: 1 ETH = 2000 USD
      const ethUsdAdapter = await viem.deployContract("MockPricing", [
        2000n * 10n ** 18n,
      ]);

      // Swapped order: relative (USD output) plucked before reference (ETH input)
      const compValue = encodeWithinRatioCompValue({
        referenceAdapter: ethUsdAdapter.address,
        relativeAdapter: zeroAddress,
        referencePluckIndex: 19,
        referenceDecimals: 18, // ETH
        relativePluckIndex: 7,
        relativeDecimals: 18, // USD stablecoin
        minRatio: 9950, // 99.5% (0.5% tolerance)
        maxRatio: 10050, // 100.5%
      });

      await allowFunction(
        flattenCondition(matchesWithRatio([pluck(7), pluck(19)], compValue)),
      );

      // invoke(relative, reference) since param0→relative (USD), param1→reference (ETH)
      // Selling 10 ETH for 20,000 USD → exactly 100%
      await invoke(20000n * 10n ** 18n, 10n * 10n ** 18n);

      // Selling 10 ETH for 19,880 USD → 99.4% < 99.5%
      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke(19880n * 10n ** 18n, 10n * 10n ** 18n),
        roles,
        "ConditionViolation",
        [
          ConditionViolationStatus.RatioBelowMin,
          2n, // WithinRatio node
          anyValue,
        ],
      );

      // Selling 10 ETH for 20,120 USD → 100.6% > 100.5%
      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke(20120n * 10n ** 18n, 10n * 10n ** 18n),
        roles,
        "ConditionViolation",
        [
          ConditionViolationStatus.RatioAboveMax,
          2n, // WithinRatio node
          anyValue,
        ],
      );
    });

    it("WBTC/ETH swap - cross-asset with different decimals", async () => {
      const { roles, allowFunction, invoke } =
        await loadFixture(setupTwoParams);

      // Swapped: param0→relative (WBTC), param1→reference (ETH)
      // ETH/USD: 1 ETH = 2000 USD
      // BTC/USD: 1 BTC = 150,000 USD
      const ethUsdAdapter = await viem.deployContract("MockPricing", [
        2000n * 10n ** 18n,
      ]);
      const btcUsdAdapter = await viem.deployContract("MockPricing", [
        150000n * 10n ** 18n,
      ]);

      const compValue = encodeWithinRatioCompValue({
        referenceAdapter: ethUsdAdapter.address,
        relativeAdapter: btcUsdAdapter.address,
        referencePluckIndex: 91,
        referenceDecimals: 18, // ETH
        relativePluckIndex: 42,
        relativeDecimals: 8, // WBTC
        minRatio: 9500, // 95%
        maxRatio: 10500, // 105% (5% slippage)
      });

      await allowFunction(
        flattenCondition(matchesWithRatio([pluck(42), pluck(91)], compValue)),
      );

      // invoke(relative, reference)
      // Selling 75 ETH ($150,000) for 1 BTC ($150,000) → 100%
      await invoke(1n * 10n ** 8n, 75n * 10n ** 18n);

      // Selling 75 ETH for 0.94 BTC → 94% < 95%
      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke(94n * 10n ** 6n, 75n * 10n ** 18n),
        roles,
        "ConditionViolation",
        [
          ConditionViolationStatus.RatioBelowMin,
          2n, // WithinRatio node
          anyValue,
        ],
      );

      // Selling 75 ETH for 1.06 BTC → 106% > 105%
      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke(106n * 10n ** 6n, 75n * 10n ** 18n),
        roles,
        "ConditionViolation",
        [
          ConditionViolationStatus.RatioAboveMax,
          2n, // WithinRatio node
          anyValue,
        ],
      );
    });

    it("USDC/exotic token swap - maximum decimal difference", async () => {
      const { roles, allowFunction, invoke } =
        await loadFixture(setupTwoParams);

      // ExoticToken/USDC: 1 ExoticToken = 2 USDC
      const exoticUsdcAdapter = await viem.deployContract("MockPricing", [
        2n * 10n ** 18n,
      ]);

      // Swapped: param0→pluckedValues[61]=relative (ExoticToken), param1→pluckedValues[83]=reference (USDC)
      const compValue = encodeWithinRatioCompValue({
        referenceAdapter: zeroAddress,
        relativeAdapter: exoticUsdcAdapter.address,
        referencePluckIndex: 83,
        referenceDecimals: 6, // USDC
        relativePluckIndex: 61,
        relativeDecimals: 27, // ExoticToken
        minRatio: 9975, // 99.75%
        maxRatio: 10025, // 100.25%
      });

      await allowFunction(
        flattenCondition(matchesWithRatio([pluck(61), pluck(83)], compValue)),
      );

      // invoke(relative, reference) since param0→relative (ExoticToken), param1→reference (USDC)
      // Selling 1000 USDC for 500 ExoticToken → (500 × 2) / 1000 = 100%
      await invoke(500n * 10n ** 27n, 1000n * 10n ** 6n);

      // Selling 1000 USDC for 498.7 ExoticToken → 99.74% < 99.75%
      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke(4987n * 10n ** 24n, 1000n * 10n ** 6n),
        roles,
        "ConditionViolation",
        [
          ConditionViolationStatus.RatioBelowMin,
          2n, // WithinRatio node
          anyValue,
        ],
      );
    });

    it("no adapters - enforces min 25% ratio", async () => {
      const { roles, allowFunction, invoke } =
        await loadFixture(setupTwoParams);

      // No price adapters - direct token ratio comparison
      const compValue = encodeWithinRatioCompValue({
        referencePluckIndex: 37,
        referenceDecimals: 18,
        relativePluckIndex: 53,
        relativeDecimals: 18,
        minRatio: 2500, // 25%
        maxRatio: 0, // no upper bound
      });

      await allowFunction(
        flattenCondition(matchesWithRatio([pluck(37), pluck(53)], compValue)),
      );

      // 249 / 1000 = 24.9% < 25% → fail
      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke(1000n * 10n ** 18n, 249n * 10n ** 18n),
        roles,
        "ConditionViolation",
        [
          ConditionViolationStatus.RatioBelowMin,
          2n, // WithinRatio node
          anyValue,
        ],
      );

      // 250 / 1000 = 25% → pass
      await invoke(1000n * 10n ** 18n, 250n * 10n ** 18n);

      // 300 / 1000 = 30% → pass
      await invoke(1000n * 10n ** 18n, 300n * 10n ** 18n);
    });

    it("no adapters - enforces max 500% ratio", async () => {
      const { roles, allowFunction, invoke } =
        await loadFixture(setupTwoParams);

      // Swapped: param0→relative, param1→reference
      const compValue = encodeWithinRatioCompValue({
        referencePluckIndex: 64,
        referenceDecimals: 18,
        relativePluckIndex: 28,
        relativeDecimals: 18,
        minRatio: 0, // no lower bound
        maxRatio: 50000, // 500%
      });

      await allowFunction(
        flattenCondition(matchesWithRatio([pluck(28), pluck(64)], compValue)),
      );

      // invoke(relative, reference)
      // 4900 / 1000 = 490% → pass
      await invoke(4900n * 10n ** 18n, 1000n * 10n ** 18n);

      // 5000 / 1000 = 500% → pass (boundary)
      await invoke(5000n * 10n ** 18n, 1000n * 10n ** 18n);

      // 5001 / 1000 = 500.1% → fail
      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke(5001n * 10n ** 18n, 1000n * 10n ** 18n),
        roles,
        "ConditionViolation",
        [
          ConditionViolationStatus.RatioAboveMax,
          2n, // WithinRatio node
          anyValue,
        ],
      );
    });

    it("USD/WBTC swap - WBTC converts to USD base via relative adapter", async () => {
      const { roles, allowFunction, invoke } =
        await loadFixture(setupTwoParams);

      // WBTC/USD adapter: 1 WBTC = 150,000 USD
      const wbtcUsdAdapter = await viem.deployContract("MockPricing", [
        150000n * 10n ** 18n,
      ]);

      const compValue = encodeWithinRatioCompValue({
        referenceAdapter: zeroAddress, // USD stablecoin is the base (no conversion)
        relativeAdapter: wbtcUsdAdapter.address,
        referencePluckIndex: 71,
        referenceDecimals: 18, // USD stablecoin
        relativePluckIndex: 18,
        relativeDecimals: 8, // WBTC uses 8 decimals
        minRatio: 9900, // 99%
        maxRatio: 10100, // 101% (1% slippage)
      });

      await allowFunction(
        flattenCondition(matchesWithRatio([pluck(71), pluck(18)], compValue)),
      );

      // Reference: 45,000 USD, Relative: 0.3 WBTC × 150,000 = 45,000 USD → 100%
      await invoke(45000n * 10n ** 18n, 3n * 10n ** 7n);

      // Relative: 0.297 WBTC → 44,550 / 45,000 = 99% → pass
      await invoke(45000n * 10n ** 18n, 297n * 10n ** 5n);

      // Relative: 0.2967 WBTC → 44,505 / 45,000 = 98.9% → fail
      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke(45000n * 10n ** 18n, 2967n * 10n ** 4n),
        roles,
        "ConditionViolation",
        [
          ConditionViolationStatus.RatioBelowMin,
          2n, // WithinRatio node
          anyValue,
        ],
      );
    });

    it("ETH/WBTC swap - converts to ETH base via relative adapter", async () => {
      const { roles, allowFunction, invoke } =
        await loadFixture(setupTwoParams);

      // Swapped: param0→relative (WBTC), param1→reference (ETH)
      // WBTC/ETH adapter: 1 WBTC = 75 ETH
      const wbtcEthAdapter = await viem.deployContract("MockPricing", [
        75n * 10n ** 18n,
      ]);

      const compValue = encodeWithinRatioCompValue({
        referenceAdapter: zeroAddress, // ETH is the base
        relativeAdapter: wbtcEthAdapter.address,
        referencePluckIndex: 95,
        referenceDecimals: 18, // ETH
        relativePluckIndex: 33,
        relativeDecimals: 8, // WBTC
        minRatio: 9500, // 95%
        maxRatio: 10500, // 105% (5% slippage)
      });

      await allowFunction(
        flattenCondition(matchesWithRatio([pluck(33), pluck(95)], compValue)),
      );

      // invoke(relative, reference)
      // Reference: 75 ETH, Relative: 1 WBTC × 75 = 75 ETH → 100%
      await invoke(1n * 10n ** 8n, 75n * 10n ** 18n);

      // Relative: 0.95 WBTC → 71.25 / 75 = 95% → pass
      await invoke(95n * 10n ** 6n, 75n * 10n ** 18n);

      // Relative: 0.949 WBTC → 71.175 / 75 = 94.9% → fail
      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke(949n * 10n ** 5n, 75n * 10n ** 18n),
        roles,
        "ConditionViolation",
        [
          ConditionViolationStatus.RatioBelowMin,
          2n, // WithinRatio node
          anyValue,
        ],
      );

      // Relative: 1.051 WBTC → 78.825 / 75 = 105.1% → fail
      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke(1051n * 10n ** 5n, 75n * 10n ** 18n),
        roles,
        "ConditionViolation",
        [
          ConditionViolationStatus.RatioAboveMax,
          2n, // WithinRatio node
          anyValue,
        ],
      );
    });
    it("handles WBTC (8 decimals) vs FunkyToken (27 decimals) both with adapters", async () => {
      const { roles, allowFunction, invoke } =
        await loadFixture(setupTwoParams);

      // Reference: WBTC (8 decimals), price = $100,000
      // Relative: FunkyToken (27 decimals), price = $2
      const wbtcAdapter = await viem.deployContract("MockPricing", [
        100000n * 10n ** 18n,
      ]);
      const funkyAdapter = await viem.deployContract("MockPricing", [
        2n * 10n ** 18n,
      ]);

      const compValue = encodeWithinRatioCompValue({
        referenceAdapter: wbtcAdapter.address,
        relativeAdapter: funkyAdapter.address,
        referencePluckIndex: 3,
        referenceDecimals: 8,
        relativePluckIndex: 7,
        relativeDecimals: 27,
        minRatio: 9900,
        maxRatio: 10100,
      });

      await allowFunction(
        flattenCondition(matchesWithRatio([pluck(3), pluck(7)], compValue)),
      );

      // Reference: 1 WBTC × $100,000 = $100,000
      // Relative: 50,000 FunkyToken × $2 = $100,000
      // Ratio = 100%
      await invoke(1n * 10n ** 8n, 50000n * 10n ** 27n);

      // Relative: 49,500 FunkyToken × $2 = $99,000 → 99%
      await invoke(1n * 10n ** 8n, 49500n * 10n ** 27n);

      // Relative: 49,400 FunkyToken × $2 = $98,800 → 98.8% < 99%
      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke(1n * 10n ** 8n, 49400n * 10n ** 27n),
        roles,
        "ConditionViolation",
        [
          ConditionViolationStatus.RatioBelowMin,
          2n, // WithinRatio node
          anyValue,
        ],
      );

      // Relative: 50,600 FunkyToken × $2 = $101,200 → 101.2% > 101%
      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke(1n * 10n ** 8n, 50600n * 10n ** 27n),
        roles,
        "ConditionViolation",
        [
          ConditionViolationStatus.RatioAboveMax,
          2n, // WithinRatio node
          anyValue,
        ],
      );
    });
  });

  describe("Parameter Extraction", () => {
    it("extracts values from AbiEncoded params", async () => {
      const abi = parseAbi(["function mixedParams(uint256, bytes, uint256)"]);
      const selector = toFunctionSelector(abi[0]);
      const { roles, member, testContractAddress, roleKey } =
        await loadFixture(setupTestContract);

      const compValue = encodeWithinRatioCompValue({
        referencePluckIndex: 0,
        referenceDecimals: 0,
        relativePluckIndex: 1,
        relativeDecimals: 0,
        minRatio: 0,
        maxRatio: 12000, // 120%
      });

      const packed = await packConditions(
        roles,
        flattenCondition({
          paramType: Encoding.None,
          operator: Operator.And,
          children: [
            {
              paramType: Encoding.AbiEncoded,
              operator: Operator.Matches,
              children: [
                pluck(0), // param 0 → pluckedValues[0]
                { paramType: Encoding.Dynamic, operator: Operator.Pass },
                pluck(1), // param 2 → pluckedValues[1]
              ],
            },
            {
              paramType: Encoding.None,
              operator: Operator.WithinRatio,
              compValue,
            },
          ],
        }),
      );
      await roles.write.allowFunctionPacked([
        roleKey,
        testContractAddress,
        selector,
        packed,
        ExecutionOptions.None,
      ]);

      const invoke = (a: bigint, b: bigint) =>
        roles.write.execTransactionFromModule(
          [
            testContractAddress,
            0n,
            encodeFunctionData({
              abi,
              functionName: "mixedParams",
              args: [a, "0xaabbcc", b],
            }),
            0,
          ],
          { account: member.account },
        );

      // 1200 / 1000 = 120% → pass
      await invoke(1000n, 1200n);

      // 1201 / 1000 = 120.1% > 120% → fail
      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke(1000n, 1201n),
        roles,
        "ConditionViolation",
        [
          ConditionViolationStatus.RatioAboveMax,
          2n, // WithinRatio node (And=0, Matches=1, WithinRatio=2)
          anyValue,
        ],
      );
    });

    it("extracts values from nested AbiEncoded", async () => {
      const abi = parseAbi(["function dynamic(bytes)"]);
      const selector = toFunctionSelector(abi[0]);
      const { roles, member, testContractAddress, roleKey } =
        await loadFixture(setupTestContract);

      const compValue = encodeWithinRatioCompValue({
        referencePluckIndex: 0,
        referenceDecimals: 0,
        relativePluckIndex: 1,
        relativeDecimals: 0,
        minRatio: 0,
        maxRatio: 8000, // 80%
      });

      const packed = await packConditions(
        roles,
        flattenCondition({
          paramType: Encoding.None,
          operator: Operator.And,
          children: [
            {
              paramType: Encoding.AbiEncoded,
              operator: Operator.Matches,
              children: [
                {
                  paramType: Encoding.AbiEncoded,
                  operator: Operator.Matches,
                  compValue: "0x0000", // leadingBytes = 0
                  children: [
                    pluck(0), // encoded[0] → pluckedValues[0]
                    { paramType: Encoding.Static, operator: Operator.Pass },
                    pluck(1), // encoded[2] → pluckedValues[1]
                  ],
                },
              ],
            },
            {
              paramType: Encoding.None,
              operator: Operator.WithinRatio,
              compValue,
            },
          ],
        }),
      );
      await roles.write.allowFunctionPacked([
        roleKey,
        testContractAddress,
        selector,
        packed,
        ExecutionOptions.None,
      ]);

      const invoke = (encoded: Hex) =>
        roles.write.execTransactionFromModule(
          [
            testContractAddress,
            0n,
            encodeFunctionData({
              abi,
              functionName: "dynamic",
              args: [encoded],
            }),
            0,
          ],
          { account: member.account },
        );

      // 800 / 1000 = 80% → pass
      const encoded = encodeAbiParameters(
        parseAbiParameters("uint256, uint256, uint256"),
        [1000n, 500n, 800n],
      );
      await invoke(encoded);

      // 801 / 1000 = 80.1% > 80% → fail
      const encodedFail = encodeAbiParameters(
        parseAbiParameters("uint256, uint256, uint256"),
        [1000n, 500n, 801n],
      );
      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke(encodedFail),
        roles,
        "ConditionViolation",
        [
          ConditionViolationStatus.RatioAboveMax,
          2n, // WithinRatio node: And[0] -> Matches[1], WithinRatio[2]
          anyValue,
        ],
      );
    });

    it("extracts values from Tuple", async () => {
      const abi = parseAbi([
        "function mixedTuple((uint256 amount, uint256 second, uint256 limit, uint256 fourth))",
      ]);
      const selector = toFunctionSelector(abi[0]);
      const { roles, member, testContractAddress, roleKey } =
        await loadFixture(setupTestContract);

      const compValue = encodeWithinRatioCompValue({
        referencePluckIndex: 0,
        referenceDecimals: 0,
        relativePluckIndex: 1,
        relativeDecimals: 0,
        minRatio: 0,
        maxRatio: 15000, // 150%
      });

      const packed = await packConditions(
        roles,
        flattenCondition({
          paramType: Encoding.None,
          operator: Operator.And,
          children: [
            {
              paramType: Encoding.AbiEncoded,
              operator: Operator.Matches,
              children: [
                {
                  paramType: Encoding.Tuple,
                  operator: Operator.Matches,
                  children: [
                    { paramType: Encoding.Static, operator: Operator.Pass }, // amount
                    pluck(0), // second → pluckedValues[0] (reference)
                    { paramType: Encoding.Static, operator: Operator.Pass }, // limit
                    pluck(1), // fourth → pluckedValues[1] (relative)
                  ],
                },
              ],
            },
            {
              paramType: Encoding.None,
              operator: Operator.WithinRatio,
              compValue,
            },
          ],
        }),
      );
      await roles.write.allowFunctionPacked([
        roleKey,
        testContractAddress,
        selector,
        packed,
        ExecutionOptions.None,
      ]);

      const invoke = (
        amount: bigint,
        second: bigint,
        limit: bigint,
        fourth: bigint,
      ) =>
        roles.write.execTransactionFromModule(
          [
            testContractAddress,
            0n,
            encodeFunctionData({
              abi,
              functionName: "mixedTuple",
              args: [{ amount, second, limit, fourth }],
            }),
            0,
          ],
          { account: member.account },
        );

      // 1500 / 1000 = 150% → pass
      await invoke(500n, 1000n, 800n, 1500n);

      // 1501 / 1000 = 150.1% > 150% → fail
      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke(500n, 1000n, 800n, 1501n),
        roles,
        "ConditionViolation",
        [
          ConditionViolationStatus.RatioAboveMax,
          2n, // WithinRatio node: And[0] -> Matches[1], WithinRatio[2]
          anyValue,
        ],
      );
    });

    it("WithinRatio inside And as tuple field - Tuple(Static, And(WithinRatio, Static))", async () => {
      const abi = parseAbi(["function twoParams(uint256 ref, uint256 rel)"]);
      const selector = toFunctionSelector(abi[0]);
      const { roles, member, testContractAddress, roleKey } =
        await loadFixture(setupTestContract);

      const compValue = encodeWithinRatioCompValue({
        referencePluckIndex: 0,
        referenceDecimals: 0,
        relativePluckIndex: 1,
        relativeDecimals: 0,
        minRatio: 0,
        maxRatio: 15000, // 150%
      });

      const packed = await packConditions(
        roles,
        flattenCondition({
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          children: [
            {
              // First tuple field: just a Pluck
              paramType: Encoding.Static,
              operator: Operator.Pluck,
              compValue: "0x00", // pluckedValues[0] = reference
            },
            {
              // Second tuple field: And wrapping WithinRatio + Pluck
              paramType: Encoding.None,
              operator: Operator.And,
              children: [
                {
                  paramType: Encoding.Static,
                  operator: Operator.Pluck,
                  compValue: "0x01", // pluckedValues[1] = relative
                },
                {
                  paramType: Encoding.None,
                  operator: Operator.WithinRatio,
                  compValue,
                },
              ],
            },
          ],
        }),
      );
      await roles.write.allowFunctionPacked([
        roleKey,
        testContractAddress,
        selector,
        packed,
        ExecutionOptions.None,
      ]);

      const invoke = (reference: bigint, relative: bigint) =>
        roles.write.execTransactionFromModule(
          [
            testContractAddress,
            0n,
            encodeFunctionData({
              abi,
              functionName: "twoParams",
              args: [reference, relative],
            }),
            0,
          ],
          { account: member.account },
        );

      // 1500 / 1000 = 150% → pass
      await invoke(1000n, 1500n);

      // 1501 / 1000 = 150.1% > 150% → fail
      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke(1000n, 1501n),
        roles,
        "ConditionViolation",
        [
          ConditionViolationStatus.RatioAboveMax,
          4n, // WithinRatio: Matches[0] -> Pluck[1], And[2] -> Pluck[3], WithinRatio[4]
          anyValue,
        ],
      );
    });

    it("extracts values from Array", async () => {
      const abi = parseAbi(["function uint256ArrayStatic(uint256[])"]);
      const selector = toFunctionSelector(abi[0]);
      const { roles, member, testContractAddress, roleKey } =
        await loadFixture(setupTestContract);

      const compValue = encodeWithinRatioCompValue({
        referencePluckIndex: 0,
        referenceDecimals: 0,
        relativePluckIndex: 1,
        relativeDecimals: 0,
        minRatio: 0,
        maxRatio: 12000, // 120%
      });

      const packed = await packConditions(
        roles,
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
                  operator: Operator.Matches,
                  children: [
                    pluck(0), // array[0] → pluckedValues[0] (reference)
                    { paramType: Encoding.Static, operator: Operator.Pass },
                    pluck(1), // array[2] → pluckedValues[1] (relative)
                  ],
                },
              ],
            },
            {
              paramType: Encoding.None,
              operator: Operator.WithinRatio,
              compValue,
            },
          ],
        }),
      );
      await roles.write.allowFunctionPacked([
        roleKey,
        testContractAddress,
        selector,
        packed,
        ExecutionOptions.None,
      ]);

      const invoke = (arr: bigint[]) =>
        roles.write.execTransactionFromModule(
          [
            testContractAddress,
            0n,
            encodeFunctionData({
              abi,
              functionName: "uint256ArrayStatic",
              args: [arr],
            }),
            0,
          ],
          { account: member.account },
        );

      // 1200 / 1000 = 120% → pass
      await invoke([1000n, 500n, 1200n]);

      // 1201 / 1000 = 120.1% > 120% → fail
      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke([1000n, 500n, 1201n]),
        roles,
        "ConditionViolation",
        [
          ConditionViolationStatus.RatioAboveMax,
          2n, // WithinRatio node: And[0] -> Matches[1], WithinRatio[2]
          anyValue,
        ],
      );
    });

    it("extracts sliced values from bytes parameter", async () => {
      const abi = parseAbi(["function dynamicParam(bytes)"]);
      const selector = toFunctionSelector(abi[0]);
      const { roles, member, testContractAddress, roleKey } =
        await loadFixture(setupTestContract);

      // Slice compValue: 2 bytes shift + 1 byte size
      const sliceCompValue = (shift: number, size: number) =>
        encodePacked(["uint16", "uint8"], [shift, size]);

      const compValue = encodeWithinRatioCompValue({
        referencePluckIndex: 0,
        referenceDecimals: 0,
        relativePluckIndex: 1,
        relativeDecimals: 0,
        minRatio: 9000, // 90%
        maxRatio: 11000, // 110%
      });

      // Structure: And[Matches[And[Slice[Pluck], Slice[Pluck]]], WithinRatio]
      // Extract two 4-byte values from bytes at different offsets
      const packed = await packConditions(
        roles,
        flattenCondition({
          paramType: Encoding.None,
          operator: Operator.And,
          children: [
            {
              paramType: Encoding.AbiEncoded,
              operator: Operator.Matches,
              children: [
                {
                  // And inside the Dynamic param to apply multiple slices
                  paramType: Encoding.None,
                  operator: Operator.And,
                  children: [
                    {
                      // Slice bytes 0-3 → pluckedValues[0] (reference)
                      paramType: Encoding.Dynamic,
                      operator: Operator.Slice,
                      compValue: sliceCompValue(0, 4),
                      children: [
                        {
                          paramType: Encoding.Static,
                          operator: Operator.Pluck,
                          compValue: "0x00",
                        },
                      ],
                    },
                    {
                      // Slice bytes 4-7 → pluckedValues[1] (relative)
                      paramType: Encoding.Dynamic,
                      operator: Operator.Slice,
                      compValue: sliceCompValue(4, 4),
                      children: [
                        {
                          paramType: Encoding.Static,
                          operator: Operator.Pluck,
                          compValue: "0x01",
                        },
                      ],
                    },
                  ],
                },
              ],
            },
            {
              paramType: Encoding.None,
              operator: Operator.WithinRatio,
              compValue,
            },
          ],
        }),
      );
      await roles.write.allowFunctionPacked([
        roleKey,
        testContractAddress,
        selector,
        packed,
        ExecutionOptions.None,
      ]);

      const invoke = (bytesData: Hex) =>
        roles.write.execTransactionFromModule(
          [
            testContractAddress,
            0n,
            encodeFunctionData({
              abi,
              functionName: "dynamicParam",
              args: [bytesData],
            }),
            0,
          ],
          { account: member.account },
        );

      // bytes: [reference: 4 bytes][relative: 4 bytes]
      // reference = 0x000003e8 (1000), relative = 0x000003e8 (1000) → 100%
      await invoke("0x000003e8000003e8");

      // reference = 0x000003e8 (1000), relative = 0x00000384 (900) → 90%
      await invoke("0x000003e800000384");

      // reference = 0x000003e8 (1000), relative = 0x00000379 (889) → 88.9% < 90%
      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke("0x000003e800000379"),
        roles,
        "ConditionViolation",
        [ConditionViolationStatus.RatioBelowMin, anyValue, anyValue],
      );

      // reference = 0x000003e8 (1000), relative = 0x00000451 (1105) → 110.5% > 110%
      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke("0x000003e800000451"),
        roles,
        "ConditionViolation",
        [ConditionViolationStatus.RatioAboveMax, anyValue, anyValue],
      );
    });

    it("extracts EtherValue", async () => {
      // Different pattern - uses single param + ether value, keep inline
      const abi = parseAbi(["function fn(uint256)"]);
      const selector = toFunctionSelector(abi[0]);
      const { roles, member, testContractAddress, roleKey } =
        await loadFixture(setupTestContract);

      // Pluck ether value → pluckedValues[0]
      // Pluck param → pluckedValues[1]
      const compValue = encodeWithinRatioCompValue({
        referencePluckIndex: 0,
        referenceDecimals: 18,
        relativePluckIndex: 1,
        relativeDecimals: 18,
        minRatio: 0,
        maxRatio: 20000, // 200%
      });

      const packed = await packConditions(
        roles,
        flattenCondition({
          paramType: Encoding.None,
          operator: Operator.And,
          children: [
            {
              paramType: Encoding.AbiEncoded,
              operator: Operator.Matches,
              children: [pluck(1)],
            },
            {
              paramType: Encoding.EtherValue,
              operator: Operator.Pluck,
              compValue: "0x00",
            },
            {
              paramType: Encoding.None,
              operator: Operator.WithinRatio,
              compValue,
            },
          ],
        }),
      );
      await roles.write.allowFunctionPacked([
        roleKey,
        testContractAddress,
        selector,
        packed,
        ExecutionOptions.Send,
      ]);

      // 2 ETH / 1 ETH = 200% → pass
      await roles.write.execTransactionFromModule(
        [
          testContractAddress,
          10n ** 18n,
          encodeFunctionData({
            abi,
            functionName: "fn",
            args: [2n * 10n ** 18n],
          }),
          0,
        ],
        { account: member.account },
      );

      // 1 ETH / 1 ETH = 100% → pass
      await roles.write.execTransactionFromModule(
        [
          testContractAddress,
          10n ** 18n,
          encodeFunctionData({
            abi,
            functionName: "fn",
            args: [1n * 10n ** 18n],
          }),
          0,
        ],
        { account: member.account },
      );

      // 2.1 ETH / 1 ETH = 210% > 200% → fail
      await viem.assertions.revertWithCustomErrorWithArgs(
        roles.write.execTransactionFromModule(
          [
            testContractAddress,
            10n ** 18n,
            encodeFunctionData({
              abi,
              functionName: "fn",
              args: [21n * 10n ** 17n],
            }),
            0,
          ],
          { account: member.account },
        ),
        roles,
        "ConditionViolation",
        [
          ConditionViolationStatus.RatioAboveMax,
          3n, // WithinRatio node: And[0] -> Matches[1], Pluck[2], WithinRatio[3]
          anyValue,
        ],
      );
    });
  });

  describe("violation context", () => {
    it("reports the violating node index", async () => {
      const { roles, allowFunction, invoke } =
        await loadFixture(setupTwoParams);

      const compValue = encodeWithinRatioCompValue({
        referencePluckIndex: 7,
        referenceDecimals: 0,
        relativePluckIndex: 3,
        relativeDecimals: 0,
        minRatio: 9000, // 90%
        maxRatio: 11000, // 110%
      });

      await allowFunction(
        flattenCondition(matchesWithRatio([pluck(3), pluck(7)], compValue)),
      );

      // 850 / 1000 = 85% < 90% → fail
      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke(850n, 1000n),
        roles,
        "ConditionViolation",
        [
          ConditionViolationStatus.RatioBelowMin,
          2n, // WithinRatio node at BFS index 3
          anyValue,
        ],
      );
    });

    it("reports the calldata range of the violation", async () => {
      const { roles, allowFunction, invoke } =
        await loadFixture(setupTwoParams);

      const compValue = encodeWithinRatioCompValue({
        referencePluckIndex: 7,
        referenceDecimals: 0,
        relativePluckIndex: 3,
        relativeDecimals: 0,
        minRatio: 0,
        maxRatio: 9000, // 90%
      });

      await allowFunction(
        flattenCondition(matchesWithRatio([pluck(3), pluck(7)], compValue)),
      );

      // 950 / 1000 = 95% > 90% → fail
      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke(950n, 1000n),
        roles,
        "ConditionViolation",
        [
          ConditionViolationStatus.RatioAboveMax,
          anyValue,
          0n, // calldataOffset: WithinRatio uses plucked values, no direct payload
        ],
      );
    });
  });
});

// Helper function to encode compValue for WithinRatio operator
//
// Layout: base(12) [ + refBlob [ + relBlob ] ]
// Each adapter blob: len(1) + address(20) + params(len)
function encodeWithinRatioCompValue({
  referenceAdapter,
  relativeAdapter,
  referencePluckIndex,
  referenceDecimals,
  relativePluckIndex,
  relativeDecimals,
  minRatio,
  maxRatio,
  referenceParams,
  relativeParams,
}: {
  referenceAdapter?: Address;
  relativeAdapter?: Address;
  referencePluckIndex: number;
  referenceDecimals: number;
  relativePluckIndex: number;
  relativeDecimals: number;
  minRatio: number;
  maxRatio: number;
  referenceParams?: Hex;
  relativeParams?: Hex;
}): Hex {
  const base = encodePacked(
    ["uint8", "uint8", "uint8", "uint8", "uint32", "uint32"],
    [
      referencePluckIndex,
      referenceDecimals,
      relativePluckIndex,
      relativeDecimals,
      minRatio,
      maxRatio,
    ],
  );

  if (!referenceAdapter && !relativeAdapter) return base;

  let result = base;

  if (referenceAdapter) {
    const refParamsBytes = referenceParams || "0x";
    const refParamsLen = (refParamsBytes.length - 2) / 2;
    // ref blob: blobLen(1) + address(20) + params(blobLen - 20)
    result = encodePacked(
      ["bytes", "uint8", "address", "bytes"],
      [result, 20 + refParamsLen, referenceAdapter, refParamsBytes],
    );
  } else {
    // blobLen=0: no ref adapter
    result = encodePacked(["bytes", "uint8"], [result, 0]);
  }

  if (relativeAdapter) {
    const relParamsBytes = relativeParams || "0x";
    const relParamsLen = (relParamsBytes.length - 2) / 2;
    // rel blob: blobLen(1) + address(20) + params(blobLen - 20)
    result = encodePacked(
      ["bytes", "uint8", "address", "bytes"],
      [result, 20 + relParamsLen, relativeAdapter, relParamsBytes],
    );
  }

  return result;
}
