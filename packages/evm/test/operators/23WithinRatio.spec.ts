import { expect } from "chai";
import { anyValue } from "@nomicfoundation/hardhat-ethers-chai-matchers/withArgs";

import { AbiCoder, Interface, solidityPacked, ZeroAddress } from "ethers";

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
  withinRatioCompValue: string,
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
const { ethers, networkHelpers } = connection;
const { loadFixture } = networkHelpers;
const { setupTestContract, setupTwoParams } = createSetup(connection);

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
          await expect(invoke(950, 1000)).to.not.be.revert(ethers);
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
          await expect(invoke(1000, 800)).to.not.be.revert(ethers);
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
          await expect(invoke(951, 1000))
            .to.be.revertedWithCustomError(roles, "ConditionViolation")
            .withArgs(
              ConditionViolationStatus.RatioAboveMax,
              2, // WithinRatio node
              anyValue,
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
          await expect(invoke(1000, 5000)).to.not.be.revert(ethers);
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
          await expect(invoke(900, 1000)).to.not.be.revert(ethers);
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
          await expect(invoke(950, 1000)).to.not.be.revert(ethers);
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
          await expect(invoke(1000, 850))
            .to.be.revertedWithCustomError(roles, "ConditionViolation")
            .withArgs(
              ConditionViolationStatus.RatioBelowMin,
              2, // WithinRatio node
              anyValue,
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
          await expect(invoke(10, 1000)).to.not.be.revert(ethers);
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
        const MockPricing = await ethers.getContractFactory("MockPricing");
        const usdcEthAdapter = await MockPricing.deploy(5n * 10n ** 14n); // 0.0005 ETH

        const compValue = encodeWithinRatioCompValue({
          relativeAdapter: await usdcEthAdapter.getAddress(),
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
        await expect(
          invoke(2000n * 10n ** 6n, 1n * 10n ** 18n),
        ).to.not.be.revert(ethers);

        // Relative: 1980 USDC × 0.0005 = 0.99 ETH → 99% (boundary)
        await expect(
          invoke(1980n * 10n ** 6n, 1n * 10n ** 18n),
        ).to.not.be.revert(ethers);

        // Relative: 1970 USDC × 0.0005 = 0.985 ETH → 98.5% < 99%
        await expect(invoke(1970n * 10n ** 6n, 1n * 10n ** 18n))
          .to.be.revertedWithCustomError(roles, "ConditionViolation")
          .withArgs(
            ConditionViolationStatus.RatioBelowMin,
            2, // WithinRatio node
            anyValue,
          );
      });

      it("normalizes when relative has more decimals (with reference adapter)", async () => {
        const { roles, allowFunction, invoke } =
          await loadFixture(setupTwoParams);

        // Swapped: param0→pluckedValues[11]=relative, param1→pluckedValues[22]=reference
        // Reference: 8 decimals (WBTC), Relative: 18 decimals (ETH)
        // Reference adapter: 1 WBTC = 75 ETH (price in 18 decimals)
        const MockPricing = await ethers.getContractFactory("MockPricing");
        const wbtcEthAdapter = await MockPricing.deploy(75n * 10n ** 18n);

        const compValue = encodeWithinRatioCompValue({
          referenceAdapter: await wbtcEthAdapter.getAddress(),
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
        await expect(invoke(75n * 10n ** 18n, 1n * 10n ** 8n)).to.not.be.revert(
          ethers,
        );

        // Relative: 74.25 ETH → 99%
        await expect(
          invoke(7425n * 10n ** 16n, 1n * 10n ** 8n),
        ).to.not.be.revert(ethers);

        // Relative: 76.01 ETH → 101.3% > 101%
        await expect(invoke(7601n * 10n ** 16n, 1n * 10n ** 8n))
          .to.be.revertedWithCustomError(roles, "ConditionViolation")
          .withArgs(
            ConditionViolationStatus.RatioAboveMax,
            2, // WithinRatio node
            anyValue,
          );
      });

      it("handles maximum decimal difference with adapters (6 vs 27 decimals)", async () => {
        const { roles, allowFunction, invoke } =
          await loadFixture(setupTwoParams);

        // Reference: USDC (6 decimals), Relative: ExoticToken (27 decimals)
        // Reference adapter: 1 USDC = 1 USD (stable)
        // Relative adapter: 1 ExoticToken = 0.5 USD
        const MockPricing = await ethers.getContractFactory("MockPricing");
        const usdcUsdAdapter = await MockPricing.deploy(1n * 10n ** 18n);
        const exoticUsdAdapter = await MockPricing.deploy(5n * 10n ** 17n); // 0.5 USD

        const compValue = encodeWithinRatioCompValue({
          referenceAdapter: await usdcUsdAdapter.getAddress(),
          relativeAdapter: await exoticUsdAdapter.getAddress(),
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
        await expect(
          invoke(1000n * 10n ** 6n, 2000n * 10n ** 27n),
        ).to.not.be.revert(ethers);

        // Relative: 2020 ExoticToken × 0.5 = 1010 USD → 101%
        await expect(
          invoke(1000n * 10n ** 6n, 2020n * 10n ** 27n),
        ).to.not.be.revert(ethers);

        // Relative: 2030 ExoticToken × 0.5 = 1015 USD → 101.5% > 101%
        await expect(invoke(1000n * 10n ** 6n, 2030n * 10n ** 27n))
          .to.be.revertedWithCustomError(roles, "ConditionViolation")
          .withArgs(
            ConditionViolationStatus.RatioAboveMax,
            2, // WithinRatio node
            anyValue,
          );
      });
    });

    describe("price adapters", () => {
      it("applies single adapter to reference amount", async () => {
        const { roles, allowFunction, invoke } =
          await loadFixture(setupTwoParams);

        // Swapped: param0→relative (USD), param1→reference (token)
        // Reference adapter: 1 token = 2000 USD
        const MockPricing = await ethers.getContractFactory("MockPricing");
        const refAdapter = await MockPricing.deploy(2000n * 10n ** 18n);

        const compValue = encodeWithinRatioCompValue({
          referenceAdapter: await refAdapter.getAddress(),
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
        await expect(
          invoke(20000n * 10n ** 18n, 10n * 10n ** 18n),
        ).to.not.be.revert(ethers);

        // Relative: 19,700 USD → Ratio = 98.5% < 99%
        await expect(invoke(19700n * 10n ** 18n, 10n * 10n ** 18n))
          .to.be.revertedWithCustomError(roles, "ConditionViolation")
          .withArgs(
            ConditionViolationStatus.RatioBelowMin,
            2, // WithinRatio node
            anyValue,
          );
      });

      it("applies single adapter to relative amount", async () => {
        const { roles, allowFunction, invoke } =
          await loadFixture(setupTwoParams);

        // Relative adapter: 1 token = 150,000 USD
        const MockPricing = await ethers.getContractFactory("MockPricing");
        const relAdapter = await MockPricing.deploy(150000n * 10n ** 18n);

        // Swapped order: relative plucked before reference
        const compValue = encodeWithinRatioCompValue({
          relativeAdapter: await relAdapter.getAddress(),
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
        await expect(
          invoke(3n * 10n ** 7n, 45000n * 10n ** 18n),
        ).to.not.be.revert(ethers);

        // Relative: 0.297 WBTC × 150,000 = 44,550 USD → Ratio = 99%
        await expect(
          invoke(297n * 10n ** 5n, 45000n * 10n ** 18n),
        ).to.not.be.revert(ethers);

        // Relative: 0.2967 WBTC → Ratio ≈ 98.9% < 99%
        await expect(invoke(2967n * 10n ** 4n, 45000n * 10n ** 18n))
          .to.be.revertedWithCustomError(roles, "ConditionViolation")
          .withArgs(
            ConditionViolationStatus.RatioBelowMin,
            2, // WithinRatio node
            anyValue,
          );
      });

      it("applies adapters to both amounts (cross-asset)", async () => {
        const { roles, allowFunction, invoke } =
          await loadFixture(setupTwoParams);

        // ETH/USD: 1 ETH = 2000 USD
        // BTC/USD: 1 BTC = 150,000 USD
        const MockPricing = await ethers.getContractFactory("MockPricing");
        const ethUsdAdapter = await MockPricing.deploy(2000n * 10n ** 18n);
        const btcUsdAdapter = await MockPricing.deploy(150000n * 10n ** 18n);

        const compValue = encodeWithinRatioCompValue({
          referenceAdapter: await ethUsdAdapter.getAddress(),
          relativeAdapter: await btcUsdAdapter.getAddress(),
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
        await expect(
          invoke(225n * 10n ** 17n, 3n * 10n ** 7n),
        ).to.not.be.revert(ethers);

        // Relative: 0.2985 BTC → Ratio = 99.5%
        await expect(
          invoke(225n * 10n ** 17n, 2985n * 10n ** 4n),
        ).to.not.be.revert(ethers);

        // Relative: 0.30225 BTC → Ratio = 100.75% > 100.5%
        await expect(invoke(225n * 10n ** 17n, 30225n * 10n ** 4n))
          .to.be.revertedWithCustomError(roles, "ConditionViolation")
          .withArgs(
            ConditionViolationStatus.RatioAboveMax,
            2, // WithinRatio node
            anyValue,
          );
      });

      it("applies reference adapter only (33-byte compValue)", async () => {
        const { allowFunction, invoke } = await loadFixture(setupTwoParams);

        // Reference adapter: 1 token = 2000 USD, no relative adapter
        const MockPricing = await ethers.getContractFactory("MockPricing");
        const refAdapter = await MockPricing.deploy(2000n * 10n ** 18n);

        // 33-byte encoding: base(12) + refLen(1) + refAdapter(20)
        const compValue = solidityPacked(
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
            await refAdapter.getAddress(),
          ],
        );

        await allowFunction(
          flattenCondition(matchesWithRatio([pluck(33), pluck(44)], compValue)),
        );

        // Reference: 10 tokens × 2000 = 20,000 USD
        // Relative: 20,000 USD × 1 (no adapter) = 20,000 USD
        // Ratio = 100%
        await expect(
          invoke(20000n * 10n ** 18n, 10n * 10n ** 18n),
        ).to.not.be.revert(ethers);
      });

      it("applies relative adapter only (54-byte compValue)", async () => {
        const { roles, allowFunction, invoke } =
          await loadFixture(setupTwoParams);

        // Relative adapter only: 1 WBTC = 150,000 USD
        const MockPricing = await ethers.getContractFactory("MockPricing");
        const relAdapter = await MockPricing.deploy(150000n * 10n ** 18n);

        // 54-byte encoding: base(12) + refLen(1) + refAdapter(20) + relLen(1) + relAdapter(20)
        const compValue = solidityPacked(
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
            "0x0000000000000000000000000000000000000000", // no reference adapter
            20, // relBlobLen (address only, no params)
            await relAdapter.getAddress(),
          ],
        );

        await allowFunction(
          flattenCondition(matchesWithRatio([pluck(17), pluck(55)], compValue)),
        );

        // Reference: 45,000 USD × 1 (no adapter) = 45,000 USD
        // Relative: 0.3 WBTC × 150,000 = 45,000 USD
        // Ratio = 100%
        await expect(
          invoke(3n * 10n ** 7n, 45000n * 10n ** 18n),
        ).to.not.be.revert(ethers);
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

        const MockPricing = await ethers.getContractFactory("MockPricing");
        const relativeAdapter = await MockPricing.deploy(2n * 10n ** 18n - 1n);

        const compValue = encodeWithinRatioCompValue({
          relativeAdapter: await relativeAdapter.getAddress(),
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
        await expect(invoke(1, 1))
          .to.be.revertedWithCustomError(roles, "ConditionViolation")
          .withArgs(
            ConditionViolationStatus.RatioAboveMax,
            2, // WithinRatio node
            anyValue,
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
        await expect(invoke(10002, 10001))
          .to.be.revertedWithCustomError(roles, "ConditionViolation")
          .withArgs(
            ConditionViolationStatus.RatioAboveMax,
            2, // WithinRatio node
            anyValue,
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
        await expect(invoke(10000, 10001)).to.not.be.revert(ethers);

        // reversing the amounts puts the ratio just above max.
        await expect(invoke(10001, 10000))
          .to.be.revertedWithCustomError(roles, "ConditionViolation")
          .withArgs(
            ConditionViolationStatus.RatioAboveMax,
            2, // WithinRatio node
            anyValue,
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
        await expect(invoke(99999, 100000))
          .to.be.revertedWithCustomError(roles, "ConditionViolation")
          .withArgs(
            ConditionViolationStatus.RatioBelowMin,
            2, // WithinRatio node
            anyValue,
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
        await expect(invoke(10n ** 50n, 10n ** 50n)).to.not.be.revert(ethers);

        // Beyond the supported magnitude the cross products overflow and the
        // check reverts rather than wrapping around
        await expect(invoke(ethers.MaxUint256, ethers.MaxUint256)).to.be.revert(
          ethers,
        );
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
        await expect(invoke(1, 0))
          .to.be.revertedWithCustomError(roles, "ConditionViolation")
          .withArgs(
            ConditionViolationStatus.RatioAboveMax,
            2, // WithinRatio node
            anyValue,
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

        await expect(invoke(0, 0)).to.not.be.revert(ethers);
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
        await expect(invoke(5, 0)).to.not.be.revert(ethers);
      });
    });

    describe("adapter call safety", () => {
      it("reverts with PricingAdapterNotAContract when reference adapter not deployed", async () => {
        const { roles, allowFunction, invoke } =
          await loadFixture(setupTwoParams);

        const [, , randomEOA] = await ethers.getSigners();

        const compValue = encodeWithinRatioCompValue({
          referenceAdapter: randomEOA.address,
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

        await expect(invoke(1000, 1000))
          .to.be.revertedWithCustomError(roles, "ConditionViolation")
          .withArgs(
            ConditionViolationStatus.PricingAdapterNotAContract,
            2, // WithinRatio node
            anyValue,
          );
      });

      it("reverts with PricingAdapterNotAContract when relative adapter not deployed", async () => {
        const { roles, allowFunction, invoke } =
          await loadFixture(setupTwoParams);

        const [, , randomEOA] = await ethers.getSigners();

        // Swapped order: relative plucked before reference
        const compValue = encodeWithinRatioCompValue({
          relativeAdapter: randomEOA.address,
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

        await expect(invoke(1000, 1000))
          .to.be.revertedWithCustomError(roles, "ConditionViolation")
          .withArgs(
            ConditionViolationStatus.PricingAdapterNotAContract,
            2, // WithinRatio node
            anyValue,
          );
      });

      it("reverts with PricingAdapterReverted when adapter has no getPrice function", async () => {
        const { roles, allowFunction, invoke } =
          await loadFixture(setupTwoParams);

        const MockPricingNoInterface = await ethers.getContractFactory(
          "MockPricingNoInterface",
        );
        const noInterfaceAdapter = await MockPricingNoInterface.deploy();

        const compValue = encodeWithinRatioCompValue({
          referenceAdapter: await noInterfaceAdapter.getAddress(),
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

        await expect(invoke(1000, 1000))
          .to.be.revertedWithCustomError(roles, "ConditionViolation")
          .withArgs(
            ConditionViolationStatus.PricingAdapterReverted,
            2, // WithinRatio node
            anyValue,
          );
      });

      it("reverts with PricingAdapterReverted when adapter reverts", async () => {
        const { roles, allowFunction, invoke } =
          await loadFixture(setupTwoParams);

        const MockPricingReverting = await ethers.getContractFactory(
          "MockPricingReverting",
        );
        const revertingAdapter = await MockPricingReverting.deploy();

        // Swapped order: relative plucked before reference
        const compValue = encodeWithinRatioCompValue({
          referenceAdapter: await revertingAdapter.getAddress(),
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

        await expect(invoke(1000, 1000))
          .to.be.revertedWithCustomError(roles, "ConditionViolation")
          .withArgs(
            ConditionViolationStatus.PricingAdapterReverted,
            2, // WithinRatio node
            anyValue,
          );
      });

      it("reverts with PricingAdapterInvalidResult when adapter returns wrong type", async () => {
        const { roles, allowFunction, invoke } =
          await loadFixture(setupTwoParams);

        const MockPricingWrongReturn = await ethers.getContractFactory(
          "MockPricingWrongReturn",
        );
        const wrongReturnAdapter = await MockPricingWrongReturn.deploy();

        const compValue = encodeWithinRatioCompValue({
          referenceAdapter: await wrongReturnAdapter.getAddress(),
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

        await expect(invoke(1000, 1000))
          .to.be.revertedWithCustomError(roles, "ConditionViolation")
          .withArgs(
            ConditionViolationStatus.PricingAdapterInvalidResult,
            2, // WithinRatio node
            anyValue,
          );
      });

      it("reverts with PricingAdapterZeroPrice when adapter returns zero", async () => {
        const { roles, allowFunction, invoke } =
          await loadFixture(setupTwoParams);

        const MockPricing = await ethers.getContractFactory("MockPricing");
        const zeroAdapter = await MockPricing.deploy(0);

        // Swapped order: relative plucked before reference
        const compValue = encodeWithinRatioCompValue({
          referenceAdapter: await zeroAdapter.getAddress(),
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

        await expect(invoke(1000, 1000))
          .to.be.revertedWithCustomError(roles, "ConditionViolation")
          .withArgs(
            ConditionViolationStatus.PricingAdapterZeroPrice,
            2, // WithinRatio node
            anyValue,
          );
      });
    });
  });

  describe("parameterized adapters", () => {
    it("ref with params, rel with params", async () => {
      const { roles, allowFunction, invoke } =
        await loadFixture(setupTwoParams);

      const MockPricingParameterized = await ethers.getContractFactory(
        "MockPricingParameterized",
      );
      const refAdapter = await MockPricingParameterized.deploy();
      const relAdapter = await MockPricingParameterized.deploy();

      const refParams = "0xaaaa";
      const relParams = "0xbbbbcccc";

      await refAdapter.setPrice(refParams, 2000n * 10n ** 18n);
      await relAdapter.setPrice(relParams, 1n * 10n ** 18n);

      // counterfactual: wrong rel params → adapter reverts
      const wrongCompValue = encodeWithinRatioCompValue({
        referencePluckIndex: 3,
        referenceDecimals: 0,
        relativePluckIndex: 7,
        relativeDecimals: 0,
        minRatio: 9000,
        maxRatio: 11000,
        referenceAdapter: await refAdapter.getAddress(),
        relativeAdapter: await relAdapter.getAddress(),
        referenceParams: refParams,
        relativeParams: "0xffff",
      });
      await allowFunction(
        flattenCondition(
          matchesWithRatio([pluck(3), pluck(7)], wrongCompValue),
        ),
      );
      await expect(invoke(1, 2000))
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(ConditionViolationStatus.PricingAdapterReverted, 2, anyValue);

      // correct params
      const compValue = encodeWithinRatioCompValue({
        referencePluckIndex: 3,
        referenceDecimals: 0,
        relativePluckIndex: 7,
        relativeDecimals: 0,
        minRatio: 9000,
        maxRatio: 11000,
        referenceAdapter: await refAdapter.getAddress(),
        relativeAdapter: await relAdapter.getAddress(),
        referenceParams: refParams,
        relativeParams: relParams,
      });
      await allowFunction(
        flattenCondition(matchesWithRatio([pluck(3), pluck(7)], compValue)),
      );

      // ref=1 * 2000 = 2000, rel=2000 * 1 = 2000, ratio=10000 (100%) → pass
      await expect(invoke(1, 2000)).to.not.be.revert(ethers);

      // ref=1 * 2000 = 2000, rel=1600 * 1 = 1600, ratio=8000 (80%) < 90% → fail
      await expect(invoke(1, 1600))
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(ConditionViolationStatus.RatioBelowMin, 2, anyValue);
    });

    it("ref with adapter no params, rel with params", async () => {
      const { roles, allowFunction, invoke } =
        await loadFixture(setupTwoParams);

      const MockPricingParameterized = await ethers.getContractFactory(
        "MockPricingParameterized",
      );
      const relAdapter = await MockPricingParameterized.deploy();
      const relParams = "0xdeadbeef";
      await relAdapter.setPrice(relParams, 3n * 10n ** 18n); // 3x

      // ref adapter requires empty params
      const refAdapter = await (
        await ethers.getContractFactory("MockPricingEmptyParams")
      ).deploy(2n * 10n ** 18n); // 2x

      // counterfactual: wrong rel params → adapter reverts
      const wrongCompValue = encodeWithinRatioCompValue({
        referencePluckIndex: 3,
        referenceDecimals: 0,
        relativePluckIndex: 7,
        relativeDecimals: 0,
        minRatio: 9000,
        maxRatio: 11000,
        referenceAdapter: await refAdapter.getAddress(),
        relativeAdapter: await relAdapter.getAddress(),
        relativeParams: "0xcafebabe",
      });
      await allowFunction(
        flattenCondition(
          matchesWithRatio([pluck(3), pluck(7)], wrongCompValue),
        ),
      );
      await expect(invoke(100, 60))
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(ConditionViolationStatus.PricingAdapterReverted, 2, anyValue);

      // correct params
      const compValue = encodeWithinRatioCompValue({
        referencePluckIndex: 3,
        referenceDecimals: 0,
        relativePluckIndex: 7,
        relativeDecimals: 0,
        minRatio: 9000,
        maxRatio: 11000,
        referenceAdapter: await refAdapter.getAddress(),
        relativeAdapter: await relAdapter.getAddress(),
        relativeParams: relParams,
      });
      await allowFunction(
        flattenCondition(matchesWithRatio([pluck(3), pluck(7)], compValue)),
      );

      // ref=100 * 2 = 200, rel=60 * 3 = 180, ratio=9000 (90%) → pass
      await expect(invoke(100, 60)).to.not.be.revert(ethers);
    });

    it("ref without adapter, rel with params", async () => {
      const { roles, allowFunction, invoke } =
        await loadFixture(setupTwoParams);

      const MockPricingParameterized = await ethers.getContractFactory(
        "MockPricingParameterized",
      );
      const relAdapter = await MockPricingParameterized.deploy();
      const relParams = "0xdeadbeef";
      await relAdapter.setPrice(relParams, 2n * 10n ** 18n); // 2x

      // counterfactual: wrong rel params → adapter reverts
      const wrongCompValue = encodeWithinRatioCompValue({
        referencePluckIndex: 3,
        referenceDecimals: 0,
        relativePluckIndex: 7,
        relativeDecimals: 0,
        minRatio: 9000,
        maxRatio: 11000,
        relativeAdapter: await relAdapter.getAddress(),
        relativeParams: "0xcafebabe",
      });
      await allowFunction(
        flattenCondition(
          matchesWithRatio([pluck(3), pluck(7)], wrongCompValue),
        ),
      );
      await expect(invoke(1000, 500))
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(ConditionViolationStatus.PricingAdapterReverted, 2, anyValue);

      // correct params, ref blobLen=0 (no adapter)
      const compValue = encodeWithinRatioCompValue({
        referencePluckIndex: 3,
        referenceDecimals: 0,
        relativePluckIndex: 7,
        relativeDecimals: 0,
        minRatio: 9000,
        maxRatio: 11000,
        relativeAdapter: await relAdapter.getAddress(),
        relativeParams: relParams,
      });
      await allowFunction(
        flattenCondition(matchesWithRatio([pluck(3), pluck(7)], compValue)),
      );

      // ref=1000 * 1 = 1000, rel=500 * 2 = 1000, ratio=10000 → pass
      await expect(invoke(1000, 500)).to.not.be.revert(ethers);
    });
  });

  describe("Real-World Scenarios", () => {
    it("ETH/USD swap - validates output within slippage tolerance", async () => {
      const { roles, allowFunction, invoke } =
        await loadFixture(setupTwoParams);

      // ETH/USD: 1 ETH = 2000 USD
      const MockPricing = await ethers.getContractFactory("MockPricing");
      const ethUsdAdapter = await MockPricing.deploy(2000n * 10n ** 18n);

      // Swapped order: relative (USD output) plucked before reference (ETH input)
      const compValue = encodeWithinRatioCompValue({
        referenceAdapter: await ethUsdAdapter.getAddress(),
        relativeAdapter: ZeroAddress,
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
      await expect(
        invoke(20000n * 10n ** 18n, 10n * 10n ** 18n),
      ).to.not.be.revert(ethers);

      // Selling 10 ETH for 19,880 USD → 99.4% < 99.5%
      await expect(invoke(19880n * 10n ** 18n, 10n * 10n ** 18n))
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(
          ConditionViolationStatus.RatioBelowMin,
          2, // WithinRatio node
          anyValue,
        );

      // Selling 10 ETH for 20,120 USD → 100.6% > 100.5%
      await expect(invoke(20120n * 10n ** 18n, 10n * 10n ** 18n))
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(
          ConditionViolationStatus.RatioAboveMax,
          2, // WithinRatio node
          anyValue,
        );
    });

    it("WBTC/ETH swap - cross-asset with different decimals", async () => {
      const { roles, allowFunction, invoke } =
        await loadFixture(setupTwoParams);

      // Swapped: param0→relative (WBTC), param1→reference (ETH)
      // ETH/USD: 1 ETH = 2000 USD
      // BTC/USD: 1 BTC = 150,000 USD
      const MockPricing = await ethers.getContractFactory("MockPricing");
      const ethUsdAdapter = await MockPricing.deploy(2000n * 10n ** 18n);
      const btcUsdAdapter = await MockPricing.deploy(150000n * 10n ** 18n);

      const compValue = encodeWithinRatioCompValue({
        referenceAdapter: await ethUsdAdapter.getAddress(),
        relativeAdapter: await btcUsdAdapter.getAddress(),
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
      await expect(invoke(1n * 10n ** 8n, 75n * 10n ** 18n)).to.not.be.revert(
        ethers,
      );

      // Selling 75 ETH for 0.94 BTC → 94% < 95%
      await expect(invoke(94n * 10n ** 6n, 75n * 10n ** 18n))
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(
          ConditionViolationStatus.RatioBelowMin,
          2, // WithinRatio node
          anyValue,
        );

      // Selling 75 ETH for 1.06 BTC → 106% > 105%
      await expect(invoke(106n * 10n ** 6n, 75n * 10n ** 18n))
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(
          ConditionViolationStatus.RatioAboveMax,
          2, // WithinRatio node
          anyValue,
        );
    });

    it("USDC/exotic token swap - maximum decimal difference", async () => {
      const { roles, allowFunction, invoke } =
        await loadFixture(setupTwoParams);

      // ExoticToken/USDC: 1 ExoticToken = 2 USDC
      const MockPricing = await ethers.getContractFactory("MockPricing");
      const exoticUsdcAdapter = await MockPricing.deploy(2n * 10n ** 18n);

      // Swapped: param0→pluckedValues[61]=relative (ExoticToken), param1→pluckedValues[83]=reference (USDC)
      const compValue = encodeWithinRatioCompValue({
        referenceAdapter: ZeroAddress,
        relativeAdapter: await exoticUsdcAdapter.getAddress(),
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
      await expect(
        invoke(500n * 10n ** 27n, 1000n * 10n ** 6n),
      ).to.not.be.revert(ethers);

      // Selling 1000 USDC for 498.7 ExoticToken → 99.74% < 99.75%
      await expect(invoke(4987n * 10n ** 24n, 1000n * 10n ** 6n))
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(
          ConditionViolationStatus.RatioBelowMin,
          2, // WithinRatio node
          anyValue,
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
      await expect(invoke(1000n * 10n ** 18n, 249n * 10n ** 18n))
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(
          ConditionViolationStatus.RatioBelowMin,
          2, // WithinRatio node
          anyValue,
        );

      // 250 / 1000 = 25% → pass
      await expect(
        invoke(1000n * 10n ** 18n, 250n * 10n ** 18n),
      ).to.not.be.revert(ethers);

      // 300 / 1000 = 30% → pass
      await expect(
        invoke(1000n * 10n ** 18n, 300n * 10n ** 18n),
      ).to.not.be.revert(ethers);
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
      await expect(
        invoke(4900n * 10n ** 18n, 1000n * 10n ** 18n),
      ).to.not.be.revert(ethers);

      // 5000 / 1000 = 500% → pass (boundary)
      await expect(
        invoke(5000n * 10n ** 18n, 1000n * 10n ** 18n),
      ).to.not.be.revert(ethers);

      // 5001 / 1000 = 500.1% → fail
      await expect(invoke(5001n * 10n ** 18n, 1000n * 10n ** 18n))
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(
          ConditionViolationStatus.RatioAboveMax,
          2, // WithinRatio node
          anyValue,
        );
    });

    it("USD/WBTC swap - WBTC converts to USD base via relative adapter", async () => {
      const { roles, allowFunction, invoke } =
        await loadFixture(setupTwoParams);

      // WBTC/USD adapter: 1 WBTC = 150,000 USD
      const MockPricing = await ethers.getContractFactory("MockPricing");
      const wbtcUsdAdapter = await MockPricing.deploy(150000n * 10n ** 18n);

      const compValue = encodeWithinRatioCompValue({
        referenceAdapter: ZeroAddress, // USD stablecoin is the base (no conversion)
        relativeAdapter: await wbtcUsdAdapter.getAddress(),
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
      await expect(
        invoke(45000n * 10n ** 18n, 3n * 10n ** 7n),
      ).to.not.be.revert(ethers);

      // Relative: 0.297 WBTC → 44,550 / 45,000 = 99% → pass
      await expect(
        invoke(45000n * 10n ** 18n, 297n * 10n ** 5n),
      ).to.not.be.revert(ethers);

      // Relative: 0.2967 WBTC → 44,505 / 45,000 = 98.9% → fail
      await expect(invoke(45000n * 10n ** 18n, 2967n * 10n ** 4n))
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(
          ConditionViolationStatus.RatioBelowMin,
          2, // WithinRatio node
          anyValue,
        );
    });

    it("ETH/WBTC swap - converts to ETH base via relative adapter", async () => {
      const { roles, allowFunction, invoke } =
        await loadFixture(setupTwoParams);

      // Swapped: param0→relative (WBTC), param1→reference (ETH)
      // WBTC/ETH adapter: 1 WBTC = 75 ETH
      const MockPricing = await ethers.getContractFactory("MockPricing");
      const wbtcEthAdapter = await MockPricing.deploy(75n * 10n ** 18n);

      const compValue = encodeWithinRatioCompValue({
        referenceAdapter: ZeroAddress, // ETH is the base
        relativeAdapter: await wbtcEthAdapter.getAddress(),
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
      await expect(invoke(1n * 10n ** 8n, 75n * 10n ** 18n)).to.not.be.revert(
        ethers,
      );

      // Relative: 0.95 WBTC → 71.25 / 75 = 95% → pass
      await expect(invoke(95n * 10n ** 6n, 75n * 10n ** 18n)).to.not.be.revert(
        ethers,
      );

      // Relative: 0.949 WBTC → 71.175 / 75 = 94.9% → fail
      await expect(invoke(949n * 10n ** 5n, 75n * 10n ** 18n))
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(
          ConditionViolationStatus.RatioBelowMin,
          2, // WithinRatio node
          anyValue,
        );

      // Relative: 1.051 WBTC → 78.825 / 75 = 105.1% → fail
      await expect(invoke(1051n * 10n ** 5n, 75n * 10n ** 18n))
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(
          ConditionViolationStatus.RatioAboveMax,
          2, // WithinRatio node
          anyValue,
        );
    });
    it("handles WBTC (8 decimals) vs FunkyToken (27 decimals) both with adapters", async () => {
      const { roles, allowFunction, invoke } =
        await loadFixture(setupTwoParams);

      // Reference: WBTC (8 decimals), price = $100,000
      // Relative: FunkyToken (27 decimals), price = $2
      const MockPricing = await ethers.getContractFactory("MockPricing");
      const wbtcAdapter = await MockPricing.deploy(100000n * 10n ** 18n);
      const funkyAdapter = await MockPricing.deploy(2n * 10n ** 18n);

      const compValue = encodeWithinRatioCompValue({
        referenceAdapter: await wbtcAdapter.getAddress(),
        relativeAdapter: await funkyAdapter.getAddress(),
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
      await expect(
        invoke(1n * 10n ** 8n, 50000n * 10n ** 27n),
      ).to.not.be.revert(ethers);

      // Relative: 49,500 FunkyToken × $2 = $99,000 → 99%
      await expect(
        invoke(1n * 10n ** 8n, 49500n * 10n ** 27n),
      ).to.not.be.revert(ethers);

      // Relative: 49,400 FunkyToken × $2 = $98,800 → 98.8% < 99%
      await expect(invoke(1n * 10n ** 8n, 49400n * 10n ** 27n))
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(
          ConditionViolationStatus.RatioBelowMin,
          2, // WithinRatio node
          anyValue,
        );

      // Relative: 50,600 FunkyToken × $2 = $101,200 → 101.2% > 101%
      await expect(invoke(1n * 10n ** 8n, 50600n * 10n ** 27n))
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(
          ConditionViolationStatus.RatioAboveMax,
          2, // WithinRatio node
          anyValue,
        );
    });
  });

  describe("Parameter Extraction", () => {
    it("extracts values from AbiEncoded params", async () => {
      const iface = new Interface([
        "function mixedParams(uint256, bytes, uint256)",
      ]);
      const fn = iface.getFunction("mixedParams")!;
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
      await roles.allowFunctionPacked(
        roleKey,
        testContractAddress,
        fn.selector,
        packed,
        ExecutionOptions.None,
      );

      const invoke = (a: number, b: number) =>
        roles
          .connect(member)
          .execTransactionFromModule(
            testContractAddress,
            0,
            iface.encodeFunctionData(fn, [a, "0xaabbcc", b]),
            0,
          );

      // 1200 / 1000 = 120% → pass
      await expect(invoke(1000, 1200)).to.not.be.revert(ethers);

      // 1201 / 1000 = 120.1% > 120% → fail
      await expect(invoke(1000, 1201))
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(
          ConditionViolationStatus.RatioAboveMax,
          2, // WithinRatio node (And=0, Matches=1, WithinRatio=2)
          anyValue,
        );
    });

    it("extracts values from nested AbiEncoded", async () => {
      const iface = new Interface(["function dynamic(bytes)"]);
      const fn = iface.getFunction("dynamic")!;
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
      await roles.allowFunctionPacked(
        roleKey,
        testContractAddress,
        fn.selector,
        packed,
        ExecutionOptions.None,
      );

      const abiCoder = AbiCoder.defaultAbiCoder();

      const invoke = (encoded: string) =>
        roles
          .connect(member)
          .execTransactionFromModule(
            testContractAddress,
            0,
            iface.encodeFunctionData(fn, [encoded]),
            0,
          );

      // 800 / 1000 = 80% → pass
      const encoded = abiCoder.encode(
        ["uint256", "uint256", "uint256"],
        [1000, 500, 800],
      );
      await expect(invoke(encoded)).to.not.be.revert(ethers);

      // 801 / 1000 = 80.1% > 80% → fail
      const encodedFail = abiCoder.encode(
        ["uint256", "uint256", "uint256"],
        [1000, 500, 801],
      );
      await expect(invoke(encodedFail))
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(
          ConditionViolationStatus.RatioAboveMax,
          2, // WithinRatio node: And[0] -> Matches[1], WithinRatio[2]
          anyValue,
        );
    });

    it("extracts values from Tuple", async () => {
      const iface = new Interface([
        "function mixedTuple((uint256 amount, uint256 second, uint256 limit, uint256 fourth))",
      ]);
      const fn = iface.getFunction("mixedTuple")!;
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
      await roles.allowFunctionPacked(
        roleKey,
        testContractAddress,
        fn.selector,
        packed,
        ExecutionOptions.None,
      );

      const invoke = (
        amount: number,
        second: number,
        limit: number,
        fourth: number,
      ) =>
        roles
          .connect(member)
          .execTransactionFromModule(
            testContractAddress,
            0,
            iface.encodeFunctionData(fn, [[amount, second, limit, fourth]]),
            0,
          );

      // 1500 / 1000 = 150% → pass
      await expect(invoke(500, 1000, 800, 1500)).to.not.be.revert(ethers);

      // 1501 / 1000 = 150.1% > 150% → fail
      await expect(invoke(500, 1000, 800, 1501))
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(
          ConditionViolationStatus.RatioAboveMax,
          2, // WithinRatio node: And[0] -> Matches[1], WithinRatio[2]
          anyValue,
        );
    });

    it("WithinRatio inside And as tuple field - Tuple(Static, And(WithinRatio, Static))", async () => {
      const iface = new Interface([
        "function twoParams(uint256 reference, uint256 relative)",
      ]);
      const fn = iface.getFunction("twoParams")!;
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
      await roles.allowFunctionPacked(
        roleKey,
        testContractAddress,
        fn.selector,
        packed,
        ExecutionOptions.None,
      );

      const invoke = (reference: number, relative: number) =>
        roles
          .connect(member)
          .execTransactionFromModule(
            testContractAddress,
            0,
            iface.encodeFunctionData(fn, [reference, relative]),
            0,
          );

      // 1500 / 1000 = 150% → pass
      await expect(invoke(1000, 1500)).to.not.be.revert(ethers);

      // 1501 / 1000 = 150.1% > 150% → fail
      await expect(invoke(1000, 1501))
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(
          ConditionViolationStatus.RatioAboveMax,
          4, // WithinRatio: Matches[0] -> Pluck[1], And[2] -> Pluck[3], WithinRatio[4]
          anyValue,
        );
    });

    it("extracts values from Array", async () => {
      const iface = new Interface(["function uint256ArrayStatic(uint256[])"]);
      const fn = iface.getFunction("uint256ArrayStatic")!;
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
      await roles.allowFunctionPacked(
        roleKey,
        testContractAddress,
        fn.selector,
        packed,
        ExecutionOptions.None,
      );

      const invoke = (arr: number[]) =>
        roles
          .connect(member)
          .execTransactionFromModule(
            testContractAddress,
            0,
            iface.encodeFunctionData(fn, [arr]),
            0,
          );

      // 1200 / 1000 = 120% → pass
      await expect(invoke([1000, 500, 1200])).to.not.be.revert(ethers);

      // 1201 / 1000 = 120.1% > 120% → fail
      await expect(invoke([1000, 500, 1201]))
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(
          ConditionViolationStatus.RatioAboveMax,
          2, // WithinRatio node: And[0] -> Matches[1], WithinRatio[2]
          anyValue,
        );
    });

    it("extracts sliced values from bytes parameter", async () => {
      const iface = new Interface(["function dynamicParam(bytes)"]);
      const fn = iface.getFunction("dynamicParam")!;
      const { roles, member, testContractAddress, roleKey } =
        await loadFixture(setupTestContract);

      // Slice compValue: 2 bytes shift + 1 byte size
      const sliceCompValue = (shift: number, size: number) =>
        solidityPacked(["uint16", "uint8"], [shift, size]);

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
      await roles.allowFunctionPacked(
        roleKey,
        testContractAddress,
        fn.selector,
        packed,
        ExecutionOptions.None,
      );

      const invoke = (bytesData: string) =>
        roles
          .connect(member)
          .execTransactionFromModule(
            testContractAddress,
            0,
            iface.encodeFunctionData(fn, [bytesData]),
            0,
          );

      // bytes: [reference: 4 bytes][relative: 4 bytes]
      // reference = 0x000003e8 (1000), relative = 0x000003e8 (1000) → 100%
      await expect(invoke("0x000003e8000003e8")).to.not.be.revert(ethers);

      // reference = 0x000003e8 (1000), relative = 0x00000384 (900) → 90%
      await expect(invoke("0x000003e800000384")).to.not.be.revert(ethers);

      // reference = 0x000003e8 (1000), relative = 0x00000379 (889) → 88.9% < 90%
      await expect(invoke("0x000003e800000379"))
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(ConditionViolationStatus.RatioBelowMin, anyValue, anyValue);

      // reference = 0x000003e8 (1000), relative = 0x00000451 (1105) → 110.5% > 110%
      await expect(invoke("0x000003e800000451"))
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(ConditionViolationStatus.RatioAboveMax, anyValue, anyValue);
    });

    it("extracts EtherValue", async () => {
      // Different pattern - uses single param + ether value, keep inline
      const iface = new Interface(["function fn(uint256)"]);
      const fn = iface.getFunction("fn")!;
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
      await roles.allowFunctionPacked(
        roleKey,
        testContractAddress,
        fn.selector,
        packed,
        ExecutionOptions.Send,
      );

      // 2 ETH / 1 ETH = 200% → pass
      await expect(
        roles
          .connect(member)
          .execTransactionFromModule(
            testContractAddress,
            10n ** 18n,
            iface.encodeFunctionData(fn, [2n * 10n ** 18n]),
            0,
          ),
      ).to.not.be.revert(ethers);

      // 1 ETH / 1 ETH = 100% → pass
      await expect(
        roles
          .connect(member)
          .execTransactionFromModule(
            testContractAddress,
            10n ** 18n,
            iface.encodeFunctionData(fn, [1n * 10n ** 18n]),
            0,
          ),
      ).to.not.be.revert(ethers);

      // 2.1 ETH / 1 ETH = 210% > 200% → fail
      await expect(
        roles
          .connect(member)
          .execTransactionFromModule(
            testContractAddress,
            10n ** 18n,
            iface.encodeFunctionData(fn, [21n * 10n ** 17n]),
            0,
          ),
      )
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(
          ConditionViolationStatus.RatioAboveMax,
          3, // WithinRatio node: And[0] -> Matches[1], Pluck[2], WithinRatio[3]
          anyValue,
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
      await expect(invoke(850, 1000))
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(
          ConditionViolationStatus.RatioBelowMin,
          2, // WithinRatio node at BFS index 3
          anyValue,
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
      await expect(invoke(950, 1000))
        .to.be.revertedWithCustomError(roles, "ConditionViolation")
        .withArgs(
          ConditionViolationStatus.RatioAboveMax,
          anyValue,
          0, // calldataOffset: WithinRatio uses plucked values, no direct payload
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
  referenceAdapter?: string;
  relativeAdapter?: string;
  referencePluckIndex: number;
  referenceDecimals: number;
  relativePluckIndex: number;
  relativeDecimals: number;
  minRatio: number;
  maxRatio: number;
  referenceParams?: string;
  relativeParams?: string;
}): string {
  const base = solidityPacked(
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
    result = solidityPacked(
      ["bytes", "uint8", "address", "bytes"],
      [result, 20 + refParamsLen, referenceAdapter, refParamsBytes],
    );
  } else {
    // blobLen=0: no ref adapter
    result = solidityPacked(["bytes", "uint8"], [result, 0]);
  }

  if (relativeAdapter) {
    const relParamsBytes = relativeParams || "0x";
    const relParamsLen = (relParamsBytes.length - 2) / 2;
    // rel blob: blobLen(1) + address(20) + params(blobLen - 20)
    result = solidityPacked(
      ["bytes", "uint8", "address", "bytes"],
      [result, 20 + relParamsLen, relativeAdapter, relParamsBytes],
    );
  }

  return result;
}

describe("integrity", () => {
  after(async () => {
    await connection.close();
  });

  it("reverts UnsuitableParameterType for invalid encodings", async () => {
    const { roles } = await loadFixture(setupTestContract);

    const compValue = encodeWithinRatioCompValue({
      referencePluckIndex: 0,
      referenceDecimals: 0,
      relativePluckIndex: 1,
      relativeDecimals: 0,
      minRatio: 9000,
      maxRatio: 11000,
    });

    for (const encoding of [
      Encoding.AbiEncoded,
      Encoding.Array,
      Encoding.Dynamic,
      Encoding.EtherValue,
      Encoding.Static,
      Encoding.Tuple,
    ]) {
      await expect(
        packConditions(roles, [
          {
            parent: 0,
            paramType: encoding,
            operator: Operator.WithinRatio,
            compValue,
          },
        ]),
      ).to.be.revertedWithCustomError(roles, "UnsuitableParameterType");
    }
  });

  describe("compValue", () => {
    it("accepts 12-byte compValue (no adapters)", async () => {
      const { roles } = await loadFixture(setupTestContract);

      // 12 bytes: referencePluckIndex(1) + referenceDecimals(1) + relativePluckIndex(1) + relativeDecimals(1) + minRatio(4) + maxRatio(4)
      const compValue12 = solidityPacked(
        ["uint8", "uint8", "uint8", "uint8", "uint32", "uint32"],
        [0, 0, 1, 0, 9000, 11000],
      );

      // Should succeed without reverting
      await roles.packConditions([
        {
          parent: 0,
          paramType: Encoding.None,
          operator: Operator.And,
          compValue: "0x",
        },
        {
          parent: 0,
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          compValue: "0x",
        },
        {
          parent: 0,
          paramType: Encoding.None,
          operator: Operator.WithinRatio,
          compValue: compValue12,
        },
        {
          parent: 1,
          paramType: Encoding.Static,
          operator: Operator.Pluck,
          compValue: "0x00",
        },
        {
          parent: 1,
          paramType: Encoding.Static,
          operator: Operator.Pluck,
          compValue: "0x01",
        },
      ]);
    });

    it("accepts 33-byte compValue (one adapter, no params)", async () => {
      const { roles } = await loadFixture(setupTestContract);

      // 33 bytes: 12 base + refLen(1) + refAdapter(20)
      const compValue33 = solidityPacked(
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
        [0, 0, 1, 0, 9000, 11000, 20, ZeroAddress],
      );

      // Should succeed without reverting
      await roles.packConditions([
        {
          parent: 0,
          paramType: Encoding.None,
          operator: Operator.And,
          compValue: "0x",
        },
        {
          parent: 0,
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          compValue: "0x",
        },
        {
          parent: 0,
          paramType: Encoding.None,
          operator: Operator.WithinRatio,
          compValue: compValue33,
        },
        {
          parent: 1,
          paramType: Encoding.Static,
          operator: Operator.Pluck,
          compValue: "0x00",
        },
        {
          parent: 1,
          paramType: Encoding.Static,
          operator: Operator.Pluck,
          compValue: "0x01",
        },
      ]);
    });

    it("accepts 54-byte compValue (two adapters, no params)", async () => {
      const { roles } = await loadFixture(setupTestContract);

      // 54 bytes: 12 base + refLen(1) + refAdapter(20) + relLen(1) + relAdapter(20)
      const compValue54 = solidityPacked(
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
        [0, 0, 1, 0, 9000, 11000, 20, ZeroAddress, 20, ZeroAddress],
      );

      // Should succeed without reverting
      await roles.packConditions([
        {
          parent: 0,
          paramType: Encoding.None,
          operator: Operator.And,
          compValue: "0x",
        },
        {
          parent: 0,
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          compValue: "0x",
        },
        {
          parent: 0,
          paramType: Encoding.None,
          operator: Operator.WithinRatio,
          compValue: compValue54,
        },
        {
          parent: 1,
          paramType: Encoding.Static,
          operator: Operator.Pluck,
          compValue: "0x00",
        },
        {
          parent: 1,
          paramType: Encoding.Static,
          operator: Operator.Pluck,
          compValue: "0x01",
        },
      ]);
    });

    it("reverts UnsuitableCompValue when compValue is less than 12 bytes", async () => {
      const { roles } = await loadFixture(setupTestContract);

      await expect(
        packConditions(roles, [
          {
            parent: 0,
            paramType: Encoding.None,
            operator: Operator.WithinRatio,
            compValue: "0x" + "ab".repeat(11), // 11 bytes
          },
        ]),
      ).to.be.revertedWithCustomError(roles, "UnsuitableCompValue");
    });

    it("reverts UnsuitableCompValue when compValue is between 12 and 33 bytes", async () => {
      const { roles } = await loadFixture(setupTestContract);

      await expect(
        packConditions(roles, [
          {
            parent: 0,
            paramType: Encoding.None,
            operator: Operator.WithinRatio,
            compValue: "0x" + "ab".repeat(20), // 20 bytes - invalid
          },
        ]),
      ).to.be.revertedWithCustomError(roles, "UnsuitableCompValue");
    });

    it("reverts AllowanceDecimalsExceedMax when referenceDecimals exceeds 27", async () => {
      const { roles } = await loadFixture(setupTestContract);
      const compValue = encodeWithinRatioCompValue({
        referencePluckIndex: 0,
        referenceDecimals: 28,
        relativePluckIndex: 1,
        relativeDecimals: 18,
        minRatio: 9000,
        maxRatio: 11000,
      });

      await expect(
        packConditions(roles, [
          {
            parent: 0,
            paramType: Encoding.None,
            operator: Operator.WithinRatio,
            compValue,
          },
        ]),
      )
        .to.be.revertedWithCustomError(roles, "AllowanceDecimalsExceedMax")
        .withArgs(0);
    });

    it("reverts AllowanceDecimalsExceedMax when relativeDecimals exceeds 27", async () => {
      const { roles } = await loadFixture(setupTestContract);
      const compValue = encodeWithinRatioCompValue({
        referencePluckIndex: 0,
        referenceDecimals: 18,
        relativePluckIndex: 1,
        relativeDecimals: 28,
        minRatio: 9000,
        maxRatio: 11000,
      });

      await expect(
        packConditions(roles, [
          {
            parent: 0,
            paramType: Encoding.None,
            operator: Operator.WithinRatio,
            compValue,
          },
        ]),
      )
        .to.be.revertedWithCustomError(roles, "AllowanceDecimalsExceedMax")
        .withArgs(0);
    });

    it("accepts compValue with adapter params", async () => {
      const { roles } = await loadFixture(setupTestContract);

      // 12 base + refBlobLen(1) + refAdapter(20) + refParams(2)
      //        + relBlobLen(1) + relAdapter(20) + relParams(2) = 58
      const compValue = solidityPacked(
        [
          "uint8",
          "uint8",
          "uint8",
          "uint8",
          "uint32",
          "uint32",
          "uint8",
          "address",
          "bytes",
          "uint8",
          "address",
          "bytes",
        ],
        [
          0,
          0,
          1,
          0,
          9000,
          11000,
          22, // blobLen = 20 (address) + 2 (params)
          "0x0000000000000000000000000000000000000001",
          "0xaabb",
          22, // blobLen = 20 (address) + 2 (params)
          "0x0000000000000000000000000000000000000002",
          "0xccdd",
        ],
      );

      // Should succeed without reverting
      await roles.packConditions([
        {
          parent: 0,
          paramType: Encoding.None,
          operator: Operator.And,
          compValue: "0x",
        },
        {
          parent: 0,
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          compValue: "0x",
        },
        {
          parent: 0,
          paramType: Encoding.None,
          operator: Operator.WithinRatio,
          compValue,
        },
        {
          parent: 1,
          paramType: Encoding.Static,
          operator: Operator.Pluck,
          compValue: "0x00",
        },
        {
          parent: 1,
          paramType: Encoding.Static,
          operator: Operator.Pluck,
          compValue: "0x01",
        },
      ]);
    });

    it("reverts WithinRatioNoRatioProvided when both minRatio and maxRatio are zero", async () => {
      const { roles } = await loadFixture(setupTestContract);

      const compValue = encodeWithinRatioCompValue({
        referencePluckIndex: 3,
        referenceDecimals: 0,
        relativePluckIndex: 7,
        relativeDecimals: 0,
        minRatio: 0,
        maxRatio: 0, // Both zero is invalid
      });

      await expect(
        packConditions(roles, [
          {
            parent: 0,
            paramType: Encoding.None,
            operator: Operator.And,
            compValue: "0x",
          },
          {
            parent: 0,
            paramType: Encoding.AbiEncoded,
            operator: Operator.Matches,
            compValue: "0x",
          },
          {
            parent: 0,
            paramType: Encoding.None,
            operator: Operator.WithinRatio,
            compValue,
          },
          {
            parent: 1,
            paramType: Encoding.Static,
            operator: Operator.Pluck,
            compValue: "0x03",
          },
          {
            parent: 1,
            paramType: Encoding.Static,
            operator: Operator.Pluck,
            compValue: "0x07",
          },
        ]),
      ).to.be.revertedWithCustomError(roles, "WithinRatioNoRatioProvided");
    });

    it("reverts WithinRatioMinExceedsMax when minRatio is greater than maxRatio", async () => {
      const { roles } = await loadFixture(setupTestContract);

      const compValue = encodeWithinRatioCompValue({
        referencePluckIndex: 3,
        referenceDecimals: 0,
        relativePluckIndex: 7,
        relativeDecimals: 0,
        minRatio: 11000,
        maxRatio: 9000, // min > max is invalid
      });

      await expect(
        packConditions(roles, [
          {
            parent: 0,
            paramType: Encoding.None,
            operator: Operator.And,
            compValue: "0x",
          },
          {
            parent: 0,
            paramType: Encoding.AbiEncoded,
            operator: Operator.Matches,
            compValue: "0x",
          },
          {
            parent: 0,
            paramType: Encoding.None,
            operator: Operator.WithinRatio,
            compValue,
          },
          {
            parent: 1,
            paramType: Encoding.Static,
            operator: Operator.Pluck,
            compValue: "0x03",
          },
          {
            parent: 1,
            paramType: Encoding.Static,
            operator: Operator.Pluck,
            compValue: "0x07",
          },
        ]),
      ).to.be.revertedWithCustomError(roles, "WithinRatioMinExceedsMax");
    });
  });

  it("reverts LeafNodeCannotHaveChildren when WithinRatio has children", async () => {
    const { roles } = await loadFixture(setupTestContract);

    const compValue = encodeWithinRatioCompValue({
      referencePluckIndex: 3,
      referenceDecimals: 0,
      relativePluckIndex: 7,
      relativeDecimals: 0,
      minRatio: 9000,
      maxRatio: 11000,
    });

    await expect(
      packConditions(roles, [
        {
          parent: 0,
          paramType: Encoding.AbiEncoded,
          operator: Operator.Matches,
          compValue: "0x",
        },
        {
          parent: 0,
          paramType: Encoding.Static,
          operator: Operator.Pluck,
          compValue: "0x03",
        },
        {
          parent: 0,
          paramType: Encoding.Static,
          operator: Operator.Pluck,
          compValue: "0x07",
        },
        {
          parent: 0,
          paramType: Encoding.None,
          operator: Operator.WithinRatio,
          compValue,
        },
        {
          parent: 3,
          paramType: Encoding.Static,
          operator: Operator.Pass,
          compValue: "0x",
        },
      ]),
    ).to.be.revertedWithCustomError(roles, "LeafNodeCannotHaveChildren");
  });
});
