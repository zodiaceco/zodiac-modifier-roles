// SPDX-License-Identifier: BUSL-1.1
// Copyright (c) 2026 Zodiac Labs GmbH
// Zodiac Roles Modifier v3
// Converts to LGPL-3.0-or-later on 2030-03-01
pragma solidity >=0.8.17 <0.9.0;

import "../../common/PriceLoader.sol";
import "../../types/Types.sol";

/**
 * @title WithinRatioChecker
 * @notice Validates that a relative amount falls within a ratio range of a
 *         reference amount, with optional price adapter conversion.
 *
 * @dev Bounds are in basis points (10000 = 100%). Both amounts are read from
 *      pluckedValues by index, scaled to shared precision, optionally priced
 *      via adapters, then checked against [minRatio, maxRatio] using exact
 *      cross-multiplied comparisons (no rounding; overflow reverts).
 *
 * @author gnosisguild
 */
library WithinRatioChecker {
    /**
     * @dev Configuration decoded from compValue bytes.
     *
     * Base layout (12 bytes, always present):
     * ┌───────────────────┬───────────────────┬───────────────────┬───────────────────┬────────────┬────────────┐
     * │ referencePluckIdx │ referenceDecimals │ relativePluckIdx  │ relativeDecimals  │  minRatio  │  maxRatio  │
     * │      (uint8)      │      (uint8)      │      (uint8)      │      (uint8)      │  (uint32)  │  (uint32)  │
     * ├───────────────────┼───────────────────┼───────────────────┼───────────────────┼────────────┼────────────┤
     * │         0         │         1         │         2         │         3         │    4–7     │    8–11    │
     * └───────────────────┴───────────────────┴───────────────────┴───────────────────┴────────────┴────────────┘
     *
     * Optionally followed by a ref adapter blob, then a rel adapter blob.
     
     * Adapter blob structure:
     * ┌──────────┬─────────────┬──────────────────────┐
     * │ blobLen  │   adapter   │       params         │
     * │ (uint8)  │  (address)  │ (blobLen - 20) bytes │
     * └──────────┴─────────────┴──────────────────────┘
     *
     * blobLen is the length of the blob excluding the prefix byte itself (0 or >= 20).
     * A blobLen of 0 means no adapter.
     * To include a rel blob without a ref adapter, set ref blobLen to 0.
     * Valid sizes: 12, 13 + refBlobLen, 14 + refBlobLen + relBlobLen
     */
    struct CompValue {
        uint8 referencePluckIndex;
        uint8 referenceDecimals;
        uint8 relativePluckIndex;
        uint8 relativeDecimals;
        uint32 minRatio;
        uint32 maxRatio;
        address referenceAdapter;
        address relativeAdapter;
        bytes referenceParams;
        bytes relativeParams;
    }

    uint256 private constant BPS = 10000;

    /**
     * @notice Checks if ratio of relative to reference amount is within bounds.
     * @param compValue Packed configuration bytes
     * @param pluckedValues Array of values extracted from calldata
     * @return Status Ok if within bounds, error status otherwise
     */
    function check(
        bytes calldata compValue,
        bytes32[] calldata pluckedValues
    ) external view returns (Status) {
        CompValue memory config = _unpack(compValue);
        (
            Status status,
            uint256 referenceAmountUp,
            uint256 relativeAmountUp
        ) = _convert(config, pluckedValues);
        if (status != Status.Ok) {
            return status;
        }

        /*
         * The naive formula looks like:
         *
         *                 relativeAmountUp
         *   ratio (bps) = ───────────────── × 10,000   within [minRatio, maxRatio]
         *                 referenceAmountUp
         *
         * It is equivalent to the following, which does no truncation:
         *
         *   below min ⇔ relativeAmountUp × 10,000 < referenceAmountUp × minRatio
         *   above max ⇔ relativeAmountUp × 10,000 > referenceAmountUp × maxRatio
         *
         * A zero reference needs no special case: nothing is below min, and
         * any nonzero relative amount exceeds a configured max. Checked
         * arithmetic reverts if a multiplication overflows.
         */
        if (
            config.minRatio != 0 &&
            relativeAmountUp * BPS < referenceAmountUp * config.minRatio
        ) {
            return Status.RatioBelowMin;
        }
        if (
            config.maxRatio != 0 &&
            relativeAmountUp * BPS > referenceAmountUp * config.maxRatio
        ) {
            return Status.RatioAboveMax;
        }

        return Status.Ok;
    }

    /**
     * @dev Extracts and converts reference and relative amounts for ratio comparison.
     *
     *      1. Reads raw values from pluckedValues by index
     *      2. Scales both to the higher decimal precision
     *      3. Applies price adapters (if configured)
     *
     * @return status Ok, or the adapter failure status
     * @return referenceAmount Reference amount, scaled up to common precision
     * @return relativeAmount Relative amount, scaled up to common precision
     */
    function _convert(
        CompValue memory config,
        bytes32[] calldata pluckedValues
    )
        private
        view
        returns (Status status, uint256 referenceAmount, uint256 relativeAmount)
    {
        uint256 precision = config.referenceDecimals > config.relativeDecimals
            ? config.referenceDecimals
            : config.relativeDecimals;

        (status, referenceAmount) = _scaleAndPrice(
            uint256(pluckedValues[config.referencePluckIndex]),
            config.referenceDecimals,
            precision,
            config.referenceAdapter,
            config.referenceParams
        );
        if (status != Status.Ok) return (status, 0, 0);

        (status, relativeAmount) = _scaleAndPrice(
            uint256(pluckedValues[config.relativePluckIndex]),
            config.relativeDecimals,
            precision,
            config.relativeAdapter,
            config.relativeParams
        );
        if (status != Status.Ok) return (status, 0, 0);
    }

    /// @dev Returns the scaled value multiplied by the adapter price. The
    ///      price's 10^18 factor is never divided out — it carries on both
    ///      sides and cancels in the ratio comparison.
    function _scaleAndPrice(
        uint256 value,
        uint256 decimals,
        uint256 precision,
        address adapter,
        bytes memory params
    ) private view returns (Status status, uint256 price) {
        (status, price) = PriceLoader.load(adapter, params);
        if (status != Status.Ok) {
            return (status, 0);
        }

        return (Status.Ok, value * (10 ** (precision - decimals)) * price);
    }

    function _unpack(
        bytes calldata compValue
    ) private pure returns (CompValue memory config) {
        bytes32 packed = bytes32(compValue);

        config.referencePluckIndex = uint8(bytes1(packed));
        config.referenceDecimals = uint8(bytes1(packed << 8));
        config.relativePluckIndex = uint8(bytes1(packed << 16));
        config.relativeDecimals = uint8(bytes1(packed << 24));
        config.minRatio = uint32(bytes4(packed << 32));
        config.maxRatio = uint32(bytes4(packed << 64));

        uint256 offset = 12;
        (
            config.referenceAdapter,
            config.referenceParams,
            offset
        ) = _unpackAdapterBlob(compValue, offset);

        (config.relativeAdapter, config.relativeParams, ) = _unpackAdapterBlob(
            compValue,
            offset
        );
    }

    /// @dev Reads an adapter blob at the given offset: blobLen(1) + adapter(20) + params(blobLen - 20).
    ///      blobLen is the total blob length excluding the prefix byte itself.
    ///      Returns the adapter address, params bytes, and the offset after the blob.
    function _unpackAdapterBlob(
        bytes memory buffer,
        uint256 offset
    ) private pure returns (address adapter, bytes memory params, uint256) {
        uint256 blobLen;
        if (offset < buffer.length) {
            blobLen = uint8(buffer[offset]);
            offset += 1;
        }

        if (blobLen >= 20) {
            assembly {
                // 0x20 skips the memory length prefix
                adapter := shr(96, mload(add(add(buffer, 0x20), offset)))
            }
            offset += 20;
        }

        if (blobLen > 20) {
            uint256 length = blobLen - 20;
            params = new bytes(length);
            assembly {
                mcopy(add(params, 0x20), add(add(buffer, 0x20), offset), length)
            }
            offset += length;
        }

        return (adapter, params, offset);
    }
}
