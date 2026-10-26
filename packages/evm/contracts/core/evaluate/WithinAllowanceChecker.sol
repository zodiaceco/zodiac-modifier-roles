// SPDX-License-Identifier: BUSL-1.1
// Copyright (c) 2026 Zodiac Labs GmbH
// Zodiac Roles Modifier v3
// Converts to LGPL-3.0-or-later on 2030-03-01
pragma solidity >=0.8.17 <0.9.0;

import "../../common/AllowanceConsumer.sol";
import "../../common/PriceLoader.sol";
import "../../types/Types.sol";

/**
 * @title WithinAllowanceChecker
 * @notice Validates allowance consumption with optional amount conversion.
 *
 * @dev Checks if a value is within an allowance and consumes it. The input
 *      is converted to balance units (dust rounded up), then consumed via
 *      AllowanceConsumer.
 *
 *      The `consumptions` array is treated as immutable. If consumption occurs,
 *      a new array is allocated and returned (Copy-on-Write).
 *
 * @author gnosisguild
 */
library WithinAllowanceChecker {
    /**
     * CompValue Layout (32, 34, 54, or 54+ bytes):
     * ┌─────────────────────────┬──────────┬──────────┬─────────────────────┬─────────────────────┐
     * │      allowanceKey       │ balance  │  input   │       adapter       │    adapterParams    │
     * │        (bytes32)        │ decimals │ decimals │      (address)      │       (bytes)       │
     * ├─────────────────────────┼──────────┼──────────┼─────────────────────┼─────────────────────┤
     * │         0 - 31          │    32    │    33    │       34 - 53       │        54+          │
     * └─────────────────────────┴──────────┴──────────┴─────────────────────┴─────────────────────┘
     *                           └── optional ─────────┴───── optional ──────┴──── optional ───────┘
     *
     * balanceDecimals: decimals used to track the allowance balance
     * inputDecimals: decimals of the value being checked
     * adapterParams: optional trailing bytes passed to IPricing.getPrice(params)
     */
    function check(
        Consumption[] memory consumptions,
        uint256 value,
        bytes memory compValue
    ) internal view returns (Status status, Consumption[] memory) {
        // 1. Convert the input value to balance units
        (status, value) = _scaleInput(value, compValue);
        if (status != Status.Ok) {
            return (status, consumptions);
        }

        // 2. Consume it from the allowance
        return
            AllowanceConsumer.consume(consumptions, bytes32(compValue), value);
    }

    /**
     * @dev Converts an input value to balance-denominated units: scales up
     *      to the highest decimal precision, applies the price, then scales
     *      back down in a single division that rounds dust up.
     *
     *      Consuming the rounded amount is equivalent to comparing at full
     *      precision: ⌈v/f⌉ > b − c  ⟺  v > (b − c)·f
     */
    function _scaleInput(
        uint256 value,
        bytes memory compValue
    ) private view returns (Status status, uint256) {
        // A 32-byte compValue contains only the allowance key, so the input is
        // already denominated in balance units and needs no conversion.
        if (compValue.length == 32) {
            return (Status.Ok, value);
        }

        (
            uint256 balanceDecimals,
            uint256 inputDecimals,
            uint256 precision
        ) = _unpack(compValue);

        address adapter;
        if (compValue.length > 34) {
            assembly {
                adapter := shr(96, mload(add(compValue, 0x42)))
            }
        }

        bytes memory params;
        if (compValue.length > 54) {
            uint256 length = compValue.length - 54;
            params = new bytes(length);
            assembly {
                // 0x56 = 0x20 (memory length prefix) + 0x36 (byte 54)
                mcopy(add(params, 0x20), add(compValue, 0x56), length)
            }
        }

        uint256 price;
        (status, price) = PriceLoader.load(adapter, params);
        if (status != Status.Ok) {
            return (status, 0);
        }

        return (
            Status.Ok,
            _ceilDiv(
                value * (10 ** (precision - inputDecimals)) * price,
                (10 ** (precision - balanceDecimals)) * 1e18
            )
        );
    }

    function _unpack(
        bytes memory compValue
    )
        private
        pure
        returns (
            uint256 balanceDecimals,
            uint256 inputDecimals,
            uint256 precision
        )
    {
        balanceDecimals = uint8(compValue[32]);
        inputDecimals = uint8(compValue[33]);
        precision = balanceDecimals > inputDecimals
            ? balanceDecimals
            : inputDecimals;
    }

    /// @dev Ceiling division. Returns 0 for 0, otherwise ⌈a / b⌉.
    function _ceilDiv(uint256 a, uint256 b) private pure returns (uint256) {
        if (a == 0) return 0;
        return (a - 1) / b + 1;
    }
}
