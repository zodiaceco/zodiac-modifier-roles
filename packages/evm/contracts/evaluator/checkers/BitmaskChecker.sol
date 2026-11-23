// SPDX-License-Identifier: BUSL-1.1
// Copyright (c) 2026 Zodiac Labs GmbH
// Zodiac Roles Modifier v3
// Converts to LGPL-3.0-or-later on 2030-03-01
pragma solidity >=0.8.17 <0.9.0;

import {Status} from "../types/EvaluatorTypes.sol";

/**
 * @title BitmaskChecker
 * @notice Validates that selected bits of an operand match an expected pattern.
 *
 * @dev compValue layout (total length = 2 + 2 * N bytes, N >= 1):
 *
 *      ┌────────────────────┬────────────────────┬────────────────────┐
 *      │ shift (16 bits)    │ mask (8N bits)     │ expected (8N bits) │
 *      └────────────────────┴────────────────────┴────────────────────┘
 *
 *      Fields:
 *        - shift     uint16, byte offset into the operand at which the mask
 *                    window starts.
 *        - mask      N bytes; selects which bits of the operand are checked.
 *        - expected  N bytes; the required value of the selected bits.
 *
 *      The operand is the bytes the check applies to, and nothing else: a
 *      Static value (or the window a Slice narrows it to), or the content of
 *      a Dynamic value, without its length word or padding. The caller has
 *      found it within calldata.
 *
 *      Bounds: the window, `shift + N`, must not exceed the operand. It is
 *      processed in 32-byte chunks; the trailing chunk is rinsed so the bytes
 *      past the window cannot contribute to the comparison.
 *
 * @author gnosisguild
 */
library BitmaskChecker {
    function check(
        bytes calldata operand,
        bytes memory compValue
    ) internal pure returns (Status) {
        uint256 shift = uint16(bytes2(compValue));
        uint256 n = (compValue.length - 2) / 2;

        // the mask window must fit within the operand
        if (shift + n > operand.length) {
            return Status.BitmaskOverflow;
        }

        /*
         * Load actual, expected, and mask in 32-byte chunks. Final chunk
         * gets rinsed if less than 32 bytes remain.
         */
        for (uint256 i; i < n; i += 32) {
            /*
             * compValue memory layout:
             * | 32: length | 2: shift | N: mask | N: expected |
             *                         ^--- 0x22 offset
             */
            bytes32 mask;
            assembly {
                mask := mload(add(add(compValue, 0x22), i))
            }

            bytes32 expected;
            assembly {
                expected := mload(add(add(compValue, 0x22), add(n, i)))
            }

            bytes32 actual;
            assembly {
                actual := calldataload(add(operand.offset, add(shift, i)))
            }

            bytes32 rinseMask = _rinseMask(n - i);

            if (expected & rinseMask != actual & mask & rinseMask) {
                return Status.BitmaskNotAllowed;
            }
        }

        return Status.Ok;
    }

    /// @dev Returns a mask with leading 1s for byteCount bytes, rest 0s.
    function _rinseMask(uint256 bytesLeft) private pure returns (bytes32) {
        uint256 bitsToRinse = (bytesLeft > 31 ? 0 : 32 - bytesLeft) * 8;
        return bytes32(type(uint256).max << bitsToRinse);
    }
}
