// SPDX-License-Identifier: BUSL-1.1
// Copyright (c) 2026 Zodiac Labs GmbH
// Zodiac Roles Modifier v3
// Converts to LGPL-3.0-or-later on 2030-03-01
pragma solidity >=0.8.17 <0.9.0;

import {Status} from "../../types/Types.sol";

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
 *      Operand framing (passed via `inlined` and `size`):
 *        - inlined == true   Operand is a Static value (`size` bytes at
 *                            location; normally 32, or 1-32 after Slice)
 *        - inlined == false  Operand is a Dynamic value; `location` points at
 *                            the length-prefix word, content begins at
 *                            `location + 32` and `shift` indexes into content
 *                            (the prefix is not part of the addressable range)
 *
 *      Bounds: `shift + N` must not exceed the operand's actual byte length
 *      (`size` for Static, the value of the length prefix for Dynamic). The
 *      window is processed in 32-byte chunks; the trailing chunk is rinsed
 *      so unused tail bits cannot contribute to the comparison.
 *
 * @author gnosisguild
 */
library BitmaskChecker {
    function check(
        bytes calldata data,
        uint256 location,
        bytes memory compValue,
        bool inlined,
        uint256 size
    ) internal pure returns (Status) {
        uint256 shift = uint16(bytes2(compValue));
        uint256 n = (compValue.length - 2) / 2;

        /*
         * Resolve the operand's encoded byte length so the compare cannot
         * bleed into trailing zero padding (or, for Dynamic operands sitting
         * mid-buffer, into the next ABI field).
         *   - Static (inlined): `size` bytes inline at `location`. We rely on
         *     the passed `size` because a static node may itself be sliced.
         *   - Dynamic: length prefix at `location`, content at `location + 32`.
         */
        uint256 start = location;
        uint256 encodedLength = size;
        if (inlined == false) {
            if (start + 32 > data.length) {
                return Status.BitmaskOverflow;
            }

            assembly {
                encodedLength := calldataload(add(data.offset, start))
            }

            start += 32;
        }

        // mask window must fit within the declared value length
        if (shift + n > encodedLength) {
            return Status.BitmaskOverflow;
        }

        // declared value length must be physically present in calldata
        if (start + encodedLength > data.length) {
            return Status.CalldataOverflow;
        }

        bytes calldata value = data[start:];

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
                actual := calldataload(add(value.offset, add(shift, i)))
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
