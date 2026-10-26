// SPDX-License-Identifier: BUSL-1.1
// Copyright (c) 2026 Zodiac Labs GmbH
// Zodiac Roles Modifier v3
// Converts to LGPL-3.0-or-later on 2030-03-01
pragma solidity >=0.8.17 <0.9.0;

import {AVATAR_SLOT} from "../StorageSlots.sol";

import "../../types/Types.sol";

/**
 * @title  ConditionUnpacker
 * @notice A library that provides unpacking functions for reconstructing the
 *         Condition tree from a memory-optimized buffer.
 *
 * @dev    This is performance-critical code. Every transaction execution
 *         begins by loading packed conditions from contract storage
 *         (via extcodecopy) and performing tree unpacking. The implementation
 *         is deliberately low-level to minimize execution overhead.
 *
 * @author gnosisguild
 */
library ConditionUnpacker {
    uint256 private constant HEADER_BYTES = 3;
    uint256 private constant NODE_BYTES = 4;

    function unpack(
        bytes memory buffer
    )
        internal
        view
        returns (Condition memory condition, uint256 maxPluckValue)
    {
        /*
         * ┌───────────────────────────────────────────────────────────────┐
         * │ header 24 bits, 3 bytes:                                      │
         * │   • conditionNodeCount    16 bits  [23-8]                     │
         * │   • maxPluckCount          8 bits  [7-0]                      │
         * └───────────────────────────────────────────────────────────────┘
         */
        uint256 header = uint24(bytes3(buffer));

        Condition[] memory conditions = new Condition[]((header >> 8));

        _unpackConditions(buffer, conditions);

        condition = conditions[0];
        maxPluckValue = header & 0xFF;
    }

    function _unpackConditions(
        bytes memory buffer,
        Condition[] memory conditions
    ) private view {
        uint256 offset;
        uint256 compValueOffset;
        uint256 childConditionPtr;
        assembly {
            offset := add(add(buffer, 0x20), HEADER_BYTES)
            compValueOffset := add(offset, mul(mload(conditions), NODE_BYTES))
            childConditionPtr := add(conditions, 0x40)
        }

        for (uint256 c; c < conditions.length; ++c) {
            /*
             * ┌───────────────────────────────────────────────────────────┐
             * │ packed 32 bits, 4 bytes:                                  │
             * │   • encoding              3 bits  [31-29]                 │
             * │   • operator              5 bits  [28-24]                 │
             * │   • childCount           10 bits  [23-14]                 │
             * │   • inlinedSize          13 bits  [13-1]                  │
             * │   • hasCompValue          1 bit   [0]                     │
             * └───────────────────────────────────────────────────────────┘
             */
            uint256 packed;
            assembly {
                packed := shr(224, mload(offset))
                offset := add(offset, NODE_BYTES)
            }

            Condition memory condition = conditions[c];

            // Extract fields from packed bits
            uint256 encoding = (packed >> 29);
            if (encoding == 6) encoding = 0; // EtherValue -> None
            uint256 childCount = (packed >> 14) & 0x3FF;
            uint256 inlinedSize = (packed >> 1) & 0x1FFF;

            /*
             * Set Condition fields in struct order:
             *   0x00 index
             *   0x20 encoding
             *   0x40 operator
             *   0x60 compValue     (set via assembly below)
             *   0x80 children      (set via assembly below)
             *   0xa0 inlined
             *   0xc0 size
             *   0xe0 leadingBytes  (set when parsing compValue)
             */
            condition.index = c;
            condition.encoding = Encoding(encoding);
            condition.operator = Operator((packed >> 24) & 0x1F);
            condition.inlined = inlinedSize > 0;
            condition.size = inlinedSize;

            // hasCompValue
            if ((packed & 1) != 0) {
                uint256 length;
                assembly {
                    length := shr(240, mload(compValueOffset))
                    compValueOffset := add(compValueOffset, 2)
                }

                // Encoding.AbiEncoded(5): first 2 bytes are leadingBytes
                if (encoding == 5) {
                    uint256 leadingBytes;
                    assembly {
                        leadingBytes := shr(240, mload(compValueOffset))
                        compValueOffset := add(compValueOffset, 2)
                        length := sub(length, 2)
                    }
                    condition.leadingBytes = leadingBytes;
                }

                // parse compValue
                if (length > 0) {
                    assembly {
                        // free mem pointer: load
                        let compValue := mload(0x40)
                        // free mem pointer: advance
                        mstore(0x40, add(add(compValue, 0x20), length))

                        // new buffer: store length
                        mstore(compValue, length)
                        // new buffer: copy body
                        mcopy(add(compValue, 0x20), compValueOffset, length)

                        //condition: point to copied buffer (compValue at offset 0x60)
                        mstore(add(condition, 0x60), compValue)
                        // advance pointer
                        compValueOffset := add(compValueOffset, length)
                    }
                }
            }

            // Parse children
            if (childCount > 0) {
                assembly {
                    let size := mul(childCount, 0x20)
                    // free mem pointer: load
                    let dest := mload(0x40)
                    // free mem pointer: advance
                    mstore(0x40, add(add(dest, 0x20), size))

                    // new array: store length
                    mstore(dest, childCount)
                    // new array: shallow copy body
                    mcopy(add(dest, 0x20), childConditionPtr, size)

                    // condition: point to copied array (children at offset 0x80)
                    mstore(add(condition, 0x80), dest)
                    // advance child pointer
                    childConditionPtr := add(childConditionPtr, size)
                }
            }

            // EqualToAvatar: replace with EqualTo + avatar address
            if (condition.operator == Operator.EqualToAvatar) {
                condition.operator = Operator.EqualTo;
                address avatar;
                assembly {
                    avatar := sload(AVATAR_SLOT)
                }
                condition.compValue = abi.encode(avatar);
            }
        }
    }
}
