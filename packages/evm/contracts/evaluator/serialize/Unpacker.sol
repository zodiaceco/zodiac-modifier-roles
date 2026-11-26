// SPDX-License-Identifier: BUSL-1.1
// Copyright (c) 2026 Zodiac Labs GmbH
// Zodiac Roles Modifier v3
// Converts to LGPL-3.0-or-later on 2030-03-01
pragma solidity >=0.8.17 <0.9.0;

import {IRolesCore} from "../../IEvaluator.sol";
import {Condition, Encoding, Operator} from "../types/EvaluatorTypes.sol";

/**
 * @title  Unpacker
 * @notice Reconstructs a `Condition` tree from a bit-packed buffer in the
 *         format defined by `Packer`.
 *
 * @dev    Performance-critical: every transaction execution begins by loading
 *         the packed condition tree from runtime code (via `extcodecopy`) and
 *         unpacking it. Minimizes Solidity memory overhead via targeted inline
 *         assembly.
 */
library Unpacker {
    uint256 private constant HEADER_BYTES = 3;
    uint256 private constant NODE_BYTES = 4;
    uint256 private constant CONDITION_BYTES = 0xe0; // condition in memory is 7 words

    /**
     * @dev Avoids `new Condition[](count)` (which zeroes each struct and keeps
     *      an outer pointer array):
     *      - Single allocation: reserves one block for all structs by
     *        advancing the free memory pointer once.
     *      - Direct struct init: the block is unzeroed, so the loop writes
     *        every word in place (pointing empty `compValue` and `children`
     *        to Solidity's zero slot `0x60`).
     *      - Contiguous BFS wiring: children sit consecutively in the block,
     *        so a single cursor fills each parent's `children` array.
     *
     *      Assumes a valid, non-empty buffer matching `Packer`'s format (no
     *      bounds, `count > 0`, or enum range checks).
     */
    function unpack(
        bytes memory buffer,
        address core
    ) internal view returns (Condition memory root, uint256 maxPluckCount) {
        /*
         * ┌───────────────────────────────────────────────────────────────┐
         * │ header 24 bits, 3 bytes:                                      │
         * │   • conditionNodeCount    16 bits  [23-8]                     │
         * │   • maxPluckCount          8 bits  [7-0]                      │
         * └───────────────────────────────────────────────────────────────┘
         */
        uint256 count;
        // Read positions in the packed buffer
        uint256 nodePtr;
        uint256 compValuePtr;
        // Next struct in the output block not yet given to a parent
        uint256 nextChildPtr;
        assembly {
            let header := mload(add(buffer, 0x20))
            count := shr(240, header)
            maxPluckCount := byte(2, header)

            // Reserve one contiguous block for all Condition structs, root
            // first. Not zeroed: the loop initializes every field.
            root := mload(0x40)
            mstore(0x40, add(root, mul(count, CONDITION_BYTES)))

            // Buffer layout: [3B header | count * 4B nodes | compValues]
            nodePtr := add(add(buffer, 0x20), HEADER_BYTES)
            compValuePtr := add(nodePtr, mul(count, NODE_BYTES))
            // Root is no one's child, so start at the second struct.
            nextChildPtr := add(root, CONDITION_BYTES)
        }

        Condition memory condition = root;
        for (uint256 c; c < count; ++c) {
            /*
             * ┌───────────────────────────────────────────────────────────┐
             * │ node entry, 32 bits, 4 bytes:                             │
             * │   • encoding              3 bits  [31-29]                 │
             * │   • operator              5 bits  [28-24]                 │
             * │   • childCount           10 bits  [23-14]                 │
             * │   • inlinedSize          13 bits  [13-1]                  │
             * │   • hasCompValue          1 bit   [0]                     │
             * └───────────────────────────────────────────────────────────┘
             */
            uint256 packed;
            assembly {
                // Right-align the 4-byte node entry into bits [31-0] (upper
                // bits are zeroed, so `encoding` needs no mask).
                packed := shr(224, mload(nodePtr))
                nodePtr := add(nodePtr, NODE_BYTES)
            }

            // Kept as uint256: converting to the enum types would range-check
            // every node.
            uint256 encoding = packed >> 29;
            if (encoding == uint256(Encoding.EtherValue)) {
                // EtherValue -> None: reads tx value, not calldata
                encoding = uint256(Encoding.None);
            }
            uint256 operator = (packed >> 24) & 0x1F;

            /*
             * Set all Condition fields, in struct order:
             *   0x00 index
             *   0x20 encoding
             *   0x40 operator
             *   0x60 compValue     (empty; filled below if present)
             *   0x80 children      (empty; filled below if present)
             *   0xa0 inlineSize
             *   0xc0 leadingBytes  (zero; filled below for AbiEncoded)
             *
             * 0x60 is Solidity's zero slot: length 0 for empty bytes/arrays.
             */
            assembly {
                mstore(condition, c)
                mstore(add(condition, 0x20), encoding)
                mstore(add(condition, 0x40), operator)
                mstore(add(condition, 0x60), 0x60)
                mstore(add(condition, 0x80), 0x60)
                mstore(add(condition, 0xa0), and(shr(1, packed), 0x1FFF))
                mstore(add(condition, 0xc0), 0)
            }

            // hasCompValue: wire format is [uint16 length][data]
            if ((packed & 1) != 0) {
                uint256 length;
                assembly {
                    length := shr(240, mload(compValuePtr))
                    compValuePtr := add(compValuePtr, 2)
                }

                // AbiEncoded: data starts with [uint16 leadingBytes]
                // followed by any bytes to match against the prefix.
                if (encoding == uint256(Encoding.AbiEncoded)) {
                    uint256 leadingBytes;
                    assembly {
                        leadingBytes := shr(240, mload(compValuePtr))
                        compValuePtr := add(compValuePtr, 2)
                        length := sub(length, 2)
                    }
                    condition.leadingBytes = leadingBytes;
                }

                if (length > 0) {
                    assembly {
                        // Allocate bytes buffer: 0x20 length prefix + data.
                        // Advance FMP past (0x20 + length), rounded up to a
                        // 32-byte word boundary (0x20 + 0x1f = 0x3f).
                        // Trailing padding bytes in the last word are left
                        // unzeroed.
                        let compValue := mload(0x40)
                        mstore(
                            0x40,
                            and(add(add(compValue, 0x3f), length), not(0x1f))
                        )
                        mstore(compValue, length)
                        mcopy(add(compValue, 0x20), compValuePtr, length)

                        mstore(add(condition, 0x60), compValue)
                        compValuePtr := add(compValuePtr, length)
                    }
                }
            }

            // Parse children
            uint256 childCount = (packed >> 14) & 0x3FF;
            if (childCount > 0) {
                assembly {
                    // Allocate Condition[]: length word followed by direct
                    // pointers to the next childCount structs in the reserved
                    // block (populated by later iterations of the outer loop).
                    let children := mload(0x40)
                    let end := add(add(children, 0x20), mul(childCount, 0x20))
                    mstore(0x40, end)
                    mstore(children, childCount)
                    for {
                        let slot := add(children, 0x20)
                    } lt(slot, end) {
                        slot := add(slot, 0x20)
                    } {
                        mstore(slot, nextChildPtr)
                        nextChildPtr := add(nextChildPtr, CONDITION_BYTES)
                    }

                    mstore(add(condition, 0x80), children)
                }
            }

            // EqualToAvatar: replace with EqualTo + avatar address from Core
            if (operator == uint256(Operator.EqualToAvatar)) {
                condition.operator = Operator.EqualTo;
                // same: condition.compValue = abi.encode(IRolesCore(core).avatar());
                condition.compValue = _avatar(core);
            }

            assembly {
                condition := add(condition, CONDITION_BYTES)
            }
        }
    }

    /**
     * @dev Same value as `abi.encode(IRolesCore(core).avatar())`, without
     *      decoding the returned address and encoding it again: the call
     *      writes its 32-byte answer straight into a new `bytes`. Saves
     *      around 300 gas per EqualToAvatar node.
     */
    function _avatar(address core) private view returns (bytes memory result) {
        bytes4 selector = IRolesCore.avatar.selector;
        assembly {
            // Allocate bytes of length 32: length word + one data word.
            result := mload(0x40)
            mstore(0x40, add(result, 0x40))
            mstore(result, 0x20)

            // Selector goes in scratch space; the return value is written
            // directly into the data word.
            mstore(0x00, selector)
            let success := staticcall(
                gas(),
                core,
                0x00,
                0x04,
                add(result, 0x20),
                0x20
            )
            // Also guards against EOAs or short returns, where the call
            // succeeds without writing 32 bytes.
            if iszero(and(success, gt(returndatasize(), 0x1f))) {
                revert(0, 0)
            }
        }
    }
}
