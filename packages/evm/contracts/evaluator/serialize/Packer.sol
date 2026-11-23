// SPDX-License-Identifier: BUSL-1.1
// Copyright (c) 2026 Zodiac Labs GmbH
// Zodiac Roles Modifier v3
// Converts to LGPL-3.0-or-later on 2030-03-01
pragma solidity >=0.8.17 <0.9.0;

import {ConditionFlat} from "../../IEvaluator.sol";
import {Encoding, Operator} from "../types/EvaluatorTypes.sol";

/**
 * @title  Packer
 * @notice A library that provides packing functions for conditions,
 *         transforming ConditionFlat[] into a memory-optimized buffer.
 *
 * @dev    A first pass computes every node's child count and inlined size,
 *         so that packing does not rescan the tree for each node.
 *
 * ╔════════════════════════════════ BUFFER ═════════════════════════════════╗
 * ║ ┌─────────────────────────────────────────────────────────────────────┐ ║
 * ║ │ HEADER (3 bytes = 24 bits)                                          │ ║
 * ║ ├─────────────────────────────────────────────────────────────────────┤ ║
 * ║ │ • conditionNodeCount     16 bits (bytes 0-1)                        │ ║
 * ║ │ • maxPluckValue           8 bits (byte 2)                           │ ║
 * ║ └─────────────────────────────────────────────────────────────────────┘ ║
 * ║ ┌─────────────────────────────────────────────────────────────────────┐ ║
 * ║ │ NODES (nodeCount × 4 bytes each)                                    │ ║
 * ║ ├─────────────────────────────────────────────────────────────────────┤ ║
 * ║ │ Each node (32 bits = 4 bytes):                                      │ ║
 * ║ │   • encoding              3 bits  [31-29]                           │ ║
 * ║ │   • operator              5 bits  [28-24]                           │ ║
 * ║ │   • childCount           10 bits  [23-14]                           │ ║
 * ║ │   • inlinedSize          13 bits  [13-1]                            │ ║
 * ║ │   • hasCompValue          1 bit   [0]                               │ ║
 * ║ └─────────────────────────────────────────────────────────────────────┘ ║
 * ║ ┌─────────────────────────────────────────────────────────────────────┐ ║
 * ║ │ COMPVALUES (variable length)                                        │ ║
 * ║ ├─────────────────────────────────────────────────────────────────────┤ ║
 * ║ │ For each node with hasCompValue=true (in BFS order):                │ ║
 * ║ │   • length               16 bits  (compValue byte length)           │ ║
 * ║ │   • data                 N bytes  (actual compValue data)           │ ║
 * ║ └─────────────────────────────────────────────────────────────────────┘ ║
 * ╚═════════════════════════════════════════════════════════════════════════╝
 *
 */
library Packer {
    uint256 private constant HEADER_BYTES = 3;
    uint256 private constant NODE_BYTES = 4;

    function pack(
        ConditionFlat[] memory conditions
    ) internal pure returns (bytes memory buffer) {
        LayoutNode[] memory nodes = _layout(conditions);

        _transform(conditions, nodes);

        (uint256 compValuesSize, uint256 maxPluckCount) = _count(conditions);

        uint256 nodeCount = conditions.length;

        buffer = new bytes(
            HEADER_BYTES + nodeCount * NODE_BYTES + compValuesSize
        );

        uint256 header = (nodeCount << 8) | maxPluckCount;
        assembly {
            mstore(add(buffer, 0x20), shl(232, header))
        }

        _packNodes(conditions, nodes, buffer);
    }

    function _packNodes(
        ConditionFlat[] memory conditions,
        LayoutNode[] memory nodes,
        bytes memory buffer
    ) private pure {
        uint256 offset = HEADER_BYTES;
        uint256 compValueOffset = HEADER_BYTES + conditions.length * NODE_BYTES;

        for (uint256 i; i < conditions.length; ++i) {
            ConditionFlat memory condition = conditions[i];

            uint8 encoding = condition.paramType;
            uint256 childCount = nodes[i].childCount;
            uint256 inlinedSize = nodes[i].inlinedSize;

            bytes memory compValue = condition.compValue;
            uint256 compValueLength = compValue.length;
            bool hasCompValue = compValueLength > 0;

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
            uint256 packed = (uint256(encoding) << 29) |
                (uint256(condition.operator) << 24) |
                (childCount << 14) |
                (inlinedSize << 1) |
                (hasCompValue ? 1 : 0);

            /*
             * The or with mload preserves bytes 4-31 (compValues written in
             * previous iterations) while writing our 4 bytes at positions 0-3.
             */
            assembly {
                let dest := add(add(buffer, 0x20), offset)
                mstore(dest, or(mload(dest), shl(224, packed)))
            }
            offset += NODE_BYTES;

            // Pack compValue writes at tail, no preserving required
            if (hasCompValue) {
                assembly {
                    let dest := add(add(buffer, 0x20), compValueOffset)
                    // write 2 bytes length
                    mstore(dest, shl(240, compValueLength))
                    // copy compValue body
                    mcopy(add(dest, 2), add(compValue, 0x20), compValueLength)
                }
                compValueOffset = compValueOffset + 2 + compValueLength;
            }
        }
    }

    function _count(
        ConditionFlat[] memory conditions
    ) private pure returns (uint256 compValuesSize, uint256 maxPluckCount) {
        for (uint256 i; i < conditions.length; ++i) {
            if (conditions[i].operator == uint8(Operator.Pluck)) {
                uint8 pluckIndex = uint8(conditions[i].compValue[0]);
                if (pluckIndex + 1 > maxPluckCount) {
                    maxPluckCount = pluckIndex + 1;
                }
            }

            uint256 length = conditions[i].compValue.length;
            if (length > 0) {
                compValuesSize += 2 + length;
            }
        }
    }

    /**
     * @dev Normalizes conditions in-place before packing:
     *      1. AbiEncoded without compValue gets default leadingBytes (0x0004)
     *      2. EqualTo at offset has 32-byte head pointer stripped
     */
    function _transform(
        ConditionFlat[] memory conditions,
        LayoutNode[] memory nodes
    ) private pure {
        for (uint256 i; i < conditions.length; ++i) {
            /*
             * Patch AbiEncoded leadingBytes
             *
             * AbiEncoded nodes without compValue need a default leadingBytes of 4
             * (function selector size). Store as 2-byte big-endian value.
             */
            if (
                conditions[i].paramType == uint8(Encoding.AbiEncoded) &&
                conditions[i].compValue.length == 0
            ) {
                conditions[i].compValue = hex"0004";
            }

            /*
             * Remove Extraneous Offsets - Strip the head offset from EqualTo
             * compValues
             *
             * Callers pass `abi.encode(value)` as compValue. For a value that
             * is not inlined, that encoding starts with a 32-byte offset to the
             * data. The evaluator compares against the parameter where its data
             * sits in calldata, with no such offset, so the first word is
             * dropped here.
             *
             * Inlined values are encoded without an offset and stay as is.
             */
            if (
                conditions[i].operator == uint8(Operator.EqualTo) &&
                nodes[i].notInlined
            ) {
                bytes memory compValue = conditions[i].compValue;
                assembly {
                    let newLength := sub(mload(compValue), 32)
                    compValue := add(compValue, 32)
                    mstore(compValue, newLength)
                }
                conditions[i].compValue = compValue;
            }
        }
    }

    struct LayoutNode {
        uint256 childCount;
        /// The node or a descendant is Dynamic, Array or AbiEncoded
        bool notInlined;
        /// Encoded size in bytes, 0 if not inlined
        uint256 inlinedSize;
    }

    /**
     * @dev Linear pre-pass: child count, inlined and size of every node.
     *
     *      A node is inlined when its value is encoded in place and always
     *      has the same size. That holds unless the node, or anything below
     *      it, is Dynamic, Array or AbiEncoded.
     *
     *      Sizes:
     *      - Static:      32 bytes
     *      - None:        the size of its first child that has one
     *      - anything else: the sum of its children
     *      - not inlined: 0
     *
     *      Runs backwards, leveraging BFS order: children before parents.
     */
    function _layout(
        ConditionFlat[] memory conditions
    ) private pure returns (LayoutNode[] memory nodes) {
        uint256 count = conditions.length;
        nodes = new LayoutNode[](count);

        for (uint256 next = count; next > 0; --next) {
            uint256 i = next - 1;
            LayoutNode memory node = nodes[i];
            uint8 encoding = conditions[i].paramType;

            if (
                encoding == uint8(Encoding.Dynamic) ||
                encoding == uint8(Encoding.Array) ||
                encoding == uint8(Encoding.AbiEncoded)
            ) {
                node.notInlined = true;
            }

            if (node.notInlined) {
                node.inlinedSize = 0;
            } else if (encoding == uint8(Encoding.Static)) {
                node.inlinedSize = 32;
            }

            if (i == 0) break;

            uint256 parentIndex = conditions[i].parent;
            LayoutNode memory parent = nodes[parentIndex];
            ++parent.childCount;
            if (node.notInlined) {
                parent.notInlined = true;
            } else if (
                conditions[parentIndex].paramType != uint8(Encoding.None)
            ) {
                parent.inlinedSize += node.inlinedSize;
            } else if (node.inlinedSize > 0) {
                // And / Or are transparent: the size of the value they sit
                // at, given by the first child that has one. Children are
                // visited last to first, so the first one is written last
                parent.inlinedSize = node.inlinedSize;
            }
        }
    }
}
