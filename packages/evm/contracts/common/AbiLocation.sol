// SPDX-License-Identifier: BUSL-1.1
// Copyright (c) 2026 Zodiac Labs GmbH
// Zodiac Roles Modifier v3
// Converts to LGPL-3.0-or-later on 2030-03-01
pragma solidity >=0.8.17 <0.9.0;

import {Condition, Encoding} from "../types/Condition.sol";
import {Operator} from "../types/Operator.sol";

/**
 * @title AbiLocation
 * @notice Resolves calldata locations and sizes for ABI-encoded structures.
 *
 * @author gnosisguild
 */
library AbiLocation {
    /**
     * @dev Resolves calldata locations for each child of a block type.
     *      Supports Tuple, Array, and AbiEncoded.
     *
     * @param data      Calldata buffer.
     * @param location  Start of the container block.
     * @param condition Condition defining structure.
     *
     * @return result   Absolute location for each child element.
     * @return overflow True if any location exceeds data bounds.
     */

    function children(
        bytes calldata data,
        uint256 location,
        Condition memory condition
    ) internal pure returns (uint256[] memory result, bool overflow) {
        bool isArray = condition.encoding == Encoding.Array;

        uint256 childCount = condition.children.length;
        if (isArray) {
            /*
             * Arrays prefix their block with an element count word. Read it
             * and advance location to the actual beginning of the block. Treat
             * the rest like a tuple.
             */
            if (location + 32 > data.length) return (result, true);
            assembly {
                childCount := calldataload(add(data.offset, location))
            }
            location += 32;
        }
        result = new uint256[](childCount);

        /*
         * HEAD + TAIL encoding for block types (tuples, arrays):
         *
         * HEAD: Fixed-size region at block start. Each element occupies a
         *       slot here - static children store values inline (possibly
         *       multi-word), dynamic children store a 32-byte offset pointing
         *       into TAIL.
         *
         * TAIL: Variable-size region after HEAD with actual dynamic data,
         *       in declaration order. Offsets are relative to block start.
         */
        uint256 headOffset;
        for (uint256 i; i < childCount; ++i) {
            Condition memory child = condition.children[isArray ? 0 : i];

            if (child.inlined) {
                /* Static elements */
                result[i] = location + headOffset;
                headOffset += child.size;
            } else {
                /* Dynamic elements */
                result[i] = _tailLocation(data, location, headOffset);
                headOffset += 32;
            }

            if (result[i] > data.length) {
                return (result, true);
            }
        }
        return (result, false);
    }

    /**
     * @dev Computes the encoded size of a value at location.
     */
    function size(
        bytes calldata data,
        uint256 location,
        Condition memory condition
    ) internal pure returns (uint256 result) {
        // Every ABI-encoded element occupies at least one word.
        if (location + 32 > data.length) return data.length + 1;

        Encoding encoding = condition.encoding;
        if (encoding == Encoding.Static) {
            return 32;
        }

        /*
         * Always preload the first word - its meaning depends on encoding:
         * - Dynamic: byte length of content
         * - Array: element count
         */
        uint256 word;
        assembly {
            word := calldataload(add(data.offset, location))
        }

        /*
         * A Note on AbiEncoded and this function:
         *
         * AbiEncoded location is patched during ConditionEvaluation
         * so that top-level and nested AbiEncoded nodes are treated
         * uniformly by the evaluator. As a consequence, this function
         * only supports nested AbiEncoded nodes – calling it on a
         * root one would fail. This is fine because the entry point
         * for size is always via EqualTo, and AbiEncoded cannot be
         * paired with that operator.
         */
        if (encoding == Encoding.Dynamic || encoding == Encoding.AbiEncoded) {
            // Dynamic types: length prefix + padded content (ceil32)
            return 32 + ((word + 31) & ~uint256(31));
        }

        uint256 childCount = condition.children.length;
        if (encoding == Encoding.None) {
            /*
             * Logical nodes (And/Or) are transparent. We delegate the size
             * calculation to the first valid (non-empty, non-overflowing)
             * child subtree.
             *
             * This works for both:
             * - Non-Variant: All children share the same type tree.
             * - Variant: Children have different types, but variants are
             *            always Dynamic-encoded, so size is deterministic.
             */
            for (uint256 i; i < childCount; ++i) {
                result = size(data, location, condition.children[i]);
                if (result > 0 && result <= data.length) return result;
            }
            return data.length + 1;
        }

        bool isArray = encoding == Encoding.Array;
        if (isArray) {
            /*
             * Arrays prefix their block with an element count word. Read it
             * and advance location to the actual beginning of the block. Treat
             * the rest like a tuple.
             */
            childCount = word;
            location += 32;
            result = 32;
        }

        /*
         * HEAD + TAIL encoding for block types (tuples, arrays):
         *
         * HEAD: Fixed-size region at block start. Each element occupies a
         *       slot here - static children store values inline (possibly
         *       multi-word), dynamic children store a 32-byte offset pointing
         *       into TAIL.
         *
         * TAIL: Variable-size region after HEAD with actual dynamic data,
         *       in declaration order. Offsets are relative to block start.
         */
        uint256 headOffset;
        for (uint256 i; i < childCount; ++i) {
            Condition memory child = condition.children[isArray ? 0 : i];

            if (child.inlined) {
                /* Static elements */
                result += child.size;
                headOffset += child.size;
            } else {
                /* Dynamic elements */
                result +=
                    32 +
                    size(
                        data,
                        _tailLocation(data, location, headOffset),
                        child
                    );
                headOffset += 32;
            }
        }
    }

    /**
     * @dev Computes the absolute position of a dynamic (non-inline) element.
     *      Reads the relative offset from HEAD and adds it to the block start
     *      to locate the element in the TAIL region.
     *
     * @param data       The calldata being inspected.
     * @param location   Absolute start position of the current ABI block.
     * @param headOffset Byte offset within HEAD where the pointer resides.
     * @return           Absolute position, or data.length + 1 on overflow.
     */
    function _tailLocation(
        bytes calldata data,
        uint256 location,
        uint256 headOffset
    ) private pure returns (uint256) {
        // HEAD overflows buffer
        if (location + headOffset + 32 > data.length) {
            return data.length + 1;
        }

        uint256 tailOffset;
        assembly {
            tailOffset := calldataload(
                add(data.offset, add(location, headOffset))
            )
        }

        // TAIL points backwards (malicious or malformed)
        if (tailOffset <= headOffset) {
            return data.length + 1;
        }

        // TAIL overflows buffer
        if (location + tailOffset + 32 > data.length) {
            return data.length + 1;
        }

        return location + tailOffset;
    }
}
