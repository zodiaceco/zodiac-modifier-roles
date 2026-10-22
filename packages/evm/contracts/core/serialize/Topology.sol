// SPDX-License-Identifier: BUSL-1.1
// Copyright (c) 2026 Zodiac Labs GmbH
// Zodiac Roles Modifier v3
// Converts to LGPL-3.0-or-later on 2030-03-01
pragma solidity >=0.8.17 <0.9.0;

import "../../types/Types.sol";

/**
 * @title  Topology
 * @notice Utilities for navigating flat condition tree structure.
 *
 * @author gnosisguild
 */
library Topology {
    /**
     * @notice Gets the bounds and counts of children for a given node
     * @param conditions The flat array of conditions
     * @param index The index of the parent node
     *
     * @return childStart The index of the first child (0 if no children)
     * @return childCount The total number of children
     */
    function childBounds(
        ConditionFlat[] memory conditions,
        uint256 index
    ) internal pure returns (uint256 childStart, uint256 childCount) {
        uint256 len = conditions.length;

        for (uint256 i = index + 1; i < len; ++i) {
            uint256 parent = conditions[i].parent;

            if (parent == index) {
                if (childCount == 0) childStart = i;
                ++childCount;
            } else if (parent > index) {
                break;
            }
        }
    }

    /**
     * @notice Checks if a node is inlined (all descendants are static)
     */
    function isInlined(
        ConditionFlat[] memory conditions,
        uint256 index
    ) internal pure returns (bool) {
        Encoding encoding = conditions[index].paramType;
        if (
            encoding == Encoding.Dynamic ||
            encoding == Encoding.Array ||
            encoding == Encoding.AbiEncoded
        ) {
            return false;
        }

        (uint256 childStart, uint256 childCount) = childBounds(
            conditions,
            index
        );
        for (uint256 i; i < childCount; ++i) {
            if (!isInlined(conditions, childStart + i)) {
                return false;
            }
        }
        return true;
    }

    /**
     * @notice Computes the inlined size (in bytes) for a node.
     *
     * @dev Only invoked on nodes already known to be inlined; the assertion
     *      documents this invariant rather than acting as a runtime guard.
     */
    function inlinedSize(
        ConditionFlat[] memory conditions,
        uint256 index
    ) internal pure returns (uint256 size) {
        assert(isInlined(conditions, index) == true);

        /*
         * Dynamic, Array, and AbiEncoded types are never inlined, so this
         * function is guaranteed to only process Static, Tuple, or None types
         * (enforced by the assertion above).
         */
        Encoding encoding = conditions[index].paramType;

        if (encoding == Encoding.Static) {
            return 32;
        }

        /*
         * Remaining encodings:
         * - Tuple: sum of all children sizes
         * - None: delegates to first structural child
         */
        (uint256 childStart, uint256 childCount) = childBounds(
            conditions,
            index
        );

        for (uint256 i; i < childCount; ++i) {
            uint256 childSize = inlinedSize(conditions, childStart + i);
            /*
             * None nodes are transparent wrappers (And/Or or non-structural).
             * Since inlined nodes can't have variants, all structural children
             * share the same size. Return on first non-zero (structural) child.
             */
            if (encoding == Encoding.None && childSize > 0) return childSize;
            size += childSize;
        }
    }
}
