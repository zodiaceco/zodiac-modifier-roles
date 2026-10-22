// SPDX-License-Identifier: BUSL-1.1
// Copyright (c) 2026 Zodiac Labs GmbH
// Zodiac Roles Modifier v3
// Converts to LGPL-3.0-or-later on 2030-03-01
pragma solidity >=0.8.17 <0.9.0;

import "../../types/Types.sol";
import "./Topology.sol";

/**
 * @title  TypeTree
 * @notice Extracts type trees from flat conditions for use in decoding.
 *         Variants can appear in logical or array nodes and must be handled.
 *         See inline comments for rules
 *
 * @author gnosisguild
 */
library TypeTree {
    /**
     * @notice Resolves type tree for condition at an index
     */
    function resolve(
        ConditionFlat[] memory conditions,
        uint256 i
    ) internal pure returns (Layout memory layout) {
        bool isLogical = conditions[i].operator == Operator.And ||
            conditions[i].operator == Operator.Or;
        bool isVariant = _isVariant(conditions, i);

        (uint256 childStart, uint256 childCount) = Topology.childBounds(
            conditions,
            i
        );

        if (isLogical && !isVariant) {
            /*
             * Non-variant logical nodes: first structural child defines the type tree
             */
            for (uint256 j; j < childCount; ++j) {
                if (hash(conditions, childStart + j) != 0) {
                    return resolve(conditions, childStart + j);
                }
            }

            /*
             * No structural child was found.
             */
            Layout memory none;
            return none;
        }

        layout.encoding = conditions[i].paramType == Encoding.EtherValue
            ? Encoding.None
            : conditions[i].paramType;

        /*
         * Extract leadingBytes for AbiEncoded from compValue, first 2 bytes
         * Default is 4 (selector size) when compValue is empty
         */
        if (layout.encoding == Encoding.AbiEncoded) {
            bytes memory compValue = conditions[i].compValue;
            layout.leadingBytes = compValue.length >= 2
                ? uint16(bytes2(compValue))
                : 4;
        }

        bool isArray = conditions[i].paramType == Encoding.Array;
        layout.children = new Layout[](childCount);

        uint256 length;
        for (uint256 j; j < layout.children.length; ++j) {
            if (hash(conditions, childStart + j) != bytes32(0)) {
                layout.children[length++] = resolve(conditions, childStart + j);

                /*
                 * For non-variant arrays, the first child serves as a template for
                 * all elements. For all other nodes, traverse all structural children
                 */
                if (isArray && !isVariant) {
                    break;
                }
            }
        }
        assembly {
            // layout.children is at offset 0x20 (second field)
            mstore(mload(add(layout, 0x20)), length)
        }

        layout.inlined = Topology.isInlined(conditions, i);
    }

    /**
     * @notice Computes a unique hash for a type tree structure
     */
    function hash(
        ConditionFlat[] memory conditions,
        uint256 index
    ) internal pure returns (bytes32) {
        return hash(resolve(conditions, index));
    }

    /**
     * @notice Computes a unique hash for a Layout tree
     */
    function hash(Layout memory tree) internal pure returns (bytes32 result) {
        Encoding encoding = tree.encoding == Encoding.EtherValue
            ? Encoding.None
            : tree.encoding;

        if (tree.children.length == 0) {
            return bytes32(uint256(encoding));
        }

        result = bytes32(uint256(encoding));
        for (uint256 i; i < tree.children.length; ++i) {
            bytes32 childHash = hash(tree.children[i]);
            if (childHash != 0) {
                result = keccak256(abi.encodePacked(result, childHash));
            }
        }
    }

    /**
     * @notice Checks if a node is a variant. Ignores non structural subtrees
     */
    function _isVariant(
        ConditionFlat[] memory conditions,
        uint256 index
    ) private pure returns (bool) {
        (uint256 childStart, uint256 childCount) = Topology.childBounds(
            conditions,
            index
        );

        bytes32 prevHash;
        for (uint256 i; i < childCount; ++i) {
            bytes32 nextHash = hash(conditions, childStart + i);

            if (prevHash == 0) prevHash = nextHash;
            if (nextHash == 0) continue;
            else if (prevHash != nextHash) return true;
        }
        return false;
    }
}
