// SPDX-License-Identifier: BUSL-1.1
// Copyright (c) 2026 Zodiac Labs GmbH
// Zodiac Roles Modifier v3
// Converts to LGPL-3.0-or-later on 2030-03-01
pragma solidity >=0.8.17 <0.9.0;

import "../../common/AbiLocation.sol";
import "../../core/serialize/Integrity.sol";
import "../../core/serialize/ConditionPacker.sol";
import "../../core/serialize/ConditionUnpacker.sol";

/**
 * @dev Exposes AbiLocation, with the calldata as the frame: values are
 *      given, and reported, by their location in it.
 */
contract MockLocator {
    /**
     * @dev The location of every child of the value at `location`: the
     *      elements of an Array, the children of any other node. On
     *      overflow, the locations found until then.
     */
    function getChildLocations(
        bytes calldata data,
        uint256 location,
        ConditionFlat[] memory conditions,
        uint256 conditionIndex
    ) public view returns (uint256[] memory result, bool overflow) {
        Integrity.enforce(conditions);
        Condition memory condition = _unpackAndFind(conditions, conditionIndex);
        if (location > data.length) {
            if (condition.encoding != Encoding.Array) {
                result = new uint256[](condition.children.length);
            }
            return (result, true);
        }

        (Span[] memory children, bool ok) = AbiLocation.children(
            data[location:],
            condition
        );
        overflow = !ok;

        // From spans to locations. A child not found is left at 0
        result = new uint256[](children.length);
        for (uint256 i; i < children.length; ++i) {
            if (Span.unwrap(children[i]) != 0) {
                result[i] = _locate(data, AbiLocation.fromSpan(children[i]));
            }
        }
    }

    /**
     * @dev The size of the value at `location`, or `data.length + 1` if it
     *      does not lie within the calldata.
     */
    function getSize(
        bytes calldata data,
        uint256 location,
        ConditionFlat[] memory conditions,
        uint256 conditionIndex
    ) public view returns (uint256) {
        Integrity.enforce(conditions);
        Condition memory condition = _unpackAndFind(conditions, conditionIndex);
        if (location > data.length) return data.length + 1;

        (bytes calldata region, bool ok) = AbiLocation.sliceEncoded(
            data[location:],
            condition
        );
        return ok ? region.length : data.length + 1;
    }

    /// @dev Where `slice` starts, as an offset into `data`.
    function _locate(
        bytes calldata data,
        bytes calldata slice
    ) private pure returns (uint256 result) {
        return AbiLocation.offsetOf(AbiLocation.toSpan(data), slice);
    }

    /**
     * @dev Packs conditions, unpacks to build tree, then finds condition at BFS index.
     */
    function _unpackAndFind(
        ConditionFlat[] memory conditions,
        uint256 bfsIndex
    ) internal view returns (Condition memory) {
        bytes memory packed = ConditionPacker.pack(conditions);
        (Condition memory root, ) = ConditionUnpacker.unpack(packed);

        // BFS traversal to find condition at bfsIndex
        Condition[] memory queue = new Condition[](conditions.length);
        uint256 head;
        uint256 tail;

        queue[tail++] = root;

        while (head < tail) {
            Condition memory current = queue[head];

            if (head == bfsIndex) {
                return current;
            }

            head++;

            for (uint256 i; i < current.children.length; ++i) {
                queue[tail++] = current.children[i];
            }
        }

        revert("BFS index out of bounds");
    }
}
