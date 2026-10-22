// SPDX-License-Identifier: BUSL-1.1
// Copyright (c) 2026 Zodiac Labs GmbH
// Zodiac Roles Modifier v3
// Converts to LGPL-3.0-or-later on 2030-03-01
pragma solidity >=0.8.17 <0.9.0;

import "../../common/AbiLocation.sol";
import "../../core/serialize/Integrity.sol";
import "../../core/serialize/ConditionPacker.sol";
import "../../core/serialize/ConditionUnpacker.sol";

contract MockLocator {
    function getChildLocations(
        bytes calldata data,
        uint256 location,
        ConditionFlat[] memory conditions,
        uint256 conditionIndex
    ) public view returns (uint256[] memory, bool overflow) {
        Integrity.enforce(conditions);
        Condition memory condition = _unpackAndFind(conditions, conditionIndex);
        return AbiLocation.children(data, location, condition);
    }

    function getSize(
        bytes calldata data,
        uint256 location,
        ConditionFlat[] memory conditions,
        uint256 conditionIndex
    ) public view returns (uint256) {
        Integrity.enforce(conditions);
        Condition memory condition = _unpackAndFind(conditions, conditionIndex);
        return AbiLocation.size(data, location, condition);
    }

    function pluck(
        bytes calldata data,
        uint256 offset,
        uint256 size
    ) public pure returns (bytes calldata) {
        return data[offset:offset + size];
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
