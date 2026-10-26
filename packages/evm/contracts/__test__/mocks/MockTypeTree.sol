// SPDX-License-Identifier: BUSL-1.1
// Copyright (c) 2026 Zodiac Labs GmbH
// Zodiac Roles Modifier v3
// Converts to LGPL-3.0-or-later on 2030-03-01
pragma solidity >=0.8.17 <0.9.0;

import "../../core/serialize/TypeTree.sol";

contract MockTypeTree {
    struct FlatLayoutForTest {
        uint256 parent;
        Encoding encoding;
        bool inlined;
    }

    function inspect(
        ConditionFlat[] memory conditions
    ) public pure returns (FlatLayoutForTest[] memory) {
        return _flattenLayout(TypeTree.resolve(conditions, 0));
    }

    function hash(
        ConditionFlat[] memory conditions
    ) public pure returns (bytes32) {
        return TypeTree.hash(conditions, 0);
    }

    function hash(
        ConditionFlat[] memory conditions,
        uint256 index
    ) public pure returns (bytes32) {
        return TypeTree.hash(conditions, index);
    }

    function _flattenLayout(
        Layout memory root
    ) internal pure returns (FlatLayoutForTest[] memory) {
        uint256 total = _countNodes(root);
        FlatLayoutForTest[] memory result = new FlatLayoutForTest[](total);

        Layout[] memory queue = new Layout[](total);
        uint256[] memory parents = new uint256[](total);

        queue[0] = root;
        parents[0] = 0;

        uint256 head = 0;
        uint256 tail = 1;
        uint256 current = 0;

        while (head < tail) {
            Layout memory node = queue[head];
            uint256 parent = parents[head];
            head++;

            result[current] = FlatLayoutForTest({
                parent: parent,
                encoding: node.encoding,
                inlined: node.inlined
            });

            for (uint256 i = 0; i < node.children.length; ++i) {
                queue[tail] = node.children[i];
                parents[tail] = current;
                tail++;
            }

            current++;
        }

        return result;
    }

    function _countNodes(
        Layout memory node
    ) private pure returns (uint256 count) {
        count = 1;
        for (uint256 i = 0; i < node.children.length; ++i) {
            count += _countNodes(node.children[i]);
        }
    }
}
