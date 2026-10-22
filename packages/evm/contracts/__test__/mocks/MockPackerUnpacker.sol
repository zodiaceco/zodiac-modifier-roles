// SPDX-License-Identifier: BUSL-1.1
// Copyright (c) 2026 Zodiac Labs GmbH
// Zodiac Roles Modifier v3
// Converts to LGPL-3.0-or-later on 2030-03-01
pragma solidity >=0.8.17 <0.9.0;

import "../../core/serialize/ConditionPacker.sol";
import "../../core/serialize/ConditionUnpacker.sol";
import "../../core/serialize/Integrity.sol";

contract MockPackerUnpacker {
    struct ConditionForTest {
        uint256 parent;
        Operator operator;
        bytes compValue;
        Encoding encoding;
        bool inlined;
        uint256 size;
    }

    function roundtrip(
        ConditionFlat[] memory conditions
    )
        public
        view
        returns (ConditionForTest[] memory result, uint256 maxPluckValueCount)
    {
        Integrity.enforce(conditions);
        bytes memory buffer = ConditionPacker.pack(conditions);

        (Condition memory condition, uint256 maxCount) = ConditionUnpacker
            .unpack(buffer);

        result = _flatten(condition);
        maxPluckValueCount = maxCount;
    }

    function _flatten(
        Condition memory root
    ) internal pure returns (ConditionForTest[] memory) {
        uint256 total = _count(root);
        ConditionForTest[] memory result = new ConditionForTest[](total);

        Condition[] memory queue = new Condition[](total);
        uint256[] memory parents = new uint256[](total);

        queue[0] = root;
        parents[0] = 0;

        uint256 head = 0;
        uint256 tail = 1;
        uint256 current = 0;

        while (head < tail) {
            Condition memory node = queue[head];
            uint256 parent = parents[head];
            head++;

            result[current] = ConditionForTest({
                parent: parent,
                operator: node.operator,
                compValue: node.compValue,
                encoding: node.encoding,
                inlined: node.inlined,
                size: node.size
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

    function _count(
        Condition memory node
    ) private pure returns (uint256 count) {
        count = 1;
        for (uint256 i = 0; i < node.children.length; ++i) {
            count += _count(node.children[i]);
        }
    }
}
