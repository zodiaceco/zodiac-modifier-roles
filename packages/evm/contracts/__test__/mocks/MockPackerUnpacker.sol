// SPDX-License-Identifier: BUSL-1.1
// Copyright (c) 2026 Zodiac Labs GmbH
// Zodiac Roles Modifier v3
// Converts to LGPL-3.0-or-later on 2030-03-01
pragma solidity >=0.8.17 <0.9.0;

import {ConditionFlat} from "../../IEvaluator.sol";
import "../../evaluator/Integrity.sol";
import "../../evaluator/serialize/Packer.sol";
import "../../evaluator/serialize/Unpacker.sol";
import "../../evaluator/types/EvaluatorError.sol";
import "../../evaluator/types/EvaluatorTypes.sol";

contract MockPackerUnpacker is IEvaluatorError {
    address public avatar;

    function setAvatar(address _avatar) external {
        avatar = _avatar;
    }

    struct ConditionForTest {
        uint256 parent;
        Operator operator;
        bytes compValue;
        Encoding encoding;
        uint256 inlineSize;
        uint256 leadingBytes;
    }

    function roundtrip(
        ConditionFlat[] memory conditions
    )
        public
        view
        returns (ConditionForTest[] memory result, uint256 maxPluckCount)
    {
        Integrity.enforce(conditions);
        bytes memory buffer = Packer.pack(conditions);

        _dirtyMemory();
        (Condition memory condition, uint256 maxCount) = Unpacker.unpack(
            buffer,
            address(this)
        );

        result = _flatten(condition);
        maxPluckCount = maxCount;
    }

    /// @dev Integrity + pack, as `packConditions` does. Used by the Lean
    ///      differential test (formal/test/lean-model.spec.ts).
    function pack(
        ConditionFlat[] memory conditions
    ) public pure returns (bytes memory) {
        Integrity.enforce(conditions);
        return Packer.pack(conditions);
    }

    /// @dev Without Integrity, as the SDK packs for the `...Packed` setters.
    function packUnchecked(
        ConditionFlat[] memory conditions
    ) public pure returns (bytes memory) {
        return Packer.pack(conditions);
    }

    /// @dev Unpacks a buffer as the evaluator loads it, whoever packed it.
    function unpack(
        bytes memory buffer
    )
        public
        view
        returns (ConditionForTest[] memory result, uint256 maxPluckCount)
    {
        _dirtyMemory();
        (Condition memory condition, uint256 maxCount) = Unpacker.unpack(
            buffer,
            address(this)
        );

        result = _flatten(condition);
        maxPluckCount = maxCount;
    }

    function unpackGas(bytes memory buffer) public view returns (uint256) {
        uint256 beforeGas = gasleft();
        Unpacker.unpack(buffer, address(this));
        return beforeGas - gasleft();
    }

    /// @dev Fills 512 KB of free memory with ones, without allocating it.
    ///      Memory past the free pointer is not guaranteed to be zero, and
    ///      the unpacker reserves its nodes without clearing them.
    function _dirtyMemory() private pure {
        assembly {
            let start := mload(0x40)
            mstore(start, not(0))
            // each copy doubles the filled region
            for {
                let size := 0x20
            } lt(size, 0x80000) {
                size := mul(size, 2)
            } {
                mcopy(add(start, size), start, size)
            }
        }
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
                inlineSize: node.inlineSize,
                leadingBytes: node.leadingBytes
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
