// SPDX-License-Identifier: BUSL-1.1
// Copyright (c) 2026 Zodiac Labs GmbH
// Zodiac Roles Modifier v3
// Converts to LGPL-3.0-or-later on 2030-03-01
pragma solidity >=0.8.17 <0.9.0;

import "../interfaces/ITransactionUnwrapper.sol";

interface IMultiSend {
    function multiSend(bytes memory transactions) external payable;
}

contract MultiSendUnwrapper is ITransactionUnwrapper {
    uint256 private constant OFFSET_START = 68;

    error UnsupportedMode();
    error MalformedHeader();
    error MalformedBody();

    function unwrap(
        address,
        uint256 value,
        bytes calldata data,
        Operation operation
    ) external pure returns (UnwrappedTransaction[] memory) {
        if (value != 0) {
            revert UnsupportedMode();
        }
        if (operation != Operation.DelegateCall) {
            revert UnsupportedMode();
        }
        _validateHeader(data);
        uint256 count = _validateEntries(data);
        return _unwrapEntries(data, count);
    }

    function _validateHeader(bytes calldata data) private pure {
        // first 4 bytes are the selector for multiSend(bytes)
        if (bytes4(data) != IMultiSend.multiSend.selector) {
            revert MalformedHeader();
        }

        // the following 32 bytes are the offset to the bytes param
        // (always 0x20)
        if (bytes32(data[4:]) != bytes32(uint256(0x20))) {
            revert MalformedHeader();
        }

        // the following 32 bytes are the length of the bytes param
        uint256 length = uint256(bytes32(data[36:]));

        // validate that the total calldata length matches
        // it's the 4 + 32 + 32 bytes checked above + the <length> bytes
        // padded to a multiple of 32
        if (4 + _ceil32(32 + 32 + length) != data.length) {
            revert MalformedHeader();
        }
    }

    function _validateEntries(
        bytes calldata data
    ) private pure returns (uint256 count) {
        uint256 offset = OFFSET_START;
        uint256 end = OFFSET_START + uint256(bytes32(data[36:]));

        for (; offset < end; ) {
            // Per transaction:
            // Operation   1  bytes
            // To          20 bytes
            // Value       32 bytes
            // Length      32 bytes
            // Data        Length bytes
            uint8 operation = uint8(bytes1(data[offset:]));
            if (operation > 1) {
                revert MalformedBody();
            }

            uint256 length = uint256(bytes32(data[offset + 53:]));
            if (offset + 85 + length > end) {
                revert MalformedBody();
            }

            offset += 85 + length;
            count++;
        }

        if (count == 0) {
            revert MalformedBody();
        }
    }

    function _unwrapEntries(
        bytes calldata data,
        uint256 count
    ) private pure returns (UnwrappedTransaction[] memory result) {
        result = new UnwrappedTransaction[](count);

        uint256 offset = OFFSET_START;
        for (uint256 i; i < count; ++i) {
            result[i].operation = Operation(uint8(bytes1(data[offset:])));
            offset += 1;

            result[i].to = address(bytes20(data[offset:]));
            offset += 20;

            result[i].value = uint256(bytes32(data[offset:]));
            offset += 32;

            uint256 size = uint256(bytes32(data[offset:]));
            offset += 32;

            result[i].dataLocation = offset;
            result[i].dataSize = size;
            offset += size;
        }
    }

    function _ceil32(uint256 length) private pure returns (uint256) {
        return (length + 31) & ~uint256(31);
    }
}
