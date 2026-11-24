// SPDX-License-Identifier: BUSL-1.1
// Copyright (c) 2026 Zodiac Labs GmbH
// Zodiac Roles Modifier v3
// Converts to LGPL-3.0-or-later on 2030-03-01
pragma solidity >=0.8.17 <0.9.0;

import "./types/CoreError.sol";

interface ISingletonFactory {
    function deploy(
        bytes memory initCode,
        bytes32 salt
    ) external returns (address);
}

/**
 * @title  ExtCode
 * @notice Stores immutable byte buffers as contract runtime code (SSTORE2).
 *
 * @dev    Deployed via the ERC-2470 singleton factory with salt 0, so
 *         identical buffers resolve to the same address chain-wide.
 *         Runtime code is `0x00 ++ buffer`; readers skip the leading byte.
 */
library ExtCode {
    address internal constant SINGLETON_FACTORY =
        0xce0042B868300000d44A59004Da54A005ffdcf9f;

    /**
     * @notice Stores `buffer` and returns the address of its pointer contract.
     *         Deploys only if the pointer does not exist yet.
     *
     * @param buffer   The bytes to store.
     * @return pointer The address whose runtime code is `0x00 ++ buffer`.
     */
    function write(bytes memory buffer) internal returns (address pointer) {
        bytes memory bytecode = _creationBytecode(buffer);
        pointer = _calculateAddress(bytecode);

        uint256 size;
        assembly {
            size := extcodesize(pointer)
        }

        if (size != 0) {
            return pointer;
        }

        // The factory returns address(0) when CREATE2 fails, e.g. when the
        // buffer exceeds the EIP-170 code size limit
        if (
            ISingletonFactory(SINGLETON_FACTORY).deploy(bytecode, bytes32(0)) !=
            pointer
        ) {
            revert ICoreError.ExtCodeWriteFailed();
        }
    }

    /**
     * @dev Creation bytecode whose constructor returns `0x00 ++ data` as
     *      runtime code. The leading `0x00` (STOP) makes the pointer contract
     *      a no-op when called.
     *
     * ```
     * 0x00    63 <XXXXXXXX>  PUSH4 code_size   ; runtime size (data + 1)
     * 0x05    80             DUP1              ; duplicate size
     * 0x06    60 0e          PUSH1 0x0e        ; offset of runtime code
     * 0x08    60 00          PUSH1 0x00        ; destination offset
     * 0x0a    39             CODECOPY          ; copy code_size bytes to memory
     * 0x0b    60 00          PUSH1 0x00        ; return offset
     * 0x0d    f3             RETURN            ; return as runtime code
     * 0x0e    00 <data>                        ; runtime code
     * ```
     */
    function _creationBytecode(
        bytes memory data
    ) private pure returns (bytes memory) {
        return
            abi.encodePacked(
                hex"63",
                uint32(data.length + 1),
                hex"80_60_0E_60_00_39_60_00_F3",
                hex"00",
                data
            );
    }

    function _calculateAddress(
        bytes memory creationBytecode
    ) private pure returns (address) {
        bytes32 hash = keccak256(
            abi.encodePacked(
                bytes1(0xff),
                SINGLETON_FACTORY,
                bytes32(0),
                keccak256(creationBytecode)
            )
        );
        return address(uint160(uint256(hash)));
    }
}
