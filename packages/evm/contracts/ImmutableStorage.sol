// SPDX-License-Identifier: BUSL-1.1
// Copyright (c) 2026 Zodiac Labs GmbH
// Zodiac Roles Modifier v3
// Converts to LGPL-3.0-or-later on 2030-03-01
pragma solidity >=0.8.17 <0.9.0;

interface ISingletonFactory {
    function deploy(
        bytes memory initCode,
        bytes32 salt
    ) external returns (address);
}

library ImmutableStorage {
    address public constant SINGLETON_FACTORY =
        0xce0042B868300000d44A59004Da54A005ffdcf9f;

    function store(bytes memory buffer) internal returns (address pointer) {
        bytes memory bytecode = _creationBytecode(buffer);
        pointer = _calculateAddress(bytecode);

        uint256 size;
        assembly {
            size := extcodesize(pointer)
        }

        if (size == 0) {
            assert(
                pointer ==
                    ISingletonFactory(SINGLETON_FACTORY).deploy(
                        bytecode,
                        bytes32(0)
                    )
            );
        }
    }

    /**
     * @notice Reads the runtime bytecode stored at a `pointer` contract, skipping the first byte.
     *
     * @param pointer The address of the deployed pointer contract.
     * @return buffer The raw bytecode (minus the prepended 0x00) read from `pointer`.
     */
    function load(address pointer) internal view returns (bytes memory buffer) {
        assembly {
            let size := sub(extcodesize(pointer), 1)
            // free memory point ought to be multiple of 32
            let rounded := and(add(size, 31), not(31))

            // Get free pointer
            buffer := mload(0x40)
            // Store length
            mstore(buffer, size)
            // Update free pointer
            mstore(0x40, add(add(buffer, 0x20), rounded))

            // Copy code starting from offset 0x01 (skip the 0x00 prefix)
            extcodecopy(pointer, add(buffer, 0x20), 0x01, size)
        }
    }

    /**
     * @notice Generates creation bytecode that deploys a contract containing `data` as its runtime bytecode.
     * @dev The generated constructor copies `data` into memory and returns it as the contract's code.
     *      A leading `0x00` byte is prepended so the resulting contract cannot be called.
     *
     * Assembly layout (constructor):
     *
     * ```
     * 0x00    63 <XXXXXX>   PUSH4 code_size         ; push code length (runtime size)
     * 0x01    80             DUP1                   ; duplicate size
     * 0x02    60 0e          PUSH1 0x0e             ; offset of actual code
     * 0x03    60 00          PUSH1 0x00             ; destination offset
     * 0x04    39             CODECOPY               ; copy <code_size> bytes from offset 0x0e
     * 0x05    60 00          PUSH1 0x00             ; return offset
     * 0x06    f3             RETURN                 ; return code as runtime bytecode
     * <CODE>                                        ; runtime code (0x00 + data)
     * ```
     *
     */
    function _creationBytecode(
        bytes memory data
    ) private pure returns (bytes memory) {
        return
            abi.encodePacked(
                hex"63",
                uint32(data.length + 1),
                hex"80_60_0E_60_00_39_60_00_F3",
                // Prepend 0x00 to prevent the deployed contract from being callable
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
