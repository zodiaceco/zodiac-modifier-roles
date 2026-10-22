// SPDX-License-Identifier: BUSL-1.1
// Copyright (c) 2026 Zodiac Labs GmbH
// Zodiac Roles Modifier v3
// Converts to LGPL-3.0-or-later on 2030-03-01
pragma solidity >=0.8.17 <0.9.0;

import {Operation} from "@gnosis-guild/zodiac-core/contracts/core/Operation.sol";

library RoleTx {
    bytes32 internal constant TYPEHASH =
        keccak256(
            "RoleTx(address to,uint256 value,bytes data,uint8 operation,bytes32 roleKey,bool shouldRevert,bytes32 salt)"
        );

    /**
     * @dev Computes the EIP-712 struct hash for a RoleTx message.
     *      This is `hashStruct(message)`, not the final EIP-712 digest;
     *      the domain separator is applied by zodiac-core during authentication.
     * @param to Destination of the transaction.
     * @param value Ether value of the transaction.
     * @param data Transaction calldata.
     * @param operation Transaction operation.
     * @param roleKey Role under which the transaction is authorized.
     * @param shouldRevert Whether a failed inner execution should revert.
     * @param salt Value used to distinguish the signed message for replay protection.
     * @return structHash Hash of the encoded RoleTx message and its type hash.
     */
    function hashStruct(
        address to,
        uint256 value,
        bytes calldata data,
        Operation operation,
        bytes32 roleKey,
        bool shouldRevert,
        bytes32 salt
    ) internal pure returns (bytes32 structHash) {
        return
            keccak256(
                abi.encode(
                    TYPEHASH,
                    to,
                    value,
                    keccak256(data),
                    operation,
                    roleKey,
                    shouldRevert,
                    salt
                )
            );
    }
}
