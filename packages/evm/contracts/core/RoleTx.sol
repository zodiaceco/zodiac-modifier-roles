// SPDX-License-Identifier: BUSL-1.1
// Copyright (c) 2026 Zodiac Labs GmbH
// Zodiac Roles Modifier v3
// Converts to LGPL-3.0-or-later on 2030-03-01
pragma solidity >=0.8.17 <0.9.0;

import {Operation} from "@gnosis-guild/zodiac-core/contracts/core/Operation.sol";

/**
 * @notice A transaction to execute under a role, signed by a module and
 *         relayed by anyone (EIP-712).
 *
 * @custom:member to Destination of the transaction.
 * @custom:member value Ether value of the transaction.
 * @custom:member data Transaction calldata.
 * @custom:member operation Transaction operation.
 * @custom:member roleKey Role under which the transaction is authorized.
 * @custom:member salt Distinguishes otherwise identical messages; each
 *                digest executes at most once.
 * @custom:member deadline Last timestamp at which the transaction may
 *                execute. type(uint64).max for no expiry.
 */
struct RoleTx {
    address to;
    uint256 value;
    bytes data;
    Operation operation;
    bytes32 roleKey;
    bytes32 salt;
    uint64 deadline;
}

library RoleTxLib {
    bytes32 internal constant TYPEHASH =
        keccak256(
            "RoleTx(address to,uint256 value,bytes data,uint8 operation,bytes32 roleKey,bytes32 salt,uint64 deadline)"
        );

    /**
     * @dev Computes the EIP-712 struct hash for a RoleTx message.
     *      This is `hashStruct(message)`, not the final EIP-712 digest;
     *      the domain separator is applied by zodiac-core during authentication.
     * @return structHash Hash of the encoded RoleTx message and its type hash.
     */
    function hashStruct(
        RoleTx calldata roleTx
    ) internal pure returns (bytes32 structHash) {
        return
            keccak256(
                abi.encode(
                    TYPEHASH,
                    roleTx.to,
                    roleTx.value,
                    keccak256(roleTx.data),
                    roleTx.operation,
                    roleTx.roleKey,
                    roleTx.salt,
                    roleTx.deadline
                )
            );
    }
}
