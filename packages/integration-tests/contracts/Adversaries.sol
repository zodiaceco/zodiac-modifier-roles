// SPDX-License-Identifier: LGPL-3.0-only
pragma solidity ^0.8.24;

/**
 * @title Hostile
 * @notice A call target that, when the avatar calls it, makes the calls it
 *         was given (into Roles: executions, setters, invalidate, ...) and
 *         records how each ended. It can also be an enabled module of Roles
 *         and call it directly (`act`).
 */
contract Hostile {
    struct Attempt {
        address to;
        bytes data;
    }

    Attempt[] private plan;
    /// @notice For each attempt of the last run: zero on success, else the
    ///         revert data's selector (0xffffffff for empty revert data).
    bytes4[] public results;
    bool public revertAfter;
    uint256 public runs;

    function setPlan(
        address[] calldata tos,
        bytes[] calldata datas,
        bool revertAfter_
    ) external {
        delete plan;
        for (uint256 i; i < tos.length; ++i) {
            plan.push(Attempt(tos[i], datas[i]));
        }
        revertAfter = revertAfter_;
    }

    function resultCount() external view returns (uint256) {
        return results.length;
    }

    /// @notice Calls `to` as this contract (as a module, or any caller).
    function act(address to, bytes calldata data) external payable {
        (bool ok, bytes memory ret) = to.call{value: msg.value}(data);
        if (!ok) {
            assembly {
                revert(add(ret, 0x20), mload(ret))
            }
        }
    }

    fallback() external payable {
        delete results;
        ++runs;
        for (uint256 i; i < plan.length; ++i) {
            (bool ok, bytes memory ret) = plan[i].to.call(plan[i].data);
            results.push(
                ok ? bytes4(0) : ret.length < 4 ? bytes4(0xffffffff) : bytes4(ret)
            );
        }
        if (revertAfter) revert("hostile");
    }
}

/**
 * @title Signer1271
 * @notice An ERC-1271 signer that is also a module: valid for hashes it
 *         approved, or misbehaving as set by `mode`.
 *
 * mode 0: valid for approved hashes only
 * mode 1: valid for every hash
 * mode 2: reverts
 * mode 3: returns a wrong value
 * mode 4: tries to execute through Roles (`reenter`), and is valid only if
 *         that failed: a reentry that succeeded would show as a rejected
 *         signature
 * mode 5: returns 2 bytes
 */
contract Signer1271 {
    bytes4 private constant MAGIC = 0x1626ba7e;

    uint8 public mode;
    mapping(bytes32 => bool) public approved;
    address public reenterTo;
    bytes public reenterData;

    function setMode(uint8 mode_) external {
        mode = mode_;
    }

    function approve(bytes32 hash) external {
        approved[hash] = true;
    }

    function setReenter(address to, bytes calldata data) external {
        reenterTo = to;
        reenterData = data;
    }

    function act(address to, bytes calldata data) external payable {
        (bool ok, bytes memory ret) = to.call{value: msg.value}(data);
        if (!ok) {
            assembly {
                revert(add(ret, 0x20), mload(ret))
            }
        }
    }

    function isValidSignature(
        bytes32 hash,
        bytes calldata
    ) external returns (bytes4) {
        uint8 m = mode;
        if (m == 2) revert("no");
        if (m == 3) return 0xdeadbeef;
        if (m == 4) {
            (bool ok, ) = reenterTo.call(reenterData);
            return ok ? bytes4(0) : MAGIC;
        }
        if (m == 5) {
            assembly {
                mstore(0, shl(240, 0x1626))
                return(0, 2)
            }
        }
        return m == 1 || approved[hash] ? MAGIC : bytes4(0);
    }
}

/// @notice A call target that reverts.
contract Reverter {
    fallback() external payable {
        revert("reverter");
    }
}
