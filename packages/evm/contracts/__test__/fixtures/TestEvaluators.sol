// SPDX-License-Identifier: BUSL-1.1
// Copyright (c) 2026 Zodiac Labs GmbH
// Zodiac Roles Modifier v3
// Converts to LGPL-3.0-or-later on 2030-03-01
pragma solidity >=0.8.17 <0.9.0;

import "../../IEvaluator.sol";
import {Status} from "../../evaluator/types/EvaluatorTypes.sol";

/// @dev Malicious/permissive evaluator that always approves every call.
contract TestAlwaysAllowEvaluator is IEvaluator {
    function evaluate(
        uint256,
        address,
        uint256,
        bytes calldata,
        Operation,
        Consumption[] calldata consumptions
    ) external pure override returns (Result memory) {
        return Result(0, 0, 0, consumptions);
    }

    function pack(
        ConditionFlat[] calldata
    ) external pure override returns (bytes memory) {
        return "";
    }
}

/// @dev Replacement evaluator that always rejects with a fixed violation.
contract TestAlwaysDenyEvaluator is IEvaluator {
    function evaluate(
        uint256,
        address,
        uint256,
        bytes calldata,
        Operation,
        Consumption[] calldata
    ) external pure override returns (Result memory) {
        return
            Result(
                uint8(Status.ParameterNotAllowed),
                7,
                4,
                new Consumption[](0)
            );
    }

    function pack(
        ConditionFlat[] calldata
    ) external pure override returns (bytes memory) {
        return "";
    }
}

/// @dev Simulates a future Evaluator that defines new Encoding, Operator, and
///      Status codes beyond the v3 enums.
contract TestFutureEvaluator is IEvaluator {
    uint8 public constant FUTURE_STATUS = 200;

    function evaluate(
        uint256,
        address,
        uint256,
        bytes calldata,
        Operation,
        Consumption[] calldata
    ) external pure override returns (Result memory) {
        return Result(FUTURE_STATUS, 3, 36, new Consumption[](0));
    }

    function pack(
        ConditionFlat[] calldata conditions
    ) external pure override returns (bytes memory) {
        // Accepts arbitrary uint8 paramType / operator values and returns
        // non-empty opaque bytes so Core stores them without enum checks.
        return
            abi.encodePacked(conditions[0].paramType, conditions[0].operator);
    }
}

/// @dev Malicious evaluator that attempts to mutate storage during evaluation.
///      Must revert because Core invokes the evaluator via STATICCALL.
contract TestMutatingEvaluator {
    uint256 public counter;

    function evaluate(
        uint256,
        address,
        uint256,
        bytes calldata,
        Operation,
        Consumption[] calldata consumptions
    ) external returns (Result memory) {
        counter += 1;
        return Result(0, 0, 0, consumptions);
    }
}

/// @dev Malicious evaluator returning arbitrary caller-configured consumptions
///      (e.g. forged balance/timestamp, overspend, or duplicate keys).
contract TestForgingConsumptionEvaluator is IEvaluator {
    Consumption[] private _forged;

    function setForged(Consumption[] calldata forged) external {
        delete _forged;
        for (uint256 i; i < forged.length; ++i) {
            _forged.push(forged[i]);
        }
    }

    function evaluate(
        uint256,
        address,
        uint256,
        bytes calldata,
        Operation,
        Consumption[] calldata
    ) external view override returns (Result memory) {
        return Result(0, 0, 0, _forged);
    }

    function pack(
        ConditionFlat[] calldata
    ) external pure override returns (bytes memory) {
        return "";
    }
}

/// @dev Evaluator that reverts during evaluation and packing.
contract TestRevertingEvaluator is IEvaluator {
    error IntentionalEvaluatorRevert();

    function evaluate(
        uint256,
        address,
        uint256,
        bytes calldata,
        Operation,
        Consumption[] calldata
    ) external pure override returns (Result memory) {
        revert IntentionalEvaluatorRevert();
    }

    function pack(
        ConditionFlat[] calldata
    ) external pure override returns (bytes memory) {
        revert IntentionalEvaluatorRevert();
    }
}

/// @dev Evaluator that returns invalid/unparseable bytes.
contract TestMalformedReturnEvaluator {
    function evaluate(
        uint256,
        address,
        uint256,
        bytes calldata,
        Operation,
        Consumption[] calldata
    ) external pure {
        assembly {
            mstore(0x00, 0xdeadbeef)
            return(0x00, 0x04)
        }
    }
}
