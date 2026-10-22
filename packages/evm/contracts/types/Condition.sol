// SPDX-License-Identifier: BUSL-1.1
// Copyright (c) 2026 Zodiac Labs GmbH
// Zodiac Roles Modifier v3
// Converts to LGPL-3.0-or-later on 2030-03-01
pragma solidity >=0.8.17 <0.9.0;

import {Operator} from "./Operator.sol";

enum Encoding {
    None,
    Static,
    Dynamic,
    Tuple,
    Array,
    AbiEncoded,
    /* EtherValue is a nonstructural, and an alias for None */
    EtherValue
}

struct Condition {
    /// @dev BFS index from unpacking - identifies this node in the flattened tree
    uint256 index;
    Encoding encoding;
    Operator operator;
    bytes compValue;
    Condition[] children;
    /* meta fields */
    bool inlined;
    uint256 size;
    uint256 leadingBytes;
}

// This struct is a flattened version of Condition
// used for ABI encoding a scope config tree
// (ABI does not support recursive types)
struct ConditionFlat {
    uint16 parent;
    Encoding paramType;
    Operator operator;
    bytes compValue;
}

/// @dev Layout is a type tree used for AbiDecoder and EIP712 encoding.
struct Layout {
    Encoding encoding;
    Layout[] children;
    uint256 leadingBytes;
    bool inlined;
}

struct LayoutFlat {
    uint256 parent;
    Encoding encoding;
}

/// @dev Payload is the result of AbiDecoder.inspect() - maps parameter locations.
struct Payload {
    uint256 location;
    uint256 size;
    Payload[] children;
    /* meta flags */
    bool inlined;
    bool variant;
    bool overflow;
}
