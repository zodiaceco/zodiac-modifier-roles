// SPDX-License-Identifier: BUSL-1.1
// Copyright (c) 2026 Zodiac Labs GmbH
// Zodiac Roles Modifier v3
// Converts to LGPL-3.0-or-later on 2030-03-01
pragma solidity >=0.8.17 <0.9.0;

/*
 * StorageSlots — slot indices of `RolesStorage` state variables, exposed for
 * inline-assembly consumers that can't reference the variables directly
 * (i.e. libraries).
 *
 * Storage layout of `Roles` (zodiac-core 4 + RolesStorage):
 *
 *   ┌──────┬─────────────────────────────────────────────────────────┐
 *   │ Slot │ Source                                                  │
 *   ├──────┼─────────────────────────────────────────────────────────┤
 *   │  0   │ Initializable._initialized (bool)         ┐             │
 *   │      │ Ownable.owner              (address)      ┘  packed     │
 *   │  1   │ Module.avatar              (address)                    │
 *   │  2   │ Module.target              (address)                    │
 *   │  3   │ ExecutionTracker.consumed  (mapping)                    │
 *   │  4   │ Modifier.modules           (mapping)                    │
 *   │  5   │ RolesStorage.roles         (mapping)                    │
 *   │  6   │ RolesStorage.allowances    (mapping)                    │
 *   │  7   │ RolesStorage.unwrappers    (mapping)                    │
 *   │  8   │ RolesStorage.defaultRoles  (mapping)                    │
 *   └──────┴─────────────────────────────────────────────────────────┘
 *
 * Transient (TLOAD/TSTORE — not regular storage):
 *   Modifier._authenticatedModule
 *   RolesStorage._reentrancyGuard
 *
 */

uint256 constant AVATAR_SLOT = 1;
uint256 constant ALLOWANCES_SLOT = 6;
