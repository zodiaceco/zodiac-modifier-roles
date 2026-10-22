> [!IMPORTANT]
> **This repository hosts Roles v3, which is not yet released for production.** The contracts, the `zodiac-roles-sdk` in `packages/sdk` and the docs here may change in breaking ways.
>
> **Roles v2**, the version in production today, and its tooling (including the `zodiac-roles-sdk` 4.x releases on npm) live at **[zodiaceco/zodiac-modifier-roles-v2](https://github.com/zodiaceco/zodiac-modifier-roles-v2)**.

---

# Zodiac Roles Modifier v3

[![Build Status](https://github.com/zodiaceco/zodiac-modifier-roles/actions/workflows/ci.yml/badge.svg)](https://github.com/zodiaceco/zodiac-modifier-roles/actions/workflows/ci.yml)
[![Coverage Status](https://coveralls.io/repos/github/zodiaceco/zodiac-modifier-roles/badge.svg?branch=main)](https://coveralls.io/github/zodiaceco/zodiac-modifier-roles?branch=main)
[![Contributor Covenant](https://img.shields.io/badge/Contributor%20Covenant-2.1-4baaaa.svg)](https://github.com/gnosisguild/CODE_OF_CONDUCT)

The Roles Modifier belongs to the [Zodiac](https://github.com/gnosisguild/zodiac) collection of tools, which can be accessed through the Zodiac App available on [Safe](https://safe.global/).

If you have any questions about Zodiac, join the [Gnosis Guild Discord](http://discord.gnosisguild.org). Follow [@GnosisGuild](https://twitter.com/gnosisguild) on Twitter for updates.

### About the Roles Modifier

This modifier allows avatars to enforce granular, role-based, permissions for attached modules.

Modules that have been granted a role are able to unilaterally make calls to any approved addresses, approved functions, and using approved parameters.

The interface mirrors the relevant parts of the Safe's interface, so this contract can be placed between Safe modules and the Safe itself to enforce role-based permissions.

The contracts have been developed with [Solidity 0.8.37](https://github.com/ethereum/solidity/releases/tag/v0.8.37) targeting evm version cancun.

### Features

- Create multiple roles
- Assign roles to addresses
- Allow roles access to call, delegate call, and/or send to address
- Scope which functions a role can call on given address
- Define conditions on function parameters

### Flow

- Define a role by setting targets, functions, and parameters that it can call
- Assign the role to an address with `assignRoles()`
- Address can now trigger the safe to call those targets, functions, and parameters via `execTransactionWithRole()`

### Deployments

Roles v3 is not yet deployed for production. The first release targets Ethereum, Optimism, Gnosis, Arbitrum, Base and Sepolia; Zodiac deploys it to further chains.

The production **Roles v2** contracts, their addresses and the chains they are deployed on are listed at [zodiaceco/zodiac-modifier-roles-v2](https://github.com/zodiaceco/zodiac-modifier-roles-v2#deployments).

### Development environment setup

1. For each package where a `.env.sample` file is present (`packages/evm`), copy it to a `.env` file at the same location and fill in your keys.
2. From the repo root run `yarn`
3. From the repo root run `yarn build`

After that, you can start working on the different packages.

### Packages

This monorepo uses [yarn workspaces](https://yarnpkg.com/features/workspaces) and is comprised of:

- **evm**: the Roles v3 smart contracts, with tests and the formal verification (`packages/evm/formal`)
- **sdk**: a TypeScript SDK for managing roles, `zodiac-roles-sdk` (the v3 version is unreleased; the published 4.x releases come from [zodiac-modifier-roles-v2](https://github.com/zodiaceco/zodiac-modifier-roles-v2))
- **app**: a webapp for viewing roles, https://roles.gnosisguild.org (uses the published `zodiac-roles-sdk` 4.x)
- **docs**: the documentation page, https://docs.roles.gnosisguild.org
- **integration-tests**: tests of the contracts together with the SDK, currently for message signing (`personal_sign`, EIP-712)

### Audits

Roles v3 has been audited by Côme du Crest (October 2026): [report](packages/evm/docs/Audit05_Roles-V3_Oct2026_ComeDuCrest.pdf).

### Security and Liability

All contracts are WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.

### License

This repository is dual-licensed as follows:

#### Contracts and App

All smart contracts and the web app in this repository are licensed under the **Business Source License 1.1 (BUSL-1.1)**.

- Production use is restricted until **March 1, 2030**.
- On that date, these components will automatically convert to **LGPL-3.0-or-later**.

See `LICENSE.md` for full terms.

---

### SDK and Developer Tooling

The SDK included in this repository is licensed under the **GNU Lesser General Public License v3.0 or later (LGPL-3.0-or-later)** and is available under open-source terms immediately.

These components are not subject to the BUSL restrictions.

The SDK package includes its own LICENSE file.

---

#### Summary

| Component Type | License Now | License After 2030-03-01 |
|----------------|-------------|---------------------------|
| Contracts | BUSL-1.1 | LGPL-3.0-or-later |
| App | BUSL-1.1 | LGPL-3.0-or-later |
| SDK  | LGPL-3.0-or-later | LGPL-3.0-or-later |
