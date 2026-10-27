import { id } from "ethers"
import { c, forAll, Permission } from "zodiac-roles-sdk"
import {
  WRAPPED_NATIVE_CURRENCIES,
  COW_PROTOCOL_VAULT_RELAYER_ADDRESS,
} from "@cowprotocol/sdk-config"
import { SupportedChainId } from "./types"

const cowOrderSigner = "0x23dA9AdE38E4477b23770DeD512fD37b12381FAB" as const

/**
 * Returns permissions allowing the avatar to sign the specified CowSwap orders.
 *
 * When "native" is specified in the sell or buy arrays, the function automatically:
 * - Replaces "native" with the chain's wrapped native token (e.g., WETH) for order signing
 * - Adds WETH.deposit() permission when native is in sell (to wrap native tokens before selling)
 * - Adds WETH.withdraw() permission when native is in buy (to unwrap received tokens)
 *
 * @deprecated The `zodiac-roles-sdk/swaps` entrypoint is deprecated and will be removed in the next major release.
 */
export const allowCowOrderSigning = ({
  chainId,
  sell,
  buy,
  receiver,
  approveAllowance,
  buyAllowance,
  sellAllowance,
  allowBalancerBalanceAccess,
}: {
  /** The chain ID where the swap will be executed. */
  chainId: SupportedChainId

  sell: (`0x${string}` | "native")[]
  buy: (`0x${string}` | "native")[]

  /** Defaults to the avatar of the Roles Modifier. */
  receiver?: `0x${string}`

  /** Allowance key to restrict approve amounts across sell tokens. If not provided, infinite approvals are allowed. */
  approveAllowance?: string
  /** Allowance key to restrict buy amount within allowance. If not provided, no buy amount restriction is applied. */
  buyAllowance?: string
  /** Allowance key to restrict sell amount within allowance. If not provided, no sell amount restriction is applied. */
  sellAllowance?: string

  /** If set to true, swaps can withdraw and deposit Balancer internal token balances of the avatar. */
  allowBalancerBalanceAccess?: boolean
}): Permission[] => {
  const gpV2VaultRelayer = COW_PROTOCOL_VAULT_RELAYER_ADDRESS[
    chainId
  ] as `0x${string}`
  const wrappedNativeToken = WRAPPED_NATIVE_CURRENCIES[chainId]
    .address as `0x${string}`

  const sellIncludesNative = sell.includes("native")
  const buyIncludesNative = buy.includes("native")

  // Replace "native" with the wrapped native token address
  const resolveTokens = (
    tokens: (`0x${string}` | "native")[]
  ): `0x${string}`[] =>
    tokens.map((token) => {
      if (token === "native") {
        return wrappedNativeToken
      }
      return token
    })

  // An empty list would leave that token unrestricted
  if (sell.length === 0 || buy.length === 0) {
    throw new Error("`sell` and `buy` must each list at least one token")
  }

  // Throw if sell and buy are identical single-element arrays (swapping a token into itself is not possible)
  if (
    sell.length === 1 &&
    buy.length === 1 &&
    ((sell[0] === "native" && buy[0] === "native") ||
      (sell[0] !== "native" &&
        buy[0] !== "native" &&
        sell[0].toLowerCase() === buy[0].toLowerCase()))
  ) {
    throw new Error("Cannot swap a token into itself")
  }

  const sellTokens = resolveTokens(sell)
  const buyTokens = resolveTokens(buy)

  // Check if all tokens are native or wrapped native
  const isOnlyNativeOrWrapped = (tokens: (`0x${string}` | "native")[]) =>
    tokens.every(
      (token) =>
        token === "native" ||
        token.toLowerCase() === wrappedNativeToken.toLowerCase()
    )

  // If both sell and buy tokens are only native/wrapped native, skip signOrder, approve, and unsignOrder permissions
  if (isOnlyNativeOrWrapped(sell) && isOnlyNativeOrWrapped(buy)) {
    const permissions: Permission[] = []

    // Add WETH.deposit() permission when selling native tokens
    if (sellIncludesNative && wrappedNativeToken) {
      permissions.push({
        targetAddress: wrappedNativeToken,
        signature: "deposit()",
        send: true,
      })
    }

    // Add WETH.withdraw() permission when buying native tokens
    if (buyIncludesNative && wrappedNativeToken) {
      permissions.push({
        targetAddress: wrappedNativeToken,
        signature: "withdraw(uint256)",
      })
    }

    return permissions
  }

  const permissions: Permission[] = [
    ...allowErc20Approve(sellTokens, gpV2VaultRelayer, approveAllowance),
    {
      targetAddress: cowOrderSigner,
      signature:
        "signOrder((address,address,address,uint256,uint256,uint32,bytes32,uint256,bytes32,bool,bytes32,bytes32),uint32,uint256)",
      condition: c.calldataMatches(
        [
          c.matches({
            sellToken: oneOf(sellTokens),
            buyToken: oneOf(buyTokens),
            receiver: receiver ? receiver : c.avatar,
            buyAmount: buyAllowance
              ? c.withinAllowance(buyAllowance)
              : undefined,
            sellAmount: sellAllowance
              ? c.withinAllowance(sellAllowance)
              : undefined,
            sellTokenBalance: allowBalancerBalanceAccess
              ? undefined
              : c.eq(id("erc20")),
            buyTokenBalance: allowBalancerBalanceAccess
              ? undefined
              : c.eq(id("erc20")),
          }),
        ],
        [
          "(address sellToken, address buyToken, address receiver, uint256 sellAmount, uint256 buyAmount, uint32 validTo, bytes32 appData, uint256 feeAmount, bytes32 kind, bool partiallyFillable, bytes32 sellTokenBalance, bytes32 buyTokenBalance)",
          "uint32",
          "uint256",
        ]
      ),
      delegatecall: true,
    },
    {
      targetAddress: cowOrderSigner,
      signature:
        "unsignOrder((address,address,address,uint256,uint256,uint32,bytes32,uint256,bytes32,bool,bytes32,bytes32))",
      condition: c.calldataMatches(
        [
          c.matches({
            sellToken: oneOf(sellTokens),
            buyToken: oneOf(buyTokens),
            receiver: receiver ? receiver : c.avatar,
          }),
        ],
        [
          "(address sellToken, address buyToken, address receiver, uint256 sellAmount, uint256 buyAmount, uint32 validTo, bytes32 appData, uint256 feeAmount, bytes32 kind, bool partiallyFillable, bytes32 sellTokenBalance, bytes32 buyTokenBalance)",
        ]
      ),
      delegatecall: true,
    },
  ]

  // Add WETH.deposit() permission when selling native tokens
  if (sellIncludesNative && wrappedNativeToken) {
    permissions.push({
      targetAddress: wrappedNativeToken,
      signature: "deposit()",
      send: true,
    })
  }

  // Add WETH.withdraw() permission when buying native tokens
  if (buyIncludesNative && wrappedNativeToken) {
    permissions.push({
      targetAddress: wrappedNativeToken,
      signature: "withdraw(uint256)",
    })
  }

  return permissions
}

const allowErc20Approve = (
  tokens: readonly `0x${string}`[],
  spender: `0x${string}`,
  allowanceKey?: string
) =>
  forAll(tokens, {
    signature: "approve(address,uint256)",
    condition: c.calldataMatches(
      [spender, allowanceKey ? c.withinAllowance(allowanceKey) : undefined],
      ["address", "uint256"]
    ),
  })

const oneOf = (values: string[]) =>
  values.length === 0
    ? undefined
    : values.length === 1
      ? c.eq(values[0])
      : c.or(...(values as [string, string, ...string[]]))
