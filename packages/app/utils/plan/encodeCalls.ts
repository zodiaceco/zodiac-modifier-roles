import { Interface } from "ethers"
import { flattenCondition, rolesAbi } from "zodiac-roles-sdk"

import { Call } from "./Call"

const rolesInterface = new Interface(rolesAbi)
const posterInterface = Interface.from([
  "function post(string content,string tag)",
])

export const encodeCalls = (
  calls: Call[],
  rolesMod: `0x${string}`
): { to: `0x${string}`; data: `0x${string}` }[] => {
  return calls.map((call) => {
    switch (call.call) {
      case "allowTarget": {
        return {
          to: rolesMod,
          data: rolesInterface.encodeFunctionData("allowTarget", [
            call.roleKey,
            call.targetAddress,
            call.executionOptions,
          ]) as `0x${string}`,
        }
      }

      case "scopeTarget": {
        return {
          to: rolesMod,
          data: rolesInterface.encodeFunctionData("scopeTarget", [
            call.roleKey,
            call.targetAddress,
          ]) as `0x${string}`,
        }
      }

      case "revokeTarget": {
        return {
          to: rolesMod,
          data: rolesInterface.encodeFunctionData("revokeTarget", [
            call.roleKey,
            call.targetAddress,
          ]) as `0x${string}`,
        }
      }

      case "allowFunction": {
        return {
          to: rolesMod,
          data: rolesInterface.encodeFunctionData("allowFunction", [
            call.roleKey,
            call.targetAddress,
            call.selector,
            call.executionOptions,
          ]) as `0x${string}`,
        }
      }

      case "scopeFunction": {
        try {
          return {
            to: rolesMod,
            data: rolesInterface.encodeFunctionData("scopeFunction", [
              call.roleKey,
              call.targetAddress,
              call.selector,
              flattenCondition(call.condition).map((c) => ({
                ...c,
                compValue: c.compValue || "0x",
              })),
              call.executionOptions,
            ]) as `0x${string}`,
          }
        } catch (e) {
          console.warn([
            call.roleKey,
            call.targetAddress,
            call.selector,
            flattenCondition(call.condition).map((c) => ({
              ...c,
              compValue: c.compValue || "0x",
            })),
            call.executionOptions,
          ])
          throw e
        }
      }

      case "revokeFunction": {
        return {
          to: rolesMod,
          data: rolesInterface.encodeFunctionData("revokeFunction", [
            call.roleKey,
            call.targetAddress,
            call.selector,
          ]) as `0x${string}`,
        }
      }
      case "assignRoles": {
        return {
          to: rolesMod,
          data: rolesInterface.encodeFunctionData("assignRoles", [
            call.member,
            [call.roleKey],
            [call.join],
          ]) as `0x${string}`,
        }
      }
      case "setAllowance": {
        return {
          to: rolesMod,
          data: rolesInterface.encodeFunctionData("setAllowance", [
            call.key,
            call.balance,
            call.maxRefill,
            call.refill,
            call.period,
            call.timestamp,
          ]) as `0x${string}`,
        }
      }

      case "postAnnotations": {
        const content = JSON.stringify({
          rolesMod,
          roleKey: call.roleKey,
          ...call.body,
        })
        const tag = POSTER_TAG_ROLES_ANNOTATION

        return {
          to: POSTER_ADDRESS,
          data: posterInterface.encodeFunctionData("post", [
            content,
            tag,
          ]) as `0x${string}`,
        }
      }
    }
  })
}

// EIP-3722 Poster contract
const POSTER_ADDRESS =
  "0x000000000000cd17345801aa8147b8D3950260FF" as `0x${string}`
const POSTER_TAG_ROLES_ANNOTATION = "ROLES_PERMISSION_ANNOTATION"
