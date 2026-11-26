import { TypedData, TypedDataToPrimitiveTypes } from "abitype"

/**
 * Type-level utilities for deriving primitive TypeScript types from an
 * EIP-712 `TypedData` definition.
 *
 * The primary type is the one struct that is not referenced as a field type
 * by any other struct (`EIP712Domain` excluded — it is always a root).
 */
type ReferencedStructs<T extends TypedData> = {
  [K in keyof T]: T[K][number]["type"] extends infer FieldType
    ? FieldType extends `${infer Base}[${string}]`
      ? Base extends keyof T
        ? Base
        : never
      : FieldType extends keyof T
        ? FieldType
        : never
    : never
}[keyof T]

export type PrimaryType<T extends TypedData> = Exclude<
  keyof T,
  "EIP712Domain" | ReferencedStructs<T>
>

export type DomainStructOf<T extends TypedData> =
  TypedDataToPrimitiveTypes<T>["EIP712Domain"]

/** The message struct of `P`, by default the inferred primary type. */
export type MessageStructOf<
  T extends TypedData,
  P extends keyof T & string = PrimaryType<T> & string,
> = TypedDataToPrimitiveTypes<T>[P]
