import { after, describe, it } from "node:test";
import { network } from "hardhat";
import {
  encodeAbiParameters,
  encodeFunctionData,
  encodePacked,
  parseAbi,
  parseAbiParameters,
} from "viem";
import type { Hex } from "viem";

import { createSetup } from "../setup.js";
import {
  ConditionViolationStatus,
  Encoding,
  ExecutionOptions,
  Operator,
  flattenCondition,
  type RolesContract,
} from "../utils.js";

const SEL = "0xaabbccdd";

const connection = await network.create();
const { viem, networkHelpers } = connection;
const { loadFixture } = networkHelpers;
const { setupTestContract } = createSetup(connection);

type ConditionInput = Parameters<typeof flattenCondition>[0];

interface RawNode {
  encoding: Encoding;
  operator: Operator;
  childCount?: number;
  inlineSize?: number;
  compValue?: string;
}

const enc = (types: string[], values: readonly unknown[]) =>
  encodeAbiParameters(parseAbiParameters(types.join(", ")), values);

const word = (n: bigint | number) => BigInt(n).toString(16).padStart(64, "0");

const calldata = (...words: string[]): Hex => (SEL + words.join("")) as Hex;

const pass = (
  paramType: Encoding,
  children?: ConditionInput[],
): ConditionInput =>
  children
    ? { paramType, operator: Operator.Pass, children }
    : { paramType, operator: Operator.Pass };

const matches = (children: ConditionInput[]): ConditionInput => ({
  paramType: Encoding.AbiEncoded,
  operator: Operator.Matches,
  children,
});

const eq = (
  paramType: Encoding,
  compValue: string,
  children?: ConditionInput[],
): ConditionInput => ({
  paramType,
  operator: Operator.EqualTo,
  compValue,
  ...(children ? { children } : {}),
});

/** Packs raw nodes without running Integrity, matching ConditionUnpacker format. */
function packRaw(nodes: RawNode[], maxPluck = 0): Hex {
  const header =
    nodes.length.toString(16).padStart(4, "0") +
    maxPluck.toString(16).padStart(2, "0");
  const nodeWords: string[] = [];
  const compChunks: string[] = [];
  for (const n of nodes) {
    const cv = n.compValue ? n.compValue.replace(/^0x/, "") : "";
    const hasCv = cv.length > 0 ? 1 : 0;
    const w =
      ((n.encoding & 0x7) << 29) |
      ((n.operator & 0x1f) << 24) |
      (((n.childCount ?? 0) & 0x3ff) << 14) |
      (((n.inlineSize ?? 0) & 0x1fff) << 1) |
      hasCv;
    nodeWords.push((w >>> 0).toString(16).padStart(8, "0"));
    if (hasCv) {
      compChunks.push((cv.length / 2).toString(16).padStart(4, "0") + cv);
    }
  }
  return ("0x" + header + nodeWords.join("") + compChunks.join("")) as Hex;
}

async function setup() {
  const base = await setupTestContract();
  const { roles, member, testContractAddress, roleKey } = base;

  const allow = (condition: ConditionInput, options = ExecutionOptions.None) =>
    base.allowTarget(flattenCondition(condition), options);

  const allowRaw = (packed: Hex, options = ExecutionOptions.None) =>
    roles.write.allowTargetPacked([
      roleKey,
      testContractAddress,
      packed,
      options,
    ]);

  const invoke = (data: Hex, value: bigint | number = 0) =>
    roles.write.execTransactionFromModule(
      [testContractAddress, BigInt(value), data, 0],
      { account: member.account },
    );

  return { ...base, allow, allowRaw, invoke };
}

const expectOverflow = (
  roles: RolesContract,
  tx: Promise<Hex>,
  nodeIndex?: number,
  offset?: number,
) =>
  viem.assertions.revertWithCustomErrorWithArgs(
    tx,
    roles,
    "ConditionViolation",
    [
      ConditionViolationStatus.CalldataOverflow,
      nodeIndex !== undefined ? BigInt(nodeIndex) : (i: bigint) => i >= 0n,
      offset !== undefined ? BigInt(offset) : (o: bigint) => o >= 0n,
    ],
  );

describe("Calldata slicing and traversal safety", () => {
  after(async () => {
    await connection.close();
  });

  // ───────────────────────────────────────────────────────────────
  // 1. Containment: reads never escape their enclosing slice
  // ───────────────────────────────────────────────────────────────
  describe("Containment", () => {
    it("bounds nested AbiEncoded static fields to the outer bytes length", async () => {
      const { roles, allow, invoke } = await loadFixture(setup);

      // Outer: fn(bytes inner, uint256 decoy)
      // Inner expects two uint256s (64 bytes), but outer bytes only declares 32 bytes.
      // Decoy sits right after inner in outer calldata — must NOT be readable as inner[1].
      await allow(
        matches([
          {
            paramType: Encoding.AbiEncoded,
            operator: Operator.Matches,
            compValue: "0x0000",
            children: [
              eq(Encoding.Static, enc(["uint256"], [1])),
              eq(Encoding.Static, enc(["uint256"], [2])),
            ],
          },
          pass(Encoding.Static),
        ]),
      );

      // head: ptr(inner)=0x40, decoy=2; tail: len=32, inner[0]=1, trailing=2
      const data = calldata(word(0x40), word(2), word(32), word(1), word(2));
      await expectOverflow(roles, invoke(data), 1);
    });

    it("bounds nested AbiEncoded dynamic offsets to the outer bytes length", async () => {
      const { roles, allow, invoke } = await loadFixture(setup);

      // Outer: fn(bytes inner, bytes decoy)
      // Inner has 1 dynamic bytes param whose offset points past inner's declared
      // 32-byte length directly into decoy's tail in outer calldata.
      await allow(
        matches([
          {
            paramType: Encoding.AbiEncoded,
            operator: Operator.Matches,
            compValue: "0x0000",
            children: [eq(Encoding.Dynamic, enc(["bytes"], ["0xdeadbeef"]))],
          },
          pass(Encoding.Dynamic),
        ]),
      );

      // inner (at 0x40): len = 32, payload = [offset = 0x40] (points past inner's 32 bytes!)
      // decoy (at 0x80): len = 4, data = 0xdeadbeef
      const data = calldata(
        word(0x40), // ptr(inner)
        word(0x80), // ptr(decoy)
        word(32), // inner.length = 32 bytes (only covers its head slot)
        word(0x40), // inner param0 offset = 64 -> would land on decoy at 0xa0 if unbounded
        word(4), // decoy.length
        "deadbeef" + "00".repeat(28),
      );
      await expectOverflow(roles, invoke(data), 1);
    });

    it("rejects nested AbiEncoded when leadingBytes exceeds outer bytes length", async () => {
      const { roles, allow, invoke } = await loadFixture(setup);

      await allow(
        matches([
          {
            paramType: Encoding.AbiEncoded,
            operator: Operator.Matches,
            compValue: "0x0004", // expects 4 leading bytes
            children: [pass(Encoding.Static)],
          },
          pass(Encoding.Static),
        ]),
      );

      // inner declares only 2 bytes, even though 30 padding + sibling bytes follow
      const data = calldata(
        word(0x40),
        word(0),
        word(2),
        "aabb" + "00".repeat(30),
      );
      await expectOverflow(roles, invoke(data), 1);
    });

    it("rejects Pluck on a dynamic array whose element escapes into a sibling parameter", async () => {
      const { roles, allow, invoke } = await loadFixture(setup);

      // fn(bytes[] a, bytes decoy): a[0]'s offset jumps past a into decoy
      await allow(
        matches([
          {
            paramType: Encoding.Array,
            operator: Operator.Pluck,
            compValue: "0x00",
            children: [pass(Encoding.Dynamic)],
          },
          pass(Encoding.Dynamic),
        ]),
      );

      // a (at 0x40): count = 1, a[0] offset = 0x60 (skips past head to decoy)
      // decoy (at 0x80): len = 2, 0xaabb
      const data = calldata(
        word(0x40), // ptr(a)
        word(0x80), // ptr(decoy)
        word(1), // a.length
        word(0x60), // a[0] offset != 0x20 (tries to reach decoy)
        word(2), // decoy.length
        "aabb" + "00".repeat(30),
      );
      await expectOverflow(roles, invoke(data), 1);
    });

    it("confines Zip to empty Span on an unwritten pluck slot instead of reading root calldata", async () => {
      const { roles, allowRaw, invoke } = await loadFixture(setup);

      // Raw-packed ZipEvery reading slots 0 and 1 when neither was plucked
      const packed = packRaw(
        [
          {
            encoding: Encoding.None,
            operator: Operator.ZipEvery,
            childCount: 1,
            compValue: "0x0001",
          },
          {
            encoding: Encoding.Tuple,
            operator: Operator.Matches,
            childCount: 2,
          },
          {
            encoding: Encoding.Static,
            operator: Operator.Pass,
            inlineSize: 32,
          },
          {
            encoding: Encoding.Static,
            operator: Operator.Pass,
            inlineSize: 32,
          },
        ],
        2,
      );
      await allowRaw(packed);

      // Even if root calldata starts with a valid array count (0), unwritten
      // pluck slots hold Span(0) (length 0), so Zip fails with CalldataOverflow.
      const data = ("0x" + word(0) + word(0)) as Hex;
      await expectOverflow(roles, invoke(data), 0);
    });

    it("applies the same Slice window to every element under ArrayEvery", async () => {
      const { roles, allow, invoke } = await loadFixture(setup);

      // Each uint256 element passes if either its low 4 bytes, read through
      // Slice(shift=28, size=4), equal 0x11223344, or the full word equals
      // 0x55667788. The Slice window must not leak into the sibling EqualTo
      // or into the next element.
      const abi = parseAbi(["function fn(uint256[])"]);

      await allow(
        matches([
          {
            paramType: Encoding.Array,
            operator: Operator.ArrayEvery,
            children: [
              {
                paramType: Encoding.None,
                operator: Operator.Or,
                children: [
                  {
                    paramType: Encoding.Static,
                    operator: Operator.Slice,
                    compValue: encodePacked(["uint16", "uint8"], [28, 4]),
                    children: [
                      eq(Encoding.Static, enc(["uint256"], [0x11223344])),
                    ],
                  },
                  eq(Encoding.Static, enc(["uint256"], [0x55667788])),
                ],
              },
            ],
          },
        ]),
      );

      // Elem 0 hits Slice (matches low 4 bytes despite upper bytes set),
      // Elem 1 fails Slice and falls through to full 32-byte EqualTo.
      const elem0 = (1n << 200n) | 0x11223344n;
      const elem1 = 0x55667788n;
      await invoke(
        encodeFunctionData({ abi, functionName: "fn", args: [[elem0, elem1]] }),
      );

      // Elem 2 has upper bytes set + low 4 bytes 0x55667788 -> must fail both branches
      const elem2 = (1n << 200n) | 0x55667788n;
      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke(
          encodeFunctionData({
            abi,
            functionName: "fn",
            args: [[elem0, elem2]],
          }),
        ),
        roles,
        "ConditionViolation",
        [
          ConditionViolationStatus.NotEveryArrayElementPasses,
          2n,
          (o: bigint) => o > 0n,
        ],
      );
    });

    it("bounds even a raw-packed navigation child under Slice to the slice window", async () => {
      const { roles, allowRaw, invoke } = await loadFixture(setup);

      // Raw-packed: Matches [ Slice(shift=0, size=4) -> Matches [ Static(32) ] ]
      // Even though outer calldata has 32 bytes, the child only sees the 4-byte window.
      const packed = packRaw([
        {
          encoding: Encoding.AbiEncoded,
          operator: Operator.Matches,
          childCount: 1,
          compValue: "0x0004",
        },
        {
          encoding: Encoding.Static,
          operator: Operator.Slice,
          childCount: 1,
          inlineSize: 32,
          compValue: encodePacked(["uint16", "uint8"], [0, 4]),
        },
        {
          encoding: Encoding.Tuple,
          operator: Operator.Matches,
          childCount: 1,
        },
        {
          encoding: Encoding.Static,
          operator: Operator.Pass,
          inlineSize: 32,
        },
      ]);
      await allowRaw(packed);

      await expectOverflow(roles, invoke(calldata(word(42))), 2, 4);
    });
  });

  // ───────────────────────────────────────────────────────────────
  // 2. Head & tail bounds (overflow-safe, never reverts on bad data)
  // ───────────────────────────────────────────────────────────────
  describe("Head & tail bounds", () => {
    it("rejects calldata one byte short of a static head slot", async () => {
      const { roles, allow, invoke } = await loadFixture(setup);

      await allow(matches([pass(Encoding.Static)]));

      // selector + 31 bytes
      await expectOverflow(roles, invoke((SEL + "00".repeat(31)) as Hex), 0);
    });

    it("accepts exactly 32 bytes for a static param", async () => {
      const { allow, invoke } = await loadFixture(setup);

      await allow(matches([pass(Encoding.Static)]));

      await invoke(calldata(word(0)));
    });

    it("rejects calldata one byte short of a dynamic head pointer", async () => {
      const { roles, allow, invoke } = await loadFixture(setup);

      await allow(matches([pass(Encoding.Dynamic)]));

      // selector + 31 bytes
      await expectOverflow(roles, invoke((SEL + "00".repeat(31)) as Hex), 0);
    });

    it("rejects a truncated second dynamic head pointer", async () => {
      const { roles, allow, invoke } = await loadFixture(setup);

      await allow(matches([pass(Encoding.Dynamic), pass(Encoding.Dynamic)]));

      // selector + ptr0 + 16 bytes of ptr1
      await expectOverflow(
        roles,
        invoke((SEL + word(0x40) + "00".repeat(16)) as Hex),
        0,
      );
    });

    it("rejects out-of-bounds, backwards, and truncated dynamic tails", async () => {
      const { roles, allow, invoke } = await loadFixture(setup);

      await allow(matches([eq(Encoding.Dynamic, enc(["bytes"], ["0xaa"]))]));

      // Offset beyond calldata
      await expectOverflow(roles, invoke(calldata(word(0x40))), 0);
      // Backwards offset (points to 0, before own slot end 0x20)
      await expectOverflow(roles, invoke(calldata(word(0), word(0))), 0);
      // Offset inside own slot (0x1f < 0x20)
      await expectOverflow(roles, invoke(calldata(word(0x1f), word(0))), 0);
      // Partial tail length word (only 16 bytes at offset 0x20)
      await expectOverflow(
        roles,
        invoke((SEL + word(0x20) + "00".repeat(16)) as Hex),
        0,
      );
      // Declared length = 64, only 32 bytes follow
      await expectOverflow(
        roles,
        invoke(calldata(word(0x20), word(64), word(0))),
        1,
      );
      // ceil32(33) = 64 exceeds 32 bytes present
      await expectOverflow(
        roles,
        invoke(calldata(word(0x20), word(33), word(0))),
        1,
      );
      // Declared length = 5 fits in 5 bytes present, but ceil32(5) = 32 padding is missing
      await expectOverflow(
        roles,
        invoke((SEL + word(0x20) + word(5) + "aabbccddee") as Hex),
        1,
      );
    });

    it("rejects out-of-bounds or backwards element offsets inside an Array", async () => {
      const { roles, allow, invoke } = await loadFixture(setup);

      await allow(
        matches([
          {
            paramType: Encoding.Array,
            operator: Operator.ArrayEvery,
            children: [pass(Encoding.Dynamic)],
          },
        ]),
      );

      // count = 1, arr[0] offset = 0x40 (beyond calldata)
      await expectOverflow(
        roles,
        invoke(calldata(word(0x20), word(1), word(0x40))),
        1,
      );
      // count = 1, arr[0] offset = 0 (points backwards into head slot)
      await expectOverflow(
        roles,
        invoke(calldata(word(0x20), word(1), word(0), word(0))),
        1,
      );
    });

    it("rejects huge array counts without reverting or over-allocating", async () => {
      const { roles, allow, invoke } = await loadFixture(setup);

      // Dynamic array navigation (ArrayEvery)
      await allow(
        matches([
          {
            paramType: Encoding.Array,
            operator: Operator.ArrayEvery,
            children: [pass(Encoding.Static)],
          },
        ]),
      );

      // count = uint256.max
      const maxU256 = (1n << 256n) - 1n;
      await expectOverflow(
        roles,
        invoke(calldata(word(0x20), word(maxU256))),
        1,
      );
      // count = 2 when only 1 word follows (count > body.length / 32)
      await expectOverflow(
        roles,
        invoke(calldata(word(0x20), word(2), word(1))),
        1,
      );

      // Static-element array in sliceEncoded (EqualTo) with count = uint256.max
      await allow(
        matches([
          eq(Encoding.Array, enc(["uint256[]"], [[1]]), [
            pass(Encoding.Static),
          ]),
        ]),
      );
      await expectOverflow(
        roles,
        invoke(calldata(word(0x20), word(maxU256))),
        1,
      );
    });

    it("handles uint256 overflow words cleanly without panicking", async () => {
      const { roles, allow, invoke } = await loadFixture(setup);

      const maxU256 = (1n << 256n) - 1n;
      await allow(matches([eq(Encoding.Dynamic, enc(["bytes"], ["0x00"]))]));

      // offset = uint256.max
      await expectOverflow(roles, invoke(calldata(word(maxU256))), 0);
      // length = uint256.max
      await expectOverflow(
        roles,
        invoke(calldata(word(0x20), word(maxU256))),
        1,
      );
      // length = uint256.max - 30 (would overflow `length + 31` if unchecked)
      await expectOverflow(
        roles,
        invoke(calldata(word(0x20), word(maxU256 - 30n))),
        1,
      );
    });
  });

  // ───────────────────────────────────────────────────────────────
  // 3. Exact ABI regions (`sliceEncoded`): back-to-back tails,
  //    in order, zero padding; contrast with `children`/`elements`
  // ───────────────────────────────────────────────────────────────
  describe("Exact ABI regions (sliceEncoded)", () => {
    const tupleEqCondition = () =>
      matches([
        eq(Encoding.Tuple, enc(["(bytes,bytes)"], [["0xaa", "0xbb"]]), [
          pass(Encoding.Dynamic),
          pass(Encoding.Dynamic),
        ]),
      ]);

    const tail = (hex: string) => word(hex.length / 2) + hex.padEnd(64, "0");

    it("rejects gap between tails in Tuple (EqualTo) and Array (EqualTo & Pluck)", async () => {
      const { roles, allow, invoke } = await loadFixture(setup);

      // Tuple (bytes, bytes): a at 0x40..0x80, 32-byte gap at 0x80..0xa0, b at 0xa0
      const gappedTuple = calldata(
        word(0x20), // ptr(tuple)
        word(0x40), // ptr(a)
        word(0xa0), // ptr(b) — skipped 0x20 gap!
        tail("aa"),
        word(0), // gap
        tail("bb"),
      );

      await allow(tupleEqCondition());
      await expectOverflow(roles, invoke(gappedTuple), 1);

      // Array bytes[]: elem0 at 0x40..0x80, gap at 0x80..0xa0, elem1 at 0xa0
      const gappedArray = calldata(
        word(0x20), // ptr(array)
        word(2), // count
        word(0x40), // ptr(arr[0])
        word(0xa0), // ptr(arr[1]) — gap!
        tail("aa"),
        word(0),
        tail("bb"),
      );
      await allow(
        matches([
          eq(Encoding.Array, enc(["bytes[]"], [["0xaa", "0xbb"]]), [
            pass(Encoding.Dynamic),
          ]),
        ]),
      );
      await expectOverflow(roles, invoke(gappedArray), 1);

      await allow(
        matches([
          {
            paramType: Encoding.Array,
            operator: Operator.Pluck,
            compValue: "0x00",
            children: [pass(Encoding.Dynamic)],
          },
        ]),
      );
      await expectOverflow(roles, invoke(gappedArray), 1);
    });

    it("rejects shared tails in Tuple and Array", async () => {
      const { roles, allow, invoke } = await loadFixture(setup);

      // Tuple (bytes, bytes): both offsets point to 0x40
      const sharedTuple = calldata(
        word(0x20),
        word(0x40),
        word(0x40), // shared!
        tail("aa"),
      );
      await allow(
        matches([
          eq(Encoding.Tuple, enc(["(bytes,bytes)"], [["0xaa", "0xaa"]]), [
            pass(Encoding.Dynamic),
            pass(Encoding.Dynamic),
          ]),
        ]),
      );
      await expectOverflow(roles, invoke(sharedTuple), 1);

      // Array bytes[]: both elements point to 0x40
      const sharedArray = calldata(
        word(0x20),
        word(2),
        word(0x40),
        word(0x40), // shared!
        tail("aa"),
      );
      await allow(
        matches([
          eq(Encoding.Array, enc(["bytes[]"], [["0xaa", "0xaa"]]), [
            pass(Encoding.Dynamic),
          ]),
        ]),
      );
      await expectOverflow(roles, invoke(sharedArray), 1);
    });

    it("rejects out-of-order tails in Tuple and Array", async () => {
      const { roles, allow, invoke } = await loadFixture(setup);

      // Tuple (bytes, bytes): b sits at 0x40, a sits at 0x80
      const reorderedTuple = calldata(
        word(0x20),
        word(0x80), // a second
        word(0x40), // b first
        tail("bb"),
        tail("aa"),
      );
      await allow(tupleEqCondition());
      await expectOverflow(roles, invoke(reorderedTuple), 1);

      // Array bytes[]: arr[1] at 0x40, arr[0] at 0x80
      const reorderedArray = calldata(
        word(0x20),
        word(2),
        word(0x80),
        word(0x40),
        tail("bb"),
        tail("aa"),
      );
      await allow(
        matches([
          eq(Encoding.Array, enc(["bytes[]"], [["0xaa", "0xbb"]]), [
            pass(Encoding.Dynamic),
          ]),
        ]),
      );
      await expectOverflow(roles, invoke(reorderedArray), 1);
    });

    it("rejects offset pointing short of the head end in Tuple", async () => {
      const { roles, allow, invoke } = await loadFixture(setup);

      // Tuple (bytes, uint256): head is 0x40 bytes, but ptr(bytes) = 0x20 (lands on uint256!)
      await allow(
        matches([
          eq(Encoding.Tuple, enc(["(bytes,uint256)"], [["0x", 0]]), [
            pass(Encoding.Dynamic),
            pass(Encoding.Static),
          ]),
        ]),
      );
      const data = calldata(word(0x20), word(0x20), word(0));
      await expectOverflow(roles, invoke(data), 1);
    });

    it("rejects truncated dynamic Tuple head in sliceEncoded", async () => {
      const { roles, allow, invoke } = await loadFixture(setup);

      // Tuple (uint256, bytes) needs a 64-byte head, but only 32 bytes sit at its offset
      await allow(
        matches([
          eq(Encoding.Tuple, enc(["(uint256,bytes)"], [[1, "0x"]]), [
            pass(Encoding.Static),
            pass(Encoding.Dynamic),
          ]),
        ]),
      );
      await expectOverflow(roles, invoke(calldata(word(0x20), word(1))), 1);
    });

    it("accepts zero padding and rejects dirty padding on a Dynamic value", async () => {
      const { roles, allow, invoke } = await loadFixture(setup);

      await allow(
        matches([eq(Encoding.Dynamic, enc(["bytes"], ["0xaabbccddee"]))]),
      );

      const clean = calldata(
        word(0x20),
        word(5),
        "aabbccddee" + "00".repeat(27),
      );
      await invoke(clean);

      // first padding byte set
      const dirtyFirst = calldata(
        word(0x20),
        word(5),
        "aabbccddee01" + "00".repeat(26),
      );
      await expectOverflow(roles, invoke(dirtyFirst), 1);

      // last padding byte set
      const dirtyLast = calldata(
        word(0x20),
        word(5),
        "aabbccddee" + "00".repeat(26) + "01",
      );
      await expectOverflow(roles, invoke(dirtyLast), 1);
    });

    it("does not treat a full last word as padding", async () => {
      const { allow, invoke } = await loadFixture(setup);

      const fullWord = "ff".repeat(32);
      await allow(
        matches([eq(Encoding.Dynamic, enc(["bytes"], ["0x" + fullWord]))]),
      );

      await invoke(calldata(word(0x20), word(32), fullWord));
    });

    it("accepts empty bytes, which has no payload word at all", async () => {
      const { allow, invoke } = await loadFixture(setup);

      await allow(matches([eq(Encoding.Dynamic, enc(["bytes"], ["0x"]))]));

      await invoke(calldata(word(0x20), word(0)));
    });

    it("rejects dirty padding on a Dynamic field inside a Tuple", async () => {
      const { roles, allow, invoke } = await loadFixture(setup);

      await allow(
        matches([
          eq(Encoding.Tuple, enc(["(uint256,bytes)"], [[1, "0xaa"]]), [
            pass(Encoding.Static),
            pass(Encoding.Dynamic),
          ]),
        ]),
      );

      const clean = calldata(
        word(0x20), // ptr(tuple)
        word(1), // tuple.0
        word(0x40), // ptr(tuple.1)
        word(1), // tuple.1 length
        "aa" + "00".repeat(31),
      );
      await invoke(clean);

      const dirty = calldata(
        word(0x20),
        word(1),
        word(0x40),
        word(1),
        "aa" + "00".repeat(30) + "01",
      );
      await expectOverflow(roles, invoke(dirty), 1);
    });

    it("rejects dirty padding on a Dynamic element inside an Array", async () => {
      const { roles, allow, invoke } = await loadFixture(setup);

      await allow(
        matches([
          eq(Encoding.Array, enc(["bytes[]"], [["0xaa"]]), [
            pass(Encoding.Dynamic),
          ]),
        ]),
      );

      const clean = calldata(
        word(0x20), // ptr(array)
        word(1), // count
        word(0x20), // ptr(arr[0])
        word(1), // arr[0] length
        "aa" + "00".repeat(31),
      );
      await invoke(clean);

      const dirty = calldata(
        word(0x20),
        word(1),
        word(0x20),
        word(1),
        "aa" + "00".repeat(30) + "01",
      );
      await expectOverflow(roles, invoke(dirty), 1);
    });

    it("rejects dirty padding on a nested AbiEncoded field inside a Tuple", async () => {
      const { roles, allow, invoke } = await loadFixture(setup);

      // inner payload: 4-byte selector + one uint256 = 36 bytes, so 28 bytes of padding
      const inner = "0xaabbccdd" + word(7);
      await allow(
        matches([
          eq(Encoding.Tuple, enc(["(uint256,bytes)"], [[1, inner]]), [
            pass(Encoding.Static),
            pass(Encoding.AbiEncoded),
          ]),
        ]),
      );

      const clean = calldata(
        word(0x20), // ptr(tuple)
        word(1), // tuple.0
        word(0x40), // ptr(tuple.1)
        word(36), // tuple.1 length
        "aabbccdd" + word(7) + "00".repeat(28),
      );
      await invoke(clean);

      const dirty = calldata(
        word(0x20),
        word(1),
        word(0x40),
        word(36),
        "aabbccdd" + word(7) + "00".repeat(27) + "01",
      );
      await expectOverflow(roles, invoke(dirty), 1);
    });

    it("allows in-bounds shared and out-of-order tails during navigation (Matches / ArrayEvery)", async () => {
      const { allow, invoke } = await loadFixture(setup);

      // Matches on (bytes, bytes) where both point to the same tail at 0x40
      await allow(
        matches([
          {
            paramType: Encoding.Tuple,
            operator: Operator.Matches,
            children: [
              eq(Encoding.Dynamic, enc(["bytes"], ["0xaa"])),
              eq(Encoding.Dynamic, enc(["bytes"], ["0xaa"])),
            ],
          },
        ]),
      );
      const sharedTuple = calldata(
        word(0x20),
        word(0x40),
        word(0x40),
        tail("aa"),
      );
      await invoke(sharedTuple);

      // ArrayEvery on bytes[] with out-of-order tails
      await allow(
        matches([
          {
            paramType: Encoding.Array,
            operator: Operator.ArrayEvery,
            children: [
              {
                paramType: Encoding.None,
                operator: Operator.Or,
                children: [
                  eq(Encoding.Dynamic, enc(["bytes"], ["0xaa"])),
                  eq(Encoding.Dynamic, enc(["bytes"], ["0xbb"])),
                ],
              },
            ],
          },
        ]),
      );
      const reorderedArray = calldata(
        word(0x20),
        word(2),
        word(0x80),
        word(0x40),
        tail("bb"),
        tail("aa"),
      );
      await invoke(reorderedArray);
    });

    it("ignores dirty padding under Pass, where the value is never read", async () => {
      const { allow, invoke } = await loadFixture(setup);

      await allow(matches([pass(Encoding.Dynamic)]));

      const dirty = calldata(
        word(0x20),
        word(5),
        "aabbccddee" + "00".repeat(26) + "01",
      );
      await invoke(dirty);
    });
  });

  // ───────────────────────────────────────────────────────────────
  // 4. Fallthrough on CalldataOverflow (no reverts break Or/Some)
  // ───────────────────────────────────────────────────────────────
  describe("Fallthrough on CalldataOverflow", () => {
    it("falls through Or when the first branch hits CalldataOverflow (huge count, overflow offset, shared tail, dirty padding)", async () => {
      const { allow, invoke } = await loadFixture(setup);

      // Branch 0 reads param0 as bytes[] through sliceEncoded;
      // Branch 1 passes param0 as a plain static word.
      await allow({
        paramType: Encoding.None,
        operator: Operator.Or,
        children: [
          matches([
            eq(Encoding.Array, enc(["bytes[]"], [["0xaa"]]), [
              pass(Encoding.Dynamic),
            ]),
          ]),
          matches([pass(Encoding.Static)]),
        ],
      });

      const maxU256 = (1n << 256n) - 1n;
      // Huge array count in branch 0 -> CalldataOverflow -> branch 1 passes
      await invoke(calldata(word(0x20), word(maxU256)));
      // Overflow offset in branch 0 -> CalldataOverflow -> branch 1 passes
      await invoke(calldata(word(maxU256)));
      // Shared tail in branch 0 -> CalldataOverflow -> branch 1 passes
      await invoke(
        calldata(
          word(0x20),
          word(2),
          word(0x40),
          word(0x40),
          word(1),
          "aa" + "00".repeat(31),
        ),
      );
      // Dirty padding in branch 0 -> CalldataOverflow -> branch 1 passes
      await invoke(
        calldata(
          word(0x20),
          word(1),
          word(0x20),
          word(1),
          "aa" + "00".repeat(30) + "01",
        ),
      );
    });

    it("falls through ArraySome when an earlier element overflows and a later element passes", async () => {
      const { allow, invoke } = await loadFixture(setup);

      await allow(
        matches([
          {
            paramType: Encoding.Array,
            operator: Operator.ArraySome,
            children: [eq(Encoding.Dynamic, enc(["bytes"], ["0xaa"]))],
          },
        ]),
      );

      // arr[0] has dirty padding (CalldataOverflow), arr[1] is clean "0xaa"
      const data = calldata(
        word(0x20), // ptr(arr)
        word(2), // count = 2
        word(0x40), // ptr(arr[0])
        word(0x80), // ptr(arr[1])
        word(1),
        "aa" + "00".repeat(30) + "01", // dirty padding -> CalldataOverflow
        word(1),
        "aa" + "00".repeat(31), // valid -> passes!
      );
      await invoke(data);
    });
  });

  // ───────────────────────────────────────────────────────────────
  // 5. Evaluator edge cases
  // ───────────────────────────────────────────────────────────────
  describe("Evaluator edge cases", () => {
    it("enforces inlineSize bounds on raw-packed root Static nodes", async () => {
      const { roles, allowRaw, invoke } = await loadFixture(setup);

      const packed = packRaw([
        {
          encoding: Encoding.Static,
          operator: Operator.EqualTo,
          inlineSize: 32,
          compValue: enc(["uint256"], [0]),
        },
      ]);
      await allowRaw(packed);

      // Empty calldata must fail closed, not pass EqualTo(0)
      await expectOverflow(roles, invoke("0x"), 0, 0);
      // 32 zero bytes + trailing bytes reads exactly the 32-byte slice
      await invoke(("0x" + "00".repeat(32) + "ff".repeat(32)) as Hex);
    });

    it("fails closed on raw-packed malformed Static node with inlineSize = 0", async () => {
      const { roles, allowRaw, invoke } = await loadFixture(setup);

      // Malformed Static with inlineSize = 0 must return CalldataOverflow,
      // NOT succeed with an empty slice (which would hash/read as word 0).
      const packed = packRaw([
        {
          encoding: Encoding.Static,
          operator: Operator.EqualTo,
          inlineSize: 0,
          compValue: enc(["uint256"], [0]),
        },
      ]);
      await allowRaw(packed);

      await expectOverflow(roles, invoke(calldata(word(42))), 0, 0);
    });

    it("rejects EqualTo when raw-packed compValue.length does not match operand length", async () => {
      const { roles, allowRaw, invoke } = await loadFixture(setup);

      // 1. Static 32-byte operand compared against a 16-byte compValue
      const shortComp = packRaw([
        {
          encoding: Encoding.Static,
          operator: Operator.EqualTo,
          inlineSize: 32,
          compValue: "0x" + "00".repeat(16),
        },
      ]);
      await allowRaw(shortComp);
      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke(("0x" + word(0)) as Hex),
        roles,
        "ConditionViolation",
        [ConditionViolationStatus.ParameterNotAllowed, 0n, 0n],
      );

      // 2. Dynamic operand (> 32 bytes) compared against a 32-byte compValue
      const shortDynamicComp = packRaw([
        {
          encoding: Encoding.AbiEncoded,
          operator: Operator.Matches,
          childCount: 1,
          compValue: "0x0004",
        },
        {
          encoding: Encoding.Dynamic,
          operator: Operator.EqualTo,
          compValue: "0x" + word(0),
        },
      ]);
      await allowRaw(shortDynamicComp);
      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke(calldata(word(0x20), word(1), "aa" + "00".repeat(31))),
        roles,
        "ConditionViolation",
        [ConditionViolationStatus.ParameterNotAllowed, 1n, 36n],
      );
    });

    it("bounds-checks Custom operands via sliceEncoded and passes size = 0 for EtherValue", async () => {
      const { roles, allow, invoke } = await loadFixture(setup);

      const custom = await viem.deployContract("TestCustomChecker");
      const customAddr = custom.address;

      // 1. Dynamic Tuple with gap must fail CalldataOverflow before reaching adapter
      await allow(
        matches([
          {
            paramType: Encoding.Tuple,
            operator: Operator.Custom,
            compValue: customAddr,
            children: [pass(Encoding.Dynamic), pass(Encoding.Dynamic)],
          },
        ]),
      );
      const gappedTuple = calldata(
        word(0x20),
        word(0x40),
        word(0xa0), // gap!
        word(1),
        "aa" + "00".repeat(31),
        word(0),
        word(1),
        "bb" + "00".repeat(31),
      );
      await expectOverflow(roles, invoke(gappedTuple), 1);

      // 2. EtherValue Custom: passes length = 0 cleanly even on empty calldata "0x"
      //    (TestCustomChecker reads 0 bytes -> param = 0 <= 100 -> CustomConditionViolation,
      //    proving it was invoked cleanly with size = 0 rather than CalldataOverflow)
      await allow(
        {
          paramType: Encoding.EtherValue,
          operator: Operator.Custom,
          compValue: customAddr,
        },
        ExecutionOptions.Send,
      );
      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke("0x", 123),
        roles,
        "ConditionViolation",
        [ConditionViolationStatus.CustomConditionViolation, 0n, 0n],
      );
    });

    it("reverts with UnsupportedOperator on a raw-packed placeholder operator", async () => {
      const { evaluator, allowRaw, invoke } = await loadFixture(setup);

      await allowRaw(
        packRaw([
          { encoding: Encoding.None, operator: Operator._Placeholder03 },
        ]),
      );
      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke(calldata(word(0))),
        evaluator,
        "UnsupportedOperator",
        [0n],
      );

      await allowRaw(
        packRaw([
          { encoding: Encoding.None, operator: Operator._Placeholder24 },
        ]),
      );
      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke(calldata(word(0))),
        evaluator,
        "UnsupportedOperator",
        [0n],
      );

      await allowRaw(
        packRaw([
          { encoding: Encoding.None, operator: Operator._Placeholder31 },
        ]),
      );
      await viem.assertions.revertWithCustomErrorWithArgs(
        invoke(calldata(word(0))),
        evaluator,
        "UnsupportedOperator",
        [0n],
      );
    });

    it("rejects raw-packed root Dynamic with fewer than 32 bytes of calldata", async () => {
      const { roles, allowRaw, invoke } = await loadFixture(setup);

      await allowRaw(
        packRaw([
          {
            encoding: Encoding.Dynamic,
            operator: Operator.EqualTo,
            compValue: enc(["bytes"], ["0x"]),
          },
        ]),
      );
      await expectOverflow(
        roles,
        invoke(("0x" + "00".repeat(16)) as Hex),
        0,
        0,
      );
    });

    it("delegates sliceEncoded through Encoding.None to inlined children and fails when exhausted", async () => {
      const { roles, allowRaw, invoke } = await loadFixture(setup);

      // Raw-packed: Matches [ EqualTo(Tuple, inlineSize=0, [None(inlineSize=0, [Static(64)])]) ]
      const expected = "0x" + word(0x20) + word(1) + word(2);
      await allowRaw(
        packRaw([
          {
            encoding: Encoding.AbiEncoded,
            operator: Operator.Matches,
            childCount: 1,
            compValue: "0x0004",
          },
          {
            encoding: Encoding.Tuple,
            operator: Operator.EqualTo,
            childCount: 1,
            inlineSize: 0,
            compValue: expected,
          },
          {
            encoding: Encoding.None,
            operator: Operator.Pass,
            childCount: 1,
            inlineSize: 0,
          },
          {
            encoding: Encoding.Static,
            operator: Operator.Pass,
            inlineSize: 64,
          },
        ]),
      );

      // Full 64-byte tail at offset 0x20 succeeds through None -> Static(64)
      await invoke(calldata(word(0x20), word(0x20), word(1), word(2)));

      // Only 32 bytes at offset 0x20 -> Static(64) overflows -> None returns ok = false
      await expectOverflow(
        roles,
        invoke(calldata(word(0x20), word(0x20), word(1))),
        1,
      );
    });
  });
});
