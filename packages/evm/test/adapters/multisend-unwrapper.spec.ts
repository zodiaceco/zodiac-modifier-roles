import assert from "node:assert/strict";
import { after, describe, it } from "node:test";
import { network } from "hardhat";
import { encodeFunctionData, encodePacked, getAddress, parseAbi } from "viem";
import type { Hex } from "viem";

import { encodeMultisendPayload, type MetaTransaction } from "../utils.js";

const connection = await network.create();
const { viem, networkHelpers } = connection;
const { loadFixture } = networkHelpers;

const AddressOne = "0x0000000000000000000000000000000000000001";

enum Operation {
  Call = 0,
  DelegateCall = 1,
}

const testAbi = parseAbi([
  "function simple(uint256)",
  "function staticDynamicDynamic32(address, bytes, uint32[])",
]);

describe("MultiSendUnwrapper", () => {
  after(async () => {
    await connection.close();
  });

  async function setup() {
    const multisend = await viem.deployContract("MultiSend");
    const unwrapper = await viem.deployContract("MultiSendUnwrapper");

    return {
      multisend,
      unwrapper,
    };
  }

  it("reverts if wrong selector used", async () => {
    const { unwrapper, multisend } = await loadFixture(setup);

    const simpleCalldata = encodeFunctionData({
      abi: testAbi,
      functionName: "simple",
      args: [1n],
    });

    const data = encodeFunctionData({
      abi: multisend.abi,
      functionName: "multiSend",
      args: [
        encodeMultisendPayload([
          {
            to: AddressOne,
            value: 0,
            operation: Operation.Call,
            data: simpleCalldata,
          },
        ]),
      ],
    });

    const selectorWrong = "bbccddee";
    const selectorOk = "8d80ff0a";

    await viem.assertions.revertWithCustomError(
      unwrapper.read.unwrap([
        AddressOne,
        0n,
        `${data.slice(0, 2)}${selectorWrong}${data.slice(10)}` as Hex,
        Operation.DelegateCall,
      ]),
      unwrapper,
      "MalformedHeader",
    );

    await unwrapper.read.unwrap([
      AddressOne,
      0n,
      `${data.slice(0, 2)}${selectorOk}${data.slice(10)}` as Hex,
      Operation.DelegateCall,
    ]);
  });

  it("reverts if header offset incorrect", async () => {
    const { unwrapper, multisend } = await loadFixture(setup);

    const simpleCalldata = encodeFunctionData({
      abi: testAbi,
      functionName: "simple",
      args: [1n],
    });

    const data = encodeFunctionData({
      abi: multisend.abi,
      functionName: "multiSend",
      args: [
        encodeMultisendPayload([
          {
            to: AddressOne,
            value: 0,
            operation: Operation.DelegateCall,
            data: simpleCalldata,
          },
        ]),
      ],
    });

    const offsetOk =
      "0000000000000000000000000000000000000000000000000000000000000020";
    const offsetWrong =
      "f000000000000000000000000000000000000000000000000000000000000020";

    await viem.assertions.revertWithCustomError(
      unwrapper.read.unwrap([
        AddressOne,
        0n,
        `${data.slice(0, 10)}${offsetWrong}${data.slice(74)}` as Hex,
        Operation.DelegateCall,
      ]),
      unwrapper,
      "MalformedHeader",
    );

    await unwrapper.read.unwrap([
      AddressOne,
      0n,
      `${data.slice(0, 10)}${offsetOk}${data.slice(74)}` as Hex,
      Operation.DelegateCall,
    ]);
  });

  it("reverts if calldata length incorrect", async () => {
    const { unwrapper, multisend } = await loadFixture(setup);

    const simpleCalldata = encodeFunctionData({
      abi: testAbi,
      functionName: "simple",
      args: [1n],
    });

    const data = encodeFunctionData({
      abi: multisend.abi,
      functionName: "multiSend",
      args: [
        encodeMultisendPayload([
          {
            to: AddressOne,
            value: 0,
            operation: Operation.DelegateCall,
            data: simpleCalldata,
          },
        ]),
      ],
    });

    const lengthWrong =
      "0000000000000000000000000000000000000000000000000000000000000000";

    await viem.assertions.revertWithCustomError(
      unwrapper.read.unwrap([
        AddressOne,
        0n,
        `${data.slice(0, 74)}${lengthWrong}${data.slice(140)}` as Hex,
        Operation.DelegateCall,
      ]),
      unwrapper,
      "MalformedHeader",
    );

    await unwrapper.read.unwrap([AddressOne, 0n, data, Operation.DelegateCall]);
  });

  it("reverts if value not zero", async () => {
    const { unwrapper, multisend } = await loadFixture(setup);

    const txData = encodeFunctionData({
      abi: testAbi,
      functionName: "simple",
      args: [1n],
    });

    const data = encodeFunctionData({
      abi: multisend.abi,
      functionName: "multiSend",
      args: [
        encodeMultisendPayload([
          {
            to: "0xaaff330000000000000000000aa0000ff0000000",
            value: 999444555,
            operation: Operation.Call,
            data: txData,
          },
        ]),
      ],
    });

    await viem.assertions.revertWithCustomError(
      unwrapper.read.unwrap([AddressOne, 1n, data, Operation.DelegateCall]),
      unwrapper,
      "UnsupportedMode",
    );
    await unwrapper.read.unwrap([AddressOne, 0n, data, Operation.DelegateCall]);
  });

  it("reverts if operation not delegate call", async () => {
    const { unwrapper, multisend } = await loadFixture(setup);

    const txData = encodeFunctionData({
      abi: testAbi,
      functionName: "simple",
      args: [1n],
    });

    const data = encodeFunctionData({
      abi: multisend.abi,
      functionName: "multiSend",
      args: [
        encodeMultisendPayload([
          {
            to: "0xaaff330000000000000000000aa0000ff0000000",
            value: 999444555,
            operation: Operation.Call,
            data: txData,
          },
        ]),
      ],
    });

    await viem.assertions.revertWithCustomError(
      unwrapper.read.unwrap([AddressOne, 0n, data, Operation.Call]),
      unwrapper,
      "UnsupportedMode",
    );
    await unwrapper.read.unwrap([AddressOne, 0n, data, Operation.DelegateCall]);
  });

  it("reverts if no transaction encoded", async () => {
    const { unwrapper, multisend } = await loadFixture(setup);

    const data = encodeFunctionData({
      abi: multisend.abi,
      functionName: "multiSend",
      args: ["0x"],
    });

    await viem.assertions.revertWithCustomError(
      unwrapper.read.unwrap([AddressOne, 0n, data, Operation.DelegateCall]),
      unwrapper,
      "MalformedBody",
    );
  });

  it("reverts if single transaction length wrong", async () => {
    const { unwrapper, multisend } = await loadFixture(setup);

    const simpleCalldata = encodeFunctionData({
      abi: testAbi,
      functionName: "simple",
      args: [1n],
    });

    const data = encodeFunctionData({
      abi: multisend.abi,
      functionName: "multiSend",
      args: [
        encodeMultisendWrongLength([
          {
            to: AddressOne,
            value: 0,
            operation: Operation.DelegateCall,
            data: simpleCalldata,
          },
        ]),
      ],
    });

    await viem.assertions.revertWithCustomError(
      unwrapper.read.unwrap([AddressOne, 0n, data, Operation.DelegateCall]),
      unwrapper,
      "MalformedBody",
    );
  });

  it("unwraps a single transaction", async () => {
    const { unwrapper, multisend } = await loadFixture(setup);

    const txData = encodeFunctionData({
      abi: testAbi,
      functionName: "simple",
      args: [1n],
    });

    const data = encodeFunctionData({
      abi: multisend.abi,
      functionName: "multiSend",
      args: [
        encodeMultisendPayload([
          {
            to: "0xaaff330000000000000000000aa0000ff0000000",
            value: 999444555,
            operation: Operation.DelegateCall,
            data: txData,
          },
        ]),
      ],
    });

    const result = await unwrapper.read.unwrap([
      AddressOne,
      0n,
      data,
      Operation.DelegateCall,
    ]);

    assert.equal(result.length, 1);
    assert.equal(
      getAddress(result[0].to),
      getAddress("0xaaff330000000000000000000aa0000ff0000000"),
    );
    assert.equal(result[0].value, 999444555n);

    const { left, right } = location(result[0]);
    assert.equal(data.slice(2).slice(left, right), txData.slice(2));
  });

  it("unwraps multiple transactions", async () => {
    const { unwrapper, multisend } = await loadFixture(setup);

    const txData1 = encodeFunctionData({
      abi: testAbi,
      functionName: "simple",
      args: [1n],
    });
    const txData2 = encodeFunctionData({
      abi: testAbi,
      functionName: "staticDynamicDynamic32",
      args: [AddressOne, "0xaabbcc", [1, 2, 3]],
    });

    const data = encodeFunctionData({
      abi: multisend.abi,
      functionName: "multiSend",
      args: [
        encodeMultisendPayload([
          {
            to: "0x0000000000000000000000000000000000000002",
            value: 999444555,
            operation: Operation.DelegateCall,
            data: txData1,
          },
          {
            to: "0x0000000000000000000000000000000000000003",
            value: 7654,
            operation: Operation.Call,
            data: txData2,
          },
        ]),
      ],
    });

    const result = await unwrapper.read.unwrap([
      AddressOne,
      0n,
      data,
      Operation.DelegateCall,
    ]);

    assert.equal(result.length, 2);
    assert.equal(
      getAddress(result[0].to),
      getAddress("0x0000000000000000000000000000000000000002"),
    );
    assert.equal(result[0].value, 999444555n);
    assert.equal(result[0].operation, Operation.DelegateCall);

    assert.equal(
      getAddress(result[1].to),
      getAddress("0x0000000000000000000000000000000000000003"),
    );
    assert.equal(result[1].value, 7654n);
    assert.equal(result[1].operation, Operation.Call);

    let { left, right } = location(result[0]);
    assert.equal(data.slice(2).slice(left, right), txData1.slice(2));
    ({ left, right } = location(result[1]));
    assert.equal(data.slice(2).slice(left, right), txData2.slice(2));
  });

  it("reverts if inner transaction operation incorrect", async () => {
    const { unwrapper, multisend } = await loadFixture(setup);

    const txData = encodeFunctionData({
      abi: testAbi,
      functionName: "simple",
      args: [1n],
    });

    // operation = 2 is invalid
    let data = encodeFunctionData({
      abi: multisend.abi,
      functionName: "multiSend",
      args: [
        encodeMultisendPayload([
          {
            to: "0xaaff330000000000000000000aa0000ff0000000",
            value: 999444555,
            operation: 2,
            data: txData,
          },
        ]),
      ],
    });
    await viem.assertions.revertWithCustomError(
      unwrapper.read.unwrap([AddressOne, 0n, data, Operation.DelegateCall]),
      unwrapper,
      "MalformedBody",
    );

    // operation = 1 (DelegateCall) is valid
    data = encodeFunctionData({
      abi: multisend.abi,
      functionName: "multiSend",
      args: [
        encodeMultisendPayload([
          {
            to: "0xaaff330000000000000000000aa0000ff0000000",
            value: 999444555,
            operation: Operation.DelegateCall,
            data: txData,
          },
        ]),
      ],
    });
    await unwrapper.read.unwrap([AddressOne, 0n, data, Operation.DelegateCall]);
  });
});

const encodeMultisendWrongLength = (txs: MetaTransaction[]): Hex => {
  return ("0x" +
    txs
      .map((tx) =>
        encodePacked(
          ["uint8", "address", "uint256", "uint256", "bytes"],
          [tx.operation, tx.to, BigInt(tx.value), 4000000n, tx.data],
        ).slice(2),
      )
      .join("")) as Hex;
};

function location(result: { dataLocation: bigint; dataSize: bigint }) {
  const offset = Number(result.dataLocation);
  const length = Number(result.dataSize);
  const left = offset * 2;
  const right = (offset + length) * 2;

  return { left, right };
}
