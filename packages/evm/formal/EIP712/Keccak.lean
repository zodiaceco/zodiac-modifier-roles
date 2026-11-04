import DecoderFaithfulness.Bytes

/-!
# keccak256 (executable)

Only the differential-testing driver uses this, as the `K` of the
transcription and the spec. No theorem depends on it. Keccak-f[1600] with
rate 136 bytes and the original Keccak padding (`0x01 … 0x80`), as in
Ethereum. The driver checks it against known digests.
-/

namespace EIP712.Keccak
open DecoderFaithfulness

def RC : Array UInt64 := #[
  0x0000000000000001, 0x0000000000008082, 0x800000000000808A, 0x8000000080008000,
  0x000000000000808B, 0x0000000080000001, 0x8000000080008081, 0x8000000000008009,
  0x000000000000008A, 0x0000000000000088, 0x0000000080008009, 0x000000008000000A,
  0x000000008000808B, 0x800000000000008B, 0x8000000000008089, 0x8000000000008003,
  0x8000000000008002, 0x8000000000000080, 0x000000000000800A, 0x800000008000000A,
  0x8000000080008081, 0x8000000000008080, 0x0000000080000001, 0x8000000080008008]

/-- Rotation offsets `r[x + 5y]`. -/
def ROT : Array UInt64 := #[
  0, 1, 62, 28, 27,
  36, 44, 6, 55, 20,
  3, 10, 43, 25, 39,
  41, 45, 15, 21, 8,
  18, 2, 61, 56, 14]

def rotl (x n : UInt64) : UInt64 := if n = 0 then x else (x <<< n) ||| (x >>> (64 - n))

def round (a : Array UInt64) (rc : UInt64) : Array UInt64 := Id.run do
  -- θ
  let c := (List.range 5).toArray.map fun x =>
    a[x]! ^^^ a[x + 5]! ^^^ a[x + 10]! ^^^ a[x + 15]! ^^^ a[x + 20]!
  let d := (List.range 5).toArray.map fun x => c[(x + 4) % 5]! ^^^ rotl c[(x + 1) % 5]! 1
  let a := (List.range 25).toArray.map fun i => a[i]! ^^^ d[i % 5]!
  -- ρ and π: B[y, 2x + 3y] = rot(A[x, y], r[x, y])
  let mut b : Array UInt64 := Array.replicate 25 0
  for x in [0:5] do
    for y in [0:5] do
      b := b.set! (y + 5 * ((2 * x + 3 * y) % 5)) (rotl a[x + 5 * y]! ROT[x + 5 * y]!)
  -- χ
  let a := (List.range 25).toArray.map fun i =>
    let x := i % 5
    let y := i / 5
    b[i]! ^^^ ((~~~ b[(x + 1) % 5 + 5 * y]!) &&& b[(x + 2) % 5 + 5 * y]!)
  -- ι
  return a.set! 0 (a[0]! ^^^ rc)

def keccakF (a : Array UInt64) : Array UInt64 := RC.foldl round a

def lane (bs : Array UInt8) (i : Nat) : UInt64 :=
  (List.range 8).foldl (fun acc k => acc ||| ((bs[i * 8 + k]!).toUInt64 <<< (8 * k).toUInt64)) 0

def keccak256Raw (input : Array UInt8) : Array UInt8 := Id.run do
  let rate := 136
  let padLen := rate - input.size % rate
  let pad := (Array.replicate padLen (0 : UInt8)).set! 0 0x01
  let pad := pad.set! (padLen - 1) (pad[padLen - 1]! ||| 0x80)
  let msg := input ++ pad
  let mut st : Array UInt64 := Array.replicate 25 0
  for blk in [0:msg.size / rate] do
    let chunk := msg.extract (blk * rate) (blk * rate + rate)
    for i in [0:17] do
      st := st.set! i (st[i]! ^^^ lane chunk i)
    st := keccakF st
  let mut out : Array UInt8 := #[]
  for i in [0:4] do
    for k in [0:8] do
      out := out.push ((st[i]! >>> (8 * k).toUInt64).toUInt8)
  return out

def keccak256 (bs : Bytes) : Bytes :=
  (keccak256Raw (bs.map fun b => b.val.toUInt8).toArray).toList.map fun b =>
    ⟨b.toNat % 256, Nat.mod_lt _ (by decide)⟩

end EIP712.Keccak
