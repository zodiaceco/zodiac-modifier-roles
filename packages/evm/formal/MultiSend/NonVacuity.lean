import MultiSend.Agree

/-!
# Non-vacuity of `unwrap_exec`

A concrete `multiSend(bytes)` calldata with a two-entry batch (a call with
4 bytes of calldata, then a delegatecall with none) that
`MultiSendUnwrapper.unwrap` accepts. So the hypothesis `h` of `unwrap_parse`
/ `unwrap_exec` holds on a non-trivial input, and the conclusion of
`unwrap_exec` is instantiated on it. Checked by the kernel (`decide`), no
`native_decide`.
-/

set_option maxRecDepth 100000

namespace MultiSend.NonVacuity
open DecoderFaithfulness DecoderFaithfulness.Roles MultiSend

def b (n : Nat) : Byte := ⟨n % 256, Nat.mod_lt _ (by decide +kernel)⟩

/-- `encodePacked(uint8 op, address to, uint256 value, uint256 len, bytes d)`. -/
def entry (op to value : Nat) (d : Bytes) : Bytes :=
  [b op] ++ natBE 20 to ++ word value ++ word d.length ++ d

def batch : Bytes :=
  entry 0 0xAAAA 7 [b 0xde, b 0xad, b 0xbe, b 0xef] ++ entry 1 0xBBBB 0 []

/-- The calldata: selector, offset `0x20`, length, batch, zero padding. -/
def data : Bytes :=
  selMultiSend ++ word 32 ++ word batch.length ++ batch ++
    zeros (ceil32 batch.length - batch.length)

def us : List Unwrapped :=
  [⟨0, 0xAAAA, 7, 68 + 85, 4⟩, ⟨1, 0xBBBB, 0, 68 + 85 + 4 + 85, 0⟩]

theorem batch_len : batch.length = 174 := by decide +kernel

theorem unwrap_ok : unwrap data 0 1 = some us := by decide +kernel

/-- `unwrap_exec` on this calldata: MultiSend executes the two entries. -/
example (junk : Bytes) :
    let tx := (data.drop 68).take (load data 36)
    let mem := word tx.length ++ tx ++ junk
    execLoop mem (mload mem 0) (us.length + 1) 32 = some (us.map (Unwrapped.view data)) :=
  unwrap_exec data junk 0 1 us unwrap_ok (by decide +kernel)

/-- The entries Roles checks are the intended ones (not degenerate). -/
example : us.map (Unwrapped.view data) =
    [⟨0, 0xAAAA, 7, [b 0xde, b 0xad, b 0xbe, b 0xef]⟩, ⟨1, 0xBBBB, 0, []⟩] := by decide +kernel

/-- A mutated batch (operation `2`) is rejected. -/
example : unwrap (data.set 68 (b 2)) 0 1 = none := by decide +kernel

end MultiSend.NonVacuity
