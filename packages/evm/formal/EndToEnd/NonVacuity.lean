import EndToEnd.Hashes
import EndToEnd.Pins
import EndToEnd.Library
import EndToEnd.Routes
import EndToEnd.Consume
import EndToEnd.Batch

/-!
# Non-vacuity of the batch theorems

A concrete MultiSend batch of two transactions through a role:

* `0xAAAA`, a call with value 7 and calldata `deadbeef`, under a target-wide
  permission that allows sending, with the condition
  `And[WithinAllowance(ether value, K), Or[And[CallWithinAllowance(K), Empty], Pass]]`:
  it charges 7 to `K`, and the first `Or` branch charges 1 more and then fails;
* `0xBBBB`, a delegatecall with empty calldata, under a target-wide
  permission that allows delegatecall, with `CallWithinAllowance(K)`.

`authorize` lets it through with one entry for `K` that consumed 8 (not 9:
the failed branch's charge is gone). So the hypothesis `h` of
`executed_authorized`, `authorize_persist` and the `Execs` premise of
`executions_limit` hold on a non-trivial batch, with real charges. Checked
by the kernel (`decide +kernel`), no `native_decide`.
-/

set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

namespace EndToEnd.NonVacuity
open DecoderFaithfulness DecoderFaithfulness.Roles Evaluate MultiSend

def b (n : Nat) : Byte := ⟨n % 256, Nat.mod_lt _ (by decide +kernel)⟩

def entry (op to value : Nat) (d : Bytes) : Bytes :=
  [b op] ++ natBE 20 to ++ word value ++ word d.length ++ d

def batch : Bytes :=
  entry 0 0xAAAA 7 [b 0xde, b 0xad, b 0xbe, b 0xef] ++ entry 1 0xBBBB 0 []

def data : Bytes :=
  selMultiSend ++ word 32 ++ word batch.length ++ batch ++
    zeros (ceil32 batch.length - batch.length)

def MS : Nat := 0xCCCC

/-- The allowance key (a 32-byte compValue: amounts are raw). -/
def K : Bytes := word 0x4b

def leaf (op : Operator) (enc : Encoding := .None) (cv : Bytes := []) : Condition :=
  ⟨enc, op, [], false, 0, 0, cv⟩

def condA : Condition :=
  ⟨.None, .And,
    [leaf .WithinAllowance .None K,
     ⟨.None, .Or,
       [⟨.None, .And, [leaf .CallWithinAllowance .None K, leaf .Empty], false, 0, 0, []⟩,
        leaf .Pass], false, 0, 0, []⟩], false, 0, 0, []⟩

def condB : Condition := leaf .CallWithinAllowance .None K

def scA : Nat := 1 * 2 ^ 160 + 1   -- Send allowed
def scB : Nat := 2 * 2 ^ 160 + 2   -- DelegateCall allowed

def p : Perms where
  clearance := fun to => if to = 0xAAAA ∨ to = 0xBBBB then 1 else 0
  scope := fun k => if k = targetKey 0xAAAA then scA else if k = targetKey 0xBBBB then scB else 0
  load := fun sc => if sc = scA then (condA, 0) else (condB, 0)
  unwrapper := fun k => k = fnKey MS (sel selMultiSend)

def cfg : Bytes → Allowance.Config := fun _ => ⟨0, 0, 0⟩
def st : Bytes → Allowance.State := fun _ => ⟨10, 0⟩

def envOf (e : Entry) : Env :=
  { value := e.value
    balance := fun k => (Allowance.accrue (cfg k) (st k) 0).balance
    scale := fun _ _ => (254, 0)
    customCall := fun _ _ _ _ => .inl 254
    ratio := fun _ _ => 254 }

def us : List Unwrapped :=
  [⟨0, 0xAAAA, 7, 68 + 85, 4⟩, ⟨1, 0xBBBB, 0, 68 + 85 + 4 + 85, 0⟩]

theorem unwrap_ok : unwrap data 0 1 = some us := by decide +kernel

theorem view_ok : us.map (Unwrapped.view data) =
    [⟨0, 0xAAAA, 7, [b 0xde, b 0xad, b 0xbe, b 0xef]⟩, ⟨1, 0xBBBB, 0, []⟩] := by decide +kernel

theorem sel_ok : p.unwrapper (fnKey MS (sel data)) = true := by decide +kernel

theorem txA : transaction p (envOf ⟨0, 0xAAAA, 7, [b 0xde, b 0xad, b 0xbe, b 0xef]⟩) []
    ⟨0, 0xAAAA, 7, [b 0xde, b 0xad, b 0xbe, b 0xef]⟩ = some [⟨K, 10, 7⟩] := by
  simp (config := {decide := true}) [transaction, resolve, p, targetKey, scA, scB, optionsOk, run, condA,
    leaf, depth, depthL, evalC, seqLoop, orLoop, allowance, consume, envOf, cfg, st, Allowance.accrue,
    input, inputB, result, Evaluate.ok, violation, sOk, sCalldataNotEmpty, sAllowanceExceeded, revert, K]

theorem txB : transaction p (envOf ⟨1, 0xBBBB, 0, []⟩) [⟨K, 10, 7⟩] ⟨1, 0xBBBB, 0, []⟩ =
    some [⟨K, 10, 8⟩] := by
  simp (config := {decide := true}) [transaction, resolve, p, targetKey, scA, scB, optionsOk, run, condB,
    leaf, depth, depthL, evalC, allowance, consume, envOf, cfg, st, Allowance.accrue,
    result, Evaluate.ok, violation, sOk, sAllowanceExceeded, K]

theorem authorize_ok : authorize p envOf MS 0 data 1 = some [⟨K, 10, 8⟩] := by
  unfold authorize
  simp only [sel_ok, ↓reduceIte, unwrap_ok, Option.bind, view_ok, chain, txA, txB]

/-- `executed_authorized` on it: the avatar executes the two entries. -/
example : ∃ es, chain p envOf [] es = some [⟨K, 10, 8⟩] ∧ (∀ e ∈ es, Permitted p (envOf e) e) ∧
    (if p.unwrapper (fnKey MS (sel data)) then
        let tx := (data.drop 68).take (load data 36)
        let mem := word tx.length ++ tx ++ []
        ∃ fuel, execLoop mem (mload mem 0) fuel 32 = some es
      else es = [⟨1, MS, 0, data⟩]) :=
  executed_authorized authorize_ok (by decide +kernel) []

theorem hcustom : ∀ e cv l sz vals s, (envOf e).customCall cv l sz vals = .inl s → s ≠ sOk := by
  intro e cv l sz vals s h
  simp only [envOf, Sum.inl.injEq] at h
  subst h; decide

/-- `authorize_persist` on it: one `Allowance.tx` for `K` with both
    transactions' charges; the stored balance is 2. -/
example : ∃ log, Steps (fun k => (Allowance.accrue (cfg k) (st k) 0).balance) [] log [⟨K, 10, 8⟩] ∧
    ∀ k, Allowance.tx (cfg k) (st k) 0 (charges log k) =
      .ok (persist (fun k => Allowance.accrue (cfg k) (st k) 0) st [⟨K, 10, 8⟩] k) :=
  authorize_persist cfg st 0 (fun _ => rfl) hcustom authorize_ok

example : (persist (fun k => Allowance.accrue (cfg k) (st k) 0) st [⟨K, 10, 8⟩] K).balance = 2 := by
  decide +kernel

/-- The `Execs` premise of `executions_limit` holds for this execution, and
    the limit then bounds `K`'s charges by its stored balance, 10. -/
example : ∃ log st', Execs cfg st [(0, log)] st' ∧
    Allowance.charged ((([(0, log)] : List (Nat × List (Bytes × Nat)))).flatMap
      fun x => charges x.2 K) ≤ 10 := by
  obtain ⟨log, hl, -⟩ := authorize_persist cfg st 0 (fun _ => rfl) hcustom authorize_ok
  have he : Execs cfg st [(0, log)] _ := .exec hl (.nil _)
  refine ⟨log, _, he, ?_⟩
  have := executions_limit he K 0 (by simp)
  simpa [st, cfg, Allowance.periods] using this

end EndToEnd.NonVacuity

/-!
# Non-vacuity of `route_bytes` and `only_flagged` (signMessage route)

A `signMessage(bytes)` call whose message is the 32-byte digest `D` of a
typed message, under a permission that pins the message to `D`
(`Matches[EqualTo(Dynamic, abi(D))]`). Roles passes it, Solidity's decoder
accepts it, and the stored key makes the Safe accept `D`: every hypothesis
of `only_flagged` (and of `route_bytes`, with `pinsArg` true) holds. `K`
is a toy hash with 32-byte outputs (the theorems hold for every such `K`;
with keccak256 the collision disjunct is the assumption).
-/

namespace EndToEnd.NonVacuitySign
open DecoderFaithfulness DecoderFaithfulness.Roles Evaluate SafeSigning EndToEnd

def b (n : Nat) : Byte := ⟨n % 256, Nat.mod_lt _ (by decide +kernel)⟩

/-- A toy hash: the first 32 bytes, zero-padded. -/
def K (x : Bytes) : Bytes := (x ++ zeros 32).take 32
theorem hK : ∀ x, (K x).length = 32 := by intro x; simp [K]

def ds : Bytes := word 0xd5
def domainSep : Bytes := word 0x1234
def roleTH : Bytes := word 0x5678
def fields : Bytes := word 1
def D : Bytes := typedDigest K domainSep roleTH fields

/-- `signMessage(bytes)`: selector, offset, length, the 32 bytes of `D`. -/
def data : Bytes := [b 0x85, b 0xa5, b 0xaf, b 0xfe] ++ word 32 ++ word 32 ++ D

theorem dec_ok : solDecodeBytes data = some D := by decide +kernel

def pin : Condition := ⟨.Dynamic, .EqualTo, [], false, 0, 0, word 32 ++ D⟩
def root : Condition := ⟨.AbiEncoded, .Matches, [pin], false, 0, 4, []⟩

theorem pins : pinsArg leafBytes 0 3 root = true := by decide +kernel

theorem run_ok (env : Env) : (evalC env data 0 5 0 root [] Slots.empty).status = sOk := by
  simp (config := {decide := true}) [evalC, root, pin, leadingCheck, childrenE, children,
    childrenLoop, seqLoop, input, Roles.size, tailLocation, inputB, cvB, Evaluate.compare,
    result, Evaluate.ok, sOk]

/-- `route_bytes`: the hypotheses hold, and the pinned message is `D`. -/
example (env : Env) : ∃ e, PinUnder 0 root e ∧ pinnedLeaf leafBytes e = true ∧
    D = pinnedBytes e.compValue :=
  route_bytes pins (run_ok env) dec_ok

/-- `only_flagged`: every hypothesis holds (the library stored
    `signMessageKey K ds D`, which makes the Safe accept `D`). -/
example (env : Env) :
    (∃ kind, FlaggedOrExact root 3 roleTH D kind ∧
      ((kind = 0 ∧ ∃ m, solDecodeBytes data = some m ∧ signMessageKey K ds D = signMessageKey K ds m) ∨
       (kind = 1 ∧ ∃ dg, signMessageKey K ds D = signTypedKey K ds dg))) ∨
    CollisionIn K (safeMessageInputs K (safeTypeHash K) ds D ++
      typedDigestInputs K domainSep roleTH fields ++ (LibSign.message (K := K) (ds := ds) dec_ok).inputs) :=
  only_flagged (f := 3) K hK (by decide +kernel) (run_ok env) rfl (by decide +kernel) (by decide +kernel)
    (.message dec_ok) rfl

end EndToEnd.NonVacuitySign
