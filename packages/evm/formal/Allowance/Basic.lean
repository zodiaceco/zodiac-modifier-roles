/-!
# Allowances: transcription of the contract

* `accrue`: `AllowanceConsumer.accrue`, the refill computed when a
  transaction first touches an allowance.
* `charge`: `WithinAllowanceChecker._scaleInput`, what a spend costs in
  balance units: a raw amount (32-byte compValue, `CallWithinAllowance`, a
  custom checker's consumption), or a priced amount with balance decimals,
  input decimals and the adapter's price (`10^18` without an adapter). A
  zero price is a violation, an overflow a revert (checked arithmetic).
* `consumeAll`: `AllowanceConsumer.consume` for each spend, in order.
* `tx`, `run`: a transaction persists the accrued balance minus what it
  consumed and the accrued timestamp (`Settlement._persist`); one that
  fails changes nothing.

Numbers are `Nat`; the word sizes (`uint128` balances, `uint64` times) are
hypotheses of `Allowance.Agree.accrue_bounds`.
-/

namespace Allowance

structure Config where
  refill : Nat
  maxRefill : Nat
  period : Nat

structure State where
  balance : Nat
  timestamp : Nat
deriving DecidableEq, Repr

/-- `AllowanceConsumer.accrue`. -/
def accrue (c : Config) (s : State) (now : Nat) : State :=
  if c.period = 0 then s
  else if now ≤ s.timestamp then s
  else
    let k := (now - s.timestamp) / c.period
    if k = 0 then s
    else
      let ts := s.timestamp + k * c.period
      if c.maxRefill ≤ s.balance then ⟨s.balance, ts⟩
      else
        ⟨if s.balance + c.refill * k < c.maxRefill then s.balance + c.refill * k
          else c.maxRefill, ts⟩

/-- `_ceilDiv`. -/
def ceilDiv (a b : Nat) : Nat := if a = 0 then 0 else (a - 1) / b + 1

def W : Nat := 2 ^ 256

/-- Checked `a * b`: `none` is a panic. -/
def mul? (a b : Nat) : Option Nat := if a * b < W then some (a * b) else none

/-- Checked `10 ** e`. -/
def pow10? (e : Nat) : Option Nat := if 10 ^ e < W then some (10 ^ e) else none

/-- `_scaleInput` after the price is loaded:
    `ceilDiv(v * 10^(P - di) * price, 10^(P - db) * 1e18)` with
    `P = max db di`; `none` is a panic. -/
def scale (v price db di : Nat) : Option Nat := do
  let P := max db di
  let a ← pow10? (P - di)
  let n1 ← mul? v a
  let n ← mul? n1 price
  let b ← pow10? (P - db)
  let d ← mul? b (10 ^ 18)
  pure (ceilDiv n d)

inductive Spend where
  /-- An amount already in balance units. -/
  | raw (amount : Nat)
  /-- `value` with `di` decimals at `price` (18 decimals), into a balance
      with `db` decimals. -/
  | priced (value price db di : Nat)
deriving Repr

inductive Fail where
  | exceeded | deny | panic
deriving DecidableEq, Repr

/-- What a spend costs in balance units. -/
def charge : Spend → Except Fail Nat
  | .raw a => .ok a
  | .priced v p db di =>
    if p = 0 then .error .deny
    else match scale v p db di with
      | some c => .ok c
      | none => .error .panic

/-- `consume` for each spend, in order, on an entry with balance `bal`. -/
def consumeAll (bal : Nat) : Nat → List Spend → Except Fail Nat
  | used, [] => .ok used
  | used, sp :: rest =>
    match charge sp with
    | .error e => .error e
    | .ok a => if a > bal - used then .error .exceeded else consumeAll bal (used + a) rest

/-- A transaction whose authorized path makes these spends from the
    allowance at block time `now`. Without spends it does not touch it. -/
def tx (c : Config) (s : State) (now : Nat) (sps : List Spend) : Except Fail State :=
  if sps = [] then .ok s
  else
    let a := accrue c s now
    match consumeAll a.balance 0 sps with
    | .ok used => .ok ⟨a.balance - used, a.timestamp⟩
    | .error e => .error e

/-- Transactions in order; a failing one reverts. Returns the final state
    and the spends of the transactions that went through. -/
def run (c : Config) : State → List (Nat × List Spend) → State × List Spend
  | s, [] => (s, [])
  | s, (now, sps) :: rest =>
    match tx c s now sps with
    | .ok s' => let r := run c s' rest; (r.1, sps ++ r.2)
    | .error _ => run c s rest

/-- What spends that went through cost. -/
def chargeOf (sp : Spend) : Nat :=
  match charge sp with
  | .ok a => a
  | .error _ => 0

def charged (sps : List Spend) : Nat := (sps.map chargeOf).sum

/-- A spend's value in balance units, times `10^(18+K)`: exact for input
    decimals up to `K` (`raw` amounts are in balance units). -/
def worth (K : Nat) : Spend → Nat
  | .raw a => a * 10 ^ (18 + K)
  | .priced v p db di => v * p * 10 ^ db * 10 ^ (K - di)

def totalWorth (K : Nat) (sps : List Spend) : Nat := (sps.map (worth K)).sum

/-- The SDK's `accrueThenUpdate`: what `setAllowance` stores to change the
    refill at `now`. The balance is accrued under the old configuration;
    the new configuration starts at `now` (or at a later stored start). A
    partly elapsed old period is not credited. -/
def accrueThenUpdate (c : Config) (s : State) (now : Nat) : State :=
  ⟨(accrue c s now).balance, max now (accrue c s now).timestamp⟩

/-- Full periods from `t0` to `t` (none without a refill period). -/
def periods (c : Config) (t0 t : Nat) : Nat := if c.period = 0 then 0 else (t - t0) / c.period

end Allowance
