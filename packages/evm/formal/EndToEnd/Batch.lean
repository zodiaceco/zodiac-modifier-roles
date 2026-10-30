import EndToEnd.Consume
import MultiSend
import Allowance

/-!
# Batches: what the avatar executes, and what the allowances pay

`Authorization._authorize` checks a call through a role: either the call
itself, or, when a transaction unwrapper is registered for its target and
selector, each transaction of the batch, threading the consumptions from one
to the next. After the avatar executes, `Settlement._persist` stores them.

* `executed_authorized`: every transaction the avatar executes (the call,
  or each transaction `MultiSend` runs) passed its own permission: a scope
  entry for its target and selector, execution options that allow its value
  and operation, and a condition that passes on its calldata.
* `authorize_steps`: the batch's consumptions are successful `consume`
  steps from the empty list, across all its transactions.
* `authorize_persist`: so, for every allowance, what `_persist` stores is
  one `Allowance.tx` with the charges of the whole batch.
* `executions_limit`: over any sequence of executions, every allowance
  obeys the spending limit of `Allowance.spending_limit`, batches included.

Hypotheses, each a fact about the deployment rather than the code:
* An unwrapper is registered only for `MultiSendUnwrapper` at a `MultiSend`
  (owner configuration, `setTransactionUnwrapper`).
* `envOf` is what the evaluation reads besides calldata and the tree:
  custom checkers, ratio and price adapters, accrued balances. All
  transactions of a batch are checked before any executes, so all read the
  state from before the batch (one `envOf`, fixed for the batch).
* Nothing else writes the allowances between executions: owner calls, or
  the executed transactions themselves (the settlement caveat in the docs).
-/

namespace EndToEnd
open DecoderFaithfulness DecoderFaithfulness.Roles Evaluate MultiSend

/-! ## `_authorize` -/

/-- A role's configuration, as `_transaction` reads it. -/
structure Perms where
  /-- `role.clearance[to]`: `0` None, `1` Target, `2` Function. -/
  clearance : Nat → Nat
  /-- `role.scopeConfig[key]` (`0`: none). -/
  scope : Nat → Nat
  /-- `ConditionLoader.load(scopeConfig)`: the tree `evaluate` runs, and
      `maxPluckIndex`. -/
  load : Nat → Condition × Nat
  /-- `unwrappers[_key(to, selector)] != address(0)`. -/
  unwrapper : Nat → Bool

/-- `bytes4(data)`, zero-padded. -/
def sel (data : Bytes) : Nat := wordVal ((data ++ zeros 4).take 4)

/-- Scope keys: `[20 bytes address][8 bytes][4 bytes selector]`. -/
def fnKey (to s : Nat) : Nat := to * 2 ^ 96 + s * 2 ^ 64
def targetKey (to : Nat) : Nat := to * 2 ^ 96 + (2 ^ 96 - 1)
def globalKey (s : Nat) : Nat := s * 2 ^ 64

/-- Scope resolution: the destination entry, then the global entry. -/
def resolve (p : Perms) (to : Nat) (data : Bytes) : Nat :=
  let sc := if p.clearance to = 2 then p.scope (fnKey to (sel data))
    else if p.clearance to = 1 then p.scope (targetKey to) else 0
  if sc = 0 ∧ data ≠ [] then p.scope (globalKey (sel data)) else sc

/-- `ExecutionOptions` in the high bits of `scopeConfig`: bit 0 allows
    value, bit 1 delegatecall. -/
def optionsOk (sc value op : Nat) : Bool :=
  let o := sc / 2 ^ 160
  !(o % 2 = 0 && value > 0) && !((o / 2) % 2 = 0 && op = 1)

/-- `_transaction`: the consumptions after checking one transaction, or
    `none` (a revert). -/
def transaction (p : Perms) (env : Env) (cons : List Consumption) (e : Entry) :
    Option (List Consumption) :=
  if e.data.length ≠ 0 ∧ e.data.length < 4 then none
  else
    let sc := resolve p e.to e.data
    if sc = 0 then none
    else if !optionsOk sc e.value e.op then none
    else
      let r := run env e.data (p.load sc).1 (p.load sc).2 cons
      if r.status = sOk then some r.cons else none

/-- Transactions in order, threading the consumptions. -/
def chain (p : Perms) (envOf : Entry → Env) : List Consumption → List Entry → Option (List Consumption)
  | cons, [] => some cons
  | cons, e :: es => (transaction p (envOf e) cons e).bind (chain p envOf · es)

/-- `_authorize(roleKey, to, value, data, operation)`. -/
def authorize (p : Perms) (envOf : Entry → Env) (to value : Nat) (data : Bytes) (op : Nat) :
    Option (List Consumption) :=
  if p.unwrapper (fnKey to (sel data)) then
    (unwrap data value op).bind fun us => chain p envOf [] (us.map (Unwrapped.view data))
  else chain p envOf [] [⟨op, to, value, data⟩]

/-! ## Every executed transaction passed its permission -/

/-- What `_transaction` requires of one transaction: calldata empty or with
    a selector, a scope entry, options allowing its value and operation,
    and its condition passing on its calldata. -/
def Permitted (p : Perms) (env : Env) (e : Entry) : Prop :=
  ¬(e.data.length ≠ 0 ∧ e.data.length < 4) ∧ resolve p e.to e.data ≠ 0 ∧
    optionsOk (resolve p e.to e.data) e.value e.op = true ∧
    ∃ cons, (run env e.data (p.load (resolve p e.to e.data)).1
      (p.load (resolve p e.to e.data)).2 cons).status = sOk

theorem transaction_permitted {p : Perms} {env : Env} {cons cons' : List Consumption} {e : Entry}
    (h : transaction p env cons e = some cons') : Permitted p env e := by
  unfold transaction at h
  split at h
  · cases h
  · rename_i h1
    simp only at h
    split at h
    · cases h
    · rename_i h2
      split at h
      · cases h
      · rename_i h3
        split at h
        · rename_i h4
          exact ⟨h1, h2, by simpa using h3, cons, h4⟩
        · cases h

theorem chain_permitted {p : Perms} {envOf : Entry → Env} :
    ∀ {cons cons' : List Consumption} {es : List Entry}, chain p envOf cons es = some cons' →
      ∀ e ∈ es, Permitted p (envOf e) e
  | _, _, [], _, e, he => by simp at he
  | cons, cons', e0 :: es, h, e, he => by
    simp only [chain] at h
    rcases ht : transaction p (envOf e0) cons e0 with _ | c1
    · rw [ht] at h; cases h
    · rw [ht] at h
      rcases List.mem_cons.mp he with rfl | he
      · exact transaction_permitted ht
      · exact chain_permitted h e he

/-- **Every transaction the avatar executes passed its permission.** When
    `_authorize` lets a call through, the transactions the avatar executes
    are either the call itself, or, if an unwrapper is registered for it
    (`MultiSendUnwrapper` at a `MultiSend`), exactly the transactions
    `MultiSend`'s loop runs on the batch (`unwrap_exec`, whatever memory
    follows it). Each of them is `Permitted`, with the consumptions
    threaded from one to the next. -/
theorem executed_authorized {p : Perms} {envOf : Entry → Env} {to value op : Nat} {data : Bytes}
    {cons : List Consumption} (h : authorize p envOf to value data op = some cons)
    (hdl : data.length < 2 ^ 256) (junk : Bytes) :
    ∃ es, chain p envOf [] es = some cons ∧ (∀ e ∈ es, Permitted p (envOf e) e) ∧
      (if p.unwrapper (fnKey to (sel data)) then
        let tx := (data.drop 68).take (load data 36)
        let mem := word tx.length ++ tx ++ junk
        ∃ fuel, execLoop mem (mload mem 0) fuel 32 = some es
      else es = [⟨op, to, value, data⟩]) := by
  unfold authorize at h
  split at h
  · rename_i hu
    rcases hw : unwrap data value op with _ | us
    · rw [hw] at h; cases h
    · rw [hw] at h
      refine ⟨_, h, chain_permitted h, ?_⟩
      rw [if_pos hu]
      exact ⟨_, unwrap_exec data junk value op us hw hdl⟩
  · rename_i hu
    refine ⟨_, h, chain_permitted h, ?_⟩
    rw [if_neg hu]

/-! ## The batch's consumptions -/

section
variable {bal : Bytes → Nat} {p : Perms} {envOf : Entry → Env}
  (hbal : ∀ e, (envOf e).balance = bal)
  (hcustom : ∀ e cv l sz vals s, (envOf e).customCall cv l sz vals = .inl s → s ≠ sOk)

include hbal hcustom in
theorem transaction_steps {cons cons' : List Consumption} {e : Entry}
    (h : transaction p (envOf e) cons e = some cons') : ∃ log, Steps bal cons log cons' := by
  unfold transaction at h
  split at h
  · cases h
  · simp only at h
    split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · rename_i hok
          simp only [Option.some.injEq] at h
          subst h
          have := evalC_steps (envOf e) e.data _ (hcustom e) _ 0 _ cons Slots.empty hok
          rw [hbal] at this
          exact this
        · cases h

include hbal hcustom in
theorem chain_steps : ∀ {cons cons' : List Consumption} {es : List Entry},
    chain p envOf cons es = some cons' → ∃ log, Steps bal cons log cons'
  | cons, _, [], h => by simp only [chain, Option.some.injEq] at h; subst h; exact ⟨[], .nil cons⟩
  | cons, cons', e :: es, h => by
    simp only [chain] at h
    rcases ht : transaction p (envOf e) cons e with _ | c1
    · rw [ht] at h; cases h
    · rw [ht] at h
      obtain ⟨l1, h1⟩ := transaction_steps hbal hcustom ht
      obtain ⟨l2, h2⟩ := chain_steps h
      exact ⟨_, h1.trans h2⟩

include hbal hcustom in
/-- **A batch charges by steps.** The consumptions `_authorize` returns are
    successful `consume` steps from the empty list, through all the
    transactions of the batch. -/
theorem authorize_steps {to value op : Nat} {data : Bytes} {cons : List Consumption}
    (h : authorize p envOf to value data op = some cons) : ∃ log, Steps bal [] log cons := by
  unfold authorize at h
  split at h
  · rcases hw : unwrap data value op with _ | us
    · rw [hw] at h; cases h
    · rw [hw] at h; exact chain_steps hbal hcustom h
  · exact chain_steps hbal hcustom h

end

/-- **Settlement after a batch is one `Allowance.tx` per allowance.**
    Balances accrued at the block time `now` from the stored state `st`:
    after `_authorize` lets a call through, there are charges `log` (the
    batch's, in order) such that, for every allowance key, what `_persist`
    stores is `Allowance.tx` on that key's charges. -/
theorem authorize_persist (cfg : Bytes → Allowance.Config) (st : Bytes → Allowance.State) (now : Nat)
    {p : Perms} {envOf : Entry → Env}
    (hbal : ∀ e, (envOf e).balance = fun k => (Allowance.accrue (cfg k) (st k) now).balance)
    (hcustom : ∀ e cv l sz vals s, (envOf e).customCall cv l sz vals = .inl s → s ≠ sOk)
    {to value op : Nat} {data : Bytes} {cons : List Consumption}
    (h : authorize p envOf to value data op = some cons) :
    ∃ log, Steps (fun k => (Allowance.accrue (cfg k) (st k) now).balance) [] log cons ∧
      ∀ k, Allowance.tx (cfg k) (st k) now (charges log k) =
        .ok (persist (fun k => Allowance.accrue (cfg k) (st k) now) st cons k) := by
  obtain ⟨log, hl⟩ := authorize_steps hbal hcustom h
  exact ⟨log, hl, persist_tx cfg st now hl⟩

/-! ## The spending limit over executions -/

/-- Executions that went through, in order, at block times `now`: each
    charges `log` by steps from balances accrued from the stored state, and
    `_persist` stores the result. (A failed execution stores nothing and is
    left out. Nothing else writes the allowances in between.) -/
inductive Execs (cfg : Bytes → Allowance.Config) :
    (Bytes → Allowance.State) → List (Nat × List (Bytes × Nat)) → (Bytes → Allowance.State) → Prop
  | nil (st : Bytes → Allowance.State) : Execs cfg st [] st
  | exec {st st' : Bytes → Allowance.State} {now : Nat} {log : List (Bytes × Nat)}
      {cons : List Consumption} {rest : List (Nat × List (Bytes × Nat))}
      (h : Steps (fun k => (Allowance.accrue (cfg k) (st k) now).balance) [] log cons)
      (hrest : Execs cfg (persist (fun k => Allowance.accrue (cfg k) (st k) now) st cons) rest st') :
      Execs cfg st ((now, log) :: rest) st'

/-- Per allowance, executions are `Allowance.run` on their charges. -/
theorem execs_run {cfg : Bytes → Allowance.Config} (k : Bytes) :
    ∀ {st st' : Bytes → Allowance.State} {txs : List (Nat × List (Bytes × Nat))},
      Execs cfg st txs st' →
      Allowance.run (cfg k) (st k) (txs.map fun x => (x.1, charges x.2 k)) =
        (st' k, txs.flatMap fun x => charges x.2 k)
  | _, _, _, .nil st => by simp [Allowance.run]
  | st, st', _, @Execs.exec _ _ _ now log cons rest h hrest => by
    simp only [List.map_cons, Allowance.run, List.flatMap_cons]
    rw [persist_tx cfg st now h k]
    simp only
    rw [execs_run k hrest]

/-- **Spending limit, end to end.** Over any executions through Roles at
    block times up to `T`, batches included, the charges to an allowance
    total at most its stored balance plus `refill` for each full period from
    the stored timestamp to `T`. -/
theorem executions_limit {cfg : Bytes → Allowance.Config} {st st' : Bytes → Allowance.State}
    {txs : List (Nat × List (Bytes × Nat))} (h : Execs cfg st txs st') (k : Bytes) (T : Nat)
    (hT : ∀ x ∈ txs, x.1 ≤ T) :
    Allowance.charged (txs.flatMap fun x => charges x.2 k) ≤
      (st k).balance + (cfg k).refill * Allowance.periods (cfg k) (st k).timestamp T := by
  have := Allowance.spending_limit (cfg k) (st k) (txs.map fun x => (x.1, charges x.2 k)) T
    (by intro x hx; obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx; exact hT y hy)
  rw [execs_run k h] at this
  exact this

end EndToEnd
