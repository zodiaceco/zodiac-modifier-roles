import Normalize.Defs

/-!
# What a condition means

`sem W c v` evaluates condition `c` on the decoded value `v`, as the Roles
evaluator does, with the two kinds of state it threads through `And`/`Or`:

* slots `S` (plucked values): written into shared context and never rolled
  back, so a failing `Or` branch leaves its writes for the next branch;
* consumptions `C` (allowance charges): copy-on-write, so each `Or` branch
  starts from the consumptions the `Or` started with.

A result is `(some c', s')` (passes, with consumptions `c'`) or
`(none, s')` (fails). The structural operators normalization rewrites are
defined here: `Pass`, `And`, `Or`, and `Matches` on tuples and calldata
(children read the fields in order; a non-structural child reads no field).
Every other operator is the world's `ext`, which sees its children only
through their meanings; `World.Ok` lists what is assumed of it.
-/

namespace Normalize

section
variable {V S C Ch : Type}

abbrev Res (S C : Type) := Option C × S
abbrev Thunk (S C : Type) := S → C → Res S C

def passT : Thunk S C := fun sl cs => (some cs, sl)

/-- Continue with `k` after a passing result. -/
def bindR (r : Res S C) (k : Thunk S C) : Res S C :=
  match r with
  | (some c, s) => k s c
  | (none, s) => (none, s)

/-- `_and`, `_matches`: children in order, stop at the first failure. -/
def seqT : List (Thunk S C) → Thunk S C
  | [] => passT
  | t :: ts => fun sl cs => bindR (t sl cs) (seqT ts)

/-- `_or`: children in order from the same consumptions, stop at the first
    success; slots carry over from failed branches. -/
def orT : List (Thunk S C) → Thunk S C
  | [] => fun sl _ => (none, sl)
  | t :: ts => fun sl cs =>
    match t sl cs with
    | (some c, s) => (some c, s)
    | (none, s) => orT ts s cs

structure World (V S C : Type) where
  /-- The fields of a tuple or calldata value, as a `Matches` with encoding,
      compValue and children reads them (the children say where each
      field is). -/
  fields : Nat → List Nat → List Cond → V → List V
  /-- The value of a field a `Matches` child reads past the end. -/
  dflt : V
  /-- `Matches` checks before its children (leading bytes, overflow). -/
  gate : Nat → List Nat → List Cond → V → Bool
  /-- Every other operator: the node (for what it reads of its own
      encoding and children), and its children's meanings. -/
  ext : Cond → List (V → Thunk S C) → V → Thunk S C

/-- Which value each `Matches` child reads. -/
def assign (d : V) : List Cond → List V → V → List (Cond × V)
  | [], _, _ => []
  | c :: cs, fs, v =>
    if isStruct c then (c, fs.headD d) :: assign d cs fs.tail v
    else (c, v) :: assign d cs fs v

mutual
  def sem (W : World V S C) : Cond → V → Thunk S C
    | ⟨e, o, cv, ch⟩, v =>
      if o = 0 then passT
      else if o = 1 then seqT (semAt W ch v)
      else if o = 2 then orT (semAt W ch v)
      else if o = 5 ∧ (e = 3 ∨ e = 5) then fun sl cs =>
        if W.gate e cv ch v then seqT (semM W ch (W.fields e cv ch v) v) sl cs else (none, sl)
      else W.ext ⟨e, o, cv, ch⟩ (semL W ch) v

  def semAt (W : World V S C) : List Cond → V → List (Thunk S C)
    | [], _ => []
    | c :: cs, v => sem W c v :: semAt W cs v

  def semM (W : World V S C) : List Cond → List V → V → List (Thunk S C)
    | [], _, _ => []
    | c :: cs, fs, v =>
      if isStruct c then sem W c (fs.headD W.dflt) :: semM W cs fs.tail v
      else sem W c v :: semM W cs fs v

  def semL (W : World V S C) : List Cond → List (V → Thunk S C)
    | [] => []
    | c :: cs => sem W c :: semL W cs
end

theorem semAt_eq (W : World V S C) (cs : List Cond) (v : V) :
    semAt W cs v = cs.map fun c => sem W c v := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp [semAt, ih]

theorem semM_eq (W : World V S C) (cs : List Cond) (fs : List V) (v : V) :
    semM W cs fs v = (assign W.dflt cs fs v).map fun p => sem W p.1 p.2 := by
  induction cs generalizing fs with
  | nil => rfl
  | cons c cs ih => by_cases h : isStruct c <;> simp [semM, assign, h, ih]

theorem semL_eq (W : World V S C) (cs : List Cond) : semL W cs = cs.map (sem W) := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp [semL, ih]

theorem mem_assign {d : V} {cs : List Cond} {fs : List V} {v : V} {p : Cond × V}
    (h : p ∈ assign d cs fs v) : p.1 ∈ cs := by
  induction cs generalizing fs with
  | nil => simp [assign] at h
  | cons c cs ih =>
    simp only [assign] at h
    split at h <;>
    · rcases List.mem_cons.1 h with rfl | h
      · simp
      · exact List.mem_cons_of_mem _ (ih h)

theorem assign_fst (d : V) (cs : List Cond) (fs : List V) (v : V) :
    (assign d cs fs v).map Prod.fst = cs := by
  induction cs generalizing fs with
  | nil => rfl
  | cons c cs ih => by_cases h : isStruct c <;> simp [assign, h, ih]

/-- The meaning of a `Matches` node on tuples and calldata. -/
def matchesT (W : World V S C) (e : Nat) (cv : List Nat) (ch : List Cond) (v : V) : Thunk S C :=
  fun sl cs => if W.gate e cv ch v then
    seqT ((assign W.dflt ch (W.fields e cv ch v) v).map fun p => sem W p.1 p.2) sl cs else (none, sl)

theorem sem_mk (W : World V S C) (e o cv ch v) :
    sem W ⟨e, o, cv, ch⟩ v =
      if o = 0 then passT
      else if o = 1 then seqT (ch.map fun c => sem W c v)
      else if o = 2 then orT (ch.map fun c => sem W c v)
      else if o = 5 ∧ (e = 3 ∨ e = 5) then matchesT W e cv ch v
      else W.ext ⟨e, o, cv, ch⟩ (ch.map (sem W)) v := by
  rw [sem, semAt_eq, semL_eq, semM_eq]
  rfl

theorem sem_eq (W : World V S C) (c : Cond) (v : V) :
    sem W c v =
      if c.op = 0 then passT
      else if c.op = 1 then seqT (c.ch.map fun x => sem W x v)
      else if c.op = 2 then orT (c.ch.map fun x => sem W x v)
      else if c.op = 5 ∧ (c.enc = 3 ∨ c.enc = 5) then matchesT W c.enc c.cv c.ch v
      else W.ext c (c.ch.map (sem W)) v := by
  rcases c; exact sem_mk ..

/-! ## Effects -/

def KeepsT (t : Thunk S C) : Prop := ∀ sl cs, (t sl cs).2 = sl

/-- Passes or fails depending on the slots only, charges nothing. -/
def PureT (t : Thunk S C) : Prop :=
  ∃ b : S → Bool, ∀ sl cs, t sl cs = (if b sl then some cs else none, sl)

/-- Charging a list of amounts in order (`AllowanceConsumer.consume`). -/
def applyL (step : C → Ch → Option C) : C → List Ch → Option C
  | cs, [] => some cs
  | cs, x :: xs => (step cs x).bind fun c => applyL step c xs

/-- Fails, or charges a list of amounts fixed by the slots. -/
def ChargerT (step : C → Ch → Option C) (t : Thunk S C) : Prop :=
  ∃ g : S → Option (List Ch), ∀ sl cs, t sl cs = ((g sl).bind (applyL step cs), sl)

/-- What is assumed of the operators normalization does not rewrite. -/
structure World.Ok (W : World V S C) (step : C → Ch → Option C) : Prop where
  /-- Two charges commute (true of `AllowanceConsumer.consume`, see `consume_comm`). -/
  comm : ∀ c x y, (step c x).bind (step · y) = (step c y).bind (step · x)
  /-- Only `Pluck` writes slots. -/
  keeps : ∀ c ss, c.op ≠ 14 → (∀ s ∈ ss, ∀ v, KeepsT (s v)) → ∀ v, KeepsT (W.ext c ss v)
  /-- Only `Custom`, `WithinAllowance`, `CallWithinAllowance` charge. -/
  pure : ∀ c ss, c.op ≠ 14 → c.op ≠ 22 → c.op ≠ 28 → c.op ≠ 30 → (∀ s ∈ ss, ∀ v, PureT (s v)) →
    ∀ v, PureT (W.ext c ss v)
  /-- Only choices (`ArraySome`, `ZipSome`) pick charges depending on earlier ones. -/
  charger : ∀ c ss, c.op ≠ 14 → c.op ≠ 2 → c.op ≠ 6 → c.op ≠ 10 →
    (∀ s ∈ ss, ∀ v, ChargerT step (s v)) → ∀ v, ChargerT step (W.ext c ss v)

/-- What normalization needs of a world that reads a value through the tree's
    own types (where each field of a `Matches` is depends on its children):
    an invariant `inv` of the trees under which the world reads a normalized
    child as the child, and the `Or` a merge puts at a hinge as each
    branch's hinge child. -/
structure World.NormOk (W : World V S C) (inv : Cond → Prop) : Prop where
  sub : ∀ c, inv c → ∀ x ∈ c.ch, inv x
  pre : ∀ n c, inv c → keepsAsWritten c = false →
    inv (unwrap (dedupe (flatten { c with ch := c.ch.map (normalize n) })))
  push : ∀ c x, inv c → pushStep c = some x → inv x
  fields : ∀ n e cv (ch : List Cond), (∀ x ∈ ch, inv x) → ∀ v,
    W.fields e cv (ch.map (normalize n)) v = W.fields e cv ch v ∧
    W.gate e cv (ch.map (normalize n)) v = W.gate e cv ch v
  ext : ∀ n c, inv c → keepsAsWritten c = false →
    W.ext { c with ch := c.ch.map (normalize n) } = W.ext c
  hinge : ∀ e cv (pre post hs : List Cond), sameType hs = true → hs ≠ [] → ∀ x ∈ hs, ∀ v,
    W.fields e cv (pre ++ x :: post) v = W.fields e cv (pre ++ orNode hs :: post) v ∧
    W.gate e cv (pre ++ x :: post) v = W.gate e cv (pre ++ orNode hs :: post) v

/-! ## Thunk algebra -/

@[simp] theorem bindR_some (c : C) (s : S) (k : Thunk S C) : bindR (some c, s) k = k s c := rfl
@[simp] theorem bindR_none (s : S) (k : Thunk S C) : bindR ((none : Option C), s) k = (none, s) := rfl

theorem seqT_cons (t : Thunk S C) ts sl cs : seqT (t :: ts) sl cs = bindR (t sl cs) (seqT ts) := rfl

theorem bindR_assoc (r : Res S C) (k1 k2 : Thunk S C) :
    bindR (bindR r k1) k2 = bindR r fun s c => bindR (k1 s c) k2 := by
  rcases r with ⟨_ | c, s⟩ <;> rfl

theorem seqT_append (a b : List (Thunk S C)) sl cs :
    seqT (a ++ b) sl cs = bindR (seqT a sl cs) (seqT b) := by
  induction a generalizing sl cs with
  | nil => rfl
  | cons t ts ih =>
    simp only [List.cons_append, seqT_cons, bindR_assoc]
    rcases t sl cs with ⟨_ | c, s⟩
    · rfl
    · exact ih s c

theorem seqT_pass_append (a : List (Thunk S C)) :
    seqT (a ++ [passT]) = seqT a := by
  funext sl cs
  rw [seqT_append]
  rcases seqT a sl cs with ⟨_ | c, s⟩ <;> rfl

theorem orT_append (a b : List (Thunk S C)) sl cs :
    orT (a ++ b) sl cs = match orT a sl cs with
      | (some c, s) => (some c, s)
      | (none, s) => orT b s cs := by
  induction a generalizing sl with
  | nil => rfl
  | cons t ts ih =>
    simp only [List.cons_append, orT]
    rcases t sl cs with ⟨_ | c, s⟩
    · exact ih s
    · rfl

theorem seqT_single (t : Thunk S C) : seqT [t] = t := by
  funext sl cs
  simp only [seqT_cons]
  rcases t sl cs with ⟨_ | c, s⟩ <;> rfl

theorem orT_single (t : Thunk S C) : orT [t] = t := by
  funext sl cs
  simp only [orT]
  rcases t sl cs with ⟨_ | c, s⟩ <;> rfl

theorem keeps_eq {t : Thunk S C} (h : KeepsT t) sl cs : ∃ r, t sl cs = (r, sl) :=
  ⟨(t sl cs).1, Prod.ext rfl (h sl cs)⟩

theorem seqT_keeps {l : List (Thunk S C)} (h : ∀ t ∈ l, KeepsT t) : KeepsT (seqT l) := by
  induction l with
  | nil => intro sl cs; rfl
  | cons t ts ih =>
    intro sl cs
    obtain ⟨r, hr⟩ := keeps_eq (h t (by simp)) sl cs
    rw [seqT_cons, hr]
    rcases r with _ | c
    · rfl
    · exact ih (fun t' ht' => h t' (by simp [ht'])) sl c

theorem orT_keeps {l : List (Thunk S C)} (h : ∀ t ∈ l, KeepsT t) : KeepsT (orT l) := by
  induction l with
  | nil => intro sl cs; rfl
  | cons t ts ih =>
    intro sl cs
    obtain ⟨r, hr⟩ := keeps_eq (h t (by simp)) sl cs
    simp only [orT, hr]
    rcases r with _ | c
    · exact ih (fun t' ht' => h t' (by simp [ht'])) sl cs
    · rfl

theorem PureT.keeps {t : Thunk S C} (h : PureT t) : KeepsT t := by
  obtain ⟨b, hb⟩ := h
  intro sl cs
  rw [hb]

theorem seqT_pure {l : List (Thunk S C)} (h : ∀ t ∈ l, PureT t) : PureT (seqT l) := by
  induction l with
  | nil => exact ⟨fun _ => true, fun _ _ => rfl⟩
  | cons t ts ih =>
    obtain ⟨b, hb⟩ := h t (by simp)
    obtain ⟨b', hb'⟩ := ih fun t' ht' => h t' (by simp [ht'])
    refine ⟨fun sl => b sl && b' sl, fun sl cs => ?_⟩
    rw [seqT_cons, hb]
    by_cases h1 : b sl
    · simp [h1, hb']
    · simp [h1]

theorem orT_pure {l : List (Thunk S C)} (h : ∀ t ∈ l, PureT t) : PureT (orT l) := by
  induction l with
  | nil => exact ⟨fun _ => false, fun _ _ => rfl⟩
  | cons t ts ih =>
    obtain ⟨b, hb⟩ := h t (by simp)
    obtain ⟨b', hb'⟩ := ih fun t' ht' => h t' (by simp [ht'])
    refine ⟨fun sl => b sl || b' sl, fun sl cs => ?_⟩
    simp only [orT, hb]
    by_cases h1 : b sl
    · simp [h1]
    · simp [h1, hb']

theorem applyL_append (step : C → Ch → Option C) (cs : C) (a b : List Ch) :
    applyL step cs (a ++ b) = (applyL step cs a).bind fun c => applyL step c b := by
  induction a generalizing cs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.cons_append, applyL, Option.bind_assoc]
    congr 1
    funext c
    exact ih c

theorem applyL_perm {step : C → Ch → Option C}
    (comm : ∀ c x y, (step c x).bind (step · y) = (step c y).bind (step · x))
    {a b : List Ch} (h : a.Perm b) (cs : C) : applyL step cs a = applyL step cs b := by
  induction h generalizing cs with
  | nil => rfl
  | cons x _ ih => simp only [applyL]; congr 1; funext c; exact ih c
  | swap x y l =>
    simp only [applyL]
    rw [← Option.bind_assoc, ← Option.bind_assoc, comm]
  | trans _ _ ih1 ih2 => rw [ih1, ih2]

theorem PureT.charger {t : Thunk S C} (step : C → Ch → Option C) (h : PureT t) :
    ChargerT step t := by
  obtain ⟨b, hb⟩ := h
  refine ⟨fun sl => if b sl then some [] else none, fun sl cs => ?_⟩
  rw [hb]
  by_cases h1 : b sl <;> simp [h1, applyL]

theorem ChargerT.keeps {step : C → Ch → Option C} {t : Thunk S C} (h : ChargerT step t) :
    KeepsT t := by
  obtain ⟨g, hg⟩ := h
  intro sl cs
  rw [hg]

theorem seqT_charger {step : C → Ch → Option C} {l : List (Thunk S C)}
    (h : ∀ t ∈ l, ChargerT step t) : ChargerT step (seqT l) := by
  induction l with
  | nil => exact ⟨fun _ => some [], fun _ _ => rfl⟩
  | cons t ts ih =>
    obtain ⟨g, hg⟩ := h t (by simp)
    obtain ⟨g', hg'⟩ := ih fun t' ht' => h t' (by simp [ht'])
    refine ⟨fun sl => (g sl).bind fun l1 => (g' sl).map (l1 ++ ·), fun sl cs => ?_⟩
    rw [seqT_cons, hg]
    dsimp only
    rcases g sl with _ | l1
    · rfl
    · rcases h2 : applyL step cs l1 with _ | c1
      · rcases g' sl with _ | l2 <;> simp [applyL_append, h2]
      · rcases h3 : g' sl with _ | l2 <;> simp [hg', h3, applyL_append, h2]

/-- Running `a` then `b` equals running `b` then `a`, before any continuation. -/
def Comm (a b : Thunk S C) : Prop :=
  ∀ (k : Thunk S C) sl cs,
    bindR (a sl cs) (fun s c => bindR (b s c) k) = bindR (b sl cs) (fun s c => bindR (a s c) k)

theorem comm_pure {a b : Thunk S C} (ha : PureT a) (hb : KeepsT b) : Comm a b := by
  obtain ⟨p, hp⟩ := ha
  intro k sl cs
  obtain ⟨r, hr⟩ := keeps_eq hb sl cs
  rw [hp, hr]
  by_cases h1 : p sl
  · simp only [h1, ite_true, bindR_some, hr]
    rcases r with _ | c
    · rfl
    · simp [hp, h1]
  · simp only [h1]
    rcases r with _ | c
    · rfl
    · simp [hp, h1]

theorem Comm.symm {a b : Thunk S C} (h : Comm a b) : Comm b a := fun k sl cs => (h k sl cs).symm

theorem comm_charger {step : C → Ch → Option C}
    (comm : ∀ c x y, (step c x).bind (step · y) = (step c y).bind (step · x))
    {a b : Thunk S C} (ha : ChargerT step a) (hb : ChargerT step b) : Comm a b := by
  obtain ⟨ga, hga⟩ := ha
  obtain ⟨gb, hgb⟩ := hb
  have key : ∀ (k : Thunk S C) sl cs (la lb : List Ch),
      bindR ((applyL step cs la), sl) (fun s c => bindR ((applyL step c lb), s) k) =
        match applyL step cs (la ++ lb) with
        | some c => k sl c
        | none => (none, sl) := by
    intro k sl cs la lb
    rw [applyL_append]
    rcases applyL step cs la with _ | c
    · rfl
    · simp only [bindR_some, Option.bind_some]
      rcases applyL step c lb with _ | c' <;> rfl
  intro k sl cs
  rw [hga, hgb]
  rcases h1 : ga sl with _ | la <;> rcases h2 : gb sl with _ | lb
  · rfl
  · simp only [Option.bind_none, bindR_none, Option.bind_some]
    rcases applyL step cs lb with _ | c <;> simp [hga, h1]
  · simp only [Option.bind_none, bindR_none, Option.bind_some]
    rcases applyL step cs la with _ | c <;> simp [hgb, h2]
  · simp only [Option.bind_some]
    have e1 : ∀ c, b sl c = ((applyL step c lb), sl) := fun c => by rw [hgb, h2]; rfl
    have e2 : ∀ c, a sl c = ((applyL step c la), sl) := fun c => by rw [hga, h1]; rfl
    have : (bindR (applyL step cs la, sl) fun s c => bindR (b s c) k) =
        bindR (applyL step cs la, sl) fun s c => bindR ((applyL step c lb), s) k := by
      rcases applyL step cs la with _ | c
      · rfl
      · simp only [bindR_some, e1]
    rw [this, key]
    have : (bindR (applyL step cs lb, sl) fun s c => bindR (a s c) k) =
        bindR (applyL step cs lb, sl) fun s c => bindR ((applyL step c la), s) k := by
      rcases applyL step cs lb with _ | c
      · rfl
      · simp only [bindR_some, e2]
    rw [this, key, applyL_perm comm List.perm_append_comm]

theorem seqT_swap {a b : Thunk S C} (h : Comm a b) (l : List (Thunk S C)) :
    seqT (a :: b :: l) = seqT (b :: a :: l) := by
  funext sl cs
  simp only [seqT_cons]
  exact h (seqT l) sl cs

end
end Normalize
