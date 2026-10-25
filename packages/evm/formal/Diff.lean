import DecoderFaithfulness.Roles
import ConditionPacking.Model
import ConditionCheck.Stored
import Normalize.Defs
import Evaluate.Model
import Bridge.InvCheck

/-!
Differential-testing driver for the Roles transcription (`DecoderFaithfulness/Roles.lean`).

Reads one query per line on stdin:

    <calldata hex> <location> <node index> <nodes>

`<nodes>` is the flat BFS tree as `parent:encoding:operator:compValueHex`
entries joined by `|` (`ConditionFlat[]`, enum values as in Solidity).
For the node at `<node index>` (BFS order, after pack/unpack) it prints

    <children result> <size result>

where the children result is `none` (overflow) or comma-separated locations
(`-` for an empty list).

A line `bm <calldata hex> <location> <compValue hex> <inlined 0|1> <size>`
runs `bitmaskCheck` instead and prints the `Status` number it returns
(0 `Ok`, 8 `BitmaskOverflow`, 9 `BitmaskNotAllowed`, 20 `CalldataOverflow`).

A line `pk <nodes>` prints the buffer `ConditionPacker.pack` produces in the
packing model (`ConditionPacking/Model.lean`), as hex. A line `up <buffer hex>`
runs the model's `ConditionUnpacker.unpack` on a buffer (avatar = address 0)
and prints `<maxPluckValue> <nodes>`, the unpacked tree in BFS order as
`parent:encoding:operator:compValueHex:inlined:size` entries joined by `|`
(the format of `MockPackerUnpacker.roundtrip`), or `none`.

A line `ck <s 0|1> <nodes>` runs `ConditionCheck.checkStored s` (the full SDK
check) on the flat array and prints `ok <type>` (typed root), `ns` (root reads no
calldata) or `none` (rejected, also for unknown encoding/operator codes).

A line `ev <value> <allowances> <calldata hex> <nodes>` packs and unpacks the
tree in the packing model and runs the evaluator model
(`Evaluate/Model.lean`) on it, with `msg.value` = `<value>` and the
allowance balances `<allowances>` (`key:balance` joined by `,`, or `-`). It
prints `<status> <consumptions>`: the `Status` number (255 for a revert) and
the consumption list as `key:balance:consumed` joined by `,` (or `-`).

Trees can also be given nested, independently of any flattening:
`(<enc> <op> <cv hex or -> <child> ...)`, e.g. `(5 5 - (1 16 00..01))`.
`nzt <tree>` normalizes and prints the result in the same form, `ivt <tree>`
is `iv` on it, and `fl <tree> <nodes>` prints `eq` if the flat BFS array
`<nodes>` reads back as the tree (`buildCond`, the driver's `nest`), else
`ne`.

A line `iv <nodes>` builds the SDK tree and runs `Bridge.invB` (the
well-typedness `Bridge` assumes) and prints `ok`, or `bad <node> <clauses>`:
the first node (BFS index) that fails and which clauses of `invP` fail
(`ad` adOk, `enc` And/Or encoding, `lay` And/Or layouts, `ns` And/Or
children that read nothing, `td` type descriptions, `st` children read a
parameter, `sz` inlined size).

Used by `test/formal/lean-model.spec.ts` and `test/formal/integrity-gaps.spec.ts`.
-/

open DecoderFaithfulness DecoderFaithfulness.Roles

def hexVal (c : Char) : Nat :=
  if '0' ≤ c ∧ c ≤ '9' then c.toNat - '0'.toNat
  else if 'a' ≤ c ∧ c ≤ 'f' then c.toNat - 'a'.toNat + 10
  else if 'A' ≤ c ∧ c ≤ 'F' then c.toNat - 'A'.toNat + 10
  else 0

def parseHex (s : String) : Bytes :=
  let s := if s.startsWith "0x" then String.ofList (s.toList.drop 2) else s
  let rec go : List Char → Bytes
    | a :: b :: rest => ⟨(hexVal a * 16 + hexVal b) % 256, Nat.mod_lt _ (by decide)⟩ :: go rest
    | _ => []
  go s.toList

def toEncoding : Nat → Encoding
  | 0 => .None | 1 => .Static | 2 => .Dynamic | 3 => .Tuple | 4 => .Array
  | 5 => .AbiEncoded | _ => .EtherValue

def toOperator : Nat → Operator
  | 0 => .Pass | 1 => .And | 2 => .Or | 4 => .Empty | 5 => .Matches | 6 => .ArraySome
  | 7 => .ArrayEvery | 8 => .ArrayTailMatches | 10 => .ZipSome | 11 => .ZipEvery
  | 13 => .Slice | 14 => .Pluck | 15 => .EqualToAvatar | 16 => .EqualTo
  | 17 => .GreaterThan | 18 => .LessThan | 19 => .SignedIntGreaterThan
  | 20 => .SignedIntLessThan | 21 => .Bitmask | 22 => .Custom | 23 => .WithinRatio
  | 28 => .WithinAllowance | 30 => .CallWithinAllowance | _ => .Pass

structure Flat where
  parent : Nat
  encoding : Nat
  operator : Nat
  compValue : Bytes
  deriving Inhabited

/-- Raw node `i` with its subtree (children: later nodes whose parent is `i`). -/
def build (nodes : Array Flat) : Nat → Nat → Condition
  | 0, _ => default
  | fuel + 1, i =>
    let n := nodes[i]!
    let kids := (List.range nodes.size).filter (fun j => j ≠ 0 ∧ j ≠ i ∧ nodes[j]!.parent = i)
    let lb := if n.compValue.length ≥ 2
      then (n.compValue.getD 0 0).val * 256 + (n.compValue.getD 1 0).val else 4
    { encoding := toEncoding n.encoding
      operator := toOperator n.operator
      children := kids.map (build nodes fuel)
      inlined := false, size := 0
      leadingBytes := lb
      compValue := n.compValue }

/-- BFS order of a tree. -/
def bfs (root : Condition) : Nat → List Condition → List Condition
  | 0, _ => []
  | _, [] => []
  | fuel + 1, c :: queue => c :: bfs root fuel (queue ++ c.children)

def showLocs : Option (List Nat) → String
  | none => "none"
  | some [] => "-"
  | some ls => ",".intercalate (ls.map toString)

def statusCode : BitmaskStatus → Nat
  | .Ok => 0
  | .BitmaskOverflow => 8
  | .BitmaskNotAllowed => 9
  | .CalldataOverflow => 20

def hexOf (bs : Bytes) : String :=
  let d := "0123456789abcdef".toList
  "0x" ++ String.ofList (bs.flatMap fun b => [d.getD (b.val / 16) '0', d.getD (b.val % 16) '0'])

def parseNodes (nodesStr : String) : Array Flat :=
  (nodesStr.splitOn "|").toArray.map fun e =>
    match e.splitOn ":" with
    | [p, en, op, cv] => { parent := p.toNat!, encoding := en.toNat!, operator := op.toNat!,
                           compValue := parseHex cv : Flat }
    | _ => { parent := 0, encoding := 0, operator := 0, compValue := [] }

def showUnpacked (buf : Bytes) : String :=
  match ConditionPacking.unpack (zeros 32) (ConditionPacking.bufMem buf fun _ => 0) with
  | none => "none"
  | some (root, maxPluck) =>
    let rec go : Nat → Nat → List (Nat × Condition) → List String
      | 0, _, _ => []
      | _, _, [] => []
      | fuel + 1, idx, (p, c) :: queue =>
        s!"{p}:{ConditionPacking.encCode c.encoding}:{ConditionPacking.opCode c.operator}:{(hexOf c.compValue).drop 2}:{if c.inlined then 1 else 0}:{c.size}"
          :: go fuel (idx + 1) (queue ++ c.children.map fun ch => (idx, ch))
    s!"{maxPluck} " ++ "|".intercalate (go 100000 0 [(0, root)])

/-- The type as `S`, `D`, `T(..)`, `A(..)`, `C<lb>(..)`, open types with a
    trailing `..` field (as `tyKey` in the
    SDK's checkStored.ts). -/
partial def tyKey : ConditionCheck.Ty → String
  | .static => "S"
  | .dynamic => "D"
  | .tuple ts o => "T(" ++ ",".intercalate (ts.map tyKey ++ (if o then [".."] else [])) ++ ")"
  | .array t => "A(" ++ tyKey t ++ ")"
  | .call lb ts o =>
    s!"C{lb}(" ++ ",".intercalate (ts.map tyKey ++ (if o then [".."] else [])) ++ ")"

/-- An SDK condition tree from flat nodes `parent:enc:op:cv` (BFS order). -/
partial def buildCond (ns : Array Flat) (i : Nat) : Normalize.Cond :=
  let n := ns[i]!
  let kids := (List.range ns.size).filter fun j => j > i && ns[j]!.parent == i
  ⟨n.encoding, n.operator, n.compValue.map (·.toNat), kids.map (buildCond ns)⟩

def showCond (c : Normalize.Cond) : String :=
  "|".intercalate ((Normalize.bfsGo (Normalize.nodeCount c) [(c, 0)] #[]).toList.map
    fun (p, x) => s!"{p}:{x.enc}:{x.op}:{(Normalize.hexOf x.cv).drop 2}")

def toPackingFlat (ns : List Flat) : Option (List ConditionPacking.Flat) :=
  ns.mapM fun n =>
    match ConditionPacking.encOf? n.encoding, ConditionPacking.opOf? n.operator with
    | some e, some o => some ({ parent := n.parent, paramType := e, operator := o,
                                compValue := n.compValue } : ConditionPacking.Flat)
    | _, _ => none

/-- The `ev` query (see the header). Runs that need an external call
    (`Custom`, `WithinRatio`, a price adapter) report status 254. -/
def runEval (value allowances hex nodesStr : String) : String :=
  let bal : List (Bytes × Nat) :=
    if allowances == "-" then []
    else (allowances.splitOn ",").map fun kv =>
      match kv.splitOn ":" with
      | [k, b] => (parseHex k, b.toNat!)
      | _ => ([], 0)
  let env : Evaluate.Env :=
    { value := value.toNat!
      balance := fun k => ((bal.find? (·.1 == k)).map (·.2)).getD 0
      scale := fun _ _ => (254, 0)
      customCall := fun _ _ _ _ => .inl 254
      ratio := fun _ _ => 254 }
  match toPackingFlat (parseNodes nodesStr).toList with
  | none => "bad-input"
  | some fs =>
    match ConditionPacking.unpack (zeros 32)
        (ConditionPacking.bufMem (ConditionPacking.pack (fun _ => 0) fs) fun _ => 0) with
    | none => "unpack-failed"
    | some (root, maxPluck) =>
      let r := Evaluate.run env (parseHex hex) root maxPluck []
      let cons := if r.cons.isEmpty then "-" else ",".intercalate (r.cons.map fun c =>
        s!"{(hexOf c.key).drop 2}:{c.balance}:{c.consumed}")
      s!"{r.status} {cons}"

/-- The clauses of `invP` a node fails (see the `iv` query). -/
def invWhy (c : Normalize.Cond) : List String :=
  let av := zeros 32
  let isLog := c.op == 1 || c.op == 2
  let one (k : String) (b : Bool) := if b then [] else [k]
  one "ad" (Bridge.adOkB c) ++
  one "enc" (!isLog || c.enc == 0) ++
  one "lay" (!isLog || c.ch.all fun x => c.ch.all fun y =>
    !Normalize.isStruct x || !Normalize.isStruct y || Bridge.layB av x y) ++
  one "ns" (!isLog || c.ch.all fun x => Normalize.isStruct x || Bridge.zB av x ||
    c.ch.any fun y => Normalize.isStruct y && !Normalize.isInl y) ++
  one "td" (!Bridge.descOp c.op || c.ch.all Bridge.tdB) ++
  one "st" (isLog || Normalize.keepsAsWritten c ||
    (c.ch.all Normalize.isStruct && (c.enc != 3 || !c.ch.isEmpty))) ++
  one "sz" (!Normalize.isStruct c || !Normalize.isInl c || decide (0 < Bridge.rawSz av c))

def runInv (c : Normalize.Cond) : String :=
  if Bridge.invB (zeros 32) c then "ok" else
  let nodes := (Normalize.bfsGo (Normalize.nodeCount c) [(c, 0)] #[]).toList
  match (nodes.zipIdx).find? fun ((_, x), _) => !Bridge.invPB (zeros 32) x with
  | some ((_, x), i) => s!"bad {i} {",".intercalate (invWhy x)}"
  | none => "bad ? ?"

/-- Parses a nested tree `(enc op cv child ...)`. -/
partial def parseTree (cs : List Char) : Option (Normalize.Cond × List Char) :=
  let skip (l : List Char) := l.dropWhile (· == ' ')
  let token (l : List Char) : String × List Char :=
    let l := skip l
    (String.ofList (l.takeWhile fun c => c != ' ' && c != '(' && c != ')'),
      l.dropWhile fun c => c != ' ' && c != '(' && c != ')')
  match skip cs with
  | '(' :: rest =>
    let (e, rest) := token rest
    let (o, rest) := token rest
    let (cv, rest) := token rest
    let rec kids (l : List Char) (acc : List Normalize.Cond) : Option (List Normalize.Cond × List Char) :=
      match skip l with
      | ')' :: r => some (acc.reverse, r)
      | l' => match parseTree l' with
        | some (k, r) => kids r (k :: acc)
        | none => none
    match kids rest [] with
    | some (ch, r) =>
      some (⟨e.toNat!, o.toNat!, if cv == "-" then [] else (parseHex cv).map (·.toNat), ch⟩, r)
    | none => none
  | _ => none

partial def showTree (c : Normalize.Cond) : String :=
  let cv := if c.cv.isEmpty then "-" else ((Normalize.hexOf c.cv).drop 2).toString
  "(" ++ " ".intercalate ([toString c.enc, toString c.op, cv] ++ c.ch.map showTree) ++ ")"

def withTree (t : String) (k : Normalize.Cond → String) : String :=
  match parseTree t.toList with
  | some (c, rest) => if rest.all (· == ' ') then k c else "bad-input"
  | none => "bad-input"

def runLine (line : String) : String :=
  let line := (line.splitOn "\n").headD ""
  -- nested trees contain spaces: split off the command and the last field
  let cmd := (line.splitOn " ").headD ""
  if cmd == "nzt" then withTree (line.drop 4).toString fun c => showTree (Normalize.normalize 1000 c) else
  if cmd == "ivt" then withTree (line.drop 4).toString runInv else
  if cmd == "fl" then
    let rest := (line.drop 3).toString
    let nodesStr := (rest.splitOn " ").getLast!
    withTree (rest.dropEnd (nodesStr.length + 1)).toString fun c =>
      if decide (buildCond (parseNodes nodesStr) 0 = c) then "eq" else "ne" else
  match line.splitOn " " with
  | ["ev", value, allowances, hex, nodesStr] => runEval value allowances hex nodesStr
  | ["pk", nodesStr] =>
    let fs := (parseNodes nodesStr).toList.map fun n =>
      ({ parent := n.parent, paramType := toEncoding n.encoding, operator := toOperator n.operator,
         compValue := n.compValue } : ConditionPacking.Flat)
    hexOf (ConditionPacking.pack (fun _ => 0) fs)
  | ["up", hex] => showUnpacked (parseHex hex)
  | ["iv", nodesStr] => runInv (buildCond (parseNodes nodesStr) 0)
  | ["nz", nodesStr] => showCond (Normalize.normalize 1000 (buildCond (parseNodes nodesStr) 0))
  | ["ck", sStr, nodesStr] =>
    let ns := (parseNodes nodesStr).toList
    let fs? := ns.mapM fun n =>
      match ConditionPacking.encOf? n.encoding, ConditionPacking.opOf? n.operator with
      | some e, some o => some ({ parent := n.parent, paramType := e, operator := o,
                                  compValue := n.compValue } : ConditionPacking.Flat)
      | _, _ => none
    match fs? with
    | none => "none"
    | some fs =>
      match ConditionCheck.checkStored (sStr == "1") fs with
      | some (.typed t) => s!"ok {tyKey t}"
      | some .noCalldata => "ns"
      | none => "none"
  | ["bm", hex, loc, cv, inl, sz] =>
    toString (statusCode
      (bitmaskCheck (parseHex hex) loc.toNat! (parseHex cv) (inl == "1") sz.toNat! []))
  | [hex, loc, idx, nodesStr] =>
    let data := parseHex hex
    let nodes := (nodesStr.splitOn "|").toArray.map fun e =>
      match e.splitOn ":" with
      | [p, en, op, cv] => { parent := p.toNat!, encoding := en.toNat!, operator := op.toNat!,
                             compValue := parseHex cv : Flat }
      | _ => { parent := 0, encoding := 0, operator := 0, compValue := [] }
    let root := annotate (build nodes (nodes.size + 1) 0)
    let order := bfs root (nodes.size + 1) [root]
    let node := order.getD idx.toNat! default
    let l := loc.toNat!
    s!"{showLocs (children data l node)} {size data l node}"
  | _ => "bad-input"

def main : IO Unit := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  repeat
    let line ← stdin.getLine
    if line.isEmpty then break
    stdout.putStrLn (runLine line)
    stdout.flush
