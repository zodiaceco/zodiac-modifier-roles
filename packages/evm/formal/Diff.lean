import DecoderFaithfulness.Roles

/-!
Differential-testing driver for the Roles transcription (`DecoderFaithfulness/Roles.lean`).

Reads one query per line on stdin:

    <calldata hex> <location> <node index> <nodes>

`<nodes>` is the flat BFS tree as `parent:encoding:operator:compValueHex`
entries joined by `|` (`ConditionFlat[]`, enum values as in Solidity).
For the node at `<node index>` (BFS order, after pack/unpack) it prints

    <children result> <size result>

where the children result is `none` (overflow) or comma-separated locations
(`-` for an empty list). Used by `test/formal/lean-model.spec.ts`.
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

def runLine (line : String) : String :=
  match ((line.splitOn "\n").headD "").splitOn " " with
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
