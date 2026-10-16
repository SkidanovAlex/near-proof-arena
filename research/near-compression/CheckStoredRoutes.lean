import NearCompression.TerminalStoredRouteCheck
import NearCompression.DiagnosticExt4Embedding
import Lean
open Lean NearCompression ZkFormal.Algebra

private def need (x : Except String α) : IO α :=
  match x with | .ok a => pure a | .error e => throw (IO.userError e)
private def require (b : Bool) (msg : String) : IO Unit :=
  if b then pure () else throw (IO.userError msg)
private def field (j : Json) (k : String) : IO Json := need (j.getObjVal? k)
private def op (s : String) : IO GKRBinaryOp :=
  match s with
  | "add" => pure .add
  | "sub" => pure .sub
  | "mul" => pure .mul
  | _ => throw (IO.userError "unknown operation")
private def gate (j : Json) : IO GKRWiringGate := do
  let a ← need j.getArr?
  require (a.size==3) "gate arity"
  return ⟨←op (←need a[0]!.getStr?),←need a[1]!.getNat?,←need a[2]!.getNat?⟩
private def node (j : Json) : IO (TerminalDAGNode Fp4) := do
  let a ← need j.getArr?
  require (0<a.size) "empty node"
  let tag ← need a[0]!.getStr?
  if tag=="input" then
    require (a.size==2) "input arity"
    return .input (←need a[1]!.getNat?)
  else if tag=="const" then
    require (a.size==5) "constant arity"
    let xs ← (a.toList.drop 1).mapM (fun x => need x.getNat?)
    require (xs.all (· < 2013265921)) "noncanonical constant"
    return .constant ⟨⟨Fp.ofNat xs[0]!,Fp.ofNat xs[2]!⟩,⟨Fp.ofNat xs[1]!,Fp.ofNat xs[3]!⟩⟩
  else
    require (a.size==3) "binary arity"
    return .binary (←op tag) (←need a[1]!.getNat?) (←need a[2]!.getNat?)
private def placement (j : Json) (nodeCount : Nat) : IO (List Nat × List Nat) := do
  let obj ← need j.getObj?
  let mut live := []
  let mut positions := Array.replicate nodeCount 0
  for (key,value) in obj.toList do
    let some i := key.toNat? | throw (IO.userError "invalid node key")
    require (toString i==key && i<nodeCount) "noncanonical/out-of-range node key"
    live := i::live
    positions := positions.set! i (←need value.getNat?)
  return (live.reverse,positions.toList)

def main (args : List String) : IO Unit := do
  require (args.length==1) "expected certificate bundle path"
  let bundle ← need (Json.parse (←IO.FS.readFile args[0]!))
  let circuit ← field bundle "circuit"
  let layout ← field bundle "layout"
  let certificate ← field bundle "certificate"
  let nodes ← (←need (←field circuit "nodes").getArr?).toList.mapM node
  let (live,positions) ← placement (←field certificate "initial") nodes.length
  let layers ← need (←field layout "layers").getArr?
  let plans ← need (←field certificate "plans").getArr?
  require (layers.size==plans.size) "layer/plan count"
  let mut stages := []
  let mut gateCount := 0
  for i in List.range layers.size do
    let (ls,ps) ← placement plans[i]! nodes.length
    let gates ← (←need layers[i]!.getArr?).toList.mapM gate
    gateCount := gateCount+gates.length
    stages := stages++[⟨ls,ps,gates⟩]
  let inputSize ← need (←field layout "input_size").getNat?
  require (0<inputSize) "empty input"
  let root ← need (←field circuit "root").getNat?
  let rootSlot ← need (←field layout "root").getNat?
  let final := terminalLastPlacement live (fun i => positions.getD i 0) (stages.map (fun s => s.plan))
  require (final.1.contains root && final.2 root==rootSlot) "final root route"
  require (terminalStoredChainCheck nodes live (fun i => positions.getD i 0) (inputSize-1) stages)
    "stored route chain rejected"
  IO.println (Json.mkObj [("status",toJson "PASS"),("nodes",toJson nodes.length),
    ("layers",toJson stages.length),("gates",toJson gateCount),
    ("scope",toJson "Lean checker execution; not a kernel proof of this JSON instance")]).compress
