import NearCompression.TerminalCompiledCheck
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
private def scalar (j : Json) : IO Fp4 := do
  let a ← need j.getArr?
  require (a.size==4) "constant width"
  let xs ← a.toList.mapM (fun x => need x.getNat?)
  require (xs.all (· < 2013265921)) "noncanonical constant"
  return ⟨⟨Fp.ofNat xs[0]!,Fp.ofNat xs[2]!⟩,⟨Fp.ofNat xs[1]!,Fp.ofNat xs[3]!⟩⟩
private def node (j : Json) : IO (TerminalDAGNode Fp4) := do
  let a ← need j.getArr?
  require (0<a.size) "empty node"
  let tag ← need a[0]!.getStr?
  if tag=="input" then
    require (a.size==2) "input arity"
    return .input (←need a[1]!.getNat?)
  else if tag=="const" then
    require (a.size==5) "constant arity"
    return .constant (←scalar (Json.arr (a.extract 1 5)))
  else
    require (a.size==3) "binary arity"
    return .binary (←op tag) (←need a[1]!.getNat?) (←need a[2]!.getNat?)

private def arithmetic (nodes : List (TerminalDAGNode Fp4)) (op : GKRBinaryOp)
    (x y z : Nat) : IO (TerminalArithmeticWitness Fp4) := do
  let constants := match nodes.getD x (.input 0),nodes.getD y (.input 0) with
    | .constant a,.constant b => [TerminalArithmeticWitness.constant a b]
    | _,_ => []
  let candidates := constants++[.direct,.addZeroLeft,.addZeroRight,.subZeroRight,.subSame,
    .mulZeroLeft,.mulZeroRight,.mulOneLeft,.mulOneRight]
  for w in candidates do
    if terminalStoredArithmeticCheck nodes op x y z w then return w
  throw (IO.userError "no valid arithmetic witness")

private partial def expansion (j : Json) : IO TerminalExpansionTree := do
  let a ← need j.getArr?
  require (a.size==3 || a.size==5) "expansion arity"
  let tag ← need a[0]!.getStr?
  let i ← need a[1]!.getNat?
  let s ← need a[2]!.getBool?
  if tag=="leaf" then
    require (a.size==3) "leaf arity"
    return .leaf i s
  require (tag=="branch" && a.size==5) "branch arity"
  return .branch i s (←expansion a[3]!) (←expansion a[4]!)

private def terms (j : Json) : IO (List (Nat × Bool)) := do
  (←need j.getArr?).toList.mapM fun t => do
    let a ← need t.getArr?
    require (a.size==2) "term arity"
    return (←need a[0]!.getNat?,←need a[1]!.getBool?)

private def passCert (nodes : List (TerminalDAGNode Fp4)) :
    List (Nat × Bool) → List (Nat × Bool) → IO (TerminalPassCertificate Fp4)
  | [],[] => pure .empty
  | [a],[c] => do
      require (a==c) "changed odd carry"
      return .singleton a
  | a::b::rest,c::out => do
      let kind := if a.2==b.2 then GKRBinaryOp.add else .sub
      let (x,y) := if a.2==b.2 || a.2 then (a.1,b.1) else (b.1,a.1)
      return .pair a b c (←arithmetic nodes kind x y c.1) (←passCert nodes rest out)
  | _,_ => throw (IO.userError "pass shape")

private def balanceStages (nodes : List (TerminalDAGNode Fp4)) (result : Nat) :
    List (List (Nat × Bool)) → IO (TerminalBalanceCertificate Fp4)
  | [[]] => pure (.empty result)
  | [[(x,true)]] => do
      require (x==result) "positive result"
      return .positive x
  | [[(x,false)]] => do
      let zeroNode := nodes.findIdx (fun n => n==.constant 0)
      return .negative x zeroNode result (←arithmetic nodes .sub zeroNode x result)
  | old::next::rest => do
      return .pass (←passCert nodes old next) (←balanceStages nodes result (next::rest))
  | _ => throw (IO.userError "unfinished balance")

private def balance (nodes : List (TerminalDAGNode Fp4)) (j : Json) : IO (TerminalBalanceCertificate Fp4) := do
  let stages ← (←need (←field j "stages").getArr?).toList.mapM terms
  balanceStages nodes (←need (←field j "result").getNat?) stages

/-- Diagnostic assignments only, not extracted committed inputs. -/
private def inputValue (seed slot : Nat) : Fp4 :=
  ⟨⟨Fp.ofNat ((slot+1)*(seed+1)),0⟩,⟨0,0⟩⟩

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

private structure ParsedProgram where
  environment : TerminalProgramEnvironment Fp4
  program : List (TerminalInstruction Fp4)
  records : List (TerminalRebuildRecord Fp4)
  root : Nat

private def checkProgram (target : List (TerminalDAGNode Fp4)) (seed : Nat) (p : Json) : IO (Nat × ParsedProgram) := do
  let ins ← need (←field p "instructions").getArr?
  require (0<ins.size) "empty program"
  let base ← need (←field p "base").getNat?
  let width ← need (←field p "column_capacity").getNat?
  let sels ← field p "selectors"
  let first ← scalar (←field sels "first")
  let last ← scalar (←field sels "last")
  let trans ← scalar (←field sels "trans")
  let env : TerminalProgramEnvironment Fp4 :=
    ⟨(fun i => inputValue seed (base+i)),(fun i => inputValue seed (base+width+i)),first,last,trans⟩
  let mut program : List (TerminalInstruction Fp4) := []
  for j in ins do
    let a ← need j.getArr?
    require (a.size==7) "instruction arity"
    let code ← need a[0]!.getNat?
    let some opcode := terminalDecodeOpcode code | throw (IO.userError "instruction opcode")
    let left ← need a[1]!.getNat?
    let right ← need a[2]!.getNat?
    if code==1 || code==2 then require (left<width) "column bound"
    program := ⟨opcode,left,right,←scalar (Json.arr (a.extract 3 7))⟩::program
  program := program.reverse
  let source := program.map (terminalProgramNode env)
  require (terminalAcyclicCheck 0 source) "source acyclicity"
  let entries ← need (←field p "records").getObj?
  let mut indexed : List (Nat × Json) := []
  let mut mapping := Array.replicate ins.size 0
  for (key,value) in entries.toList do
    let some i := key.toNat? | throw (IO.userError "invalid record key")
    require (toString i==key && i<ins.size) "record key bounds"
    let z ← need (←field value "node").getNat?
    mapping := mapping.set! i z
    indexed := (i,value)::indexed
  indexed := indexed.mergeSort (fun a b => a.1≤b.1)
  let mut records : List (TerminalRebuildRecord Fp4) := []
  for (i,r) in indexed do
    let a ← need ins[i]!.getArr?
    let code ← need a[0]!.getNat?
    let x ← need a[1]!.getNat?
    let y ← need a[2]!.getNat?
    let z := mapping[i]!
    let recipe ← if code==0 then pure (.constant (←scalar (Json.arr (a.extract 3 7))))
      else if code==1 || code==2 then pure (.input (base+x+(if code==2 then width else 0)))
      else if code==3 then pure (.constant first)
      else if code==4 then pure (.constant last)
      else if code==5 then pure (.constant trans)
      else if code==8 then do
        require (x<ins.size && y<ins.size) "binary index bounds"
        pure (.binary .mul x y mapping[x]! mapping[y]! (←arithmetic target .mul mapping[x]! mapping[y]! z))
      else pure (.expanded (←expansion (←field r "tree")) mapping.toList (←balance target (←field r "balance")))
    records := ⟨i,z,recipe⟩::records
  records := records.reverse
  let root ← need (←field p "root").getNat?
  require (terminalRebuildRecordsCheck source target (inputValue seed) [] records (ins.size-1) root)
    "rebuild records rejected"
  return (records.length,⟨env,program,records,root⟩)

def main (args : List String) : IO Unit := do
  require (args.length==4) "expected DAG bundle, rebuild capture, replay manifest, diagnostic seed"
  let some seed := args[3]!.toNat? | throw (IO.userError "invalid seed")
  let bundle ← need (Json.parse (←IO.FS.readFile args[0]!))
  let rebuild ← need (Json.parse (←IO.FS.readFile args[1]!))
  let circuit ← field bundle "circuit"
  let target ← (←need (←field circuit "nodes").getArr?).toList.mapM node
  require (terminalAcyclicCheck 0 target) "target acyclicity"
  let manifest ← need (Json.parse (←IO.FS.readFile args[2]!))
  let expected ← field manifest "expected_batch"
  let rho ← scalar (←field expected "rho")
  let weights ← need (←field expected "weights").getArr?
  let claims ← need (←field expected "claims").getArr?
  let outputs ← need (←field rebuild "outputs").getArr?
  let mut count := 0
  let mut entries : List (TerminalBatchEntry Fp4) := []
  let mut tables : List (TerminalCompiledTable Fp4) := []
  let programs ← need (←field rebuild "programs").getArr?
  require (outputs.size==programs.size && weights.size==programs.size && claims.size==programs.size) "batch count"
  for i in List.range programs.size do
    let (n,parsed) ← checkProgram target seed programs[i]!
    count := count+n
    let programRoot := parsed.root
    let out := outputs[i]!
    let wn ← need (←field out "weight").getNat?
    let cn ← need (←field out "claim").getNat?
    let pn ← need (←field out "power").getNat?
    let weighted ← need (←field out "node").getNat?
    let delta ← need (←field out "delta").getNat?
    let term ← need (←field out "batch_node").getNat?
    let entry : TerminalBatchEntry Fp4 := ⟨programRoot,←scalar weights[i]!,←scalar claims[i]!,wn,cn,pn,weighted,delta,term,
      ←arithmetic target .mul programRoot wn weighted,←arithmetic target .sub weighted cn delta,
      ←arithmetic target .mul pn delta term⟩
    entries := entry::entries
    tables := ⟨parsed.environment,parsed.program,parsed.program.length-1,parsed.records,entry⟩::tables
  entries := entries.reverse
  tables := tables.reverse
  require (terminalBatchEntriesCheck target rho 1 entries) "batch entries rejected"
  let finalBalance ← balance target (←field rebuild "balance")
  require (finalBalance.terms==entries.map (fun e => (e.termNode,true))) "batch terms mismatch"
  require (terminalBalanceCheck target finalBalance) "final balance rejected"
  let root ← need (←field rebuild "root").getNat?
  require (root==(←need (←field circuit "root").getNat?)) "circuit root mismatch"
  let zeroNode := target.findIdx (fun n => n==.constant 0)
  require (terminalBatchRootCheck target finalBalance.result root zeroNode) "final root rejected"
  require (0<programs.size) "no programs"
  let layout ← field bundle "layout"
  let certificate ← field bundle "certificate"
  let (live,positions) ← placement (←field certificate "initial") target.length
  let layers ← need (←field layout "layers").getArr?
  let plans ← need (←field certificate "plans").getArr?
  require (layers.size==plans.size) "layer/plan count"
  let mut stages : List TerminalStoredPlan := []
  for i in List.range layers.size do
    let (ls,ps) ← placement plans[i]! target.length
    let gates ← (←need layers[i]!.getArr?).toList.mapM gate
    stages := ⟨ls,ps,gates⟩::stages
  stages := stages.reverse
  let inputSize ← need (←field layout "input_size").getNat?
  require (0<inputSize) "empty input"
  let rootSlot ← need (←field layout "root").getNat?
  let capacity ← need (←field layout "private_capacity").getNat?
  let mut constants : Array Fp4 := Array.replicate inputSize 0
  for (key,value) in (←need (←field layout "constants").getObj?).toList do
    let some i := key.toNat? | throw (IO.userError "invalid constant key")
    require (toString i==key && capacity≤i && i<inputSize) "constant slot bounds"
    constants := constants.set! i (←scalar value)
  require (terminalCompiledFiniteCheck target (inputValue seed) (fun i => constants[i]?.getD 0)
    rho tables finalBalance root zeroNode capacity live positions (inputSize-1) stages rootSlot)
    "combined finite compiler check rejected"
  IO.println (Json.mkObj [("status",toJson "PASS"),("programs",toJson programs.size),
    ("records",toJson count),("seed",toJson seed),("batch_entries",toJson entries.length),
    ("scope",toJson "Native combined finite compiler check on diagnostic assignment and supplied replay manifest; excludes extraction, AIR compiler refinement, parser refinement and concrete kernel certificates")]).compress
