import NearCompression.SHA384SharedCore
import NearCompression.SHA512CombinedWitness
import Lean

/-! Configurable compression-certificate component, not a whole hash/call proof.
The caller must fix the ordered use-table commitment externally. -/
namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 NearSpecV3.SHA512
set_option maxRecDepth 65536

def chunkLog (n : Nat) : Nat := ((List.range 14).find? (fun l => n<2^l)).getD 14

def chunkGlobal (base : Nat) (message : List Expr) : List Expr :=
  .add (.const base) (message.headD (.const 0)) :: message.drop 1

def sha384NodeChunkAir (base count fanoutBits uses : Nat) : AirP :=
  let data := 2+fanoutBits
  let core : Table := {sha384SharedCore with
    maxLog := chunkLog (80*count)
    constraints:=sha384BatchCoreConstraints count
    interactions:=[
      ⟨0,[sha384BatchPhase 0],chunkGlobal base (sha384BatchState false),false⟩,
      ⟨1,[sha384BatchPhase 79],chunkGlobal base (sha384BatchState true),true⟩,
      ⟨2,[sha384BatchPhase 0],chunkGlobal base sha384BatchMessage,false⟩]}
  let endpoint : Table := {sha384SharedEndpoint with
    maxLog := chunkLog count
    constraints:=(List.range 8).flatMap (fun i=>instructionAdd64Constraints.map (sha512RelocateExpr (208*i))) ++ sharedPrefix 1665 1664 count
    interactions:=[
      ⟨0,[.col 1665 false],chunkGlobal base (sha384EndpointLimbMessage 0),false⟩,
      ⟨1,[.col 1665 false],chunkGlobal base (sha384EndpointLimbMessage 4),false⟩,
      ⟨3,[.col 1665 false],chunkGlobal base (sha384EndpointLimbMessage 8 ++ sha384EndpointDigestMessage),true⟩]}
  let records : Table := {
    width := data+176
    maxLog := chunkLog count
    constraints:=sharedPrefix 1 0 count ++ (List.range fanoutBits).flatMap (fun b=>
      [instructionBitConstraint (2+b),.mul (sharedSub (.const 1) (.col 1 false)) (.col (2+b) false)])
    interactions:=[
      ⟨0,[.const 0,.col 1 false],chunkGlobal base (.col 0 false::sharedCols data 32),true⟩,
      ⟨2,[.col 1 false],chunkGlobal base (.col 0 false::sharedCols (data+32) 64),true⟩,
      ⟨3,[.col 1 false],chunkGlobal base (.col 0 false::sharedCols (data+96) 80),false⟩,
      ⟨4,(List.range fanoutBits).map (fun b=>.col (2+b) false),chunkGlobal base (.col 0 false::sharedCols data 176),true⟩]}
  let useTable : Table := {
    width := 179
    maxLog := chunkLog uses
    constraints:=sharedPrefix 1 0 uses
    interactions:=[⟨4,[.col 1 false],sharedCols 2 177,false⟩]}
  {tables:=[core,endpoint,records,useTable],numBuses:=5,numPub:=0,maxPub:=0,pubSegs:=[]}
end NearCompression

open NearCompression ZkFormal.Air ZkFormal.Algebra NearSpecV3.SHA512 Lean
private def chunkLimbs (words : List Nat) : List Nat := words.flatMap fun w=>(List.range 4).map (fun l=>w/65536^l%65536)
private def chunkValues (v : Vars) : List Nat := [v.a,v.b,v.c,v.d,v.e,v.f,v.g,v.h]
private def writeRows (path : System.FilePath) (rows : Array (Array Nat)) : IO Unit :=
  IO.FS.writeFile path (Json.mkObj [("rows",toJson rows)]).compress

def main (args : List String) : IO Unit := do
  let input ← match Json.parse (← IO.FS.readFile args[0]!) with |.ok j=>pure j |.error e=>throw (IO.userError e)
  let parseNat (key : String) : IO Nat := match input.getObjValAs? Nat key with |.ok n=>pure n |.error e=>throw (IO.userError e)
  let base ← parseNat "base"
  let count ← parseNat "count"
  let bits ← parseNat "fanout_bits"
  let nodes ← match input.getObjValAs? (List (List Nat)) "nodes" with |.ok n=>pure n |.error e=>throw (IO.userError e)
  let uses ← match input.getObjValAs? (List Nat) "uses" with |.ok n=>pure n |.error e=>throw (IO.userError e)
  unless 0<count && count<=25 && base+count<P && 0<bits && bits<=13 && 0<uses.length && uses.length<8192 && nodes.length==count do
    throw (IO.userError "bounded chunk config")
  unless uses.all (fun i=>base<=i && i<base+count) do throw (IO.userError "use global ID outside interval")
  unless nodes.all (fun ns=>ns.length==144) do throw (IO.userError "node must contain8 initial words,128 block bytes,8 output words")
  let out := System.FilePath.mk args[1]!
  IO.FS.createDirAll out
  let mut core : Array (Array Nat) := #[]
  let mut endpoints : Array (Array Nat) := #[]
  let mut records : Array (Array Nat) := #[]
  let mut nodeFields : Array (List Nat) := #[]
  for nodeLocal in List.range count do
    let ns := nodes[nodeLocal]!
    let initial := ns.take 8
    let block := (ns.drop 8).take 128
    let output := ns.drop 136
    unless initial.all (fun v=>v<2^64) && output.all (fun v=>v<2^64) && block.all (fun v=>v<256) do throw (IO.userError "noncanonical node bytes/words")
    unless compress initial block == output do throw (IO.userError "actual node compression mismatch")
    let fanout := (uses.filter (fun i=>i==base+nodeLocal)).length
    unless fanout<2^bits do throw (IO.userError "fanout capacity")
    let mut state := ofList initial
    let mut window := words block
    let mut finalEp : Array Nat := #[]
    for phase in List.range 80 do
      let key := K.getD phase 0
      let row := ((List.range 5152).map (sha512CombinedWitnessRow state window key)).toArray
      core := core.push ((row.map Fp.toNat) ++ ((List.range 80).map (fun i=>if i=phase then 1 else 0)).toArray ++ #[1,nodeLocal])
      if phase==79 then
        let terminal := chunkValues (sha512CombinedOutput (fun c=>row[c]?.getD 0))
        finalEp := ((List.range 1664).map (fun c=>(instructionAdd64Witness
          (UInt64.ofNat (initial.getD (c/208) 0)) (UInt64.ofNat (terminal.getD (c/208) 0)) (c%208)).toNat)).toArray
      state := round state key (window.headD 0)
      window := nextWindow window
    let data := chunkLimbs initial ++ chunkLimbs (words block) ++ chunkLimbs output ++ ((digestBytes output).take 48).map UInt8.toNat
    nodeFields := nodeFields.push data
    endpoints := endpoints.push (finalEp ++ #[nodeLocal,1])
    records := records.push (([nodeLocal,1] ++ (List.range bits).map (fun b=>fanout/2^b%2) ++ data).toArray)
  let mut useRows : Array (Array Nat) := #[]
  for i in List.range uses.length do
    let node := uses[i]!
    useRows := useRows.push (([i,1,node] ++ nodeFields[node-base]!).toArray)
  let air := sha384NodeChunkAir base count bits uses.length
  let logs := [chunkLog (80*count),chunkLog count,chunkLog count,chunkLog uses.length]
  let traces := [core,endpoints,records,useRows]
  for t in List.range 4 do
    let width := air.tables[t]!.width
    let rows := traces[t]! ++ Array.replicate (2^(logs[t]!)-(traces[t]!).size) (Array.replicate width 0)
    writeRows (out/s!"source-{if t<10 then "0" else ""}{t}-rows.json") rows
  IO.FS.writeFile (out/"spec.json") ("{\"air\":"++air.exportJson++",\"public\":[],\"log_rows\":"++(toJson logs).compress++"}")
  IO.println s!"PASS canonical chunk witness: {count} nodes, {uses.length} ordered uses; no hash-call routing claim"
