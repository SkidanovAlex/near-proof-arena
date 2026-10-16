import ZkFormal.V2.Export
import ZkFormal.V2.VerifierDefs
import Lean

open Lean ZkFormal.Air ZkFormal.V2 ZkFormal.Algebra
namespace NearCompression
private def field (j : Json) (key : String) : Except String Json := j.getObjVal? key
private def natField (j : Json) (key : String) : Except String Nat := do (←field j key).getNat?
private def listField (j : Json) (key : String) : Except String (List Json) := do pure (←(←field j key).getArr?).toList
private def naturalList (j : Json) : Except String (List Nat) := do
  (←j.getArr?).toList.mapM Json.getNat?
/-- Bounded executable parser only; no claim of a verified wire codec. -/
private def readExpr : Nat → Json → Except String ZkFormal.Air.Expr
  | 0,_ => .error "expression nesting limit"
  | fuel+1,j => do
    let xs ← j.getArr?
    let tag ← (xs[0]?.getD Json.null).getStr?
    let arg (i : Nat) := xs[i]?.getD Json.null
    match tag with
    | "c" => pure (.const (←(arg 1).getNat?))
    | "p" => pure (.pub (←(arg 1).getNat?))
    | "v" => pure (.col (←(arg 1).getNat?) ((←(arg 2).getNat?)==1))
    | "first" => pure .isFirst
    | "last" => pure .isLast
    | "trans" => pure .isTransition
    | "+" => pure (.add (←readExpr fuel (arg 1)) (←readExpr fuel (arg 2)))
    | "*" => pure (.mul (←readExpr fuel (arg 1)) (←readExpr fuel (arg 2)))
    | "-" => pure (.neg (←readExpr fuel (arg 1)))
    | _ => throw "unknown expression"
private def readInteraction (j : Json) : Except String Interaction := do
  return {
    bus:= ←natField j "bus",send:= ←(←field j "send").getBool?,
    mult:= ←(←listField j "mult").mapM (readExpr 128),msg:= ←(←listField j "msg").mapM (readExpr 128)}
private def readTable (j : Json) : Except String Table := do
  return {
    width:= ←natField j "width",maxLog:= ←natField j "maxLog",
    constraints:= ←(←listField j "constraints").mapM (readExpr 128),
    interactions:= ←(←listField j "interactions").mapM readInteraction}
private def optionalNat (j : Json) : Except String (Option Nat) :=
  if j == Json.null then .ok none else j.getNat?.map some
private def readSegment (j : Json) : Except String PubSeg := do
  return {
    bus:= ←natField j "bus",send:= ←(←field j "send").getBool?,
    width:= ←natField j "width",countAt:= ←natField j "countAt",start:= ←natField j "start",
    startAt:= ←optionalNat (←field j "startAt"),indexBase:= ←optionalNat (←field j "indexBase"),
    msgPrefix:= ←naturalList (←field j "prefix")}
private def readAir (j : Json) : Except String AirP := do
  return {
    tables:= ←(←listField j "tables").mapM readTable,numBuses:= ←natField j "numBuses",
    numPub:= ←natField j "numPub",maxPub:= ←natField j "maxPub",pubSegs:= ←(←listField j "pubSegs").mapM readSegment}
private def replay (j : Json) : Except String Json := do
  let label ← (←field j "label").getStr?
  let spec ← field j "spec"
  let air ← readAir (←field spec "air")
  let logs ← naturalList (←field spec "log_rows")
  let pub := (←naturalList (←field spec "public")).map Fp.ofNat
  let rows ← (←listField j "rows_by_table").mapM fun table=>do
    (←table.getArr?).toList.mapM naturalList
  let tr : Trace Fp := {
    log:=fun t=>logs.getD t 0,
    cell:=fun t r c=>Fp.ofNat (((rows.getD t []).getD r []).getD c 0)}
  let residuals := air.tables.zipIdx.map fun ((table,ti) : Table × Nat)=>
    (List.range (tr.height ti)).map fun r=>table.constraints.map fun (e : ZkFormal.Air.Expr)=>(e.eval tr ti r pub).toNat
  let interactions := air.tables.zipIdx.map fun ((table,ti) : Table × Nat)=>
    (List.range (tr.height ti)).map fun r=>table.interactions.map fun (i : Interaction)=>Json.mkObj [
      ("bits",toJson (i.mult.map fun (e : ZkFormal.Air.Expr)=>(e.eval tr ti r pub).toNat)),
      ("multiplicity",toJson (i.multNat tr ti r pub)),("message",toJson ((i.msgVal tr ti r pub).map Fp.toNat))]
  let publicMessages := (pubMsgs air pub).map fun (b,s,m)=>Json.arr #[toJson b,toJson s,toJson (m.map Fp.toNat)]
  let automaticResiduals := air.tables.zipIdx.map fun ((table,ti) : Table × Nat)=>
    (List.range (tr.height ti)).map fun r=> (table.allConstraints.drop table.constraints.length).map fun (e : ZkFormal.Air.Expr)=>(e.eval tr ti r pub).toNat
  pure (Json.mkObj [("label",toJson label),("residuals",toJson residuals),
    ("interactions",toJson interactions),("public_messages",toJson publicMessages),
    ("automatic_multiplicity_residuals",toJson automaticResiduals),("public_fits",toJson (pubFit air pub))])
end NearCompression

def main (args : List String) : IO Unit := do
  let input ← IO.FS.readFile (args.headD "/tmp/near-prepared-code-table/source-parity-input.json")
  let result := do
    let j ← Json.parse input
    let cases ← j.getArr?
    cases.toList.mapM NearCompression.replay
  match result with
  | .error e => throw (IO.userError e)
  | .ok results => IO.println (toJson results).compress
