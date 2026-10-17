import NearCompression.CallSourceOpening
import NearCompression.DiagnosticExt4Embedding
import Lean
open Lean NearCompression ZkFormal.Algebra
private def need (x : Except String α) : IO α :=
  match x with | .ok a => pure a | .error e => throw (IO.userError e)
private def require (b : Bool) (msg : String) : IO Unit :=
  if b then pure () else throw (IO.userError msg)
private def field (j : Json) (k : String) : IO Json := need (j.getObjVal? k)
private def scalar (j : Json) : IO Fp4 := do
  let a ← need j.getArr?
  require (a.size==4) "constant width"
  let xs ← a.toList.mapM (fun x => need x.getNat?)
  require (xs.all (· < 2013265921)) "noncanonical constant"
  return ⟨⟨Fp.ofNat xs[0]!,Fp.ofNat xs[2]!⟩,⟨Fp.ofNat xs[1]!,Fp.ofNat xs[3]!⟩⟩


private def flat (x : Fp4) : List Nat := [x.a.a.toNat,x.b.a.toNat,x.a.b.toNat,x.b.b.toNat]
def main (args : List String) : IO Unit := do
  let input ← need (Json.parse (←IO.FS.readFile args[0]!))
  let rowLog ← need (←field input "row_log").getNat?
  let columnLog ← need (←field input "column_log").getNat?
  let width ← need (←field input "width").getNat?
  let rows ← (←need (←field input "rows").getArr?).toList.mapM fun j=>do
    (←need j.getArr?).toList.mapM (fun x=>need x.getNat?)
  require (rows.length==2^rowLog && rows.all (fun row=>row.length==width && row.all (· <2013265921))) "source shape"
  let table := fun r c=>diagnosticExt4Embed (Fp.ofNat ((rows.getD r []).getD c 0))
  let mut known : Array Fp4 := Array.replicate (2^(rowLog+columnLog)) 0
  for j in (←need (←field input "constants").getArr?).toList do
    let pair ← need j.getArr?
    require (pair.size==2) "constant entry"
    let index ← need pair[0]!.getNat?
    require (index<known.size) "constant bounds"
    known:=known.set! index (←scalar pair[1]!)
  let mut result : List Json := []
  for j in (←need (←field input "queries").getArr?).toList do
    let point ← (←need (←field j "point").getArr?).toList.mapM scalar
    let scale ← scalar (←field j "scale")
    require (point.length==rowLog+columnLog) "point dimensions"
    let atPoint:=fun i=>point.getD i 0
    let coefficients:=(List.range width).map (fun c=>scale*rowEqualityWeight columnLog (fun i=>atPoint (rowLog+i)) c)
    let privateValues:=genericPackedValues rowLog columnLog width 0 table
    let source:=scale*callSourceFunctional rowLog columnLog width table atPoint
    let privateMLE:=scale*genericRowMLE (rowLog+columnLog) privateValues atPoint
    let knownMLE:=scale*genericRowMLE (rowLog+columnLog) (fun i=>known[i]?.getD 0) atPoint
    let fullMLE:=scale*genericRowMLE (rowLog+columnLog) (fun i=>privateValues i+known[i]?.getD 0) atPoint
    require (source==privateMLE && fullMLE==source+knownMLE) "source identity"
    result:=result++[Json.mkObj [("coefficients",toJson (coefficients.map flat)),
      ("source",toJson (flat source)),("known",toJson (flat knownMLE)),("full",toJson (flat fullMLE))]]
  IO.FS.writeFile args[1]! (toJson result).compress
  IO.println s!"PASS source opening replay: {result.length} queries"
