import NearCompression.DiagnosticExt4Polynomial
import Lean
open NearCompression ZkFormal.Algebra Lean

def main (args : List String) : IO Unit := do
  let j ← match Json.parse (← IO.FS.readFile args[0]!) with | .ok x=>pure x | .error e=>throw (IO.userError e)
  let cases ← match j.getArr? with | .ok x=>pure x | .error e=>throw (IO.userError e)
  let mut out : Array Json := #[]
  for c in cases do
    let get (α : Type) [FromJson α] (key : String) : IO α :=
      match c.getObjValAs? α key with | .ok x=>pure x | .error e=>throw (IO.userError e)
    let n ← get Nat "n"
    let p ← get Nat "p"
    let width ← get Nat "width"
    let rows ← get (List (List Nat)) "rows"
    let points ← get (List (List Nat)) "points"
    unless n≤3 && p≤2 && n+p≤4 && 0<width && width≤7 && rows.length==2^n &&
      rows.all (fun r=>r.length==width && r.all (·<2013265921)) && points.length≤12 &&
      points.all (fun x=>x.length==4 && x.all (·<2013265921)) do throw (IO.userError "bounded canonical fixture")
    let table:=fun r col=>diagnosticExt4Embed (Fp.ofNat ((rows.getD r []).getD col 0))
    let polys := (List.range ((width+2^p-1)/2^p)).map (fun lane=>packedComputedPolynomial n p width lane table)
    let evaluations := points.map (fun x=>
      let point:=diagnosticExt4ToTower ⟨Fp.ofNat (x.getD 0 0),Fp.ofNat (x.getD 1 0),Fp.ofNat (x.getD 2 0),Fp.ofNat (x.getD 3 0)⟩
      polys.map (fun f=>
        let value:=diagnosticExt4FromTower (f.eval point)
        [value.c0.toNat,value.c1.toNat,value.c2.toNat,value.c3.toNat]))
    out:=out.push (toJson evaluations)
  IO.FS.writeFile args[1]! (toJson out).compress
