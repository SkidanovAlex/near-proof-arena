import NearCompression.SHA384ComputedSource
import Lean
open NearCompression ZkFormal.Algebra Lean

def main (args : List String) : IO Unit := do
  let j ← match Json.parse (← IO.FS.readFile args[0]!) with | .ok x => pure x | .error e => throw (IO.userError e)
  let cases ← match j.getArr? with | .ok x => pure x | .error e => throw (IO.userError e)
  let mut results : Array Json := #[]
  for c in cases do
    let get (α : Type) [FromJson α] (key : String) : IO α :=
      match c.getObjValAs? α key with | .ok x => pure x | .error e => throw (IO.userError e)
    let n ← get Nat "n"
    let p ← get Nat "p"
    let width ← get Nat "width"
    let rows ← get (List (List Nat)) "rows"
    let omega ← get Nat "omega"
    let context ← get (List Nat) "context"
    unless n≤3 && p≤2 && width≤7 && rows.length==2^n &&
      rows.all (fun r=>r.length==width && r.all (·<2013265921)) &&
      context.all (·<256) do throw (IO.userError "fixture shape")
    let table:=fun r col=>Fp.ofNat ((rows.getD r []).getD col 0)
    let source:=sha384ComputedSource n p width table (Fp.ofNat omega)
    let coefficients:=(List.range ((width+2^p-1)/2^p)).map (fun lane=>
      (packedComputedCoefficients n p width lane table).map Fp.toNat)
    let root:=sha384SourceRoot sha384ChainDigest (context.map UInt8.ofNat)
      (source.map sha384FieldWords) (n+p+1)
    results:=results.push (Json.mkObj [("source",toJson source),("coefficients",toJson coefficients),
      ("root",toJson (root.map UInt8.toNat))])
  IO.FS.writeFile args[1]! (toJson results).compress
