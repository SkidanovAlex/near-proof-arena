import NearCompression.SHA384PackedSourceBinding
import Lean
open NearCompression ZkFormal.Algebra Lean

def main (args : List String) : IO Unit := do
  let j ← match Json.parse (← IO.FS.readFile args[0]!) with |.ok x=>pure x|.error e=>throw (IO.userError e)
  let get (α : Type) [FromJson α] (key : String) : IO α :=
    match j.getObjValAs? α key with |.ok x=>pure x|.error e=>throw (IO.userError e)
  let source ← get (List (List Nat)) "source"
  let context ← get (List Nat) "context"
  let beta ← get (List (List Nat)) "beta"
  let samples ← get (List Nat) "samples"
  let depth ← get Nat "depth"
  let d ← get Nat "degree"
  unless 1≤depth && depth≤8 && source.length==2^depth && source.length==2*d &&
      context.all (·<256) && source.all (fun row=>row.length==2*beta.length && row.all (·<2013265921)) &&
      beta.all (fun v=>v.length==4 && v.all (·<2013265921)) do throw (IO.userError "canonical source fixture")
  let bytes:=source.map sha384FieldWords
  let ctx:=context.map UInt8.ofNat
  let root:=sha384SourceRoot sha384ChainDigest ctx bytes depth
  let mut results : Array Json := #[]
  for sample in samples do
    let index:=sample%(2*d)
    let values:=source.getD index []
    let path:=sha384TreePath sha384ChainDigest ctx bytes depth 0 index
    let mut coordinates : Array Json := #[]
    for k in [0,1] do
      let pair:=(List.range 4).map (fun component=>
        let weights:=beta.map (fun lane=>Fp.ofNat (lane.getD component 0))
        let result:=projectedBetaPair k d sample weights (sha384SourceWordPairs (K:=Fp) values)
        [result.1.toNat,result.2.toNat])
      coordinates:=coordinates.push (toJson pair)
    results:=results.push (Json.mkObj [("index",toJson index),("pairs",toJson coordinates),
      ("accepted",toJson (sha384VerifyPath sha384ChainDigest root ctx source.length index
        (sha384FieldWords values) path))])
  let first:=source.getD 0 []
  let firstPath:=sha384TreePath sha384ChainDigest ctx bytes depth 0 0
  let changedAccepted:=(List.range first.length).map (fun slot=>
    let changed:=first.set slot ((first.getD slot 0+1)%2013265921)
    sha384VerifyPath sha384ChainDigest root ctx source.length 0 (sha384FieldWords changed) firstPath)
  IO.FS.writeFile args[1]! (Json.mkObj [("root",toJson (root.map UInt8.toNat)),
    ("source_bytes",toJson (bytes.map (List.map UInt8.toNat))),("samples",toJson results),("changedAccepted",toJson changedAccepted)]).compress
