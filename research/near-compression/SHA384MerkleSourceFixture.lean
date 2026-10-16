import NearCompression.SHA384MerkleSource
import Lean
open NearCompression Lean

def main (args : List String) : IO Unit := do
  let j ← match Json.parse (← IO.FS.readFile args[0]!) with |.ok x=>pure x|.error e=>throw (IO.userError e)
  let rows ← match j.getArr? with |.ok x=>pure x|.error e=>throw (IO.userError e)
  let mut out : Array Json := #[]
  for row in rows do
    let get (α : Type) [FromJson α] (key : String) : IO α :=
      match row.getObjValAs? α key with |.ok x=>pure x|.error e=>throw (IO.userError e)
    let context ← get (List Nat) "context"
    let leaves ← get (List (List Nat)) "leaves"
    let depth ← get Nat "depth"
    unless 1≤depth && depth≤6 && leaves.length==2^depth &&
        (context::leaves).all (fun bs=>bs.all (·<256)) do throw (IO.userError "fixture shape")
    let ctx:=context.map UInt8.ofNat
    let source:=leaves.map (List.map UInt8.ofNat)
    let root:=sha384SourceRoot sha384ChainDigest ctx source depth
    let layers:=(List.range (depth+1)).map (fun level=>
      (List.range (2^(depth-level))).map (fun index=>
        (sha384TreeValue sha384ChainDigest ctx source level index).map UInt8.toNat))
    let paths:=(List.range source.length).map (fun index=>
      (sha384TreePath sha384ChainDigest ctx source depth 0 index).map (List.map UInt8.toNat))
    let accepted:=(List.range source.length).map (fun index=>sha384VerifyPath sha384ChainDigest root ctx source.length index
      (source.getD index []) (sha384TreePath sha384ChainDigest ctx source depth 0 index))
    let changedAccepted:=(List.range source.length).map (fun index=>sha384VerifyPath sha384ChainDigest root ctx source.length index
      ((source.getD index [])++[0]) (sha384TreePath sha384ChainDigest ctx source depth 0 index))
    out:=out.push (Json.mkObj [("root",toJson (root.map UInt8.toNat)),("layers",toJson layers),
      ("paths",toJson paths),("accepted",toJson accepted),("changedAccepted",toJson changedAccepted)])
  IO.FS.writeFile args[1]! (toJson out).compress
