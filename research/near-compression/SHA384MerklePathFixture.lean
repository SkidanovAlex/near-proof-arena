import NearCompression.SHA384MerklePath
import Lean
open NearCompression Lean

def main (args : List String) : IO Unit := do
  let j ← match Json.parse (← IO.FS.readFile args[0]!) with |.ok x=>pure x|.error e=>throw (IO.userError e)
  let rows ← match j.getArr? with |.ok x=>pure x|.error e=>throw (IO.userError e)
  let mut out : Array Json := #[]
  for row in rows do
    let get (α : Type) [FromJson α] (key : String) : IO α :=
      match row.getObjValAs? α key with |.ok x=>pure x|.error e=>throw (IO.userError e)
    let root ← get (List Nat) "root"
    let context ← get (List Nat) "context"
    let leaf ← get (List Nat) "leaf"
    let path ← get (List (List Nat)) "path"
    let count ← get Nat "count"
    let index ← get Nat "index"
    unless (root::context::leaf::path).all (fun bs=>bs.all (·<256)) do throw (IO.userError "noncanonical byte")
    let accepted:=sha384VerifyPath sha384ChainDigest (root.map UInt8.ofNat) (context.map UInt8.ofNat)
      count index (leaf.map UInt8.ofNat) (path.map (List.map UInt8.ofNat))
    let queries:=sha384MerklePathQueries sha384ChainDigest (context.map UInt8.ofNat)
      count index (leaf.map UInt8.ofNat) (path.map (List.map UInt8.ofNat))
    out:=out.push (Json.mkObj [("accepted",toJson accepted),("queries",toJson (queries.map (List.map UInt8.toNat)))])
  IO.FS.writeFile args[1]! (toJson out).compress
