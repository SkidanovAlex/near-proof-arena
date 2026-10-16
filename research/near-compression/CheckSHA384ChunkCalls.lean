import NearCompression.SHA384ChunkCallCheck
import Lean
open NearCompression ZkFormal.Algebra Lean

/-! Runtime regression driver for the proved checker, not a compression proof
or a commitment/operand-provenance verifier. -/
def main (args : List String) : IO Unit := do
  let input ← match Json.parse (← IO.FS.readFile args[0]!) with
    | .ok j=>pure j | .error e=>throw (IO.userError e)
  let cases ← match input.getArr? with
    | .ok xs=>pure xs | .error e=>throw (IO.userError e)
  let mut accepted := 0
  let mut rejected := 0
  for testcase in cases do
    let get {α : Type} [FromJson α] (key : String) : IO α :=
      match testcase.getObjValAs? α key with
      | .ok x=>pure x | .error e=>throw (IO.userError e)
    let name : String ← get "name"
    let rows : List (List Nat) ← get "rows"
    let message : List Nat ← get "message"
    let ordinals : List Nat ← get "ordinals"
    let blocks : List (List Nat) ← get "blocks"
    let final : List Nat ← get "final"
    let expected : Bool ← get "expected"
    unless rows.all (fun row=>row.length==179 && row.all (fun x=>x<P)) &&
      message.all (fun x=>x<256) && ordinals.length==blocks.length do
      throw (IO.userError s!"malformed regression case {name}")
    let nodes := rows.map (fun row=>row.getD 2 0)
    let payload := fun i j=>Fp.ofNat ((rows.getD i []).getD (3+j) 0)
    let result := checkChunkCall nodes payload (message.map UInt8.ofNat) (ordinals.zip blocks) final
    unless result==expected do throw (IO.userError s!"checker mismatch {name}: {result}")
    if result then accepted:=accepted+1 else rejected:=rejected+1
  IO.println (Json.mkObj [("status",toJson "PASS"),("accepted",toJson accepted),("rejected",toJson rejected)]).compress
