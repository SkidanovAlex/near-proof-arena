import NearCompression.SHA384CallEquations
import Lean
open NearCompression NearSpecV3.SHA512 Lean

/-! Export exact descriptors from independently padded positive call fixtures.
This is a regression exporter, not a verifier of compression or provenance. -/
def main (args : List String) : IO Unit := do
  let input ← match Json.parse (←IO.FS.readFile args[0]!) with
    | .ok j=>pure j | .error e=>throw (IO.userError e)
  let cases ← match input.getArr? with
    | .ok xs=>pure xs | .error e=>throw (IO.userError e)
  let rows ← match args[2]!.toNat? with
    | some n=>pure n | none=>throw (IO.userError "row count")
  let mut result : List (List Nat) := []
  for testcase in cases do
    let get {α : Type} [FromJson α] (key : String) : IO α :=
      match testcase.getObjValAs? α key with
      | .ok x=>pure x | .error e=>throw (IO.userError e)
    let positive : Bool ← get "expected"
    if positive then
      let message : List Nat ← get "message"
      let ordinals : List Nat ← get "ordinals"
      let final : List Nat ← get "final"
      unless message.all (fun x=>x<256) && ordinals.all (fun x=>x<rows) &&
        final.length==8 && final.all (fun x=>x<2^64) do
        throw (IO.userError "canonical fixture")
      let padded := pad ((message.map UInt8.ofNat).map UInt8.toNat)
      unless padded.length==128*ordinals.length do throw (IO.userError "block count")
      let blocks := (List.range ordinals.length).map (fun i=>(padded.drop (128*i)).take 128)
      let eqs := callEquations rows (ordinals.zip blocks) ((digestBytes final).take 48)
      result:=result++eqs.map (fun e=>[e.left,if e.right.isSome then 1 else 0,e.right.getD 0,e.value])
  IO.FS.writeFile args[1]! (toJson result).compress
  IO.println s!"PASS exported {result.length} call equations"
