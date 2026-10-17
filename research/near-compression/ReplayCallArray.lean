import NearCompression.CallArrayCompilation
import NearCompression.SHA384CallLinear
import Lean
open NearCompression ZkFormal.Algebra Lean

/-! Regression replay of four base-field coordinates. This is not a proof of
Python execution or an extension-field multiplication implementation. -/
def main (args : List String) : IO Unit := do
  let input ← match Json.parse (← IO.FS.readFile args[0]!) with
    | .ok j => pure j | .error e => throw (IO.userError e)
  let get {α : Type} [FromJson α] (key : String) : IO α :=
    match input.getObjValAs? α key with
    | .ok x => pure x | .error e => throw (IO.userError e)
  let capacity : Nat ← get "capacity"
  let equations : List (List Nat) ← get "equations"
  let weights : List (List Nat) ← get "weights"
  unless equations.length==weights.length do throw (IO.userError "weight count")
  let mut outputs : List (List Nat × Nat) := []
  for coordinate in List.range 4 do
    let batch := (equations.zip weights).map fun (e,w) =>
      (Fp.ofNat (w[coordinate]!),
       ({left:=e[0]!,right:=if e[1]! == 0 then none else some e[2]!,value:=Fp.ofNat e[3]!} : CallBatchEquation Fp))
    let result:=callArrayRun batch (Array.replicate capacity (Fp.ofNat 0),Fp.ofNat 0)
    outputs:=outputs++[(result.1.toList.map Fp.toNat,result.2.toNat)]
  IO.FS.writeFile args[1]! (toJson outputs).compress
  IO.println s!"PASS replayed {equations.length} equations in four coordinates"
