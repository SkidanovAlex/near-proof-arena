import NearCompression.SHA384PackingContext
import Lean
open NearCompression Lean

def main (args : List String) : IO Unit := do
  let j ← match Json.parse (← IO.FS.readFile args[0]!) with |.ok x=>pure x|.error e=>throw (IO.userError e)
  let rows : List (Nat × Nat × Nat) ← match fromJson? j with |.ok x=>pure x|.error e=>throw (IO.userError e)
  let mut out : Array Json := #[]
  for (n,w,p) in rows do
    let valid := @decide (SHA384PackingFits n w p) (by unfold SHA384PackingFits; infer_instance)
    out:=out.push (Json.mkObj [("valid",toJson valid),("bytes",toJson
      (if valid then (sha384PackingContext n w p).map UInt8.toNat else []))])
  IO.FS.writeFile args[1]! (toJson out).compress
