import NearCompression.PackedByteMacro
import ZkFormal.Air.Export
import Lean

open Lean NearCompression ZkFormal.Air
private def need (x : Except String α) : IO α :=
  match x with | .ok v => pure v | .error e => throw (IO.userError e)

/-- Export theorem-backed AST pairs for externally supplied layout positions.
Matching these is an implementation check, not a kernel proof of Python. -/
def main (args : List String) : IO Unit := do
  if args.length != 1 then throw (IO.userError "expected macro-position JSON file")
  let input ← need (Json.parse (← IO.FS.readFile args[0]!))
  let positions ← need input.getArr?
  let mut pairs : List String := []
  for entry in positions do
    let xs ← need entry.getArr?
    if xs.size != 4 then throw (IO.userError "expected base, low, high, next")
    let base ← need xs[0]!.getNat?
    let lo ← need xs[1]!.getNat?
    let hi ← need xs[2]!.getNat?
    let nx ← need xs[3]!.getBool?
    pairs := pairs ++ [jsonList [(packedSourceLimb base nx).toJson,
      (packedTargetLimb lo hi nx).toJson]]
  IO.println (jsonList pairs)
