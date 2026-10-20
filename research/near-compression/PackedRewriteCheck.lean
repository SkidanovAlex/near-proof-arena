import NearCompression.PackedConcreteRewrite
import ZkFormal.Air.Export
import Lean
open Lean NearCompression ZkFormal.Air
private def need (x : Except String α) : IO α :=
  match x with | .ok v => pure v | .error e => throw (IO.userError e)
private def readExpr : Nat → Json → Except String ZkFormal.Air.Expr
  | 0,_ => .error "expression nesting limit"
  | fuel+1,j => do
    let xs ← j.getArr?
    let tag ← (xs[0]?.getD Json.null).getStr?
    let arg (i : Nat) := xs[i]?.getD Json.null
    match tag with
    | "c" => pure (.const (←(arg 1).getNat?))
    | "p" => pure (.pub (←(arg 1).getNat?))
    | "v" => pure (.col (←(arg 1).getNat?) ((←(arg 2).getNat?)==1))
    | "first" => pure .isFirst
    | "last" => pure .isLast
    | "trans" => pure .isTransition
    | "+" => pure (.add (←readExpr fuel (arg 1)) (←readExpr fuel (arg 2)))
    | "*" => pure (.mul (←readExpr fuel (arg 1)) (←readExpr fuel (arg 2)))
    | "-" => pure (.neg (←readExpr fuel (arg 1)))
    | _ => throw "unknown expression"

def main (args : List String) : IO Unit := do
  if args.length != 1 then throw (IO.userError "expected expression input")
  let input ← need (Json.parse (← IO.FS.readFile args[0]!))
  let tables ← need input.getArr?
  if tables.size != 2 then throw (IO.userError "expected EXEC and CODE")
  let mut output : List String := []
  for ti in [0:2] do
    let regions := if ti==0 then packedExecRegions else packedCodeRegions
    let entries ← need tables[ti]!.getArr?
    let mut result : List String := []
    for entry in entries do
      let e ← need (readExpr 128 entry)
      let roundtrip ← need (Json.parse e.toJson)
      if roundtrip != entry then throw (IO.userError "noncanonical expression")
      result := result ++ [match packedRewrite (packedConcreteMacro regions)
        (packedConcreteColumn regions) e with
        | none => "null"
        | some e' => e'.toJson]
    output := output ++ [jsonList result]
  IO.println (jsonList output)
