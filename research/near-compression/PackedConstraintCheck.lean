import NearCompression.PackedConstraintRefinement
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


private def canonicalExpr (j : Json) : IO ZkFormal.Air.Expr := do
  let e ← need (readExpr 128 j)
  if (← need (Json.parse e.toJson)) != j then throw (IO.userError "noncanonical expression")
  return e
private def readCert (j : Json) : IO PackedConstraintCert := do
  let xs ← need j.getArr?
  let tag ← need xs[0]!.getStr?
  match tag with
  | "retained" => return .retained (← canonicalExpr xs[1]!)
  | "boolean" => return .boolean (← need xs[1]!.getNat?)
  | "inactive" => return .inactive (← need xs[1]!.getNat?) (← need xs[2]!.getNat?)
  | _ => throw (IO.userError "unknown certificate")
def main (args : List String) : IO Unit := do
  if args.length != 1 then throw (IO.userError "expected certificate file")
  let input ← need (Json.parse (← IO.FS.readFile args[0]!))
  let tables ← need input.getArr?
  let mut results : Array Json := #[]
  for table in tables do
    let ti ← need (← need (table.getObjVal? "table")).getNat?
    if ti>1 then throw (IO.userError "invalid table")
    let regions := if ti==0 then packedExecRegions else packedCodeRegions
    let rawTarget ← need (← need (table.getObjVal? "target")).getArr?
    let target ← rawTarget.toList.mapM canonicalExpr
    let entries ← need (← need (table.getObjVal? "entries")).getArr?
    let mut answers : Array Bool := #[]
    for entry in entries do
      let xs ← need entry.getArr?
      let e ← canonicalExpr xs[0]!
      let cert ← readCert xs[1]!
      answers := answers.push (packedConstraintCertCheck regions target e cert)
    results := results.push (toJson answers)
  IO.println (Json.arr results).compress
