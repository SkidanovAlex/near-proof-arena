import NearCompression.PackedBusRefinement
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


private def interaction (j : Json) : IO Interaction := do
  let bus ← need (← need (j.getObjVal? "bus")).getNat?
  let send ← need (← need (j.getObjVal? "send")).getBool?
  let msg ← need (← need (j.getObjVal? "msg")).getArr?
  let mult ← need (← need (j.getObjVal? "mult")).getArr?
  let messages ← msg.toList.mapM (fun e=>need (readExpr 128 e))
  let multiplicities ← mult.toList.mapM (fun e=>need (readExpr 128 e))
  let i : Interaction := { bus := bus, send := send, msg := messages, mult := multiplicities }
  if (← need (Json.parse i.toJson)) != j then throw (IO.userError "noncanonical interaction")
  return i
def main (args : List String) : IO Unit := do
  if args.length != 1 then throw (IO.userError "expected interaction pairs")
  let tasks ← need (← need (Json.parse (← IO.FS.readFile args[0]!))).getArr?
  let mut answers : Array Bool := #[]
  for task in tasks do
    let ti ← need (← need (task.getObjVal? "table")).getNat?
    if ti>1 then throw (IO.userError "invalid table")
    let regions := if ti==0 then packedExecRegions else packedCodeRegions
    let xs ← need (← need (task.getObjVal? "source")).getArr?
    let ys ← need (← need (task.getObjVal? "target")).getArr?
    answers := answers.push (packedInteractionsCheck regions
      (← xs.toList.mapM interaction) (← ys.toList.mapM interaction))
  IO.println (toJson answers).compress
