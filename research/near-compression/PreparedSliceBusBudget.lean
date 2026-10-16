import NearCompression.BusTraceMass
import NearCompression.PreparedLiteral
import Lean

open Lean NearCompression ZkFormal.Air ZkFormal.V2 ZkFormal.Algebra
private def need (x : Except String α) : IO α :=
  match x with | .ok v=>pure v | .error e=>throw (IO.userError e)
private def naturalList (j : Json) : IO (List Nat) := do
  let xs ← need j.getArr?
  xs.toList.mapM (fun x=>need x.getNat?)

def main (args : List String) : IO Unit := do
  let statement ← need (Json.parse (←IO.FS.readFile args[0]!))
  let spec ← need (statement.getObjVal? "spec")
  let logs ← naturalList (←need (spec.getObjVal? "log_rows"))
  let values ← naturalList (←need (spec.getObjVal? "public"))
  if !(values.all (·<ZkFormal.Algebra.P)) then throw (IO.userError "noncanonical public field")
  let pub:=values.map Fp.ofNat
  let air:=preparedLiteralAir ((values.length-66)/25)
  -- Budget uses only row heights, public records and literal descriptors.
  let tr : Trace Fp := {log:=fun t=>logs.getD t 0,cell:=fun _ _ _=>0}
  IO.println (Json.mkObj [
    ("support",toJson (busSupportSize tr air.tables 0+(pubMsgs air pub).length)),
    ("send_mass",toJson (busTableMass tr true air.tables 0+(busTracePublic air pub true).length)),
    ("receive_mass",toJson (busTableMass tr false air.tables 0+(busTracePublic air pub false).length)),
    ("numerator",toJson (busTraceErrorBudget air tr pub 28))]).compress
