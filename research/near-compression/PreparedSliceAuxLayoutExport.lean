import NearCompression.BusSourceFormulaLowering
import NearCompression.PreparedLiteral
import ZkFormal.Algebra.Fp8
import Lean
open Lean NearCompression ZkFormal.Algebra
private def encode : BusProgramFormula Fp8→Json
  | .literal x=>toJson ([toJson "c",toJson (Fp8.toList x |>.map Fp.toNat)] : List Json)
  | .current c=>toJson ([toJson "v",toJson c] : List Json)
  | .next c=>toJson ([toJson "next",toJson c] : List Json)
  | .first=>toJson ([toJson "first"] : List Json)
  | .last=>toJson ([toJson "last"] : List Json)
  | .transition=>toJson ([toJson "trans"] : List Json)
  | .add a b=>toJson ([toJson "+",encode a,encode b] : List Json)
  | .sub a b=>toJson ([toJson "-",encode a,encode b] : List Json)
  | .mul a b=>toJson ([toJson "*",encode a,encode b] : List Json)
private def need {α : Type} (x : Except String α) : IO α :=
  match x with | .ok v=>pure v | .error e=>throw (IO.userError e)
def main (args : List String) : IO Unit := do
  let statement ← need (Json.parse (←IO.FS.readFile args[0]!))
  let spec ← need (statement.getObjVal? "spec")
  let values ← need ((←need (spec.getObjVal? "public")).getArr?)
  let pubNats ← values.toList.mapM (fun x=>need x.getNat?)
  let pubValues:=pubNats.map (fun n=>Fp8.ofBase (Fp.ofNat n))
  let air:=preparedLiteralAir ((pubNats.length-66)/25)
  let cases := air.tables.zipIdx |>.flatMap fun (table,t)=>[0,1,7].map fun a=>Id.run do
    let alpha:=Fp8.ofBase (Fp.ofNat a)
    let interactions:=table.interactions.map (lowerBusInteraction pubValues alpha 5)
    let residuals:=busTableResiduals interactions table.width (fun j=>Fp8.ofBase (Fp.ofNat (7+j)))
    return Json.mkObj [("table",toJson t),("alpha",toJson a),
      ("chain_columns",toJson (busTableChainColumns interactions)),
      ("residuals",toJson (residuals.map encode))]
  IO.println (toJson cases).compress
