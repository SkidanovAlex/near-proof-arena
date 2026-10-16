import NearCompression.BusInteractionFormulaLayout
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
def main : IO Unit := do
  let cases := [0,1,2,25].map fun n=>Id.run do
    let power : BusProgramFormula Fp8:=.sub (.literal 5) (.current 0)
    let width:=1+n
    let bits:=((List.range n).map (fun i=>BusProgramFormula.current (1+i)))
    let residuals:=busInteractionResiduals power bits width (width+2*(n-1)) 7
    return Json.mkObj [("bits",toJson n),("residuals",toJson (residuals.map encode))]
  IO.println (toJson cases).compress
