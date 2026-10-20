import NearCompression.BusChainFormulaLayout
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
  let cases := [0,1,24].map fun k=>Id.run do
    let power : BusProgramFormula Fp8:=.sub (.literal 5) (.current 0)
    let accumulator : BusProgramFormula Fp8:=.add (.literal 1) (.mul (.current 1) (.sub power (.literal 1)))
    let built:=buildBusChain power accumulator ((List.range k).map (fun i=>.current (2+i))) (2+k) (2+2*k)
    return Json.mkObj [("tail_bits",toJson k),("residuals",toJson ((built.squares++built.links).map encode))]
  IO.println (toJson cases).compress
