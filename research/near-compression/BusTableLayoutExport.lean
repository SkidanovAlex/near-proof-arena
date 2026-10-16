import NearCompression.BusTableFormulaLayout
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
  let profiles : List (List (Nat × Bool)) := [[],[(0,false)],[(1,true),(1,true),(1,false)],
    [(25,false),(1,true)],[(0,false),(2,true),(25,false),(1,true)],
    [(2,true),(0,false),(1,false),(25,true)]]
  let cases := profiles.map fun profile=>Id.run do
    let interactions : List (BusFormulaInteraction Fp8) := profile.zipIdx |>.map fun ((n,send),j)=>
      ⟨.sub (.literal 5) (.current j), (List.range n).map (fun i=>.current (4+i)), send⟩
    let bindings:=busTableBindings interactions 30 (fun j=>Fp8.ofBase (Fp.ofNat (7+j)))
    let residuals:=busTableResiduals interactions 30 (fun j=>Fp8.ofBase (Fp.ofNat (7+j)))
    return Json.mkObj [("profile",toJson (profile.map (fun (n,s)=>Json.mkObj [("bits",toJson n),("send",toJson s)]))),
      ("chain_columns",toJson (busTableChainColumns interactions)),
      ("offsets",toJson ((allocateBusInteractions interactions 30).map (fun a=>a.offset))),
      ("accumulators",toJson (bindings.map (fun b=>b.accumulator))),
      ("residuals",toJson (residuals.map encode))]
  IO.println (toJson cases).compress
