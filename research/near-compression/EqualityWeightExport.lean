import NearCompression.EqualityWeightResidual
import NearCompression.WeightedSumcheckTerminal
import ZkFormal.Air.Export
open NearCompression ZkFormal.Algebra ZkFormal.Air

def main : IO Unit := do
  let mut cases : List String := []
  for n in List.range 11 do
    for seed in List.range 5 do
      let point := (List.range n).map (fun i => Fp.ofNat
        (if seed=0 then 0 else if seed=1 then 1 else if seed=2 then
          (if i%2=0 then 0 else 1) else if seed=3 then P-1 else 17+31*i))
      let coefficients := (List.range (2^n)).map (fun i => Fp.ofNat (i*i+19*i+7))
      let weights := equalityWeights point
      let residual := scalarRSResidual weights (Poly.mk coefficients)
      let mle := genericRowMLE n (fun i => coefficients.getD i 0) (fun i => point.getD i 0)
      cases := cases ++ [jsonList [jsonList (point.map (fun x => toString x.toNat)),
        jsonList (weights.map (fun x => toString x.toNat)),toString residual.toNat,toString mle.toNat]]
  IO.println (jsonList cases)
