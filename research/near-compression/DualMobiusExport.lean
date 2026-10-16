import NearCompression.DualMobiusWeights
import ZkFormal.Air.Export
open NearCompression ZkFormal.Algebra ZkFormal.Air

def main : IO Unit := do
  let mut cases : List String := []
  for n in List.range 9 do
    for seed in List.range 4 do
      let point := (List.range n).map (fun i => Fp.ofNat
        (if seed=0 then 0 else if seed=1 then 1 else if seed=2 then P-1 else 17+31*i))
      let vs := (List.range (2^n)).map (fun i => Fp.ofNat (i*i+19*i+7))
      let v := fun i => vs.getD i 0
      let u := fun i => point.getD i 0
      let encode := fun xs : List Fp => jsonList (xs.map (fun x => toString x.toNat))
      let table := fun f : Nat → Fp => encode ((List.range (2^n)).map f)
      cases := cases ++ [jsonList [toString n,encode point,encode vs,
        table (mobiusCoefficients n v),table (upperZeta n (rowEqualityWeight n u)),
        table (upperZeta n (cyclicRowWeight n u)),
        toString (genericRowMLE n v u).toNat,toString (genericRowNextMLE n v u).toNat]]
  IO.println (jsonList cases)
