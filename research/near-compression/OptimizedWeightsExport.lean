import NearCompression.DualBorrowWeightMLE
import NearCompression.UpperZetaBitPass
import ZkFormal.Air.Export
open NearCompression ZkFormal.Algebra ZkFormal.Air

def main : IO Unit := do
  let mut cases : List String := []
  let encode := fun xs : List Fp => jsonList (xs.map (fun x => toString x.toNat))
  for n in List.range 6 do
    for seed in List.range 4 do
      let point := (List.range n).map (fun i => Fp.ofNat
        (if seed=0 then 0 else if seed=1 then 1 else if seed=2 then P-1 else 17+31*i))
      let values := (List.range (2^n)).map (fun i => Fp.ofNat (i*i+19*i+7))
      for mode in List.range 3 do
        let u := (List.range n).map (fun i => Fp.ofNat (if mode=0 then 0 else if mode=1 then 1 else 71+13*i))
        let coords := point.zip u
        cases := cases ++ [jsonList [toString n,encode point,encode u,encode values,
          encode (upperZetaMutableList n values),
          toString (currentWeightAccumulator coords 1).toNat,
          toString (dualBorrowDP coords 0 1).toNat]]
  IO.println (jsonList cases)
