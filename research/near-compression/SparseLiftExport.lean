import NearCompression.SparseLiftMLE
import ZkFormal.Air.Export
import ZkFormal.Algebra.Fp
open NearCompression ZkFormal.Algebra ZkFormal.Air

def main : IO Unit := do
  let mut cases : List String := []
  for n in List.range 5 do
    for k in List.range 5 do
      for seed in List.range 3 do
        let point := (List.range (n+k)).map (fun i => Fp.ofNat
          (if seed=0 then 0 else if seed=1 then 1 else 17+31*i))
        let cs := (List.range (2^n)).map (fun i => Fp.ofNat (i*i+19*i+7))
        let ws := (List.range (2^n)).map (fun i => Fp.ofNat (3*i*i+11*i+2))
        let c := fun i => cs.getD i 0
        let w := fun i => ws.getD i 0
        let u := fun i => point.getD i 0
        let encode := fun xs : List Fp => jsonList (xs.map (fun x => toString x.toNat))
        cases := cases ++ [jsonList [toString n,toString k,encode point,encode cs,encode ws,
          encode ((List.range (2^(k+n))).map (sparseLowLift k c)),
          encode ((List.range (2^(k+n))).map (repeatLowWeights k w)),
          toString (genericRowMLE (k+n) (sparseLowLift k c) u).toNat,
          toString (genericRowMLE (k+n) (repeatLowWeights k w) u).toNat,
          toString (lowZeroFactor k u).toNat]]
  IO.println (jsonList cases)
