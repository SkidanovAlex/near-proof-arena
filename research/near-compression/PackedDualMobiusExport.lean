import NearCompression.PackedDualMobiusWeights
import ZkFormal.Air.Export
open NearCompression ZkFormal.Algebra ZkFormal.Air

def main : IO Unit := do
  let mut cases : List String := []
  for n in List.range 4 do
    for p in List.range 4 do
      for mode in List.range 3 do
        let width := max 1 (2^p-1)
        let point := (List.range n).map (fun i => Fp.ofNat (if mode=0 then 0 else if mode=1 then 1 else 17+31*i))
        let u := (List.range (n+p)).map (fun i => Fp.ofNat (if mode=0 then 1 else if mode=1 then 0 else 53+19*i))
        let a := fun c => if c<width then Fp.ofNat (7+3*c) else 0
        let b := fun c => if c<width then Fp.ofNat (11+5*c) else 0
        let values := fun r c => if c<width then Fp.ofNat (r*r+19*r+7*c+13*r*c) else 0
        let weights := packedDualWeight n p (fun i => point.getD i 0) a b
        let coeff := mobiusCoefficients (n+p) (fun i => values (i%2^n) (i/2^n))
        let encode := fun xs : List Fp => jsonList (xs.map (fun x => toString x.toNat))
        let table := fun f : Nat → Fp => encode ((List.range (2^(n+p))).map f)
        cases := cases ++ [jsonList [toString n,toString p,toString width,encode point,encode u,
          encode ((List.range (2^p)).map a),encode ((List.range (2^p)).map b),
          table weights,table coeff,toString (cubeSum (n+p) (fun i => weights i*coeff i)).toNat,
          toString (genericRowMLE (n+p) weights (fun i => u.getD i 0)).toNat]]
  IO.println (jsonList cases)
