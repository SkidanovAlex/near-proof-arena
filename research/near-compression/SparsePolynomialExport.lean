import NearCompression.SparseLiftPolynomial
import ZkFormal.Air.Export
open NearCompression ZkFormal.Algebra ZkFormal.Air

def main : IO Unit := do
  let encode := fun xs : List Fp => jsonList (xs.map (fun x => toString x.toNat))
  let mut cases : List String := []
  for n in List.range 4 do
    for k in List.range 4 do
      let lanes : List (List Fp) := [[],(List.range ((2^n)/2)).map (fun i => Fp.ofNat (i+3)),
        (List.range (2^n)).map (fun i => Fp.ofNat (i*i+19*i+7))]
      let beta : List Fp := [0,1,7]
      let p := branchWordsPolynomial k n beta lanes
      for x0 in [0,1,17] do
        let x := Fp.ofNat x0
        cases := cases ++ [jsonList [toString n,toString k,jsonList (lanes.map encode),encode beta,
          toString x0,encode ((List.range (2^(k+n))).map p.coeff),toString (p.eval x).toNat]]
  IO.println (jsonList cases)
