import NearCompression.RadixTwoFFTStages
import ZkFormal.Air.Export
open NearCompression ZkFormal.Algebra ZkFormal.Air

def main : IO Unit := do
  let encode := fun xs : List Fp => jsonList (xs.map (fun x => toString x.toNat))
  let mut cases : List String := []
  for n in List.range 8 do
    let omega : Fp := (Fp.ofNat 440564289)^((2^27)/(2^n))
    for mode in List.range 3 do
      let len := if mode=0 then 0 else if mode=1 then (2^n)/2 else 2^n
      let cs := (List.range len).map (fun i => Fp.ofNat (i*i+17*i+P-1))
      let stages := (List.range (n+1)).map (fun s =>
        (List.range (2^n)).map (fun i => fftBlockStage n omega (fun j => cs.getD j 0) s (i/(2^s)) (i%(2^s))))
      cases := cases ++ [jsonList [toString n,toString omega.toNat,encode cs,jsonList (stages.map encode)]]
  IO.println (jsonList cases)
