import ZkFormal.Algebra.Fp8
import Lean
open ZkFormal.Algebra Lean
private def encode (a : Fp8) : Lean.Json := toJson ((Fp8.toList a).map Fp.toNat)
private def sample (i : Nat) : Fp8 := Fp8.ofCoeffs fun j=>
  Fp.ofNat (if i=0 then 0 else if i=1 then if j=0 then 1 else 0
    else if i=2 then P-1 else if i<11 then if j=i-3 then 1 else 0
    else (i+7)*(j+13)*1234567+i*i*987654321+j*j*191919)
def main : IO Unit := do
  let pairs := ((List.range 40).map fun i=>(sample i, sample (39-i))) ++
    ((List.range 8).flatMap fun i=>(List.range 8).map fun j=>(sample (i+3), sample (j+3)))
  let rows := pairs.zipIdx |>.map fun ((a,b),i)=>
    let s:=Fp.ofNat (i*187654321)
    Lean.Json.mkObj [("a",encode a),("b",encode b),("scalar",toJson s.toNat),
      ("add",encode (a+b)),("sub",encode (a-b)),("mul",encode (a*b)),
      ("inv",encode a⁻¹),("pow17",encode (a^17)),("scale",encode (Fp8.smulBase s a)),
      ("tower_mul",encode (Fp8.ofT (Fp8.toT a*Fp8.toT b)))]
  IO.println (toJson rows).compress
