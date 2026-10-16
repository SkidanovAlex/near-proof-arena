import NearCompression.SHA512Round
import NearCompression.SHA512ScheduleTrace
open NearCompression ZkFormal.Air ZkFormal.Algebra NearSpecV3.SHA512

def schedEnsure (b : Bool) (label : String) : IO Unit :=
  unless b do throw (IO.userError label)

def schedWitness (w0 w1 w9 w14 : Nat) : Array Fp := Id.run do
  let bits0 := sha512BitsWitness (UInt64.ofNat w14) 0 0
  let bits1 := sha512BitsWitness (UInt64.ofNat w1) 0 0
  let add0 := instructionAdd64Witness (UInt64.ofNat (ssig1 w14)) (UInt64.ofNat w9)
  let add1 := instructionAdd64Witness (UInt64.ofNat (ssig0 w1)) (UInt64.ofNat w0)
  let add2 := instructionAdd64Witness (UInt64.ofNat (add64 (ssig1 w14) w9))
    (UInt64.ofNat (add64 (ssig0 w1) w0))
  return ((List.range 1776).map fun c =>
    if c < 576 then bits0 c else if c < 1152 then bits1 (c-576)
    else if c < 1360 then add0 (c-1152) else if c < 1568 then add1 (c-1360)
    else add2 (c-1568)).toArray

def schedCell (row : Array Fp) (c : Nat) : Fp := row[c]?.getD 0

def schedWires : List SHA512RoundWire :=
  [⟨1152,384,true⟩,⟨1360,896,true⟩,⟨1568,1160,false⟩,⟨1572,1368,false⟩]
def schedConstraints : List Expr :=
  ((List.range 2).flatMap fun i => sha512BitsConstraints.map (sha512RelocateExpr (576*i))) ++
  ((List.range 3).flatMap fun i => instructionAdd64Constraints.map (sha512RelocateExpr (1152+208*i))) ++
  schedWires.flatMap sha512RoundWireConstraints

def schedCheck (row : Array Fp) : Bool :=
  schedConstraints.all fun e => decide (e.evalWith (instructionAddEnv (schedCell row)) = 0)
def schedLocal (row : Array Fp) : Bool :=
  (List.range 2).all (fun i => sha512BitsConstraints.all fun e =>
    decide (e.evalWith (instructionAddEnv (fun c => schedCell row (576*i+c))) = 0)) &&
  (List.range 3).all (fun i => instructionAdd64Constraints.all fun e =>
    decide (e.evalWith (instructionAddEnv (fun c => schedCell row (1152+208*i+c))) = 0))
def schedOutput (row : Array Fp) : Nat := instructionAdd64Word (schedCell row) 1576

def schedCase (w0 w1 w9 w14 : Nat) : IO Unit := do
  let row := schedWitness w0 w1 w9 w14
  schedEnsure (schedCheck row) "honest schedule core rejected"
  schedEnsure ((List.range 1776).all fun c =>
    decide (schedCell row c = sha512ScheduleWitness w0 w1 w9 w14 c))
    "formal and independent schedule witnesses disagree"
  schedEnsure (sha512ScheduleW0 (schedCell row) == w0 &&
    sha512ScheduleW1 (schedCell row) == w1 && sha512ScheduleW9 (schedCell row) == w9 &&
    sha512ScheduleW14 (schedCell row) == w14) "schedule input decoding mismatch"
  let tr : Trace Fp := ⟨fun _ => 1, fun _ _ c => schedCell row c⟩
  for r in List.range 2 do
    schedEnsure (sha512ScheduleConstraints.all fun e => decide (e.eval tr 0 r [] = 0))
      "actual schedule trace evaluation failed"
  schedEnsure (schedOutput row == add64 (add64 (ssig1 w14) w9) (add64 (ssig0 w1) w0))
    "schedule recurrence mismatch"
  for wire in schedWires do
    let idx := (wire.target-1152)/208
    let side := (wire.target-1152)%208
    let base := 1152+208*idx
    let a := instructionAdd64Word (schedCell row) base
    let b := instructionAdd64Word (schedCell row) (base+4)
    let replacement := instructionAdd64Witness
      (UInt64.ofNat (if side == 0 then (a+1)%2^64 else a))
      (UInt64.ofNat (if side == 4 then (b+1)%2^64 else b))
    let forged := ((List.range 1776).map fun c =>
      if base ≤ c && c < base+208 then replacement (c-base) else schedCell row c).toArray
    schedEnsure (schedLocal forged) "schedule forgery invalid locally"
    schedEnsure (!(schedCheck forged)) "broken schedule dependency accepted"

def main : IO Unit := do
  schedEnsure (schedConstraints == sha512ScheduleConstraints) "formal schedule layout mismatch"
  let m := 18446744073709551615
  for (a,b,c,d) in ([(0,0,0,0),(m,m,m,m),(m,0,1,0),(0,1,0,m),
      (1,2,3,4),(65535,65536,4294967295,4294967296),
      (9223372036854775808,1,0,9223372036854775808),
      (81985529216486895,18364758544493064720,1085102592571150095,12297829382473034410)] :
      List (Nat × Nat × Nat × Nat)) do
    schedCase a b c d
  -- Software supplies the window links here; the AIR core does not yet bind them.
  let mut window := List.range 16
  for _ in List.range 64 do
    let row := schedWitness (window.getD 0 0) (window.getD 1 0) (window.getD 9 0) (window.getD 14 0)
    schedEnsure (schedCheck row) "expanded schedule row rejected"
    let next := nextWindow window
    schedEnsure (schedOutput row == next.getD 15 0) "actual nextWindow mismatch"
    window := window.drop 1 ++ [schedOutput row]
  schedEnsure (window.getD 15 0 == 7471377847041668307) "independent Python W79 mismatch"
  -- A fresh valid row with the wrong W14 passes: temporal bindings remain absent.
  schedEnsure (schedCheck (schedWitness 0 1 9 15)) "unexpected temporal schedule binding"
  IO.println "PASS: 8 schedule cases,32 locally valid dependency forgeries rejected,64 software-linked expansions."
