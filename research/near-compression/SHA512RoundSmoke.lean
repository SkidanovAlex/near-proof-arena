import NearCompression.SHA512Round
import NearCompression.SHA512RoundTrace
import NearCompression.SHA512RoundWitness
import NearCompression.SHA512Relocate
open NearCompression ZkFormal.Algebra

def ensureRound (b : Bool) (label : String) : IO Unit :=
  unless b do throw (IO.userError label)

def roundWitness (v : NearSpecV3.SHA512.Vars) (k w : Nat) : Nat → Fp := Id.run do
  let mut rows : Array (Nat → Fp) := #[]
  for i in List.range 7 do
    let input := sha512RoundAddInputs v k w (fun r => rows[r]?.getD (fun _ => 0)) i
    rows := rows.push (instructionAdd64Witness (UInt64.ofNat input.1) (UInt64.ofNat input.2))
  let abc := sha512BitsWitness (UInt64.ofNat v.a) (UInt64.ofNat v.b) (UInt64.ofNat v.c)
  let efg := sha512BitsWitness (UInt64.ofNat v.e) (UInt64.ofNat v.f) (UInt64.ofNat v.g)
  return fun c => if c < 576 then abc c else if c < 1152 then efg (c-576)
    else (rows[(c-1152)/208]?.getD (fun _ => 0)) ((c-1152)%208)

-- Independently assemble the layout and compare with the formal constraint list.
def smokeRoundConstraints : List ZkFormal.Air.Expr :=
  ((List.range 2).flatMap fun i => sha512BitsConstraints.map (sha512RelocateExpr (576*i))) ++
  ((List.range 7).flatMap fun i => instructionAdd64Constraints.map (sha512RelocateExpr (sha512RoundAddBase i))) ++
  sha512RoundWires.flatMap sha512RoundWireConstraints

def checkRound (row : Nat → Fp) : Bool :=
  sha512RoundConstraints.all fun e => decide (e.evalWith (instructionAddEnv row) = 0)

def checkRoundLocal (row : Nat → Fp) : Bool :=
  (List.range 2).all (fun i => sha512BitsConstraints.all fun e =>
    decide (e.evalWith (instructionAddEnv (sha512RoundBitsRow row i)) = 0)) &&
  (List.range 7).all (fun i => instructionAdd64Constraints.all fun e =>
    decide (e.evalWith (instructionAddEnv (sha512RoundAddRow row i)) = 0))

def testRoundCircuit (v : NearSpecV3.SHA512.Vars) (k w : Nat) : IO Unit := do
  let row := roundWitness v k w
  ensureRound ((List.range 2608).all fun c => decide (row c = sha512RoundWitness v k w c))
    "independent and formal witnesses disagree"
  ensureRound (checkRound row) "honest round rejected"
  let tr : ZkFormal.Air.Trace Fp := ⟨fun _ => 1, fun _ _ c => row c⟩
  for r in List.range 2 do
    ensureRound (sha512RoundConstraints.all fun e =>
      decide (e.eval tr 0 r [Fp.ofNat 123] = 0)) "actual trace evaluator rejected"

  let decoded := sha512RoundVars row
  ensureRound (decoded.a == v.a && decoded.b == v.b && decoded.c == v.c && decoded.d == v.d &&
    decoded.e == v.e && decoded.f == v.f && decoded.g == v.g && decoded.h == v.h &&
    sha512RoundK row == k && sha512RoundW row == w) "round input decoding mismatch"
  let actual := NearSpecV3.SHA512.round v k w
  ensureRound (actual.a == instructionAdd64Word (sha512RoundAddRow row 5) 8 &&
    actual.e == instructionAdd64Word (sha512RoundAddRow row 6) 8) "round output mismatch"
  -- Each forged adder is internally valid; only the inter-gadget wiring rejects it.
  for wire in sha512RoundWires do
    let idx := (wire.target - 1152) / 208
    let side := (wire.target - 1152) % 208
    let old := sha512RoundAddRow row idx
    let a := instructionAdd64Word old 0
    let b := instructionAdd64Word old 4
    let replacement := instructionAdd64Witness
      (UInt64.ofNat (if side == 0 then (a+1)%2^64 else a))
      (UInt64.ofNat (if side == 4 then (b+1)%2^64 else b))
    let base := sha512RoundAddBase idx
    let forged := fun c => if base ≤ c && c < base+208 then replacement (c-base) else row c
    ensureRound (checkRoundLocal forged) "coherent forgery invalid locally"
    ensureRound (!(checkRound forged)) "broken round dependency accepted"

def main : IO Unit := do
  ensureRound (smokeRoundConstraints == sha512RoundConstraints) "independent layout mismatch"
  testRoundCircuit ⟨0,0,0,0,0,0,0,0⟩ 0 0
  let m := 18446744073709551615
  testRoundCircuit ⟨m,m,m,m,m,m,m,m⟩ m m
  testRoundCircuit (NearSpecV3.SHA512.ofList NearSpecV3.SHA512.H0)
    (NearSpecV3.SHA512.K.headD 0) 9223372036854775808
  testRoundCircuit ⟨1,2,3,4,5,6,7,8⟩ 81985529216486895 18364758544493064720
  let fixture := roundWitness ⟨1,2,3,4,5,6,7,8⟩ 81985529216486895 18364758544493064720
  ensureRound (instructionAdd64Word (sha512RoundAddRow fixture 5) 8 == 5981413123817488 &&
    instructionAdd64Word (sha512RoundAddRow fixture 6) 8 == 5981343297044497)
    "independent Python round fixture mismatch"
  IO.println "PASS: 4 wired SHA512 rounds; 40 locally valid dependency forgeries rejected."
