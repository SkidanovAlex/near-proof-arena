import NearCompression.SHA512AddBridge
open NearCompression NearSpecV3.Wasm ZkFormal.Algebra

def ensure64 (b : Bool) (label : String) : IO Unit :=
  unless b do throw (IO.userError label)

def check64 (row : Nat → Fp) : Bool :=
  instructionAdd64Table.constraints.all fun e => decide (e.evalWith (instructionAddEnv row) = 0)

def roundRows (v : NearSpecV3.SHA512.Vars) (k w : Nat) : Array (Nat → Fp) := Id.run do
  let mut rows := #[]
  for i in List.range 7 do
    let input := sha512RoundAddInputs v k w (fun r => rows[r]?.getD (fun _ => 0)) i
    rows := rows.push (instructionAdd64Witness (UInt64.ofNat input.1) (UInt64.ofNat input.2))
  return rows

def testRound (v : NearSpecV3.SHA512.Vars) (k w : Nat) : IO Unit := do
  let rows := roundRows v k w
  let get := fun r => rows[r]?.getD (fun _ => 0)
  for i in List.range 7 do
    let input := sha512RoundAddInputs v k w get i
    ensure64 (input.1 < 2^64 && input.2 < 2^64) "round fixture input truncated"
    ensure64 (check64 (get i)) "round addition row rejected"
    ensure64 (instructionAdd64Word (get i) 0 == input.1 &&
      instructionAdd64Word (get i) 4 == input.2) "round input binding mismatch"
  let actual := NearSpecV3.SHA512.round v k w
  ensure64 (actual.a == instructionAdd64Word (get 5) 8 &&
    actual.e == instructionAdd64Word (get 6) 8) "actual SHA512 round addition mismatch"

def main : IO Unit := do
  let cases : List (Nat × Nat) := [(0,0),(65535,1),(4294967295,1),(281474976710655,1),
    (18446744073709551615,1),(18446744073709551615,18446744073709551615),
    (9223372036854775808,9223372036854775808),(81985529216486895,18364758544493064720)]
  let mut mutations := 0
  for (a,b) in cases do
    let row := instructionAdd64Witness (UInt64.ofNat a) (UInt64.ofNat b)
    ensure64 (check64 row) "honest i64 witness rejected"
    ensure64 (instructionAdd64Word row 0 == a && instructionAdd64Word row 4 == b)
      "i64 input binding mismatch"
    ensure64 (decide (Num.binop 64 0 a b = some (instructionAdd64Word row 8))) "Wasm i64 mismatch"
    ensure64 (NearSpecV3.SHA512.add64 a b == instructionAdd64Word row 8) "SHA512 add64 mismatch"
    for col in List.range 208 do
      ensure64 (!(check64 (fun i => if i = col then row i + (1 : Fp) else row i)))
        "i64 column mutation accepted"
      mutations := mutations + 1
    for col in List.range' 16 192 do
      ensure64 (!(check64 (fun i => if i = col then (1 : Fp) - row i else row i)))
        "i64 boolean bit flip accepted"
      mutations := mutations + 1
  testRound ⟨0,0,0,0,0,0,0,0⟩ 0 0
  let m := 18446744073709551615
  testRound ⟨m,m,m,m,m,m,m,m⟩ m m
  testRound (NearSpecV3.SHA512.ofList NearSpecV3.SHA512.H0)
    (NearSpecV3.SHA512.K.headD 0) 9223372036854775808
  testRound ⟨1,2,3,4,5,6,7,8⟩ 81985529216486895 18364758544493064720
  IO.println s!"PASS: {cases.length} i64/SHA512-add cases, {mutations} mutations rejected, 4 SHA512 round-addition compositions (28 rows)."
