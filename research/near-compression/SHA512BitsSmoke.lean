import NearCompression.SHA512Bits
open NearCompression ZkFormal.Algebra

def ensureBits (b : Bool) (label : String) : IO Unit :=
  unless b do throw (IO.userError label)

def checkBits (row : Nat → Fp) : Bool :=
  sha512BitsTable.constraints.all fun e => decide (e.evalWith (instructionAddEnv row) = 0)

def main : IO Unit := do
  let m := 18446744073709551615
  let cases : List (Nat × Nat × Nat) := [(0,0,0),(m,m,m),(m,0,m),(0,m,0),
    (1,2,4),(9223372036854775808,1,m),(12297829382473034410,6148914691236517205,0),
    (81985529216486895,18364758544493064720,1085102592571150095)]
  let mut rejected := 0
  for (x,y,z) in cases do
    let row := sha512BitsWitness (UInt64.ofNat x) (UInt64.ofNat y) (UInt64.ofNat z)
    ensureBits (checkBits row) "honest SHA512 bit row rejected"
    ensureBits (sha512BitsWord row 0 == x && sha512BitsWord row 64 == y &&
      sha512BitsWord row 128 == z) "input bit reconstruction mismatch"
    let expected := #[NearSpecV3.SHA512.bsig0 x,NearSpecV3.SHA512.bsig1 x,
      NearSpecV3.SHA512.ssig0 x,NearSpecV3.SHA512.ssig1 x,
      NearSpecV3.SHA512.ch x y z,NearSpecV3.SHA512.maj x y z]
    for slot in List.range 6 do
      ensureBits (sha512BitsWord row (192 + 64 * slot) == expected[slot]!)
        "actual SHA512 word operation mismatch"
    if x == 81985529216486895 then
      let independent : Array Nat := #[13242124488700510635,8575716958325396839,
        8039707622016752289,8116407978251530618,1012195045828461056,1085102592571150095]
      for slot in List.range 6 do
        ensureBits (sha512BitsWord row (192 + 64 * slot) == independent[slot]!)
          "independent Python bit-operation fixture mismatch"
    for col in List.range 192 do
      ensureBits (!(checkBits (fun i => if i = col then (2 : Fp) else row i)))
        "nonboolean input accepted"
      rejected := rejected + 1
    for col in List.range' 192 384 do
      ensureBits (!(checkBits (fun i => if i = col then row i + (1 : Fp) else row i)))
        "output increment accepted"
      ensureBits (!(checkBits (fun i => if i = col then (1 : Fp) - row i else row i)))
        "output boolean flip accepted"
      rejected := rejected + 2
  -- Rotations exercise every bit position, including word-boundary wrap.
  for bit in List.range 64 do
    let x := 2^bit
    let row := sha512BitsWitness (UInt64.ofNat x) 0 0
    ensureBits (checkBits row) "one-hot bit row rejected"
    ensureBits (sha512BitsWord row 192 == NearSpecV3.SHA512.bsig0 x &&
      sha512BitsWord row 256 == NearSpecV3.SHA512.bsig1 x &&
      sha512BitsWord row 320 == NearSpecV3.SHA512.ssig0 x &&
      sha512BitsWord row 384 == NearSpecV3.SHA512.ssig1 x) "one-hot sigma mismatch"
  IO.println s!"PASS: {cases.length} six-operation word cases, 64 one-hot rotation cases, {rejected} malformed-input/output mutations rejected."
