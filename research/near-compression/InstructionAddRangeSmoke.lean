import NearCompression.InstructionAddRange

open NearCompression ZkFormal.Algebra ZkFormal.Air NearSpecV3.Wasm

/-- Only polynomial evaluation, with no external integer range guard. -/
def checkRangeAir (row : Nat → Fp) : Bool :=
  instructionAdd32RangeConstraints.all fun e =>
    decide (e.evalWith (instructionAddEnv row) = 0)

def assertRangeCase (name : String) (value : Bool) : IO Unit :=
  unless value do throw (IO.userError ("FAIL: " ++ name))

def main : IO Unit := do
  let cases : List (Nat × Nat) := [
    (0, 0), (1, 2), (65535, 1), (65536, 65536),
    (4294967295, 1), (4294967295, 4294967295),
    (2147483648, 2147483648), (305419896, 2596069104)]
  let mut rejected := 0
  for (a, b) in cases do
    let row := instructionAdd32RangeWitness (UInt32.ofNat a) (UInt32.ofNat b)
    assertRangeCase "honest arithmetic and range polynomials" (checkRangeAir row)
    assertRangeCase "honest input bindings"
      (decide (instructionAddWord row 0 1 = a ∧ instructionAddWord row 2 3 = b))
    assertRangeCase "actual Wasm arithmetic"
      (decide (Num.binop 32 0 a b = some (instructionAddWord row 4 5)))
    for col in List.range 104 do
      let bad := fun i => if i = col then row i + (1 : Fp) else row i
      assertRangeCase "individual column mutation rejected" (!(checkRangeAir bad))
      rejected := rejected + 1
    -- Flip a bit to the other valid boolean: booleanity alone cannot reject it,
    -- so this exercises the reconstruction equation itself.
    for col in List.range' 8 96 do
      let bad := fun i => if i = col then (1 : Fp) - row i else row i
      assertRangeCase "boolean bit flip rejected by reconstruction" (!(checkRangeAir bad))
      rejected := rejected + 1
  let outOfRange := fun i => Fp.ofNat (match i with
    | 0 | 4 => 65536
    | 1 | 5 => 65535
    | _ => 0)
  assertRangeCase "previous range-omission forgery rejected by polynomials"
    (!(checkRangeAir outOfRange))
  IO.println s!"PASS: {cases.length} honest range-enforced addition witnesses, {rejected} mutations, previous range-omission forgery rejected."
