import NearCompression.InstructionAdd

open NearCompression ZkFormal.Algebra ZkFormal.Air NearSpecV3.Wasm

def arithmeticCheck (row : Nat → Fp) : Bool :=
  instructionAdd32Constraints.all fun e =>
    decide (e.evalWith (instructionAddEnv row) = 0)

def rangeCheck (row : Nat → Fp) : Bool :=
  (List.range 6).all fun i => decide ((row i).toNat < 65536)

def check (row : Nat → Fp) : Bool := arithmeticCheck row && rangeCheck row

def assertCase (name : String) (value : Bool) : IO Unit :=
  unless value do throw (IO.userError ("FAIL: " ++ name))

def main : IO Unit := do
  let cases : List (Nat × Nat) := [
    (0, 0), (1, 2), (65535, 1), (65536, 65536),
    (4294967295, 1), (4294967295, 4294967295),
    (2147483648, 2147483648), (305419896, 2596069104)]
  let mut rejected := 0
  for (a, b) in cases do
    let row := instructionAdd32Witness (UInt32.ofNat a) (UInt32.ofNat b)
    assertCase "honest arithmetic and range" (check row)
    assertCase "honest input bindings"
      (decide (instructionAddWord row 0 1 = a ∧ instructionAddWord row 2 3 = b))
    assertCase "actual Wasm arithmetic"
      (decide (Num.binop 32 0 a b = some (instructionAddWord row 4 5)))
    for col in [4, 5, 6, 7] do
      let bad := fun i => if i = col then row i + (1 : Fp) else row i
      assertCase "output/carry mutation rejected" (!(check bad))
      rejected := rejected + 1
  -- This satisfies both linear residuals and carry booleanity but encodes
  -- out = a = 2^32. Without range constraints the claimed uint32 output is false.
  let outOfRange := fun i => Fp.ofNat (match i with
    | 0 | 4 => 65536
    | 1 | 5 => 65535
    | _ => 0)
  assertCase "range omission counterexample vanishes" (arithmeticCheck outOfRange)
  assertCase "range omission counterexample rejected" (!(check outOfRange))
  assertCase "range omission changes arithmetic result"
    (decide (Num.binop 32 0 (instructionAddWord outOfRange 0 1)
      (instructionAddWord outOfRange 2 3) ≠ some (instructionAddWord outOfRange 4 5)))
  IO.println s!"PASS: {cases.length} honest addition witnesses, {rejected} output/carry mutations, range-omission counterexample."
