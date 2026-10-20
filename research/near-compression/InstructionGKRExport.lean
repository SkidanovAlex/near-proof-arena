import NearCompression.InstructionAddRange
import Lean

open NearCompression ZkFormal.Algebra ZkFormal.Air Lean

/-- Export the actual Lean AIR expression; unsupported environment inputs fail closed. -/
def exportLocalExpr : ZkFormal.Air.Expr → Except String Json
  | .const c => pure <| Json.mkObj [("const", toJson c)]
  | .col i false => pure <| Json.mkObj [("col", toJson i)]
  | .add a b => do pure <| Json.mkObj [("add", Json.arr #[← exportLocalExpr a, ← exportLocalExpr b])]
  | .mul a b => do pure <| Json.mkObj [("mul", Json.arr #[← exportLocalExpr a, ← exportLocalExpr b])]
  | .neg a => do pure <| Json.mkObj [("neg", ← exportLocalExpr a)]
  | _ => .error "non-local AIR environment input"

def main : IO Unit := do
  let constraints ← match instructionAdd32RangeConstraints.mapM exportLocalExpr with
    | .ok es => pure es
    | .error e => throw <| IO.userError e
  let cases : List (Nat × Nat) := [(0,0),(1,2),(65535,1),(65536,65536),
    (4294967295,1),(4294967295,4294967295),(2147483648,2147483648),(305419896,2596069104)]
  let rows := cases.map fun (a,b) =>
    (List.range 104).map fun i => (instructionAdd32RangeWitness (UInt32.ofNat a) (UInt32.ofNat b) i).toNat
  IO.println <| (Json.mkObj [("field_modulus", toJson ZkFormal.Algebra.P),
    ("columns", toJson (104 : Nat)), ("constraints", toJson constraints),
    ("rows", toJson rows), ("inputs", toJson cases)]).compress
