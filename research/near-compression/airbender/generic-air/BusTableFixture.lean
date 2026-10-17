import ZkFormal.V2.Export
import ZkFormal.Algebra.Fp
import Lean

open ZkFormal.Air ZkFormal.V2 ZkFormal.Algebra Lean
namespace NearCompression.BusTableFixture

def subE (a b : ZkFormal.Air.Expr) : ZkFormal.Air.Expr := .add a (.neg b)
def gate (s a b : ZkFormal.Air.Expr) : ZkFormal.Air.Expr := .mul s (subE a b)
def power16 (e : ZkFormal.Air.Expr) : ZkFormal.Air.Expr :=
  let e2 := .mul e e
  let e4 := .mul e2 e2
  let e8 := .mul e4 e4
  .mul e8 e8

/-- Neither local table fixes the Boolean multiplicity pattern. Consequently,
the bus-only-invalid case genuinely requires global bus balance to reject. -/
def localConstraints : List ZkFormal.Air.Expr := [
  gate .isTransition (.col 0 true) (.add (.col 0 false) (.const 1)),
  gate .isFirst (.col 0 false) (.pub 4),
  gate .isLast (.col 0 true) (.pub 4),
  subE (power16 (.col 1 false)) (.col 1 false)]

def tableA : Table where
  width := 2
  maxLog := 3
  constraints := localConstraints
  interactions := [{bus := 0,send := true,mult := [.col 1 false,.const 0],msg := [.col 0 false]}]

def tableB : Table where
  width := 2
  maxLog := 3
  constraints := localConstraints
  interactions := [
    {bus := 0,send := false,mult := [.col 1 false,.const 0],msg := [.col 0 false]},
    {bus := 1,send := true,mult := [.const 1],msg := [.col 0 false]}]

def air : AirP where
  tables := [tableA,tableB]
  numBuses := 2
  numPub := 12
  maxPub := 12
  pubSegs := [{bus := 1,send := false,width := 1,countAt := 0,start := 4}]

def rows (start : Nat) : List (List (List Nat)) :=
  let table := (List.range 8).map fun r => [start+r,if r=0 ∨ r=7 then 1 else 0]
  [table,table]

def publicValues (start : Nat) : List Nat := [8,0,0,0] ++ (List.range 8).map (start+·)

def trace (rs : List (List (List Nat))) : Trace Fp where
  log := fun _ => 3
  cell := fun t r c => Fp.ofNat (((rs.getD t []).getD r []).getD c 0)

def mutateCell (rs : List (List (List Nat))) (t r c value : Nat) : List (List (List Nat)) :=
  rs.modify t fun table => table.modify r fun row => row.set c value

def residuals (rs : List (List (List Nat))) (ps : List Nat) : List (List (List Nat)) :=
  let tr := trace rs
  let pub := ps.map Fp.ofNat
  air.tables.zipIdx.map fun ((table,ti) : Table × Nat) =>
    (List.range (tr.height ti)).map fun r => table.allConstraints.map fun sourceExpr =>
      (sourceExpr.eval tr ti r pub).toNat

def caseJson (label : String) (rs : List (List (List Nat))) (ps : List Nat) : Json :=
  Json.mkObj [("label",toJson label),("rows_by_table",toJson rs),("public",toJson ps),
    ("residuals",toJson (residuals rs ps))]

end NearCompression.BusTableFixture

def main : IO Unit := do
  let parsed ← match Json.parse NearCompression.BusTableFixture.air.exportJson with
    | .ok j => pure j
    | .error e => throw (IO.userError e)
  let rs := NearCompression.BusTableFixture.rows 10
  let ps := NearCompression.BusTableFixture.publicValues 10
  let cases := [
    NearCompression.BusTableFixture.caseJson "honest" rs ps,
    NearCompression.BusTableFixture.caseJson "bus-only-invalid"
      (NearCompression.BusTableFixture.mutateCell rs 1 1 1 1) ps,
    NearCompression.BusTableFixture.caseJson "nonboolean"
      (NearCompression.BusTableFixture.mutateCell rs 0 3 1 2) ps,
    NearCompression.BusTableFixture.caseJson "alternate-public"
      (NearCompression.BusTableFixture.rows 20) (NearCompression.BusTableFixture.publicValues 20)]
  IO.println <| (Json.mkObj [("air",parsed),("public",toJson ps),("rows_by_table",toJson rs),
    ("field_modulus",toJson P),("cases",toJson cases)]).compress
