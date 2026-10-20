import ZkFormal.Air.Export
import ZkFormal.Algebra.Fp
import Lean

open ZkFormal.Air ZkFormal.Algebra Lean
namespace GenericTableFixture

def subE (a b : ZkFormal.Air.Expr) : ZkFormal.Air.Expr := .add a (.neg b)
def gate (s a b : ZkFormal.Air.Expr) : ZkFormal.Air.Expr := .mul s (subE a b)
def power16 (e : ZkFormal.Air.Expr) : ZkFormal.Air.Expr :=
  let e2 := .mul e e
  let e4 := .mul e2 e2
  let e8 := .mul e4 e4
  .mul e8 e8

/-- Local fixture only: the declared sender has no matching bus receiver. -/
def table : Table where
  width := 2
  maxLog := 3
  constraints := [
    gate .isTransition (.col 0 true) (.add (.col 0 false) (.const 1)),
    gate .isFirst (.col 0 false) (.pub 0),
    gate .isLast (.col 0 true) (.pub 0),
    subE (.col 1 false) (.add .isFirst .isLast),
    subE (power16 (.col 1 false)) (.col 1 false),
    .pub 5]
  interactions := [{ bus := 0, send := true, mult := [.col 1 false], msg := [.col 0 false] }]

def air : Air where
  tables := [table]
  numPub := 6
  numBuses := 1

def rows (start : Nat) : List (List Nat) :=
  (List.range 8).map fun i => [start + i, if i = 0 ∨ i = 7 then 1 else 0]
def trace (rs : List (List Nat)) : Trace Fp where
  log := fun _ => 3
  cell := fun _ r c => Fp.ofNat ((rs.getD r []).getD c 0)

def caseJson (label : String) (rs : List (List Nat)) (ps : List Nat) : Json :=
  let tr := trace rs
  let pub := ps.map Fp.ofNat
  let residuals := (List.range 8).map fun r =>
    table.allConstraints.map fun (e : ZkFormal.Air.Expr) => (e.eval tr 0 r pub).toNat
  Json.mkObj [("label", toJson label), ("rows", toJson rs), ("public", toJson ps),
    ("residuals", toJson residuals)]

end GenericTableFixture

def main : IO Unit := do
  let parsed ← match Json.parse GenericTableFixture.air.exportJson with
    | .ok j => pure j
    | .error e => throw (IO.userError e)
  let rs := GenericTableFixture.rows 10
  let bad := rs.modify 3 fun row => row.set 1 2
  let cases := [GenericTableFixture.caseJson "honest" rs [10],
    GenericTableFixture.caseJson "nonboolean-witness" bad [10],
    GenericTableFixture.caseJson "different-valid-statement" (GenericTableFixture.rows 20) [20]]
  let residuals := (List.range 8).map fun r =>
    GenericTableFixture.table.allConstraints.map fun (e : ZkFormal.Air.Expr) =>
      (e.eval (GenericTableFixture.trace rs) 0 r [Fp.ofNat 10]).toNat
  IO.println <| (Json.mkObj [("air", parsed), ("table_index", toJson (0 : Nat)),
    ("public", toJson ([10] : List Nat)), ("rows", toJson rs), ("residuals", toJson residuals),
    ("field_modulus", toJson P),
    ("numPub", toJson (6 : Nat)), ("numBuses", toJson (1 : Nat)),
    ("constraint_degrees", toJson (GenericTableFixture.table.allConstraints.map Expr.degree)),
    ("cases", toJson cases)]).compress
