import ZkFormal.V2.Export
import ZkFormal.Algebra.Fp
import Lean

open ZkFormal.Air ZkFormal.V2 ZkFormal.Algebra Lean
namespace GenericAirFixture
instance : PubVal Fp where val := Fp.toNat

def subE (a b : ZkFormal.Air.Expr) : ZkFormal.Air.Expr := .add a (.neg b)
def gate (selector a b : ZkFormal.Air.Expr) : ZkFormal.Air.Expr := .mul selector (subE a b)
def tableA : Table where
  width := 2
  maxLog := 2
  constraints := [gate .isTransition (.col 0 true) (.add (.col 0 false) (.const 1)),
    gate .isFirst (.col 0 false) (.pub 8), gate .isLast (.col 0 true) (.pub 8), .pub 99]
  interactions := [{ bus := 0, send := true, mult := [.col 1 false, .const 0], msg := [.col 0 false] }]
def tableB : Table where
  width := 4
  maxLog := 1
  constraints := [subE (.col 1 false) (.add (.col 0 false) (.const 1)),
    gate .isTransition (.col 0 true) (.add (.col 0 false) (.const 2)),
    gate .isFirst (.col 0 false) (.pub 8), gate .isLast (.col 0 true) (.pub 8),
    gate .isFirst (.col 3 false) (.const 5),
    gate .isTransition (.col 3 true) (.add (.col 3 false) (.const 1))]
  interactions := [
    { bus := 0, send := false, mult := [.col 2 false], msg := [.col 0 false] },
    { bus := 0, send := false, mult := [.col 2 false], msg := [.col 1 false] },
    { bus := 1, send := true, mult := [.col 2 false], msg := [.const 77, .col 3 false, .col 0 false, .col 1 false] }]
def air : AirP where
  tables := [tableA, tableB]
  numBuses := 2
  numPub := 100
  maxPub := 12
  pubSegs := [
    { bus := 1, send := false, width := 2, countAt := 0, start := 0,
      startAt := some 4, msgPrefix := [77], indexBase := some 5 },
    { bus := 0, send := false, width := 1, countAt := 99, start := 0 }]
def rows : List (List (List Nat)) := [
  [[10,1],[11,1],[12,1],[13,1]], [[10,11,1,5],[12,13,1,6]]]
def publicValues : List Nat := [2,0,0,0,8,0,0,0,10,11,12,13]
def trace (rs : List (List (List Nat))) : Trace Fp where
  log := fun t => if t = 0 then 2 else 1
  cell := fun t r c => Fp.ofNat (((rs.getD t []).getD r []).getD c 0)
def mutateCell (rs : List (List (List Nat))) (t r c value : Nat) :=
  rs.modify t fun table => table.modify r fun row => row.set c value

def cases : List (String × List (List (List Nat)) × List Nat) := [
  ("honest", rows, publicValues),
  ("next-row-value", mutateCell rows 0 1 0 15, publicValues),
  ("nonboolean-multiplicity", mutateCell rows 0 1 1 2, publicValues),
  ("zero-multiplicity", mutateCell rows 0 1 1 0, publicValues),
  ("wrong-implicit-index", mutateCell rows 1 1 3 7, publicValues),
  ("wrong-public-payload", rows, publicValues.set 11 14),
  ("wrong-public-operand", rows, publicValues.set 8 9)]
def caseJson (label : String) (rs : List (List (List Nat))) (ps : List Nat) : Json := Id.run do
  let tr := trace rs
  let pub := ps.map Fp.ofNat
  let residuals := air.tables.zipIdx.map fun ((table, ti) : Table × Nat) =>
    (List.range (tr.height ti)).map fun ri => table.allConstraints.map fun (e : ZkFormal.Air.Expr) => (e.eval tr ti ri pub).toNat
  let interactions := air.tables.zipIdx.map fun ((table, ti) : Table × Nat) =>
    (List.range (tr.height ti)).map fun ri => table.interactions.map fun (i : Interaction) =>
      Json.mkObj [("bits", toJson (i.mult.map fun (e : ZkFormal.Air.Expr) => (e.eval tr ti ri pub).toNat)),
        ("multiplicity", toJson (i.multNat tr ti ri pub)),
        ("message", toJson ((i.msgVal tr ti ri pub).map Fp.toNat))]
  let messages := (pubMsgs air pub).map fun (b,s,m) =>
    Json.arr #[toJson b, toJson s, toJson (m.map Fp.toNat)]
  return Json.mkObj [("label", toJson label), ("rows", toJson rs), ("public", toJson ps),
    ("residuals", toJson residuals), ("interactions", toJson interactions),
    ("public_messages", toJson messages), ("pub_fit", toJson (pubFit air pub))]
end GenericAirFixture

def main : IO Unit := do
  let parsed ← match Json.parse GenericAirFixture.air.exportJson with
    | .ok j => pure j
    | .error e => throw (IO.userError e)
  IO.println <| (Json.mkObj [("air", parsed), ("field_modulus", toJson P),
    ("cases", toJson (GenericAirFixture.cases.map fun (label,rs,ps) =>
      GenericAirFixture.caseJson label rs ps))]).compress
