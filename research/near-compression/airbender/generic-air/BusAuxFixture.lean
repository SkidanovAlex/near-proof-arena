import ZkFormal.Stark.VerifierDefs
import ZkFormal.Air.Export
import ZkFormal.Algebra.Fp
import Lean

open ZkFormal.Air ZkFormal.Algebra Lean
namespace BusAuxFixture

def table : Table where
  width := 3
  maxLog := 1
  constraints := []
  interactions := [
    { bus := 0, send := false, mult := [.col 1 false,.col 2 false,.isFirst], msg := [.col 0 false] },
    { bus := 1, send := true, mult := [], msg := [.pub 0,.col 0 true] },
    { bus := 0, send := true, mult := [.col 1 false], msg := [.col 0 false] },
    { bus := 1, send := false, mult := [.col 2 false,.isTransition], msg := [.pub 0,.col 0 true] }]

def env (cur nxt ps : List Nat) (s : List Nat) : Env Fp where
  ofNat := Fp.ofNat
  add := (· + ·)
  mul := (· * ·)
  neg := Neg.neg
  col := fun c nx => Fp.ofNat ((if nx then nxt else cur).getD c 0)
  pub := fun i => Fp.ofNat (ps.getD i 0)
  isFirst := Fp.ofNat (s.getD 0 0)
  isLast := Fp.ofNat (s.getD 1 0)
  isTransition := Fp.ofNat (s.getD 2 0)

def caseJson (label : String) (cur nxt s : List Nat) (alpha gamma : Nat) : Json :=
  let ac := (List.range 10).map (· + 2)
  let an := (List.range 10).map (· + 12)
  let fins := [22,23,24,25]
  let en := env cur nxt [11] s
  let residuals := ZkFormal.Stark.auxConstraints table 1 en (Fp.ofNat alpha) (Fp.ofNat gamma)
    (ac.map Fp.ofNat) (an.map Fp.ofNat) (fins.map Fp.ofNat)
  Json.mkObj [("label",toJson label), ("current",toJson cur), ("next",toJson nxt),
    ("public",toJson ([11] : List Nat)), ("selectors",toJson s),
    ("alpha",toJson alpha), ("gamma",toJson gamma),
    ("aux_current",toJson ac), ("aux_next",toJson an), ("finals",toJson fins),
    ("fingerprints",toJson (table.interactions.map fun i =>
      (ZkFormal.Stark.fingerprint en (Fp.ofNat alpha) i).toNat)),
    ("residuals",toJson (residuals.map Fp.toNat))]
end BusAuxFixture

def main : IO Unit := do
  let parsed ← match Json.parse BusAuxFixture.table.toJson with
    | .ok j => pure j
    | .error e => throw (IO.userError e)
  IO.println <| (Json.mkObj [("table",parsed),
    ("cases", toJson [BusAuxFixture.caseJson "first-zero-factor" [7,1,0] [8,0,1] [1,0,1] 3 10,
      BusAuxFixture.caseJson "last" [8,0,1] [7,1,0] [0,1,0] 3 10,
      BusAuxFixture.caseJson "arbitrary-off-cube" [21,4,7] [8,0,1] [5,6,7] 3 29])]).compress
