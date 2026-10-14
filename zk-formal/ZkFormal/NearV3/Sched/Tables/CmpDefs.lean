import ZkFormal.Air.Basic
import ZkFormal.Chacha.Rng.Table
import ZkFormal.Chacha.Table

/-!
# `ZkFormal.NearV3.Sched.Tables.CmpDefs`

The definitions of `ZkFormal.NearV3.Sched.Tables.Cmp` that the deployed verifier model
(`NpUdrStarkV2.Model.verifier`) uses, moved verbatim (same names, statements and bodies).
`ZkFormal.NearV3.Sched.Tables.Cmp` imports this module, so its importers see the same names. Definitions only:
the model's import closure must not contain proof modules (judge native-lean build,
lane v3-model-split, docs/logs/v3-model-split-2026-10.md).
-/

namespace ZkFormal.NearV3.Sched.Cmp

open ZkFormal.Air ZkFormal.Chacha ZkFormal.Chacha.Table.E

open ZkFormal.Chacha.Rng.Table (num)

def colAct : Nat := 0
def colX : Nat := 1
def colY : Nat := 2
def colB : Nat := 3
def colD (k : Nat) : Nat := 4 + k
def nbits : Nat := 29
def width : Nat := 33

def dE : Expr := num colD nbits

/-- `d − (b·(x − y) + (1 − b)·(y − x − 1))`. -/
def mainC : Expr :=
  sub dE (.add (.mul (c colB) (sub (c colX) (c colY)))
              (.mul (sub (k 1) (c colB)) (sub (sub (c colY) (c colX)) (k 1))))

def constraints : List Expr :=
  [ZkFormal.Chacha.Table.boolC colAct, ZkFormal.Chacha.Table.boolC colB] ++
  (List.range nbits).map (fun j => ZkFormal.Chacha.Table.boolC (colD j)) ++ [mainC]

def msg : List Expr := [c colX, c colY, c colB]

def interactions (busCmp : Nat) : List Interaction :=
  [{ bus := busCmp, mult := [c colAct], send := false, msg := msg }]

def maxLog : Nat := 22

def table (busCmp : Nat) : Table :=
  { width := width, constraints := constraints, interactions := interactions busCmp, maxLog := maxLog }

section

end

end ZkFormal.NearV3.Sched.Cmp
