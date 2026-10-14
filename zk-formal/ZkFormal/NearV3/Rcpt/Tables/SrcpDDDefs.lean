import ZkFormal.Air.Basic
import ZkFormal.Near.Tables.Dsl
import ZkFormal.NearV3.Rcpt.Candidates.DedupTableDefs
import ZkFormal.NearV3.Rcpt.Tables.Srcp
import ZkFormal.NearV3.Rcpt.Tables.SrcpDDefs

/-!
# `ZkFormal.NearV3.Rcpt.Tables.SrcpDDDefs`

The definitions of `ZkFormal.NearV3.Rcpt.Tables.SrcpDD` that the deployed verifier model
(`NpUdrStarkV2.Model.verifier`) uses, moved verbatim (same names, statements and bodies).
`ZkFormal.NearV3.Rcpt.Tables.SrcpDD` imports this module, so its importers see the same names. Definitions only:
the model's import closure must not contain proof modules (judge native-lean build,
lane v3-model-split, docs/logs/v3-model-split-2026-10.md).
-/

namespace ZkFormal.NearV3.SrcpDD

open ZkFormal.Air ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.SrcpV3

open ZkFormal.NearV3.Rcpt.Candidates

/-- Depth-slack bit `e` (`e < 6`). -/
def db (e : Nat) : Nat := 57 + e
def width : Nat := 63

def depthBits : Expr := bits (fun e => c (db e)) 0 6

/-- The A10 constraints: six boolean slack bits and, on a computed root row,
`DP0 − (qe − q − 1) = slack`. -/
def depthConstraints : List Expr :=
  (List.range 6).map (fun e => bool (c (db e))) ++
  [ .mul DedupTable.computedRoot (sub depthBits (sub (k DP0) (sub (sub (c qe) (c q)) (k 1)))) ]

def table : Table :=
  { width := width, constraints := DedupTable.constraints ++ depthConstraints,
    interactions := DedupTable.interactions, maxLog := SrcpV3.maxLog }

end ZkFormal.NearV3.SrcpDD
