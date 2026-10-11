import ZkFormal.NearV3.Rcpt.Tables.Srcp
import ZkFormal.Near.Extract.Common

/-!
# ZkFormal.NearV3.Rcpt.Tables.SrcpD — `srcpV3` with the A10 depth check

User decision 2026-10-11: RelD0a's A10 (`w.path_depth`: every used source proof's Merkle path
has `≤ Dp0 = 32` items) is enforced by the AIR.  `q` already counts the segments of a list
(the root row carries `q = ql − 1`, its last message is `SRC(qe)` with `qe = ql + depth`), so
the per-list path-item counter is `qe − q − 1`; the root row range-checks

    `DP0 − (qe − q − 1) = Σ_{e<6} 2^e · db_e`,   `db_e` boolean

i.e. `0 ≤ DP0 − depth < 64`.  Six new columns `db_0 … db_5` (`56 … 61`); every constraint and
interaction of `SrcpV3.table` is kept verbatim (`local_base`).
-/

namespace ZkFormal.NearV3.SrcpV3

open ZkFormal.Air ZkFormal.Near ZkFormal.Near.Dsl

/-- The path-depth budget (`NearSpecV3.Dp0`). -/
def DP0 : Nat := 32

/-- Depth-slack bit `e` (`e < 6`). -/
def db (e : Nat) : Nat := 56 + e
def widthD : Nat := 62

def depthBits : Expr := bits (fun e => c (db e)) 0 6

/-- The A10 constraints: six boolean slack bits, and on a root row
`DP0 − (qe − q − 1) = slack`. -/
def depthConstraints : List Expr :=
  (List.range 6).map (fun e => bool (c (db e))) ++
  [ .mul (c rt) (sub depthBits (sub (k DP0) (sub (sub (c qe) (c q)) (k 1)))) ]

def tableD : Table :=
  { width := widthD, constraints := constraints ++ depthConstraints,
    interactions := interactions, maxLog := maxLog }

theorem local_base {tr : Trace ZkFormal.Algebra.Fp} {t : Nat} {pub : List ZkFormal.Algebra.Fp}
    (h : TableLocal tableD tr t pub) : TableLocal table tr t pub :=
  ⟨h.log_ge, h.log_le, fun r hr e he => h.constr r hr e (List.mem_append_left _ he), h.bits⟩

theorem local_of_base {tr : Trace ZkFormal.Algebra.Fp} {t : Nat} {pub : List ZkFormal.Algebra.Fp}
    (h : TableLocal table tr t pub)
    (hd : ∀ r, r < tr.height t → ∀ e ∈ depthConstraints, e.eval tr t r pub = 0) :
    TableLocal tableD tr t pub := by
  refine ⟨h.log_ge, h.log_le, fun r hr e he => ?_, h.bits⟩
  rcases List.mem_append.1 he with he | he
  · exact h.constr r hr e he
  · exact hd r hr e he

end ZkFormal.NearV3.SrcpV3
