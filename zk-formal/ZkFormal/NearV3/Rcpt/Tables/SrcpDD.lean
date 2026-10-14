import ZkFormal.NearV3.Rcpt.Candidates.DedupTable
import ZkFormal.NearV3.Rcpt.Tables.SrcpD
import ZkFormal.NearV3.Rcpt.Tables.SrcpDDDefs

/-!
# ZkFormal.NearV3.Rcpt.Tables.SrcpDD — table 20: the dedup source table with the A10 depth check

User decision 2026-10-12 (lead): `nearAirV3` table 20 is `Rcpt/Candidates/DedupTable` (the
public source record carries the all-occurrence repetition bit `rep`, every occurrence of a
repeated key has an empty list `L = 12`, a later occurrence (`dup`) is a one-row reference
block) plus the `srcpV3.tableD` A10 depth counter: six boolean slack bits `db_0 … db_5`
(columns `57 … 62`, after DedupTable's `repeated = 56`) and, on a **computed** root row
(`rt − dup`; `dup` rows are references without a path),

    `DP0 − (qe − q − 1) = Σ_{e<6} 2^e · db_e`,

i.e. `0 ≤ DP0 − depth < 64`.  Every constraint and interaction of `DedupTable.table` is kept
verbatim (`local_dedup`), so all `DedupProof` views apply.
-/

namespace ZkFormal.NearV3.SrcpDD

open ZkFormal.Air ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.SrcpV3
open ZkFormal.NearV3.Rcpt.Candidates

theorem local_dedup {tr : Trace ZkFormal.Algebra.Fp} {t : Nat} {pub : List ZkFormal.Algebra.Fp}
    (h : TableLocal table tr t pub) : TableLocal (DedupTable.table 24) tr t pub :=
  ⟨h.log_ge, by have := h.log_le; simp only [table, SrcpV3.maxLog] at this; simp only [DedupTable.table]; omega,
    fun r hr e he => h.constr r hr e (List.mem_append_left _ he), h.bits⟩

theorem local_of_dedup {tr : Trace ZkFormal.Algebra.Fp} {t : Nat} {pub : List ZkFormal.Algebra.Fp}
    (h : TableLocal (DedupTable.table 24) tr t pub) (hlog : tr.log t ≤ SrcpV3.maxLog)
    (hd : ∀ r, r < tr.height t → ∀ e ∈ depthConstraints, e.eval tr t r pub = 0) :
    TableLocal table tr t pub :=
  ⟨h.log_ge, hlog, fun r hr e he => by
    rcases List.mem_append.1 he with he | he
    · exact h.constr r hr e he
    · exact hd r hr e he, h.bits⟩

set_option maxRecDepth 16384 in
theorem constraints_degree : table.constraints.all (fun e => decide (e.degree ≤ 4)) = true := by
  decide +kernel

end ZkFormal.NearV3.SrcpDD
