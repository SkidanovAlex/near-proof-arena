import ZkFormal.NearV3.Rcpt.Candidates.DedupRender
import ZkFormal.NearV3.Rcpt.Candidates.DedupTableDefs

/-! Candidate source AIR only. It is not installed in the active assembly or admitted
by the current log22 protocol. Logical-renderer and partition-continuation proofs are
separate work; the `cap` parameter does not change the active Table.wf predicate. -/
namespace ZkFormal.NearV3.Rcpt.Candidates.DedupTable
open ZkFormal.Air ZkFormal.Near ZkFormal.Near.Dsl SrcpV3

abbrev width : Nat := 57

def table (cap : Nat) : Table :=
  { width := width, constraints := constraints, interactions := interactions, maxLog := cap }

set_option maxRecDepth 16384 in
/-- New dedup transitions retain the original degree4 bound. -/
theorem constraints_degree : constraints.all (fun e => decide (e.degree ≤ 4)) = true := by
  decide +kernel

set_option maxRecDepth 16384 in
theorem expressions_width : ((table 24).exprs.all fun e => decide (e.colBound ≤ width)) = true := by
  decide +kernel

theorem counts : constraints.length = 122 ∧ interactions.length = 5 := by decide +kernel

end ZkFormal.NearV3.Rcpt.Candidates.DedupTable
