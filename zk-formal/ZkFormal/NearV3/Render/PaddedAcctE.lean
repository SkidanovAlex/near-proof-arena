import ZkFormal.NearV3.Render.PaddedRcpt
import ZkFormal.NearV3.Rcpt.Candidates.AccountEmptyCap

/-!
# Aligned render of the repaired account table `acctTableV3` (table 17), empty case included

`AcctV3OkE as := as = [] ∨ AcctV3Ok as`.  No account read (`as = []`, an accepted chunk whose
applied source lists are all empty): the all-zero trace of height 2 (`AccountEmpty.emptyTrace`,
log 1 ≡ 1 mod 3), legal for the repaired first-row constraint and silent.  Otherwise the
existing aligned render (`acct_aligned_complete`), whose original constraints imply the repaired
ones (`AccountEmpty.old_local_at`).
-/
namespace ZkFormal.NearV3.Render
open ZkFormal.Near ZkFormal.Air ZkFormal.Algebra
open ZkFormal.NearV3.Rcpt.Candidates

/-- The honest-side condition of table 17: no account, or the nonempty `AcctV3Ok`. -/
def AcctV3OkE (as : List AcctV) : Prop := as = [] ∨ AcctV3Ok as

open Classical in
/-- The honest table-17 trace. -/
noncomputable def acctTraceAlignedE (as : List AcctV) : Trace Fp :=
  if as = [] then AccountEmpty.emptyTrace else acctTraceAligned as

/-- **Account table completeness for `acctTableV3`** (cap 19, empty chunk included). -/
theorem acct_aligned_completeE (as : List AcctV) (ok : AcctV3OkE as) (t : Nat) (pub : List Fp) :
    TableLocal ZkFormal.NearV3.Assembly.acctTableV3 (acctTraceAlignedE as) t pub ∧
    TableTraffic AcctV3.interactions (acctTraceAlignedE as) t pub (acctV3Traffic as) ∧
    (acctTraceAlignedE as).log t % 3 = 1 := by
  by_cases he : as = []
  · subst he
    simp only [acctTraceAlignedE, if_pos rfl]
    exact ⟨AccountEmpty.empty_local_at (by decide) t pub, AccountEmpty.empty_traffic_exact t pub, rfl⟩
  · have ok' : AcctV3Ok as := ok.resolve_left he
    simp only [acctTraceAlignedE, if_neg he]
    obtain ⟨hl, ht, ha⟩ := acct_aligned_complete as ok' t pub
    exact ⟨AccountEmpty.old_local_at hl, ht, ha⟩

end ZkFormal.NearV3.Render
