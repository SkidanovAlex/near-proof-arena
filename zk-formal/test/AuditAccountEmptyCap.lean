import ZkFormal.NearV3.Render.PaddedAcctE
import ZkFormal.NearV3.Assembly.ViewsV3

/-! Guard the assumptions of the empty-capable account table 17 (`acctTableV3`): soundness
split, two-branch view, empty-case render. -/

/-- info: 'ZkFormal.NearV3.Assembly.acctV3_empty_or_old' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Assembly.acctV3_empty_or_old

/-- info: 'ZkFormal.NearV3.acctV3E_view_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.acctV3E_view_at

/-- info: 'ZkFormal.NearV3.Assembly.acctView' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Assembly.acctView

/-- info: 'ZkFormal.NearV3.Rcpt.Candidates.AccountEmpty.old_local_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Rcpt.Candidates.AccountEmpty.old_local_at

/-- info: 'ZkFormal.NearV3.Render.acct_aligned_completeE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Render.acct_aligned_completeE
