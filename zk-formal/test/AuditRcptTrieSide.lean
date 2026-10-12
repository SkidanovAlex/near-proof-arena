import ZkFormal.NearV3.Assembly.RenderV3RcptTrieSide
import ZkFormal.NearV3.Assembly.SizeBudgetAccepted
import ZkFormal.NearV3.Assembly.RenderV3SrcpSha

/-! Guard the receipt SHA family / BYTES-DIGEST receipt halves and the combined receipt+trie side. -/

/-- info: 'ZkFormal.NearV3.Render.outcome_traffic_v3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Render.outcome_traffic_v3

/-- info: 'ZkFormal.NearV3.Assembly.AcceptedV3.accountJobs_bytes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Assembly.AcceptedV3.accountJobs_bytes

/-- info: 'ZkFormal.NearV3.Assembly.AcceptedV3.receipt_sha' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Assembly.AcceptedV3.receipt_sha

/-- info: 'ZkFormal.NearV3.Assembly.AcceptedV3.account_digests' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Assembly.AcceptedV3.account_digests

/-- info: 'ZkFormal.NearV3.Assembly.RcptTrieSide.rcpt_trie_side' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Assembly.RcptTrieSide.rcpt_trie_side

/-- info: 'ZkFormal.NearV3.Assembly.AcceptedV3.srcShaAll_rows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Assembly.AcceptedV3.srcShaAll_rows

/-- info: 'ZkFormal.NearV3.Assembly.AcceptedV3.srcShaAll_msgRows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Assembly.AcceptedV3.srcShaAll_msgRows

/-- info: 'ZkFormal.NearV3.Assembly.AcceptedV3.srcShaAll_bytes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Assembly.AcceptedV3.srcShaAll_bytes

/-- info: 'ZkFormal.NearV3.Assembly.AcceptedV3.srcp_bytes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Assembly.AcceptedV3.srcp_bytes

/-- info: 'ZkFormal.NearV3.Assembly.AcceptedV3.srcp_digests' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Assembly.AcceptedV3.srcp_digests

/-- info: 'ZkFormal.NearV3.Assembly.AcceptedV3.rc_digests' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Assembly.AcceptedV3.rc_digests

/-- info: 'ZkFormal.NearV3.Assembly.TrieSide.trie_side_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Assembly.TrieSide.trie_side_exact

/-- info: 'ZkFormal.NearV3.Assembly.TrieSide.sizeBudget_of_coarse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Assembly.TrieSide.sizeBudget_of_coarse

/-- info: 'ZkFormal.NearV3.Assembly.AcceptedV3.srcpSize_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Assembly.AcceptedV3.srcpSize_le

/-- info: 'ZkFormal.NearV3.Assembly.AcceptedV3.sizeBudget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Assembly.AcceptedV3.sizeBudget
