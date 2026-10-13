import ZkFormal.NearV3.Assembly.RenderV3RcptTrie
import ZkFormal.NearV3.Assembly.RenderV3RcptTables
import ZkFormal.NearV3.Assembly.RcptViewV3
import ZkFormal.NearV3.Assembly.NearAirCheck
import ZkFormal.NearV3.Assembly.NearAirSize
import ZkFormal.NearV3.Assembly.RcptReceiptRepaired

/-! Guard the routing-index range check of table 16 (`RcptV3.tableQ`, user decision 2026-10-12)
and the receipt-side premises of `trie_side` (VSLOT views, `RcptKeys`, `RcptFinal`). -/

theorem tableQ_shape : ZkFormal.NearV3.RcptV3.tableQ.constraints =
    ZkFormal.NearV3.RcptV3.tableR.constraints ++ [ZkFormal.NearV3.RcptV3.qBoundR] := rfl

theorem nearAir_table16 : ZkFormal.NearV3.Assembly.nearAirV3.tables[16]? =
    some ZkFormal.NearV3.RcptV3.tableQ := rfl

/-- info: 'ZkFormal.NearV3.Assembly.RcptSkeleton.tableQ_eq' depends on axioms: [propext] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Assembly.RcptSkeleton.tableQ_eq

/-- info: 'ZkFormal.NearV3.Assembly.ReceiptCandidateProof.extracted_q_ltQ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Assembly.ReceiptCandidateProof.extracted_q_ltQ

/-- info: 'ZkFormal.NearV3.Assembly.ReceiptCandidateProof.view_q' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Assembly.ReceiptCandidateProof.view_q

/-- info: 'ZkFormal.NearV3.Assembly.rcptV3_view_nearAir' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Assembly.rcptV3_view_nearAir

/-- info: 'ZkFormal.NearV3.Assembly.rcptLocalQ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Assembly.rcptLocalQ

/-- info: 'ZkFormal.NearV3.Assembly.rcptLocal' depends on axioms: [propext, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Assembly.rcptLocal

/-- info: 'ZkFormal.NearV3.Assembly.RcptSkeleton.rcptTraceB_q_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Assembly.RcptSkeleton.rcptTraceB_q_bound

/-- info: 'ZkFormal.NearV3.Assembly.RcptSkeleton.rcpt_aligned_completeQ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Assembly.RcptSkeleton.rcpt_aligned_completeQ

/-- info: 'ZkFormal.NearV3.Assembly.RcptSkeleton.rcptTraceNative_patched_local' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Assembly.RcptSkeleton.rcptTraceNative_patched_local

/-- info: 'ZkFormal.NearV3.Assembly.RcptSkeleton.patched_counts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Assembly.RcptSkeleton.patched_counts

/-- info: 'ZkFormal.NearV3.Assembly.RcptSkeleton.honest_rcpt_keys' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Assembly.RcptSkeleton.honest_rcpt_keys

/-- info: 'ZkFormal.NearV3.Assembly.RcptSkeleton.honest_rcpt_final' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Assembly.RcptSkeleton.honest_rcpt_final

/-- info: 'ZkFormal.NearV3.Assembly.AcceptedV3.vslot_views' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Assembly.AcceptedV3.vslot_views

/-- info: 'ZkFormal.NearV3.Assembly.AcceptedV3.rcpt_keys' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Assembly.AcceptedV3.rcpt_keys

/-- info: 'ZkFormal.NearV3.Assembly.AcceptedV3.rcpt_final' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Assembly.AcceptedV3.rcpt_final

/-- info: 'ZkFormal.NearV3.Assembly.nearAirV3_wf' depends on axioms: [propext] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Assembly.nearAirV3_wf

/-- info: 'ZkFormal.NearV3.Assembly.nearV3_sizeMaxAligned' depends on axioms: [propext] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Assembly.nearV3_sizeMaxAligned
