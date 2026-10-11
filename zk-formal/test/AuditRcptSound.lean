import ZkFormal.NearV3.Rcpt.Link.RcptCore
import ZkFormal.NearV3.Rcpt.Link.MemOf
import ZkFormal.NearV3.Rcpt.Link.AcctSlots

/-- info: 'ZkFormal.NearV3.RcptLink.applyReceipts_of_ledger' depends on axioms: [propext, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.RcptLink.applyReceipts_of_ledger

/-- info: 'ZkFormal.NearV3.RcptLink.forwardRun_of_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.RcptLink.forwardRun_of_split

/-- info: 'ZkFormal.NearV3.RcptLink.mem_bal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.RcptLink.mem_bal

/-- info: 'ZkFormal.NearV3.RcptLink.tprev_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.RcptLink.tprev_eq

/-- info: 'ZkFormal.NearV3.RcptLink.mem_read' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.RcptLink.mem_read

/-- info: 'ZkFormal.NearV3.RcptLink.mem_final' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.RcptLink.mem_final

/-- info: 'ZkFormal.NearV3.RcptLink.memHyp_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.RcptLink.memHyp_of

/-- info: 'ZkFormal.NearV3.RcptLink.RunModel.ledgerAll_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.RcptLink.RunModel.ledgerAll_eq

/-- info: 'ZkFormal.NearV3.RcptLink.applyNewChunk_of_parts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.RcptLink.applyNewChunk_of_parts

/-- info: 'ZkFormal.NearV3.RcptLink.rcptOk_all' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.RcptLink.rcptOk_all

/-- info: 'ZkFormal.NearV3.RcptLink.prepD0_fwd' depends on axioms: [propext, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.RcptLink.prepD0_fwd

/-- info: 'ZkFormal.NearV3.RcptLink.mainRun_of_records' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.RcptLink.mainRun_of_records

/-- info: 'ZkFormal.NearV3.RcptLink.applied_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.RcptLink.applied_eq

/-- info: 'ZkFormal.NearV3.RcptLink.acct_k_nodup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.RcptLink.acct_k_nodup

/-- info: 'ZkFormal.NearV3.RcptLink.memHyp_of'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.RcptLink.memHyp_of'
