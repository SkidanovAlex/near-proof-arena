import ZkFormal.NearV3.Rcpt.Link.RcptCore
import ZkFormal.NearV3.Rcpt.Link.MemOf
import ZkFormal.NearV3.Rcpt.Link.AcctSlots
import ZkFormal.NearV3.Rcpt.Link.GasPub
import ZkFormal.NearV3.Rcpt.Link.RcptHolds
import ZkFormal.NearV3.Rcpt.Link.ValBytes
import ZkFormal.NearV3.Rcpt.Link.RcptHoldsB

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

/-- info: 'ZkFormal.NearV3.RcptLink.gasPrice_pub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.RcptLink.gasPrice_pub

/-- info: 'ZkFormal.NearV3.RcptLink.mainRun_of_holdsP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.RcptLink.mainRun_of_holdsP

/-- info: 'ZkFormal.NearV3.Link3.val_bytes8' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Link3.val_bytes8

/-- info: 'ZkFormal.NearV3.RcptLink.acct_pre_byte' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.RcptLink.acct_pre_byte

/-- info: 'ZkFormal.NearV3.RcptLink.preB_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.RcptLink.preB_of

/-- info: 'ZkFormal.NearV3.RcptLink.peoBytes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.RcptLink.peoBytes

/-- info: 'ZkFormal.NearV3.RcptLink.burntBytes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.RcptLink.burntBytes

/-- info: 'ZkFormal.NearV3.RcptLink.rfStream_body' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.RcptLink.rfStream_body

/-- info: 'ZkFormal.NearV3.RcptLink.ramtBytes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.RcptLink.ramtBytes

/-- info: 'ZkFormal.NearV3.RcptLink.rfid_sha' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.RcptLink.rfid_sha

/-- info: 'ZkFormal.NearV3.RcptLink.rfS_refundOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.RcptLink.rfS_refundOf

/-- info: 'ZkFormal.NearV3.RcptLink.decodeBody_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.RcptLink.decodeBody_tail

/-- info: 'ZkFormal.NearV3.RcptLink.refunds_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.RcptLink.refunds_of

/-- info: 'ZkFormal.NearV3.RcptLink.mainRun_of_holdsP_sha' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.RcptLink.mainRun_of_holdsP_sha
