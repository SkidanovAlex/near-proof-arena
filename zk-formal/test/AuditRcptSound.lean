import ZkFormal.NearV3.Rcpt.Link.RcptCore
import ZkFormal.NearV3.Rcpt.Link.MemOf
import ZkFormal.NearV3.Rcpt.Link.AcctSlots
import ZkFormal.NearV3.Rcpt.Link.GasPub
import ZkFormal.NearV3.Rcpt.Link.RcptHolds
import ZkFormal.NearV3.Rcpt.Link.QvCodec
import ZkFormal.NearV3.Rcpt.Link.QvMain
import ZkFormal.NearV3.Rcpt.Link.ValExact
import ZkFormal.NearV3.Rcpt.Link.RcptRoute
import ZkFormal.NearV3.Rcpt.Link.RcptRunHdr
import ZkFormal.NearV3.Rcpt.Link.ValBytes
import ZkFormal.NearV3.Rcpt.Link.RcptHoldsB
import ZkFormal.NearV3.Rcpt.Link.AkeyAkc
import ZkFormal.NearV3.Rcpt.Link.SrecLink
import ZkFormal.NearV3.Rcpt.Link.QvPre
import ZkFormal.NearV3.Rcpt.Link.QvBal

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

/-- info: 'ZkFormal.NearV3.RcptLink.hsz_of_links' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.RcptLink.hsz_of_links

/-- info: 'ZkFormal.NearV3.RcptLink.prepClaim_layout_wf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.RcptLink.prepClaim_layout_wf

/-- info: 'ZkFormal.NearV3.RcptLink.mainRun_of_holdsP_fwd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.RcptLink.mainRun_of_holdsP_fwd

/-- info: 'ZkFormal.NearV3.RcptLink.akc_akey' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.RcptLink.akc_akey

/-- info: 'ZkFormal.NearV3.RcptLink.akey_byte' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.RcptLink.akey_byte

/-- info: 'ZkFormal.NearV3.RcptLink.akey_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.RcptLink.akey_value

/-- info: 'ZkFormal.NearV3.RcptLink.srecBal_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.RcptLink.srecBal_of

/-- info: 'ZkFormal.NearV3.RcptLink.ee_of_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.RcptLink.ee_of_self

/-- info: 'ZkFormal.NearV3.RcptLink.own_index_of_route' depends on axioms: [propext, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.RcptLink.own_index_of_route

/-- info: 'ZkFormal.NearV3.RcptLink.mainRun_of_holdsP_route' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.RcptLink.mainRun_of_holdsP_route

/-- info: 'ZkFormal.NearV3.RcptLink.ledgerAll_find_other' depends on axioms: [propext, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.RcptLink.ledgerAll_find_other

/-- info: 'ZkFormal.NearV3.RcptLink.reads_of_pre' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.RcptLink.reads_of_pre

/-- info: 'ZkFormal.NearV3.RcptLink.mainRun_of_holdsP_pre' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.RcptLink.mainRun_of_holdsP_pre

/-- info: 'ZkFormal.NearV3.RcptLink.qv_hkey' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.RcptLink.qv_hkey

/-- info: 'ZkFormal.NearV3.RcptLink.qv_hfinal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.RcptLink.qv_hfinal

/-- info: 'ZkFormal.NearV3.RcptLink.qv_hK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.RcptLink.qv_hK

/-- info: 'ZkFormal.NearV3.RcptLink.RunModel.valsAt_lenPres' depends on axioms: [propext] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.RcptLink.RunModel.valsAt_lenPres

/-- info: 'ZkFormal.NearV3.Qv.Extract.QvRc.recComplete_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Qv.Extract.QvRc.recComplete_of

/-- info: 'ZkFormal.NearV3.Qv.Extract.QvRc.empty_read' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Qv.Extract.QvRc.empty_read

/-- info: 'ZkFormal.NearV3.Qv.Extract.QvRc.buffered_read' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Qv.Extract.QvRc.buffered_read

/-- info: 'ZkFormal.NearV3.Qv.Extract.QvRc.count_read' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Qv.Extract.QvRc.count_read

/-- info: 'ZkFormal.NearV3.RcptLink.codec_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.RcptLink.codec_closed

/-- info: 'ZkFormal.NearV3.RcptLink.recComplete_holdsP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.RcptLink.recComplete_holdsP

/-- info: 'ZkFormal.NearV3.RcptLink.qsh_holdsP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.RcptLink.qsh_holdsP

/-- info: 'ZkFormal.NearV3.RcptLink.qvc_holdsP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.RcptLink.qvc_holdsP

/-- info: 'ZkFormal.NearV3.RcptLink.bytes8_holdsP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.RcptLink.bytes8_holdsP

/-- info: 'ZkFormal.NearV3.Qv.Extract.QvRc.no_group' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Qv.Extract.QvRc.no_group

/-- info: 'ZkFormal.NearV3.Qv.Extract.QvRc.queue_premises' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Qv.Extract.QvRc.queue_premises

/-- info: 'ZkFormal.NearV3.Qv.Extract.QvRc.assemble_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Qv.Extract.QvRc.assemble_sub

/-- info: 'ZkFormal.NearV3.RcptLink.flatR_le_WAK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.RcptLink.flatR_le_WAK

/-- info: 'ZkFormal.NearV3.RcptLink.queue_reads_holdsP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.RcptLink.queue_reads_holdsP

/-- info: 'ZkFormal.NearV3.RcptLink.walkHyp_holdsP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.RcptLink.walkHyp_holdsP

/-- info: 'ZkFormal.NearV3.RcptLink.queue_main_holdsP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.RcptLink.queue_main_holdsP

/-- info: 'ZkFormal.NearV3.RcptLink.mainRun_of_holdsP_q' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.RcptLink.mainRun_of_holdsP_q

/-- info: 'ZkFormal.NearV3.RcptLink.vbytes_perm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.RcptLink.vbytes_perm

/-- info: 'ZkFormal.NearV3.RcptLink.stream_record' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.RcptLink.stream_record

/-- info: 'ZkFormal.NearV3.RcptLink.acct_value_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.RcptLink.acct_value_exact

/-- info: 'ZkFormal.NearV3.RcptLink.akey_value_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.RcptLink.akey_value_exact

/-- info: 'ZkFormal.NearV3.RcptLink.akk_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.RcptLink.akk_value

/-- info: 'ZkFormal.NearV3.RcptLink.bnd_lookup_perm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.RcptLink.bnd_lookup_perm

/-- info: 'ZkFormal.NearV3.RcptLink.prepClaim_ctx_walk' depends on axioms: [propext] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.RcptLink.prepClaim_ctx_walk

/-- info: 'ZkFormal.NearV3.RcptLink.bndp_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.RcptLink.bndp_count

/-- info: 'ZkFormal.NearV3.RcptLink.boundedPrep_self' depends on axioms: [propext, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.RcptLink.boundedPrep_self

/-- info: 'ZkFormal.NearV3.RcptLink.route_holdsP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.RcptLink.route_holdsP

/-- info: 'ZkFormal.NearV3.RcptLink.mainRun_of_holdsP_r' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.RcptLink.mainRun_of_holdsP_r

/-- info: 'ZkFormal.NearV3.RcptLink.hroute_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.RcptLink.hroute_holds

/-- info: 'ZkFormal.NearV3.RcptLink.decodeBody_shape' depends on axioms: [propext, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.RcptLink.decodeBody_shape

/-- info: 'ZkFormal.NearV3.RcptLink.body_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.RcptLink.body_tail

/-- info: 'ZkFormal.NearV3.RcptLink.decodeChunkInner_burnt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.RcptLink.decodeChunkInner_burnt

/-- info: 'ZkFormal.NearV3.RcptLink.walkD0_H' depends on axioms: [propext] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.RcptLink.walkD0_H

/-- info: 'ZkFormal.NearV3.RcptLink.burnt_pub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.RcptLink.burnt_pub

/-- info: 'ZkFormal.NearV3.RcptLink.mainOut_of_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.RcptLink.mainOut_of_run

/-- info: 'ZkFormal.NearV3.RcptLink.runHdr_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.RcptLink.runHdr_of
