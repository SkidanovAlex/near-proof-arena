import ZkFormal.NearV3.Assembly.RcptCandidateNaturalTotals
import ZkFormal.NearV3.Rcpt.Extract.V.PreparedRanges
import ZkFormal.NearV3.Sched.Pub.Prep
import ZkFormal.NearV3.Candidates.ProcessRepairForeignByteTags
import ZkFormal.NearV3.Candidates.ProcessRepairQueuePublicCore
namespace ZkFormal.NearV3.Candidates.ProcessRepairQueuePublic
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.V2 NearSpecV3
open RcptV3Proof Assembly.ReceiptCandidateProof
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

theorem receipt_count {AP:AirP} {tr:Trace Fp}
    {cb:NearSpec.Bytes} {hint:Hint} {p:Prep} (hp:prepD0 cb hint=.ok p) (overhead:Nat)
    (view:ProcessRepairInterface.View AP (ZkFormal.Udr.pubOf Fp (Public.preparedBytes p overhead)) tr)
    {bs:List ListBlock} {e:Nat} (hc:ListChain (ProcPriorRoutedReceiptView.receipt tr) 0 0 bs e) :
    (bs.map fun B=>B.receipts.length).sum=p.hdr.n ∧
    (bs.map fun B=>B.receipts.length).sum≤W_AK := by
  have he:=prepared_receipt_count hp overhead (Assembly.prepD0_roots hp)
  have hn:=prepD0_count_bound hp
  have hl:=Assembly.ReceiptCandidateProof.repaired_local_base
    (ProcessRepairForeignByteTags.local_receipt view)
  have hs:=ListChain.natural_count hl hc (by rw [he];exact hn.2)
    (fun i _=>public_byte p overhead (PH_N+i))
  rw [he] at hs
  refine ⟨hs,?_⟩
  rw [hs]
  change p.hdr.n≤8192
  omega

end ZkFormal.NearV3.Candidates.ProcessRepairQueuePublic
