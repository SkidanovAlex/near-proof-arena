import ZkFormal.NearV3.Rcpt.Tables.RcptR
import ZkFormal.NearV3.Assembly.RcptCandidateTableLocal
import ZkFormal.NearV3.Assembly.RcptCandidateRoutingTrace

/-! `RcptV3.tableR` (the installed repaired receipt table) is the candidate
`receiptArithmeticCandidate` the renderer and soundness migrations are proved for. -/
namespace ZkFormal.NearV3.Assembly.RcptSkeleton

theorem tableR_eq : RcptV3.tableR = receiptArithmeticCandidate := rfl

/-- The installed table 16 (`tableR` + routing-index range check) is the routing candidate
over the arithmetic repairs (`booleanReceiptTrace_native_repaired_tableLocal` is proved for it). -/
theorem tableQ_eq : RcptV3.tableQ = ReceiptCandidateRouting.candidateTable := rfl

end ZkFormal.NearV3.Assembly.RcptSkeleton
