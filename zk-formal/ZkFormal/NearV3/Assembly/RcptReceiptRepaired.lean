import ZkFormal.NearV3.Rcpt.Tables.RcptR
import ZkFormal.NearV3.Assembly.RcptCandidateTableLocal

/-! `RcptV3.tableR` (the installed repaired receipt table) is the candidate
`receiptArithmeticCandidate` the renderer and soundness migrations are proved for. -/
namespace ZkFormal.NearV3.Assembly.RcptSkeleton

theorem tableR_eq : RcptV3.tableR = receiptArithmeticCandidate := rfl

end ZkFormal.NearV3.Assembly.RcptSkeleton
