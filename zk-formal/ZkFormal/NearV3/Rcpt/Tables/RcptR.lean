import ZkFormal.NearV3.Rcpt.Tables.Rcpt
import ZkFormal.NearV3.Rcpt.Tables.RcptRDefs

/-!
# ZkFormal.NearV3.Rcpt.Tables.RcptR — the repaired receipt table `rcptV3` (`nearAirV3` table 16)

User decision 2026-10-11: adopt both isolated arithmetic repairs of `RcptV3.table`
(`docs/zk-formal/RCPT-RENDER-CANDIDATE.md`):

* **system gas** (`RcptSystemGasCandidate`): the refund surplus stream is gated by
  `gq = ge·(1 − sys)` instead of `ge`, so a system receipt (no refund) never overflows
  (`RcptGasContradiction.old_gas_surplus_top_zero` showed the original rejects a decodable
  system receipt with gas price `u128::MAX` against block price `0`);
* **deposit age** (`RcptDepositAgeCandidate`): the first-DEP-row version distance `r − tprev`
  is a 13-bit value (`xb53..65`) instead of 9 bits (`RcptDepositContradiction.
  old_deposit_initial_512_impossible`: receipt `≥ 512` reading an initial account).

Same columns, interactions and `maxLog`; 881 constraints.  The parameterized families are
verbatim copies of the candidate modules' (`Assembly/RcptReceiptRepaired.lean` proves
`tableR = receiptArithmeticCandidate` by `rfl`).
-/

namespace ZkFormal.NearV3.RcptV3

open ZkFormal.Air ZkFormal.Near ZkFormal.Near.Dsl

end ZkFormal.NearV3.RcptV3
