import ZkFormal.NearV3.Rcpt.Tables.Rcpt.Arith
import ZkFormal.NearV3.Rcpt.Tables.RcptDefs

/-!
# ZkFormal.NearV3.Rcpt.Tables.Rcpt — `rcptV3`: the applied receipts

v1's `rcpt` (`Near/Tables/Rcpt.lean`, NEAR-AIR.md §3.3) for `NearSpecV3.applyReceipts`
(V3-D0-DESIGN §3.4): one row per emitted byte; per applied source list `j` a 12-row header
then its receipts (one segment each, v1's fields); then padding.

Interactions:
* 3 × `BYTES` send: `RC(j)` (the list `u64 own ‖ u32 n_j ‖ Σ borsh(receipt)`, consumed by
  `srcpV3`), `PEO(r)`, `LEAF(r)`, `RID(r)` (as v1), and the refund body `(K_RF, pos, byte)`,
  `pos ≥ 8`, received by the public bus (`B`, positions pinned by `|B|`);
* `DIGEST` receive (refund id and `H(PEO(r))`, as v1);
* `KEYNIB` send × 2 (slots A / B): the account walk `r` (`[0] ‖ receiver`) and, for a gas
  refund of a system receipt, the access-key walk `W_AK + r` (`[2] ‖ signer ‖ [2] ‖ pk`);
* `FINAL` receive: account walk → value record `kslot` (`VAL`); access-key walk → absent or
  `kF` (`VAL`);
* `MEM` read / write (balances of value record `kslot`, as v1);
* `RIDS` send (ids, for `sortV3`); `MPOS` send (outcome leaf `r`, for `mrkV3`);
* `RCL (j, |RC(j)|)` send (last row of list `j`, for `srcpV3`);
* `SREC` send / receive (signer = receiver test);
* `AKC` receive / send (present access key `kF`, chained through `akeyV3`);
* `BND` receive / send (routing lookups, chained through `bndV3`).
-/

namespace ZkFormal.NearV3.RcptV3

open ZkFormal.Air ZkFormal.Near ZkFormal.Near.Dsl

end ZkFormal.NearV3.RcptV3
