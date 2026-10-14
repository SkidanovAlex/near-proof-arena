import ZkFormal.NearV3.Rcpt.Tables.Rcpt.Fields
import ZkFormal.Near.Tables.Rcpt.Arith
import ZkFormal.NearV3.Rcpt.Tables.Rcpt.ArithDefs

/-!
# ZkFormal.NearV3.Rcpt.Tables.Rcpt.Arith — registers, ids, keys, gas, balances, v3 checks

v1's `Rcpt.Arith` (`Near/Tables/Rcpt/Arith.lean`) without the claim rows, and:

* **Registers.** The list header loads `u64 own` (public) and the two bytes of `n_j`; `bgp`
  and `height` come from the prepared header (`PH_GP`, `PH_HEIGHT`).  `tok` starts at `0`
  and is compared with `H.prev_balance_burnt` (`PH_BURNT`) on the last active row.
* **System receipts** (`sys`): predecessor `= "system"` (both directions: `sys = 1 ⇒` length 6
  and the six bytes match, `sys = 0 ⇒` v1's inequality witness); no refund, burn price `0`
  (`pc = (1 − sys)·p`, so `burnt = 0`, tokens unchanged, outcome `tokens_burnt = 0`).
* **Signer = receiver** (`ee`, only with `sys`): with `ee` every signer byte receives the
  receiver byte at its position on `SREC (r, i, ·)` (and `Ls = Lv`); without `ee` a system
  receipt shows `Ls ≠ Lv` (`dz`) or one position whose bytes differ (`dd`).
* **Access-key walk** (`ee`): key `[2] ‖ signer ‖ [2] ‖ pk.encode` on `KEYNIB` (walk
  `W_AK + r`; symbols from the `T0`, `SL`, `S`, `KT`, `PK` rows, `END` on the first `GP` row);
  its `FINAL` on the `T0` row: absent, or a value record `kF` validated by `akeyV3` (`AKC`).
* **Routing (A2)**: the receiver against the own interval `q` (`[lo, hi)`), byte by byte on the
  `V` rows and at position `Lv` on the first `RID` row (where the receiver byte is `0`, the
  end marker), with chained `BND` lookups while undecided.
-/

namespace ZkFormal.NearV3.RcptV3

open ZkFormal.Air ZkFormal.Near ZkFormal.Near.Dsl NearSpec

/-! ## Expression helpers (v1's, over `rcptV3`'s column names) -/

/-! ## Registers -/

/-! ## Account ids, `"system"` -/

/-! ## Key symbols: account walk (`r`) and access-key walk (`W_AK + r`) -/

/-! ## System receipts, signer = receiver -/

/-! ## Routing (A2) -/

/-! ## Gas (`GP` rows) -/

/-! ## Balances (`DEP` rows): v1's -/

/-! ## End of the active part, digest lookups -/

end ZkFormal.NearV3.RcptV3
