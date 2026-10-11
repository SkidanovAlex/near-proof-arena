import ZkFormal.NearV3.Assembly.RenderV3Bundle
import ZkFormal.NearV3.Render.HonestBalanceBnd
import ZkFormal.NearV3.Render.PaddedQvNative
import ZkFormal.NearV3.Render.PaddedSrcp
import ZkFormal.NearV3.Render.PaddedRcpt
import ZkFormal.NearV3.Render.PaddedAcctE

/-!
# `TableRenderV3` instances for the receipt-side tables 16–20 and 22

Each instance packages one honest aligned render (`Render/Padded*.lean`) at its fixed
`nearAirV3` index: the trace, its exact traffic, local legality against
`nearAirV3.tables[t]`, and the roll-aligned height.  The hypotheses are the per-table honest
conditions (`RcptOk`, `AcctV3OkE`, `AkeyOk`, the bnd row bound, `SrcpWf` + A10, `QvNativeOk`).
Table 21 is `UnfoldA7.sizeA7` (A7, lane `v3-trie-complete`).
-/

namespace ZkFormal.NearV3.Assembly
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near
open ZkFormal.NearV3.Render ZkFormal.NearV3.Assembly.RcptSkeleton

/-- Table 16 (`rcptV3`, repaired, ranked boundary counters). -/
def rcptRenderV3 (pub : List Fp) (x : RcptInput) (ok : RcptOk pub x) :
    TableRenderV3 pub 16 (by decide) where
  tr := rcptTraceAlignedB pub x
  tf := rcptTrafficB pub x
  loc := (rcpt_aligned_completeB pub x ok 16).1
  traffic := (rcpt_aligned_completeB pub x ok 16).2.1
  aligned := (rcpt_aligned_completeB pub x ok 16).2.2

/-- Table 17 (`acctTableV3`: `acctV3` at cap 19 with the empty-chunk repair; `as = []` allowed). -/
noncomputable def acctRenderV3 (pub : List Fp) (as : List AcctV) (ok : AcctV3OkE as) :
    TableRenderV3 pub 17 (by decide) where
  tr := acctTraceAlignedE as
  tf := acctV3Traffic as
  loc := (acct_aligned_completeE as ok 17 pub).1
  traffic := (acct_aligned_completeE as ok 17 pub).2.1
  aligned := (acct_aligned_completeE as ok 17 pub).2.2

/-- Table 18 (`akeyV3`). -/
def akeyRenderV3 (pub : List Fp) (es : List AkeyE) (ok : AkeyOk es) :
    TableRenderV3 pub 18 (by decide) where
  tr := akeyTraceAligned es
  tf := akeyTraffic es
  loc := (akey_aligned_complete es ok 18 pub).1
  traffic := (akey_aligned_complete es ok 18 pub).2.1
  aligned := (akey_aligned_complete es ok 18 pub).2.2

/-- Table 19 (`bndV3`). -/
def bndRenderV3 (pub : List Fp) (es : List BndE) (hn : es.length ≤ 2 ^ BndV3.maxLog) :
    TableRenderV3 pub 19 (by decide) where
  tr := bndTraceAligned es
  tf := bndTraffic es
  loc := (bnd_aligned_complete es hn 19 pub).1
  traffic := (bnd_aligned_complete es hn 19 pub).2.1
  aligned := (bnd_aligned_complete es hn 19 pub).2.2

/-- Table 20 (`srcpV3` with the A10 depth check). -/
def srcpRenderV3 (pub : List Fp) (bs : List SrcpB) (h : SrcpWf bs)
    (hd : ∀ B ∈ bs, B.path.length ≤ NearSpecV3.Dp0) : TableRenderV3 pub 20 (by decide) where
  tr := srcpTraceAligned bs
  tf := srcpTraffic bs
  loc := (srcp_aligned_complete bs h hd 20 pub).1
  traffic := (srcp_aligned_complete bs h hd 20 pub).2.1
  aligned := (srcp_aligned_complete bs h hd 20 pub).2.2

/-- Table 22 (`qvV3`, repaired key interface), over native queue inputs. -/
def qvRenderV3 (pub : List Fp) (pre : NearSpec.PTrie) (v : Qv.MainValues) (pres : List NearSpec.PTrie)
    (ok : QvNativeOk pre v pres pub) : TableRenderV3 pub 22 (by decide) where
  tr := qvNativeTrace pre v pres
  tf := qvNativeTraffic pre v pres
  loc := (qv_native_aligned_complete pre v pres pub ok 22).1
  traffic := (qv_native_aligned_complete pre v pres pub ok 22).2.1
  aligned := (qv_native_aligned_complete pre v pres pub ok 22).2.2

end ZkFormal.NearV3.Assembly
