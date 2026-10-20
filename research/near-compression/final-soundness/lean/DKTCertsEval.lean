import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.FirstOrder.Squarefree.Sharp
import ArkLib.Data.CodingTheory.ReedSolomon.ListDecodability.FirstOrder.Profile
open ReedSolomon.CurveProfile ReedSolomon.CurveCertificate ReedSolomon.FirstOrder.Squarefree
open ReedSolomon ReedSolomon.HiddenDerivative Polynomial

namespace DKTEval
def mkProfile (n k A ell m M mu H : ℕ) : LineProfile :=
  let D := k - 1
  let dim := firstOrderDimensionCount D A m M mu
  let slots := firstOrderHeightSlotCount D A m M mu H
  ⟨n, k, A, m, M, mu, ell, dim, certifiedEnlargedRankBound 1 m M 0, dim * (H + 1) - slots, H, slots⟩
def argminConvex (f : ℕ → ℚ) : ℕ → ℕ → ℕ → ℕ
  | 0, lo, _ => lo
  | fuel + 1, lo, hi =>
    if lo < hi then
      let mid := (lo + hi) / 2
      if f mid ≤ f (mid + 1) then argminConvex f fuel lo mid else argminConvex f fuel (mid + 1) hi
    else lo
def ordAt (p : LineProfile) (L0 : ℕ) : ℚ :=
  retainedSquarefreeOrdinaryCurveMCAAt p.n p.D p.batchingDegree L0 p.agreement p.totalJetCap
    p.firstDerivativeCap p.height
def regAt (p : LineProfile) (L : ℕ) : ℚ :=
  regularSymbolicCurveMCADerivativeBoundTwo p.n p.batchingDegree (p.D + 1) (p.D + 1) L p.agreement
    p.totalJetCap p.firstDerivativeCap p.height (hybridTau p.D)
def listQ (p : LineProfile) : ℚ :=
  (firstOrderCurveFiberStageOne p.k p.totalJetCap p.firstDerivativeCap (hybridTau (p.k - 1)) : ℚ) *
    ((p.n - p.k + 1 : ℕ) : ℚ) / ((p.agreement - p.k + 1 : ℕ) : ℚ) +
  (ordinaryDegreeEnvelope p.totalJetCap p.firstDerivativeCap : ℚ)
def report (tag : String) (n k A ell m M mu H : ℕ) : String :=
  let p := mkProfile n k A ell m M mu H
  let L0 := argminConvex (ordAt p) 80 (p.D + 1) A
  let L := argminConvex (regAt p) 80 k A
  let e := ordAt p L0 + regAt p L
  let lq := listQ p
  s!"CERT {tag} dim={p.supportDimension} rank={p.localRank} colw={p.columnY₀Weight} slots={p.heightSlots} rows={p.shiftedRowSlots ell} hs={p.shiftedHeightSlots ell} verified={decide p.CurveVerification} L0={L0} L={L} E={e.num}/{e.den} list={lq.num}/{lq.den} tightlist={(tightListEnvelope p).num}/{(tightListEnvelope p).den}"
end DKTEval

#eval! IO.println (DKTEval.report "31457280,64,34443,1" 31457280 64 34443 1 22 44 12431 520167)
#eval! IO.println (DKTEval.report "31457280,1024,160628,1" 31457280 1024 160628 1 6 6 894 13929)
#eval! IO.println (DKTEval.report "31457280,16384,580789,1" 31457280 16384 580789 1 16 32 538 15869)
#eval! IO.println (DKTEval.report "62914560,128,68886,1" 62914560 128 68886 1 24 48 13561 633495)
#eval! IO.println (DKTEval.report "62914560,2048,321256,1" 62914560 2048 321256 1 6 6 894 14203)
#eval! IO.println (DKTEval.report "62914560,32768,1161578,1" 62914560 32768 1161578 1 16 32 538 15912)
#eval! IO.println (DKTEval.report "125829120,256,137772,1" 125829120 256 137772 1 24 48 13561 1491340)
#eval! IO.println (DKTEval.report "125829120,4096,642511,1" 125829120 4096 642511 1 6 6 894 14346)
#eval! IO.println (DKTEval.report "125829120,65536,2323156,1" 125829120 65536 2323156 1 16 32 538 15933)
#eval! IO.println (DKTEval.report "251658240,512,275544,1" 251658240 512 275544 1 24 48 13561 4677393)
#eval! IO.println (DKTEval.report "251658240,512,275645,1" 251658240 512 275645 1 24 48 13566 2602699)
#eval! IO.println (DKTEval.report "251658240,4096,892417,1" 251658240 4096 892417 1 6 9 1241 15225)
#eval! IO.println (DKTEval.report "251658240,8192,1285022,1" 251658240 8192 1285022 1 6 6 894 14417)
#eval! IO.println (DKTEval.report "251658240,32768,2349001,1" 251658240 32768 2349001 1 12 24 817 11395)
#eval! IO.println (DKTEval.report "251658240,131072,4646311,1" 251658240 131072 4646311 1 16 32 538 15945)
#eval! IO.println (DKTEval.report "251658240,262144,6635860,1" 251658240 262144 6635860 1 16 24 425 19542)
#eval! IO.println (DKTEval.report "503316480,1024,551087,1" 503316480 1024 551087 1 26 52 14692 780761)
#eval! IO.println (DKTEval.report "503316480,1024,551289,1" 503316480 1024 551289 1 24 48 13566 6462556)
#eval! IO.println (DKTEval.report "503316480,8192,1784834,1" 503316480 8192 1784834 1 6 9 1241 15282)
#eval! IO.println (DKTEval.report "503316480,16384,2570043,1" 503316480 16384 2570043 1 6 6 894 14454)
#eval! IO.println (DKTEval.report "503316480,65536,4698001,1" 503316480 65536 4698001 1 12 24 817 11402)
#eval! IO.println (DKTEval.report "503316480,262144,9292622,1" 503316480 262144 9292622 1 16 32 538 15950)
#eval! IO.println (DKTEval.report "503316480,524288,13271719,1" 503316480 524288 13271719 1 16 24 425 19549)
#eval! IO.println (DKTEval.report "503316480,524288,13271719,140" 503316480 524288 13271719 140 16 24 425 2736971)
#eval! IO.println (DKTEval.report "503316480,524288,16371380,140" 503316480 524288 16371380 140 4 2 118 120643)
#eval! IO.println (DKTEval.report "1006632960,2048,1102577,1" 1006632960 2048 1102577 1 24 48 13566 25109834)
#eval! IO.println (DKTEval.report "1006632960,16384,3569668,1" 1006632960 16384 3569668 1 6 9 1241 15311)
#eval! IO.println (DKTEval.report "1006632960,131072,9396001,1" 1006632960 131072 9396001 1 12 24 817 11405)
#eval! IO.println (DKTEval.report "1006632960,262144,13564120,1" 1006632960 262144 13564120 1 10 15 491 14008)
#eval! IO.println (DKTEval.report "2013265920,4096,2205154,1" 2013265920 4096 2205154 1 26 52 14697 781226)
#eval! IO.println (DKTEval.report "2013265920,32768,7139336,1" 2013265920 32768 7139336 1 6 9 1241 15326)
#eval! IO.println (DKTEval.report "2013265920,262144,18792001,1" 2013265920 262144 18792001 1 12 24 817 11407)
#eval! IO.println (DKTEval.report "2013265920,524288,27128239,1" 2013265920 524288 27128239 1 10 15 491 14010)
#eval! IO.println (DKTEval.report "2013265920,524288,27128239,140" 2013265920 524288 27128239 140 10 15 491 1961426)
#eval! IO.println (DKTEval.report "2013265920,524288,32742759,140" 2013265920 524288 32742759 140 4 2 237 226324)
#eval! IO.println (DKTEval.report "2013265920,2097152,65485518,600" 2013265920 2097152 65485518 600 4 2 118 517056)
