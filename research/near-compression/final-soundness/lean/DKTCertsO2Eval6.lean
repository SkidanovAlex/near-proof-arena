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

#eval! IO.println (DKTEval.report "125829120,64,68730,1" 125829120 64 68730 1 22 44 24807 1622780)
#eval! IO.println (DKTEval.report "125829120,512,196057,1" 125829120 512 196057 1 22 44 8845 583227)
#eval! IO.println (DKTEval.report "125829120,1024,278313,1" 125829120 1024 278313 1 20 40 5707 2186122)
#eval! IO.println (DKTEval.report "125829120,8192,799757,1" 125829120 8192 799757 1 18 36 1845 67226)
#eval! IO.println (DKTEval.report "125829120,16384,1139277,1" 125829120 16384 1139277 1 16 32 1168 151533)
#eval! IO.println (DKTEval.report "251658240,64,97014,1" 251658240 64 97014 1 22 44 35015 6882843)
#eval! IO.println (DKTEval.report "251658240,128,137459,1" 251658240 128 137459 1 24 48 27062 2117854)
#eval! IO.println (DKTEval.report "251658240,1024,392113,1" 251658240 1024 392113 1 22 44 8845 733762)
#eval! IO.println (DKTEval.report "251658240,1024,392125,1" 251658240 1024 392125 1 22 44 8845 722207)
#eval! IO.println (DKTEval.report "251658240,2048,556626,1" 251658240 2048 556626 1 20 40 5707 5478485)
#eval! IO.println (DKTEval.report "251658240,16384,1599513,1" 251658240 16384 1599513 1 18 36 1845 67730)
#eval! IO.println (DKTEval.report "251658240,16384,1599516,1" 251658240 16384 1599516 1 18 36 1845 67700)
#eval! IO.println (DKTEval.report "503316480,128,194028,1" 503316480 128 194028 1 24 48 38199 14892369)
#eval! IO.println (DKTEval.report "503316480,256,274918,1" 503316480 256 274918 1 24 48 27062 58787535)
#eval! IO.println (DKTEval.report "503316480,2048,784225,1" 503316480 2048 784225 1 22 44 8845 842679)
#eval! IO.println (DKTEval.report "503316480,2048,784249,1" 503316480 2048 784249 1 22 44 8845 827456)
#eval! IO.println (DKTEval.report "503316480,4096,1113251,1" 503316480 4096 1113251 1 20 40 5707 22741268)
#eval! IO.println (DKTEval.report "503316480,32768,3199026,1" 503316480 32768 3199026 1 18 36 1845 67980)
#eval! IO.println (DKTEval.report "503316480,32768,3199032,1" 503316480 32768 3199032 1 18 36 1845 67949)
#eval! IO.println (DKTEval.report "1006632960,256,388055,1" 1006632960 256 388055 1 26 52 41382 4508205)
#eval! IO.println (DKTEval.report "1006632960,512,549835,1" 1006632960 512 549835 1 26 52 29317 2207244)
#eval! IO.println (DKTEval.report "1006632960,4096,1568450,1" 1006632960 4096 1568450 1 22 44 8845 909913)
#eval! IO.println (DKTEval.report "1006632960,4096,1568498,1" 1006632960 4096 1568498 1 22 44 8845 892179)
#eval! IO.println (DKTEval.report "1006632960,8192,2226502,1" 1006632960 8192 2226502 1 22 44 6278 236650)
#eval! IO.println (DKTEval.report "1006632960,65536,6398051,1" 1006632960 65536 6398051 1 18 36 1845 68108)
#eval! IO.println (DKTEval.report "1006632960,65536,6398063,1" 1006632960 65536 6398063 1 18 36 1845 68078)
#eval! IO.println (DKTEval.report "1006632960,262144,13000110,1" 1006632960 262144 13000110 1 16 32 833 31591)
#eval! IO.println (DKTEval.report "2013265920,512,776109,1" 2013265920 512 776109 1 26 52 41382 13704405)
#eval! IO.println (DKTEval.report "2013265920,1024,1099669,1" 2013265920 1024 1099669 1 26 52 29317 2872250)
#eval! IO.println (DKTEval.report "2013265920,8192,3136899,1" 2013265920 8192 3136899 1 22 44 8845 947940)
#eval! IO.println (DKTEval.report "2013265920,8192,3136995,1" 2013265920 8192 3136995 1 22 44 8845 928702)
#eval! IO.println (DKTEval.report "2013265920,16384,4453003,1" 2013265920 16384 4453003 1 22 44 6278 238397)
#eval! IO.println (DKTEval.report "2013265920,131072,12796101,1" 2013265920 131072 12796101 1 18 36 1845 68172)
#eval! IO.println (DKTEval.report "2013265920,131072,12796125,1" 2013265920 131072 12796125 1 18 36 1845 68142)
#eval! IO.println (DKTEval.report "2013265920,524288,26000219,1" 2013265920 524288 26000219 1 16 32 833 31599)
#eval! IO.println (DKTEval.report "4026531840,16384,6273989,1" 4026531840 16384 6273989 1 22 44 8845 948113)
#eval! IO.println (DKTEval.report "4026531840,262144,25592250,1" 4026531840 262144 25592250 1 18 36 1845 68173)
#eval! IO.println (DKTEval.report "4026531840,1048576,52000438,1" 4026531840 1048576 52000438 1 16 32 833 31603)
#eval! IO.println (DKTEval.report "4026531840,1048576,52000438,52" 4026531840 1048576 52000438 52 16 32 833 1643373)
#eval! IO.println (DKTEval.report "4026531840,1048576,52000438,140" 4026531840 1048576 52000438 140 16 32 833 4424467)
#eval! IO.println (DKTEval.report "4026531840,1048576,52000438,600" 4026531840 1048576 52000438 600 18 36 848 9563028)
#eval! IO.println (DKTEval.report "4026531840,1048576,65485518,52" 4026531840 1048576 65485518 52 4 2 237 84064)
#eval! IO.println (DKTEval.report "4026531840,1048576,65485518,140" 4026531840 1048576 65485518 140 4 2 237 226328)
#eval! IO.println (DKTEval.report "4026531840,1048576,65485518,600" 4026531840 1048576 65485518 600 4 2 237 969978)
