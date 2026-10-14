import ZkFormal.Near.Extract.RcptChain
import ZkFormal.Near.Extract.RcptView
import ZkFormal.NearV3.D1.Tables.TxDefs

/-!
# `ZkFormal.NearV3.D1.Extract.TxView` — what `txV3` holds (`TxViewStmt`)

Lane `v3-d1-phase2` (milestone V2).  One `TxE` per 16-row op (in row order): the op constants
and 16 lanes (bytes least significant first).  Values are naturals `< P` (cells); facts that
need byte values are stated under `TxE.Bytes` (the inputs are bytes: the public `TXP` lanes
`N`, `Bd`, `C`, the account lanes `amt`, `lk`, `st` from `MEM`, the key nonce `kn` from
`AKMEM`; the link provides them).

Traffic:
* receives `TXP (16·op + j, kind, strict, ok, tov, stage, cok, Nⱼ, Bdⱼ, Cⱼ)` (`j < 16`),
  `SIG (op, valid)`, `FINAL (W_TX + 2·op, 0, 1 − s1, vidA)` if `fW`, `FINAL (W_TX + 2·op + 1, 0,
  1 − s2, vidK)` if `fK`, `MEM (vidA, tpA, j, amtⱼ, lkⱼ, stⱼ)` if `s1`, `AKMEM (vidK, tpK, j, knⱼ,
  fa)` (`j < 8`) if `s2`;
* sends `MEM (vidA, op + 1, j, moⱼ, lkⱼ, stⱼ)` if `s1`, `AKMEM (vidK, op + 1, j, nkⱼ, fa)`
  (`j < 8`) if `s2`.

Facts (`TxOpWf`): the flag algebra; the gates; the written values (`mo = amt`, `nk = kn` unless
written; written: `nk = N`, `mo` bytes); the memory times `tp + d ≡ op` with `d < 2¹⁴`; and under
byte inputs the verdict: a debit's `ok = 1` iff FullAccess key (`s2 ∧ fa`), the nonce check
(`kn < N`, strict: `N = kn + 1`), `N < Bd`, `C ≤ A`, `A − C + L < 2¹²⁸` and the stake
(`10¹⁹·st mod 2¹²⁸ ≤ A − C + L ∨ st ≤ 770`), the written amount `A − C`; a credit writes
`A + C < 2¹²⁸ − 1` with the stake on `A + C + L`.
-/

namespace ZkFormal.NearV3.D1

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near

structure TxLaneE where
  g : Nat
  xN : Nat
  xB : Nat
  xC : Nat
  amt : Nat
  lk : Nat
  st : Nat
  mo : Nat
  kn : Nat
  nk : Nat
  deriving Repr, Inhabited

structure TxE where
  op : Nat
  kind : Nat
  strict : Nat
  okP : Nat
  tov : Nat
  stage : Nat
  cok : Nat
  valid : Nat
  s1 : Nat
  s2 : Nat
  cand : Nat
  wr : Nat
  fa : Nat
  vidA : Nat
  vidK : Nat
  tpA : Nat
  tpK : Nat
  fW : Nat
  fK : Nat
  ln : List TxLaneE
  deriving Repr, Inhabited

namespace TxE
variable (e : TxE)

def lane (j : Nat) : TxLaneE := e.ln.getD j default

/-- Little-endian value of a lane field over the 16 lanes. -/
def val (f : TxLaneE → Nat) : Nat := ZkFormal.Near.RcptProof.sumL (fun j => f (e.lane j)) 16

/-- The inputs are bytes. -/
def Bytes : Prop :=
  ∀ j, j < 16 → (e.lane j).xN < 256 ∧ (e.lane j).xB < 256 ∧ (e.lane j).xC < 256 ∧
    (e.lane j).amt < 256 ∧ (e.lane j).lk < 256 ∧ (e.lane j).st < 256 ∧ (e.lane j).kn < 256

/-- The verdict and written values under byte inputs. -/
structure Arith : Prop where
  debit : e.kind = 0 →
    (e.okP = 1 ↔ (e.s2 = 1 ∧ e.fa = 1 ∧ e.val TxLaneE.kn < e.val TxLaneE.xN ∧
      (e.strict ≠ 0 → e.val TxLaneE.xN = e.val TxLaneE.kn + 1) ∧
      e.val TxLaneE.xN < e.val TxLaneE.xB ∧ e.val TxLaneE.xC ≤ e.val TxLaneE.amt ∧
      e.val TxLaneE.amt - e.val TxLaneE.xC + e.val TxLaneE.lk < NearSpec.Params.two128 ∧
      ((NearSpec.Params.storageAmountPerByte * e.val TxLaneE.st) % NearSpec.Params.two128 ≤
          e.val TxLaneE.amt - e.val TxLaneE.xC + e.val TxLaneE.lk ∨
        e.val TxLaneE.st ≤ NearSpec.Params.zeroBalanceStorageLimit))) ∧
    (e.wr = 1 → e.val TxLaneE.mo = e.val TxLaneE.amt - e.val TxLaneE.xC)
  credit : e.kind = 1 →
    e.val TxLaneE.mo = e.val TxLaneE.amt + e.val TxLaneE.xC ∧
    e.val TxLaneE.mo < NearSpec.Params.u128Max ∧
    e.val TxLaneE.mo + e.val TxLaneE.lk < NearSpec.Params.two128 ∧
    ((NearSpec.Params.storageAmountPerByte * e.val TxLaneE.st) % NearSpec.Params.two128 ≤
        e.val TxLaneE.mo + e.val TxLaneE.lk ∨
      e.val TxLaneE.st ≤ NearSpec.Params.zeroBalanceStorageLimit)

end TxE

/-- Per-op facts of `txV3`. -/
structure TxOpWf (e : TxE) : Prop where
  len : e.ln.length = 16
  bools : e.kind ≤ 1 ∧ e.strict ≤ 1 ∧ e.okP ≤ 1 ∧ e.tov ≤ 1 ∧ e.cok ≤ 1 ∧ e.valid ≤ 1 ∧
    e.s1 ≤ 1 ∧ e.s2 ≤ 1 ∧ e.fa ≤ 1
  stage : e.stage = e.s1 + e.s2
  s2s1 : e.s2 = 1 → e.s1 = 1
  cand : e.cand = e.valid * e.cok
  debitWalk : e.kind = 0 → e.s1 = 1 → e.cand = 1
  credit : e.kind = 1 → e.s1 = 1 ∧ e.s2 = 0
  fW : e.fW = (if e.kind = 1 then 1 else e.cand)
  fK : e.fK = (if e.kind = 1 then 0 else e.s1)
  wr : e.wr = (if e.kind = 1 then 1 else e.okP * (1 - e.tov))
  lanes : ∀ j, j < 16 →
    Fp.ofNat (e.lane j).g = Fp.ofNat (16 * e.op + j) ∧
    (8 ≤ j → (e.lane j).kn = 0) ∧
    (e.wr = 0 → (e.lane j).mo = (e.lane j).amt ∧ (e.lane j).nk = (e.lane j).kn) ∧
    (e.wr = 1 → (e.lane j).nk = (e.lane j).xN ∧ (e.lane j).mo < 256)
  tA : e.s1 = 1 → ∃ d, d < 2 ^ 14 ∧ Fp.ofNat (e.tpA + d) = Fp.ofNat e.op
  tK : e.s2 = 1 → ∃ d, d < 2 ^ 14 ∧ Fp.ofNat (e.tpK + d) = Fp.ofNat e.op
  arith : e.Bytes → e.Arith
  canon : e.op < P ∧ e.vidA < P ∧ e.vidK < P ∧ e.tpA < P ∧ e.tpK < P ∧
    ∀ j, j < 16 → (e.lane j).g < P ∧ (e.lane j).xN < P ∧ (e.lane j).xB < P ∧ (e.lane j).xC < P ∧
      (e.lane j).amt < P ∧ (e.lane j).lk < P ∧ (e.lane j).st < P ∧ (e.lane j).mo < P ∧
      (e.lane j).kn < P ∧ (e.lane j).nk < P

structure TxWf (es : List TxE) : Prop where
  ops : ∀ e ∈ es, TxOpWf e
  rows : 16 * es.length ≤ 2 ^ TxV3.maxLog

def txSends (es : List TxE) (b : Nat) : List Msg :=
  if b = B_MEM then es.flatMap fun e => if e.s1 = 1 then
      (List.range 16).map fun j => [e.vidA, e.op + 1, j, (e.lane j).mo, (e.lane j).lk, (e.lane j).st]
    else []
  else if b = B_AKMEM then es.flatMap fun e => if e.s2 = 1 then
      (List.range 8).map fun j => [e.vidK, e.op + 1, j, (e.lane j).nk, e.fa]
    else []
  else []

def txRecvs (es : List TxE) (b : Nat) : List Msg :=
  if b = B_TXP then es.flatMap fun e => (List.range 16).map fun j =>
      [(e.lane j).g, e.kind, e.strict, e.okP, e.tov, e.stage, e.cok, (e.lane j).xN, (e.lane j).xB,
       (e.lane j).xC]
  else if b = B_SIG then es.map fun e => [e.op, e.valid]
  else if b = B_FINAL then es.flatMap fun e =>
      (if e.fW = 1 then [[W_TX + 2 * e.op, 0, 1 - e.s1, e.vidA]] else []) ++
      (if e.fK = 1 then [[W_TX + 2 * e.op + 1, 0, 1 - e.s2, e.vidK]] else [])
  else if b = B_MEM then es.flatMap fun e => if e.s1 = 1 then
      (List.range 16).map fun j => [e.vidA, e.tpA, j, (e.lane j).amt, (e.lane j).lk, (e.lane j).st]
    else []
  else if b = B_AKMEM then es.flatMap fun e => if e.s2 = 1 then
      (List.range 8).map fun j => [e.vidK, e.tpK, j, (e.lane j).kn, e.fa]
    else []
  else []

def txTraffic (es : List TxE) : Traffic := ⟨txSends es, txRecvs es⟩

/-- **The `txV3` view statement.** -/
def TxViewStmt : Prop :=
  ∀ (tr : Trace Fp) (pub : List Fp) (t : Nat), TableLocal TxV3.table tr t pub →
    ∃ es, TxWf es ∧ TableTraffic TxV3.interactions tr t pub (txTraffic es)

end ZkFormal.NearV3.D1
