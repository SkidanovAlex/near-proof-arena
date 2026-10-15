import ZkFormal.NearV3.Assembly.LinkV3
import ZkFormal.NearV3.D1.R.ViewDefs
import ZkFormal.NearV3.D1.Extract.TxView
import ZkFormal.NearV3.D1.Extract.AkmView
import ZkFormal.NearV3.D1.Extract.PlfProof
import ZkFormal.NearV3.D1.Extract.RidProof
import ZkFormal.NearV3.D1.StmtsT
import ZkFormal.NearV3.D1.Extract.AirD1
import ZkFormal.NearV3.D1.Extract.KibD1Proof

/-!
# `ZkFormal.NearV3.D1.Link.RecordsDefs` — the records and the record-form balance of `nearAirV3D1` (L1)

Lane `v3-d1-phase2`, item L1.  Definitions only.  The D1 analogue of `Assembly.LinkV3`'s
`V3Records` / `V3RecordsWf` / `V3RecordsTraffic` / `balSum` / `V3Balance`:

* `D1Records`: D0a's records (`base : V3Records`; the receipt lists are `rcptV3D1`'s, the
  `mrk` view is `mrkViewD1`'s) and the records of the five D1 tables (`txV3`, `akmV3`,
  `kibV3`, `plfV3`, `ridV3`);
* `BaseWfD1` / `BaseTrafficD1`: D0a's fields with the receipt facts `RcptV3WfD1` and
  `rcptV3D1`'s traffic (`tableQD1.interactions`, `rcptTraffic3D1`) at table 16;
* `balSumD1`: the bus count of the 33 tables in record form (D0a's sum for tables `0 … 24`,
  then the five D1 tables); `D1Balance` adds `pubCount nearAirV3D1`;
* `LinkInputsD1`: everything the link receives (preparation, tape bound, `HoldsP`, records,
  SHA contracts, balance), so that the link statements (`Link/Statements`) stay short.
-/

namespace ZkFormal.NearV3.D1.Link

open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 NearSpec NearSpecV3 ZkFormal.NearV3.D1
open ZkFormal.NearV3.D1.RcptD1 ZkFormal.NearV3.Assembly

/-- The records of `nearAirV3D1`'s viewed tables. -/
structure D1Records where
  base : ZkFormal.NearV3.Assembly.V3Records
  txs : List TxE
  akms : List AkmE
  kibs : List KibE
  plfs : List PlfE
  rids : List RidE

/-- D0a's view post-conditions with the D1 receipt facts. -/
structure BaseWfD1 (pub : List Fp) (r : V3Records) : Prop where
  nodes : ZkFormal.NearV3.NodeWf3 r.nodes
  heads : ZkFormal.NearV3.HeadWf r.heads
  values : ZkFormal.NearV3.ValWf r.values
  walks : ZkFormal.NearV3.WalkWf3 r.walks
  walkSteps : (r.walks.flatMap (·.steps)).length ≤ 2 ^ 22
  uniq : ZkFormal.NearV3.UniqWf r.uniq
  ups : ZkFormal.NearV3.UpsWf r.ups
  lists : RcptV3WfD1 pub r.lists
  accts : ZkFormal.NearV3.AcctV3WfE 19 r.accts
  akeys : ZkFormal.NearV3.AkeyWf r.akeys
  bnds : ZkFormal.NearV3.BndWf r.bnds
  srcp : ZkFormal.NearV3.DDWf r.srcp r.srcpRep
  /-- A10 from the AIR (`SrcpDD.table`): every source block's path has `≤ Dp0` items. -/
  srcpDepth : ∀ B ∈ r.srcp, B.path.length ≤ NearSpecV3.Dp0
  size : ZkFormal.NearV3.SizeWf pub r.size
  mrk : ZkFormal.NearV3.Assembly.MrkWfE pub r.mrkE r.mrk
  /-- at most `2^22` receipt lists and receipts (physical rows, `rcptV3_view_counts`) -/
  listsCount : r.lists.length ≤ 2 ^ 22 ∧ (ZkFormal.NearV3.flatR r.lists).length ≤ 2 ^ 22
  /-- every receipt's routing quotient is `< 128` (table 16, `RcptV3.tableQ`) -/
  listsQ : ∀ x ∈ ZkFormal.NearV3.flatR r.lists, x.q < 128
  /-- A7 (`sizeA7`): `B0 − Σ y_t` is a 24-bit value -/
  a7size : ZkFormal.NearV3.A7SizeWf r.a7
  /-- A7 (`upsA7`): `nD = Σ dd_i · N_i` on every segment's first row -/
  a7ups : ZkFormal.NearV3.UpsA7Wf r.ups

/-- D0a's exact traffic with `rcptV3D1` at table 16. -/
structure BaseTrafficD1 (pub : List Fp) (tr : Trace Fp) (r : V3Records) : Prop where
  nodes : ZkFormal.Near.TableTraffic ZkFormal.NearV3.NodeV3.interactions tr ZkFormal.NearV3.Assembly.T_NODE pub
    (ZkFormal.NearV3.nodeTraffic3 r.nodes)
  heads : ZkFormal.Near.TableTraffic ZkFormal.NearV3.HeadV3.interactions tr ZkFormal.NearV3.Assembly.T_HEAD pub
    (ZkFormal.NearV3.headTraffic r.heads)
  values : ZkFormal.Near.TableTraffic ZkFormal.NearV3.ValV3.interactions tr ZkFormal.NearV3.Assembly.T_VAL pub
    (ZkFormal.NearV3.valTraffic r.values)
  walks : ZkFormal.Near.TableTraffic ZkFormal.NearV3.WalkV3.interactions tr ZkFormal.NearV3.Assembly.T_WALK pub
    (ZkFormal.NearV3.walkTraffic3 r.walks)
  uniq : ZkFormal.Near.TableTraffic ZkFormal.NearV3.Uniq.interactions tr ZkFormal.NearV3.Assembly.T_UNIQ pub
    (ZkFormal.NearV3.uniqTraffic r.uniq)
  ups : ZkFormal.Near.TableTraffic ZkFormal.NearV3.UpsV3.interactions tr ZkFormal.NearV3.Assembly.T_UPS pub
    (ZkFormal.NearV3.upsTraffic r.ups)
  lists : ZkFormal.Near.TableTraffic RcptD1.tableQD1.interactions tr 16 pub (rcptTraffic3D1 pub r.lists)
  accts : ZkFormal.Near.TableTraffic ZkFormal.NearV3.AcctV3.interactions tr ZkFormal.NearV3.Assembly.T_ACCT pub
    (ZkFormal.NearV3.acctV3Traffic r.accts)
  akeys : ZkFormal.Near.TableTraffic ZkFormal.NearV3.AkeyV3.interactions tr ZkFormal.NearV3.Assembly.T_AKEY pub
    (ZkFormal.NearV3.akeyTraffic r.akeys)
  bnds : ZkFormal.Near.TableTraffic ZkFormal.NearV3.BndV3.interactions tr ZkFormal.NearV3.Assembly.T_BND pub
    (ZkFormal.NearV3.bndTraffic r.bnds)
  srcp : ZkFormal.Near.TableTraffic ZkFormal.NearV3.Rcpt.Candidates.DedupTable.interactions tr ZkFormal.NearV3.Assembly.T_SRCP pub
    (ZkFormal.NearV3.ddTraffic r.srcp r.srcpRep)
  size : ZkFormal.Near.TableTraffic ZkFormal.NearV3.SizeV3.interactions tr ZkFormal.NearV3.Assembly.T_SIZE pub
    (ZkFormal.NearV3.sizeTraffic r.size)
  mrk : ZkFormal.Near.TableTraffic ZkFormal.NearV3.Candidates.MerkleEmpty.table.interactions tr
    ZkFormal.NearV3.Assembly.T_MRK pub (ZkFormal.NearV3.Assembly.mrkTrafficE pub r.mrkE r.mrk)
  /-- the A7 interactions appended to `nodeV3`, `valV3`, `upsV3`, `sizeV3` (`Tables/UnfoldA7.lean`) -/
  a7nodes : ZkFormal.Near.TableTraffic ZkFormal.NearV3.UnfoldA7.Node.interactions tr ZkFormal.NearV3.Assembly.T_NODE pub
    (ZkFormal.NearV3.a7NodeTraffic r.nodes r.rplN)
  a7values : ZkFormal.Near.TableTraffic ZkFormal.NearV3.UnfoldA7.Val.interactions tr ZkFormal.NearV3.Assembly.T_VAL pub
    (ZkFormal.NearV3.a7ValTraffic r.values r.rplV)
  a7ups : ZkFormal.Near.TableTraffic ZkFormal.NearV3.UnfoldA7.Ups.interactions tr ZkFormal.NearV3.Assembly.T_UPS pub
    (ZkFormal.NearV3.a7UpsTraffic r.ups)
  a7size : ZkFormal.Near.TableTraffic ZkFormal.NearV3.UnfoldA7.Size.interactions tr ZkFormal.NearV3.Assembly.T_SIZE pub
    (ZkFormal.NearV3.a7SizeTraffic r.a7)
  /-- table 20's records are its dedup block chain, with the chain's repetition bits -/
  srcpChain : ∃ e, ZkFormal.NearV3.Rcpt.Candidates.DedupProof.BlockChain tr ZkFormal.NearV3.Assembly.T_SRCP 0 r.srcp e ∧
    r.srcpRep = (ZkFormal.NearV3.Rcpt.Candidates.DedupProof.sourceViews tr ZkFormal.NearV3.Assembly.T_SRCP 0 r.srcp).map Prod.snd

/-- The view post-conditions of all records. -/
structure D1RecordsWf (pub : List Fp) (r : D1Records) : Prop where
  base : BaseWfD1 pub r.base
  txs : TxWf r.txs
  akms : AkmWf r.akms
  kibs : KibD1Wf r.kibs
  plfs : PlfWf r.plfs
  rids : RidWf r.rids

/-- The exact traffic of all records. -/
structure D1RecordsTraffic (pub : List Fp) (tr : Trace Fp) (r : D1Records) : Prop where
  base : BaseTrafficD1 pub tr r.base
  txs : ZkFormal.Near.TableTraffic TxV3.interactions tr T_TX pub (txTraffic r.txs)
  akms : ZkFormal.Near.TableTraffic AkmV3.interactions tr T_AKM pub (akmTraffic r.akms)
  kibs : ZkFormal.Near.TableTraffic KibD1.interactions tr T_KIB pub (kibD1Traffic r.kibs)
  plfs : ZkFormal.Near.TableTraffic PlfV3.interactions tr T_PLF pub (plfTraffic r.plfs)
  rids : ZkFormal.Near.TableTraffic RidV3.interactions tr T_RID pub (ridTraffic r.rids)

/-- D0a's `balSum` for the first 25 tables of `nearAirV3D1` (table 16 read through
`rcptTraffic3D1`, table 23 is `mrkV3` with D0a's interactions). -/
def balSumBaseD1 (pub : List Fp) (tr : Trace Fp) (r : V3Records) (b : Nat) (s : Bool) (m : List Fp) : Nat :=
  tableBusCount shaTable.interactions tr ZkFormal.NearV3.Assembly.T_SHA_T pub b s m +
  (tableBusCount shaTable.interactions tr ZkFormal.NearV3.Assembly.T_SHA_R pub b s m +
  ((ZkFormal.NearV3.Assembly.tcnt (ZkFormal.NearV3.nodeTraffic3 r.nodes) s b m +
      tableBusCount ZkFormal.NearV3.UnfoldA7.Node.interactions tr ZkFormal.NearV3.Assembly.T_NODE pub b s m +
      tableBusCount NodeStub.interactions tr ZkFormal.NearV3.Assembly.T_NODE pub b s m) +
  (ZkFormal.NearV3.Assembly.tcnt (ZkFormal.NearV3.headTraffic r.heads) s b m +
  ((ZkFormal.NearV3.Assembly.tcnt (ZkFormal.NearV3.valTraffic r.values) s b m +
      tableBusCount ZkFormal.NearV3.UnfoldA7.Val.interactions tr ZkFormal.NearV3.Assembly.T_VAL pub b s m) +
  (ZkFormal.NearV3.Assembly.tcnt (ZkFormal.NearV3.walkTraffic3 r.walks) s b m +
  ((ZkFormal.NearV3.Assembly.tcnt (ZkFormal.NearV3.uniqTraffic r.uniq) s b m +
      tableBusCount UniqGap.interactions tr ZkFormal.NearV3.Assembly.T_UNIQ pub b s m) +
  ((ZkFormal.NearV3.Assembly.tcnt (ZkFormal.NearV3.upsTraffic r.ups) s b m +
      tableBusCount ZkFormal.NearV3.UnfoldA7.Ups.interactions tr ZkFormal.NearV3.Assembly.T_UPS pub b s m) +
  (tableBusCount (ZkFormal.Chacha.Table.table22 ZkFormal.NearV3.Sched.B_SCHACHA).interactions
    tr ZkFormal.NearV3.Assembly.T_CHACHA pub b s m +
  (tableBusCount (ZkFormal.Chacha.Rng.Table.table22 ZkFormal.NearV3.Sched.B_SCHACHA
    ZkFormal.NearV3.Sched.B_SGEN).interactions tr ZkFormal.NearV3.Assembly.T_RNG pub b s m +
  (tableBusCount (ZkFormal.Chacha.Shuffle.Table.table22 ZkFormal.NearV3.Sched.B_SSIN
    ZkFormal.NearV3.Sched.B_SSOUT ZkFormal.NearV3.Sched.B_SSMEM ZkFormal.NearV3.Sched.B_SGEN
    ZkFormal.NearV3.Sched.B_SSHUF).interactions tr ZkFormal.NearV3.Assembly.T_SHUF pub b s m +
  (tableBusCount ZkFormal.NearV3.Sched.Codec.table.interactions tr ZkFormal.NearV3.Assembly.T_CODEC pub b s m +
  (tableBusCount ZkFormal.NearV3.Sched.ScanDist.table.interactions tr ZkFormal.NearV3.Assembly.T_SSD pub b s m +
  (tableBusCount ZkFormal.NearV3.Sched.Proc.table.interactions tr ZkFormal.NearV3.Assembly.T_PROC pub b s m +
  (tableBusCount ZkFormal.NearV3.Sched.Mem.table.interactions tr ZkFormal.NearV3.Assembly.T_MEM pub b s m +
  (tableBusCount (ZkFormal.NearV3.Sched.Cmp.table ZkFormal.NearV3.Sched.B_SCMP).interactions
    tr ZkFormal.NearV3.Assembly.T_CMP pub b s m +
  (ZkFormal.NearV3.Assembly.tcnt (rcptTraffic3D1 pub r.lists) s b m +
  (ZkFormal.NearV3.Assembly.tcnt (ZkFormal.NearV3.acctV3Traffic r.accts) s b m +
  (ZkFormal.NearV3.Assembly.tcnt (ZkFormal.NearV3.akeyTraffic r.akeys) s b m +
  (ZkFormal.NearV3.Assembly.tcnt (ZkFormal.NearV3.bndTraffic r.bnds) s b m +
  (ZkFormal.NearV3.Assembly.tcnt (ZkFormal.NearV3.ddTraffic r.srcp r.srcpRep) s b m +
  ((ZkFormal.NearV3.Assembly.tcnt (ZkFormal.NearV3.sizeTraffic r.size) s b m +
      tableBusCount ZkFormal.NearV3.UnfoldA7.Size.interactions tr ZkFormal.NearV3.Assembly.T_SIZE pub b s m) +
  (tableBusCount ZkFormal.NearV3.Qv.Candidates.KeyTrafficRepair.table.interactions
    tr ZkFormal.NearV3.Assembly.T_QV pub b s m +
  (ZkFormal.NearV3.Assembly.tcnt (ZkFormal.NearV3.Assembly.mrkTrafficE pub r.mrkE r.mrk) s b m +
  (tableBusCount sortTableV3.interactions tr ZkFormal.NearV3.Assembly.T_SORT pub b s m +
    0))))))))))))))))))))))))

/-- The bus count of the 33 tables of `nearAirV3D1` in record form.  (The stub / gap
extensions of tables 2 and 6 and the unread-key tables `30 … 32` of lane v3-d1-a7b enter as
raw table counts; their views are used by the A7 step only.) -/
def balSumD1 (pub : List Fp) (tr : Trace Fp) (r : D1Records) (b : Nat) (s : Bool) (m : List Fp) : Nat :=
  balSumBaseD1 pub tr r.base b s m +
  (ZkFormal.NearV3.Assembly.tcnt (txTraffic r.txs) s b m +
  (ZkFormal.NearV3.Assembly.tcnt (akmTraffic r.akms) s b m +
  (ZkFormal.NearV3.Assembly.tcnt (kibD1Traffic r.kibs) s b m +
  (ZkFormal.NearV3.Assembly.tcnt (plfTraffic r.plfs) s b m +
  (ZkFormal.NearV3.Assembly.tcnt (ridTraffic r.rids) s b m +
  (tableBusCount WalkU.interactions tr T_WALKU pub b s m +
  (tableBusCount NmemV3.interactions tr T_NMEM pub b s m +
  tableBusCount UvalV3.interactions tr T_UVAL pub b s m)))))))

/-- **The bus balance of `nearAirV3D1` in record form.** -/
def D1Balance (pub : List Fp) (tr : Trace Fp) (r : D1Records) : Prop :=
  ∀ b m, balSumD1 pub tr r b true m + pubCount nearAirV3D1 pub b true m =
    balSumD1 pub tr r b false m + pubCount nearAirV3D1 pub b false m

/-- The balance seen from D0a's records (the generated link copies take it in place of
`V3Balance`): the D1 records extending `r` balance. -/
def V3BalanceD1 (pub : List Fp) (tr : Trace Fp) (r : V3Records) : Prop :=
  ∃ R : D1Records, R.base = r ∧ D1Balance pub tr R

/-- The verifier's public input. -/
def pubD1 (p : Public.PrepD1) (h : HintD1) : List Fp :=
  ZkFormal.Udr.pubOf Fp (Public.preparedBytesD1 p (txOverhead h))

/-- **Everything the D1 link receives.** -/
structure LinkInputsD1 (cb : Bytes) (h : HintD1) (p : Public.PrepD1) (tr : Trace Fp) (r : D1Records) :
    Prop where
  prep : prepD1 cb h = .ok p
  size : (Public.preparedBytesD1 p (txOverhead h)).length < ZkFormal.Algebra.P
  holds : HoldsP nearAirV3D1 (pubD1 p h) tr
  wf : D1RecordsWf (pubD1 p h) r
  traffic : D1RecordsTraffic (pubD1 p h) tr r
  shaT : ZkFormal.Near.ShaFacts (ZkFormal.NearV3.Assembly.shaCountAt tr (pubD1 p h) ZkFormal.NearV3.Assembly.T_SHA_T true)
    (ZkFormal.NearV3.Assembly.shaCountAt tr (pubD1 p h) ZkFormal.NearV3.Assembly.T_SHA_T false)
  shaR : ZkFormal.Near.ShaFacts (ZkFormal.NearV3.Assembly.shaCountAt tr (pubD1 p h) ZkFormal.NearV3.Assembly.T_SHA_R true)
    (ZkFormal.NearV3.Assembly.shaCountAt tr (pubD1 p h) ZkFormal.NearV3.Assembly.T_SHA_R false)
  balance : D1Balance (pubD1 p h) tr r

end ZkFormal.NearV3.D1.Link
