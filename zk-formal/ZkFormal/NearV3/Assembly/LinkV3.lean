import ZkFormal.NearV3.Assembly.ViewsV3
import ZkFormal.NearV3.Assembly.RcptViewV3
import ZkFormal.NearV3.Assembly.ComposeV3
import ZkFormal.NearV3.Assembly.ShaUnionFacts
import ZkFormal.NearV3.Assembly.NearAdmission
import ZkFormal.NearV3.Rcpt.Extract.Srcp.Depth
import ZkFormal.NearV3.Candidates.MerklePhysical
import ZkFormal.NearV3.Assembly.LinkClaim
import ZkFormal.NearV3.Assembly.RcptViewCounts
import ZkFormal.NearV3.Assembly.A7SizeView
import ZkFormal.NearV3.Assembly.A7ValView
import ZkFormal.NearV3.Assembly.A7UpsView

/-!
# ZkFormal.NearV3.Assembly.LinkV3 — the linking step of `ExtractV3Stmt`

`ExtractV3StmtAt B` (AIR ⇒ `GoodV3 B`) splits as v1's `ExtractStmt`
(`Near/Extract/Statements.lean`, `Near/Extract/Compose.lean`) into

* the **per-table views** (proved: `ViewsV3.lean`, `ExtractV3.lean:rcptV3_view_nearAir`,
  `srcp_view`, the `mrk` view `MerkleEmpty.remapped_view` moved to `T_MRK` by `focus`):
  every viewed table's rows decompose into concrete records with exact traffic;
* the **SHA contract** of the two SHA instances (`shaFactsAt`, proved);
* the **bus balance** in record form (`V3Balance`, derived from `HoldsP.balance` and the
  exact traffic, including the public messages of `nearAirV3.pubSegs`);
* the **link** `LinkV3Stmt B`: records + their well-formedness + SHA contract + record-form
  balance ⇒ `GoodV3 B`.

`extractV3_of_link : LinkV3Stmt B → ExtractV3StmtAt B` is the mechanical composition.

**Trace-level tables.**  Thirteen tables have trace-free views.  The other ten
(`rawTables`: the three ChaCha tables, the five scheduler tables, `qvV3`, and `sortV3`) do
not: their proved soundness (`Sched.schedCore_sound`, `Chacha.shuffle_sound`, the `Qv`
extraction lemmas) is stated against `HoldsP` of a v2 AIR, and v1's `sort_view` is fixed at
`maxLog 13`/index 6 (`sortV3` has `maxLog 18`).  So `LinkV3Stmt` keeps the trace and
`HoldsP` as hypotheses, the raw tables enter `V3Balance` through their `tableBusCount`, and
the viewed tables' records are tied to the trace by their exact traffic
(`V3RecordsTraffic`).  Replacing a raw table by a trace-free view only removes a summand.
-/

namespace ZkFormal.NearV3.Assembly

open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 NearSpec NearSpecV3

/-! ## Records of the viewed tables -/

/-- The extracted records of the thirteen viewed tables of `nearAirV3`. -/
structure V3Records where
  nodes : List ZkFormal.NearV3.NodeS3
  heads : List ZkFormal.NearV3.HeadE
  values : List ZkFormal.NearV3.ValE
  walks : List ZkFormal.NearV3.WalkR
  uniq : List ZkFormal.NearV3.UniqE
  ups : List ZkFormal.NearV3.UpsSeg
  lists : ZkFormal.NearV3.RcptV3Vs
  accts : List ZkFormal.Near.AcctV
  akeys : List ZkFormal.NearV3.AkeyE
  bnds : List ZkFormal.NearV3.BndE
  srcp : List ZkFormal.NearV3.SrcpB
  size : ZkFormal.NearV3.SizeV
  mrk : ZkFormal.Near.MrkV
  /-- the outcome tree is empty (count 0): no Merkle rows/traffic -/
  mrkE : Bool
  /-- A7: the replaced node records (`nodeA7`'s `rpl` flag, by record index) -/
  rplN : Nat → Bool
  /-- A7: the replaced value records (`valA7`'s `rplv` flag, by record index) -/
  rplV : Nat → Bool
  /-- A7: the three totals received by `sizeA7` -/
  a7 : ZkFormal.NearV3.A7Y

/-- The `mrk` view's well-formedness: empty tree (public count 0 and zero root bytes) or a
well-formed v1 Merkle view (`MerkleEmpty.table`, nearAirV3's empty-tree repair). -/
def MrkWfE (pub : List Fp) (e : Bool) (v : ZkFormal.Near.MrkV) : Prop :=
  if e then (∀ (tr : Trace Fp) (t r : Nat), ZkFormal.NearV3.Candidates.MerkleEmpty.countE.eval tr t r pub = 0) ∧
      (∀ i < 32, pub.getD (ZkFormal.NearV3.PH_OUT + i) 0 = 0)
  else ZkFormal.Near.MrkWf (ZkFormal.NearV3.Candidates.MerklePublic.aliasPublic pub) v

/-- The `mrk` traffic: nothing for an empty tree, else the v1 view's traffic. -/
def mrkTrafficE (pub : List Fp) (e : Bool) (v : ZkFormal.Near.MrkV) : ZkFormal.Near.Traffic :=
  if e then ⟨fun _ => [], fun _ => []⟩ else ZkFormal.Near.mrkTraffic (ZkFormal.NearV3.Candidates.MerklePublic.aliasPublic pub) v

/-- The view post-conditions (well-formedness) of the records. -/
structure V3RecordsWf (pub : List Fp) (r : V3Records) : Prop where
  nodes : ZkFormal.NearV3.NodeWf3 r.nodes
  heads : ZkFormal.NearV3.HeadWf r.heads
  values : ZkFormal.NearV3.ValWf r.values
  walks : ZkFormal.NearV3.WalkWf3 r.walks
  walkSteps : (r.walks.flatMap (·.steps)).length ≤ 2 ^ 22
  uniq : ZkFormal.NearV3.UniqWf r.uniq
  ups : ZkFormal.NearV3.UpsWf r.ups
  lists : ZkFormal.NearV3.RcptV3Wf pub r.lists
  accts : ZkFormal.NearV3.AcctV3WfE 19 r.accts
  akeys : ZkFormal.NearV3.AkeyWf r.akeys
  bnds : ZkFormal.NearV3.BndWf r.bnds
  srcp : ZkFormal.NearV3.SrcpWf r.srcp
  /-- A10 from the AIR (`SrcpV3.tableD`): every source block's path has `≤ Dp0` items. -/
  srcpDepth : ∀ B ∈ r.srcp, B.path.length ≤ NearSpecV3.Dp0
  size : ZkFormal.NearV3.SizeWf pub r.size
  mrk : MrkWfE pub r.mrkE r.mrk
  /-- at most `2^22` receipt lists and receipts (physical rows, `rcptV3_view_counts`) -/
  listsCount : r.lists.length ≤ 2 ^ 22 ∧ (ZkFormal.NearV3.flatR r.lists).length ≤ 2 ^ 22
  /-- every receipt's routing quotient is `< 128` (table 16, `RcptV3.tableQ`) -/
  listsQ : ∀ x ∈ ZkFormal.NearV3.flatR r.lists, x.q < 128
  /-- A7 (`sizeA7`): `B0 − Σ y_t` is a 24-bit value -/
  a7size : ZkFormal.NearV3.A7SizeWf r.a7
  /-- A7 (`upsA7`): `nD = Σ dd_i · N_i` on every segment's first row -/
  a7ups : ZkFormal.NearV3.UpsA7Wf r.ups

/-- The exact traffic of each viewed table at its fixed `nearAirV3` index. -/
structure V3RecordsTraffic (pub : List Fp) (tr : Trace Fp) (r : V3Records) : Prop where
  nodes : ZkFormal.Near.TableTraffic ZkFormal.NearV3.NodeV3.interactions tr T_NODE pub
    (ZkFormal.NearV3.nodeTraffic3 r.nodes)
  heads : ZkFormal.Near.TableTraffic ZkFormal.NearV3.HeadV3.interactions tr T_HEAD pub
    (ZkFormal.NearV3.headTraffic r.heads)
  values : ZkFormal.Near.TableTraffic ZkFormal.NearV3.ValV3.interactions tr T_VAL pub
    (ZkFormal.NearV3.valTraffic r.values)
  walks : ZkFormal.Near.TableTraffic ZkFormal.NearV3.WalkV3.interactions tr T_WALK pub
    (ZkFormal.NearV3.walkTraffic3 r.walks)
  uniq : ZkFormal.Near.TableTraffic ZkFormal.NearV3.Uniq.interactions tr T_UNIQ pub
    (ZkFormal.NearV3.uniqTraffic r.uniq)
  ups : ZkFormal.Near.TableTraffic ZkFormal.NearV3.UpsV3.interactions tr T_UPS pub
    (ZkFormal.NearV3.upsTraffic r.ups)
  lists : ZkFormal.Near.TableTraffic ZkFormal.NearV3.RcptV3.interactions tr T_RCPT pub
    (ZkFormal.NearV3.rcptTraffic3 pub r.lists)
  accts : ZkFormal.Near.TableTraffic ZkFormal.NearV3.AcctV3.interactions tr T_ACCT pub
    (ZkFormal.NearV3.acctV3Traffic r.accts)
  akeys : ZkFormal.Near.TableTraffic ZkFormal.NearV3.AkeyV3.interactions tr T_AKEY pub
    (ZkFormal.NearV3.akeyTraffic r.akeys)
  bnds : ZkFormal.Near.TableTraffic ZkFormal.NearV3.BndV3.interactions tr T_BND pub
    (ZkFormal.NearV3.bndTraffic r.bnds)
  srcp : ZkFormal.Near.TableTraffic ZkFormal.NearV3.SrcpV3.interactions tr T_SRCP pub
    (ZkFormal.NearV3.srcpTraffic r.srcp)
  size : ZkFormal.Near.TableTraffic ZkFormal.NearV3.SizeV3.interactions tr T_SIZE pub
    (ZkFormal.NearV3.sizeTraffic r.size)
  mrk : ZkFormal.Near.TableTraffic ZkFormal.NearV3.Candidates.MerkleEmpty.table.interactions tr
    T_MRK pub (mrkTrafficE pub r.mrkE r.mrk)
  /-- the A7 interactions appended to `nodeV3`, `valV3`, `upsV3`, `sizeV3` (`Tables/UnfoldA7.lean`) -/
  a7nodes : ZkFormal.Near.TableTraffic ZkFormal.NearV3.UnfoldA7.Node.interactions tr T_NODE pub
    (ZkFormal.NearV3.a7NodeTraffic r.nodes r.rplN)
  a7values : ZkFormal.Near.TableTraffic ZkFormal.NearV3.UnfoldA7.Val.interactions tr T_VAL pub
    (ZkFormal.NearV3.a7ValTraffic r.values r.rplV)
  a7ups : ZkFormal.Near.TableTraffic ZkFormal.NearV3.UnfoldA7.Ups.interactions tr T_UPS pub
    (ZkFormal.NearV3.a7UpsTraffic r.ups)
  a7size : ZkFormal.Near.TableTraffic ZkFormal.NearV3.UnfoldA7.Size.interactions tr T_SIZE pub
    (ZkFormal.NearV3.a7SizeTraffic r.a7)

/-! ## Record-form bus balance -/

/-- Count of `m` among the messages a traffic sends (`s = true`) / receives on bus `b`. -/
def tcnt (tf : ZkFormal.Near.Traffic) (s : Bool) (b : Nat) (m : List Fp) : Nat :=
  (((if s then tf.sends else tf.recvs) b).map ZkFormal.Near.Msg.toFp).count m

/-- The bus count of the thirteen viewed tables, from their records. -/
def recCount (pub : List Fp) (r : V3Records) (b : Nat) (s : Bool) (m : List Fp) : Nat :=
  tcnt (ZkFormal.NearV3.nodeTraffic3 r.nodes) s b m +
  tcnt (ZkFormal.NearV3.headTraffic r.heads) s b m +
  tcnt (ZkFormal.NearV3.valTraffic r.values) s b m +
  tcnt (ZkFormal.NearV3.walkTraffic3 r.walks) s b m +
  tcnt (ZkFormal.NearV3.uniqTraffic r.uniq) s b m +
  tcnt (ZkFormal.NearV3.upsTraffic r.ups) s b m +
  tcnt (ZkFormal.NearV3.rcptTraffic3 pub r.lists) s b m +
  tcnt (ZkFormal.NearV3.acctV3Traffic r.accts) s b m +
  tcnt (ZkFormal.NearV3.akeyTraffic r.akeys) s b m +
  tcnt (ZkFormal.NearV3.bndTraffic r.bnds) s b m +
  tcnt (ZkFormal.NearV3.srcpTraffic r.srcp) s b m +
  tcnt (ZkFormal.NearV3.sizeTraffic r.size) s b m +
  tcnt (mrkTrafficE pub r.mrkE r.mrk) s b m

/-- The tables of `nearAirV3` without a trace-free view (index, table). -/
def rawTables : List (Nat × ZkFormal.Air.Table) :=
  [(T_CHACHA, ZkFormal.Chacha.Table.table22 ZkFormal.NearV3.Sched.B_SCHACHA),
   (T_RNG, ZkFormal.Chacha.Rng.Table.table22 ZkFormal.NearV3.Sched.B_SCHACHA
      ZkFormal.NearV3.Sched.B_SGEN),
   (T_SHUF, ZkFormal.Chacha.Shuffle.Table.table22 ZkFormal.NearV3.Sched.B_SSIN
      ZkFormal.NearV3.Sched.B_SSOUT ZkFormal.NearV3.Sched.B_SSMEM ZkFormal.NearV3.Sched.B_SGEN
      ZkFormal.NearV3.Sched.B_SSHUF),
   (T_CODEC, ZkFormal.NearV3.Sched.Codec.table),
   (T_SSD, ZkFormal.NearV3.Sched.ScanDist.table),
   (T_PROC, ZkFormal.NearV3.Sched.Proc.tableB),
   (T_MEM, ZkFormal.NearV3.Sched.Mem.table),
   (T_CMP, ZkFormal.NearV3.Sched.Cmp.table ZkFormal.NearV3.Sched.B_SCMP),
   (T_QV, ZkFormal.NearV3.Qv.Candidates.KeyTrafficRepair.table),
   (T_SORT, sortTableV3)]

/-- The bus count of the raw (trace-level) tables. -/
def rawCount (tr : Trace Fp) (pub : List Fp) (b : Nat) (s : Bool) (m : List Fp) : Nat :=
  (rawTables.map fun (tT : Nat × ZkFormal.Air.Table) =>
    tableBusCount tT.2.interactions tr tT.1 pub b s m).sum

/-- The bus count of the A7 accounting interactions appended to `nodeV3`, `valV3`, `upsV3` and
`sizeV3` (`Tables/UnfoldA7.lean`); trace-level until their record views exist. -/
def a7Count (tr : Trace Fp) (pub : List Fp) (b : Nat) (s : Bool) (m : List Fp) : Nat :=
  tableBusCount ZkFormal.NearV3.UnfoldA7.Node.interactions tr T_NODE pub b s m +
  (tableBusCount ZkFormal.NearV3.UnfoldA7.Val.interactions tr T_VAL pub b s m +
  (tableBusCount ZkFormal.NearV3.UnfoldA7.Ups.interactions tr T_UPS pub b s m +
  tableBusCount ZkFormal.NearV3.UnfoldA7.Size.interactions tr T_SIZE pub b s m))

/-- The total bus count of `nearAirV3` with every viewed table read from its records (in the
table order of `busCount_nearAirV3_explicit`): the two SHA instances, the thirteen viewed tables
(`tcnt` of their records' traffic, plus the appended A7 interactions of `nodeA7`, `valA7`,
`upsA7`, `sizeA7`), and the ten raw tables (`tableBusCount` on the trace). -/
def balSum (pub : List Fp) (tr : Trace Fp) (r : V3Records) (b : Nat) (s : Bool) (m : List Fp) : Nat :=
  tableBusCount shaTable.interactions tr T_SHA_T pub b s m +
  (tableBusCount shaTable.interactions tr T_SHA_R pub b s m +
  ((tcnt (ZkFormal.NearV3.nodeTraffic3 r.nodes) s b m +
      tableBusCount ZkFormal.NearV3.UnfoldA7.Node.interactions tr T_NODE pub b s m) +
  (tcnt (ZkFormal.NearV3.headTraffic r.heads) s b m +
  ((tcnt (ZkFormal.NearV3.valTraffic r.values) s b m +
      tableBusCount ZkFormal.NearV3.UnfoldA7.Val.interactions tr T_VAL pub b s m) +
  (tcnt (ZkFormal.NearV3.walkTraffic3 r.walks) s b m +
  (tcnt (ZkFormal.NearV3.uniqTraffic r.uniq) s b m +
  ((tcnt (ZkFormal.NearV3.upsTraffic r.ups) s b m +
      tableBusCount ZkFormal.NearV3.UnfoldA7.Ups.interactions tr T_UPS pub b s m) +
  (tableBusCount (ZkFormal.Chacha.Table.table22 ZkFormal.NearV3.Sched.B_SCHACHA).interactions
    tr T_CHACHA pub b s m +
  (tableBusCount (ZkFormal.Chacha.Rng.Table.table22 ZkFormal.NearV3.Sched.B_SCHACHA
    ZkFormal.NearV3.Sched.B_SGEN).interactions tr T_RNG pub b s m +
  (tableBusCount (ZkFormal.Chacha.Shuffle.Table.table22 ZkFormal.NearV3.Sched.B_SSIN
    ZkFormal.NearV3.Sched.B_SSOUT ZkFormal.NearV3.Sched.B_SSMEM ZkFormal.NearV3.Sched.B_SGEN
    ZkFormal.NearV3.Sched.B_SSHUF).interactions tr T_SHUF pub b s m +
  (tableBusCount ZkFormal.NearV3.Sched.Codec.table.interactions tr T_CODEC pub b s m +
  (tableBusCount ZkFormal.NearV3.Sched.ScanDist.table.interactions tr T_SSD pub b s m +
  (tableBusCount ZkFormal.NearV3.Sched.Proc.table.interactions tr T_PROC pub b s m +
  (tableBusCount ZkFormal.NearV3.Sched.Mem.table.interactions tr T_MEM pub b s m +
  (tableBusCount (ZkFormal.NearV3.Sched.Cmp.table ZkFormal.NearV3.Sched.B_SCMP).interactions
    tr T_CMP pub b s m +
  (tcnt (ZkFormal.NearV3.rcptTraffic3 pub r.lists) s b m +
  (tcnt (ZkFormal.NearV3.acctV3Traffic r.accts) s b m +
  (tcnt (ZkFormal.NearV3.akeyTraffic r.akeys) s b m +
  (tcnt (ZkFormal.NearV3.bndTraffic r.bnds) s b m +
  (tcnt (ZkFormal.NearV3.srcpTraffic r.srcp) s b m +
  ((tcnt (ZkFormal.NearV3.sizeTraffic r.size) s b m +
      tableBusCount ZkFormal.NearV3.UnfoldA7.Size.interactions tr T_SIZE pub b s m) +
  (tableBusCount ZkFormal.NearV3.Qv.Candidates.KeyTrafficRepair.table.interactions
    tr T_QV pub b s m +
  (tcnt (mrkTrafficE pub r.mrkE r.mrk) s b m +
  (tableBusCount sortTableV3.interactions tr T_SORT pub b s m +
    0))))))))))))))))))))))))

/-- **The bus balance of `nearAirV3` in record form**: the two SHA instances (by their
counts), the thirteen viewed tables (by their records), the ten raw tables (by the trace)
and the public messages of `nearAirV3.pubSegs`, sends = receives on every bus. -/
def V3Balance (pub : List Fp) (tr : Trace Fp) (r : V3Records) : Prop :=
  ∀ b m, balSum pub tr r b true m + pubCount nearAirV3 pub b true m =
    balSum pub tr r b false m + pubCount nearAirV3 pub b false m

/-! ## The linking statement -/

/-- **The linking statement** at A7 bound `B`.  From a successful preparation, an accepted
trace, the records of the viewed tables with their well-formedness and exact traffic, the
SHA contract of both SHA instances and the record-form bus balance, reconstruct `GoodV3 B`.
`HoldsP` is kept for the ten raw tables (see the module doc). -/
def LinkV3Stmt (B : Nat) : Prop :=
  ∀ (cb : Bytes) (h : Hint) (p : Prep) (oh : Nat) (tr : Trace Fp) (r : V3Records),
    prepD0 cb h = .ok p →
    (ZkFormal.NearV3.Public.preparedBytes p oh).length < ZkFormal.Algebra.P →
    HoldsP nearAirV3 (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr →
    V3RecordsWf (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r →
    V3RecordsTraffic (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr r →
    ZkFormal.Near.ShaFacts
      (shaCountAt tr (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) T_SHA_T true)
      (shaCountAt tr (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) T_SHA_T false) →
    ZkFormal.Near.ShaFacts
      (shaCountAt tr (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) T_SHA_R true)
      (shaCountAt tr (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) T_SHA_R false) →
    V3Balance (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr r →
    ∃ k x, GoodV3 B cb k h p x

/-- **The open core of the link**: `LinkV3Stmt` with the walk and the claim-level fields
already supplied (`walkD0_of_prepD0`), asking only for the view-level `GoodV3` fields
(`ExtFieldsV3`). -/
def LinkCoreV3Stmt (B : Nat) : Prop :=
  ∀ (cb : Bytes) (h : Hint) (p : Prep) (oh : Nat) (tr : Trace Fp) (r : V3Records) (k : WalkD0),
    prepD0 cb h = .ok p → walkD0 cb = .ok k → ClaimFieldsV3 k →
    (ZkFormal.NearV3.Public.preparedBytes p oh).length < ZkFormal.Algebra.P →
    HoldsP nearAirV3 (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr →
    V3RecordsWf (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r →
    V3RecordsTraffic (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr r →
    ZkFormal.Near.ShaFacts
      (shaCountAt tr (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) T_SHA_T true)
      (shaCountAt tr (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) T_SHA_T false) →
    ZkFormal.Near.ShaFacts
      (shaCountAt tr (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) T_SHA_R true)
      (shaCountAt tr (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) T_SHA_R false) →
    V3Balance (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr r →
    ∃ x, ExtFieldsV3 B cb k h p x

/-- The link from its core: the walk and the claim-level fields come from `prepD0`. -/
theorem linkV3_of_core {B : Nat} (hc : LinkCoreV3Stmt B) : LinkV3Stmt B := by
  intro cb h p oh tr r hp hsz hH hw ht hs1 hs2 hb
  exact goodV3_of_ext hp fun k hk =>
    hc cb h p oh tr r k hp hk (walkD0_of_prepD0 hp |>.elim fun k' ⟨hk', C⟩ => by
      rw [hk] at hk'; cases hk'; exact C) hsz hH hw ht hs1 hs2 hb

/-! ## Mechanical composition: `LinkV3Stmt ⇒ ExtractV3Stmt` -/

/-- `busCount nearAirV3` as the explicit sum over its 25 tables, in the `V3Balance` form. -/
theorem busCount_nearAirV3_explicit (tr : Trace Fp) (pub : List Fp) (b : Nat) (s : Bool)
    (m : List Fp) :
    busCount nearAirV3.toAir tr pub b s m =
      tableBusCount shaTable.interactions tr T_SHA_T pub b s m +
      (tableBusCount shaTable.interactions tr T_SHA_R pub b s m +
      (tableBusCount ZkFormal.NearV3.UnfoldA7.nodeA7.interactions tr T_NODE pub b s m +
      (tableBusCount ZkFormal.NearV3.HeadV3.interactions tr T_HEAD pub b s m +
      (tableBusCount ZkFormal.NearV3.UnfoldA7.valA7.interactions tr T_VAL pub b s m +
      (tableBusCount ZkFormal.NearV3.WalkV3.interactions tr T_WALK pub b s m +
      (tableBusCount ZkFormal.NearV3.Uniq.interactions tr T_UNIQ pub b s m +
      (tableBusCount ZkFormal.NearV3.UnfoldA7.upsA7.interactions tr T_UPS pub b s m +
      (tableBusCount (ZkFormal.Chacha.Table.table22 ZkFormal.NearV3.Sched.B_SCHACHA).interactions
        tr T_CHACHA pub b s m +
      (tableBusCount (ZkFormal.Chacha.Rng.Table.table22 ZkFormal.NearV3.Sched.B_SCHACHA
        ZkFormal.NearV3.Sched.B_SGEN).interactions tr T_RNG pub b s m +
      (tableBusCount (ZkFormal.Chacha.Shuffle.Table.table22 ZkFormal.NearV3.Sched.B_SSIN
        ZkFormal.NearV3.Sched.B_SSOUT ZkFormal.NearV3.Sched.B_SSMEM ZkFormal.NearV3.Sched.B_SGEN
        ZkFormal.NearV3.Sched.B_SSHUF).interactions tr T_SHUF pub b s m +
      (tableBusCount ZkFormal.NearV3.Sched.Codec.table.interactions tr T_CODEC pub b s m +
      (tableBusCount ZkFormal.NearV3.Sched.ScanDist.table.interactions tr T_SSD pub b s m +
      (tableBusCount ZkFormal.NearV3.Sched.Proc.tableB.interactions tr T_PROC pub b s m +
      (tableBusCount ZkFormal.NearV3.Sched.Mem.table.interactions tr T_MEM pub b s m +
      (tableBusCount (ZkFormal.NearV3.Sched.Cmp.table ZkFormal.NearV3.Sched.B_SCMP).interactions
        tr T_CMP pub b s m +
      (tableBusCount ZkFormal.NearV3.RcptV3.interactions tr T_RCPT pub b s m +
      (tableBusCount ZkFormal.NearV3.AcctV3.interactions tr T_ACCT pub b s m +
      (tableBusCount ZkFormal.NearV3.AkeyV3.interactions tr T_AKEY pub b s m +
      (tableBusCount ZkFormal.NearV3.BndV3.interactions tr T_BND pub b s m +
      (tableBusCount ZkFormal.NearV3.SrcpV3.interactions tr T_SRCP pub b s m +
      (tableBusCount ZkFormal.NearV3.UnfoldA7.sizeA7.interactions tr T_SIZE pub b s m +
      (tableBusCount ZkFormal.NearV3.Qv.Candidates.KeyTrafficRepair.table.interactions
        tr T_QV pub b s m +
      (tableBusCount ZkFormal.NearV3.Candidates.MerkleEmpty.table.interactions tr T_MRK pub b s m +
      (tableBusCount sortTableV3.interactions tr T_SORT pub b s m +
        0)))))))))))))))))))))))) := rfl

/-- `rawCount` as an explicit sum. -/
theorem rawCount_explicit (tr : Trace Fp) (pub : List Fp) (b : Nat) (s : Bool) (m : List Fp) :
    rawCount tr pub b s m =
      tableBusCount (ZkFormal.Chacha.Table.table22 ZkFormal.NearV3.Sched.B_SCHACHA).interactions
        tr T_CHACHA pub b s m +
      (tableBusCount (ZkFormal.Chacha.Rng.Table.table22 ZkFormal.NearV3.Sched.B_SCHACHA
        ZkFormal.NearV3.Sched.B_SGEN).interactions tr T_RNG pub b s m +
      (tableBusCount (ZkFormal.Chacha.Shuffle.Table.table22 ZkFormal.NearV3.Sched.B_SSIN
        ZkFormal.NearV3.Sched.B_SSOUT ZkFormal.NearV3.Sched.B_SSMEM ZkFormal.NearV3.Sched.B_SGEN
        ZkFormal.NearV3.Sched.B_SSHUF).interactions tr T_SHUF pub b s m +
      (tableBusCount ZkFormal.NearV3.Sched.Codec.table.interactions tr T_CODEC pub b s m +
      (tableBusCount ZkFormal.NearV3.Sched.ScanDist.table.interactions tr T_SSD pub b s m +
      (tableBusCount ZkFormal.NearV3.Sched.Proc.tableB.interactions tr T_PROC pub b s m +
      (tableBusCount ZkFormal.NearV3.Sched.Mem.table.interactions tr T_MEM pub b s m +
      (tableBusCount (ZkFormal.NearV3.Sched.Cmp.table ZkFormal.NearV3.Sched.B_SCMP).interactions
        tr T_CMP pub b s m +
      (tableBusCount ZkFormal.NearV3.Qv.Candidates.KeyTrafficRepair.table.interactions
        tr T_QV pub b s m +
      (tableBusCount sortTableV3.interactions tr T_SORT pub b s m +
        0))))))))) := rfl

/-- Exact traffic, as a count equation on both sides. -/
theorem tcnt_of_traffic {is : List Interaction} {tr : Trace Fp} {t : Nat} {pub : List Fp}
    {tf : ZkFormal.Near.Traffic} (h : ZkFormal.Near.TableTraffic is tr t pub tf)
    (s : Bool) (b : Nat) (m : List Fp) :
    tableBusCount is tr t pub b s m = tcnt tf s b m := by
  cases s
  · exact (h b m).2
  · exact (h b m).1

theorem shaCountAt_eq (tr : Trace Fp) (pub : List Fp) (t : Nat) (s : Bool) (b : Nat)
    (m : List Fp) :
    shaCountAt tr pub t s b m = tableBusCount shaTable.interactions tr t pub b s m := rfl

/-- The record-form balance from `HoldsP` and the exact traffic of the viewed tables. -/
theorem v3Balance_of_holdsP {pub : List Fp} {tr : Trace Fp} {r : V3Records}
    (hH : HoldsP nearAirV3 pub tr) (T : V3RecordsTraffic pub tr r) : V3Balance pub tr r := by
  intro b m
  have hb := hH.balance b m
  rw [busCount_nearAirV3_explicit, busCount_nearAirV3_explicit] at hb
  simp only [show ZkFormal.NearV3.UnfoldA7.nodeA7.interactions =
      ZkFormal.NearV3.NodeV3.interactions ++ ZkFormal.NearV3.UnfoldA7.Node.interactions from rfl,
    show ZkFormal.NearV3.UnfoldA7.valA7.interactions =
      ZkFormal.NearV3.ValV3.interactions ++ ZkFormal.NearV3.UnfoldA7.Val.interactions from rfl,
    show ZkFormal.NearV3.UnfoldA7.upsA7.interactions =
      ZkFormal.NearV3.UpsV3.interactions ++ ZkFormal.NearV3.UnfoldA7.Ups.interactions from rfl,
    show ZkFormal.NearV3.UnfoldA7.sizeA7.interactions =
      ZkFormal.NearV3.SizeV3.interactions ++ ZkFormal.NearV3.UnfoldA7.Size.interactions from rfl,
    tableBusCount_append] at hb
  rw [tcnt_of_traffic T.nodes, tcnt_of_traffic T.nodes, tcnt_of_traffic T.heads, tcnt_of_traffic T.heads, tcnt_of_traffic T.values, tcnt_of_traffic T.values,
    tcnt_of_traffic T.walks, tcnt_of_traffic T.walks, tcnt_of_traffic T.uniq, tcnt_of_traffic T.uniq, tcnt_of_traffic T.ups, tcnt_of_traffic T.ups,
    tcnt_of_traffic T.lists, tcnt_of_traffic T.lists, tcnt_of_traffic T.accts, tcnt_of_traffic T.accts, tcnt_of_traffic T.akeys, tcnt_of_traffic T.akeys,
    tcnt_of_traffic T.bnds, tcnt_of_traffic T.bnds, tcnt_of_traffic T.srcp, tcnt_of_traffic T.srcp, tcnt_of_traffic T.size, tcnt_of_traffic T.size,
    tcnt_of_traffic T.mrk, tcnt_of_traffic T.mrk] at hb
  unfold balSum
  exact hb

/-- The SHA table's `TableLocal` is the SHA lane's `ShaLocal`. -/
theorem shaLocal_of_tableLocal {tr : Trace Fp} {t : Nat} {pub : List Fp}
    (h : ZkFormal.Near.TableLocal shaTable tr t pub) : ZkFormal.Sha.ShaLocal tr t pub :=
  ⟨h.log_ge, h.log_le, h.constr⟩

theorem getElem?_sha_t : nearAirV3.tables[T_SHA_T]? = some shaTable := rfl
theorem getElem?_sha_r : nearAirV3.tables[T_SHA_R]? = some shaTable := rfl

/-- The `mrk` view at `T_MRK = 23` (`MerkleEmpty.table`): an empty tree (count 0, zero
public root, no traffic), or the public-index-translated v1 Merkle view
(`MerkleEmpty.nonempty_view`), moved from v1's index by the proof-only `focus`. -/
theorem mrkView {pub : List Fp} {tr : Trace Fp} (hH : HoldsP nearAirV3 pub tr) :
    ∃ e v, MrkWfE pub e v ∧
      ZkFormal.Near.TableTraffic ZkFormal.NearV3.Candidates.MerkleEmpty.table.interactions tr T_MRK pub (mrkTrafficE pub e v) := by
  have hL := tableLocal_of_holdsP hH getElem?_mrk
  have hF := ZkFormal.NearV3.Candidates.MerkleEmpty.focus_local hL ZkFormal.Near.T_MRK
  by_cases hc : ZkFormal.NearV3.Candidates.MerkleEmpty.countE.eval (ZkFormal.NearV3.Candidates.MerkleEmpty.focus tr T_MRK) ZkFormal.Near.T_MRK 0 pub = 0
  · obtain ⟨hr, hz⟩ := ZkFormal.NearV3.Candidates.MerkleEmpty.empty_view hF hc
    refine ⟨true, default, ⟨fun _ _ _ => hc, hr⟩, fun b m => ?_⟩
    have h1 := hz b true m
    have h0 := hz b false m
    rw [ZkFormal.NearV3.Candidates.MerkleEmpty.focus_count] at h1 h0
    simp only [mrkTrafficE, ite_true, List.map_nil, List.count_nil]
    exact ⟨h1, h0⟩
  · obtain ⟨v, hw, ht⟩ := ZkFormal.NearV3.Candidates.MerkleEmpty.nonempty_view hF hc
    refine ⟨false, v, hw, fun b m => ?_⟩
    simpa only [ZkFormal.NearV3.Candidates.MerkleEmpty.focus_count, mrkTrafficE, Bool.false_eq_true, ite_false] using ht b m

/-- **All views at once.** From `HoldsP` on a successful preparation (below the field size):
records of the thirteen viewed tables, their well-formedness and exact traffic. -/
theorem v3Records_of_holdsP {cb : Bytes} {h : Hint} {p : Prep} {oh : Nat} {tr : Trace Fp}
    (hp : prepD0 cb h = .ok p)
    (hsz : (ZkFormal.NearV3.Public.preparedBytes p oh).length < ZkFormal.Algebra.P)
    (hH : HoldsP nearAirV3 (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr) :
    ∃ r, V3RecordsWf (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r ∧
      V3RecordsTraffic (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr r := by
  obtain ⟨vs, sN, wN, tN, aN⟩ := ZkFormal.NearV3.nodeA7_view tr _ T_NODE (tableLocal_of_holdsP hH getElem?_node)
  obtain ⟨hs, wH, tH⟩ := headView hH
  obtain ⟨es, sV, wV, tV, aV⟩ := ZkFormal.NearV3.valA7_view tr _ T_VAL (tableLocal_of_holdsP hH getElem?_val)
  obtain ⟨ws, wW, wS, tW⟩ := walkView hH
  obtain ⟨us, wU, tU⟩ := uniqView hH
  obtain ⟨u, wP, tP, aP, aPw⟩ := ZkFormal.NearV3.upsA7_view tr _ T_UPS (tableLocal_of_holdsP hH getElem?_ups)
  obtain ⟨ay, aYw, aY⟩ := ZkFormal.NearV3.A7SizeProof.sizeA7_view (tableLocal_of_holdsP hH getElem?_size)
  obtain ⟨ls, wR, tR, cR1, cR2, qR⟩ := rcptV3_view_counts hp hsz hH
  obtain ⟨as, wA, tA⟩ := acctView hH
  obtain ⟨ks, wK, tK⟩ := akeyView hH
  obtain ⟨bs, wB, tB⟩ := bndView hH
  obtain ⟨ss, wS', dS', tS'⟩ := ZkFormal.NearV3.srcpD_view (srcpLocal hH)
  obtain ⟨sz, wZ, tZ⟩ := sizeView hH
  obtain ⟨me, mv, wM, tM⟩ := mrkView hH
  exact ⟨⟨vs, hs, es, ws, us, u, ls, as, ks, bs, ss, sz, mv, me, sN, sV, ay⟩,
    ⟨wN, wH, wV, wW, wS, wU, wP, wR, wA, wK, wB, wS', dS', wZ, wM, ⟨cR1, cR2⟩, qR, aYw, aPw⟩,
    ⟨tN, tH, tV, tW, tU, tP, tR, tA, tK, tB, tS', tZ, tM, aN, aV, aP, aY⟩⟩

/-- **`LinkV3Stmt ⇒ ExtractV3StmtAt`** (v1's `extract_of_views`): `HoldsP` gives every
view, the SHA contracts of both instances and the record-form balance. -/
theorem extractV3_of_link {B : Nat} (hL : LinkV3Stmt B) : ExtractV3StmtAt B := by
  intro cb h p oh tr hp hsz hH
  obtain ⟨r, hw, ht⟩ := v3Records_of_holdsP hp hsz hH
  exact hL cb h p oh tr r hp hsz hH hw ht
    (shaFactsAt tr _ T_SHA_T (shaLocal_of_tableLocal (tableLocal_of_holdsP hH getElem?_sha_t)))
    (shaFactsAt tr _ T_SHA_R (shaLocal_of_tableLocal (tableLocal_of_holdsP hH getElem?_sha_r)))
    (v3Balance_of_holdsP hH ht)

/-- The certificate's soundness obligation from the link at `B0`. -/
theorem extractV3Stmt_of_link (hL : LinkV3Stmt NearSpecV3.B0) : ExtractV3Stmt :=
  extractV3_of_link hL

/-- The D0a relation produced by the AIR through the link: `GoodV3` gives
`checkD0a` (`factorSound`), and `relD0a_iff` gives `RelD0a`. -/
theorem relD0a_of_good {B cb k h p x} (g : GoodV3 B cb k h p x) :
    RelD0a B cb (witnessOfV3 k x) :=
  (relD0a_iff B cb (witnessOfV3 k x)).mpr
    (ZkFormal.NearV3.Assembly.factorSound B cb k h p x g)

end ZkFormal.NearV3.Assembly
