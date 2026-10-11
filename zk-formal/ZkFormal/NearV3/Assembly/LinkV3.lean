import ZkFormal.NearV3.Assembly.ViewsV3
import ZkFormal.NearV3.Assembly.ComposeV3
import ZkFormal.NearV3.Assembly.ShaUnionFacts
import ZkFormal.NearV3.Assembly.NearAdmission
import ZkFormal.NearV3.Rcpt.Extract.Srcp.Proof
import ZkFormal.NearV3.Candidates.MerklePhysical

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
  accts : ZkFormal.NearV3.AcctV3Wf r.accts
  akeys : ZkFormal.NearV3.AkeyWf r.akeys
  bnds : ZkFormal.NearV3.BndWf r.bnds
  srcp : ZkFormal.NearV3.SrcpWf r.srcp
  size : ZkFormal.NearV3.SizeWf pub r.size
  mrk : ZkFormal.Near.MrkWf (ZkFormal.NearV3.Candidates.MerklePublic.aliasPublic pub) r.mrk

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
  mrk : ZkFormal.Near.TableTraffic ZkFormal.NearV3.Candidates.MerklePublic.table.interactions tr
    T_MRK pub
    (ZkFormal.Near.mrkTraffic (ZkFormal.NearV3.Candidates.MerklePublic.aliasPublic pub) r.mrk)

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
  tcnt (ZkFormal.Near.mrkTraffic (ZkFormal.NearV3.Candidates.MerklePublic.aliasPublic pub) r.mrk)
    s b m

/-- The tables of `nearAirV3` without a trace-free view (index, table). -/
def rawTables : List (Nat × ZkFormal.Air.Table) :=
  [(T_CHACHA, ZkFormal.Chacha.Table.table ZkFormal.NearV3.Sched.B_SCHACHA),
   (T_RNG, ZkFormal.Chacha.Rng.Table.table ZkFormal.NearV3.Sched.B_SCHACHA
      ZkFormal.NearV3.Sched.B_SGEN),
   (T_SHUF, ZkFormal.Chacha.Shuffle.Table.table ZkFormal.NearV3.Sched.B_SSIN
      ZkFormal.NearV3.Sched.B_SSOUT ZkFormal.NearV3.Sched.B_SSMEM ZkFormal.NearV3.Sched.B_SGEN
      ZkFormal.NearV3.Sched.B_SSHUF),
   (T_CODEC, ZkFormal.NearV3.Sched.Codec.table),
   (T_SSD, ZkFormal.NearV3.Sched.ScanDist.table),
   (T_PROC, ZkFormal.NearV3.Sched.Proc.table),
   (T_MEM, ZkFormal.NearV3.Sched.Mem.table),
   (T_CMP, ZkFormal.NearV3.Sched.Cmp.table ZkFormal.NearV3.Sched.B_SCMP),
   (T_QV, ZkFormal.NearV3.Qv.Candidates.KeyTrafficRepair.table),
   (T_SORT, {ZkFormal.Near.Sort.table with maxLog := 18})]

/-- The bus count of the raw (trace-level) tables. -/
def rawCount (tr : Trace Fp) (pub : List Fp) (b : Nat) (s : Bool) (m : List Fp) : Nat :=
  (rawTables.map fun (tT : Nat × ZkFormal.Air.Table) =>
    tableBusCount tT.2.interactions tr tT.1 pub b s m).sum

/-- **The bus balance of `nearAirV3` in record form**: the two SHA instances (by their
counts), the thirteen viewed tables (by their records), the ten raw tables (by the trace)
and the public messages of `nearAirV3.pubSegs`, sends = receives on every bus. -/
def V3Balance (pub : List Fp) (tr : Trace Fp) (r : V3Records) : Prop :=
  ∀ b m,
    shaCountAt tr pub T_SHA_T true b m + shaCountAt tr pub T_SHA_R true b m +
        recCount pub r b true m + rawCount tr pub b true m + pubCount nearAirV3 pub b true m =
      shaCountAt tr pub T_SHA_T false b m + shaCountAt tr pub T_SHA_R false b m +
        recCount pub r b false m + rawCount tr pub b false m + pubCount nearAirV3 pub b false m

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

/-! ## Mechanical composition: `LinkV3Stmt ⇒ ExtractV3Stmt` -/

/-- `busCount nearAirV3` as the explicit sum over its 25 tables, in the `V3Balance` form. -/
theorem busCount_nearAirV3_explicit (tr : Trace Fp) (pub : List Fp) (b : Nat) (s : Bool)
    (m : List Fp) :
    busCount nearAirV3.toAir tr pub b s m =
      tableBusCount shaTable.interactions tr T_SHA_T pub b s m +
      (tableBusCount shaTable.interactions tr T_SHA_R pub b s m +
      (tableBusCount ZkFormal.NearV3.NodeV3.interactions tr T_NODE pub b s m +
      (tableBusCount ZkFormal.NearV3.HeadV3.interactions tr T_HEAD pub b s m +
      (tableBusCount ZkFormal.NearV3.ValV3.interactions tr T_VAL pub b s m +
      (tableBusCount ZkFormal.NearV3.WalkV3.interactions tr T_WALK pub b s m +
      (tableBusCount ZkFormal.NearV3.Uniq.interactions tr T_UNIQ pub b s m +
      (tableBusCount ZkFormal.NearV3.UpsV3.interactions tr T_UPS pub b s m +
      (tableBusCount (ZkFormal.Chacha.Table.table ZkFormal.NearV3.Sched.B_SCHACHA).interactions
        tr T_CHACHA pub b s m +
      (tableBusCount (ZkFormal.Chacha.Rng.Table.table ZkFormal.NearV3.Sched.B_SCHACHA
        ZkFormal.NearV3.Sched.B_SGEN).interactions tr T_RNG pub b s m +
      (tableBusCount (ZkFormal.Chacha.Shuffle.Table.table ZkFormal.NearV3.Sched.B_SSIN
        ZkFormal.NearV3.Sched.B_SSOUT ZkFormal.NearV3.Sched.B_SSMEM ZkFormal.NearV3.Sched.B_SGEN
        ZkFormal.NearV3.Sched.B_SSHUF).interactions tr T_SHUF pub b s m +
      (tableBusCount ZkFormal.NearV3.Sched.Codec.table.interactions tr T_CODEC pub b s m +
      (tableBusCount ZkFormal.NearV3.Sched.ScanDist.table.interactions tr T_SSD pub b s m +
      (tableBusCount ZkFormal.NearV3.Sched.Proc.table.interactions tr T_PROC pub b s m +
      (tableBusCount ZkFormal.NearV3.Sched.Mem.table.interactions tr T_MEM pub b s m +
      (tableBusCount (ZkFormal.NearV3.Sched.Cmp.table ZkFormal.NearV3.Sched.B_SCMP).interactions
        tr T_CMP pub b s m +
      (tableBusCount ZkFormal.NearV3.RcptV3.interactions tr T_RCPT pub b s m +
      (tableBusCount ZkFormal.NearV3.AcctV3.interactions tr T_ACCT pub b s m +
      (tableBusCount ZkFormal.NearV3.AkeyV3.interactions tr T_AKEY pub b s m +
      (tableBusCount ZkFormal.NearV3.BndV3.interactions tr T_BND pub b s m +
      (tableBusCount ZkFormal.NearV3.SrcpV3.interactions tr T_SRCP pub b s m +
      (tableBusCount ZkFormal.NearV3.SizeV3.interactions tr T_SIZE pub b s m +
      (tableBusCount ZkFormal.NearV3.Qv.Candidates.KeyTrafficRepair.table.interactions
        tr T_QV pub b s m +
      (tableBusCount ZkFormal.NearV3.Candidates.MerklePublic.table.interactions tr T_MRK pub b s m +
      (tableBusCount {ZkFormal.Near.Sort.table with maxLog := 18}.interactions tr T_SORT pub b s m +
        0)))))))))))))))))))))))) := rfl

/-- `rawCount` as an explicit sum. -/
theorem rawCount_explicit (tr : Trace Fp) (pub : List Fp) (b : Nat) (s : Bool) (m : List Fp) :
    rawCount tr pub b s m =
      tableBusCount (ZkFormal.Chacha.Table.table ZkFormal.NearV3.Sched.B_SCHACHA).interactions
        tr T_CHACHA pub b s m +
      (tableBusCount (ZkFormal.Chacha.Rng.Table.table ZkFormal.NearV3.Sched.B_SCHACHA
        ZkFormal.NearV3.Sched.B_SGEN).interactions tr T_RNG pub b s m +
      (tableBusCount (ZkFormal.Chacha.Shuffle.Table.table ZkFormal.NearV3.Sched.B_SSIN
        ZkFormal.NearV3.Sched.B_SSOUT ZkFormal.NearV3.Sched.B_SSMEM ZkFormal.NearV3.Sched.B_SGEN
        ZkFormal.NearV3.Sched.B_SSHUF).interactions tr T_SHUF pub b s m +
      (tableBusCount ZkFormal.NearV3.Sched.Codec.table.interactions tr T_CODEC pub b s m +
      (tableBusCount ZkFormal.NearV3.Sched.ScanDist.table.interactions tr T_SSD pub b s m +
      (tableBusCount ZkFormal.NearV3.Sched.Proc.table.interactions tr T_PROC pub b s m +
      (tableBusCount ZkFormal.NearV3.Sched.Mem.table.interactions tr T_MEM pub b s m +
      (tableBusCount (ZkFormal.NearV3.Sched.Cmp.table ZkFormal.NearV3.Sched.B_SCMP).interactions
        tr T_CMP pub b s m +
      (tableBusCount ZkFormal.NearV3.Qv.Candidates.KeyTrafficRepair.table.interactions
        tr T_QV pub b s m +
      (tableBusCount {ZkFormal.Near.Sort.table with maxLog := 18}.interactions tr T_SORT pub b s m +
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
  rw [tcnt_of_traffic T.nodes, tcnt_of_traffic T.nodes, tcnt_of_traffic T.heads, tcnt_of_traffic T.heads, tcnt_of_traffic T.values, tcnt_of_traffic T.values,
    tcnt_of_traffic T.walks, tcnt_of_traffic T.walks, tcnt_of_traffic T.uniq, tcnt_of_traffic T.uniq, tcnt_of_traffic T.ups, tcnt_of_traffic T.ups,
    tcnt_of_traffic T.lists, tcnt_of_traffic T.lists, tcnt_of_traffic T.accts, tcnt_of_traffic T.accts, tcnt_of_traffic T.akeys, tcnt_of_traffic T.akeys,
    tcnt_of_traffic T.bnds, tcnt_of_traffic T.bnds, tcnt_of_traffic T.srcp, tcnt_of_traffic T.srcp, tcnt_of_traffic T.size, tcnt_of_traffic T.size,
    tcnt_of_traffic T.mrk, tcnt_of_traffic T.mrk] at hb
  rw [rawCount_explicit, rawCount_explicit, shaCountAt_eq, shaCountAt_eq, shaCountAt_eq,
    shaCountAt_eq]
  unfold recCount
  simp only [Nat.add_zero, Nat.add_assoc] at hb ⊢
  simp only [Nat.add_left_comm (tcnt _ _ _ _) (tableBusCount _ _ _ _ _ _ _)] at hb ⊢
  exact hb

/-- The SHA table's `TableLocal` is the SHA lane's `ShaLocal`. -/
theorem shaLocal_of_tableLocal {tr : Trace Fp} {t : Nat} {pub : List Fp}
    (h : ZkFormal.Near.TableLocal shaTable tr t pub) : ZkFormal.Sha.ShaLocal tr t pub :=
  ⟨h.log_ge, h.log_le, h.constr⟩

theorem getElem?_sha_t : nearAirV3.tables[T_SHA_T]? = some shaTable := rfl
theorem getElem?_sha_r : nearAirV3.tables[T_SHA_R]? = some shaTable := rfl

/-- The `mrk` view at `T_MRK = 23`: the public-index-translated v1 Merkle view
(`MerkleEmpty.remapped_view`), moved from v1's index by the proof-only `focus`. -/
theorem mrkView {pub : List Fp} {tr : Trace Fp} (hH : HoldsP nearAirV3 pub tr) :
    ∃ v, ZkFormal.Near.MrkWf (ZkFormal.NearV3.Candidates.MerklePublic.aliasPublic pub) v ∧
      ZkFormal.Near.TableTraffic ZkFormal.NearV3.Candidates.MerklePublic.table.interactions tr
        T_MRK pub
        (ZkFormal.Near.mrkTraffic (ZkFormal.NearV3.Candidates.MerklePublic.aliasPublic pub) v) := by
  have hL := tableLocal_of_holdsP hH getElem?_mrk
  obtain ⟨v, hw, ht⟩ := ZkFormal.NearV3.Candidates.MerkleEmpty.remapped_view
    (ZkFormal.NearV3.Candidates.MerkleEmpty.focus_local hL ZkFormal.Near.T_MRK)
  refine ⟨v, hw, fun b m => ?_⟩
  simpa only [ZkFormal.NearV3.Candidates.MerkleEmpty.focus_count] using ht b m

/-- **All views at once.** From `HoldsP` on a successful preparation (below the field size):
records of the thirteen viewed tables, their well-formedness and exact traffic. -/
theorem v3Records_of_holdsP {cb : Bytes} {h : Hint} {p : Prep} {oh : Nat} {tr : Trace Fp}
    (hp : prepD0 cb h = .ok p)
    (hsz : (ZkFormal.NearV3.Public.preparedBytes p oh).length < ZkFormal.Algebra.P)
    (hH : HoldsP nearAirV3 (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr) :
    ∃ r, V3RecordsWf (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r ∧
      V3RecordsTraffic (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr r := by
  obtain ⟨vs, wN, tN⟩ := nodeView hH
  obtain ⟨hs, wH, tH⟩ := headView hH
  obtain ⟨es, wV, tV⟩ := valView hH
  obtain ⟨ws, wW, wS, tW⟩ := walkView hH
  obtain ⟨us, wU, tU⟩ := uniqView hH
  obtain ⟨u, wP, tP⟩ := upsView hH
  obtain ⟨ls, wR, tR⟩ := rcptV3_view_nearAir hp hsz tr T_RCPT (rcptLocal hH)
  obtain ⟨as, wA, tA⟩ := acctView hH
  obtain ⟨ks, wK, tK⟩ := akeyView hH
  obtain ⟨bs, wB, tB⟩ := bndView hH
  obtain ⟨ss, wS', tS'⟩ := ZkFormal.NearV3.srcp_view (srcpLocal hH)
  obtain ⟨sz, wZ, tZ⟩ := sizeView hH
  obtain ⟨mv, wM, tM⟩ := mrkView hH
  exact ⟨⟨vs, hs, es, ws, us, u, ls, as, ks, bs, ss, sz, mv⟩,
    ⟨wN, wH, wV, wW, wS, wU, wP, wR, wA, wK, wB, wS', wZ, wM⟩,
    ⟨tN, tH, tV, tW, tU, tP, tR, tA, tK, tB, tS', tZ, tM⟩⟩

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
