import ZkFormal.Air.Basic
import ZkFormal.Chacha.Rng.Table
import ZkFormal.Chacha.Shuffle.Table
import ZkFormal.Chacha.Table
import ZkFormal.Near.Ids
import ZkFormal.NearV3.Candidates.MerkleEmptyDefs
import ZkFormal.NearV3.Candidates.SortEmptyDefs
import ZkFormal.NearV3.Public.PreparedDefs
import ZkFormal.NearV3.Qv.Candidates.KeyTrafficRepairDefs
import ZkFormal.NearV3.Rcpt.Candidates.AccountEmptyDefs
import ZkFormal.NearV3.Rcpt.Tables.Akey
import ZkFormal.NearV3.Rcpt.Tables.Bnd
import ZkFormal.NearV3.Rcpt.Tables.RcptRDefs
import ZkFormal.NearV3.Rcpt.Tables.SrcpDDDefs
import ZkFormal.NearV3.Sched.Ids
import ZkFormal.NearV3.Sched.Tables.CmpDefs
import ZkFormal.NearV3.Sched.Tables.Codec
import ZkFormal.NearV3.Sched.Tables.Mem
import ZkFormal.NearV3.Sched.Tables.Proc
import ZkFormal.NearV3.Sched.Tables.ScanDistDefs
import ZkFormal.NearV3.Tables.Head
import ZkFormal.NearV3.Tables.UnfoldA7
import ZkFormal.NearV3.Tables.Uniq
import ZkFormal.NearV3.Tables.Walk
import ZkFormal.Sha.Table
import ZkFormal.V2.Air

/-!
# `ZkFormal.NearV3.Assembly.NearAirDefs`

The definitions of `ZkFormal.NearV3.Assembly.NearAir` that the deployed verifier model
(`NpUdrStarkV2.Model.verifier`) uses, moved verbatim (same names, statements and bodies).
`ZkFormal.NearV3.Assembly.NearAir` imports this module, so its importers see the same names. Definitions only:
the model's import closure must not contain proof modules (judge native-lean build,
lane v3-model-split, docs/logs/v3-model-split-2026-10.md).
-/

namespace ZkFormal.NearV3.Assembly

open ZkFormal.Air ZkFormal.V2

/-- A SHA-256 table instance (`L5`, unchanged; kind-registered per §12). -/
abbrev shaTable : ZkFormal.Air.Table := ZkFormal.Sha.Table.table ZkFormal.Near.B_BYTES ZkFormal.Near.B_DIGEST

/-- The v1 tables reused at v3 heights, with their empty-input repairs (a chunk may have no
receipts; D0a does not exclude it): `mrk` (`maxLog 19`, public-index translated to the v3
`PH_N`/`PH_OUT` offsets, `MerkleEmpty`: count 0 ⇒ zero root and no traffic) and `sort`
(`maxLog 19` = the aligned height of `≤ 8192` ids, `SortEmpty`: the first row may be inactive). -/
def sortTableV3 : ZkFormal.Air.Table := { ZkFormal.NearV3.Candidates.SortEmpty.table with maxLog := 19 }

/-- Table 17: `acctV3` at the roll-aligned cap 19 with the empty-chunk repair
(`AccountEmpty.table`: row-0 constraint `isFirst·(act − af)` in place of `isFirst·(1 − af)`).
An accepted chunk whose applied source lists are all empty reads no account; the repair admits
the all-inactive (traffic-free) table, and an active first row still starts a segment
(`AccountEmptyCap.acctV3_empty_or_old`). -/
def acctTableV3 : ZkFormal.Air.Table :=
  { ZkFormal.NearV3.Rcpt.Candidates.AccountEmpty.table with maxLog := 19 }

/-- The full trie-and-beyond table list, fully literal (so `busCount` decomposes
by `rfl`): two SHA instances first, then the trie, ChaCha, scheduler, receipt,
queue-value and v1 tables in the fixed order.  `nearTablesFull_literal` ties it
to the composed `nearTablesFull`. -/
def nearTablesFull : List ZkFormal.Air.Table :=
  [shaTable, shaTable,
   ZkFormal.NearV3.UnfoldA7.nodeA7, {ZkFormal.NearV3.HeadV3.table with maxLog := 13},
   ZkFormal.NearV3.UnfoldA7.valA7, {ZkFormal.NearV3.WalkV3.table with maxLog := 22},
   ZkFormal.NearV3.Uniq.table, ZkFormal.NearV3.UnfoldA7.upsA7,
   ZkFormal.Chacha.Table.table22 ZkFormal.NearV3.Sched.B_SCHACHA,
   ZkFormal.Chacha.Rng.Table.table22 ZkFormal.NearV3.Sched.B_SCHACHA ZkFormal.NearV3.Sched.B_SGEN,
   ZkFormal.Chacha.Shuffle.Table.table22 ZkFormal.NearV3.Sched.B_SSIN ZkFormal.NearV3.Sched.B_SSOUT
     ZkFormal.NearV3.Sched.B_SSMEM ZkFormal.NearV3.Sched.B_SGEN ZkFormal.NearV3.Sched.B_SSHUF,
   ZkFormal.NearV3.Sched.Codec.table, ZkFormal.NearV3.Sched.ScanDist.table,
   ZkFormal.NearV3.Sched.Proc.tableB, ZkFormal.NearV3.Sched.Mem.table,
   ZkFormal.NearV3.Sched.Cmp.table ZkFormal.NearV3.Sched.B_SCMP,
   ZkFormal.NearV3.RcptV3.tableQ, acctTableV3, ZkFormal.NearV3.AkeyV3.table,
   ZkFormal.NearV3.BndV3.table, ZkFormal.NearV3.SrcpDD.table, ZkFormal.NearV3.UnfoldA7.sizeA7,
   ZkFormal.NearV3.Qv.Candidates.KeyTrafficRepair.table,
   ZkFormal.NearV3.Candidates.MerkleEmpty.table, sortTableV3]

/-- `numBuses` covers every bus any table uses (max in use is `B_QVC = 63`). -/
def nearBuses : Nat := 77

/-- `numPub`: static public-header reads; the variable-length data enter through the
public segments, not `.pub`. -/
def nearNumPub : Nat := 202

/-- The v1 AIR underlying the v3 candidate (no public segments). -/
def nearAirV3Air : Air := ⟨nearTablesFull, nearBuses, nearNumPub⟩

/-- **The assembled v3 AIR.** `pubSegs` is the concrete prepared statement. -/
def nearAirV3 : AirP :=
  { nearAirV3Air with pubSegs := ZkFormal.NearV3.Public.preparedSegments, maxPub := 67108864 }

end ZkFormal.NearV3.Assembly
