import ZkFormal.NearV3.BudgetUps
import ZkFormal.NearV3.Sched.Budget
import ZkFormal.NearV3.Rcpt.Budget
import ZkFormal.NearV3.Rcpt.Tables.SrcpDD
import ZkFormal.NearV3.Rcpt.Tables.RcptR
import ZkFormal.NearV3.Rcpt.Candidates.AccountEmpty
import ZkFormal.NearV3.Qv.Candidates.KeyTrafficRepair
import ZkFormal.NearV3.Candidates.MerklePublic
import ZkFormal.NearV3.Candidates.MerkleEmpty
import ZkFormal.NearV3.Candidates.SortEmpty
import ZkFormal.NearV3.Public.Prepared
import ZkFormal.Chacha.Table
import ZkFormal.Chacha.Rng.Table
import ZkFormal.Chacha.Shuffle.Table
import ZkFormal.Near.Tables.Sort
import ZkFormal.NearV3.Tables.UnfoldA7
import ZkFormal.NearV3.Assembly.NearAirDefs

/-!
# ZkFormal.NearV3.Assembly.NearAir — the assembled v3 AIR `nearAirV3`

`nearAirV3` is the single value every v3 assembly obligation is stated about: the
two SHA-256 instances (V3-D0-DESIGN §3.1, needed for `B0 = 2,000,000`), the six
trie tables of lane `v3-trie`, the three ChaCha tables of lane `v3-chacha`, the
five bandwidth-scheduler tables of lane `v3-sched`, the six receipt-side tables
of lane `v3-rcpt`, the queue-value parser of lane `v3-qvals`, and v1's `mrk`/`sort`
at their v3 heights.  The public interface is the concrete prepared statement
`Public.preparedSegments` (§2.1/§2.4).

Table order (fixed; table index = position):

```
0,1   sha_t   sha_r        (two L5 instances)
2..7  nodeV3 headV3 valV3 walkV3 uniqV3 upsV3   (trie)
8..10 chachaV3 rngV3 shufV3   (cap 22: the A9 W0 lane, `table22`)
11..15 codecV3 ssdV3 sprV3 smmV3 scpV3          (scheduler; sprV3 = boundary-repaired `Proc.tableB`)
16..21 rcptV3 acctV3 akeyV3 bndV3 srcpV3 sizeV3 (receipt; rcpt = `RcptV3.tableQ`: `tableR` (gas and
      deposit-age repairs) + the routing-index range check `q < 128`; acct = `acctTableV3` (empty-capable `AccountEmpty.table`, maxLog 19),
      size at maxLog 4,
      srcp = `SrcpDD.table` (DedupTable + the A10 depth check, `rep` public bit);
      the roll-aligned honest heights, `Render/PaddedRcpt.lean`)
22    qvV3                (queue-value parser)
23    mrkV3               (v1 Mrk at maxLog 19, empty-tree repair `MerkleEmpty.table`)
24    sortV3             (v1 Sort at maxLog 19, empty-input repair `SortEmpty.table`)
```
-/

namespace ZkFormal.NearV3.Assembly

open ZkFormal.Air ZkFormal.V2

def v1Tables : List ZkFormal.Air.Table :=
  [ZkFormal.NearV3.Candidates.MerkleEmpty.table, sortTableV3]

/-- The v3 tables, in the fixed order above, without the two SHA instances. -/
def nearTablesV3 : List ZkFormal.Air.Table :=
  ZkFormal.NearV3.Budget.trieTablesU ++
  [ZkFormal.Chacha.Table.table22 ZkFormal.NearV3.Sched.B_SCHACHA,
   ZkFormal.Chacha.Rng.Table.table22 ZkFormal.NearV3.Sched.B_SCHACHA ZkFormal.NearV3.Sched.B_SGEN,
   ZkFormal.Chacha.Shuffle.Table.table22 ZkFormal.NearV3.Sched.B_SSIN ZkFormal.NearV3.Sched.B_SSOUT
     ZkFormal.NearV3.Sched.B_SSMEM ZkFormal.NearV3.Sched.B_SGEN ZkFormal.NearV3.Sched.B_SSHUF] ++
  ZkFormal.NearV3.Sched.Budget.schedTables ++
  ZkFormal.NearV3.Rcpt.Budget.rcptTables ++
  [ZkFormal.NearV3.Qv.Candidates.KeyTrafficRepair.table] ++ v1Tables

theorem nearAirV3_toAir : nearAirV3.toAir = nearAirV3Air := rfl
theorem nearAirV3_tables : nearAirV3.tables = nearTablesFull := rfl
theorem nearAirV3_tables_length : nearAirV3.tables.length = 25 := rfl

end ZkFormal.NearV3.Assembly
