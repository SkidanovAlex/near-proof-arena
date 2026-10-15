import ZkFormal.NearV3.Assembly.NearAirDefs
import ZkFormal.NearV3.D1.Tables.TxDefs
import ZkFormal.NearV3.D1.Tables.AkmDefs
import ZkFormal.NearV3.D1.Tables.RelayDefs
import ZkFormal.NearV3.D1.Tables.RcptD1Defs
import ZkFormal.NearV3.D1.Public.PreparedD1Defs
import ZkFormal.NearV3.D1.Tables.NodeStubDefs
import ZkFormal.NearV3.D1.Tables.UniqGapDefs
import ZkFormal.NearV3.D1.Tables.WalkUDefs
import ZkFormal.NearV3.D1.Tables.NmemDefs
import ZkFormal.NearV3.D1.Tables.UvalDefs
import ZkFormal.NearV3.D1.Tables.KibUDefs

/-!
# `ZkFormal.NearV3.D1.NearAirD1Defs` — the D1 AIR `nearAirV3D1`

Lane `v3-d1-tables` (V3-D1-DESIGN §2.2, §6.4: one combined AIR, a superset of `nearAirV3`).
Definitions only (verifier-model import rule).  `nearAirV3` and its tables are not modified:
`nearAirV3D1` is a new constant built from the same table values.

Tables (index = position): `0 … 24` are `nearTablesFull` with four entries replaced,
* `16`: `rcptV3D1` (`RcptD1.tableQD1`: `tableQ` with six expressions offset by public `M0`,
  `T0`, `O0`, `TOK0`, and a 14-bit deposit age);
* `23`: `mrkV3` at `maxLog 20` (`≤ NT0 + 4481` leaves × 64 rows `< 2^20`; D0a's 19 holds
  `≤ 8192` leaves);
* `2`: `nodeD1` (`nodeA7` extended with the stub windows: `SEDGE`, `NMQ`; lane v3-d1-a7b);
* `6`: `uniqD1` (`uniqV3` extended with the gap lookups `GB`; lane v3-d1-a7b);

then the D1 tables
`25 txV3`, `26 akmV3`, `27 kibD1` (`kibV3` routing the unread-key walks to `UKEYNIB`),
`28 plfV3`, `29 ridV3`, and the unread-key tables of plan §5 R-5 → (B) (lane v3-d1-a7b):
`30 walkU` (the walks of every `txKeys` entry, with the stub terminal), `31 nmemV3`
(non-membership of a stub's hash among the store digests), `32 uvalV3` (the bytes of values
revealed only for unread keys).
Public: the 15 segments of `PreparedD1Defs.preparedSegmentsD1`, `numPub = 350` (the D0a
header, the 15 descriptors, the 28-byte extension).
-/

namespace ZkFormal.NearV3.D1

open ZkFormal.Air ZkFormal.V2 ZkFormal.NearV3.Assembly

/-- `mrkV3` at the D1 height cap. -/
def mrkTableD1 : ZkFormal.Air.Table :=
  { ZkFormal.NearV3.Candidates.MerkleEmpty.table with maxLog := 20 }

/-- The D1 tables appended after the 25 of `nearAirV3`. -/
def d1Tables : List ZkFormal.Air.Table :=
  [TxV3.table, AkmV3.table, KibD1.table, PlfV3.table, RidV3.table,
   WalkU.table, NmemV3.table, UvalV3.table]

/-- The 33 tables of `nearAirV3D1`. -/
def nearTablesD1 : List ZkFormal.Air.Table :=
  (((nearTablesFull.set 16 RcptD1.tableQD1).set 23 mrkTableD1).set 2 nodeD1).set 6 uniqD1 ++
    d1Tables

def nearAirV3D1Air : Air := ⟨nearTablesD1, nearBuses, numPubD1⟩

/-- **The assembled D1 AIR.** -/
def nearAirV3D1 : AirP :=
  { nearAirV3D1Air with pubSegs := Public.preparedSegmentsD1, maxPub := 67108864 }

end ZkFormal.NearV3.D1
