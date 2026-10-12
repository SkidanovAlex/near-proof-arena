import ZkFormal.NearV3.Render.PaddedQv
import ZkFormal.NearV3.Candidates.NativeQueueIds
import ZkFormal.NearV3.Assembly.QueuePayload

/-!
# The honest `qvV3` table over native inputs

`qv_aligned_complete` instantiated at the native queue data: the read plan
`plan pre v pres (NativeQueueIds.resolve pre v pres)` (main-queue reads, then one missing-key
read per implicit pre-trie, value ids/users allocated by `NativeQueueIds.resolve`) and the
records `queueRecords (queueForestProviders 0 0 (queueInputs pre v pres))` of the queue
providers.  The traffic `repairedTraffic` is therefore a function of `(pre, v, pres)` only.
-/

namespace ZkFormal.NearV3.Render
open ZkFormal.Near ZkFormal.Air ZkFormal.Algebra
open ZkFormal.NearV3.Qv ZkFormal.NearV3.Qv.Candidates ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen
open ZkFormal.NearV3.Assembly

/-- Native queue walks. -/
def qvNativeWalks (pre : NearSpec.PTrie) (v : MainValues) (pres : List NearSpec.PTrie) : List Walk :=
  plan pre v pres (ZkFormal.NearV3.Candidates.NativeQueueIds.resolve pre v pres)

/-- Native queue value records. -/
def qvNativeRecords (pre : NearSpec.PTrie) (v : MainValues) (pres : List NearSpec.PTrie) :
    List ValueGen.Record :=
  queueRecords (queueForestProviders 0 0 (queueInputs pre v pres))

/-- **The honest `qvV3` traffic**, over the native queue inputs. -/
def qvNativeTraffic (pre : NearSpec.PTrie) (v : MainValues) (pres : List NearSpec.PTrie) : Traffic :=
  repairedTraffic (qvNativeWalks pre v pres) (qvNativeRecords pre v pres)

def qvNativeTrace (pre : NearSpec.PTrie) (v : MainValues) (pres : List NearSpec.PTrie) : Trace Fp :=
  qvTraceAligned pre v pres (ZkFormal.NearV3.Candidates.NativeQueueIds.resolve pre v pres)
    (qvNativeRecords pre v pres)

/-- The honest hypothesis over native inputs: valid main values, valid provider records (from
accepted modes and `Σ bytes ≤ B0`, `queueRecords_valid_bytes`), the row bound, and the public
implicit count. -/
structure QvNativeOk (pre : NearSpec.PTrie) (v : MainValues) (pres : List NearSpec.PTrie)
    (pub : List Fp) : Prop where
  valid : v.Valid
  records : ∀ r ∈ qvNativeRecords pre v pres, r.Valid
  rows : qvRows (qvNativeWalks pre v pres) (qvNativeRecords pre v pres) ≤ 2 ^ 22
  pubCount : ∀ r, CombinedTable.kPublic.eval (qvNativeTrace pre v pres) 0 r pub =
    @Nat.cast Fp Lean.Grind.Semiring.natCast pres.length

/-- **Queue-value table completeness over native inputs** (`nearAirV3` table 22). -/
theorem qv_native_aligned_complete (pre : NearSpec.PTrie) (v : MainValues) (pres : List NearSpec.PTrie)
    (pub : List Fp) (ok : QvNativeOk pre v pres pub) (t : Nat) :
    TableLocal KeyTrafficRepair.table (qvNativeTrace pre v pres) t pub ∧
    TableTraffic KeyTrafficRepair.interactions (qvNativeTrace pre v pres) t pub
      (qvNativeTraffic pre v pres) ∧
    (qvNativeTrace pre v pres).log t % 3 = 1 :=
  qv_aligned_complete pre v pres _ _ pub
    ⟨ok.valid, ok.records, ok.rows, ok.pubCount⟩ t

end ZkFormal.NearV3.Render
