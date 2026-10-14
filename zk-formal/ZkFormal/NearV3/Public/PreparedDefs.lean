import NearSpecV3.PrepD0
import ZkFormal.NearV3.Ids
import ZkFormal.NearV3.Public.BodyDefs
import ZkFormal.NearV3.Public.BoundaryDefs
import ZkFormal.NearV3.Public.HeaderDefs
import ZkFormal.NearV3.Public.LayoutDefs
import ZkFormal.NearV3.Public.NatRecordsDefs
import ZkFormal.NearV3.Public.PackingDefs
import ZkFormal.NearV3.Public.SourceDefs
import ZkFormal.NearV3.Sched.Ids
import ZkFormal.NearV3.Sched.Pub.RawDefs
import ZkFormal.NearV3.Sched.RenderDefs
import ZkFormal.V2.Air

/-!
# `ZkFormal.NearV3.Public.PreparedDefs`

The definitions of `ZkFormal.NearV3.Public.Prepared` that the deployed verifier model
(`NpUdrStarkV2.Model.verifier`) uses, moved verbatim (same names, statements and bodies).
`ZkFormal.NearV3.Public.Prepared` imports this module, so its importers see the same names. Definitions only:
the model's import closure must not contain proof modules (judge native-lean build,
lane v3-model-split, docs/logs/v3-model-split-2026-10.md).
-/

namespace ZkFormal.NearV3.Public

open ZkFormal.V2 NearSpecV3

def plainPlan (bus : Nat) (send : Bool) (width : Nat) : PubSeg :=
  { bus, send, width, countAt := 0, start := 0 }

/-- Nine fixed descriptors; counts and offsets are read from the metadata header. -/
def plans : List PubSeg :=
  [sourcePlan, boundaryPlan, bodyPlan,
   plainPlan Sched.B_SPUBB true 7, plainPlan Sched.B_SPAR true 11,
   plainPlan Sched.B_SDL true 5, plainPlan Sched.B_SDL false 5,
   plainPlan B_ROOT true 33, plainPlan B_ROOT false 33]

def schedulerRecords (p : Prep) : Sched.PubRecs := Sched.render (p.sched.map Sched.instOf) p.fwd

def rootPayload (tau : Nat) (root : ByteString) : Payload := [[UInt8.ofNat tau] ++ root]

def preparedBlocks (p : Prep) : List Payload :=
  [sourcePayload p.lists, boundaryPayload p.bnds, bodyPayload p.body,
   natPayload (schedulerRecords p).pubb, natPayload (schedulerRecords p).par,
   natPayload (schedulerRecords p).dlSend, natPayload (schedulerRecords p).dlRecv,
   rootPayload 0 p.hdr.prevStateRoot, rootPayload (p.hdr.K+1) p.hdr.postStateRoot]

def preparedBytes (p : Prep) (witnessOverhead : Nat) : ByteString :=
  encode (headerBytes p witnessOverhead) (preparedBlocks p)

/-- Static segment header locations, independent of the prepared statement. -/
def preparedSegments : List PubSeg :=
  (List.range plans.length).map (fun i => descriptor (plans.getD i sourcePlan) 202 i)

end ZkFormal.NearV3.Public
