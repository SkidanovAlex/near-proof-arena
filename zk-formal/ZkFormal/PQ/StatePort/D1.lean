import ZkFormal.PQ.StatePort.Bridge
import ZkFormal.PQ.StatePort.Bounds
import ZkFormal.NearV3.D1.PrepD1Lemmas
import ZkFormal.NearV3.D1.StmtsT

/-!
# ZkFormal.PQ.StatePort.D1 — PQ base proof accepted ⇒ the D1a relation

Lane `pq-state-port`.  The D1 parallel of `PQ.StatePort.D0a`: the same bridge
(`PQ.StatePort.Bridge.holdsP_of_swirl`) applied to `nearAirV3D1`, fed into the D1 phase-1
soundness interface `ExtractD1Stmt` (`NearV3.D1.PrepD1Lemmas`).

`ExtractD1Stmt` is the D1 phase-2 obligation in its stated form: a prepared statement and a
`HoldsP nearAirV3D1` trace give a `RelD1a` witness.  This module does not prove
`ExtractD1Stmt` — it shows that **whatever it proves carries over to the PQ backend unchanged**,
because the bridge only ever produced the `HoldsP` premise that `ExtractD1Stmt` consumes.

So the D1 statement on the PQ stack is: `ExtractD1Stmt` (the backend-independent phase-2 work)
plus the bridge plus `multBoundP nearAirV3D1 < p` (proved, `Bounds.lean`) plus SWIRL's soundness.
-/

namespace ZkFormal.PQ.StatePort

open ZkFormal.Air ZkFormal.V2 ZkFormal.Algebra ZkFormal.Udr ZkFormal.NearV3
open NearSpec NearSpecV3


/-- The D1 multiplicity bound is below `p` (`Bounds.lean`, a kernel fact). -/
theorem nearAirV3D1_multBoundP_lt' : ZkFormal.NearV3.D1.nearAirV3D1.multBoundP < ZkFormal.Algebra.P :=
  nearAirV3D1_multBoundP_lt

/-- **PQ base proof accepted ⇒ the D1a relation**, given the phase-2 D1 soundness interface.

The `HoldsP nearAirV3D1` premise that `ExtractD1StmtT` takes is replaced by the SWIRL bridge: the
relation of the translated AIR, `V_d`'s checks, the multiplicity bound and the AIR's static
bounds.  Everything else is `ExtractD1StmtT` itself. -/
theorem pq_d1_rel
    (hExtract : ZkFormal.NearV3.D1.ExtractD1StmtT)
    (cb : NearSpec.Bytes) (hint : ZkFormal.NearV3.D1.HintD1) (p : ZkFormal.NearV3.D1.Public.PrepD1)
    (tr : Trace Fp) (pv : Nat → List Fp) (tape : Tape) (off : Nat)
    (hprep : ZkFormal.NearV3.D1.prepD1 cb hint = .ok p)
    (hlen : (ZkFormal.NearV3.D1.Public.preparedBytesD1 p
      (ZkFormal.NearV3.D1.txOverhead hint)).length < ZkFormal.Algebra.P)
    (hmult : ZkFormal.NearV3.D1.nearAirV3D1.multBoundP < ZkFormal.Algebra.P)
    (hs : SwirlRel off ZkFormal.NearV3.D1.nearAirV3D1 pv tr tape)
    (hv : VdChecks off ZkFormal.NearV3.D1.nearAirV3D1
      (Udr.pubOf Fp (ZkFormal.NearV3.D1.Public.preparedBytesD1 p
        (ZkFormal.NearV3.D1.txOverhead hint))) pv tr tape)
    (hfitW : ∀ s ∈ ZkFormal.NearV3.D1.nearAirV3D1.pubSegs, 1 ≤ s.width)
    (hlen25 : ∀ t (ht : t < ZkFormal.NearV3.D1.nearAirV3D1.tables.length),
      ∀ i ∈ ZkFormal.NearV3.D1.nearAirV3D1.tables[t].interactions, i.mult.length ≤ 25) :
    ∃ w, RelD1a NearSpecV3.B0 cb w :=
  hExtract cb hint p tr hprep hlen
    (holdsP_of_swirl off ZkFormal.NearV3.D1.nearAirV3D1
      (Udr.pubOf Fp (ZkFormal.NearV3.D1.Public.preparedBytesD1 p
        (ZkFormal.NearV3.D1.txOverhead hint))) pv tr tape
      hmult hs hv hfitW hlen25)

end ZkFormal.PQ.StatePort
