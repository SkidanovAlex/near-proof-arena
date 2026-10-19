import ZkFormal.PQ.StatePort.Bridge
import ZkFormal.PQ.StatePort.Bounds
import ZkFormal.NearV3.Assembly.ExtractV3Proof

/-!
# ZkFormal.PQ.StatePort.D0a — PQ base proof accepted ⇒ the D0a chunk relation

Lane `pq-state-port`.  This is the composition the port exists for: take SWIRL's relation of the
*unchanged* classical `nearAirV3` AIR (`PQ.StatePort.Swirl`), turn it into the classical
`HoldsP` (`PQ.StatePort.Bridge.holdsP_of_swirl`), and feed that to the already-proved
`extractV3`, which recovers `GoodV3` — and through `factorSound`/`relD0a_iff`, `RelD0a`.

The statement is exactly the classical D0a soundness statement, with the *only* change being
where the trace relation comes from (SWIRL instead of the classical IOP).  What is new is:

* `holdsP_of_swirl` — the bridge, proved in `Bridge.lean` with no `sorry`;
* `nearAirV3_multBoundP_lt` — P2, a kernel fact in `Bounds.lean`;
* `pq_d0a_extract` below — the composition, so a PQ base proof of the 25 classical tables yields
  `GoodV3 B0` under the same hypotheses `extractV3` already uses.

The remaining assumption is SWIRL's own soundness (P5), shared with every PQ AIR.  This module
does not touch the classical certificate, the spec or the challenges.
-/

namespace ZkFormal.PQ.StatePort

open ZkFormal.Air ZkFormal.V2 ZkFormal.Algebra ZkFormal.Udr ZkFormal.NearV3 NearSpec NearSpecV3

/-! ## Sizes and static bounds, from the existing kernel facts -/

/-- The static multiplicity bound of `nearAirV3` is below `p` (P2, `Bounds.lean`). -/
theorem nearAirV3_multBoundP_lt' : Assembly.nearAirV3.multBoundP < ZkFormal.Algebra.P :=
  nearAirV3_multBoundP_lt

/-! ## The composition -/

/-- **PQ base proof accepted ⇒ `GoodV3` (D0a).**

This is `ExtractV3StmtAt` with the `HoldsP` premise produced by the SWIRL bridge instead of by the
classical protocol.  The inputs are:

* `hs` — the SWIRL PIOP relation of the translated AIR (assumption P5);
* `hv` — `V_d`'s checks, including TAPE net multiplicities under commitment binding;
* `hmult` — `multBoundP nearAirV3 < p` (proved: `nearAirV3_multBoundP_lt`);
* `hfitW` — segment widths `≥ 1` (the classical `AirP.wf`);
* `hlen25` — the static `mult.length ≤ 25` bound of the exported AIR.

Everything else is the classical statement. -/
theorem pq_d0a_good
    (cb : NearSpec.Bytes) (hint : NearSpecV3.Hint) (p : NearSpecV3.Prep) (oh : Nat)
    (tr : Trace Fp) (pv : Nat → List Fp) (tape : Tape) (off : Nat)
    (hprep : NearSpecV3.prepD0 cb hint = .ok p)
    (hlen : (ZkFormal.NearV3.Public.preparedBytes p oh).length < ZkFormal.Algebra.P)
    (hmult : Assembly.nearAirV3.multBoundP < ZkFormal.Algebra.P)
    (hs : SwirlRel off Assembly.nearAirV3 pv tr tape)
    (hv : VdChecks off Assembly.nearAirV3
      (Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) pv tr tape)
    (hfitW : ∀ s ∈ Assembly.nearAirV3.pubSegs, 1 ≤ s.width)
    (hlen25 : ∀ t (ht : t < Assembly.nearAirV3.tables.length),
      ∀ i ∈ Assembly.nearAirV3.tables[t].interactions, i.mult.length ≤ 25) :
    ∃ k x, Assembly.GoodV3 NearSpecV3.B0 cb k hint p x :=
  Assembly.extractV3 cb hint p oh tr hprep hlen
    (holdsP_of_swirl off Assembly.nearAirV3
      (Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) pv tr tape
      hmult hs hv hfitW hlen25)

/-- **PQ base proof accepted ⇒ `RelD0a`**, through `GoodV3` and `relD0a_of_good`. -/
theorem pq_d0a_rel
    (cb : NearSpec.Bytes) (hint : NearSpecV3.Hint) (p : NearSpecV3.Prep) (oh : Nat)
    (tr : Trace Fp) (pv : Nat → List Fp) (tape : Tape) (off : Nat)
    (hprep : NearSpecV3.prepD0 cb hint = .ok p)
    (hlen : (ZkFormal.NearV3.Public.preparedBytes p oh).length < ZkFormal.Algebra.P)
    (hmult : Assembly.nearAirV3.multBoundP < ZkFormal.Algebra.P)
    (hs : SwirlRel off Assembly.nearAirV3 pv tr tape)
    (hv : VdChecks off Assembly.nearAirV3
      (Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) pv tr tape)
    (hfitW : ∀ s ∈ Assembly.nearAirV3.pubSegs, 1 ≤ s.width)
    (hlen25 : ∀ t (ht : t < Assembly.nearAirV3.tables.length),
      ∀ i ∈ Assembly.nearAirV3.tables[t].interactions, i.mult.length ≤ 25) :
    ∃ k x, NearSpecV3.RelD0a NearSpecV3.B0 cb
      (Assembly.witnessOfV3 k x) := by
  obtain ⟨k, x, hg⟩ := pq_d0a_good cb hint p oh tr pv tape off hprep hlen hmult hs hv hfitW hlen25
  exact ⟨k, x, Assembly.relD0a_of_good hg⟩

end ZkFormal.PQ.StatePort
