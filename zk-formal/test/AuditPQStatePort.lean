import ZkFormal.PQ.StatePort.Bridge
import ZkFormal.PQ.StatePort.Bounds

/-!
# Audit: the pq-state-port Lean bridge uses only the standard axioms

Lane `pq-state-port`.  The bridge lemmas and the P2 kernel facts must not depend on `sorryAx` or
any project-specific axiom.  The expected answers:

* the arithmetic/logUp/bits lemmas: `[propext, Classical.choice, Quot.sound]`;
* the height-bound lemma: `[propext, Quot.sound]`;
* the two `multBoundP < p` kernel facts: `[propext]`.
-/

open ZkFormal.PQ.StatePort

#check @countF_eq_multNat
#check @bits_of_swirl
#check @eval_eq_of_agree
#check @rowSum_eq_sub
#check @tablesSum_eq_flat
#check @busCount_le_multBound
#check @nearAirV3_multBoundP_lt
#check @nearAirV3D1_multBoundP_lt

#print axioms ZkFormal.PQ.StatePort.countF_eq_multNat
#print axioms ZkFormal.PQ.StatePort.bits_of_swirl
#print axioms ZkFormal.PQ.StatePort.busCount_le_multBound
#print axioms ZkFormal.PQ.StatePort.nearAirV3_multBoundP_lt
#print axioms ZkFormal.PQ.StatePort.nearAirV3D1_multBoundP_lt
