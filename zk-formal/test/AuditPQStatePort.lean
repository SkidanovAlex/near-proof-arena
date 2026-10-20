import ZkFormal.PQ.StatePort.Bridge
import ZkFormal.PQ.StatePort.Bounds
import ZkFormal.PQ.StatePort.D0a
import ZkFormal.PQ.StatePort.D1
import ZkFormal.PQ.StatePort.TapeCollapse
import ZkFormal.PQ.StatePort.Join
import ZkFormal.PQ.StatePort.JoinFold

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
#check @holdsP_of_swirl
#check @pq_d0a_good
#check @pq_d0a_rel
#check @pq_d1_rel
#check @canonKeys_nodup
#check @sel_fsum_eq
#check @nearAirV3_buses_below_128
#check @nearAirV3D1_buses_below_128
#check @join_partition
#check @host_buses_clear
#check @tapeNet_canon
#check @join_additive
#check @WasmRunStmt
#check @tablesSum_eq_sides
#check @balance_step
#check @nearAirV3_multBoundP_lt
#check @nearAirV3D1_multBoundP_lt

#print axioms ZkFormal.PQ.StatePort.countF_eq_multNat
#print axioms ZkFormal.PQ.StatePort.bits_of_swirl
#print axioms ZkFormal.PQ.StatePort.busCount_le_multBound
#print axioms ZkFormal.PQ.StatePort.nearAirV3_multBoundP_lt
#print axioms ZkFormal.PQ.StatePort.nearAirV3D1_multBoundP_lt
#print axioms ZkFormal.PQ.StatePort.holdsP_of_swirl
#print axioms ZkFormal.PQ.StatePort.tablesSum_eq_sides
#print axioms ZkFormal.PQ.StatePort.pq_d0a_good
#print axioms ZkFormal.PQ.StatePort.pq_d0a_rel
#print axioms ZkFormal.PQ.StatePort.pq_d1_rel
#print axioms ZkFormal.PQ.StatePort.sel_fsum_eq
#print axioms ZkFormal.PQ.StatePort.canonKeys_nodup
#print axioms ZkFormal.PQ.StatePort.nearAirV3_buses_below_128
#print axioms ZkFormal.PQ.StatePort.join_partition
#print axioms ZkFormal.PQ.StatePort.host_buses_clear
#print axioms ZkFormal.PQ.StatePort.tapeNet_canon
#print axioms ZkFormal.PQ.StatePort.join_additive
