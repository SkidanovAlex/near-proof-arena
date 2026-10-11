import ZkFormal.NearV3.Sched.Link.GridLink
import ZkFormal.NearV3.Sched.Link.SoundFin
import ZkFormal.NearV3.Assembly.NearAirSize

/-! Guard the scheduler soundness re-proved for the boundary-repaired process table
(`Proc.tableB`, `nearAirV3` table 13) and the re-checked AIR facts. -/

/-- info: 'ZkFormal.NearV3.Sched.schedCore_sound''' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Sched.schedCore_sound''

/-- info: 'ZkFormal.NearV3.Sched.Proc.inst_exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Sched.Proc.inst_exists

/-- info: 'ZkFormal.NearV3.Assembly.nearV3_size' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Assembly.nearV3_size
