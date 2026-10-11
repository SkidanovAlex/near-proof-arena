import ZkFormal.NearV3.Assembly.NearAirSize
import ZkFormal.NearV3.Assembly.NearAirCheck
import ZkFormal.NearV3.Assembly.LinkV3

/-- info: 'ZkFormal.NearV3.Assembly.nearAirV3_wf' depends on axioms: [propext] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Assembly.nearAirV3_wf

/-- info: 'ZkFormal.NearV3.Assembly.nearAirV3_npOkPg' depends on axioms: [propext, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Assembly.nearAirV3_npOkPg

/-- info: 'ZkFormal.NearV3.Assembly.nearV3_size' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Assembly.nearV3_size

/-- info: 'ZkFormal.NearV3.Assembly.tableBusCount_append' depends on axioms: [propext, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Assembly.tableBusCount_append
