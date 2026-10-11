import ZkFormal.NearV3.Assembly.RcptViewV3

/-! Guard the repaired receipt-table view of `nearAirV3`. -/

/-- info: 'ZkFormal.NearV3.Assembly.rcptV3_view_nearAir' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Assembly.rcptV3_view_nearAir

/-- info: 'ZkFormal.NearV3.Assembly.mem_send_sources' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Assembly.mem_send_sources

/-- info: 'ZkFormal.NearV3.Assembly.RcptSkeleton.tableR_eq' depends on axioms: [propext] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Assembly.RcptSkeleton.tableR_eq
