import ZkFormal.NearV3.Assembly.RenderV3Header

/-! Guard the assumptions of the hint codec bounds and the bundle header admissibility. -/

/-- info: 'ZkFormal.NearV3.Assembly.nativeHint_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Assembly.nativeHint_bounds

/-- info: 'ZkFormal.NearV3.Assembly.AcceptedV3.hint_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Assembly.AcceptedV3.hint_bounds

/-- info: 'ZkFormal.NearV3.Assembly.nearAirV3_maxLog_le' depends on axioms: [propext] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Assembly.nearAirV3_maxLog_le

/-- info: 'ZkFormal.NearV3.Assembly.nearAirV3_degree_le' depends on axioms: [propext] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Assembly.nearAirV3_degree_le

/-- info: 'ZkFormal.NearV3.Assembly.bundle_headerOk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Assembly.bundle_headerOk

/-- info: 'ZkFormal.NearV3.Assembly.bundle_headerOk_rcpt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Assembly.bundle_headerOk_rcpt
