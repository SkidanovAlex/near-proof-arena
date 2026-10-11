import ZkFormal.NearV3.Render.BundleSched

/-! Guard the `ssdV3` (table 12, frozen `ScanDist.table`) completeness of lane v3-render-sched. -/

/-- info: 'ZkFormal.NearV3.Render.SsdShard.physical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Render.SsdShard.physical

/-- info: 'ZkFormal.NearV3.Render.Ssd.local_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Render.Ssd.local_at

/-- info: 'ZkFormal.NearV3.Render.Ssd.bits_of_constraints' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Render.Ssd.bits_of_constraints

/-- info: 'ZkFormal.NearV3.Render.Ssd.table_local' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Render.Ssd.table_local

/-- info: 'ZkFormal.NearV3.Render.Ssd.scan_block' depends on axioms: [propext, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Render.Ssd.scan_block

/-- info: 'ZkFormal.NearV3.Render.Ssd.dist_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Render.Ssd.dist_block

/-- info: 'ZkFormal.NearV3.Render.Ssd.ssd_descs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Render.Ssd.ssd_descs

/-- info: 'ZkFormal.NearV3.Render.Ssd.ssd_v3_aligned_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Render.Ssd.ssd_v3_aligned_complete

/-- info: 'ZkFormal.NearV3.Render.ssdRenderV3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Render.ssdRenderV3

/-- info: 'ZkFormal.NearV3.Render.ssdRender_accepted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Render.ssdRender_accepted
