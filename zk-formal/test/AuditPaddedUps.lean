import ZkFormal.NearV3.Render.PaddedUps

/-! Guard the assumptions of the aligned `upsV3` generator (`nearAirV3` table 7). -/

/-- info: 'ZkFormal.NearV3.Render.ups_aligned_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Render.ups_aligned_complete

/-- info: 'ZkFormal.NearV3.Render.ups_groupOk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Render.ups_groupOk

/-- info: 'ZkFormal.NearV3.Render.ups_render_local_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Render.ups_render_local_at

/-- info: 'ZkFormal.NearV3.Render.ups_render_traffic_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Render.ups_render_traffic_at

