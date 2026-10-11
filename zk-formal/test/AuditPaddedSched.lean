import ZkFormal.NearV3.Render.PaddedSched

/-! Guard the assumptions of the aligned scheduler generators (`nearAirV3` tables 14, 15). -/

/-- info: 'ZkFormal.NearV3.Render.cmp_aligned_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Render.cmp_aligned_complete

/-- info: 'ZkFormal.NearV3.Render.mem_aligned_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Render.mem_aligned_complete

