import ZkFormal.NearV3.Render.PaddedSha

/-! Guard the assumptions of the aligned SHA generator (`nearAirV3` tables 0, 1). -/

/-- info: 'ZkFormal.NearV3.Render.sha_aligned_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Render.sha_aligned_complete
