import ZkFormal.NearV3.Render.PaddedQv

/-! Guard the assumptions of the aligned queue-value generator. -/

/-- info: 'ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen.mixedTrace_repaired_traffic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen.mixedTrace_repaired_traffic

/-- info: 'ZkFormal.NearV3.Render.qv_aligned_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Render.qv_aligned_complete
