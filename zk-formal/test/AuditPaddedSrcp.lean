import ZkFormal.NearV3.Render.PaddedSrcp

/-! Guard the assumptions of the aligned source-proof generator and the A10 view. -/

/-- info: 'ZkFormal.NearV3.Render.srcp_aligned_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Render.srcp_aligned_complete

/-- info: 'ZkFormal.NearV3.Render.srcp_proofs_aligned_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Render.srcp_proofs_aligned_complete

/-- info: 'ZkFormal.NearV3.srcpD_view' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.srcpD_view
