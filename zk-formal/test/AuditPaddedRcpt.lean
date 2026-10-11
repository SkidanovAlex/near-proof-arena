import ZkFormal.NearV3.Render.PaddedRcpt

/-! Guard the assumptions of the aligned receipt-side generators and cap-parametric views. -/

/-- info: 'ZkFormal.NearV3.acctV3_view_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.acctV3_view_at

/-- info: 'ZkFormal.NearV3.size_view_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.size_view_at

/-- info: 'ZkFormal.NearV3.Render.acct_aligned_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Render.acct_aligned_complete

/-- info: 'ZkFormal.NearV3.Render.acctV3Ok_wf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Render.acctV3Ok_wf

/-- info: 'ZkFormal.NearV3.Render.size_aligned_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Render.size_aligned_complete
