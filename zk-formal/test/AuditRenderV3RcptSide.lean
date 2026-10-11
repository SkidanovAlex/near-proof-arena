import ZkFormal.NearV3.Assembly.RenderV3RcptSide

/-! Guard the assumptions of BND coverage and the collected receipt side. -/

/-- info: 'ZkFormal.NearV3.Assembly.RcptSkeleton.native_boundary_rows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Assembly.RcptSkeleton.native_boundary_rows

/-- info: 'ZkFormal.NearV3.Assembly.RcptSkeleton.native_boundary_key' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Assembly.RcptSkeleton.native_boundary_key

/-- info: 'ZkFormal.NearV3.Assembly.AcceptedV3.bnd_coverage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Assembly.AcceptedV3.bnd_coverage

/-- info: 'ZkFormal.NearV3.Assembly.RcptBal.bnd_balanced_accepted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Assembly.RcptBal.bnd_balanced_accepted

/-- info: 'ZkFormal.NearV3.Assembly.rcpt_side_balanced' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Assembly.rcpt_side_balanced

/-- info: 'ZkFormal.NearV3.Assembly.rcpt_side_of_accept' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Assembly.rcpt_side_of_accept

/-- info: 'ZkFormal.NearV3.Assembly.AcceptedV3.rcptRenders' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Assembly.AcceptedV3.rcptRenders
