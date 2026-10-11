import ZkFormal.NearV3.Render.PaddedRcptR

/-! Guard the honest repaired receipt-table generator. -/

/-- info: 'ZkFormal.NearV3.Assembly.RcptSkeleton.rcpt_aligned_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Assembly.RcptSkeleton.rcpt_aligned_complete

/-- info: 'ZkFormal.NearV3.Render.tableTraffic_pin' depends on axioms: [propext, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Render.tableTraffic_pin
