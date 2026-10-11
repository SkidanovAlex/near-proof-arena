import ZkFormal.NearV3.Render.HonestBalanceMem

/-! Guard the honest receipt-side bus balances. -/

/-- info: 'ZkFormal.NearV3.Render.qvNative_qvc_balance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Render.qvNative_qvc_balance

/-- info: 'ZkFormal.NearV3.Render.qvNative_qsh_balance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Render.qvNative_qsh_balance

/-- info: 'ZkFormal.NearV3.Render.honest_size_balance' depends on axioms: [propext] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Render.honest_size_balance

/-- info: 'ZkFormal.NearV3.Assembly.RcptSkeleton.honest_rids_balance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Assembly.RcptSkeleton.honest_rids_balance

/-- info: 'ZkFormal.NearV3.Render.honest_rcl_balance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Render.honest_rcl_balance

/-- info: 'ZkFormal.NearV3.Render.honest_src_balance' depends on axioms: [propext, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Render.honest_src_balance

/-- info: 'ZkFormal.NearV3.Assembly.RcptSkeleton.honest_srec_balance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Assembly.RcptSkeleton.honest_srec_balance

/-- info: 'ZkFormal.NearV3.Assembly.RcptSkeleton.honest_mem_balance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Assembly.RcptSkeleton.honest_mem_balance
