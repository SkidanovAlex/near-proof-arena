import ZkFormal.NearV3.Render.HonestBalanceRcpt

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
