import ZkFormal.NearV3.Render.SchedScmp

/-! Guard the SCMP reduction (lane v3-render-sched). -/

/-- info: 'ZkFormal.NearV3.Render.scmp_balance_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Render.scmp_balance_core
