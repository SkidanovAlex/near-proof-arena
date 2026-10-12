import ZkFormal.NearV3.Render.SchedAccepted

/-! Guard tables 12–15 from acceptance (lane v3-render-sched). -/

/-- info: 'ZkFormal.NearV3.Render.memAllRenderV3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Render.memAllRenderV3

/-- info: 'ZkFormal.NearV3.Render.old_requests_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Render.old_requests_ok

/-- info: 'ZkFormal.NearV3.Render.sched_renders_accepted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Render.sched_renders_accepted
