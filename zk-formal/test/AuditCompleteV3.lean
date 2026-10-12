import ZkFormal.NearV3.Render.CompleteV3

/-! Guard the completeness assembly (lane v3-render-sched, package 13): `CompleteV3Stmt` from `ChachaSideV3`. -/

/-- info: 'ZkFormal.NearV3.Assembly.accepted_render_balanced' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Assembly.accepted_render_balanced

/-- info: 'ZkFormal.NearV3.Assembly.completeV3_of_chacha' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Assembly.completeV3_of_chacha

/-- info: 'ZkFormal.NearV3.Assembly.nearV3_admission_of_chacha' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Assembly.nearV3_admission_of_chacha

/-- info: 'ZkFormal.NearV3.Assembly.RcptTrieSide.rcpt_trie_vbytes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Assembly.RcptTrieSide.rcpt_trie_vbytes

/-- info: 'ZkFormal.NearV3.Assembly.RcptTrieSide.rcpt_trie_sched' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Assembly.RcptTrieSide.rcpt_trie_sched
