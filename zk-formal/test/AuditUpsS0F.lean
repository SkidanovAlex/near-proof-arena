import ZkFormal.NearV3.Render.CodecSpost

/-! Guard the ups S0F completeness (lane v3-render-sched). -/

/-- info: 'ZkFormal.NearV3.Assembly.UpsS0F.trace_val_addr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Assembly.UpsS0F.trace_val_addr

/-- info: 'ZkFormal.NearV3.Assembly.UpsS0F.s0f_vid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Assembly.UpsS0F.s0f_vid

/-- info: 'ZkFormal.NearV3.Assembly.UpsS0F.s0fOf_native' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Assembly.UpsS0F.s0fOf_native

/-- info: 'ZkFormal.NearV3.Assembly.UpsS0F.s0f_rebase' depends on axioms: [propext, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Assembly.UpsS0F.s0f_rebase

/-- info: 'ZkFormal.NearV3.Assembly.TrieDigestUps.ups_sha_scheduler_pin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Assembly.TrieDigestUps.ups_sha_scheduler_pin

/-- info: 'ZkFormal.NearV3.Assembly.TrieSide.trie_side_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Assembly.TrieSide.trie_side_exact

/-- info: 'ZkFormal.NearV3.Assembly.RenderBundleV3.balancedAt_s0f' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Assembly.RenderBundleV3.balancedAt_s0f

/-- info: 'ZkFormal.NearV3.Assembly.RcptTrieSide.rcpt_trie_sched' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Assembly.RcptTrieSide.rcpt_trie_sched
