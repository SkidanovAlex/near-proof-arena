import ZkFormal.NearV3.Assembly.RenderV3RcptTrieSide

/-! Guard the receipt SHA family / BYTES-DIGEST receipt halves and the combined receipt+trie side. -/

/-- info: 'ZkFormal.NearV3.Render.outcome_traffic_v3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Render.outcome_traffic_v3

/-- info: 'ZkFormal.NearV3.Assembly.AcceptedV3.accountJobs_bytes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Assembly.AcceptedV3.accountJobs_bytes

/-- info: 'ZkFormal.NearV3.Assembly.AcceptedV3.receipt_sha' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Assembly.AcceptedV3.receipt_sha

/-- info: 'ZkFormal.NearV3.Assembly.AcceptedV3.account_digests' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Assembly.AcceptedV3.account_digests

/-- info: 'ZkFormal.NearV3.Assembly.RcptTrieSide.rcpt_trie_side' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Assembly.RcptTrieSide.rcpt_trie_side
