import ZkFormal.NearV3.Render.CodecTriePin

/-! Guard the scheduler-upsert pin and the codec premises of `rcpt_trie_side` (lane v3-render-sched). -/

/-- info: 'ZkFormal.NearV3.Assembly.RcptTrieSide.rcpt_trie_side' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Assembly.RcptTrieSide.rcpt_trie_side

/-- info: 'ZkFormal.NearV3.Render.CdcGrant.codec_premises' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Render.CdcGrant.codec_premises

/-- info: 'ZkFormal.NearV3.Assembly.RcptTrieSide.rcpt_trie_codec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Assembly.RcptTrieSide.rcpt_trie_codec
