import ZkFormal.NearV3.Render.CodecTriePin
import ZkFormal.NearV3.Render.CodecSpost
import ZkFormal.NearV3.Render.CodecScmp
import ZkFormal.NearV3.Render.CodecCanon

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

/-- info: 'ZkFormal.NearV3.Assembly.RenderBundleV3.balancedAt_splen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Assembly.RenderBundleV3.balancedAt_splen

/-- info: 'ZkFormal.NearV3.Assembly.RcptTrieSide.rcpt_trie_sched' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Assembly.RcptTrieSide.rcpt_trie_sched

/-- info: 'ZkFormal.NearV3.Render.CdcGrant.value_stateBytes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Render.CdcGrant.value_stateBytes

/-- info: 'ZkFormal.NearV3.Assembly.RenderBundleV3.balancedAt_spost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Assembly.RenderBundleV3.balancedAt_spost

/-- info: 'ZkFormal.NearV3.Render.CdcGrant.prior_canonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Render.CdcGrant.prior_canonical

/-- info: 'ZkFormal.NearV3.Render.CdcGrant.a0s_accepted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Render.CdcGrant.a0s_accepted

/-- info: 'ZkFormal.NearV3.Render.CdcScmp.generated_reqs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Render.CdcScmp.generated_reqs

/-- info: 'ZkFormal.NearV3.Render.CdcScmp.codec_scmp_native' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs(whitespace := lax) in
#print axioms ZkFormal.NearV3.Render.CdcScmp.codec_scmp_native
