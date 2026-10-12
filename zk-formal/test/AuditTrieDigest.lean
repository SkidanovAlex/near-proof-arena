import ZkFormal.NearV3.Assembly.TrieDigestTrie

/-- info: 'ZkFormal.NearV3.Assembly.TrieDigestUps.view_digest_recv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Assembly.TrieDigestUps.view_digest_recv
/-- info: 'ZkFormal.NearV3.Assembly.TrieDigestUps.ups_sha_scheduler' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Assembly.TrieDigestUps.ups_sha_scheduler
/-- info: 'ZkFormal.NearV3.Assembly.TrieDigestTrie.node_head_digests' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Assembly.TrieDigestTrie.node_head_digests
/--
info: 'ZkFormal.NearV3.Assembly.TrieDigestTrie.RenderBundleV3.htrie_of' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ZkFormal.NearV3.Assembly.TrieDigestTrie.RenderBundleV3.htrie_of

open ZkFormal.NearV3.Assembly ZkFormal.NearV3.Assembly.TrieDigestUps in
/-- behaviour guard: a value row of the ups table receives no `DIGEST`. -/
example (I : ZkFormal.NearV3.Render.UpsInst) (p : Nat) :
    CompactPhysicalDigests.digestRowMsgs I (.v p) = [] := digest_value_row I p
