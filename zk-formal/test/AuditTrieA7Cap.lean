import ZkFormal.NearV3.Assembly.TrieA7Cap

/-- info: 'ZkFormal.NearV3.Assembly.TrieA7Post.traceUpsert_unfolded' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Assembly.TrieA7Post.traceUpsert_unfolded
/-- info: 'ZkFormal.NearV3.Assembly.TrieA7Post.ups_post_bound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Assembly.TrieA7Post.ups_post_bound
/-- info: 'ZkFormal.NearV3.Assembly.TrieA7Cap.R_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Assembly.TrieA7Cap.R_eq
/-- info: 'ZkFormal.NearV3.Assembly.TrieA7Cap.rowCap_of_upsSha' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Assembly.TrieA7Cap.rowCap_of_upsSha

open NearSpec NearSpecV3 ZkFormal.NearV3.Render.UpsGen ZkFormal.NearV3.Assembly.TrieA7Post in
/-- behaviour guard: a concrete leaf upsert keeps `|v|` + its new part inside the post trie. -/
example : ∃ run, traceUpsert (.leaf [0,15] (.val [1,2,3]) 0) [0,15] [7,7] = some run ∧ PostOk run [7,7] :=
  ⟨_, rfl, traceUpsert_unfolded (.leaf [0,15] (.val [1,2,3]) 0) [0,15] [7,7] _ rfl (by decide) (by decide)⟩
