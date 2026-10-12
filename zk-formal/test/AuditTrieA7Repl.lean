import ZkFormal.NearV3.Assembly.TrieA7Repl

/-- info: 'ZkFormal.NearV3.Assembly.TrieA7Repl.traceUpsert_replaced' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ZkFormal.NearV3.Assembly.TrieA7Repl.traceUpsert_replaced

open NearSpec NearSpecV3 ZkFormal.NearV3.Render.UpsGen ZkFormal.NearV3.Assembly.TrieA7Repl in
/-- behaviour guard: an exact leaf overwrite replaces the leaf and its old value. -/
example : ∃ run, traceUpsert (.leaf [0,15] (.val [1,2,3]) 0) [0,15] [7,7] = some run ∧
    ReplOk (.leaf [0,15] (.val [1,2,3]) 0) run [7,7] ∧ oldValCharge run = 3 :=
  ⟨_, rfl, traceUpsert_replaced (.leaf [0,15] (.val [1,2,3]) 0) [0,15] [7,7] _ rfl (by decide) (by decide), by decide⟩
