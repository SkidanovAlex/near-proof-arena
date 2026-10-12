import ZkFormal.NearV3.Assembly.TrieAll
import ZkFormal.NearV3.Assembly.RenderV3RcptAccepted

/-!
# ZkFormal.NearV3.Assembly.TrieWalkAlign — the trie side's queue values are the receipt side's

The lookup walks `ws` of `trie_all_of` are `nativeQueryWalks … (allLookupQueries … v …)` for a
`v : MainValues` with `v.Valid ∧ v.Reads m.pre m.pre m.pre` (now exported).  `MainValues` is
determined by these two facts (`mainValues_unique`: the three reads are `find`s of `m.pre`, and the
buffered shard list is the deterministic parse `bufferedShards`), so for an accepted witness
`A : AcceptedV3`, run with `A`'s execution data, **`v = A.qvVals`** (`trie_v_eq_qvVals`): the
walk table and the queue-value table (22) are built from the same queue values.
-/

namespace ZkFormal.NearV3.Assembly.TrieWalkAlign

open NearSpec NearSpecV3 ZkFormal.Near ZkFormal.NearV3 Qv

theorem mainValues_unique {v v' : MainValues} {pre : PTrie} (hv : v.Valid) (hv' : v'.Valid)
    (hr : v.Reads pre pre pre) (hr' : v'.Reads pre pre pre) : v = v' := by
  obtain ⟨d, b, -, y⟩ := hr
  obtain ⟨d', b', -, y'⟩ := hr'
  have hd : v.delayed = v'.delayed := Option.some.inj (d.symm.trans d')
  have hb : v.buffered = v'.buffered := Option.some.inj (b.symm.trans b')
  have hy : v.yielded = v'.yielded := Option.some.inj (y.symm.trans y')
  have hs1 := (bufferedShards_iff _ _).mpr hv.2.1
  have hs2 := (bufferedShards_iff _ _).mpr hv'.2.1
  rw [hb] at hs1
  have hs : v.shards = v'.shards := Except.ok.inj (hs1.symm.trans hs2)
  cases v; cases v'
  simp only at hd hb hy hs
  subst hd hb hy hs
  rfl

/-- **The trie side's queue values are `A.qvVals`.** -/
theorem trie_v_eq_qvVals {cb wb : Bytes} (A : Assembly.AcceptedV3 cb wb) {v : MainValues}
    (hv : v.Valid) (hr : v.Reads A.m.pre A.m.pre A.m.pre) : v = A.qvVals :=
  mainValues_unique hv A.qvOk.valid hr (Classical.choose_spec A.qvOk_exists).2

end ZkFormal.NearV3.Assembly.TrieWalkAlign
