import ZkFormal.NearV3.Assembly.TrieA7Post
import ZkFormal.NearV3.Rcpt.Candidates.NativeReplayByteSize
import ZkFormal.NearV3.Rcpt.Candidates.NativeWriteOccurrences

/-!
# ZkFormal.NearV3.Assembly.TrieA7Forest — forest facts of the scheduler witnesses (for `UpsA7`)

**`ups_forest_facts`**: for an accepted chunk, the scheduler witnesses `us` with
`us.map (pre, run.output) = (oldPost, m.result.trie) :: steps.map (pre, post)` and the sized account replay
`SizedAccountRun m.pre writes oldPost`:

* the native pre forest `F = m.pre :: steps.pre` is well formed;
* `us.map pre` has, occurrence by occurrence, the node-encoding lengths and the value lengths of `F`
  (the account writes keep every encoding length: `write_node_length`, `SizedAccountRun.value_lengths`);
* `Σ_u (U(u.pre) + U(u.run.output)) ≤ 2,000,000` (`= unfoldBytes ≤ B0`, `SizedAccountRun.unfolded_bytes`).
-/

namespace ZkFormal.NearV3.Assembly.TrieA7Forest

open NearSpec NearSpecV3 ZkFormal.NearV3.Assembly Rcpt.Candidates Rcpt.Candidates.NodePostUpdate

theorem ups_forest_facts {cb wb : Bytes} {k : WalkD0} {w : StateWitness}
    (hk : walkD0 cb = .ok k) (hw : decodeW wb = .ok w) (hc : checkD0a B0 cb wb = .ok ())
    {m : MainExecutionV3} {steps : List ImplicitStepV3} {last : Bytes} (hm : m.NativeValid k w)
    (hv : ImplicitTraceValid k m.result.trie.hashOf (k.implicitBlks.zip w.implicit) steps last)
    {oldPost : PTrie} {writes : List (List Nat × Bytes)} (hr : SizedAccountRun m.pre writes oldPost)
    (us : List SchedulerUpsertWitness)
    (hpairs : us.map (fun u => (u.pre, u.run.output)) = (oldPost, m.result.trie) :: steps.map (fun s => (s.pre, s.post))) :
    (∀ t ∈ m.pre :: steps.map ImplicitStepV3.pre, t.wf = true) ∧
    ((us.map SchedulerUpsertWitness.pre).flatMap ZkFormal.NearV3.occs).map
        (fun o => (ZkFormal.NearV3.nodeEnc o).length) =
      ((m.pre :: steps.map ImplicitStepV3.pre).flatMap ZkFormal.NearV3.occs).map
        (fun o => (ZkFormal.NearV3.nodeEnc o).length) ∧
    (forestBytes (us.map SchedulerUpsertWitness.pre)).map List.length =
      (forestBytes (m.pre :: steps.map ImplicitStepV3.pre)).map List.length ∧
    (us.map (fun u => NearSpecV3.unfoldedBytesT u.pre + NearSpecV3.unfoldedBytesT u.run.output)).sum ≤ 2000000 := by
  have hpre : us.map SchedulerUpsertWitness.pre = oldPost :: steps.map ImplicitStepV3.pre := by
    have := congrArg (List.map Prod.fst) hpairs
    simpa [List.map_map, Function.comp_def] using this
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t ht
    rcases List.mem_cons.mp ht with rfl | ht
    · rw [hm.pre]; exact (built_spec _ trieFuel _ _ hm.root_length).2.1
    · obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
      exact (hv.input_facts s hs).2.2
  · rw [hpre]
    simp only [List.flatMap_cons, List.map_append]
    rw [(paired_occurrences hr.forget.skeleton).node_lengths]
  · rw [hpre]
    simp only [forestBytes, List.flatMap_cons, List.map_append]
    rw [hr.value_lengths]
  · have hrr := triesD0_native_result hk hw hm hv
    have hh := (relD0a_iff B0 cb wb).mpr hc
    have hb : unfoldBytes cb wb ≤ B0 := by simpa only [a7, decide_eq_true_eq] using hh.2.2.2.2.1
    simp only [unfoldBytes, hrr] at hb
    have h2 : (us.map (fun u => NearSpecV3.unfoldedBytesT u.pre + NearSpecV3.unfoldedBytesT u.run.output)).sum =
        ((us.map (fun u => (u.pre, u.run.output))).map (fun p => NearSpecV3.unfoldedBytesT p.1 +
          NearSpecV3.unfoldedBytesT p.2)).sum := by
      simp [List.map_map, Function.comp_def]
    rw [hpairs] at h2
    have hU := NodePostUpdate.SizedAccountRun.unfolded_bytes hr
    simp only [List.map_cons, List.sum_cons] at h2
    simp only [unfoldedPairs, List.map_cons, List.sum_cons, List.map_map, Function.comp_def] at hb
    unfold B0 at hb
    simp only [List.map_map, Function.comp_def] at h2
    omega

end ZkFormal.NearV3.Assembly.TrieA7Forest
