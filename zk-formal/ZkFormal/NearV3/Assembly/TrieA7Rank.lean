import ZkFormal.NearV3.Assembly.TrieA7Ups
import ZkFormal.NearV3.Assembly.TrieUpsNative

/-!
# ZkFormal.NearV3.Assembly.TrieA7Rank — the A7 ups messages do not depend on the counter ranking

`upsRanked ws insts` (= `physicalPrefixUps`) only rewrites each instance's walk counters, so
the A7 `RPL`/`RPLV` messages and the A7 ups total of the rendered instances are those of the
native instances: `rpl_ranked`, `rplv_ranked`, `total_ranked`.
-/

namespace ZkFormal.NearV3.Assembly.TrieA7

open ZkFormal.Near ZkFormal.NearV3.Render ZkFormal.NearV3.Render.UpsGen
  ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate

theorem step_sync_rank (p : List WStep3) (I : UpsInst) (t : Nat) :
    (step (syncUps (rankUps p I)) t).mode = (step I t).mode ∧
      (step (syncUps (rankUps p I)) t).e = (step I t).e := by
  refine ⟨?_, ?_⟩
  · rw [(syncUps_semantics _ t).1, rankUps_mode]
  · rw [(syncUps_semantics _ t).2.2.1, rankUps_edge]

theorem rplMsgs_sync_rank (p : List WStep3) (I : UpsInst) :
    upsRplMsgs (syncUps (rankUps p I)) = upsRplMsgs I := rfl

theorem rplvMsgs_sync_rank (p : List WStep3) (I : UpsInst) :
    upsRplvMsgs (syncUps (rankUps p I)) = upsRplvMsgs I := by
  simp only [upsRplvMsgs, (step_sync_rank p I 3).1, (step_sync_rank p I 3).2]

theorem prefix_map_eq {β : Type} (f : UpsInst → β) (hf : ∀ p I, f (syncUps (rankUps p I)) = f I) :
    ∀ (Is : List UpsInst) (p : List WStep3), (physicalPrefixUps p Is).map f = Is.map f
  | [], _ => rfl
  | I :: Is, p => by
    simp only [physicalPrefixUps, rankUpsList, List.map_cons] at *
    rw [hf p I]
    exact congrArg (List.cons (f I)) (prefix_map_eq f hf Is (p ++ fourSteps I))

theorem rpl_ranked (ws : List WalkR) (insts : List UpsInst) :
    (TrieUpsNative.upsRanked ws insts).flatMap upsRplMsgs = insts.flatMap upsRplMsgs := by
  rw [List.flatMap_def, List.flatMap_def, TrieUpsNative.upsRanked,
    prefix_map_eq upsRplMsgs rplMsgs_sync_rank]

theorem rplv_ranked (ws : List WalkR) (insts : List UpsInst) :
    (TrieUpsNative.upsRanked ws insts).flatMap upsRplvMsgs = insts.flatMap upsRplvMsgs := by
  rw [List.flatMap_def, List.flatMap_def, TrieUpsNative.upsRanked,
    prefix_map_eq upsRplvMsgs rplvMsgs_sync_rank]

theorem total_ranked (ws : List WalkR) (insts : List UpsInst) :
    upsA7Total (TrieUpsNative.upsRanked ws insts) = upsA7Total insts := by
  unfold upsA7Total
  rw [TrieUpsNative.upsRanked,
    prefix_map_eq (fun I => L I + ((List.range (nQ I)).map fun k => (part I k).q.length).sum) (fun _ _ => rfl)]

end ZkFormal.NearV3.Assembly.TrieA7
