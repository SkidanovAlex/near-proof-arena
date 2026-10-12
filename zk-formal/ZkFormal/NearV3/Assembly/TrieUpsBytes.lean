import ZkFormal.NearV3.Assembly.TrieUpsSched
import ZkFormal.NearV3.Assembly.TrieA7Rank
import ZkFormal.NearV3.Assembly.TrieShaFamilies

/-!
# ZkFormal.NearV3.Assembly.TrieUpsBytes — the ups `BYTES` sends are the scheduler upsert jobs

**`ups_bytes_scheduler`**: for the instances of `trie_all_of` (`UpsSha insts`), the `BYTES` sends of
the aligned ups view of the RANKED instances (`view_bytes_send`: `Js.flatMap upsBytes`) are, as field
messages, the expected bytes of `schedulerShaJobs 0 us` — the scheduler family of
`scheduler_sha_of` (ids agree: `upsId = msgId K_VUPS (512 τ + j) = upsertJobId τ j`).
-/

namespace ZkFormal.NearV3.Assembly.TrieUpsBytes

open ZkFormal.Near ZkFormal.NearV3 ZkFormal.NearV3.Assembly Render Render.UpsGen Rcpt.Candidates
  Rcpt.Candidates.NodePostUpdate TrieUpsSched

theorem expectedBytes_append (a b : List Sha.Gen.Msg) :
    Sha.Gen.expectedBytes (a ++ b) = Sha.Gen.expectedBytes a ++ Sha.Gen.expectedBytes b := by
  simp [Sha.Gen.expectedBytes, List.flatMap_append]

theorem bytes_from : ∀ (us : List SchedulerUpsertWitness) (insts : List UpsInst) (t0 : Nat),
    insts.length = us.length →
    (∀ i u I, us[i]? = some u → insts[i]? = some I →
      NativeShaFamily u I ∧ I.v = u.value.map UInt8.toNat ∧ I.tau = t0 + i) →
    (insts.flatMap upsBytes).map Msg.toFp = (Sha.Gen.expectedBytes (schedulerShaJobs t0 us)).map Msg.toFp
  | [], [], _, _, _ => by simp [schedulerShaJobs, Sha.Gen.expectedBytes]
  | [], _ :: _, _, h, _ => by simp at h
  | _ :: _, [], _, h, _ => by simp at h
  | u :: us, I :: Is, t0, hl, h => by
    obtain ⟨hf, hv, ht⟩ := h 0 u I rfl rfl
    have ih := bytes_from us Is (t0 + 1) (by simpa using hl) (fun i u' I' hu hI => by
      obtain ⟨a, b, c⟩ := h (i + 1) u' I' (by simpa using hu) (by simpa using hI)
      exact ⟨a, b, by omega⟩)
    simp only [List.flatMap_cons, List.map_append, schedulerShaJobs, expectedBytes_append]
    rw [ih, ups_bytes_jobs u I hf hv, ht, Nat.add_zero]

/-- **The ups `BYTES` sends are the scheduler upsert SHA jobs' bytes.** -/
theorem ups_bytes_scheduler (ws : List WalkR) {insts : List UpsInst} (h : TrieUpsOrigin.UpsSha insts) :
    ∃ us : List SchedulerUpsertWitness,
      (Sha.Gen.honestRows (schedulerShaJobs 0 us ++ schedulerSanityJobs 0 us)).length ≤ 1663260 ∧
      ((TrieUpsNative.upsRanked ws insts).flatMap upsBytes).map Msg.toFp =
        (Sha.Gen.expectedBytes (schedulerShaJobs 0 us)).map Msg.toFp := by
  obtain ⟨us, hl, hrows, hfam⟩ := TrieShaFamilies.scheduler_sha_of h
  refine ⟨us, hrows, ?_⟩
  have hr : (TrieUpsNative.upsRanked ws insts).map upsBytes = insts.map upsBytes := by
    rw [TrieUpsNative.upsRanked]
    exact TrieA7.prefix_map_eq upsBytes (fun _ _ => rfl) insts _
  rw [List.flatMap_def, hr, ← List.flatMap_def]
  exact bytes_from us insts 0 hl (fun i u I hu hI => by
    obtain ⟨a, b, c⟩ := hfam i u I hu hI
    exact ⟨a, b, by omega⟩)

end ZkFormal.NearV3.Assembly.TrieUpsBytes
