import ZkFormal.NearV3.Assembly.TrieShaTwo
import ZkFormal.NearV3.Assembly.TrieAll
import ZkFormal.NearV3.Candidates.NativePostShaBudget
import ZkFormal.NearV3.Rcpt.Candidates.NativeShaTraffic
import ZkFormal.NearV3.Assembly.ShaOwnedBatch

/-!
# ZkFormal.NearV3.Assembly.TrieShaFamilies — the trie-side SHA job families for the choice of
`trie_all_of`

* **`native_sha_of`**: for the honest records `ns = TrieNative.nodes m steps oldPost writes q`,
  `es = TrieNative.vals m steps` (any `oldPost`/`writes`, in particular those of `trie_all_of`):
  the native family `jobsToSha (nativeShaJobs ns es)` fits `2,925,275` SHA rows and its job bytes
  are exactly the node and value tables' `BYTES` sends.
* **`scheduler_sha_of`**: `UpsSha insts` (exported by `trie_all_of`) gives the scheduler upsert
  witnesses `us` of the SAME instances, whose upsert + sanity SHA family fits `1,663,260` rows
  (`schedulerBatch_rows`), with `NativeShaFamily u I` per instance (part `k`'s bytes are job
  `k + 1` of `upsertShaJobs I.tau u.value u.run`).
-/

namespace ZkFormal.NearV3.Assembly.TrieShaFamilies

open NearSpec NearSpecV3 ZkFormal.Near ZkFormal.Air ZkFormal.Algebra Render Render.UpsGen Rcpt.Candidates
  Rcpt.Candidates.NodePostUpdate ZkFormal.NearV3.Candidates

theorem native_sha_of {cb wb : Bytes} {k : WalkD0} {w : StateWitness}
    (hk : walkD0 cb = .ok k) (hw : decodeW wb = .ok w) (hc : checkD0a B0 cb wb = .ok ())
    {m : MainExecutionV3} {steps : List ImplicitStepV3} {last : Bytes} (hm : m.NativeValid k w)
    (hv : ImplicitTraceValid k m.result.trie.hashOf (k.implicitBlks.zip w.implicit) steps last)
    (oldPost : PTrie) (writes : List (List Nat × Bytes)) (q : UseRequests)
    (he : q.edges.length < Algebra.P) (hb : q.bmaps.length < Algebra.P) (hu : q.windows.length < Algebra.P)
    (hval : ValWf (TrieNative.vals m steps)) :
    (Sha.Gen.honestRows (jobsToSha (nativeShaJobs (TrieNative.nodes m steps oldPost writes q)
        (TrieNative.vals m steps)))).length ≤ 2925275 ∧
      jobBytes (nativeShaJobs (TrieNative.nodes m steps oldPost writes q) (TrieNative.vals m steps)) =
        nodeSends3 (TrieNative.nodes m steps oldPost writes q) B_BYTES ++
          valSends (TrieNative.vals m steps) B_BYTES := by
  refine ⟨?_, nativeJobs_bytes _ _ hval⟩
  rw [jobsToSha_rows]
  have h := NativePostShaBudget.accepted hk hw hc hm hv
    (forestOldInputs (nativeReplayForest m steps oldPost writes)) q he hb hu
  simpa only [TrieNative.nodes, TrieNative.vals, TrieNative.chain, TrieNative.seedNodes, TrieNative.seedVals,
    TrieNative.forest] using h

theorem scheduler_sha_of {insts : List UpsInst} (h : TrieUpsOrigin.UpsSha insts) :
    ∃ us : List SchedulerUpsertWitness, insts.length = us.length ∧
      (Sha.Gen.honestRows (schedulerShaJobs 0 us ++ schedulerSanityJobs 0 us)).length ≤ 1663260 ∧
      ∀ tau u I, us[tau]? = some u → insts[tau]? = some I →
        NativeShaFamily u I ∧ I.v = u.value.map UInt8.toNat ∧ I.tau = tau := by
  obtain ⟨us, hl, h32, hg, hout, hval, -, hI⟩ := h
  exact ⟨us, hl, schedulerBatch_rows us h32 (fun u hu => (hg u hu).1) (fun u hu => (hg u hu).2.1) hout hval,
    fun tau u I hu hI' => ⟨(hI tau u I hu hI').1, (hI tau u I hu hI').2.1, (hI tau u I hu hI').2.2.1⟩⟩

end ZkFormal.NearV3.Assembly.TrieShaFamilies
