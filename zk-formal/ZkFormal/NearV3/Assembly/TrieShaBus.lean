import ZkFormal.NearV3.Assembly.TrieUpsBytes
import ZkFormal.NearV3.Assembly.ShaBinRender
import ZkFormal.NearV3.Candidates.NativePostShaOk
import ZkFormal.NearV3.Assembly.SourceSchedulerShaOk

/-!
# ZkFormal.NearV3.Assembly.TrieShaBus — the bundle `BYTES` balance (trie side + interfaces)

`BYTES`: node 2, val 4, ups 7, codec 11, rcpt 16, acct 17, srcp 20, mrk 23 send; sha 0, 1 and the
public statement receive.  With the SHA bins `b0`, `b1` of the four families (`two_sha_renders`:
scheduler `= schedulerShaJobs 0 us ++ schedulerSanityJobs 0 us`, native
`= jobsToSha (nativeShaJobs ns es)`, receipt, source):

* `jobBytes_expected`: `expectedBytes (jobsToSha J) = jobBytes J`;
* **`RenderBundleV3.balancedAt_bytes`**: `R.BalancedAt B_BYTES` from the trie-side identities
  (node + val sends `= jobBytes (nativeShaJobs ns es)`, `TrieShaFamilies.native_sha_of`; ups sends
  `= expectedBytes (schedulerShaJobs 0 us)`, `TrieUpsBytes.ups_bytes_scheduler`) and the two
  other lanes' identities, stated as counts: codec sends = the sanity jobs' bytes (scheduler lane),
  rcpt + acct + srcp + mrk sends = the receipt and source families' bytes plus the public `BYTES`
  receives (receipt lane).

`balancedAt_bytes` / `balancedAt_digest` take the native family as a parameter `N` (the honest choice
is `TrieShaEmpty.nativeShaJobsE ns es`, which includes the empty-value jobs that the node records'
`VPRE` slot lookups need; `N = nativeShaJobs ns es` is the earlier instance).
-/

namespace ZkFormal.NearV3.Assembly.TrieShaBus

open NearSpec NearSpecV3 ZkFormal.Near ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3 ZkFormal.NearV3.Assembly
  Render Render.UpsGen Rcpt.Candidates Rcpt.Candidates.NodePostUpdate TrieUpsSched

theorem jobBytes_expected (J : List Render.Msg) : Sha.Gen.expectedBytes (jobsToSha J) = jobBytes J := by
  simp [Sha.Gen.expectedBytes, jobsToSha, jobBytes, emitAt, List.flatMap_map]

theorem covers_bytes_send : Covers B_BYTES true
    (fun t => t == 2 || t == 4 || t == 7 || t == 11 || t == 16 || t == 17 || t == 20 || t == 23) = true := by
  decide +kernel
theorem covers_bytes_recv : Covers B_BYTES false (fun t => t == 0 || t == 1) = true := by
  decide +kernel
theorem pub_bytes_send (pub m : List Fp) : ZkFormal.V2.pubCount nearAirV3 pub B_BYTES true m = 0 :=
  pub_off _ _ (by decide +kernel) pub m

theorem cnt_append (a b : List ZkFormal.Near.Msg) (m : List Fp) : cnt (a ++ b) m = cnt a m + cnt b m := by
  simp [cnt, List.count_append]

/-- **The two SHA renders for the trie families** (glue for `balancedAt_bytes`): for the native
node/value family of `TrieNative.nodes/vals` (any field-bounded `q`) and the scheduler family of
`us` (rows `≤ 1,663,260`, as `TrieUpsBytes.ups_bytes_scheduler` gives), and the receipt/source
families with their bounds (receipt lane), the two SHA components exist with the bytes/digest
permutations, and node + val `BYTES` sends are the native family's bytes. -/
theorem sha_bins_of {cb wb : Bytes} {k : WalkD0} {w : StateWitness}
    (hk : walkD0 cb = .ok k) (hw : decodeW wb = .ok w) (hc : checkD0a B0 cb wb = .ok ())
    {m : MainExecutionV3} {steps : List ImplicitStepV3} {last : Bytes} (hm : m.NativeValid k w)
    (hv : ImplicitTraceValid k m.result.trie.hashOf (k.implicitBlks.zip w.implicit) steps last)
    (oldPost : PTrie) (writes : List (List Nat × Bytes)) (q : UseRequests)
    (he : q.edges.length < Algebra.P) (hb : q.bmaps.length < Algebra.P) (hu : q.windows.length < Algebra.P)
    (hval : ValWf (TrieNative.vals m steps))
    (us : List SchedulerUpsertWitness)
    (hs : (Sha.Gen.honestRows (schedulerShaJobs 0 us ++ schedulerSanityJobs 0 us)).length ≤ 1663260)
    (receipt source : List Sha.Gen.Msg)
    (hr : (Sha.Gen.honestRows receipt).length ≤ 1373299)
    (hp : (Sha.Gen.honestRows source).length ≤ 2257792)
    (hsm : ∀ M ∈ source, (Sha.Gen.msgRows M).length ≤ 35)
    (hbr : ∀ M ∈ receipt, ∀ x ∈ M.bytes, x < 256) (hbs : ∀ M ∈ source, ∀ x ∈ M.bytes, x < 256)
    (pub : List Fp) :
    let ns := TrieNative.nodes m steps oldPost writes q
    let es := TrieNative.vals m steps
    let all := (schedulerShaJobs 0 us ++ schedulerSanityJobs 0 us) ++ jobsToSha (nativeShaJobs ns es) ++
      receipt ++ source
    ∃ (b0 b1 : List Sha.Gen.Msg) (h0 : Sha.MsgsOk b0) (h1 : Sha.MsgsOk b1),
      (shaRenderV3 pub 0 (by decide) b0 h0).tf = shaBinTraffic b0 ∧
      (shaRenderV3 pub 1 (by decide) b1 h1).tf = shaBinTraffic b1 ∧
      (Sha.Gen.expectedBytes b0 ++ Sha.Gen.expectedBytes b1).Perm (Sha.Gen.expectedBytes all) ∧
      (Sha.Gen.expectedDigests b0 ++ Sha.Gen.expectedDigests b1).Perm (Sha.Gen.expectedDigests all) ∧
      jobBytes (nativeShaJobs ns es) = nodeSends3 ns B_BYTES ++ valSends es B_BYTES := by
  intro ns es all
  obtain ⟨hrows, hnat⟩ := TrieShaFamilies.native_sha_of hk hw hc hm hv oldPost writes q he hb hu hval
  have hnok : ZkFormal.Sha.MsgsOk (jobsToSha (nativeShaJobs ns es)) := by
    have h := Candidates.NativePostShaOk.accepted hk hw hc hm hv
      (forestOldInputs (nativeReplayForest m steps oldPost writes)) q he hb hu
    simpa only [ns, es, TrieNative.nodes, TrieNative.vals, TrieNative.chain, TrieNative.seedNodes,
      TrieNative.seedVals, TrieNative.forest] using h
  have hall : ∀ M ∈ (schedulerShaJobs 0 us ++ schedulerSanityJobs 0 us) ++ jobsToSha (nativeShaJobs ns es) ++
      receipt ++ source, ∀ x ∈ M.bytes, x < 256 := by
    intro M hM x hx
    simp only [List.mem_append] at hM
    rcases hM with (((hM | hM) | hM) | hM) | hM
    · exact schedulerShaJobs_bytes 0 us M hM x hx
    · exact schedulerSanityJobs_bytes 0 us M hM x hx
    · exact hnok.bytes M hM x hx
    · exact hbr M hM x hx
    · exact hbs M hM x hx
  obtain ⟨b0, b1, h0, h1, -, t0, t1, pb, pd⟩ := TrieShaTwo.two_sha_renders pub _ _ receipt source hs hrows hr hp hsm hall
  exact ⟨b0, b1, h0, h1, t0, t1, pb, pd, hnat⟩

theorem expectedDigests_append (a b : List Sha.Gen.Msg) :
    Sha.Gen.expectedDigests (a ++ b) = Sha.Gen.expectedDigests a ++ Sha.Gen.expectedDigests b := by
  simp [Sha.Gen.expectedDigests, List.filter_append]

theorem covers_digest_send : Covers B_DIGEST true (fun t => t == 0 || t == 1) = true := by
  decide +kernel
theorem covers_digest_recv : Covers B_DIGEST false
    (fun t => t == 2 || t == 3 || t == 7 || t == 11 || t == 16 || t == 20 || t == 23) = true := by
  decide +kernel
theorem pub_digest (s : Bool) (pub m : List Fp) : ZkFormal.V2.pubCount nearAirV3 pub B_DIGEST s m = 0 :=
  pub_off _ _ (by cases s <;> decide +kernel) pub m

namespace RenderBundleV3

variable {pub : List Fp} (R : RenderBundleV3 pub)

/-- **`BYTES` balance of a bundle** from the four SHA families. -/
theorem balancedAt_bytes (ns : List NodeS3) (es : List ValE) (N : List Render.Msg) (Js : List UpsInst) (hok : UpsRenderOk Js)
    (us : List SchedulerUpsertWitness) (receipt source b0 b1 : List Sha.Gen.Msg)
    (h0 : (R ⟨0, by decide⟩).tf = shaBinTraffic b0) (h1 : (R ⟨1, by decide⟩).tf = shaBinTraffic b1)
    (hperm : (Sha.Gen.expectedBytes b0 ++ Sha.Gen.expectedBytes b1).Perm
      (Sha.Gen.expectedBytes ((schedulerShaJobs 0 us ++ schedulerSanityJobs 0 us) ++
        jobsToSha N ++ receipt ++ source)))
    (hn : ExtOf (R ⟨T_NODE, by decide⟩).tf (nodeTraffic3 ns))
    (hv : ExtOf (R ⟨T_VAL, by decide⟩).tf (valTraffic es))
    (hu : ExtOf (R ⟨T_UPS, by decide⟩).tf (upsTraffic (UpsRows.viewOf (upsTraceAligned Js) T_UPS (UpsGen.segsOf Js))))
    (hnat : jobBytes N = nodeSends3 ns B_BYTES ++ valSends es B_BYTES)
    (hups : (Js.flatMap upsBytes).map Msg.toFp = (Sha.Gen.expectedBytes (schedulerShaJobs 0 us)).map Msg.toFp)
    (hcodec : ∀ m, cnt ((R.tf 11).sends B_BYTES) m = cnt (Sha.Gen.expectedBytes (schedulerSanityJobs 0 us)) m)
    (hrest : ∀ m, cnt ((R.tf 16).sends B_BYTES) m + cnt ((R.tf 17).sends B_BYTES) m +
        cnt ((R.tf 20).sends B_BYTES) m + cnt ((R.tf 23).sends B_BYTES) m =
      cnt (Sha.Gen.expectedBytes (receipt ++ source)) m + ZkFormal.V2.pubCount nearAirV3 pub B_BYTES false m) :
    R.BalancedAt B_BYTES := by
  intro m
  rw [R.sum_tables true _ m _ covers_bytes_send, R.sum_tables false _ m _ covers_bytes_recv, pub_bytes_send]
  have e2 := R.tf_ext 2 (by decide) hn B_BYTES (by decide) (by decide) (by decide)
  have e4 := R.tf_ext 4 (by decide) hv B_BYTES (by decide) (by decide) (by decide)
  have e7 := R.tf_ext 7 (by decide) hu B_BYTES (by decide) (by decide) (by decide)
  have e0 : R.tf 0 = shaBinTraffic b0 := by rw [← h0]; rfl
  have e1 : R.tf 1 = shaBinTraffic b1 := by rw [← h1]; rfl
  have hfs : (List.range 25).filter
      (fun t => t == 2 || t == 4 || t == 7 || t == 11 || t == 16 || t == 17 || t == 20 || t == 23) =
      [2, 4, 7, 11, 16, 17, 20, 23] := by decide
  have hfr : (List.range 25).filter (fun t => t == 0 || t == 1) = [0, 1] := by decide
  rw [hfs, hfr]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, sel, ite_true, Bool.false_eq_true,
    ite_false, e2.1, e4.1, e7.1, e0, e1, shaBinTraffic, upsTraffic, view_bytes_send Js hok]
  have hp' : cnt (Sha.Gen.expectedBytes b0) m + cnt (Sha.Gen.expectedBytes b1) m =
      cnt (Sha.Gen.expectedBytes ((schedulerShaJobs 0 us ++ schedulerSanityJobs 0 us) ++
        jobsToSha N ++ receipt ++ source)) m := by
    rw [← cnt_append]; exact (hperm.map Msg.toFp).count_eq m
  simp only [TrieUpsBytes.expectedBytes_append, cnt_append, jobBytes_expected, hnat] at hp'
  have hu' : cnt (Js.flatMap upsBytes) m = cnt (Sha.Gen.expectedBytes (schedulerShaJobs 0 us)) m := by
    simp only [cnt, hups]
  have hc := hcodec m
  have hr := hrest m
  simp only [TrieUpsBytes.expectedBytes_append, cnt_append] at hr
  simp only [nodeTraffic3, valTraffic] at *
  omega

/-- **`DIGEST` balance of a bundle** from the four SHA families: the SHA bins send the digests of
the `dmult` jobs; the receivers split by lane, with a cross term `X` (digests received on the trie
side whose SHA jobs belong to the receipt family — e.g. the written-value `VPOST` slot digests of
the node records, `ns.flatMap postSlotDigests`, whose jobs are the account jobs
`accountShaJobs as`, see `TrieShared.vslot_accepted`):
* `htrie` (trie side, OPEN): node 2 + head 3 + ups 7 receive the digests of the scheduler upsert
  jobs and the native node/value jobs, plus `X`;
* `hcodec` (scheduler lane): codec 11 receives the digests of the sanity jobs;
* `hrest` (receipt lane): rcpt 16 + srcp 20 + mrk 23 receive, together with `X`, the digests of the
  receipt and source families.  No public `DIGEST` messages. -/
theorem balancedAt_digest (N : List Render.Msg) (us : List SchedulerUpsertWitness)
    (receipt source b0 b1 : List Sha.Gen.Msg) (X : List ZkFormal.Near.Msg)
    (h0 : (R ⟨0, by decide⟩).tf = shaBinTraffic b0) (h1 : (R ⟨1, by decide⟩).tf = shaBinTraffic b1)
    (hperm : (Sha.Gen.expectedDigests b0 ++ Sha.Gen.expectedDigests b1).Perm
      (Sha.Gen.expectedDigests ((schedulerShaJobs 0 us ++ schedulerSanityJobs 0 us) ++
        jobsToSha N ++ receipt ++ source)))
    (htrie : ∀ m, cnt ((R.tf 2).recvs B_DIGEST) m + cnt ((R.tf 3).recvs B_DIGEST) m +
        cnt ((R.tf 7).recvs B_DIGEST) m =
      cnt (Sha.Gen.expectedDigests (schedulerShaJobs 0 us ++ jobsToSha N)) m + cnt X m)
    (hcodec : ∀ m, cnt ((R.tf 11).recvs B_DIGEST) m = cnt (Sha.Gen.expectedDigests (schedulerSanityJobs 0 us)) m)
    (hrest : ∀ m, cnt ((R.tf 16).recvs B_DIGEST) m + cnt ((R.tf 20).recvs B_DIGEST) m +
        cnt ((R.tf 23).recvs B_DIGEST) m + cnt X m = cnt (Sha.Gen.expectedDigests (receipt ++ source)) m) :
    R.BalancedAt B_DIGEST := by
  intro m
  rw [R.sum_tables true _ m _ covers_digest_send, R.sum_tables false _ m _ covers_digest_recv,
    pub_digest, pub_digest]
  have e0 : R.tf 0 = shaBinTraffic b0 := by rw [← h0]; rfl
  have e1 : R.tf 1 = shaBinTraffic b1 := by rw [← h1]; rfl
  have hfs : (List.range 25).filter (fun t => t == 0 || t == 1) = [0, 1] := by decide
  have hfr : (List.range 25).filter
      (fun t => t == 2 || t == 3 || t == 7 || t == 11 || t == 16 || t == 20 || t == 23) =
      [2, 3, 7, 11, 16, 20, 23] := by decide
  rw [hfs, hfr]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, sel, ite_true, Bool.false_eq_true,
    ite_false, e0, e1, shaBinTraffic]
  have hp' : cnt (Sha.Gen.expectedDigests b0) m + cnt (Sha.Gen.expectedDigests b1) m =
      cnt (Sha.Gen.expectedDigests ((schedulerShaJobs 0 us ++ schedulerSanityJobs 0 us) ++
        jobsToSha N ++ receipt ++ source)) m := by
    rw [← cnt_append]; exact (hperm.map Msg.toFp).count_eq m
  have ht := htrie m
  have hr := hrest m
  have hc := hcodec m
  simp only [expectedDigests_append, cnt_append] at hp' ht hr
  omega

end RenderBundleV3

end ZkFormal.NearV3.Assembly.TrieShaBus
