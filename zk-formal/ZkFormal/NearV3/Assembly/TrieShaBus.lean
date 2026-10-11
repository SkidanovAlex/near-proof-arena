import ZkFormal.NearV3.Assembly.TrieUpsBytes
import ZkFormal.NearV3.Assembly.ShaBinRender

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

namespace RenderBundleV3

variable {pub : List Fp} (R : RenderBundleV3 pub)

/-- **`BYTES` balance of a bundle** from the four SHA families. -/
theorem balancedAt_bytes (ns : List NodeS3) (es : List ValE) (Js : List UpsInst) (hok : UpsRenderOk Js)
    (us : List SchedulerUpsertWitness) (receipt source b0 b1 : List Sha.Gen.Msg)
    (h0 : (R ⟨0, by decide⟩).tf = shaBinTraffic b0) (h1 : (R ⟨1, by decide⟩).tf = shaBinTraffic b1)
    (hperm : (Sha.Gen.expectedBytes b0 ++ Sha.Gen.expectedBytes b1).Perm
      (Sha.Gen.expectedBytes ((schedulerShaJobs 0 us ++ schedulerSanityJobs 0 us) ++
        jobsToSha (nativeShaJobs ns es) ++ receipt ++ source)))
    (hn : ExtOf (R ⟨T_NODE, by decide⟩).tf (nodeTraffic3 ns))
    (hv : ExtOf (R ⟨T_VAL, by decide⟩).tf (valTraffic es))
    (hu : ExtOf (R ⟨T_UPS, by decide⟩).tf (upsTraffic (UpsRows.viewOf (upsTraceAligned Js) T_UPS (UpsGen.segsOf Js))))
    (hnat : jobBytes (nativeShaJobs ns es) = nodeSends3 ns B_BYTES ++ valSends es B_BYTES)
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
        jobsToSha (nativeShaJobs ns es) ++ receipt ++ source)) m := by
    rw [← cnt_append]; exact (hperm.map Msg.toFp).count_eq m
  simp only [TrieUpsBytes.expectedBytes_append, cnt_append, jobBytes_expected, hnat] at hp'
  have hu' : cnt (Js.flatMap upsBytes) m = cnt (Sha.Gen.expectedBytes (schedulerShaJobs 0 us)) m := by
    simp only [cnt, hups]
  have hc := hcodec m
  have hr := hrest m
  simp only [TrieUpsBytes.expectedBytes_append, cnt_append] at hr
  simp only [nodeTraffic3, valTraffic] at *
  omega

end RenderBundleV3

end ZkFormal.NearV3.Assembly.TrieShaBus
