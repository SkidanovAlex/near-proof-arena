import ZkFormal.NearV3.Assembly.TrieShaBus
import ZkFormal.NearV3.Candidates.ReceiptDigestPartition
import ZkFormal.NearV3.Rcpt.Candidates.EmptyValueMessages

/-!
# ZkFormal.NearV3.Assembly.TrieShaEmpty — the native SHA family WITH the empty-value jobs

**Empty-value question (settled, 2026-10-12).**  A revealed value slot of a node record (`tv`)
always receives `DIGEST (VPRE(vid), vlen, reg)` (`NodeV3`: gate `gD = gP + fs·sVH·tv`, no
`vlen ≠ 0` condition), also for an empty value (`vlen = 0`); `valA7` sends no `DIGEST` (its `vz`
row only suppresses `BYTES`/`VBYTES`; the `EmptyValue.table` repair, which would send the empty
digest from `valV3`, is NOT in `nearAirV3`).  In `nearAirV3` only the SHA tables send `DIGEST`.
The SHA table hashes zero-length messages (`Sha.MsgsOk` has no non-emptiness requirement; one
padding block, `rowsOf 0 = 18`), and the job `⟨VPRE(vid), []⟩` sends exactly
`DIGEST (VPRE(vid), 0, sha256 [])` with no `BYTES` receives.  So the honest native family must be
`nativeShaJobsE` (one job per value record, empty ones included) instead of `nativeShaJobs`
(which skips them): a proof-statement issue, not an AIR completeness gap.  The row bound is
unchanged — the established bound `nodeValueShaRows` already charges every value record, empty
ones included (`hashRows (vs.map len)`), and is EQUAL to the rows of `nativeShaJobsE`.

* `jobBytesE`: `jobBytes (nativeShaJobsE ns es) = jobBytes (nativeShaJobs ns es)`;
* `valueJobsE_digests`: the value jobs' digests are `EmptyValue.valueDigests es` exactly;
* `nativeShaJobsE_rows`: rows `= nodeValueShaRows ns es`;
* **`native_sha_ofE`**, **`sha_bins_ofE`**: the `TrieShaFamilies.native_sha_of` /
  `TrieShaBus.sha_bins_of` analogues for the E family.
-/

namespace ZkFormal.NearV3.Assembly.TrieShaEmpty

open NearSpec NearSpecV3 ZkFormal.Near ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3 ZkFormal.NearV3.Assembly
  Render Render.UpsGen Rcpt.Candidates Rcpt.Candidates.NodePostUpdate ZkFormal.NearV3.Candidates TrieUpsSched

/-- One `VPRE` job per value record, empty values included. -/
def nativeValueShaJobsE (es : List ValE) : List Render.Msg :=
  es.map (fun v => ⟨msgId K_VPRE v.vid, v.bytes⟩)

/-- The native node/value SHA family with the empty-value jobs. -/
def nativeShaJobsE (ns : List NodeS3) (es : List ValE) : List Render.Msg :=
  nativeNodeShaJobsFrom 0 ns ++ nativeValueShaJobsE es

theorem valueJobsE_bytes (es : List ValE) :
    jobBytes (nativeValueShaJobsE es) = jobBytes (nativeValueShaJobs es) := by
  induction es with
  | nil => rfl
  | cons v vs ih =>
    simp only [nativeValueShaJobsE, List.map_cons, nativeValueShaJobs, jobBytes, List.flatMap_cons,
      List.flatMap_append] at *
    rw [ih]
    by_cases h : v.bytes = []
    · simp [h, emitAt]
    · simp [h]

theorem jobBytesE (ns : List NodeS3) (es : List ValE) :
    jobBytes (nativeShaJobsE ns es) = jobBytes (nativeShaJobs ns es) := by
  have h := valueJobsE_bytes es
  simp only [nativeShaJobsE, nativeShaJobs, jobBytes, List.flatMap_append] at *
  rw [h]

theorem valueJobsE_digests (es : List ValE) :
    (nativeValueShaJobsE es).map Render.digestMsg = EmptyValue.valueDigests es := by
  simp [nativeValueShaJobsE, EmptyValue.valueDigests, List.map_map, Function.comp_def]

theorem nativeShaJobsE_rows (ns : List NodeS3) (es : List ValE) :
    ((nativeShaJobsE ns es).map (fun m => Render.rowsOf m.bytes.length)).sum = nodeValueShaRows ns es := by
  simp only [nativeShaJobsE, List.map_append, List.sum_append, nativeNodeShaJobs_rows, nodeValueShaRows,
    hashRows, nativeValueShaJobsE, List.map_map, Function.comp_def]

theorem mem_valueJobs (es : List ValE) (v : ValE) (hv : v ∈ es) (h : v.bytes ≠ []) :
    (⟨msgId K_VPRE v.vid, v.bytes⟩ : Render.Msg) ∈ nativeValueShaJobs es := by
  induction es with
  | nil => simp at hv
  | cons e es ih =>
    simp only [nativeValueShaJobs, List.mem_append]
    rcases List.mem_cons.mp hv with rfl | hv
    · left; simp [h]
    · exact Or.inr (ih hv)

/-- Every E job is a job of the old family or has no bytes. -/
theorem mem_E (ns : List NodeS3) (es : List ValE) (M : Render.Msg) (hM : M ∈ nativeShaJobsE ns es) :
    M ∈ nativeShaJobs ns es ∨ M.bytes = [] := by
  rcases List.mem_append.mp hM with hM | hM
  · exact Or.inl (List.mem_append_left _ hM)
  · obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hM
    by_cases h : v.bytes = []
    · exact Or.inr h
    · exact Or.inl (List.mem_append_right _ (mem_valueJobs es v hv h))

/-- `accepted_updated_nativeShaJobs` before its last (`≤`) step: the full row charge
`nodeValueShaRows` of the accepted native records fits `2,925,275`. -/
theorem accepted_nodeValueShaRows {cb wb : NearSpec.Bytes} {k : WalkD0}
    {w : StateWitness} {m : MainExecutionV3} {steps : List ImplicitStepV3} {last : NearSpec.Bytes}
    (hk : walkD0 cb=.ok k) (hw : decodeW wb=.ok w) (hc : checkD0a B0 cb wb=.ok ())
    (hm : m.NativeValid k w)
    (hv : ImplicitTraceValid k m.result.trie.hashOf (k.implicitBlks.zip w.implicit) steps last)
    (hs : steps.length≤31)
    (hgood : ∀t∈m.pre::steps.map ImplicitStepV3.pre,t.wf=true)
    (ns : List NodeS3) (vs : List ValE) (hn : NodeWf3 ns)
    (hpre : ns.map (fun s => (s.v.ser false).length)=
      ((m.pre::steps.map ImplicitStepV3.pre).flatMap occs).map (fun t => (nodeEnc t).length))
    (hval : vs.map (fun v => v.bytes.length)=
      (forestBytes (m.pre::steps.map ImplicitStepV3.pre)).map List.length) :
    nodeValueShaRows ns vs ≤ 2925275 := by
  have hb := checkD0a_preBytes hk hw hc hm hv
  have ha := forest_sha_amortized (m.pre::steps.map ImplicitStepV3.pre) hgood
  have he := updated_native_rows ns vs _ hn hpre hval
  simp only [List.length_cons,List.length_map] at ha
  unfold B0 at hb
  omega

/-- **`native_sha_of` for the E family**: rows `≤ 2,925,275`, bytes `< 256`, and its job bytes
are the node and value tables' `BYTES` sends. -/
theorem native_sha_ofE {cb wb : Bytes} {k : WalkD0} {w : StateWitness}
    (hk : walkD0 cb = .ok k) (hw : decodeW wb = .ok w) (hc : checkD0a B0 cb wb = .ok ())
    {m : MainExecutionV3} {steps : List ImplicitStepV3} {last : Bytes} (hm : m.NativeValid k w)
    (hv : ImplicitTraceValid k m.result.trie.hashOf (k.implicitBlks.zip w.implicit) steps last)
    (oldPost : PTrie) (writes : List (List Nat × Bytes)) (q : UseRequests)
    (he : q.edges.length < Algebra.P) (hb : q.bmaps.length < Algebra.P) (hu : q.windows.length < Algebra.P)
    (hval : ValWf (TrieNative.vals m steps)) :
    (Sha.Gen.honestRows (jobsToSha (nativeShaJobsE (TrieNative.nodes m steps oldPost writes q)
        (TrieNative.vals m steps)))).length ≤ 2925275 ∧
      (∀ M ∈ jobsToSha (nativeShaJobsE (TrieNative.nodes m steps oldPost writes q) (TrieNative.vals m steps)),
        ∀ x ∈ M.bytes, x < 256) ∧
      jobBytes (nativeShaJobsE (TrieNative.nodes m steps oldPost writes q) (TrieNative.vals m steps)) =
        nodeSends3 (TrieNative.nodes m steps oldPost writes q) B_BYTES ++
          valSends (TrieNative.vals m steps) B_BYTES := by
  refine ⟨?_, ?_, (jobBytesE _ _).trans (nativeJobs_bytes _ _ hval)⟩
  · rw [jobsToSha_rows, nativeShaJobsE_rows]
    have hd : checkD0 cb wb=.ok () := by
      have hh:=((relD0a_iff B0 cb wb).mpr hc).1
      unfold RelD0 acceptsD0 at hh
      split at hh <;> simp_all
    obtain ⟨_,_,_,_,_,hcount⟩:=checkD0_native_steps hk hw hd
    have hs : steps.length≤31 := by
      have hh:=hv.length
      simp only [List.length_zip] at hh
      omega
    have hgood : ∀t∈m.pre::steps.map ImplicitStepV3.pre,t.wf=true := by
      intro t ht
      rcases List.mem_cons.mp ht with rfl|ht
      · rw [hm.pre];exact (built_spec _ trieFuel _ _ hm.root_length).2.1
      · obtain ⟨s,hs,rfl⟩:=List.mem_map.mp ht
        exact (hv.input_facts s hs).2.2
    have hn:=(NativeExecutionPost.assigned_inputs hk hw hc (by decide) hm hv
      (forestOldInputs (nativeReplayForest m steps oldPost writes)) q he hb hu).1
    exact accepted_nodeValueShaRows hk hw hc hm hv hs hgood _ _ hn.wf
      (NativePostShaBudget.node_lengths _ hgood _ _ q) (NativePostShaBudget.value_lengths _ _ _)
  · have hok := Candidates.NativePostShaOk.accepted hk hw hc hm hv
      (forestOldInputs (nativeReplayForest m steps oldPost writes)) q he hb hu
    simp only [TrieNative.nodes, TrieNative.vals, TrieNative.chain, TrieNative.seedNodes,
      TrieNative.seedVals, TrieNative.forest] at hok ⊢
    intro M hM x hx
    obtain ⟨J, hJ, rfl⟩ := List.mem_map.mp hM
    rcases mem_E _ _ J hJ with hJ | hJ
    · exact hok.bytes _ (List.mem_map.mpr ⟨J, hJ, rfl⟩) x hx
    · simp [hJ] at hx

/-- **`sha_bins_of` for the E family.** -/
theorem sha_bins_ofE {cb wb : Bytes} {k : WalkD0} {w : StateWitness}
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
    let all := (schedulerShaJobs 0 us ++ schedulerSanityJobs 0 us) ++ jobsToSha (nativeShaJobsE ns es) ++
      receipt ++ source
    ∃ (b0 b1 : List Sha.Gen.Msg) (h0 : Sha.MsgsOk b0) (h1 : Sha.MsgsOk b1),
      (shaRenderV3 pub 0 (by decide) b0 h0).tf = shaBinTraffic b0 ∧
      (shaRenderV3 pub 1 (by decide) b1 h1).tf = shaBinTraffic b1 ∧
      (Sha.Gen.expectedBytes b0 ++ Sha.Gen.expectedBytes b1).Perm (Sha.Gen.expectedBytes all) ∧
      (Sha.Gen.expectedDigests b0 ++ Sha.Gen.expectedDigests b1).Perm (Sha.Gen.expectedDigests all) ∧
      jobBytes (nativeShaJobsE ns es) = nodeSends3 ns B_BYTES ++ valSends es B_BYTES := by
  intro ns es all
  obtain ⟨hrows, hnb, hnat⟩ := native_sha_ofE hk hw hc hm hv oldPost writes q he hb hu hval
  have hall : ∀ M ∈ (schedulerShaJobs 0 us ++ schedulerSanityJobs 0 us) ++ jobsToSha (nativeShaJobsE ns es) ++
      receipt ++ source, ∀ x ∈ M.bytes, x < 256 := by
    intro M hM x hx
    simp only [List.mem_append] at hM
    rcases hM with (((hM | hM) | hM) | hM) | hM
    · exact schedulerShaJobs_bytes 0 us M hM x hx
    · exact schedulerSanityJobs_bytes 0 us M hM x hx
    · exact hnb M hM x hx
    · exact hbr M hM x hx
    · exact hbs M hM x hx
  obtain ⟨b0, b1, h0, h1, -, t0, t1, pb, pd⟩ :=
    TrieShaTwo.two_sha_renders pub _ _ receipt source hs hrows hr hp hsm hall
  exact ⟨b0, b1, h0, h1, t0, t1, pb, pd, hnat⟩

end ZkFormal.NearV3.Assembly.TrieShaEmpty
