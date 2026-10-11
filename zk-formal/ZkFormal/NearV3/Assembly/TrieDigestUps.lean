import ZkFormal.NearV3.Assembly.TrieUpsBytes
import ZkFormal.NearV3.Assembly.TrieUpsOrigin
import ZkFormal.NearV3.Assembly.SchedulerDigestConservation
import ZkFormal.NearV3.Assembly.CompactDigestWindows
import ZkFormal.NearV3.Rcpt.Candidates.NativeReaderRankList

/-!
# ZkFormal.NearV3.Assembly.TrieDigestUps — the ups `DIGEST` receives are the scheduler upsert jobs' digests

* `view_digest_recv`: the `DIGEST` receives of the aligned ups view are
  `compactGeneratedDigests Is` (the compact relay's inventory; value rows `.v p` receive nothing,
  `W0..W2` nothing, `W3` the root, every fresh window of a part its digest);
* **`ups_sha_scheduler`**: for the instances of `trie_all_of` (`UpsSha insts`) ONE choice of scheduler
  witnesses `us` with the row bound, the ups `BYTES` identity, and: the ranked instances
  `physicalPrefixUps p insts` (any `p`, in particular `upsRanked ws insts`) have
  `DIGEST` receives `~ expectedDigests (schedulerShaJobs 0 us)` (via
  `scheduler_compact_digest_conservation`; the ranked instances keep their allocation, SHA family
  and native reader origin, `physicalPrefixUps_origins`, and the origin gives the native encoding).
-/

namespace ZkFormal.NearV3.Assembly.TrieDigestUps

open NearSpec NearSpecV3 ZkFormal.Near ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3 Render Render.UpsGen
  UpsRows Assembly Rcpt.Candidates Rcpt.Candidates.NodePostUpdate Render.UpsRelay TrieUpsSched

theorem uMsgs_digest (C D : URow) :
    uMsgs C D B_DIGEST false = compactMsgs C D B_DIGEST false := by
  simp [compactMsgs, compactInteractions, uMsgs, UpsV3.interactions, Dsl.send, Dsl.recv,
    B_BYTES, B_MIDROOT, B_ROOT, B_DIGEST, B_S0F, B_SPLEN, B_SPOST, B_EDGE, B_BMAP, B_UPB, B_MEMD]

private theorem not_seg_reg (i : Nat) (hi : i < 32) : isSeg (UpsV3.reg i) = false := by
  unfold isSeg UpsV3.reg
  have h1 : ¬129+i<49 := by omega
  have h2 : ¬176≤129+i := by omega
  have h3 : ¬129+i=186 := by omega
  simp [h1,h2,h3]

private theorem qcell_reg (I : UpsInst) (k p u i : Nat) (hi : i < 32) :
    qCell I k p u (UpsV3.reg i) = qRowCell I k p 0 (UpsV3.reg i) := by
  unfold qCell isPC UpsV3.reg
  have h1 : ¬129+i<100 := by omega
  have h2 : ¬179≤129+i := by omega
  simp only [show (decide (49≤129+i) && decide (129+i<100) ||
    decide (179≤129+i) && decide (129+i<184))=false by simp [h1,h2],Bool.false_eq_true,ite_false]
  unfold qRowCell qRow
  split <;> (try omega)

/-- A generated aligned row's `DIGEST` receives are its record's compact digest messages. -/
theorem digest_row (Is : List UpsInst) (q i : Nat) (rk : RK) (D : URow) :
    uMsgs (generatedRow Is q (i, rk)) D B_DIGEST false = CompactPhysicalDigests.digestRowMsgs (inst Is i) rk := by
  rw [uMsgs_digest]
  unfold CompactPhysicalDigests.digestRowMsgs
  apply CompactPhysicalDigests.digest_projection _ _ _ _ (fun _ => Fp.toNat_lt _) (fun _ => Fp.toNat_lt _)
  · cases rk <;> rfl
  · cases rk <;> rfl
  · cases rk <;> rfl
  · intro j hj
    simp only [rowCell, not_seg_reg j hj, Bool.false_eq_true, ite_false]
    cases rk with
    | w t => rfl
    | v p => rfl
    | q k p =>
      dsimp only [CompactPhysicalDigests.digestRowCell]
      rw [qcell_reg _ k p _ j hj]

theorem digest_value_row (I : UpsInst) (p : Nat) : CompactPhysicalDigests.digestRowMsgs I (.v p) = [] := by
  unfold CompactPhysicalDigests.digestRowMsgs
  rw [CompactPhysicalDigests.row_digest _ _ (fun _ => Fp.toNat_lt _)]
  have h : ((CompactPhysicalDigests.digestRowCell I (.v p) UpsV3.gD : Int) : Fp).toNat = 0 := rfl
  simp [h]

theorem uMsgs_digest_form (C D : URow) :
    uMsgs C D B_DIGEST false =
      if uev C D (Dsl.c UpsV3.gD) = 1 then
        [([Dsl.c UpsV3.dI, Dsl.c UpsV3.dL] ++ UpsV3.regs).map (fun e => (uev C D e).toNat)] else [] := by
  simp [uMsgs, UpsV3.interactions, Dsl.send, Dsl.recv,
    B_BYTES, B_MIDROOT, B_ROOT, B_DIGEST, B_S0F, B_SPLEN, B_SPOST, B_EDGE, B_BMAP, B_UPB, B_MEMD, uMult]
  split <;> rfl

theorem digest_congr (C C' D D' : URow) (h : ∀ x < 200, C x = C' x) :
    uMsgs C D B_DIGEST false = uMsgs C' D' B_DIGEST false := by
  have e : ∀ x < 200, uev C D (Dsl.c x) = uev C' D' (Dsl.c x) := by
    intro x hx
    simp only [uev, Expr.evalWith, uEnv, Dsl.c, h x hx, Bool.false_eq_true, ite_false]
  rw [uMsgs_digest_form, uMsgs_digest_form, e UpsV3.gD (by decide)]
  have hr : UpsV3.regs.map (fun e => (uev C D e).toNat) = UpsV3.regs.map (fun e => (uev C' D' e).toNat) := by
    simp only [UpsV3.regs, List.map_map]
    apply List.map_congr_left
    intro i hi
    have hi := List.mem_range.mp hi
    simp only [Function.comp_apply]
    rw [e (UpsV3.reg i) (by unfold UpsV3.reg; omega)]
  simp only [List.map_append, List.map_cons, List.map_nil, hr, e UpsV3.dI (by decide), e UpsV3.dL (by decide)]

/-- **`DIGEST` receives of the aligned ups view** = the compact relay inventory. -/
theorem view_digest_recv (Is : List UpsInst) (hok : UpsRenderOk Is) (t : Nat) :
    (viewOf (upsTraceAligned Is) t (segsOf Is)).flatMap (fun s => s.msgs B_DIGEST false) =
      CompactPhysicalDigests.compactGeneratedDigests Is := by
  rw [aligned_view_bus Is hok t B_DIGEST false
    (fun i rk => CompactPhysicalDigests.digestRowMsgs (inst Is i) rk)
    (fun q i rk D _ => digest_row Is q i rk D)
    (fun C C' D D' h => digest_congr C C' D D' h),
    CompactPhysicalDigests.compactGeneratedDigests_recs]
  simp only [compactRecs, List.flatMap_assoc, List.flatMap_map]
  apply congrArg (fun f => (List.range Is.length).flatMap f)
  funext i
  simp only [recsI, compactRecsI, List.flatMap_append, List.flatMap_map, digest_value_row]
  simp

/-- **The scheduler family of the ups instances, bytes AND digests from one `us`**: for the instances
of `trie_all_of` (`UpsSha insts`) there are scheduler upsert witnesses `us` whose upsert + sanity SHA
family fits `1,663,260` rows and, for the ranked instances `physicalPrefixUps p insts` (any `p`, in
particular `upsRanked ws insts`): the ups `BYTES` sends are `expectedBytes (schedulerShaJobs 0 us)`
and the ups `DIGEST` receives are `~ expectedDigests (schedulerShaJobs 0 us)` (via
`scheduler_compact_digest_conservation`; the ranked instances keep their allocation, SHA family
and native reader origin, `physicalPrefixUps_origins`, and the origin gives the native encoding). -/
theorem ups_sha_scheduler {insts : List Render.UpsInst} (h : TrieUpsOrigin.UpsSha insts) :
    ∃ us : List SchedulerUpsertWitness,
      (Sha.Gen.honestRows (schedulerShaJobs 0 us ++ schedulerSanityJobs 0 us)).length ≤ 1663260 ∧
      ∀ p : List WStep3,
        ((physicalPrefixUps p insts).flatMap upsBytes).map Msg.toFp =
          (Sha.Gen.expectedBytes (schedulerShaJobs 0 us)).map Msg.toFp ∧
        ((CompactPhysicalDigests.compactGeneratedDigests (physicalPrefixUps p insts)).map Msg.toFp).Perm
          ((Sha.Gen.expectedDigests (schedulerShaJobs 0 us)).map Msg.toFp) := by
  obtain ⟨us, hl, h32, hg, hout, hval, -, hI⟩ := h
  refine ⟨us, schedulerBatch_rows us h32 (fun u hu => (hg u hu).1) (fun u hu => (hg u hu).2.1) hout hval, ?_⟩
  intro p
  refine ⟨?_, ?_⟩
  · have hr : (physicalPrefixUps p insts).map upsBytes = insts.map upsBytes :=
      TrieA7.prefix_map_eq upsBytes (fun _ _ => rfl) insts p
    rw [List.flatMap_def, hr, ← List.flatMap_def]
    exact TrieUpsBytes.bytes_from us insts 0 hl (fun i u I hu hI' => by
      obtain ⟨a, b, c, -⟩ := hI i u I hu hI'
      exact ⟨a, b, by omega⟩)
  have hmeta := physicalPrefixUps_origins (us := us) (Is := insts) (fun tau u I hu hI' => by
    obtain ⟨sha, -, -, a, root, hroot, origin⟩ := hI tau u I hu hI'
    exact ⟨a, sha, root, hroot, origin⟩) p
  apply scheduler_compact_digest_conservation us _ (hmeta.1.trans hl)
    (fun u hu => ⟨(hg u hu).1, (hg u hu).2.2⟩)
  intro i u J hu hJ
  obtain ⟨a, sha, root, hroot, origin⟩ := hmeta.2 i u J hu hJ
  have ht := forestRootAt_tree 0 0 (us.map SchedulerUpsertWitness.pre) i
  rw [hroot, List.getElem?_map, hu] at ht
  have heq : root.tree = u.pre := Option.some.inj ht
  refine ⟨a, sha, ?_⟩
  obtain ⟨B, base, Qs, he, rfl⟩ := origin
  exact ⟨_, B, base, Qs, heq ▸ he, heq ▸ rfl⟩

end ZkFormal.NearV3.Assembly.TrieDigestUps
