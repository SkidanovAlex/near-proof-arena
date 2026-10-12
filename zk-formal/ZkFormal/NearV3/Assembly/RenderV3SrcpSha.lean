import ZkFormal.NearV3.Assembly.RenderV3RcptSha
import ZkFormal.NearV3.Assembly.TrieShaTwo
import ZkFormal.NearV3.Assembly.SourceBlockDigests
import ZkFormal.NearV3.Assembly.SourceShaBytes
import ZkFormal.NearV3.Assembly.TrieShaBus
import ZkFormal.NearV3.Assembly.RcptSourceInputs
import ZkFormal.NearV3.Assembly.PreparedSources
import ZkFormal.NearV3.Rcpt.Candidates.PreparedVerified
import ZkFormal.NearV3.Rcpt.Link.RelSources
import ZkFormal.NearV3.Rcpt.Link.SourcePayload
import ZkFormal.NearV3.Rcpt.Link.WitnessSources

/-!
# The source SHA family as the source table emits it (duplicate occurrences included)

Lead decision 2026-10-12: the source table (`srcpTraffic (blocksOfProofs A.srcps)`) hashes every
prepared source occurrence, duplicates included (leaf + path payloads, ids numbered over all
blocks), and receives an RC digest for every occurrence.  So the matching families are

* `A.srcShaAll` — all blocks' payloads (`sourcePayloads`), `K_SRC` ids as numbered by
  `blocksOfProofs`;
* `A.rcShaAll` — `sourceRcShaJobs` with every digest output enabled (`dmult := true`).

`srcShaAll_rows`: `≤ 1984·(18 + 35·32) = 2,257,792` rows (the A10 bound; 1984 counts every prepared
occurrence, duplicates included), every message `≤ 35` rows, bytes `< 256`.
`srcp_bytes`/`srcp_digests`: the exact source-table `BYTES` sends / `DIGEST` receives.
-/

namespace ZkFormal.NearV3.Assembly.AcceptedV3
open NearSpec NearSpecV3 ZkFormal.Near ZkFormal.Algebra Render.SrcpGen Rcpt.Candidates RcptSkeleton

variable {cb wb : Bytes} (A : AcceptedV3 cb wb)

/-- Source SHA jobs as the source table emits them (duplicates included). -/
def srcJobsAll : List Render.Msg :=
  (blocksOfProofs A.srcps).flatMap fun B =>
    (sourcePayloads B).map fun p => (⟨msgId K_SRC p.1, p.2⟩ : Render.Msg)

def srcShaAll : List Sha.Gen.Msg := jobsToSha A.srcJobsAll

/-- Receipt-list RC jobs with every digest output enabled. -/
def rcShaAll : List Sha.Gen.Msg :=
  (sourceRcShaJobs A.k.H.shardId A.p.lists A.w.entries).map fun m => { m with dmult := true }

theorem sum_flatMap' {α : Type} (l : List α) (f : α → List Nat) :
    (l.flatMap f).sum = (l.map fun a => (f a).sum).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [List.flatMap_cons, List.sum_append, ih]

theorem mem_blocksOfProofs {xs : List ProofInput} {B : SrcpB} (h : B ∈ blocksOfProofs xs) :
    ∃ i, ∃ hi : i < xs.length, ∃ q, B = blockOfProof xs[i].root xs[i].dup i q xs[i].entry := by
  unfold blocksOfProofs at h
  obtain ⟨⟨i, hi⟩, rfl⟩ := List.mem_ofFn.mp h
  exact ⟨i, hi, _, rfl⟩

theorem srcps_length : A.srcps.length = A.p.lists.length := by
  simp [AcceptedV3.srcps, Render.acceptedSrcpInputs]

/-- Every source input is an authenticated prepared occurrence. -/
theorem srcps_auth (i : Nat) (hi : i < A.srcps.length) :
    A.srcps[i].root = (A.p.lists.getD i ⟨[], 0, []⟩).root ∧
    A.srcps[i].entry = sourceEntry A.w.entries (A.p.lists.getD i ⟨[], 0, []⟩) ∧
    lookupLast (A.p.lists.getD i ⟨[], 0, []⟩).key A.w.entries = some A.srcps[i].entry ∧
    A.srcps[i].entry.proof.toShard = A.k.H.shardId ∧
    verifyReceiptProof (A.p.lists.getD i ⟨[], 0, []⟩).root A.srcps[i].entry = true := by
  have hil : i < A.p.lists.length := by rw [← A.srcps_length]; exact hi
  have hm : A.p.lists.getD i ⟨[], 0, []⟩ ∈ A.p.lists := by
    rw [← List.getElem_eq_getD (h := hil) ⟨[], 0, []⟩]
    exact List.getElem_mem hil
  have hx : A.srcps[i] = ⟨(A.p.lists.getD i ⟨[], 0, []⟩).root, ZkFormal.NearV3.Public.sourceDup A.p.lists i,
      sourceEntry A.w.entries (A.p.lists.getD i ⟨[], 0, []⟩)⟩ := by
    simp [AcceptedV3.srcps, Render.acceptedSrcpInputs]
  obtain ⟨k, w', hk, hd, hv, _⟩ := relD0a_sources_verified A.rel
  have hkk : k = A.k := Except.ok.inj (hk.symm.trans A.hk)
  have hww : w' = A.w := Except.ok.inj (hd.symm.trans A.hw)
  subst hkk hww
  obtain ⟨e, he, _, ht, hver⟩ := preparedSourceLists_authenticated A.w.entries A.k.H.shardId A.k.sourceBlks hv
    (prepD0_source_lists A.hp A.hk) _ hm
  have hse : sourceEntry A.w.entries (A.p.lists.getD i ⟨[], 0, []⟩) = e := by
    unfold sourceEntry; rw [he]; rfl
  rw [hx]
  exact ⟨rfl, rfl, by rw [hse]; exact he, by rw [hse]; exact ht, by rw [hse]; exact hver⟩

/-- Payload widths of every emitted block. -/
theorem block_widths {B : SrcpB} (hB : B ∈ blocksOfProofs A.srcps) :
    B.leaf.length = 32 ∧ (∀ it ∈ B.path, it.bytes.length = 64) ∧ B.path.length ≤ Dp0 := by
  obtain ⟨i, hi, q, rfl⟩ := mem_blocksOfProofs hB
  obtain ⟨-, -, hl, -, -⟩ := A.srcps_auth i hi
  have hs := lookupLast_path_shape A.hd hl
  refine ⟨by simp [blockOfProof], ?_, ?_⟩
  · intro it hit
    have hh := proofItems_lengths A.srcps[i].entry.proof.path q 32 _ (ArenaCore.sha256_length _)
      (fun step hm => (hs step hm).1) it hit
    cases hd : it.dir <;> simp [SrcpItem.bytes, hd, hh.1, hh.2]
  · simpa [blockOfProof] using A.srcpDepth _ (List.getElem_mem hi)

theorem block_rows (B : SrcpB) (hl : B.leaf.length = 32) (hp : ∀ it ∈ B.path, it.bytes.length = 64) :
    ((((sourcePayloads B).map fun p => (⟨msgId K_SRC p.1, p.2⟩ : Render.Msg))).map
      fun m => Render.rowsOf m.bytes.length).sum = 18 + 35 * B.path.length := by
  have he : (B.path.map fun it => Render.rowsOf it.bytes.length) = B.path.map (fun _ => 35) := by
    apply List.map_congr_left
    intro it hi
    rw [hp it hi]
    rfl
  simp only [sourcePayloads, List.map_append, List.map_cons, List.map_nil, List.map_map, Function.comp_def,
    List.sum_append, List.sum_cons, List.sum_nil, hl]
  rw [he, List.map_const', List.sum_replicate_nat]
  simp only [Render.rowsOf]
  omega

/-- **The source family fits the A10 bound** (duplicates included). -/
theorem srcShaAll_rows : (Sha.Gen.honestRows A.srcShaAll).length ≤ 2257792 := by
  rw [srcShaAll, jobsToSha_rows, srcJobsAll, List.map_flatMap, sum_flatMap']
  have hle : ∀ B ∈ blocksOfProofs A.srcps,
      ((((sourcePayloads B).map fun p => (⟨msgId K_SRC p.1, p.2⟩ : Render.Msg))).map
        fun m => Render.rowsOf m.bytes.length).sum ≤ 18 + 35 * Dp0 := by
    intro B hB
    obtain ⟨hl, hp, hd⟩ := A.block_widths hB
    rw [block_rows B hl hp]
    omega
  have h1 := TrieShaTwo.sum_map_le_mul _ (18 + 35 * Dp0) _ hle
  have hn : (blocksOfProofs A.srcps).length ≤ 1984 := by
    have h := (DedupCompile.relD0a_inputs A.rel A.hp A.hf A.hd).2.1
    simp only [blocksOfProofs, List.length_ofFn, A.srcps_length]
    simpa [sourceLists] using h
  have h2 : (blocksOfProofs A.srcps).length * (18 + 35 * Dp0) ≤ 1984 * (18 + 35 * Dp0) :=
    Nat.mul_le_mul_right _ hn
  have h3 : 1984 * (18 + 35 * Dp0) = 2257792 := by decide
  omega

theorem srcShaAll_msgRows : ∀ M ∈ A.srcShaAll, (Sha.Gen.msgRows M).length ≤ 35 := by
  intro M hM
  obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hM
  obtain ⟨B, hB, hm⟩ := List.mem_flatMap.mp hm
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hm
  obtain ⟨hl, hw, -⟩ := A.block_widths hB
  have hr := jobsToSha_weights [(⟨msgId K_SRC p.1, p.2⟩ : Render.Msg)]
  simp only [upsertShaWeights, jobsToSha, List.map_cons, List.map_nil, List.cons.injEq, and_true] at hr
  rw [hr]
  simp only [sourcePayloads, List.mem_append, List.mem_singleton, List.mem_map] at hp
  rcases hp with rfl | ⟨it, hit, rfl⟩
  · simp only [hl]; decide
  · simp only [hw it hit]; decide

theorem srcShaAll_bytes : ∀ M ∈ A.srcShaAll, ∀ b ∈ M.bytes, b < 256 := by
  intro M hM b hb
  obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hM
  obtain ⟨B, hB, hm⟩ := List.mem_flatMap.mp hm
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hm
  obtain ⟨i, hi, q, rfl⟩ := mem_blocksOfProofs hB
  simp only [sourcePayloads, List.mem_append, List.mem_singleton, List.mem_map] at hp
  rcases hp with rfl | ⟨it, hit, rfl⟩
  · simp only [blockOfProof] at hb
    obtain ⟨v, _, rfl⟩ := List.mem_map.mp hb
    exact v.toNat_lt
  · exact proofItems_byte_bounds _ _ _ _ it hit b hb

/-- **`BYTES`: the source table sends exactly the bytes of `srcShaAll`.** -/
theorem srcp_bytes (m : List Fp) :
    cnt ((srcpTraffic (blocksOfProofs A.srcps)).sends B_BYTES) m = cnt (Sha.Gen.expectedBytes A.srcShaAll) m := by
  rw [srcShaAll, TrieShaBus.jobBytes_expected]
  have h : (srcpTraffic (blocksOfProofs A.srcps)).sends B_BYTES = jobBytes A.srcJobsAll := by
    simp only [srcpTraffic, show B_BYTES ≠ B_SIZE by decide, ite_false, srcJobsAll, jobBytes,
      source_block_bytes]
    rw [List.flatMap_assoc]
    congr 1
    funext B
    rw [List.flatMap_map]
  rw [h]

/-- One emitted block's `DIGEST` receives: its payload outputs and its RC digest. -/
theorem block_digest_perm (root : Bytes) (dup : Bool) (j q : Nat) (e : ProofEntry)
    (hv : verifyReceiptProof root e = true) (hp : ∀ step ∈ e.proof.path, step.1.length = 32) :
    (srcpBlockMsgs (blockOfProof root dup j q e) B_DIGEST false).Perm
      (sourceBlockOutputs (blockOfProof root dup j q e) ++
        [digMsg (msgId K_RC j) (blockOfProof root dup j q e).L (blockOfProof root dup j q e).leaf]) := by
  rw [blockOfProof_digest_chain root dup j q e hv hp]
  have hj : (blockOfProof root dup j q e).j = j := rfl
  have hfl : ∀ l : List SrcpItem, l.flatMap (fun it => [digMsg (msgId K_SRC it.pq) it.pl it.acc]) =
      l.map sourceItemInput := by
    intro l; induction l <;> simp_all [sourceItemInput]
  rw [List.perm_iff_count]
  intro a
  simp only [srcpBlockMsgs, srcpRootMsgs, srcpLeafMsgs, srcpItemMsgs, B_DIGEST, B_BYTES, B_RCL, B_SRC, hj]
  simp only [and_true, true_and, ite_true, ite_false, Bool.false_eq_true, and_false, false_and, hfl,
    List.count_append, List.count_cons, List.count_nil, List.nil_append, List.append_nil, List.singleton_append,
    List.cons_append]
  omega

theorem count_flatMap_split (bs : List SrcpB) (f : SrcpB → List Msg) (g : SrcpB → Msg) (m : List Fp) :
    ((bs.flatMap fun B => f B ++ [g B]).map Msg.toFp).count m =
      ((bs.flatMap f).map Msg.toFp).count m + ((bs.map g).map Msg.toFp).count m := by
  induction bs with
  | nil => rfl
  | cons B bs ih =>
    simp only [List.flatMap_cons, List.map_cons, List.map_append, List.count_append, List.count_cons,
      List.count_nil, ih, List.map_nil]
    omega

theorem rc_digests : Sha.Gen.expectedDigests A.rcShaAll =
    (blocksOfProofs A.srcps).map fun B => digMsg (msgId K_RC B.j) B.L B.leaf := by
  have hf : A.rcShaAll.filter (·.dmult) = A.rcShaAll := by
    apply List.filter_eq_self.mpr
    intro a ha
    obtain ⟨m, -, rfl⟩ := List.mem_map.mp ha
    rfl
  unfold Sha.Gen.expectedDigests
  rw [hf]
  apply List.ext_getElem
  · simp [rcShaAll, sourceRcShaJobs, blocksOfProofs, A.srcps_length]
  · intro i h1 h2
    have hi : i < A.srcps.length := by simpa [blocksOfProofs] using h2
    obtain ⟨-, he, -, ht, -⟩ := A.srcps_auth i hi
    simp only [List.getElem_map, blocksOfProofs, List.getElem_ofFn, rcShaAll, sourceRcShaJobs,
      List.getElem_range, blockOfProof, digMsg, Fin.getElem_fin]
    rw [ht, he, show DedupCompile.entryAt A.p.lists A.w.entries i =
      sourceEntry A.w.entries (A.p.lists.getD i ⟨[], 0, []⟩) from rfl]
    simp [List.map_map, Function.comp_def]

/-- **`DIGEST`: the source table receives exactly the digests of `srcShaAll` and `rcShaAll`.** -/
theorem srcp_digests (m : List Fp) :
    cnt ((srcpTraffic (blocksOfProofs A.srcps)).recvs B_DIGEST) m =
      cnt (Sha.Gen.expectedDigests A.srcShaAll) m + cnt (Sha.Gen.expectedDigests A.rcShaAll) m := by
  have hr : (srcpTraffic (blocksOfProofs A.srcps)).recvs B_DIGEST =
      (blocksOfProofs A.srcps).flatMap fun B => srcpBlockMsgs B B_DIGEST false := by
    simp only [srcpTraffic, show B_DIGEST ≠ B_SIZE by decide, ite_false]
  have hs : Sha.Gen.expectedDigests A.srcShaAll = (blocksOfProofs A.srcps).flatMap sourceBlockOutputs := by
    rw [srcShaAll, ZkFormal.NearV3.Candidates.ReceiptDigestPartition.jobs_digests, srcJobsAll, List.map_flatMap]
    unfold sourceBlockOutputs
    simp only [List.map_map, Function.comp_def]
  have hp : ((blocksOfProofs A.srcps).flatMap fun B => srcpBlockMsgs B B_DIGEST false).Perm
      ((blocksOfProofs A.srcps).flatMap fun B => sourceBlockOutputs B ++ [digMsg (msgId K_RC B.j) B.L B.leaf]) := by
    rw [List.perm_iff_count]
    intro a
    rw [List.count_flatMap, List.count_flatMap]
    congr 1
    apply List.map_congr_left
    intro B hB
    show List.count a _ = List.count a _
    apply List.Perm.count_eq
    obtain ⟨i, hi, q, rfl⟩ := mem_blocksOfProofs hB
    obtain ⟨-, -, hl, -, hv⟩ := A.srcps_auth i hi
    have h := block_digest_perm A.srcps[i].root A.srcps[i].dup i q A.srcps[i].entry
      (by rw [show A.srcps[i].root = (A.p.lists.getD i ⟨[], 0, []⟩).root from (A.srcps_auth i hi).1]; exact hv)
      (fun step hm => (lookupLast_path_shape A.hd hl step hm).1)
    simpa only [blockOfProof] using h
  rw [hr, cnt, cnt, cnt, (hp.map Msg.toFp).count_eq m, hs, A.rc_digests]
  exact count_flatMap_split _ _ _ m

end ZkFormal.NearV3.Assembly.AcceptedV3
