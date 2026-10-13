import ZkFormal.NearV3.Rcpt.Candidates.ShaJobBridge
import ZkFormal.NearV3.Rcpt.Candidates.PreparedRouting
import ZkFormal.NearV3.Rcpt.Link.RelSources
import ZkFormal.NearV3.Rcpt.SrcpDepth
import ZkFormal.NearV3.Assembly.RenderV3Trie
import ZkFormal.NearV3.Candidates.ShaFourPhysicalCore
import ZkFormal.NearV3.Rcpt.Candidates.ShaAllocationTraffic

/-!
# ZkFormal.NearV3.Assembly.TrieShaTwo — the SHA jobs in the two `nearAirV3` SHA tables (0, 1)

* (a) `preparedSourceLists_paths`: A10 (`relD0a_paths`) reaches every prepared source occurrence
  (copy of `preparedSourceLists_raw_routing`); **`source_rows_A10`**: for an accepted witness the
  prepared source SHA family has at most `sourceShaFor maxLists (maxLists · Dp0) = 2,257,792` rows
  (was `8,932,712` without A10).
* (b) `twoBudget_fit`: two residual capacities around a large job each (`N` in bin 0, `S + Rc` in
  bin 1) hold all source jobs of `≤ 35` rows when `S + Rc + N + Σ + 35 ≤ 2 · 2^22`;
  `twoShaJobBins` = `[native ++ src₀, scheduler ++ receipt ++ src₁]` (whole jobs, `splitJobs`),
  `twoShaJobBins_preserve`, **`twoSha_physical_fit`** at the per-family bounds
  `1,663,260 / 2,925,275 / 1,373,299 / 2,257,792` (slack 168,947 rows).
* (c) **`two_sha_renders`**: the two bins are `Sha.MsgsOk`, give the two `TableRenderV3`
  components `shaRenderV3 pub 0/1`, and their `BYTES` receives / `DIGEST` sends are
  permutations of the expected bytes / digests of all four families.

Open (not here): which message lists the v3 bundle's `BYTES` senders (node, val, ups, codec, rcpt,
acct, srcp, mrk) produce, i.e. the identification of the four families with the senders' traffic
and the resulting `BYTES`/`DIGEST` bus balances.
-/

namespace ZkFormal.NearV3.Assembly.TrieShaTwo

open NearSpec NearSpecV3 ZkFormal.Near ZkFormal.Air ZkFormal.Algebra Rcpt.Candidates Rcpt.Candidates.DedupCompile
  ZkFormal.NearV3.Candidates

/-! ## (a) Source paths and the source family under A10 -/

/-- A10's used-proof path bound reaches every shuffled prepared occurrence. -/
theorem preparedSourceLists_paths {k : WalkD0} {w : StateWitness}
    (hv : ∀ B ∈ k.sourceBlks, ∀ x ∈ B.slots, SourceSlotValid w.entries k.H.shardId B x)
    (hd : ∀ e ∈ usedProofs k w, e.proof.path.length ≤ Dp0)
    {out : List SrcList} (h : preparedSourceLists k.sourceBlks = .ok out) :
    ∀ s ∈ out, (sourceEntry w.entries s).proof.path.length ≤ Dp0 := by
  refine preparedSourceLists_property (fun s => (sourceEntry w.entries s).proof.path.length ≤ Dp0)
    k.sourceBlks ?_ h
  intro B hB s hs
  obtain ⟨x, hx, hs⟩ := List.mem_flatMap.mp hs
  by_cases hn : x.1.heightIncluded == B.hdr.height
  · simp only [hn, ↓reduceIte, List.mem_singleton] at hs
    subst s
    obtain ⟨e, he, _, _, _⟩ := hv B hB x hx hn
    have hu : e ∈ usedProofs k w := by
      apply List.mem_flatMap.mpr
      refine ⟨B, hB, List.mem_filterMap.mpr ⟨x, hx, ?_⟩⟩
      simpa only [hn, ↓reduceIte] using he
    simpa only [sourceEntry, he, Option.getD_some] using hd e hu
  · simp [hn] at hs

theorem sum_map_le_mul {α : Type} (f : α → Nat) (c : Nat) :
    ∀ l : List α, (∀ x ∈ l, f x ≤ c) → (l.map f).sum ≤ l.length * c
  | [], _ => by simp
  | a :: l, h => by
    have h1 := h a (by simp)
    have h2 := sum_map_le_mul f c l (fun x hx => h x (by simp [hx]))
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul]
    omega

/-- **The prepared source SHA family fits `2,257,792` rows** (A10). -/
theorem source_rows_A10 {cb wb raw : Bytes} {codes : List Bytes} {w : StateWitness} {hint : Hint} {p : Prep}
    (hc : checkD0a B0 cb wb = .ok ()) (hp : prepD0 cb hint = .ok p)
    (hf : decodeWitnessFile wb = .ok (raw, codes)) (hr : decodeStateWitness raw = .ok w) :
    (Sha.Gen.honestRows (Assembly.sourceShaMessages p.lists w.entries)).length ≤ 2257792 := by
  have hrel := (relD0a_iff B0 cb wb).mpr hc
  obtain ⟨_, hcnt, hs⟩ := relD0a_inputs hrel hp hf hr
  obtain ⟨he, -⟩ := sourceWeights_exact hr p.lists hs
  rw [← Assembly.upsertShaWeights_sum, Assembly.sourceShaMessages_weights, he]
  obtain ⟨k, sw, hk, hsw, hv, -⟩ := relD0a_sources_verified hrel
  have hd : decodeW wb = .ok w := by simp [decodeW, hf, hr, bind, Except.bind]
  have hew := Except.ok.inj (hsw.symm.trans hd)
  subst sw
  have hpp := preparedSourceLists_paths hv (Rcpt.SrcpDepth.relD0a_paths hrel hk hd)
    (Assembly.prepD0_source_lists hp hk)
  -- every block's path is a prepared occurrence's proof path
  have hblk : ∀ B ∈ (blocks p.lists w.entries).filter (fun B => !B.dup), B.path.length ≤ Dp0 := by
    intro B hB
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp (List.mem_filter.mp hB).1
    have hjl : j < p.lists.length := List.mem_range.mp hj
    have hm : p.lists.getD j ⟨[],0,[]⟩ ∈ p.lists := by
      rw [← List.getElem_eq_getD (h := hjl) ⟨[],0,[]⟩]
      exact List.getElem_mem hjl
    have h1 := hpp _ hm
    simpa only [block, Render.SrcpGen.blockOfProof, Render.SrcpGen.proofItems_length, entryAt, sourceEntry]
      using h1
  have hL : computedLists p.lists w.entries ≤ Rcpt.SrcpDepth.maxLists := by
    have := List.length_filter_le (fun B => !B.dup) (blocks p.lists w.entries)
    rw [blocks_length] at this
    unfold computedLists
    simp only [Rcpt.SrcpDepth.maxLists]
    simp only [sourceLists] at hcnt
    omega
  have hP : computedPaths p.lists w.entries ≤ Rcpt.SrcpDepth.maxLists * Dp0 := by
    unfold computedPaths
    have := sum_map_le_mul _ Dp0 _ hblk
    have h2 : computedLists p.lists w.entries * Dp0 ≤ Rcpt.SrcpDepth.maxLists * Dp0 := Nat.mul_le_mul_right _ hL
    unfold computedLists at h2
    omega
  rw [← Rcpt.SrcpDepth.sourceSha_A10.1]
  unfold sourceShaFor
  exact Nat.add_le_add (Nat.mul_le_mul_right _ hL) (Nat.mul_le_mul_right _ hP)

/-! ## (b) Two-bin packing -/

theorem twoBudget_fit (S N Rc : Nat) (xs : List Nat) (hm : ∀ x ∈ xs, x ≤ 35) (hN : N ≤ 2 ^ 22) (hSR : S + Rc ≤ 2 ^ 22)
    (ht : S + Rc + N + xs.sum + 35 ≤ 2 * 2 ^ 22) :
    N + (splitBudget (2 ^ 22 - N) xs).1.sum ≤ 2 ^ 22 ∧ S + Rc + (splitBudget (2 ^ 22 - N) xs).2.sum ≤ 2 ^ 22 := by
  have h0 := splitBudget_prefix_le (2 ^ 22 - N) xs
  have hs := congrArg List.sum (splitBudget_reconstruct (2 ^ 22 - N) xs)
  simp only [List.sum_append] at hs
  refine ⟨by omega, ?_⟩
  cases hrest : (splitBudget (2 ^ 22 - N) xs).2 with
  | nil => simp; omega
  | cons a rest =>
    have hstop := splitBudget_stop (2 ^ 22 - N) xs hrest
    have ha : a ∈ xs := by
      rw [← splitBudget_reconstruct (2 ^ 22 - N) xs, hrest]; simp
    have haM := hm a ha
    rw [hrest] at hs
    simp only [List.sum_cons] at hs ⊢
    omega

/-- `[native ++ src₀, scheduler ++ receipt ++ src₁]`, splitting the source jobs whole. -/
def twoShaJobBins {α : Type} (weight : α → Nat) (scheduler native receipt source : List α) : List (List α) :=
  let p := splitJobs weight (2 ^ 22 - (native.map weight).sum) source
  [native ++ p.1, scheduler ++ receipt ++ p.2]

theorem twoShaJobBins_preserve {α : Type} [DecidableEq α] (weight : α → Nat) (scheduler native receipt source : List α) :
    (twoShaJobBins weight scheduler native receipt source).flatten.Perm (scheduler ++ native ++ receipt ++ source) := by
  have he := splitJobs_reconstruct weight (2 ^ 22 - (native.map weight).sum) source
  apply List.perm_iff_count.mpr
  intro a
  have hc := congrArg (List.count a) he
  simp only [List.count_append] at hc
  simp only [twoShaJobBins, List.flatten_cons, List.flatten_nil, List.append_nil, List.count_append]
  omega

theorem twoSha_physical_fit (scheduler native receipt source : List Sha.Gen.Msg)
    (hs : (Sha.Gen.honestRows scheduler).length ≤ 1663260)
    (hv : (Sha.Gen.honestRows native).length ≤ 2925275)
    (hr : (Sha.Gen.honestRows receipt).length ≤ 1373299)
    (hp : (Sha.Gen.honestRows source).length ≤ 2257792)
    (hm : ∀ m ∈ source, (Sha.Gen.msgRows m).length ≤ 35) :
    let bins := twoShaJobBins (fun m : Sha.Gen.Msg => (Sha.Gen.msgRows m).length) scheduler native receipt source
    bins.length = 2 ∧ (∀ bin ∈ bins, (Sha.Gen.honestRows bin).length ≤ 2 ^ 22) ∧
      bins.flatten.Perm (scheduler ++ native ++ receipt ++ source) := by
  intro bins
  let wt := fun m : Sha.Gen.Msg => (Sha.Gen.msgRows m).length
  have hw : ∀ l : List Sha.Gen.Msg, (Sha.Gen.honestRows l).length = (l.map wt).sum := fun l =>
    (Assembly.upsertShaWeights_sum l).symm
  have hsp := splitJobs_weights wt (2 ^ 22 - (native.map wt).sum) source
  have h1 := congrArg Prod.fst hsp
  have h2 := congrArg Prod.snd hsp
  dsimp only at h1 h2
  have hm' : ∀ x ∈ source.map wt, x ≤ 35 := by
    intro x hx
    obtain ⟨m, hm0, rfl⟩ := List.mem_map.mp hx
    exact hm m hm0
  rw [hw] at hs hv hr hp
  obtain ⟨f0, f1⟩ := twoBudget_fit (scheduler.map wt).sum (native.map wt).sum (receipt.map wt).sum
    (source.map wt) hm' (by omega) (by omega) (by omega)
  refine ⟨rfl, ?_, ?_⟩
  · intro bin hb
    simp only [bins, twoShaJobBins, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · rw [hw, List.map_append, List.sum_append, h1]; exact f0
    · rw [hw, List.map_append, List.map_append, List.sum_append, List.sum_append, h2]; exact f1
  · classical
    exact twoShaJobBins_preserve wt scheduler native receipt source

/-! ## (c) The two SHA components -/

/-- **The two SHA table components** for the four job families, with the bytes/digests traffic. -/
theorem two_sha_renders (pub : List Fp) (scheduler native receipt source : List Sha.Gen.Msg)
    (hs : (Sha.Gen.honestRows scheduler).length ≤ 1663260)
    (hv : (Sha.Gen.honestRows native).length ≤ 2925275)
    (hr : (Sha.Gen.honestRows receipt).length ≤ 1373299)
    (hp : (Sha.Gen.honestRows source).length ≤ 2257792)
    (hm : ∀ m ∈ source, (Sha.Gen.msgRows m).length ≤ 35)
    (hb : ∀ M ∈ scheduler ++ native ++ receipt ++ source, ∀ x ∈ M.bytes, x < 256) :
    ∃ (b0 b1 : List Sha.Gen.Msg) (h0 : Sha.MsgsOk b0) (h1 : Sha.MsgsOk b1),
      twoShaJobBins (fun m : Sha.Gen.Msg => (Sha.Gen.msgRows m).length) scheduler native receipt source = [b0, b1] ∧
      (shaRenderV3 pub 0 (by decide) b0 h0).tf = shaBinTraffic b0 ∧
      (shaRenderV3 pub 1 (by decide) b1 h1).tf = shaBinTraffic b1 ∧
      (Sha.Gen.expectedBytes b0 ++ Sha.Gen.expectedBytes b1).Perm
        (Sha.Gen.expectedBytes (scheduler ++ native ++ receipt ++ source)) ∧
      (Sha.Gen.expectedDigests b0 ++ Sha.Gen.expectedDigests b1).Perm
        (Sha.Gen.expectedDigests (scheduler ++ native ++ receipt ++ source)) := by
  obtain ⟨-, hrows, hperm⟩ := twoSha_physical_fit scheduler native receipt source hs hv hr hp hm
  have hok := ShaFourPhysical.bins_ok _ _ hperm hrows hb
  refine ⟨_, _, hok _ (by simp [twoShaJobBins]), hok _ (by simp [twoShaJobBins]), rfl, rfl, rfl, ?_, ?_⟩
  · simpa [twoShaJobBins] using allocated_bytes hperm
  · simpa [twoShaJobBins] using allocated_digests hperm

end ZkFormal.NearV3.Assembly.TrieShaTwo
