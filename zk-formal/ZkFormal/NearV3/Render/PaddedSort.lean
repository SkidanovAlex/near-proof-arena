import ZkFormal.NearV3.Render.PaddedCongr
import ZkFormal.NearV3.Candidates.NativeSortTraffic
import ZkFormal.NearV3.Candidates.SortEmptyCap
import ZkFormal.NearV3.Assembly.RcptSkeleton

/-!
# Aligned receipt-id sort generator (`nearAirV3` table 24, `{Sort.table with maxLog := 18}`)

`sortTraceAligned S` is the array-backed sort table (`SortGen.cell`, delay line wrapping at the
physical height) at `padLog22 (logOf (32·|S|))`, for the sorted id list `S` of
`Candidates/SortGeneral*` (`IdsOk`: nonempty, 32-byte ids, strictly increasing).  Traffic:
`sortTraffic S` on `B_RIDS` (soundness side `Near.sortTraffic`); for receipts,
`NativeSortIds.sorted rs` is a permutation of `input rs` with the same `sortTraffic` counts.

**Cap.** `18 ≢ 1 (mod 3)`: at the current cap the aligned height is `≤ 16`, i.e. at most
`2048` receipts (`sort_aligned_complete`).  The receipt bound (`≤ 8192`, `32·8192 = 2^18`)
needs the aligned height `19`: `sort_aligned_complete19` at `{Sort.table with maxLog := 19}`
holds for every `≤ 8192` ids.  **Empty input** (`S = []`) is impossible for the old
`Sort.constraints` (`SortEmpty.old_empty_impossible`); `nearAirV3` uses those constraints, so a
chunk with no receipts has no honest sort table (`SortEmpty.table` is the repaired variant).
-/
namespace ZkFormal.NearV3.Render
open ZkFormal.Near ZkFormal.Near.Render ZkFormal.Air ZkFormal.Algebra ZkFormal.Size
open ZkFormal.Near.Dsl ZkFormal.NearV3.Candidates ZkFormal.NearV3.Candidates.SortGeneral

def sortTraceAligned (S : List (Nat × List Nat)) : Trace Fp :=
  let log := padLog22 (logOf (32 * S.length))
  rowsTrace log (mkTab (2 ^ log) Sort.width (SortGen.cell S (2 ^ log)))

/-- Traffic of the sort table at any height `H ≥ 32·|S|` (the delay line wraps at `H`). -/
theorem sort_traffic_at (S : List (Nat × List Nat)) (tr : Trace Fp) (t : Nat) (pub : List Fp)
    (H : Nat) (hH : tr.height t = H) (hle : 32 * S.length ≤ H)
    (hcell : ∀ q c, q < H → c < Sort.width → tr.cell t q c = Fp.ofNat (SortGen.cell S H q c)) :
    TableTraffic Sort.interactions tr t pub (sortTraffic S) := by
  have row : ∀ q, q < H → ∀ b s,
      rowTraffic Sort.interactions tr t q pub b s =
        if b = B_RIDS ∧ s = false ∧ q < 32 * S.length then
          [[Fp.ofNat (S.getD (q / 32) (0, [])).1, Fp.ofNat (q % 32),
            Fp.ofNat ((S.getD (q / 32) (0, [])).2.getD (q % 32) 0)]]
        else [] := by
    intro q hq b s
    simp only [rowTraffic, Sort.interactions, recv, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, multNat_one, Interaction.msgVal, List.map_cons, List.map_nil, eval_c,
      hcell q _ hq (by decide : Sort.act < Sort.width), hcell q _ hq (by decide : Sort.rr < Sort.width),
      hcell q _ hq (by decide : Sort.i < Sort.width), hcell q _ hq (by decide : Sort.bb < Sort.width)]
    by_cases ha : q < 32 * S.length
    · simp only [SortGen.cell, Sort.act, Sort.rr, Sort.i, Sort.bb, Nat.reduceLeDiff, if_false, ha,
        if_true, SortGen.actCell, SortGen.bbAt, SortGen.idOf]
      by_cases hb : B_RIDS = b ∧ false = s
      · obtain ⟨rfl, rfl⟩ := hb; simp; rfl
      · rw [if_neg hb, if_neg (by rintro ⟨h1, h2, _⟩; exact hb ⟨h1.symm, h2.symm⟩)]
    · simp only [SortGen.cell, Sort.act, Nat.reduceLeDiff, if_false, ha, and_false]
      split <;> simp <;> exact fp_zero_ne_one
  apply traffic_of
  · intro b
    rw [hH, flatMap_nil' (fun q hq => by rw [row q (List.mem_range.1 hq)]; simp)]
    simp [sortTraffic]
  · intro b
    rw [hH]
    by_cases hb : b = B_RIDS
    · subst hb
      rw [range_split hle, List.flatMap_append,
        flatMap_nil' (l := List.map _ _) (fun q hq => by
          obtain ⟨q', _, rfl⟩ := List.mem_map.1 hq
          rw [row _ (by have := List.mem_range.1 ‹_›; omega)]; simp),
        flatMap_single (g := fun q => [Fp.ofNat (S.getD (q / 32) (0, [])).1, Fp.ofNat (q % 32),
            Fp.ofNat ((S.getD (q / 32) (0, [])).2.getD (q % 32) 0)])
          (fun q hq => by rw [row q (by have := List.mem_range.1 hq; omega)]; simp [List.mem_range.1 hq])]
      simp only [sortTraffic, if_true, List.append_nil]
      rw [show (fun (x : Nat × List Nat) => (List.range 32).map fun i => [x.1, i, x.2.getD i 0]) =
          (fun x => (List.range 32).map ((fun (x : Nat × List Nat) i => [x.1, i, x.2.getD i 0]) x)) from rfl]
      rw [flatMap_chunks 32 (by decide) (0, []), Nat.mul_comm, List.map_map]
      exact List.Perm.refl _
    · rw [flatMap_nil' (fun q hq => by rw [row q (List.mem_range.1 hq)]; simp [hb])]
      simp [sortTraffic, hb]

/-- Core: local legality at every cap `≥` the aligned height, and the exact traffic. -/
theorem sort_aligned_core (S : List (Nat × List Nat)) (ok : SortGeneral.IdsOk S) (hn : S.length ≤ 8192)
    (cap : Nat) (hcap : padLog22 (logOf (32 * S.length)) ≤ cap) (t : Nat) (pub : List Fp) :
    TableLocal { Sort.table with maxLog := cap } (sortTraceAligned S) t pub ∧
    TableTraffic Sort.table.interactions (sortTraceAligned S) t pub (sortTraffic S) ∧
    (sortTraceAligned S).log t % 3 = 1 := by
  have hh := padded_log_fits (32 * S.length) (by omega)
  generalize hL : padLog22 (logOf (32 * S.length)) = L at hh hcap
  have hlog : ∀ t', (sortTraceAligned S).log t' = L := by
    intro t'; show padLog22 (logOf (32 * S.length)) = L; exact hL
  have hcell : ∀ t' q col, q < 2 ^ L → col < Sort.width →
      (sortTraceAligned S).cell t' q col = Fp.ofNat (SortGen.cell S (2 ^ L) q col) := by
    intro t' q col hq hc
    unfold sortTraceAligned
    simp only [hL]
    exact rowsTrace_mkTab L _ _ t' q col hq hc
  have hH : ∀ t', (sortTraceAligned S).height t' = 2 ^ L := by
    intro t'; unfold Trace.height; rw [hlog]
  refine ⟨⟨by rw [hlog]; omega, by rw [hlog]; exact hcap, ?_, ?_⟩,
    sort_traffic_at S _ t pub (2 ^ L) (hH t) hh.1 (fun q c hq hc => hcell t q c hq hc),
    by rw [hlog]; exact hh.2.2.2⟩
  · intro r hr e he
    have h := SortGeneral.SortLocal.constr ok (tr := sortTraceAligned S) (pub := pub) (H := 2 ^ L) (hH _) hh.1
      (fun q col hq hc => hcell _ q col hq hc) (q := r) (by rw [← hH t]; exact hr) he
    exact h
  · intro r hr i hi b hb
    simp only [Sort.table, Sort.interactions, recv, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst i
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    subst b
    have hr' : r < 2 ^ L := by rw [← hH t]; exact hr
    change (sortTraceAligned S).cell t r Sort.act = 0 ∨ (sortTraceAligned S).cell t r Sort.act = 1
    rw [hcell t r Sort.act hr' (by decide)]
    by_cases ha : r < 32 * S.length
    · right; rw [show Sort.act = 0 from rfl, SortGeneral.SortLocal.v_act S _ r ha]; rfl
    · left; rw [show Sort.act = 0 from rfl, SortGeneral.SortLocal.v_pad S _ r ha 0 (by decide)]; rfl

/-- **`sortV3` aligned completeness at the current `nearAirV3` cap (18)**: honest sorted ids,
at most `2048` (aligned height `≤ 16`). -/
theorem sort_aligned_complete (S : List (Nat × List Nat)) (ok : SortGeneral.IdsOk S) (hn : S.length ≤ 2048)
    (t : Nat) (pub : List Fp) :
    TableLocal { Sort.table with maxLog := 18 } (sortTraceAligned S) t pub ∧
    TableTraffic Sort.table.interactions (sortTraceAligned S) t pub (sortTraffic S) ∧
    (sortTraceAligned S).log t % 3 = 1 :=
  sort_aligned_core S ok (by omega) 18
    (Nat.le_trans (padded_log_le _ 16 (by decide) (by decide) (by omega)) (by decide)) t pub

/-- **`sortV3` aligned completeness at cap 19** (the cap the receipt bound needs): every honest
sorted id list of at most `8192` ids. -/
theorem sort_aligned_complete19 (S : List (Nat × List Nat)) (ok : SortGeneral.IdsOk S) (hn : S.length ≤ 8192)
    (t : Nat) (pub : List Fp) :
    TableLocal { Sort.table with maxLog := 19 } (sortTraceAligned S) t pub ∧
    TableTraffic Sort.table.interactions (sortTraceAligned S) t pub (sortTraffic S) ∧
    (sortTraceAligned S).log t % 3 = 1 :=
  sort_aligned_core S ok hn 19 (padded_log_le _ 19 (by decide) (by decide) (by omega)) t pub

/-- The receipt-level traffic: the sorted ids carry exactly the indexed receipt-id bytes
`sortTraffic (input rs)` (sorting permutes the messages). -/
theorem sortTraffic_sorted (rs : List NearSpec.Receipt) (b : Nat) (m : List Fp) :
    (((sortTraffic (NativeSortIds.sorted rs)).recvs b).map Msg.toFp).count m =
      (((sortTraffic (NativeSortIds.input rs)).recvs b).map Msg.toFp).count m := by
  by_cases hb : b = B_RIDS
  · simp only [sortTraffic, hb, ite_true]
    exact ((List.Perm.flatMap_right
      (fun x : Nat × List Nat => (List.range 32).map (fun j => [x.1, j, x.2.getD j 0]))
      (NativeSortIds.permutation rs)).map Msg.toFp).count_eq m
  · simp [sortTraffic, hb]

/-- **Receipt-level `sortV3` aligned completeness at cap 19**: nonempty, well-formed receipts
with distinct ids, at most `8192`, with the soundness traffic `sortTraffic (input rs)`. -/
theorem sort_receipts_aligned_complete19 (rs : List NearSpec.Receipt) (hne : rs ≠ [])
    (hw : ∀ r ∈ rs, r.wf = true) (hd : (rs.map NearSpec.Receipt.receiptId).Nodup)
    (hn : rs.length ≤ 8192) (t : Nat) (pub : List Fp) :
    TableLocal { Sort.table with maxLog := 19 } (sortTraceAligned (NativeSortIds.sorted rs)) t pub ∧
    TableTraffic Sort.table.interactions (sortTraceAligned (NativeSortIds.sorted rs)) t pub
      (sortTraffic (NativeSortIds.input rs)) ∧
    (sortTraceAligned (NativeSortIds.sorted rs)).log t % 3 = 1 := by
  have ok : SortGeneral.IdsOk (NativeSortIds.sorted rs) :=
    ⟨by rw [NativeSortIds.length]; exact List.length_pos_iff.mpr hne, NativeSortIds.bytes rs hw,
      NativeSortIds.strict rs hw hd⟩
  obtain ⟨h1, h2, h3⟩ := sort_aligned_complete19 _ ok (by rw [NativeSortIds.length]; exact hn) t pub
  refine ⟨h1, ?_, h3⟩
  intro b m
  obtain ⟨hs, hr⟩ := h2 b m
  exact ⟨hs, hr.trans (sortTraffic_sorted rs b m)⟩


/-! ## The repaired `nearAirV3` sort table (`sortTableV3`, cap 19, empty input allowed) -/

namespace SortV3
open ZkFormal.NearV3.Assembly

/-- The aligned `sortV3` trace of a receipt list: the silent one-row-pair table for no receipts,
else the sorted ids. -/
def sortTraceV3 (rs : List NearSpec.Receipt) : Trace Fp :=
  if rs = [] then rowsTrace 1 (mkTab 2 Sort.width (fun _ _ => 0))
  else sortTraceAligned (NativeSortIds.sorted rs)

theorem tableLocal_recap {T : ZkFormal.Air.Table} {tr : Trace Fp} {t : Nat} {pub : List Fp}
    (m : Nat) (h : TableLocal T tr t pub) (hm : tr.log t ≤ m) :
    TableLocal { T with maxLog := m } tr t pub := ⟨h.log_ge, hm, h.constr, h.bits⟩

/-- **`sortV3` aligned completeness for `nearAirV3`'s repaired table** (any number of
well-formed receipts with distinct ids, at most `8192`, including none). -/
theorem sort_v3_aligned_complete (rs : List NearSpec.Receipt)
    (hw : ∀ r ∈ rs, r.wf = true) (hd : (rs.map NearSpec.Receipt.receiptId).Nodup)
    (hn : rs.length ≤ 8192) (t : Nat) (pub : List Fp) :
    TableLocal sortTableV3 (sortTraceV3 rs) t pub ∧
    TableTraffic sortTableV3.interactions (sortTraceV3 rs) t pub
      (sortTraffic (NativeSortIds.input rs)) ∧
    (sortTraceV3 rs).log t % 3 = 1 := by
  by_cases he : rs = []
  · subst he
    have hl : (SortEmpty.emptyTrace).log t = (sortTraceV3 []).log t := rfl
    have hc : ∀ r, r < (SortEmpty.emptyTrace).height t → ∀ c,
        (SortEmpty.emptyTrace).cell t r c = (sortTraceV3 []).cell t r c := by
      intro r hr c
      have hr' : r < 2 ^ 1 := hr
      show (0 : Fp) = (rowsTrace 1 (mkTab 2 Sort.width (fun _ _ => 0))).cell t r c
      rw [rowsTrace_cells 1 _ _ (fun _ _ _ => rfl) t r hr' c]; rfl
    refine ⟨tableLocal_congr_rows hl hc
        (tableLocal_recap 19 (SortEmpty.empty_local t pub) (show 1 ≤ 19 by decide)),
      tableTraffic_congr_rows hl hc ?_, rfl⟩
    intro b m
    refine ⟨?_, ?_⟩ <;>
      rw [show sortTableV3.interactions = SortEmpty.table.interactions from rfl,
        SortEmpty.empty_count] <;>
      simp [sortTraffic, NativeSortIds.input]
  · obtain ⟨h1, h2, h3⟩ := sort_receipts_aligned_complete19 rs he hw hd hn t pub
    simp only [sortTraceV3, if_neg he]
    exact ⟨SortEmpty.v3_old_local _ t pub h1, h2, h3⟩

end SortV3

namespace SortV3
open NearSpec NearSpecV3 ZkFormal.NearV3.Assembly

/-- **`sortV3` render for an accepted witness**, emitting exactly the receipt lane's RIDS traffic
`sortTraffic (NativeSortIds.input (lists.flatten.map Input.receipt))` whenever the receipt lists
flatten to the applied receipts. -/
theorem sort_v3_accepted {cb wb raw : Bytes} {k : WalkD0} {w : StateWitness} {m : MainExecutionV3}
    (hk : walkD0 cb = .ok k) (hw : decodeW wb = .ok w) (hr : decodeStateWitness raw = .ok w)
    (hc : checkD0a B0 cb wb = .ok ()) (hm : m.NativeValid k w)
    (lists : List (List RcptSkeleton.Input))
    (hls : lists.flatten.map RcptSkeleton.Input.receipt = appliedReceipts k w) (t : Nat) (pub : List Fp) :
    TableLocal sortTableV3 (sortTraceV3 (lists.flatten.map RcptSkeleton.Input.receipt)) t pub ∧
    TableTraffic sortTableV3.interactions (sortTraceV3 (lists.flatten.map RcptSkeleton.Input.receipt)) t pub
      (sortTraffic (NativeSortIds.input (lists.flatten.map RcptSkeleton.Input.receipt))) ∧
    (sortTraceV3 (lists.flatten.map RcptSkeleton.Input.receipt)).log t % 3 = 1 := by
  rw [hls]
  have hrel : RelD0a B0 cb wb := (relD0a_iff B0 cb wb).mpr hc
  have hg : (m.ctx k).gasLimit ≤ maxGasLimitD0 := by
    change k.slotB2.gasLimit ≤ maxGasLimitD0
    simpa only [a1, hk, decide_eq_true_eq] using hrel.2.1
  have hn := applyNewChunk_receipt_bound hm.run hg
  unfold checkD0a at hc
  obtain ⟨u, hc0, _⟩ := ReexecV3D0.bind_ok' hc
  cases u
  exact sort_v3_aligned_complete _ (appliedReceipts_wf hr) (checkD0_applied_nodup hk hw hc0)
    (by omega) t pub

end SortV3
end ZkFormal.NearV3.Render
