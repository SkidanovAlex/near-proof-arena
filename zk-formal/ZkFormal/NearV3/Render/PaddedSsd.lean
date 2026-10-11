import ZkFormal.NearV3.Render.SsdScanGen
import ZkFormal.NearV3.Render.SsdDistGen
import ZkFormal.NearV3.Render.RowTraffic
import ZkFormal.NearV3.Candidates.ProcScanDistPhases
import ZkFormal.NearV3.Candidates.ProcDistComparisonValid

/-!
# Aligned `ssdV3` render (`nearAirV3` table 12, the frozen `ScanDist.table`) over all runs

For the native scheduler blocks of an accepted witness (`PriorCore p B bs`) the honest merged
table — every run's scan rows, then every run's distribute rows, then zero padding, at the
scheduler's shared height `2^22` (`ProcScanDistPhases.trace bs`) — satisfies
`TableLocal ScanDist.table` (`ssd_local`): its rows are the rows of one descriptor chain
(`ssd_descs`), assembled from the per-run blocks (`scan_block`, `dist_block`), and
`Ssd.table_local` applies.  The traffic is the exact trace-free row traffic (`rowFn_traffic`):
every `ScanDist` interaction reads the current row only.
-/
namespace ZkFormal.NearV3.Render.Ssd
open ZkFormal.Near ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen
open ZkFormal.NearV3.Candidates ZkFormal.NearV3.Assembly.CodecDigest
open ProcNativeOldComparisonCapacity

/-- The native facts of one block of an accepted witness. -/
theorem block_facts {cb : NearSpec.Bytes} {hint : NearSpecV3.Hint} {p : NearSpecV3.Prep}
    (hp : NearSpecV3.prepD0 cb hint = .ok p) {B : Nat} (bs : List NativeBlock) (hc : PriorCore p B bs)
    (b : NativeBlock) (hb : b ∈ bs) :
    ActualRun.run (ProcPreparedSequence.input b.pub b.old) b.run.tau = .ok b.run ∧
    NearSpecV3.Scheduler.Params.calculate NearSpecV3.Scheduler.Config.pv86
      (ProcPreparedSequence.input b.pub b.old).ids.length = some (ProcPreparedSequence.input b.pub b.old).p ∧
    b.run.n ≤ 64 ∧ b.run.tau < P ∧ b.run.n < P ∧ ProcDistShardValid.Budget b.run ∧
    (ProcPreparedSequence.input b.pub b.old).p.maxShardBandwidth = 4500000 := by
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hb
  have hidx := hc.indexed i b hi
  have hs := prepD0_sched hp b.pub (List.mem_iff_getElem?.mpr ⟨i, hidx.1.1⟩)
  have hr : ActualRun.run (ProcPreparedSequence.input b.pub b.old) b.run.tau = .ok b.run := by
    rw [hidx.2.1]; exact hidx.1.2
  have hpar := (ProcPreparedSequence.input_bounds b.pub b.old hs).1
  have hmax := ZkFormal.NearV3.Sched.pv86_maxShard hpar
  have hn := (hc.valid b hb).2
  have hil : i < bs.length := (List.getElem?_eq_some_iff.mp hi).1
  have hlen := hc.length
  have hbud := ProcActualFinalBudgets.run _ _ _ hr
  rw [hmax] at hbud
  refine ⟨hr, hpar, hn, ?_, ?_, hbud, hmax⟩
  · rw [hidx.2.1]; unfold P; omega
  · unfold P; omega

/-- The distribute descriptors of the whole witness. -/
theorem dist_all {cb : NearSpec.Bytes} {hint : NearSpecV3.Hint} {p : NearSpecV3.Prep}
    (hp : NearSpecV3.prepD0 cb hint = .ok p) {B : Nat} (bs : List NativeBlock) (hc : PriorCore p B bs) :
    ∀ cs : List NativeBlock, (∀ b ∈ cs, b ∈ bs) →
    ∃ D : List Desc, cs.flatMap (fun b => (distribution b).rows.toList) = D.map Desc.row ∧ Chain D ∧
      (∀ x ∈ D, x.Valid) ∧ (∀ x, D.head? = some x → DistStart x) ∧
      (∀ x, D.getLast? = some x → x.Final) ∧ (∀ b ∈ cs, 0 < b.run.n → D ≠ []) := by
  intro cs hcs
  induction cs with
  | nil => exact ⟨[], rfl, chain_nil, fun _ h => by simp at h, fun _ h => by simp at h,
      fun _ h => by simp at h, fun _ h => by simp at h⟩
  | cons b cs ih =>
    obtain ⟨D, hD, hDc, hDv, hDh, hDl, hDn⟩ := ih (fun x hx => hcs x (List.mem_cons_of_mem _ hx))
    obtain ⟨hr, hpar, hn, ht, _, hbud, hmax⟩ := block_facts hp bs hc b (hcs b (List.mem_cons_self ..))
    obtain ⟨ds, hds, hc', hv, hh, hl, hne⟩ :=
      dist_block _ _ hn hbud hmax ht (distribution b) (distribution_eq b hn)
    refine ⟨ds ++ D, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [List.flatMap_cons, hds, hD, List.map_append]
    · apply chain_append _ _ hc' hDc
      intro x y hx hy
      obtain ⟨tv, n, x', c, l, bud, rfl⟩ := hDh y hy
      have hf := hl x hx
      cases x with
      | cell ids tv n i j sv rr n1 l1 n2 l2 al =>
        exact ⟨hf.2, hf.1, rfl, rfl, rfl⟩
      | _ => exact hf.elim
    · intro x hx
      rcases List.mem_append.mp hx with h | h
      · exact hv x h
      · exact hDv x h
    · intro x hx
      rw [List.head?_append] at hx
      cases hg : ds.head? with
      | none => rw [hg] at hx; exact hDh x (by simpa using hx)
      | some z => rw [hg] at hx; simp at hx; subst hx; exact hh _ hg
    · intro x hx
      rw [List.getLast?_append] at hx
      cases hg : D.getLast? with
      | none => rw [hg] at hx; exact hl x (by simpa using hx)
      | some z => rw [hg] at hx; simp at hx; subst hx; exact hDl _ hg
    · intro b' hb' hpos
      rcases List.mem_cons.mp hb' with rfl | hb'
      · have := hne hpos
        intro h; exact this (List.append_eq_nil_iff.mp h).1
      · have := hDn b' hb' hpos
        intro h; exact this (List.append_eq_nil_iff.mp h).2

/-- **The honest `ssdV3` rows are one descriptor chain.** -/
theorem ssd_descs {cb : NearSpec.Bytes} {hint : NearSpecV3.Hint} {p : NearSpecV3.Prep}
    (hp : NearSpecV3.prepD0 cb hint = .ok p) {B : Nat} (bs : List NativeBlock) (hc : PriorCore p B bs) :
    ∃ ds : List Desc, ProcScanDistPhases.rows bs = (ds.map Desc.row).toArray ∧ Chain ds ∧
      (∀ d ∈ ds, d.Valid) ∧ (∀ h : 0 < ds.length, (ds[0]'h).FirstOk) ∧
      (∀ h : ds.length - 1 < ds.length, (ds[ds.length - 1]'h).Final) := by
  -- scan part
  have hS := chain_flatten (bs.map (fun b => scanDescs b.run)) ScanStart ScanEnd
    (fun x y hx hy => by
      obtain ⟨R, c, rfl⟩ := hx; obtain ⟨R', rfl⟩ := hy; exact rfl)
    (by
      intro L hL
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hL
      obtain ⟨hr, hpar, _, ht, hn, _, _⟩ := block_facts hp bs hc b hb
      obtain ⟨_, hch, _, hh, hl, _⟩ := scan_block _ _ _ hr hpar ht hn
      exact ⟨hch, hh, hl⟩)
  obtain ⟨D, hD, hDc, hDv, hDh, hDl, hDn⟩ := dist_all hp bs hc bs (fun _ h => h)
  let S := (bs.map (fun b => scanDescs b.run)).flatten
  have hSrows : ProcScanDistPhases.scanRows bs = S.map Desc.row := by
    unfold ProcScanDistPhases.scanRows
    simp only [S, List.map_flatten, List.map_map, List.flatMap_def]
    congr 1
    apply List.map_congr_left
    intro b _
    exact scan_rows b.run
  have hSv : ∀ d ∈ S, d.Valid := by
    intro d hd
    obtain ⟨L, hL, hd⟩ := List.mem_flatten.mp hd
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hL
    obtain ⟨hr, hpar, _, ht, hn, _, _⟩ := block_facts hp bs hc b hb
    exact (scan_block _ _ _ hr hpar ht hn).2.2.1 d hd
  have hSnz : S ≠ [] → D ≠ [] := by
    intro hne
    obtain ⟨d, hd⟩ := List.exists_mem_of_ne_nil S hne
    obtain ⟨L, hL, hd⟩ := List.mem_flatten.mp hd
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hL
    obtain ⟨hr, hpar, _, ht, hn, _, _⟩ := block_facts hp bs hc b hb
    have hpos := (scan_block _ _ _ hr hpar ht hn).2.2.2.2.2 (List.ne_nil_of_mem hd)
    exact hDn b hb hpos
  refine ⟨S ++ D, ?_, ?_, ?_, ?_, ?_⟩
  · unfold ProcScanDistPhases.rows
    rw [hSrows, ProcScanDistPhases.distRows, hD, List.map_append]
  · apply chain_append _ _ hS.1 hDc
    intro x y hx hy
    obtain ⟨R, c, rfl⟩ := hS.2.2 x hx
    obtain ⟨tv, n, x', c', l, bud, rfl⟩ := hDh y hy
    exact ⟨rfl, rfl, rfl, rfl⟩
  · intro d hd
    rcases List.mem_append.mp hd with h | h
    · exact hSv d h
    · exact hDv d h
  · intro h
    have h0 : (S ++ D).head? = some (S ++ D)[0] := List.head?_eq_getElem?.trans (List.getElem?_eq_getElem h)
    rw [List.head?_append] at h0
    cases hg : S.head? with
    | none =>
      rw [hg] at h0
      simp only [Option.none_or] at h0
      obtain ⟨tv, n, x, c, l, bud, he⟩ := hDh _ h0
      rw [he]; exact ⟨rfl, rfl, rfl⟩
    | some z =>
      rw [hg] at h0
      simp only [Option.some_or, Option.some.injEq] at h0
      obtain ⟨R, he⟩ := hS.2.1 z hg
      rw [← h0, he]; trivial
  · intro h
    have h0 : (S ++ D).getLast? = some (S ++ D)[(S ++ D).length - 1] := by
      rw [List.getLast?_eq_getElem?]; exact List.getElem?_eq_getElem h
    rw [List.getLast?_append] at h0
    cases hg : D.getLast? with
    | none =>
      exfalso
      have hDe : D = [] := by simpa using hg
      have hSe : S = [] := by
        by_cases hs : S = []
        · exact hs
        · exact absurd hDe (hSnz hs)
      simp [hSe, hDe] at h
    | some z =>
      rw [hg] at h0
      simp only [Option.some_or, Option.some.injEq] at h0
      rw [← h0]; exact hDl z hg

/-- Cell `c` of row `r` of the honest merged table. -/
def ssdCell (bs : List NativeBlock) (r c : Nat) : Nat :=
  Complete.natCell (ProcScanDistPhases.rows bs) distPad r c

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem ssd_interactions_current :
    ScanDist.interactions.all (fun i => i.exprs.all ZkFormal.NearV3.Candidates.ShaHeight.currentOnly) = true := by decide +kernel

theorem ssd_currentOnly : CurrentOnly ScanDist.table.interactions := by
  intro i hi e he
  exact List.all_eq_true.mp (List.all_eq_true.mp ssd_interactions_current i hi) e he

/-- **`ssdV3` aligned completeness over all runs** (frozen `ScanDist.table`). -/
theorem ssd_v3_aligned_complete {cb : NearSpec.Bytes} {hint : NearSpecV3.Hint} {p : NearSpecV3.Prep}
    (hp : NearSpecV3.prepD0 cb hint = .ok p) {B : Nat} (bs : List NativeBlock) (hc : PriorCore p B bs)
    (t : Nat) (pub : List Fp) :
    TableLocal ScanDist.table (ProcScanDistPhases.trace bs) t pub ∧
    TableTraffic ScanDist.table.interactions (ProcScanDistPhases.trace bs) t pub
      (rowsTraffic ScanDist.table.interactions (ssdCell bs) 22 t pub) ∧
    (ProcScanDistPhases.trace bs).log t % 3 = 1 := by
  obtain ⟨ds, hrows, hch, hv, hf, hl⟩ := ssd_descs hp bs hc
  have hcap := (ProcScanDistPhases.capacity hp bs hc).2
  rw [hrows] at hcap
  have hlen : ds.length < 2 ^ 22 := by simpa using hcap
  refine ⟨?_, ?_, show 22 % 3 = 1 from rfl⟩
  · unfold ProcScanDistPhases.trace
    rw [hrows]
    exact table_local ds hlen hv (fun k hk => hch k hk) hf hl t pub
  · exact rowFn_traffic _ ssd_currentOnly (ssdCell bs) _ t 22 pub rfl (fun r _ c => rfl)

end ZkFormal.NearV3.Render.Ssd
