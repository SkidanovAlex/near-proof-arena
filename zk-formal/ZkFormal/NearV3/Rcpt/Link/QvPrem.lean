import ZkFormal.NearV3.Rcpt.Link.QvRc
import ZkFormal.NearV3.Qv.Extract.MainReadSequence

/-!
# ZkFormal.NearV3.Rcpt.Link.QvPrem — the read premises of `assemble_native_queue_reads`

From the qv table's constraints, the qv-internal `QSH` / `QVC` balances, `RecComplete` and `Bytes8`
(`QvCodec` supplies all four from `HoldsP`): a shard list `ss` and a tag `htau` with `ss.length < P`,
`hc` (the main buffered read's count is `|ss|`), `hrequests` (every walk `QSH` request is a native
shard message of `ss`), and the read premises `he` (empty indices), `hb` (buffered value), `ha`
(absent buffer ⇒ `ss = []`).

Absent buffered read: the constraint `wl·main·lo·(1-hi)·absent·count = 0` gives `count = 0`, so
there are no group reads (`main_read_prefix`) and no count request (the only one sits on main
read 1, which is absent): the `QSH` request stream is empty.
-/

namespace ZkFormal.NearV3.Qv.Extract.QvRc

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl
open Candidates.CombinedTable
open Candidates.ValueTable (count len vid tau)

theorem cell_of_cv0 {tr : Trace Fp} {t r x : Nat} (h : cv tr t r x = 0) : tr.cell t r x = 0 := by
  have e := Fp.ofNat_toNat (tr.cell t r x)
  unfold cv at h
  rw [← e, h]
  rfl

theorem getD_get {α : Type} {l : List α} {i : Nat} (d : α) (h : i < l.length) :
    l.getD i d = l[i] := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

theorem cv_of_cell0 {tr : Trace Fp} {t r x : Nat} (h : tr.cell t r x = 0) : cv tr t r x = 0 := by
  unfold cv; rw [h]; rfl

variable {tr : Trace Fp} {tt : Nat} {pub : List Fp}
  (hL : TableLocal table tr tt pub) (q : WalkChain tr tt)
include hL

omit hL in
theorem prefix_row {r : Nat} (hr : r < segEnd 0 q.segs) :
    ∃ i, ∃ hi : i < q.segs.length, q.segs[i].1 ≤ r ∧ r < q.segs[i].1 + q.segs[i].2 := by
  have hm : r ∈ List.range' 0 (segEnd 0 q.segs) := by
    simpa only [← List.range_eq_range'] using List.mem_range.mpr hr
  have he := range'_segs q.segs 0 q.consecutive
  simp only [Nat.sub_zero] at he
  rw [he] at hm
  obtain ⟨p, hp, hrow⟩ := List.mem_flatMap.mp hm
  obtain ⟨i, hi, hpi⟩ := List.mem_iff_getElem.mp hp
  have hb := List.mem_range'.mp hrow
  exact ⟨i, hi, by rw [hpi]; omega, by rw [hpi]; omega⟩

/-- With main count `0` there is no group shard request. -/
theorem no_group (h0 : cv tr tt 0 count = 0) {r : Nat} (hr : r < segEnd 0 q.segs) :
    tr.cell tt r groupByte ≠ 1 := by
  intro hg
  obtain ⟨i, hi, h1, h2⟩ := prefix_row q hr
  have hp : q.segs[i] ∈ q.segs := List.getElem_mem hi
  have hend := seg_le_end q.segs 0 q.consecutive _ hp
  have hfit : q.segs[i].1 + q.segs[i].2 ≤ tr.height tt := Nat.le_trans hend.2 q.fits
  have hs := q.valid _ hp
  have hrow : r < tr.height tt := by omega
  have hw := flag_walk hL hrow (x := groupByte) (by simp) hg
  have hh := con hL hrow (e := sub (c groupByte) (mul3 (c walk) group (Dsl.not (c wf))))
    (by simp [constraints])
  simp only [eval_sub, eval_c, eval_mul3, eval_not, group, eval_mul, hg, hw] at hh
  have hlo : tr.cell tt r lo = 1 := by
    rcases isBool hL hrow (x := lo) (by simp [walkBools]) with h | h <;> rw [h] at hh ⊢ <;> grind
  have hhi : tr.cell tt r Candidates.CombinedTable.hi = 1 := by
    rcases isBool hL hrow (x := Candidates.CombinedTable.hi) (by simp [walkBools]) with h | h <;>
      rw [h] at hh ⊢ <;> grind
  have hmain := walk_metadata hL hfit hs (x := main) (by simp) r h1 h2
  have hlo0 := walk_metadata hL hfit hs (x := lo) (by simp) r h1 h2
  have hhi0 := walk_metadata hL hfit hs (x := Candidates.CombinedTable.hi) (by simp) r h1 h2
  rcases isBool hL (show q.segs[i].1 < tr.height tt by omega) (x := main) (by simp [walkBools])
    with hm | hm
  · have hz := con hL hrow (e := mul3 (c walk) (Dsl.not (c main)) (c lo)) (by simp [constraints])
    simp only [eval_mul3, eval_c, eval_not, hw, hmain, hm, hlo] at hz
    grind
  · have hlt := ((main_read_prefix hL q).2 i hi).mp hm
    rw [h0] at hlt
    have hk := WalkChain.main_kind hL q i hi hm
    rw [← hlo0, ← hhi0, hlo, hhi] at hk
    have h10 : (1 : Fp) ≠ 0 := by decide
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 by omega) with rfl | rfl | rfl
    · exact h10 (by simpa using hk.1)
    · exact h10 (by simpa using hk.2)
    · exact h10 (by simpa using hk.1)

/-- **The read premises of `assemble_native_queue_reads`.** -/
theorem queue_premises (v : ParserChain tr tt (segEnd 0 q.segs))
    {vals : List ValE} (hv : ValWf vals) (hrc : RecComplete tr tt pub v.segs vals)
    (hb8 : ∀ e ∈ vals, Bytes8 e.bytes)
    (hqsh : ∀ m, tableBusCount interactions tr tt pub B_QSH true m =
      tableBusCount interactions tr tt pub B_QSH false m)
    (hqvc : ∀ m, tableBusCount interactions tr tt pub Candidates.ValueTable.B_QVC true m =
      tableBusCount interactions tr tt pub Candidates.ValueTable.B_QVC false m) :
    ∃ (ss : List Nat) (htau : Fp), ss.length < P ∧
      (∃ hj : 1 < q.segs.length, cv tr tt (q.segs[1]'hj).1 count = ss.length) ∧
      (∀ m ∈ (List.range (segEnd 0 q.segs)).flatMap
        (fun r => rowTraffic interactions tr tt r pub B_QSH false), m ∈ Parser.nativeShardMessages htau ss) ∧
      (∀ j ∈ [0,2], cv tr tt (q.segs.getD j (0,0)).1 absent = 0 →
        ∃ e ∈ vals, e.vid = cv tr tt (q.segs.getD j (0,0)).1 vid ∧
          EmptyQueue (some (toBytes e.bytes))) ∧
      (cv tr tt (q.segs.getD 1 (0,0)).1 absent = 0 →
        ∃ e ∈ vals, e.vid = cv tr tt (q.segs.getD 1 (0,0)).1 vid ∧
          BufferedValue (some (toBytes e.bytes)) ss) ∧
      (cv tr tt (q.segs.getD 1 (0,0)).1 absent ≠ 0 → ss = []) := by
  obtain ⟨h2, hm0, hm1, hm2⟩ := fixed_main_reads hL q
  have hj : 1 < q.segs.length := by omega
  have hg1 : q.segs.getD 1 (0,0) = q.segs[1] := getD_get _ hj
  -- the empty reads (any shard list)
  have he : ∀ j ∈ [0,2], cv tr tt (q.segs.getD j (0,0)).1 absent = 0 →
      ∃ e ∈ vals, e.vid = cv tr tt (q.segs.getD j (0,0)).1 vid ∧
        EmptyQueue (some (toBytes e.bytes)) := by
    intro j hjm ha
    have hj2 : j = 0 ∨ j = 2 := by simpa using hjm
    have hjl : j < q.segs.length := by omega
    rw [getD_get _ hjl] at ha ⊢
    have hmj : tr.cell tt q.segs[j].1 main = 1 := by rcases hj2 with rfl | rfl <;> assumption
    have hmode := main_read_mode hL q j hjl hmj
    simp only [hj2, ite_true] at hmode
    obtain ⟨e, he, -, hid, -, hval⟩ := empty_read hL q v hv hrc hb8 hqvc q.segs[j]
      (List.getElem_mem hjl) (cell_of_cv0 ha) hmode
    exact ⟨e, he, hid, hval⟩
  -- the buffered read
  have hp1 : q.segs[1] ∈ q.segs := List.getElem_mem hj
  have hend := seg_le_end q.segs 0 q.consecutive _ hp1
  have hfit : q.segs[1].1 + q.segs[1].2 ≤ tr.height tt := Nat.le_trans hend.2 q.fits
  have hs := q.valid _ hp1
  have hk := WalkChain.main_kind hL q 1 hj hm1
  simp only [show ¬(1 = 0 ∨ 1 = 2) from by omega, show 1 < 2 from by omega, ite_true, ite_false] at hk
  have hlen1 := (walk_kind_length hL hfit hs).2 (Or.inr hk.2)
  have hrow1 : q.segs[1].1 < tr.height tt := by omega
  have hwl : tr.cell tt q.segs[1].1 wl = 1 := by
    have := hs.2.2.1
    rw [hlen1, show q.segs[1].1 + 1 - 1 = q.segs[1].1 by omega] at this
    simpa only [isOne, decide_eq_true_eq] using this
  by_cases hab : tr.cell tt q.segs[1].1 absent = 0
  · -- present: the count gate fires
    have hpres : tr.cell tt q.segs[1].1 present = 1 := (present_iff hL hrow1).mpr ⟨hwl, hab⟩
    have hcr : tr.cell tt q.segs[1].1 countRead = 1 :=
      (count_request_gate hL hrow1).mpr ⟨hpres, hm1, hk.1, hk.2⟩
    obtain ⟨e, hev, -, hid, ss, hbuf, hbound, hcnt, hreq⟩ :=
      count_read hL q v hv hrc hb8 hqsh hqvc q.segs[1] hp1 hcr
    refine ⟨ss, tr.cell tt q.segs[1].1 tau, hbound, ⟨hj, hcnt⟩, hreq, he, ?_, ?_⟩
    · intro _; rw [hg1]; exact ⟨e, hev, hid, hbuf⟩
    · intro hne; rw [hg1] at hne; exact absurd (cv_of_cell0 hab) hne
  · -- absent: count 0, no requests
    have hz := con hL hrow1 (e := mul3 (c wl) (.mul (c main) (.mul (c lo) (Dsl.not (c Candidates.CombinedTable.hi))))
      (.mul (c absent) (c count))) (by simp [constraints])
    simp only [eval_mul3, eval_mul, eval_c, eval_not, hwl, hm1, hk.1, hk.2] at hz
    have hc0 : tr.cell tt q.segs[1].1 count = 0 := by
      rcases isBool hL hrow1 (x := absent) (by simp [walkBools]) with h | h
      · exact absurd h hab
      · rw [h] at hz; grind
    have hcc := WalkChain.main_count_constant hL q 1 hj hm1
    have h0 : cv tr tt 0 count = 0 := by
      apply cv_of_cell0; rw [← hcc]; exact hc0
    refine ⟨[], 0, by decide, ⟨hj, cv_of_cell0 hc0⟩, ?_, he, ?_, fun _ => rfl⟩
    · intro m hm
      exfalso
      obtain ⟨r, hr, hmr⟩ := List.mem_flatMap.mp hm
      have hr' := List.mem_range.mp hr
      rw [shard_receive_row] at hmr
      have hng := no_group hL q h0 hr'
      have hnc : tr.cell tt r countRead ≠ 1 := by
        intro hcr
        obtain ⟨i, hi, h1, h2⟩ := prefix_row q hr'
        obtain ⟨rfl, rfl⟩ := indexed_count_request hL q i hi r h1 h2 hcr
        exact hab (count_request_read_mode hL hrow1 hcr).1
      simp [hng, hnc] at hmr
    · intro habs
      exact absurd (cell_of_cv0 (by rw [hg1] at habs; exact habs)) hab

end ZkFormal.NearV3.Qv.Extract.QvRc
