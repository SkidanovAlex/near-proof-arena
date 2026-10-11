import ZkFormal.NearV3.Render.PaddedCongr
import ZkFormal.NearV3.Candidates.SchedLocalHeight

/-!
# Aligned scheduler generators: comparator `scpV3` (table 15) and memory `smmV3` (table 14)

The scheduler tables share the physical clock `2^22` (`Candidates/SchedHeight`): `22 ≡ 1 (mod 3)`
is the scheduler cap of `nearAirV3`, so the honest scheduler traces are roll-aligned at that
height.  `schedTraceAligned rows pad` is the array-backed form (`rowsTrace 22`) of
`SchedHeight.trace rows pad` (generated rows, then the padding rows `pad r`); it agrees with it on
every row of the table, so local legality and traffic transfer (`PaddedCongr`).

Entries are the scheduler generators' inputs (`Gen.Cmp` comparisons, `Gen.Mem` runs); traffic is
the exact expected lists of `Sched/Complete` (`Gen.Cmp.expected`, `sopList`/`finList`/`cmpList`).
-/
namespace ZkFormal.NearV3.Render
open ZkFormal.Near ZkFormal.Near.Render ZkFormal.Air ZkFormal.Algebra ZkFormal.Size
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen ZkFormal.NearV3.Sched.Complete
open ZkFormal.NearV3.Candidates

/-- The array-backed scheduler trace at the shared clock `2^22`. -/
def schedTraceAligned (rows : Array (Array Nat)) (pad : Nat → Array Nat) : Trace Fp :=
  rowsTrace 22 ((Array.range (2 ^ 22)).map (natRow rows pad))

theorem schedTraceAligned_log (rows : Array (Array Nat)) (pad : Nat → Array Nat) (t : Nat) :
    (schedTraceAligned rows pad).log t = 22 := rfl

theorem schedTraceAligned_cells (rows : Array (Array Nat)) (pad : Nat → Array Nat) (t : Nat) :
    ∀ r, r < (SchedHeight.trace rows pad).height t → ∀ c,
      (SchedHeight.trace rows pad).cell t r c = (schedTraceAligned rows pad).cell t r c := by
  intro r hr c
  have hr' : r < 2 ^ 22 := hr
  show Fp.ofNat (natCell rows pad r c) = Fp.ofNat ((((Array.range (2 ^ 22)).map (natRow rows pad)).getD r #[]).getD c 0)
  simp [Array.getD_eq_getD_getElem?, hr', natCell, gd]

/-! ## `scpV3` (table 15) -/

def cmpTraceAligned (cmps : List (Nat × Nat × Nat)) : Trace Fp :=
  schedTraceAligned (Gen.Cmp.rows cmps) (fun _ => Gen.Cmp.padRow)

/-- The comparator traffic: receives `Gen.Cmp.expected cmps` on `B_SCMP`, sends nothing. -/
def cmpTraffic (cmps : List (Nat × Nat × Nat)) : Traffic :=
  ⟨fun _ => [], fun b => if b = B_SCMP then Gen.Cmp.expected cmps else []⟩

/-- **`scpV3` aligned completeness**: honest comparisons (`CmpOk`: operands `< 2^29`,
`b = [y ≤ x]`) fitting the table. -/
theorem cmp_aligned_complete (cmps : List (Nat × Nat × Nat)) (hok : ∀ q ∈ cmps, CmpOk q)
    (hrows : cmps.length ≤ 2 ^ 22) (t : Nat) (pub : List Fp) :
    TableLocal (Cmp.table B_SCMP) (cmpTraceAligned cmps) t pub ∧
    TableTraffic (Cmp.table B_SCMP).interactions (cmpTraceAligned cmps) t pub (cmpTraffic cmps) ∧
    (cmpTraceAligned cmps).log t % 3 = 1 := by
  have hl : (CmpHeight.trace cmps).log t = (cmpTraceAligned cmps).log t := rfl
  have hc := schedTraceAligned_cells (Gen.Cmp.rows cmps) (fun _ => Gen.Cmp.padRow) t
  refine ⟨tableLocal_congr_rows hl hc (SchedLocalHeight.cmp_local cmps hok B_SCMP t pub),
    tableTraffic_congr_rows hl hc ?_, show 22 % 3 = 1 from rfl⟩
  intro b m
  show tableBusCount (Cmp.interactions B_SCMP) _ t pub b true m = _ ∧
    tableBusCount (Cmp.interactions B_SCMP) _ t pub b false m = _
  by_cases hb : b = B_SCMP
  · subst hb
    rw [CmpHeight.cmp_count cmps B_SCMP t pub m true hrows,
      CmpHeight.cmp_count cmps B_SCMP t pub m false hrows]
    simp [cmpTraffic, fmsgs] <;> rfl
  · have hoff : ∀ i ∈ Cmp.interactions B_SCMP, i.bus ≠ b := by
      intro i hi
      simp only [Cmp.interactions, List.mem_cons, List.not_mem_nil, or_false] at hi
      subst hi; exact fun h => hb h.symm
    rw [tableBusCount_off_bus _ _ _ _ _ _ _ hoff, tableBusCount_off_bus _ _ _ _ _ _ _ hoff]
    simp [cmpTraffic, hb]

/-! ## `smmV3` (table 14) -/

def memTraceAligned (R : Run) : Trace Fp := schedTraceAligned (Gen.Mem.rows R) memPad

/-- The memory traffic: receives the INITs and the op log on `B_SOP`, sends the final values on
`B_SFIN` and the comparisons on `B_SCMP`. -/
def memTraffic (R : Run) : Traffic :=
  ⟨fun b => if b = B_SFIN then finList R.segs else if b = B_SCMP then cmpList R.segs else [],
   fun b => if b = B_SOP then sopList R.segs else []⟩

/-- **`smmV3` aligned completeness**: honest segments (`SegOk`) fitting the table with one
padding row. -/
theorem mem_aligned_complete (R : Run) (hg : ∀ g ∈ R.segs, SegOk g)
    (hrows : (memVs R.segs).length + 1 ≤ 2 ^ 22) (t : Nat) (pub : List Fp) :
    TableLocal Mem.table (memTraceAligned R) t pub ∧
    TableTraffic Mem.table.interactions (memTraceAligned R) t pub (memTraffic R) ∧
    (memTraceAligned R).log t % 3 = 1 := by
  have hl : (MemHeight.trace R).log t = (memTraceAligned R).log t := rfl
  have hc := schedTraceAligned_cells (Gen.Mem.rows R) memPad t
  refine ⟨tableLocal_congr_rows hl hc (SchedLocalHeight.mem_local R hg hrows t pub),
    tableTraffic_congr_rows hl hc ?_, show 22 % 3 = 1 from rfl⟩
  have hnil : ∀ b s, ¬ (b = B_SOP ∧ s = false) → ¬ (b = B_SFIN ∧ s = true) →
      ¬ (b = B_SCMP ∧ s = true) → (memVs R.segs).flatMap (rowMsgs b s) = [] := by
    intro b s h1 h2 h3
    rw [List.flatMap_eq_nil_iff]
    intro X _
    exact rowMsgs_other h1 h2 h3 X
  intro b m
  show tableBusCount Mem.interactions _ t pub b true m = _ ∧
    tableBusCount Mem.interactions _ t pub b false m = _
  rw [MemHeight.mem_traffic R hg hrows t pub b true m, MemHeight.mem_traffic R hg hrows t pub b false m]
  refine ⟨?_, ?_⟩
  · by_cases h2 : b = B_SFIN
    · subst h2; rw [fin_list]; simp [memTraffic, fmsgs] <;> rfl
    · by_cases h3 : b = B_SCMP
      · subst h3; rw [cmp_list R.segs hg]; simp [memTraffic, fmsgs, B_SFIN, B_SCMP] <;> rfl
      · rw [hnil b true (by simp) (by simp [h2]) (by simp [h3])]
        simp [memTraffic, h2, h3, fmsgs]
  · by_cases h1 : b = B_SOP
    · subst h1; rw [sop_list R.segs hg]; simp [memTraffic, fmsgs] <;> rfl
    · rw [hnil b false (by simp [h1]) (by simp) (by simp)]
      simp [memTraffic, h1, fmsgs]

end ZkFormal.NearV3.Render
