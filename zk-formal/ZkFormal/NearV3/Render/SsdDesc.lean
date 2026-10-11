import ZkFormal.NearV3.Render.SsdShardLocal
import ZkFormal.NearV3.Candidates.ProcDistCellLocal
import ZkFormal.NearV3.Candidates.ProcDistHeaderPhysical
import ZkFormal.NearV3.Candidates.ProcScanParamPhysical
import ZkFormal.NearV3.Candidates.ProcScanRequestNativeLocal
import ZkFormal.NearV3.Candidates.ProcScanRequestState
import ZkFormal.NearV3.Candidates.ProcScanRequestQuietCells
import ZkFormal.NearV3.Candidates.ScanPadding
import ZkFormal.NearV3.Candidates.ProcDistCmpPhysical

/-!
# Row descriptors of the honest `ssdV3` table and local legality from a descriptor chain

The honest rows of `ScanDist.table` (table 12) are of five kinds, each with a proved row-level
local lemma: the scan param row (`ProcScanParamPhysical`), the 20 rows of a converted request
(`ProcScanRequestNativeLocal`), the distribute shard rows (`SsdShard.physical`), the grid headers
(`ProcDistHeaderPhysical`) and the grid cells (`ProcDistCellLocal`).  `Desc` names a row by its
generator parameters; `Desc.Valid` collects the row lemma's own premises and `Adj d d'` the
admissible successor descriptors (exactly what the row lemma asks of the next row).

`table_local`: a nonempty descriptor list with valid entries, admissible successors, a first
entry that may sit on row 0 (`FirstOk`), a last entry that may be followed by zero padding
(`Final`) and fewer than `2^22` entries renders (`SchedHeight.trace … distPad`, the scheduler's
shared height `2^22`) to a trace with `TableLocal ScanDist.table` — constraints on every row and
boolean multiplicities (derived from the constraints, `bits_of_constraints`).
-/
namespace ZkFormal.NearV3.Render.Ssd
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen
open ZkFormal.NearV3.Candidates

/-- A row of the honest `ssdV3` table, by its generator parameters. -/
inductive Desc where
  | param (R : Run)
  | req (R : Run) (c : CReq) (rho : Nat)
  | shard (tv n sd i x count left budget kp : Nat)
  | header (tv n i sv count left : Nat)
  | cell (ids : List Nat) (tv n i j sv rr n1 l1 n2 l2 : Nat) (al : Bool)

namespace Desc

def row : Desc → Array Nat
  | param R => Scan.paramRow R
  | req R c rho => (Scan.reqRows R c)[rho]!
  | shard tv n sd i x count left budget kp => ProcDistShardRow.row tv n sd i x count left budget kp
  | header tv n i sv count left => ProcDistHeader.row tv n i sv count left
  | cell ids tv n i j sv rr n1 l1 n2 l2 al => ProcDistCellRow.row ids tv n i j sv rr n1 l1 n2 l2 al

/-- The row lemma's own premises. -/
def Valid : Desc → Prop
  | param R => ∃ I tau, ActualRun.run I tau = .ok R ∧ R.tau < P ∧ R.n < P
  | req R c rho => ∃ I tau, ActualRun.run I tau = .ok R ∧
      NearSpecV3.Scheduler.Params.calculate NearSpecV3.Scheduler.Config.pv86 I.ids.length = some I.p ∧
      c ∈ R.conv ∧ rho < 20
  | shard tv n sd i x count left budget kp => (sd = 0 ∨ sd = 1) ∧ budget < 256 ^ 3 ∧ count ≤ 64 ∧
      left ≤ 4500000 ∧ x < 64 ∧ i < n ∧ n ≤ 64 ∧ tv < P ∧ kp < P
  | header tv n i sv count left => tv < P ∧ n < P ∧ i < P ∧ sv < P ∧ count < P ∧ left < P
  | cell _ _ n i j _ _ n1 l1 n2 l2 al => i < n ∧ j < n ∧ n ≤ 64 ∧ n1 ≤ 64 ∧ n2 ≤ 64 ∧
      l1 ≤ 4500000 ∧ l2 ≤ 4500000 ∧ (al = true → 0 < n1 ∧ 0 < n2)

/-- The admissible successors. -/
def Adj : Desc → Desc → Prop
  | param R, req R' c rho => R = R' ∧ c.cid = 0 ∧ rho = 0
  | req R c rho, req R' c' rho' =>
      (rho < 19 ∧ R = R' ∧ c = c' ∧ rho' = rho + 1) ∨ (rho = 19 ∧ R = R' ∧ c'.cid = c.cid + 1 ∧ rho' = 0)
  | req _ _ rho, param _ => rho = 19
  | req _ _ rho, shard _ _ sd i _ _ _ _ kp => rho = 19 ∧ sd = 0 ∧ i = 0 ∧ kp = 0
  | shard tv n sd i x count left _ _, shard tv' n' sd' i' _ _ _ _ kp' =>
      tv = tv' ∧ n = n' ∧
      ((i + 1 < n ∧ sd = sd' ∧ i' = i + 1 ∧ kp' = SsdShard.key count left x + 1) ∨
       (i + 1 = n ∧ sd = 0 ∧ sd' = 1 ∧ i' = 0 ∧ kp' = 0))
  | shard tv n sd i _ _ _ _ _, header tv' n' i' _ _ _ => tv = tv' ∧ n = n' ∧ i + 1 = n ∧ sd = 1 ∧ i' = 0
  | header tv n i sv count left, cell _ tv' n' i' j' sv' _ n1 l1 _ _ _ =>
      tv = tv' ∧ n = n' ∧ i = i' ∧ j' = 0 ∧ sv = sv' ∧ count = n1 ∧ left = l1
  | cell ids tv n i j sv _ n1 l1 n2 l2 al, cell ids' tv' n' i' j' sv' _ n1' l1' _ _ _ =>
      ids = ids' ∧ tv = tv' ∧ n = n' ∧ i = i' ∧ j + 1 < n ∧ j' = j + 1 ∧ sv = sv' ∧
      n1' = n1 - b2n al ∧ l1' = l1 - ProcDistCellRow.grant al n1 l1 n2 l2
  | cell _ tv n i j _ _ _ _ _ _ _, header tv' n' i' _ _ _ =>
      j + 1 = n ∧ i + 1 < n ∧ tv = tv' ∧ n = n' ∧ i' = i + 1
  | cell _ _ n i j _ _ _ _ _ _ _, shard _ _ sd i' _ _ _ _ kp => j + 1 = n ∧ i + 1 = n ∧ sd = 0 ∧ i' = 0 ∧ kp = 0
  | _, _ => False

/-- May be followed by zero padding. -/
def Final : Desc → Prop
  | cell _ _ n i j _ _ _ _ _ _ _ => i + 1 = n ∧ j + 1 = n
  | _ => False

/-- May sit on row 0. -/
def FirstOk : Desc → Prop
  | param _ => True
  | shard _ _ sd i _ _ _ _ kp => sd = 0 ∧ i = 0 ∧ kp = 0
  | _ => False

end Desc

open Desc

def rowO : Option Desc → Array Nat
  | none => zrow Dist.width
  | some d => d.row

def AdjO (d : Desc) : Option Desc → Prop
  | none => d.Final
  | some d' => d.Adj d'

/-! ## Cell values of the five row kinds -/

theorem zrow_cell (c : Nat) : (zrow Dist.width)[c]! = 0 := by
  unfold zrow
  by_cases h : c < Dist.width
  · rw [getElem!_pos _ c (by simpa using h)]; simp
  · rw [getElem!_neg _ c (by simpa using h)]; rfl

theorem header_cells (tv n i sv count left : Nat) :
    (ProcDistHeader.row tv n i sv count left)[Dist.kGH]! = 1 ∧
    (ProcDistHeader.row tv n i sv count left)[Dist.a]! = i ∧
    (ProcDistHeader.row tv n i sv count left)[Dist.tau]! = tv ∧
    (ProcDistHeader.row tv n i sv count left)[Dist.nn]! = n ∧
    (ProcDistHeader.row tv n i sv count left)[Dist.kp]! = 0 ∧
    (ProcDistHeader.row tv n i sv count left)[Dist.kC]! = 0 := by
  simp only [ProcDistHeaderPhysical.row_all]
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem param_cells (R : Run) :
    (Scan.paramRow R)[Scan.kS]! = 0 ∧ (Scan.paramRow R)[Scan.fQ]! = 0 ∧
    (Scan.paramRow R)[Dist.kGH]! = 0 ∧ (Scan.paramRow R)[Dist.kC]! = 0 ∧
    (Scan.paramRow R)[Dist.kSh]! = 0 := by
  simp only [ProcScanParamPhysical.row_all]
  refine ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem cell_n1l1 (ids : List Nat) (tv n i j sv rr n1 l1 n2 l2 : Nat) (al : Bool) :
    (ProcDistCellRow.row ids tv n i j sv rr n1 l1 n2 l2 al)[Dist.N1]! = n1 ∧
    (ProcDistCellRow.row ids tv n i j sv rr n1 l1 n2 l2 al)[Dist.L1]! = l1 := by
  rw [ProcDistCellCells.core_cell ids tv n i j sv rr n1 l1 n2 l2 al Dist.N1 (by decide) (by decide)
      (by decide) (by decide),
    ProcDistCellCells.core_cell ids tv n i j sv rr n1 l1 n2 l2 al Dist.L1 (by decide) (by decide)
      (by decide) (by decide)]
  exact ⟨rfl, rfl⟩

theorem req_row (R : Run) (c : CReq) (rho : Nat) (h : rho < 20) :
    ∃ jj cv, (Scan.reqRows R c)[rho]! = ProcScanRequestFactor.row R c rho jj cv := by
  rw [ProcScanRequestState.native]
  exact ⟨_, _, ProcScanRequestState.row_at R c 20 rho h⟩

theorem req_cells (R : Run) (c : CReq) (rho : Nat) (h : rho < 20) :
    (Scan.reqRows R c)[rho]![Scan.kS]! = 1 ∧
    (Scan.reqRows R c)[rho]![Scan.fQ]! = b2n (rho == 0) ∧
    (Scan.reqRows R c)[rho]![Scan.tau]! = R.tau ∧
    (Scan.reqRows R c)[rho]![Scan.nn]! = R.n ∧
    (Scan.reqRows R c)[rho]![Scan.base]! = R.base ∧
    (Scan.reqRows R c)[rho]![Scan.dd]! = R.D ∧
    (Scan.reqRows R c)[rho]![Scan.cid]! = c.cid ∧
    (Scan.reqRows R c)[rho]![Dist.kGH]! = 0 ∧
    (Scan.reqRows R c)[rho]![Dist.kC]! = 0 ∧
    (Scan.reqRows R c)[rho]![Dist.kSh]! = 0 := by
  obtain ⟨jj, cv, he⟩ := req_row R c rho h
  rw [he]
  have h1 := ProcScanRequestCells.controls R c rho jj cv
  have h2 := ProcScanRequestQuietCells.zeros R c rho jj cv
  exact ⟨h1.2.1, h1.2.2.1, h1.2.2.2.1, h1.2.2.2.2.1, h1.2.2.2.2.2.1, h1.2.2.2.2.2.2.1,
    h1.2.2.2.2.2.2.2, h2.2.2.1, h2.2.2.2.1, h2.2.1⟩

theorem shard_cells (tv n sd i x count left budget kp : Nat) :
    (ProcDistShardRow.row tv n sd i x count left budget kp)[Dist.kSh]! = 1 ∧
    (ProcDistShardRow.row tv n sd i x count left budget kp)[Scan.kS]! = 0 ∧
    (ProcDistShardRow.row tv n sd i x count left budget kp)[Dist.kGH]! = 0 ∧
    (ProcDistShardRow.row tv n sd i x count left budget kp)[Dist.kC]! = 0 ∧
    (ProcDistShardRow.row tv n sd i x count left budget kp)[Scan.fQ]! = 0 ∧
    (ProcDistShardRow.row tv n sd i x count left budget kp)[Dist.side]! = sd ∧
    (ProcDistShardRow.row tv n sd i x count left budget kp)[Dist.a]! = i ∧
    (ProcDistShardRow.row tv n sd i x count left budget kp)[Dist.kp]! = kp ∧
    (ProcDistShardRow.row tv n sd i x count left budget kp)[Dist.tau]! = tv ∧
    (ProcDistShardRow.row tv n sd i x count left budget kp)[Dist.nn]! = n := by
  rcases ProcDistShardControlCells.fields tv n sd i x count left budget kp with
    ⟨_, _, hkS, hkSh, hkGH, hkC, _⟩
  rcases ProcDistShardOutputCells.fields tv n sd i x count left budget kp with
    ⟨_, _, _, hkp, hside, ha, _, _, _, _, _, _, _, _, hnn, _⟩
  exact ⟨hkSh, hkS, hkGH, hkC, (SsdShard.scan_cols tv n sd i x count left budget kp).1, hside, ha, hkp,
    SsdShard.tau_cell tv n sd i x count left budget kp, hnn⟩

/-! ## Local legality of one row from its descriptor and its successor -/

section
variable {tr : Trace Fp} {t r : Nat}

theorem ofNat_succ (v : Nat) : Fp.ofNat (v + 1) = Fp.ofNat v + 1 := by
  rw [← ZkFormal.Near.ofNat_add']; rfl

/-- **Row-level local legality** of a descriptor row with an admissible successor. -/
theorem local_at (d : Desc) (nx : Option Desc) (hv : d.Valid) (hadj : AdjO d nx) (pub : List Fp)
    (hrow : ∀ col, tr.cell t r col = Fp.ofNat d.row[col]!)
    (hnext : ∀ col, tr.cell t ((r+1) % tr.height t) col = Fp.ofNat (rowO nx)[col]!)
    (hf : r = 0 → d.FirstOk) (hl : r + 1 < tr.height t) :
    ∀ e ∈ ScanDist.constraints, e.eval tr t r pub = 0 := by
  have nz : ∀ col, nx = none → tr.cell t ((r+1) % tr.height t) col = 0 := by
    intro col h; subst h; rw [hnext]; simp only [rowO, zrow_cell]; rfl
  cases d with
  | param R =>
    obtain ⟨I, tau, hr, ht, hn⟩ := hv
    cases nx with
    | none => exact hadj.elim
    | some d' =>
      cases d' with
      | req R' c rho =>
        obtain ⟨rfl, hc0, rfl⟩ := hadj
        have hc := req_cells R c 0 (by decide)
        refine ProcScanParamPhysical.physical I tau R hr ht hn tr t r pub hrow hl ?_ ?_ ?_ ?_ ?_ ?_
        all_goals rw [hnext]; simp only [rowO, row]
        · rw [hc.2.1]; rfl
        · rw [hc.2.2.2.2.2.2.1, hc0]; rfl
        · rw [hc.2.2.1]
        · rw [hc.2.2.2.1]
        · rw [hc.2.2.2.2.1]
        · rw [hc.2.2.2.2.2.1]
      | _ => exact hadj.elim
  | req R c rho =>
    obtain ⟨I, tau, hr, hp, hc, hrho⟩ := hv
    have hcur := req_cells R c rho hrho
    have hfirst : r ≠ 0 := fun h => (hf h).elim
    cases nx with
    | none => exact hadj.elim
    | some d' =>
      cases d' with
      | req R' c' rho' =>
        have hn := req_cells R' c' rho' (by rcases hadj with h | h <;> omega)
        refine ProcScanRequestNativeLocal.physical I tau R hr hp c hc rho hrho tr t r pub hrow ?_ ?_
          hfirst hl ?_ ?_ ?_
        · intro h19 col
          rcases hadj with ⟨_, rfl, rfl, rfl⟩ | ⟨h, _⟩
          · rw [hnext]; rfl
          · omega
        · intro h19
          rcases hadj with ⟨h, _⟩ | ⟨_, rfl, hcid, rfl⟩
          · omega
          · refine ⟨Or.inr ?_, Or.inr ⟨?_, ?_⟩⟩
            · rw [hnext]; simp only [rowO, row]; rw [hn.2.1]; rfl
            · rw [hnext, hrow]; simp only [rowO, row]
              rw [hn.2.2.2.2.2.2.1, hcur.2.2.2.2.2.2.1, hcid, ofNat_succ]
            · intro col hcol
              simp only [Scan.instCols, List.mem_cons, List.not_mem_nil, or_false] at hcol
              rw [hnext, hrow]; simp only [rowO, row]
              rcases hcol with rfl | rfl | rfl | rfl
              · rw [hn.2.2.1, hcur.2.2.1]
              · rw [hn.2.2.2.1, hcur.2.2.2.1]
              · rw [hn.2.2.2.2.1, hcur.2.2.2.2.1]
              · rw [hn.2.2.2.2.2.1, hcur.2.2.2.2.2.1]
        · rw [hnext]; simp only [rowO, row]; rw [hn.2.2.2.2.2.2.2.1]; rfl
        · rw [hnext]; simp only [rowO, row]; rw [hn.2.2.2.2.2.2.2.2.1]; rfl
        · left; rw [hnext]; simp only [rowO, row]; rw [hn.2.2.2.2.2.2.2.2.2]; rfl
      | param R' =>
        have hn := param_cells R'
        have h19 : rho = 19 := hadj
        refine ProcScanRequestNativeLocal.physical I tau R hr hp c hc rho hrho tr t r pub hrow
          (fun h => by omega) ?_ hfirst hl ?_ ?_ ?_
        · intro _
          refine ⟨Or.inl ?_, Or.inl ?_⟩
          · rw [hnext]; simp only [rowO, row]; rw [hn.1]; rfl
          · rw [hnext]; simp only [rowO, row]; rw [hn.2.1]; rfl
        · rw [hnext]; simp only [rowO, row]; rw [hn.2.2.1]; rfl
        · rw [hnext]; simp only [rowO, row]; rw [hn.2.2.2.1]; rfl
        · left; rw [hnext]; simp only [rowO, row]; rw [hn.2.2.2.2]; rfl
      | shard tv n sd i x count left budget kp =>
        obtain ⟨h19, rfl, rfl, rfl⟩ := hadj
        have hn := shard_cells tv n 0 0 x count left budget 0
        refine ProcScanRequestNativeLocal.physical I tau R hr hp c hc rho hrho tr t r pub hrow
          (fun h => by omega) ?_ hfirst hl ?_ ?_ ?_
        · intro _
          refine ⟨Or.inl ?_, Or.inl ?_⟩
          · rw [hnext]; simp only [rowO, row]; rw [hn.2.1]; rfl
          · rw [hnext]; simp only [rowO, row]; rw [hn.2.2.2.2.1]; rfl
        · rw [hnext]; simp only [rowO, row]; rw [hn.2.2.1]; rfl
        · rw [hnext]; simp only [rowO, row]; rw [hn.2.2.2.1]; rfl
        · right
          refine ⟨?_, ?_, ?_⟩
          · rw [hnext]; simp only [rowO, row]; rw [hn.2.2.2.2.2.1]; rfl
          · rw [hnext]; simp only [rowO, row]; rw [hn.2.2.2.2.2.2.1]; rfl
          · rw [hnext]; simp only [rowO, row]; rw [hn.2.2.2.2.2.2.2.1]; rfl
      | _ => exact hadj.elim
  | shard tv n sd i x count left budget kp =>
    obtain ⟨hsd, hb, hc, hlf, hx, hi, hn, htv, hkp⟩ := hv
    refine SsdShard.physical tv n sd i x count left budget kp hsd hb hc hlf hx hi hn htv hkp tr t r pub
      hrow hf hl ?_
    cases nx with
    | none => exact hadj.elim
    | some d' =>
      cases d' with
      | shard tv' n' sd' i' x' count' left' budget' kp' =>
        obtain ⟨rfl, rfl, h⟩ := hadj
        have hm := shard_cells tv n sd' i' x' count' left' budget' kp'
        have nc : ∀ col v, (ProcDistShardRow.row tv n sd' i' x' count' left' budget' kp')[col]! = v →
            tr.cell t ((r+1) % tr.height t) col = Fp.ofNat v := by
          intro col v hv; rw [hnext]; simp only [rowO, row]; rw [hv]
        refine ⟨nc _ _ hm.2.2.2.2.2.2.2.2.1, nc _ _ hm.2.2.2.2.2.2.2.2.2, fun hlt => ?_, fun heq => ?_⟩
        · rcases h with ⟨_, rfl, rfl, rfl⟩ | ⟨h, _⟩
          · exact ⟨(nc _ _ hm.1).trans rfl, nc _ _ hm.2.2.2.2.2.1, nc _ _ hm.2.2.2.2.2.2.1,
              nc _ _ hm.2.2.2.2.2.2.2.1⟩
          · omega
        · rcases h with ⟨h, _⟩ | ⟨_, rfl, rfl, rfl, rfl⟩
          · omega
          · refine ⟨(nc _ _ hm.2.2.2.2.2.2.2.1).trans rfl, (nc _ _ hm.2.2.2.2.2.2.1).trans rfl,
              fun _ => ⟨(nc _ _ hm.1).trans rfl, (nc _ _ hm.2.2.2.2.2.1).trans rfl⟩, fun h => by omega⟩
      | header tv' n' i' sv count' left' =>
        obtain ⟨rfl, rfl, heq, rfl, rfl⟩ := hadj
        have hm := header_cells tv n 0 sv count' left'
        have nc : ∀ col v, (ProcDistHeader.row tv n 0 sv count' left')[col]! = v →
            tr.cell t ((r+1) % tr.height t) col = Fp.ofNat v := by
          intro col v hv; rw [hnext]; simp only [rowO, row]; rw [hv]
        refine ⟨nc _ _ hm.2.2.1, nc _ _ hm.2.2.2.1, fun h => by omega, fun _ => ?_⟩
        exact ⟨(nc _ _ hm.2.2.2.2.1).trans rfl, (nc _ _ hm.2.1).trans rfl, fun h => by omega,
          fun _ => (nc _ _ hm.1).trans rfl⟩
      | _ => exact hadj.elim
  | header tv n i sv count left =>
    obtain ⟨htv, hn, hi, hsv, hc, hlf⟩ := hv
    have hfirst : r ≠ 0 := fun h => (hf h).elim
    cases nx with
    | none => exact hadj.elim
    | some d' =>
      cases d' with
      | cell ids tv' n' i' j' sv' rr n1 l1 n2 l2 al =>
        obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hadj
        have ho := ProcDistCellOutputCells.fields ids tv n i 0 sv rr count left n2 l2 al
        have hp := ProcDistCellPosition.fields ids tv n i 0 sv rr count left n2 l2 al
        have hnl := cell_n1l1 ids tv n i 0 sv rr count left n2 l2 al
        have nc : ∀ col v, (ProcDistCellRow.row ids tv n i 0 sv rr count left n2 l2 al)[col]! = v →
            tr.cell t ((r+1) % tr.height t) col = Fp.ofNat v := by
          intro col v hv; rw [hnext]; simp only [rowO, row]; rw [hv]
        exact ProcDistHeaderPhysical.physical tv n i sv count left htv hn hi hsv hc hlf tr t r pub hrow
          hfirst hl ((nc _ _ ho.2.2.1).trans rfl)
          ((nc _ _ ho.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).trans rfl)
          (nc _ _ ho.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) (nc _ _ ho.2.2.2.1)
          (nc _ _ hnl.1) (nc _ _ hnl.2) (nc _ _ hp.1) (nc _ _ ho.2.2.2.2.1)
      | _ => exact hadj.elim
  | cell ids tv n i j sv rr n1 l1 n2 l2 al =>
    obtain ⟨hi, hj, hn, h1, h2, hl1, hl2, hp⟩ := hv
    have hfirst : r ≠ 0 := fun h => (hf h).elim
    refine ProcDistCellLocal.physical ids tv n i j sv rr n1 l1 n2 l2 al hi hj hn h1 h2 hl1 hl2 hp
      tr t r pub hrow hfirst hl ?_ ?_
    · intro hjn
      cases nx with
      | none => exact absurd hadj.2 (by omega)
      | some d' =>
        cases d' with
        | cell ids' tv' n' i' j' sv' rr' n1' l1' n2' l2' al' =>
          obtain ⟨rfl, rfl, rfl, rfl, _, rfl, rfl, rfl, rfl⟩ := hadj
          exact ⟨rr', n2', l2', al', fun col => by rw [hnext]; rfl⟩
        | header => exact absurd hadj.1 (by omega)
        | shard => exact absurd hadj.1 (by omega)
        | _ => exact hadj.elim
    · refine ⟨fun hjn hin => ?_, fun hjn hin => ?_⟩
      · cases nx with
        | none => exact absurd hadj.1 hin
        | some d' =>
          cases d' with
          | header tv' n' i' sv' count' left' =>
            obtain ⟨_, _, rfl, rfl, rfl⟩ := hadj
            have hm := header_cells tv n (i+1) sv' count' left'
            have nc : ∀ col v, (ProcDistHeader.row tv n (i+1) sv' count' left')[col]! = v →
                tr.cell t ((r+1) % tr.height t) col = Fp.ofNat v := by
              intro col v hv; rw [hnext]; simp only [rowO, row]; rw [hv]
            exact ⟨(nc _ _ hm.1).trans rfl, nc _ _ hm.2.1, nc _ _ hm.2.2.1, nc _ _ hm.2.2.2.1⟩
          | cell => exact absurd hadj.2.2.2.2.1 (by omega)
          | shard => exact absurd hadj.2.1 hin
          | _ => exact hadj.elim
      · cases nx with
        | none =>
          refine ⟨nz _ rfl, Or.inl (nz _ rfl)⟩
        | some d' =>
          cases d' with
          | shard tv' n' sd' i' x count left budget kp =>
            obtain ⟨_, _, rfl, rfl, rfl⟩ := hadj
            have hm := shard_cells tv' n' 0 0 x count left budget 0
            have nc : ∀ col v, (ProcDistShardRow.row tv' n' 0 0 x count left budget 0)[col]! = v →
                tr.cell t ((r+1) % tr.height t) col = Fp.ofNat v := by
              intro col v hv; rw [hnext]; simp only [rowO, row]; rw [hv]
            exact ⟨(nc _ _ hm.2.2.2.2.2.2.2.1).trans rfl, Or.inr ⟨(nc _ _ hm.1).trans rfl,
              (nc _ _ hm.2.2.2.2.2.1).trans rfl, (nc _ _ hm.2.2.2.2.2.2.1).trans rfl⟩⟩
          | cell => exact absurd hadj.2.2.2.2.1 (by omega)
          | header => exact absurd hadj.2.1 (by omega)
          | _ => exact hadj.elim

end

end ZkFormal.NearV3.Render.Ssd
