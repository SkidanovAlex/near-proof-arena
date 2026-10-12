import ZkFormal.NearV3.Render.CodecDesc
import ZkFormal.NearV3.Candidates.CodecPadding
import ZkFormal.NearV3.Candidates.SchedHeight
import ZkFormal.Near.Extract.Common

/-!
# `TableLocal Sched.Codec.table` from a codec descriptor chain

`table_local`: a valid descriptor chain (`Desc.Valid`, `Desc.Adj`, `FirstOk`, `Final`, fewer than
`2^22` rows) renders (`SchedHeight.trace (ds.map Desc.row).toArray codecPad`, the scheduler's shared
height `2^22`) to a trace with `TableLocal Sched.Codec.table`: every constraint on every row
(`local_at` on the descriptor rows, `CodecPadding.physical_constraints` on the zero padding) and
boolean multiplicities (`mult_bits`, `CodecPadding.physical_mult_zero`).
-/
namespace ZkFormal.NearV3.Render.Cdc
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen
open ZkFormal.NearV3.Sched.Codec ZkFormal.Chacha.Table.E ZkFormal.NearV3.Candidates.SchedSetAll
open ZkFormal.NearV3.Candidates
open ZkFormal.NearV3.Sched.Complete (gd natCell natRow natRow_lt natRow_ge gd_zrow)

theorem Desc.keys (d : Desc) : ∀ q ∈ d.asg, q.1 < Codec.width := by
  cases d with
  | hdr I p => exact keys_hdrA I p
  | record I R f gg bpo bpr apv apostv bigv => exact keys_recA I R f gg bpo bpr apv apostv bigv
  | hash I dig hpre j => exact keys_hashA I dig hpre j
  | ash I a j => exact keys_ashA I a j

/-- The honest codec trace of a descriptor list. -/
def codecTrace (ds : List Desc) : Trace Fp := SchedHeight.trace (ds.map Desc.row).toArray codecPad

theorem codecTrace_height (ds : List Desc) (t : Nat) : (codecTrace ds).height t = 2 ^ 22 := rfl

theorem natCell_desc (ds : List Desc) (r : Nat) (hr : r < ds.length) (c : Nat) :
    natCell (ds.map Desc.row).toArray codecPad r c = lookup ds[r].asg c 0 := by
  unfold natCell natRow
  rw [dif_pos (by simpa using hr)]
  simp only [List.getElem_toArray, List.getElem_map, Desc.row]
  exact gd_setAll _ c (Desc.keys _)

theorem natCell_pad (ds : List Desc) (r : Nat) (hr : ds.length ≤ r) (c : Nat) :
    natCell (ds.map Desc.row).toArray codecPad r c = 0 := by
  unfold natCell natRow
  rw [dif_neg (by simp; omega)]
  exact gd_zrow _ _

theorem cell_lt (d : Desc) (hv : d.Valid) (c : Nat) : lookup d.asg c 0 < P :=
  lookup_bound _ c 0 P (by unfold P; omega) hv.1

theorem cur_desc (ds : List Desc) (hv : ∀ d ∈ ds, d.Valid) (r : Nat) (hr : r < ds.length)
    (t : Nat) (pub : List Fp) (c : Nat) :
    (tenv (codecTrace ds) t r pub).cur c = lookup ds[r].asg c 0 := by
  change (Fp.ofNat (natCell (ds.map Desc.row).toArray codecPad r c)).toNat = _
  rw [natCell_desc ds r hr, Fp.toNat_ofNat, Nat.mod_eq_of_lt (cell_lt _ (hv _ (List.getElem_mem _)) c)]

theorem cell_pad (ds : List Desc) (r : Nat) (hr : ds.length ≤ r) (t c : Nat) :
    (codecTrace ds).cell t r c = 0 := by
  change Fp.ofNat (natCell (ds.map Desc.row).toArray codecPad r c) = 0
  rw [natCell_pad ds r hr]; rfl

/-- **`TableLocal Sched.Codec.table` from a descriptor chain.** -/
theorem table_local (ds : List Desc) (hcap : ds.length < 2 ^ 22)
    (hv : ∀ d ∈ ds, d.Valid)
    (hadj : ∀ k (hk : k + 1 < ds.length), Desc.Adj ds[k] ds[k+1])
    (hfirst : ∀ h : 0 < ds.length, (ds[0]'h).FirstOk)
    (hlast : ∀ h : ds.length - 1 < ds.length, (ds[ds.length - 1]'h).Final)
    (t : Nat) (pub : List Fp) :
    ZkFormal.Near.TableLocal Codec.table (codecTrace ds) t pub := by
  have hH := codecTrace_height ds t
  have hconstr : ∀ r, r < 2 ^ 22 → ∀ e ∈ Codec.constraints, e.eval (codecTrace ds) t r pub = 0 := by
    intro r hr
    by_cases hlt : r < ds.length
    · have hmod : (r + 1) % (codecTrace ds).height t = r + 1 := by
        rw [hH]; exact Nat.mod_eq_of_lt (by omega)
      have hcur := cur_desc ds hv r hlt t pub
      have hl : (tenv (codecTrace ds) t r pub).last = 0 := by
        change (if r + 1 = (codecTrace ds).height t then (1 : Int) else 0) = 0
        rw [hH, if_neg (by omega)]
      have hfi : (tenv (codecTrace ds) t r pub).first = 0 ∨ ds[r].FirstOk := by
        by_cases h0 : r = 0
        · subst h0; exact Or.inr (hfirst hlt)
        · left; change (if r = 0 then (1 : Int) else 0) = 0; rw [if_neg h0]
      by_cases hn : r + 1 < ds.length
      · refine local_at ds[r] (some ds[r+1]) (hv _ (List.getElem_mem _)) (hadj r hn) hcur ?_ hfi hl
        intro c
        change (Fp.ofNat (natCell (ds.map Desc.row).toArray codecPad
          ((r + 1) % (codecTrace ds).height t) c)).toNat = _
        rw [hmod, natCell_desc ds (r+1) hn, Fp.toNat_ofNat,
          Nat.mod_eq_of_lt (cell_lt _ (hv _ (List.getElem_mem _)) c)]
        try rfl
      · have hr' : r = ds.length - 1 := by omega
        refine local_at ds[r] none (hv _ (List.getElem_mem _)) ?_ hcur ?_ hfi hl
        · show ds[r].Final
          subst hr'
          exact hlast hlt
        · intro c
          change (Fp.ofNat (natCell (ds.map Desc.row).toArray codecPad
            ((r + 1) % (codecTrace ds).height t) c)).toNat = _
          rw [hmod, natCell_pad ds (r+1) (by omega)]
          try rfl
    · exact CodecPadding.physical_constraints _ t r pub (cell_pad ds r (by omega) t) (by
        by_cases h : r + 1 < 2 ^ 22
        · left
          intro c
          rw [hH, Nat.mod_eq_of_lt h]
          exact cell_pad ds (r+1) (by omega) t c
        · right; rw [hH]; omega)
  refine ⟨by change 1 ≤ 22; decide, by change 22 ≤ 22; decide, ?_, ?_⟩
  · intro r hr e he
    exact hconstr r hr e he
  · intro r hr i hi b hb
    by_cases hlt : r < ds.length
    · exact mult_bits ds[r] (hv _ (List.getElem_mem _)) (cur_desc ds hv r hlt t pub) i hi b hb
    · left
      exact CodecPadding.physical_mult_zero _ t r pub (cell_pad ds r (by omega) t) i hi b hb

end ZkFormal.NearV3.Render.Cdc
