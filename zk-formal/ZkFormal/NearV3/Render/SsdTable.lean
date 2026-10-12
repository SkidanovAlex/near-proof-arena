import ZkFormal.NearV3.Render.SsdDesc

/-!
# `TableLocal ScanDist.table` from a descriptor chain

`bits_of_constraints`: on any row where all `ScanDist.constraints` vanish, every interaction
multiplicity is `0` or `1` (the kinds are one-hot booleans, `fQ`/`re` are gated by `kS`).
`table_local`: a valid descriptor chain (`Desc.Valid`, `Desc.Adj`, `FirstOk`, `Final`, fewer than
`2^22` rows) renders to `SchedHeight.trace (ds.map Desc.row).toArray distPad` with
`TableLocal ScanDist.table`.
-/
namespace ZkFormal.NearV3.Render.Ssd
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen
open ZkFormal.NearV3.Candidates ZkFormal.Chacha.Table.E

section
variable {tr : Trace Fp} {t r : Nat} {pub : List Fp}

theorem bool_cell {x : Nat} (h : (ZkFormal.Chacha.Table.boolC x).eval tr t r pub = 0) :
    (tenv tr t r pub).cur x ≤ 1 := by
  have h' : Fp.mul (tr.cell t r x) (Fp.add (tr.cell t r x) (Fp.neg (Fp.ofNat 1))) = 0 := h
  change (tr.cell t r x).toNat ≤ 1
  rcases ZkFormal.Sha.fp_mul_eq_zero h' with h0 | h1
  · rw [h0]; decide
  · have : tr.cell t r x = Fp.ofNat 1 := by
      have e := congrArg (fun z => Fp.add z (Fp.ofNat 1)) h1
      apply Fp.ext
      have h3 := congrArg Fp.toNat e
      simp only [Fp.toNat_add, Fp.toNat_neg, Fp.toNat_ofNat] at h3
      have := (tr.cell t r x).toNat_lt
      rw [show (0 : Fp) = Fp.ofNat 0 from rfl, Fp.toNat_ofNat] at h3
      rw [Fp.toNat_ofNat]
      unfold P at *
      omega
    rw [this]; decide

theorem small_zero {e : Expr} (h : e.eval tr t r pub = 0) (h1 : -10 < zev (tenv tr t r pub) e)
    (h2 : zev (tenv tr t r pub) e < 10) : zev (tenv tr t r pub) e = 0 :=
  zev_eq_zero h (by omega) (by omega)

/-- **Boolean multiplicities from the constraints.** -/
theorem bits_of_constraints (h : ∀ e ∈ ScanDist.constraints, e.eval tr t r pub = 0) :
    ∀ i ∈ ScanDist.interactions, ∀ b ∈ i.mult, b.eval tr t r pub = 0 ∨ b.eval tr t r pub = 1 := by
  have hb : ∀ x ∈ [Dist.act, Dist.kP, Dist.kS, Dist.kSh, Dist.kGH, Dist.kC, Dist.cg, Dist.dlsg,
      Dist.dlrg, Scan.fQ, Scan.re, Scan.us0, Scan.us1], (tenv tr t r pub).cur x ≤ 1 := by
    intro x hx
    apply bool_cell
    apply h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    simp only [ScanDist.constraints, Dist.constraints, Dist.cKind, Scan.own, List.mem_append]
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | (left; left; left; left; left; left; apply List.mem_map_of_mem; decide)
      | (right; left; apply List.mem_map_of_mem; decide)
  simp only [List.forall_mem_cons, List.forall_mem_nil, and_true] at hb
  obtain ⟨ba, bP, bS, bSh, bGH, bC, bcg, bsg, brg, bfQ, bre, bu0, bu1⟩ := hb
  have memSum : sub (c Dist.act) (.add (c Dist.kP) (.add (c Dist.kS)
      (.add (c Dist.kSh) (.add (c Dist.kGH) (c Dist.kC))))) ∈ ScanDist.constraints := by
    simp [ScanDist.constraints, Dist.constraints, Dist.cKind, Dist.cCommon]
  have memFQ : Expr.mul (c Scan.fQ) (Scan.notE (c Scan.kS)) ∈ ScanDist.constraints := by
    simp [ScanDist.constraints, Scan.own, Scan.body]
  have memRE : Expr.mul (c Scan.re) (Scan.notE (c Scan.kS)) ∈ ScanDist.constraints := by
    simp [ScanDist.constraints, Scan.own, Scan.body]
  have hsum := small_zero (h _ memSum) (by simp [zev, sub]; omega) (by simp [zev, sub]; omega)
  simp [zev, sub] at hsum
  have gate : ∀ x, (tenv tr t r pub).cur x ≤ 1 →
      Expr.mul (c x) (Scan.notE (c Scan.kS)) ∈ ScanDist.constraints →
      (tenv tr t r pub).cur x ≤ (tenv tr t r pub).cur Scan.kS := by
    intro x hx hm
    have he := h _ hm
    rcases (show (tenv tr t r pub).cur x = 0 ∨ (tenv tr t r pub).cur x = 1 by omega) with h1 | h1
    · omega
    · rcases (show (tenv tr t r pub).cur Scan.kS = 0 ∨ (tenv tr t r pub).cur Scan.kS = 1 by
          simp only [Scan.kS]; omega) with h2 | h2
      · have hz := small_zero he (by simp [zev, Scan.notE, h1, h2]) (by simp [zev, Scan.notE, h1, h2])
        simp [zev, Scan.notE, h1, h2] at hz
      · omega
  have fq := gate _ bfQ memFQ
  have re := gate _ bre memRE
  simp only [Scan.kS, Scan.kP, Scan.kSh, Scan.kC] at fq re
  simp only [Dist.act, Dist.kP, Dist.kS, Dist.kSh, Dist.kGH, Dist.kC, Scan.fQ, Scan.re, Scan.us0,
    Scan.us1, Dist.cg, Dist.dlsg, Dist.dlrg] at *
  have key : ∀ i ∈ ScanDist.interactions, ∀ b ∈ i.mult,
      zev (tenv tr t r pub) b = 0 ∨ zev (tenv tr t r pub) b = 1 := by
    simp only [ScanDist.interactions, List.forall_mem_cons, List.forall_mem_nil, and_true]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    · refine ⟨?_, fun _ h => (List.not_mem_nil h).elim⟩
      simp only [zev_c, zev_add, Scan.kP, Scan.kSh, Scan.kC, Scan.fQ, Scan.re, Scan.us0, Scan.us1,
        Dist.act, Dist.kP, Dist.kS, Dist.kSh, Dist.kGH, Dist.kC, Dist.cg, Dist.dlsg, Dist.dlrg]
      first | omega | (refine ⟨?_, fun _ h => (List.not_mem_nil h).elim⟩; omega)
  intro i hi b hb'
  rcases key i hi b hb' with h0 | h1
  · left; rw [eval_eq, h0]; rfl
  · right; rw [eval_eq, h1]; rfl

end

theorem rows_get (ds : List Desc) (r : Nat) (hr : r < ds.length) :
    (ds.map Desc.row).toArray[r]! = ds[r].row := by
  rw [getElem!_pos _ r (by simpa using hr)]
  simp

/-- **`TableLocal ScanDist.table` from a descriptor chain.** -/
theorem table_local (ds : List Desc) (hcap : ds.length < 2 ^ 22)
    (hv : ∀ d ∈ ds, d.Valid)
    (hadj : ∀ k (hk : k + 1 < ds.length), Desc.Adj ds[k] ds[k+1])
    (hfirst : ∀ h : 0 < ds.length, (ds[0]'h).FirstOk)
    (hlast : ∀ h : ds.length - 1 < ds.length, (ds[ds.length - 1]'h).Final)
    (t : Nat) (pub : List Fp) :
    ZkFormal.Near.TableLocal ScanDist.table
      (SchedHeight.trace (ds.map Desc.row).toArray distPad) t pub := by
  have hsize : (ds.map Desc.row).toArray.size = ds.length := by simp
  have hH : (SchedHeight.trace (ds.map Desc.row).toArray distPad).height t = 2 ^ 22 := rfl
  have hpadc : ∀ r, ds.length ≤ r → ∀ col,
      (SchedHeight.trace (ds.map Desc.row).toArray distPad).cell t r col = 0 := by
    intro r hr col
    rw [ProcDistCmpPhysical.cells_padding _ r (by omega) t]
  have hconstr : ∀ r, r < 2 ^ 22 → ∀ e ∈ ScanDist.constraints,
      e.eval (SchedHeight.trace (ds.map Desc.row).toArray distPad) t r pub = 0 := by
    intro r hr
    by_cases hlt : r < ds.length
    · have hrow : ∀ col, (SchedHeight.trace (ds.map Desc.row).toArray distPad).cell t r col =
          Fp.ofNat (ds[r]).row[col]! := by
        intro col
        rw [ProcDistCmpPhysical.cells_active _ r (by omega) t, rows_get ds r hlt]
      have hmod : (r + 1) % (SchedHeight.trace (ds.map Desc.row).toArray distPad).height t = r + 1 := by
        rw [hH]; exact Nat.mod_eq_of_lt (by omega)
      have hf : r = 0 → ds[r].FirstOk := by
        intro h0; subst h0; exact hfirst hlt
      by_cases hn : r + 1 < ds.length
      · refine local_at ds[r] (some ds[r+1]) (hv _ (List.getElem_mem _)) (hadj r hn) pub hrow ?_ hf
          (by rw [hH]; omega)
        intro col
        rw [hmod, ProcDistCmpPhysical.cells_active _ (r+1) (by omega) t, rows_get ds (r+1) hn]
        rfl
      · have hr' : r = ds.length - 1 := by omega
        refine local_at ds[r] none (hv _ (List.getElem_mem _)) ?_ pub hrow ?_ hf (by rw [hH]; omega)
        · show ds[r].Final
          subst hr'
          exact hlast hlt
        · intro col
          rw [hmod, hpadc (r+1) (by omega) col]
          simp only [rowO, zrow_cell]
          rfl
    · exact ScanPadding.physical_constraints _ t r pub (hpadc r (by omega)) (by
        by_cases h : r + 1 < 2 ^ 22
        · left
          intro col
          rw [hH, Nat.mod_eq_of_lt h]
          exact hpadc (r+1) (by omega) col
        · right; rw [hH]; omega)
  refine ⟨by change 1 ≤ 22; decide, by change 22 ≤ 22; decide, ?_, ?_⟩
  · intro r hr e he
    exact hconstr r hr e he
  · intro r hr i hi b hb
    by_cases hlt : r < ds.length
    · exact bits_of_constraints (hconstr r hr) i hi b hb
    · left
      exact ScanPadding.physical_mult_zero _ t r pub (hpadc r (by omega)) i hi b hb

end ZkFormal.NearV3.Render.Ssd
