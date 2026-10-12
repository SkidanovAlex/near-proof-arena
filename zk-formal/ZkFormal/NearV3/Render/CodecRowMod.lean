import ZkFormal.NearV3.Render.CodecCells
import ZkFormal.NearV3.Render.CodecMod

/-!
# The modular constraints (`modE`) on every honest codec row kind

`hdr_mod`, `rec_mod`, `hash_mod`, `ash_mod`: the eight constraints of `modE` vanish over `Fp` on a
trace row whose cells are the honest assignment (`hdrA`/`recA`/`hashA`/`ashA`, read by `lookup`),
via `CodecMod` (`isZ_mod`, `nzb_mod`, `wt_mod`, `wt_off`, `gate_zero`).  `row_local`: the integer pass
(`∀ e ∉ modE, zev = 0`) and the modular pass give every constraint of `Sched.Codec.table`.
-/
namespace ZkFormal.NearV3.Render.Cdc
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen
open ZkFormal.NearV3.Sched.Codec ZkFormal.Chacha.Table.E ZkFormal.NearV3.Candidates.SchedSetAll

set_option maxRecDepth 65536

/-- Cell evaluation of the honest assignments. -/
macro "cdc_cell" : tactic => `(tactic| (
  simp only [hdrA, recA, hashA, ashA, instA, regA, pbits, qbits, lookup_app, lookup_ite, lookup_cons,
    lookup_nil, List.range_succ, List.range_zero, List.nil_append, List.map_append, List.map_cons,
    List.map_nil, List.cons_append, act, kH, kR, kZ, kA, kF, tau, pos, pres, vid, nn, NN, base, fair,
    bpre, bpost, pbit, kidx, klo, khi, fS, fR, fA, g, ig7, e7, ig2, e2, lowf, wt, ap, big, ib, nzb,
    apost, ikl, ekl, ihp, ehp, sj, isj, esj, bsha, fb, al, a1, cb, afin, gfin, gb, itz, zt, cx, cy,
    cbit, cg, rend, a2, g2, vbg, fwg, pm0, pm1, dgg, bF, srcC, apR, hasC, bigR, rs, a0g, u0g, useC,
    prbit, reg_0, reg_1, reg_2, reg_3, reg_4, reg_5, reg_6, reg_7, reg_8, reg_9, reg_10, reg_11,
    reg_12, reg_13, reg_14, reg_15, reg_16, reg_17, reg_18, reg_19, reg_20, reg_21, reg_22, reg_23,
    reg_24, reg_25, reg_26, reg_27, reg_28, reg_29, reg_30, reg_31, Nat.reduceEqDiff, Nat.reduceAdd,
    ite_true, ite_false, ite_self, Bool.false_eq_true, and_self, true_and, and_true, false_and,
    and_false]))

theorem fsub_zero (x : Nat) (hx : x < P) : fsub x 0 = x := by
  unfold fsub; rw [Nat.zero_mod, Nat.sub_zero, Nat.mod_eq_of_lt hx, Nat.add_mod_right,
    Nat.mod_eq_of_lt hx]

section
variable {tr : Trace Fp} {t r : Nat} {pub : List Fp}

theorem modE_cases {Q : Expr → Prop}
    (h1 : Q (Expr.mul (c kR) (sub (c e7) (notE (.mul (sub (c g) (k 7)) (c ig7))))))
    (h2 : Q (Expr.mul (c fA) (sub (c e2) (notE (.mul (sub (c g) (k 2)) (c ig2))))))
    (h3 : Q (Expr.mul (c kR) (sub (c ekl) (notE (.mul (sub (c kidx) (sub (c NN) (k 1))) (c ikl))))))
    (h4 : Q (Expr.mul (c kH) (sub (c ehp) (notE (.mul (sub (c pos) (k 4)) (c ihp))))))
    (h5 : Q (Expr.mul (.add (c kZ) (c kA))
      (sub (c esj) (notE (.mul (sub (c sj) (.add (k 31) (smul 32 (c kA)))) (c isj))))))
    (h6 : Q (Expr.mul (c act) (sub (c zt) (notE (.mul (c tau) (c itz))))))
    (h7 : Q (.mul (c fA) (sub (c nzb) (.mul (c bpre) (c ib)))))
    (h8 : Q (.mul (sub (c fA) (c rend)) (sub (n wt) (smul 256 (c wt))))) :
    ∀ e ∈ modE, Q e := by
  simp only [modE, isZ, List.take, List.nil_append, List.cons_append, List.forall_mem_cons,
    List.forall_mem_nil, and_true]
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, fun _ h => (List.not_mem_nil h).elim⟩

/-- The `itz`/`zt` test on an active row. -/
theorem tz_mod (I : Inst) (htv : I.tv < P)
    (ha : (tenv tr t r pub).cur act = 1) (ht : (tenv tr t r pub).cur tau = I.tv)
    (hi : (tenv tr t r pub).cur itz = inv I.tv) (hz : (tenv tr t r pub).cur zt = zt0 I) :
    (Expr.mul (c act) (sub (c zt) (notE (.mul (c tau) (c itz))))).eval tr t r pub = 0 := by
  have hX : zev (tenv tr t r pub) (c tau) = (I.tv : Int) - (0 : Nat) := by
    simp only [zev_c, ht]; omega
  refine isZ_mod (c act) (c tau) itz zt I.tv 0 htv (by unfold P; omega) hX ?_ ?_
  · rw [hi, fsub_zero _ htv]
  · rw [hz]; rfl

theorem gate0 (gate y : Expr) (hg : zev (tenv tr t r pub) gate = 0) :
    (Expr.mul gate y).eval tr t r pub = 0 := gate_zero gate y hg

/-- **Header rows.** -/
theorem hdr_mod (I : Inst) (p : Nat) (hp : p ≤ 4) (htv : I.tv < P)
    (hcur : ∀ c, (tenv tr t r pub).cur c = lookup (hdrA I p) c 0) :
    ∀ e ∈ modE, e.eval tr t r pub = 0 := by
  apply modE_cases
  · exact gate0 _ _ (by simp only [zev_c, hcur]; cdc_cell; rfl)
  · exact gate0 _ _ (by simp only [zev_c, hcur]; cdc_cell; rfl)
  · exact gate0 _ _ (by simp only [zev_c, hcur]; cdc_cell; rfl)
  · refine isZ_mod (c kH) (sub (c pos) (k 4)) ihp ehp p 4 (by unfold P; omega) (by unfold P; omega)
      ?_ ?_ ?_
    · simp only [zev_sub, zev_c, zev_k, hcur]; cdc_cell
    · rw [hcur]; cdc_cell
    · rw [hcur]; cdc_cell
  · exact gate0 _ _ (by simp only [zev_c, zev_add, hcur]; cdc_cell; rfl)
  · exact tz_mod I htv (by rw [hcur]; cdc_cell) (by rw [hcur]; cdc_cell) (by rw [hcur]; cdc_cell)
      (by rw [hcur]; cdc_cell)
  · exact gate0 _ _ (by simp only [zev_c, hcur]; cdc_cell; rfl)
  · exact wt_off (by rw [hcur, hcur]; cdc_cell)

/-- **Sanity-hash rows.** -/
theorem hash_mod (I : Inst) (dig hpre : List Nat) (j : Nat) (hj : j < 32) (htv : I.tv < P)
    (hcur : ∀ c, (tenv tr t r pub).cur c = lookup (hashA I dig hpre j) c 0) :
    ∀ e ∈ modE, e.eval tr t r pub = 0 := by
  apply modE_cases
  · exact gate0 _ _ (by simp only [zev_c, hcur]; cdc_cell; rfl)
  · exact gate0 _ _ (by simp only [zev_c, hcur]; cdc_cell; rfl)
  · exact gate0 _ _ (by simp only [zev_c, hcur]; cdc_cell; rfl)
  · exact gate0 _ _ (by simp only [zev_c, hcur]; cdc_cell; rfl)
  · refine isZ_mod _ _ isj esj j 31 (by unfold P; omega) (by unfold P; omega) ?_ ?_ ?_
    · simp only [zev_sub, zev_c, zev_k, zev_add, zev_smul, hcur]; cdc_cell; omega
    · rw [hcur]; cdc_cell
    · rw [hcur]; cdc_cell
  · exact tz_mod I htv (by rw [hcur]; cdc_cell) (by rw [hcur]; cdc_cell) (by rw [hcur]; cdc_cell)
      (by rw [hcur]; cdc_cell)
  · exact gate0 _ _ (by simp only [zev_c, hcur]; cdc_cell; rfl)
  · exact wt_off (by rw [hcur, hcur]; cdc_cell)

/-- **`sha256(all_shards)` rows.** -/
theorem ash_mod (I : Inst) (ash : List Nat) (j : Nat) (hj : j < 32) (htv : I.tv < P)
    (hcur : ∀ c, (tenv tr t r pub).cur c = lookup (ashA I ash j) c 0) :
    ∀ e ∈ modE, e.eval tr t r pub = 0 := by
  apply modE_cases
  · exact gate0 _ _ (by simp only [zev_c, hcur]; cdc_cell; rfl)
  · exact gate0 _ _ (by simp only [zev_c, hcur]; cdc_cell; rfl)
  · exact gate0 _ _ (by simp only [zev_c, hcur]; cdc_cell; rfl)
  · exact gate0 _ _ (by simp only [zev_c, hcur]; cdc_cell; rfl)
  · refine isZ_mod _ _ isj esj (32 + j) 63 (by unfold P; omega) (by unfold P; omega) ?_ ?_ ?_
    · simp only [zev_sub, zev_c, zev_k, zev_add, zev_smul, hcur]; cdc_cell; omega
    · rw [hcur]; cdc_cell
    · rw [hcur]; cdc_cell
      have : (32 + j = 63) ↔ (j = 31) := by omega
      simp only [this]
  · exact tz_mod I htv (by rw [hcur]; cdc_cell) (by rw [hcur]; cdc_cell) (by rw [hcur]; cdc_cell)
      (by rw [hcur]; cdc_cell)
  · exact gate0 _ _ (by simp only [zev_c, hcur]; cdc_cell; rfl)
  · exact wt_off (by rw [hcur, hcur]; cdc_cell)

/-- **Record rows** `(f, gg)`; the next row's `wt` matters only inside the allowance field. -/
theorem rec_mod (I : Inst) (R : Rec) (f gg bpo bpr apv apostv bigv : Nat) (hf : f < 3) (hg : gg < 8)
    (htv : I.tv < P) (hkN : R.kk < I.N) (hNP : I.N ≤ P) (hbpr : bpr < P)
    (hikl : R.iklv = inv (fsub R.kk (I.N - 1)))
    (hcur : ∀ c, (tenv tr t r pub).cur c = lookup (recA I R f gg bpo bpr apv apostv bigv) c 0)
    (hnxt : f = 2 → gg < 7 → (tenv tr t r pub).nxt wt = 256 ^ (gg + 1) % 2013265921) :
    ∀ e ∈ modE, e.eval tr t r pub = 0 := by
  apply modE_cases
  · refine isZ_mod _ _ ig7 e7 gg 7 (by unfold P; omega) (by unfold P; omega) ?_ ?_ ?_
    · simp only [zev_sub, zev_c, zev_k, hcur]; cdc_cell
    · rw [hcur]; cdc_cell
    · rw [hcur]; cdc_cell
  · by_cases h2 : f = 2
    · subst h2
      refine isZ_mod _ _ ig2 e2 gg 2 (by unfold P; omega) (by unfold P; omega) ?_ ?_ ?_
      · simp only [zev_sub, zev_c, zev_k, hcur]; cdc_cell
      · rw [hcur]; cdc_cell
      · rw [hcur]; cdc_cell
    · exact gate0 _ _ (by simp only [zev_c, hcur]; cdc_cell; simp [h2])
  · refine isZ_mod _ _ ikl ekl R.kk (I.N - 1) (by unfold P at *; omega) (by unfold P at *; omega)
      ?_ ?_ ?_
    · simp only [zev_sub, zev_c, zev_k, hcur]; cdc_cell; omega
    · rw [hcur]; cdc_cell; exact hikl
    · rw [hcur]; cdc_cell
      have : (R.kk + 1 = I.N) ↔ (R.kk = I.N - 1) := by omega
      simp only [this]
  · exact gate0 _ _ (by simp only [zev_c, hcur]; cdc_cell; rfl)
  · exact gate0 _ _ (by simp only [zev_c, zev_add, hcur]; cdc_cell; rfl)
  · exact tz_mod I htv (by rw [hcur]; cdc_cell) (by rw [hcur]; cdc_cell) (by rw [hcur]; cdc_cell)
      (by rw [hcur]; cdc_cell)
  · by_cases h2 : f = 2
    · subst h2
      exact nzb_mod bpr hbpr (by rw [hcur]; cdc_cell) (by rw [hcur]; cdc_cell) (by rw [hcur]; cdc_cell)
    · exact gate0 _ _ (by simp only [zev_c, hcur]; cdc_cell; simp [h2])
  · by_cases h2 : f = 2
    · subst h2
      by_cases h7 : gg = 7
      · subst h7
        exact wt_off (by rw [hcur, hcur]; cdc_cell)
      · exact wt_mod gg (by rw [hcur]; cdc_cell) (by rw [hcur]; cdc_cell; simp [h7])
          (by rw [hcur]; cdc_cell) (hnxt rfl (by omega))
    · exact wt_off (by rw [hcur, hcur]; cdc_cell; simp [h2])

/-- **Integer pass + modular pass give every constraint.** -/
theorem row_local (hint : ∀ e ∈ constraints, e ∉ modE → zev (tenv tr t r pub) e = 0)
    (hmod : ∀ e ∈ modE, e.eval tr t r pub = 0) :
    ∀ e ∈ constraints, e.eval tr t r pub = 0 := by
  intro e he
  by_cases hm : e ∈ modE
  · exact hmod e hm
  · exact eval_zero_of (hint e he hm)

end

end ZkFormal.NearV3.Render.Cdc
