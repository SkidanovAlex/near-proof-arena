/-
DKT26 verification (lane/pq-dkt-verify): the O-1 chain composed in Lean.

ArkLib@a5aa2677 proves DKT26 Thm 5.12 (`exists_exceptional_johnson_lineMCA_allChar`) and the
interleaving / shared-level fold transfers of Cor 7.7 / 7.8
(`fullSetLevelWitness_interleaved_of_exactAgreement`, `TensorMCA.tensorFoldBad_card_le`) as
separate statements; it does not state their composition.  This file composes them, with the
exceptional count E = floor(johnsonE0 n D A eta), at an arbitrary integer threshold
A >= (sqrt(D/n) + eta) n, over any finite field, any n distinct points, any interleaving width.
-/
import ArkLib.Data.CodingTheory.ReedSolomon.PaperGuide
import ArkLib.Data.CodingTheory.ProximityGenerator.BinaryTensorFoldAgreement

open Polynomial ReedSolomon ReedSolomon.HiddenDerivative CoreDefinitions

namespace DKTVerify

/-- Thm 5.12 in the `LineExactAgreementBound` form consumed by the interleaving/fold layer,
with the natural-number exceptional count `⌊johnsonE0⌋₊`. -/
theorem johnson_lineExact {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (n D A : ℕ) (eta : ℝ) (hD : 1 ≤ D) (hDn : D ≤ n - 2) (heta : 0 < eta)
    (ha : johnsonAgreement n D eta ≤ 1) (hthr : johnsonAgreement n D eta * n ≤ A)
    (hAn : A ≤ n) (domain : Fin n ↪ F) :
    LineExactAgreementBound domain (D + 1) A (⌊johnsonE0 n D A eta⌋₊ : ℕ) := by
  classical
  intro f g
  obtain ⟨ex, hcard, hgood⟩ :=
    exists_exceptional_johnson_lineMCA_allChar n D A eta hD hDn heta ha hthr hAn domain f g
  refine ⟨ex, ?_, ?_⟩
  · have : ex.card ≤ ⌊johnsonE0 n D A eta⌋₊ := Nat.le_floor hcard
    exact_mod_cast this
  · intro z hz P hP hagree
    have hagree' : A ≤ (@polynomialAgreementSet F _ (Classical.decEq F) n domain
        (fun i ↦ f i + z * g i) P).card := by
      convert hagree
    obtain ⟨pair, hp0, hp1, heq, hset⟩ := hgood z hz P hP hagree'
    refine ⟨pair.1, pair.2, hp0, hp1, ?_, ?_⟩
    · simpa [correlatedPairSpecialization] using heq
    · have := hset
      simp only [mappedDomain] at this
      convert this using 2 <;> simp

/-- Cor 7.7 (lines) on top of Thm 5.12: one exceptional set of size `⌊johnsonE0⌋₊` serves every
interleaving width and every finite family of parents at one fold level. -/
theorem johnson_levelWitness {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (n D A : ℕ) (eta : ℝ) (hD : 1 ≤ D) (hDn : D ≤ n - 2) (heta : 0 < eta)
    (ha : johnsonAgreement n D eta ≤ 1) (hthr : johnsonAgreement n D eta * n ≤ A)
    (hAn : A ≤ n) (hDA : D + 1 ≤ A) (domain : Fin n ↪ F) {width : ℕ} (hwidth : 0 < width) :
    TensorMCA.FullSetLevelWitness ((code domain (D + 1)) ^⋈ (Fin width)) A
      ⌊johnsonE0 n D A eta⌋₊ :=
  fullSetLevelWitness_interleaved_of_exactAgreement domain
    (johnson_lineExact n D A eta hD hDn heta ha hthr hAn domain) hwidth hDA

/-- Cor 7.8 on top of Thm 5.12: an `h`-level shared-challenge binary fold of `width`-interleaved
words has at most `h * ⌊johnsonE0⌋₊ * |F|^(h-1)` bad challenge tuples (probability
`≤ h * johnsonE0 / |F|`); outside them the full tensor decomposition holds. -/
theorem johnson_tensorFold {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (n D A : ℕ) (eta : ℝ) (hD : 1 ≤ D) (hDn : D ≤ n - 2) (heta : 0 < eta)
    (ha : johnsonAgreement n D eta ≤ 1) (hthr : johnsonAgreement n D eta * n ≤ A)
    (hAn : A ≤ n) (hDA : D + 1 ≤ A) (domain : Fin n ↪ F) {width h : ℕ} (hwidth : 0 < width)
    (u : (Fin h → Bool) → Fin n → Fin width → F) :
    (TensorMCA.tensorFoldBad
        (johnson_levelWitness n D A eta hD hDn heta ha hthr hAn hDA domain hwidth) u).card ≤
      h * ⌊johnsonE0 n D A eta⌋₊ * Fintype.card F ^ (h - 1) ∧
    ∀ r ∉ TensorMCA.tensorFoldBad
        (johnson_levelWitness n D A eta hD hDn heta ha hthr hAn hDA domain hwidth) u,
      TensorMCA.HasFullTensorDecomposition ((code domain (D + 1)) ^⋈ (Fin width)) A r u :=
  ⟨TensorMCA.tensorFoldBad_card_le _ u,
   fun r hr ↦ TensorMCA.hasFullTensorDecomposition_of_not_mem_bad _ r u hr⟩

/-- Our instantiation: `eta := A/n - sqrt(D/n)` makes the analysed agreement exactly `A/n`,
so every hypothesis reduces to the integer facts `1 ≤ D ≤ n-2`, `n*D < A^2`, `A ≤ n`. -/
theorem johnsonAgreement_at (n D A : ℕ) :
    johnsonAgreement n D ((A : ℝ) / n - √((D : ℝ) / n)) = (A : ℝ) / n := by
  unfold johnsonAgreement johnsonRhoMinus; ring

theorem eta_pos_of (n D A : ℕ) (hn : 0 < n) (h : n * D < A * A) :
    0 < (A : ℝ) / n - √((D : ℝ) / n) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hlt : (D : ℝ) / n < ((A : ℝ) / n) ^ 2 := by
    rw [div_pow, div_lt_div_iff₀ hnR (by positivity)]
    have : ((n : ℝ) * D) < (A : ℝ) * A := by exact_mod_cast h
    nlinarith
  have hA : 0 ≤ (A : ℝ) / n := by positivity
  have := Real.sqrt_lt_sqrt (by positivity) hlt
  rw [Real.sqrt_sq hA] at this
  linarith

/-- Thm 5.12 exactly as bound_mca.py / dkt_verify.py use it: integer threshold `A` with
`n*D < A^2 ≤ ...`, radius `1 - A/n`, error `johnsonE0 n D A (A/n - sqrt(D/n)) / |F|`. -/
theorem o1_line_mcaError {F : Type} [Field F] [Fintype F] (n D A : ℕ) (hD : 1 ≤ D)
    (hDn : D ≤ n - 2) (hDA : n * D < A * A) (hAn : A ≤ n) (domain : Fin n ↪ F) :
    mcaError (AffineLineGenerator F) (code domain (D + 1)) (1 - (A : ℝ) / n) ≤
      min 1 (ENNReal.ofReal (johnsonE0 n D A ((A : ℝ) / n - √((D : ℝ) / n)) /
        (Fintype.card F : ℝ))) := by
  have hn : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have heta := eta_pos_of n D A hn hDA
  have hagr := johnsonAgreement_at n D A
  have ha : johnsonAgreement n D ((A : ℝ) / n - √((D : ℝ) / n)) ≤ 1 := by
    rw [hagr, div_le_one hnR]; exact_mod_cast hAn
  have h := johnson_lineMCA_probability n D _ hD hDn heta ha domain
  have hceil : Nat.ceil (johnsonAgreement n D ((A : ℝ) / n - √((D : ℝ) / n)) * n) = A := by
    rw [hagr, div_mul_cancel₀ _ hnR.ne', Nat.ceil_natCast]
  rw [hceil, hagr] at h
  exact h

end DKTVerify

#print axioms DKTVerify.johnson_lineExact
#print axioms DKTVerify.johnson_levelWitness
#print axioms DKTVerify.johnson_tensorFold
#print axioms DKTVerify.johnsonAgreement_at
#print axioms DKTVerify.eta_pos_of
#print axioms DKTVerify.o1_line_mcaError
