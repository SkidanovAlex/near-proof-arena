import NearCompression.IndependentConstraintMixing
import NearCompression.FiniteRSJohnsonCandidates

/-! Fixed-oracle Johnson candidates for the actual independent-mixer update.
This is a finite ideal sampling theorem, not commitment extraction or QROM. -/
namespace NearCompression
open Lean.Grind ZkFormal.Algebra ArenaCore.Security
variable {K : Type} [Field K]

/-- Canonical coefficient vector paired with the carried functional weights. -/
def switchPolynomialPairs (D : Nat) (weights : List K) (p : Poly K) : List (K × K) :=
  (rateShiftNormalize D p).coeffs.zip weights

omit [Field K] in
private theorem zip_first (cs ws : List K) (shape : cs.length=ws.length) :
    (cs.zip ws).map Prod.fst=cs := by
  induction cs generalizing ws with
  | nil => simp
  | cons c cs ih =>
    cases ws with
    | nil => simp at shape
    | cons w ws => simp only [List.length_cons] at shape
                   simp [ih ws (by omega)]

/-- Exact weight shape prevents silent truncation of candidate coefficients. -/
theorem switch_polynomial_pairs_coefficients (D : Nat) (weights : List K)
    (shape : weights.length=D) (p : Poly K) :
    (switchPolynomialPairs D weights p).map Prod.fst=(rateShiftNormalize D p).coeffs := by
  apply zip_first
  rw [rate_shift_normalize_length,shape]

/-- All predicates refer to the SAME polynomial, even when it is chosen after
mixers. Agreement is with a fixed received oracle. -/
def SwitchCloseMixedBad (domain : List K) (received : K→K) (D T : Nat)
    (weights : List K) (claim : K) (templates : List (K × K)) (mixers : List K) : Prop :=
  ∃ p : Poly K, p.DegLt D ∧ T≤count domain (fun x=>p.eval x=received x) ∧
    SwitchCandidateWrong (switchPolynomialPairs D weights p) claim templates ∧
    SwitchMixedAccept (switchPolynomialPairs D weights p) claim templates mixers

/-- Complete Johnson family controls adaptive selection of a close candidate.
Alphabet completeness is essential; neither candidate existence nor closeness
is inferred from acceptance of the concrete committed protocol. -/
theorem switch_johnson_mixing_count (alphabet domain : List K)
    (complete : ∀ a,a∈alphabet) (received : K→K) (D T : Nat)
    (weights : List K) (claim : K) (templates : List (K × K))
    (sample : List K) (distinct : sample.Nodup) :
    count (uniformTuples sample templates.length)
      (SwitchCloseMixedBad domain received D T weights claim templates)≤
    (johnsonCandidateList alphabet domain received D T).length*
      sample.length^(templates.length-1) := by
  let family := (johnsonCandidateList alphabet domain received D T).map
    (fun p=>p.coeffs.zip weights)
  have bound:=switch_candidate_family_mixing_count family claim templates sample distinct
  have subset : count (uniformTuples sample templates.length)
      (SwitchCloseMixedBad domain received D T weights claim templates)≤
      count (uniformTuples sample templates.length) (fun rs=>∃ xs∈family,
        SwitchCandidateWrong xs claim templates ∧ SwitchMixedAccept xs claim templates rs) := by
    apply count_mono
    intro rs h
    obtain ⟨p,degree,close,wrong,accept⟩:=h
    refine ⟨switchPolynomialPairs D weights p,?_,wrong,accept⟩
    exact List.mem_map.mpr ⟨rateShiftNormalize D p,
      johnson_candidate_list_complete alphabet domain complete received D T p degree close,rfl⟩
  simpa only [family,List.length_map] using Nat.le_trans subset bound

/-- Denominator-free bound: bad probability ≤ N²/(gap*|sample|) when
sample and gap are positive, where gap=T²-N*(D-1). A zero gap makes this
inequality vacuous. The alphabet for candidates and sampler may differ. -/
theorem switch_johnson_mixing_gap (alphabet domain : List K)
    (complete : ∀ a,a∈alphabet) (domainDistinct : domain.Nodup)
    (received : K→K) (D T : Nat) (gap : domain.length*(D-1)≤T*T)
    (weights : List K) (claim : K) (templates : List (K × K))
    (sample : List K) (distinct : sample.Nodup) (nonempty : 0<templates.length) :
    count (uniformTuples sample templates.length)
      (SwitchCloseMixedBad domain received D T weights claim templates)*sample.length*
        (T*T-domain.length*(D-1))≤
      domain.length*domain.length*sample.length^templates.length := by
  have mixing:=switch_johnson_mixing_count alphabet domain complete received D T
    weights claim templates sample distinct
  have size:=johnson_candidate_list_gap_bound alphabet domain domainDistinct received D T gap
  have power : sample.length^(templates.length-1)*sample.length=sample.length^templates.length := by
    rw [←Nat.pow_succ];congr 1;omega
  have scaled:=Nat.mul_le_mul_right sample.length mixing
  rw [Nat.mul_assoc,power] at scaled
  have combined:=Nat.mul_le_mul_right (T*T-domain.length*(D-1)) scaled
  have sized:=Nat.mul_le_mul_right (sample.length^templates.length) size
  exact Nat.le_trans combined (by simpa only [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using sized)
end NearCompression
