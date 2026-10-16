import NearCompression.GenericMonomialTensor
import NearCompression.InstructionSumcheckSoundness

/-! Ordered power batching, with leading weight one. All lanes and claims
are fixed inputs before the batching parameter is sampled. -/
namespace NearCompression
open Lean.Grind ZkFormal.Algebra ArenaCore.Security
variable {K : Type} [Field K]

def lanePowerBatch (a : K) : List K → K
  | [] => 0
  | v::rest => v+a*lanePowerBatch a rest

def lanePolynomialBatch (a : K) : List (Poly K) → Poly K
  | [] => Poly.zero
  | p::rest => p+Poly.smul a (lanePolynomialBatch a rest)

theorem lane_power_batch_polynomial (a : K) (values : List K) :
    lanePowerBatch a values=(Poly.mk values).eval a := by
  induction values with
  | nil => rfl
  | cons v rest ih => simp only [lanePowerBatch,Poly.eval,Poly.evalL] at ih ⊢; rw [ih]

theorem lane_polynomial_batch_eval (a x : K) (lanes : List (Poly K)) :
    (lanePolynomialBatch a lanes).eval x=lanePowerBatch a (lanes.map (fun p => p.eval x)) := by
  induction lanes with
  | nil => rfl
  | cons p rest ih => simp only [lanePolynomialBatch,Poly.eval_add,Poly.eval_smul,List.map_cons,lanePowerBatch,ih]

theorem lane_polynomial_batch_coeff (a : K) (i : Nat) (lanes : List (Poly K)) :
    (lanePolynomialBatch a lanes).coeff i=lanePowerBatch a (lanes.map (fun p => p.coeff i)) := by
  induction lanes with
  | nil => simp [lanePolynomialBatch,Poly.coeff,Poly.zero,lanePowerBatch]
  | cons p rest ih => simp only [lanePolynomialBatch,Poly.coeff_add,Poly.coeff_smul,List.map_cons,lanePowerBatch,ih]

private theorem even_coeff_getD (cs : List K) (i : Nat) :
    (monomialEvenCoefficients cs).getD i 0=cs.getD (2*i) 0 := by
  induction i generalizing cs with
  | zero => cases cs with
    | nil => rfl
    | cons a rest => cases rest <;> rfl
  | succ i ih =>
    cases cs with
    | nil => simp [monomialEvenCoefficients]
    | cons a rest => cases rest with
      | nil => simp [monomialEvenCoefficients]
      | cons b rest =>
        have idx : 2*(i+1)=2*i+1+1 := by omega
        simp only [monomialEvenCoefficients,List.getD_cons_succ,idx,ih]

private theorem odd_coeff_getD (cs : List K) (i : Nat) :
    (monomialOddCoefficients cs).getD i 0=cs.getD (2*i+1) 0 := by
  induction i generalizing cs with
  | zero => cases cs with
    | nil => rfl
    | cons a rest => cases rest <;> rfl
  | succ i ih =>
    cases cs with
    | nil => simp [monomialOddCoefficients]
    | cons a rest => cases rest with
      | nil => simp [monomialOddCoefficients]
      | cons b rest =>
        have idx : 2*(i+1)+1=(2*i+1)+1+1 := by omega
        simp only [monomialOddCoefficients,List.getD_cons_succ,idx,ih]

def laneTensor : Nat → (Nat → K) → (Nat → K) → K
  | 0,cs,_ => cs 0
  | n+1,cs,point => laneTensor n (fun i => cs (2*i)) (fun i => point (i+1)) +
      point 0*laneTensor n (fun i => cs (2*i+1)) (fun i => point (i+1))

theorem lane_tensor_monomial (n : Nat) (cs : List K) (point : Nat → K) :
    genericMonomialTensor n cs point=laneTensor n (fun i => cs.getD i 0) point := by
  induction n generalizing cs point with
  | zero => rfl
  | succ n ih =>
    simp only [genericMonomialTensor,laneTensor,ih,even_coeff_getD,odd_coeff_getD]

private theorem lane_tensor_add (n : Nat) (a b point : Nat → K) :
    laneTensor n (fun i => a i+b i) point=laneTensor n a point+laneTensor n b point := by
  induction n generalizing a b point with
  | zero => rfl
  | succ n ih => simp only [laneTensor,ih]; grind

private theorem lane_tensor_scale (n : Nat) (s : K) (a point : Nat → K) :
    laneTensor n (fun i => s*a i) point=s*laneTensor n a point := by
  induction n generalizing a point with
  | zero => rfl
  | succ n ih => simp only [laneTensor,ih]; grind

private theorem lane_tensor_zero (n : Nat) (point : Nat → K) :
    laneTensor n (fun _ => (0:K)) point=0 := by
  induction n generalizing point with
  | zero => rfl
  | succ n ih => simp only [laneTensor,ih]; grind

theorem lane_polynomial_batch_tensor (n : Nat) (a : K) (lanes : List (Poly K))
    (point : Nat → K) :
    genericMonomialTensor n (lanePolynomialBatch a lanes).coeffs point=
      lanePowerBatch a (lanes.map (fun p => genericMonomialTensor n p.coeffs point)) := by
  simp only [lane_tensor_monomial]
  change laneTensor n (fun i => (lanePolynomialBatch a lanes).coeff i) point = _
  induction lanes with
  | nil =>
    change laneTensor n (fun _ => 0) point=0
    exact lane_tensor_zero n point
  | cons p rest ih =>
    simp only [lanePolynomialBatch,Poly.coeff_add,Poly.coeff_smul,lane_tensor_add,
      lane_tensor_scale,List.map_cons,lanePowerBatch]
    rw [ih]
    rfl

theorem lane_batch_affine_fold (a r : K) (pairs : List (K × K)) :
    lanePowerBatch a (pairs.map (fun v => (1-r)*v.1+r*v.2)) =
      (1-r)*lanePowerBatch a (pairs.map Prod.fst)+r*lanePowerBatch a (pairs.map Prod.snd) := by
  induction pairs with
  | nil => simp only [List.map_nil,lanePowerBatch]; grind
  | cons v rest ih => simp only [List.map_cons,lanePowerBatch,ih]; grind

/-- Decoding scalar RS leaf pairs and affine folding commute with batching.
The inverse constants are supplied explicitly; establishing them as 1/2
and 1/(2x) is the separate scalar-pair representation contract. -/
theorem lane_batch_decoded_pair_fold (a r invTwo invTwoX : K) (pairs : List (K × K)) :
    lanePowerBatch a (pairs.map (fun v =>
      (1-r)*((v.1+v.2)*invTwo)+r*((v.1-v.2)*invTwoX))) =
      (1-r)*((lanePowerBatch a (pairs.map Prod.fst)+lanePowerBatch a (pairs.map Prod.snd))*invTwo)+
      r*((lanePowerBatch a (pairs.map Prod.fst)-lanePowerBatch a (pairs.map Prod.snd))*invTwoX) := by
  induction pairs with
  | nil => simp only [List.map_nil,lanePowerBatch]; grind
  | cons v rest ih => simp only [List.map_cons,lanePowerBatch,ih]; grind

theorem lane_claim_batch_bad_count (sent source : List K) (L lane : Nat)
    (sentLen : sent.length=L) (sourceLen : source.length=L)
    (wrong : sent.getD lane 0 ≠ source.getD lane 0)
    (sample : List K) (distinct : sample.Nodup) :
    count sample (fun a => lanePowerBatch a sent=lanePowerBatch a source)+1≤L := by
  let f := (Poly.mk sent)-(Poly.mk source)
  have nz : ¬ f.IsZero := by
    intro zero
    have eq := zero lane
    change ((Poly.mk sent)-(Poly.mk source)).coeff lane=0 at eq
    rw [Poly.coeff_sub] at eq
    change sent.getD lane 0-source.getD lane 0=0 at eq
    grind
  have degree : f.DegLt L := by
    apply Poly.degLt_sub
    · simpa only [sentLen] using Poly.degLt_length (Poly.mk sent)
    · simpa only [sourceLen] using Poly.degLt_length (Poly.mk source)
  have roots := PolyRoots.cardRootsLe_of polyEval polyDeg quotFacts isZeroEval
    K f L sample nz degree distinct
  have subset : count sample (fun a => lanePowerBatch a sent=lanePowerBatch a source) ≤
      count sample (fun a => f.eval a=0) := by
    apply count_mono
    intro a eq
    rw [lane_power_batch_polynomial,lane_power_batch_polynomial] at eq
    simp only [f,Poly.eval_sub,eq]
    grind
  omega

theorem lane_claim_batch_bad_count_le (sent source : List K) (L lane : Nat)
    (positive : 0<L) (sentLen : sent.length=L) (sourceLen : source.length=L)
    (wrong : sent.getD lane 0 ≠ source.getD lane 0)
    (sample : List K) (distinct : sample.Nodup) :
    count sample (fun a => lanePowerBatch a sent=lanePowerBatch a source)≤L-1 := by
  have bound := lane_claim_batch_bad_count sent source L lane sentLen sourceLen wrong sample distinct
  omega

end NearCompression
