import NearCompression.GenericAirRoundDegree
import NearCompression.AdaptivePolynomialSumcheck
import NearCompression.AirCombinedResidualRows

namespace NearCompression
open Lean.Grind ZkFormal.Air ZkFormal.Algebra
variable {K : Type} [Field K]

def busFormulaDegree : BusProgramFormula K→Nat
  | .literal _ => 0
  | .current _ | .next _ | .first | .last | .transition => 1
  | .add a b | .sub a b => max (busFormulaDegree a) (busFormulaDegree b)
  | .mul a b => busFormulaDegree a+busFormulaDegree b

def busPolynomialLower (p : AirPolynomialInputs K) : BusProgramFormula K→Poly K
  | .literal x => Poly.C x
  | .current c => p.col c false
  | .next c => p.col c true
  | .first => p.isFirst
  | .last => p.isLast
  | .transition => p.isTransition
  | .add a b => busPolynomialLower p a+busPolynomialLower p b
  | .sub a b => busPolynomialLower p a-busPolynomialLower p b
  | .mul a b => busPolynomialLower p a*busPolynomialLower p b

def busPolynomialPointEnv (p : AirPolynomialInputs K) (x : K) : TerminalProgramEnvironment K where
  current:=fun c=>(p.col c false).eval x
  next:=fun c=>(p.col c true).eval x
  first:=p.isFirst.eval x
  last:=p.isLast.eval x
  transition:=p.isTransition.eval x

theorem bus_polynomial_lower_eval (p : AirPolynomialInputs K) (formula : BusProgramFormula K) (x : K) :
    (busPolynomialLower p formula).eval x=busProgramFormulaValue (busPolynomialPointEnv p x) formula := by
  induction formula with
  | literal value => exact Poly.eval_C _ _
  | current c | next c | first | last | transition => rfl
  | add a b ha hb => simp only [busPolynomialLower,Poly.eval_add,ha,hb,busProgramFormulaValue]
  | sub a b ha hb => simp only [busPolynomialLower,Poly.eval_sub,ha,hb,busProgramFormulaValue]
  | mul a b ha hb => simp only [busPolynomialLower,Poly.eval_mul,ha,hb,busProgramFormulaValue]

theorem bus_polynomial_lower_degree (p : AirPolynomialInputs K) (affine : AirPolynomialAffine p)
    (formula : BusProgramFormula K) : (busPolynomialLower p formula).DegLt (busFormulaDegree formula+1) := by
  induction formula with
  | literal value => exact Poly.degLt_length _
  | current c => exact affine.col c false
  | next c => exact affine.col c true
  | first => exact affine.isFirst
  | last => exact affine.isLast
  | transition => exact affine.isTransition
  | add a b ha hb =>
    exact Poly.degLt_add
      (ha.mono (Nat.add_le_add_right (Nat.le_max_left _ _) 1))
      (hb.mono (Nat.add_le_add_right (Nat.le_max_right _ _) 1))
  | sub a b ha hb =>
    exact Poly.degLt_sub
      (ha.mono (Nat.add_le_add_right (Nat.le_max_left _ _) 1))
      (hb.mono (Nat.add_le_add_right (Nat.le_max_right _ _) 1))
  | mul a b ha hb => exact Poly.degLt_mul ha hb

private theorem batch_degree (mixing : K) (polys : List (Poly K)) (d : Nat)
    (bounds : ∀ p∈polys,p.DegLt (d+1)) : (lanePolynomialBatch mixing polys).DegLt (d+1) := by
  induction polys with
  | nil => exact (Poly.degLt_length Poly.zero).mono (Nat.zero_le _)
  | cons p rest ih =>
    exact Poly.degLt_add (bounds p (List.mem_cons_self ..))
      (Poly.degLt_smul mixing (ih (fun q hq=>bounds q (List.mem_cons_of_mem _ hq))))

/-- Source residuals followed by auxiliary residuals, with precisely the same
power-batching order as the combined row/point evaluator. -/
def combinedAirPolynomial (p : AirPolynomialInputs K) (source : List Expr)
    (auxiliary : List (BusProgramFormula K)) (mixing : K) : Poly K :=
  lanePolynomialBatch mixing (source.map (airPolynomialLower p)++auxiliary.map (busPolynomialLower p))

theorem combined_air_polynomial_eval (p : AirPolynomialInputs K) (source : List Expr)
    (auxiliary : List (BusProgramFormula K)) (mixing x : K) :
    (combinedAirPolynomial p source auxiliary mixing).eval x=
      lanePowerBatch mixing (source.map (fun e=>e.evalWith (airPolynomialPointEnv p x))++
        auxiliary.map (busProgramFormulaValue (busPolynomialPointEnv p x))) := by
  simp only [combinedAirPolynomial,lane_polynomial_batch_eval,List.map_append,List.map_map,
    Function.comp_def,air_polynomial_lower_eval,bus_polynomial_lower_eval]

theorem combined_air_polynomial_degree (p : AirPolynomialInputs K) (affine : AirPolynomialAffine p)
    (source : List Expr) (auxiliary : List (BusProgramFormula K)) (mixing : K) (d : Nat)
    (sourceDegrees : ∀ e∈source,e.degree≤d) (auxDegrees : ∀ e∈auxiliary,busFormulaDegree e≤d) :
    (combinedAirPolynomial p source auxiliary mixing).DegLt (d+1) := by
  apply batch_degree
  intro poly hp
  rcases List.mem_append.mp hp with hp | hp
  · obtain ⟨e,he,rfl⟩:=List.mem_map.mp hp
    exact (air_polynomial_lower_degree p affine e).mono (Nat.add_le_add_right (sourceDegrees e he) 1)
  · obtain ⟨e,he,rfl⟩:=List.mem_map.mp hp
    exact (bus_polynomial_lower_degree p affine e).mono (Nat.add_le_add_right (auxDegrees e he) 1)

/-- Each suffix assignment supplies one affine coordinate environment and
one affine equality weight. Both source and auxiliary expressions are lowered. -/
def combinedAirRoundPolynomial (source : List Expr) (auxiliary : List (BusProgramFormula K))
    (mixing : K) : List (AirPolynomialInputs K × Poly K)→Poly K
  | [] => Poly.zero
  | (p,w)::rest => w*combinedAirPolynomial p source auxiliary mixing+
      combinedAirRoundPolynomial source auxiliary mixing rest

theorem combined_air_round_eval (source : List Expr) (auxiliary : List (BusProgramFormula K))
    (mixing x : K) (slices : List (AirPolynomialInputs K × Poly K)) :
    (combinedAirRoundPolynomial source auxiliary mixing slices).eval x=
      (slices.map (fun pw=>pw.2.eval x*lanePowerBatch mixing
        (source.map (fun e=>e.evalWith (airPolynomialPointEnv pw.1 x))++
          auxiliary.map (busProgramFormulaValue (busPolynomialPointEnv pw.1 x))))).sum := by
  induction slices with
  | nil => rfl
  | cons pw rest ih => simp only [combinedAirRoundPolynomial,Poly.eval_add,Poly.eval_mul,
      combined_air_polynomial_eval,List.map_cons,List.sum_cons,ih]

theorem combined_air_round_degree (source : List Expr) (auxiliary : List (BusProgramFormula K))
    (mixing : K) (slices : List (AirPolynomialInputs K × Poly K)) (d : Nat)
    (sourceDegrees : ∀ e∈source,e.degree≤d) (auxDegrees : ∀ e∈auxiliary,busFormulaDegree e≤d)
    (affine : ∀ pw∈slices,AirPolynomialAffine pw.1 ∧ pw.2.DegLt 2) :
    (combinedAirRoundPolynomial source auxiliary mixing slices).DegLt (d+2) := by
  induction slices with
  | nil => exact (Poly.degLt_length Poly.zero).mono (Nat.zero_le _)
  | cons pw rest ih =>
    obtain ⟨hp,hw⟩:=affine pw (List.mem_cons_self ..)
    have bound:=Poly.degLt_mul hw (combined_air_polynomial_degree pw.1 hp source auxiliary mixing d sourceDegrees auxDegrees)
    apply Poly.degLt_add
    · simpa [Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using bound
    · exact ih (fun pw hm=>affine pw (List.mem_cons_of_mem _ hm))

/-- Adaptive composition with the honest degree derived from the combined
source/auxiliary ASTs. Slice representation and terminal authentication remain
explicit obligations; no detached honest-degree certificate is required. -/
theorem combined_air_adaptive_sumcheck_count (sample : List K) (distinct : sample.Nodup)
    (source : List Expr) (auxiliary : List (BusProgramFormula K)) (mixing : K)
    (d rounds : Nat) (f : List K→K) (sent : List K→Poly K) (claim : List K→K)
    (slices : List K→List (AirPolynomialInputs K × Poly K))
    (sourceDegrees : ∀ e∈source,e.degree≤d) (auxDegrees : ∀ e∈auxiliary,busFormulaDegree e≤d)
    (affine : ∀ h, h.length<rounds → ∀ pw∈slices h,AirPolynomialAffine pw.1 ∧ pw.2.DegLt 2)
    (represents : ∀ h, h.length<rounds → ∀ r,
      (combinedAirRoundPolynomial source auxiliary mixing (slices h)).eval r=
        polynomialSumcheckTruth rounds f (h++[r]))
    (wrong : claim []≠whirCubeSum rounds f) :
    ArenaCore.Security.count (uniformTuples sample rounds)
      (fun path=>polynomialSumcheckChecks (d+1) sent claim [] path ∧ claim path=f path)*sample.length≤
      ((d+1)*rounds)*sample.length^rounds := by
  exact adaptive_polynomial_cube_sumcheck_count sample distinct (d+1) rounds f sent
    (fun h=>combinedAirRoundPolynomial source auxiliary mixing (slices h)) claim
    (fun h hh=>combined_air_round_degree source auxiliary mixing (slices h) d sourceDegrees auxDegrees (affine h hh))
    represents wrong

end NearCompression
