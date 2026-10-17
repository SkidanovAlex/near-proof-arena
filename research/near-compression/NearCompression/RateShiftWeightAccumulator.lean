import NearCompression.RateShiftConstraintMixing
import NearCompression.InterleavedResidual
namespace NearCompression
open Lean.Grind ZkFormal.Algebra
variable {K : Type} [Field K]

/-- Coefficient-order monomial weights, including the constant coefficient. -/
def rateShiftMonomialWeights (x : K) : Nat → List K
  | 0 => []
  | n+1 => 1 :: (rateShiftMonomialWeights x n).map (x*·)

private theorem dot_scale (w cs : List K) (s : K) :
    coefficientDot (w.map (s*·)) cs=s*coefficientDot w cs := by
  induction w generalizing cs with
  | nil => simp only [List.map_nil,coefficientDot]; grind
  | cons a w ih => simp only [List.map_cons,coefficientDot,ih]; grind

private theorem dot_empty (w : List K) : coefficientDot w []=0 := by
  induction w with
  | nil => rfl
  | cons a w ih => simp only [coefficientDot,List.getD_nil,List.drop_nil,ih]; grind

theorem rate_shift_monomial_weights_length (x : K) (n : Nat) :
    (rateShiftMonomialWeights x n).length=n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [rateShiftMonomialWeights,List.length_cons,List.length_map,ih]

/-- The generated coordinates are the executable powers x^i. -/
theorem rate_shift_monomial_weights_coordinate (x : K) (n i : Nat) (bound : i<n) :
    (rateShiftMonomialWeights x n).getD i 0=x^i := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
    cases i with
    | zero => simp [rateShiftMonomialWeights]; grind
    | succ i =>
      have hi : i<(rateShiftMonomialWeights x n).length := by
        rw [rate_shift_monomial_weights_length];omega
      simp only [rateShiftMonomialWeights,List.getD_cons_succ]
      simp only [List.getD,List.getElem?_map,List.getElem?_eq_getElem hi,Option.map_some,Option.getD_some]
      have prev:=ih i (by omega)
      simp only [List.getD,List.getElem?_eq_getElem hi,Option.getD_some] at prev
      rw [prev]
      grind

theorem rate_shift_monomial_dot (x : K) (n : Nat) (cs : List K) (size : cs.length≤n) :
    coefficientDot (rateShiftMonomialWeights x n) cs=(Poly.mk cs).eval x := by
  induction n generalizing cs with
  | zero => cases cs with
    | nil => rfl
    | cons c cs => simp at size
  | succ n ih =>
    cases cs with
    | nil => exact dot_empty _
    | cons c cs =>
      simp only [rateShiftMonomialWeights,coefficientDot,List.getD_cons_zero,
        List.drop_succ_cons,List.drop_zero,dot_scale]
      rw [ih cs (by simp only [List.length_cons] at size;omega)]
      simp only [Poly.eval,Poly.evalL]; grind

private theorem dot_zip_add (a b cs : List K) (size : a.length=b.length) :
    coefficientDot (List.zipWith (·+·) a b) cs=coefficientDot a cs+coefficientDot b cs := by
  induction a generalizing b cs with
  | nil => cases b <;> simp_all [coefficientDot] <;> grind
  | cons a as ih =>
    cases b with
    | nil => simp at size
    | cons b bs =>
      simp only [List.zipWith_cons_cons,coefficientDot]
      rw [ih bs (cs.drop 1) (by simpa using size)]
      grind

/-- Literal zip update; equal vector sizes prevent dropped coefficients. -/
def rateShiftAddWeights (weights : List K) (x power : K) : List K :=
  List.zipWith (·+·) weights ((rateShiftMonomialWeights x weights.length).map (power*·))

theorem rate_shift_add_weights_length (weights : List K) (x power : K) :
    (rateShiftAddWeights weights x power).length=weights.length := by
  simp [rateShiftAddWeights,rate_shift_monomial_weights_length]

theorem rate_shift_add_weights_dot (weights cs : List K) (x power : K)
    (size : cs.length≤weights.length) :
    coefficientDot (rateShiftAddWeights weights x power) cs=
      coefficientDot weights cs+power*(Poly.mk cs).eval x := by
  unfold rateShiftAddWeights
  rw [dot_zip_add _ _ _ (by simp [rate_shift_monomial_weights_length]),dot_scale,
    rate_shift_monomial_dot x weights.length cs size]

/-- Sequential power progression used by the executable accumulator. -/
def rateShiftAccumulateWeights (weights : List K) (gamma power : K) : List K → List K
  | [] => weights
  | x::xs => rateShiftAccumulateWeights (rateShiftAddWeights weights x power) gamma (power*gamma) xs

private theorem accumulate_dot (points weights cs : List K) (gamma power : K)
    (size : cs.length≤weights.length) :
    coefficientDot (rateShiftAccumulateWeights weights gamma power points) cs=
      coefficientDot weights cs+power*Poly.evalL gamma (points.map (Poly.mk cs).eval) := by
  induction points generalizing weights power with
  | nil => simp only [rateShiftAccumulateWeights,List.map_nil,Poly.evalL]; grind
  | cons x xs ih =>
    rw [rateShiftAccumulateWeights,ih _ _ (by simpa only [rate_shift_add_weights_length] using size),
      rate_shift_add_weights_dot weights cs x power size]
    simp only [List.map_cons,Poly.evalL]; grind

/-- The executable vector update realizes the same fixed-candidate functional
as the mixing root bound. Valid at gamma=0 and for zero old weights. -/
theorem rate_shift_accumulated_weights_functional (weights points : List K) (gamma : K)
    (candidate : Poly K) (size : candidate.coeffs.length≤weights.length) :
    scalarRSResidual (rateShiftAccumulateWeights weights gamma gamma points) candidate=
      rateShiftAccumulatedFunctional weights points gamma candidate := by
  simp only [scalarRSResidual,scalar_residual_dot,List.drop_zero,
    rateShiftAccumulatedFunctional,rateShiftCandidateValues,Poly.eval,Poly.evalL]
  exact accumulate_dot points weights candidate.coeffs gamma gamma size
end NearCompression
