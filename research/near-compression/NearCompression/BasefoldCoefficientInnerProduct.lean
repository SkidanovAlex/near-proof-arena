import NearCompression.GenericLaneBatching
import NearCompression.GenericRowMLE
import NearCompression.WHIRTerminalWeight

/-! Semantic change of view for the Basefold comparison: univariate monomial
coefficient slots become the Boolean values of an auxiliary multilinear P.
The original monomial evaluation is an inner product with R, not generally
the evaluation of P at the original point. No proximity theorem is claimed. -/
namespace NearCompression
open Lean.Grind ZkFormal.Algebra
variable {K : Type} [Field K]

def basefoldAuxiliary : List K → (Nat → K) → K
  | [],coefficients => coefficients 0
  | b::bs,coefficients =>
      (1-b)*basefoldAuxiliary bs (fun i => coefficients (2*i))+
      b*basefoldAuxiliary bs (fun i => coefficients (2*i+1))

/-- Multilinear extension of the Boolean weights product_i z_i^b_i. -/
def basefoldInnerWeight : List K → List K → K
  | [],_ => 1
  | _::_,[] => 0
  | z::zs,b::bs => (1+b*(z-1))*basefoldInnerWeight zs bs

theorem basefold_auxiliary_row_mle (bits : List K) (coefficients : Nat → K) :
    basefoldAuxiliary bits coefficients=
      genericRowMLE bits.length coefficients (fun i => bits.getD i 0) := by
  induction bits generalizing coefficients with
  | nil => rfl
  | cons b bs ih =>
    simp only [basefoldAuxiliary,List.length_cons,genericRowMLE,
      List.getD_cons_zero,List.getD_cons_succ,ih]

theorem basefold_tensor_lane_tensor (point : List K) (coefficients : Nat → K) :
    whirTensor point coefficients=
      laneTensor point.length coefficients (fun i => point.getD i 0) := by
  induction point generalizing coefficients with
  | nil => rfl
  | cons z zs ih =>
    simp only [whirTensor,List.length_cons,laneTensor,
      List.getD_cons_zero,List.getD_cons_succ,ih]

/-- R is explicit and succinct: one affine factor per coordinate. On the
Boolean cube its low-coordinate factors are respectively 1 and z. -/
theorem basefold_weight_zero (z : K) (zs bs : List K) :
    basefoldInnerWeight (z::zs) (0::bs)=basefoldInnerWeight zs bs := by
  simp only [basefoldInnerWeight]
  grind

theorem basefold_weight_one (z : K) (zs bs : List K) :
    basefoldInnerWeight (z::zs) (1::bs)=z*basefoldInnerWeight zs bs := by
  simp only [basefoldInnerWeight]
  grind

theorem basefold_coefficient_inner_product (point : List K) (coefficients : Nat → K) :
    whirCubeSum point.length (fun bits =>
      basefoldAuxiliary bits coefficients*basefoldInnerWeight point bits)=
      whirTensor point coefficients := by
  induction point generalizing coefficients with
  | nil => simp only [List.length_nil,whirCubeSum,basefoldAuxiliary,basefoldInnerWeight,whirTensor]; grind
  | cons z zs ih =>
    simp only [List.length_cons,whirCubeSum,whirTensor]
    have even : (fun bits => basefoldAuxiliary (0::bits) coefficients*
        basefoldInnerWeight (z::zs) (0::bits)) =
      (fun bits => basefoldAuxiliary bits (fun i => coefficients (2*i))*basefoldInnerWeight zs bits) := by
      funext bits
      simp only [basefoldAuxiliary,basefold_weight_zero]
      grind
    have odd : (fun bits => basefoldAuxiliary (1::bits) coefficients*
        basefoldInnerWeight (z::zs) (1::bits)) =
      (fun bits => z*(basefoldAuxiliary bits (fun i => coefficients (2*i+1))*basefoldInnerWeight zs bits)) := by
      funext bits
      simp only [basefoldAuxiliary,basefold_weight_one]
      grind
    rw [even,odd,whir_cube_scale,ih,ih]

/-- Direct composition with the existing monomial tensor used by the PCS.
Only the first 2^point.length coefficient slots are read; shorter lists are
zero-padded by getD. The protocol separately enforces its exact list shape. -/
theorem basefold_coefficient_inner_product_monomial (point coefficients : List K) :
    whirCubeSum point.length (fun bits =>
      genericRowMLE bits.length (fun i => coefficients.getD i 0) (fun i => bits.getD i 0)*
        basefoldInnerWeight point bits)=
      genericMonomialTensor point.length coefficients (fun i => point.getD i 0) := by
  have identity := basefold_coefficient_inner_product point (fun i => coefficients.getD i 0)
  simp only [basefold_auxiliary_row_mle,basefold_tensor_lane_tensor] at identity
  rw [lane_tensor_monomial]
  exact identity

/-- On a Boolean input, P returns the selected original coefficient slot. -/
theorem basefold_coefficient_boolean_value (n : Nat) (coefficients : List K)
    (bits : Nat → Bool) :
    genericRowMLE n (fun i => coefficients.getD i 0) (genericRowBooleanPoint bits)=
      coefficients.getD (genericRowBitIndex n bits) 0 :=
  generic_row_mle_boolean n _ bits

/-- The custom affine coefficient fold is partial evaluation of P, the
auxiliary multilinear, even though it is not monomial partial evaluation. -/
theorem basefold_auxiliary_affine_fold (r : K) (tail : List K) (coefficients : Nat → K) :
    basefoldAuxiliary (r::tail) coefficients =
      basefoldAuxiliary tail (fun i => coefficients (2*i)+r*(coefficients (2*i+1)-coefficients (2*i))) := by
  have form : (fun i => coefficients (2*i)+r*(coefficients (2*i+1)-coefficients (2*i))) =
      (fun i => (1-r)*coefficients (2*i)+r*coefficients (2*i+1)) := by
    funext i
    grind
  rw [form]
  simp only [basefoldAuxiliary,basefold_auxiliary_row_mle,generic_row_mle_add,generic_row_mle_scale]

theorem basefold_weight_affine_restriction (z r : K) (point tail : List K) :
    basefoldInnerWeight (z::point) (r::tail) =
      (1+r*(z-1))*basefoldInnerWeight point tail := rfl

end NearCompression
