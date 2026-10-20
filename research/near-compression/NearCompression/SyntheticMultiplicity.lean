import NearCompression.CurveSupportInterpolation

/-! Characteristic-independent multiplicity foundations using synthetic
quotients. These statements concern formal polynomial coefficients, not just
functions on a finite field. Multi-point Hasse/GS interpolation remains open. -/
namespace NearCompression
open Lean.Grind ZkFormal.Algebra
variable {K : Type} [Field K]

/-- Successive synthetic remainders at a center; no factorial division. -/
def syntheticJet (p : Poly K) (a : K) : Nat→K
  | 0 => p.eval a
  | n+1 => syntheticJet (p.quot a) a n

/-- Taylor coefficients obtained by repeated synthetic division. -/
def syntheticTaylor (p : Poly K) (a : K) : Nat→List K
  | 0 => []
  | n+1 => p.eval a::syntheticTaylor (p.quot a) a n

/-- A root is removed at each step. Repeated nodes certify multiplicity;
distinctness is neither assumed nor needed for this certificate. -/
def SyntheticRootCertificate (p : Poly K) : List K→Prop
  | [] => True
  | a::rest => p.eval a=0 ∧ SyntheticRootCertificate (p.quot a) rest

theorem synthetic_quotient_coefficient (p : Poly K) (a : K) (i : Nat) :
    p.coeff (i+1)=(p.quot a).coeff i-a*(p.quot a).coeff (i+1) := by
  cases p with
  | mk cs =>
    induction cs with
    | nil => simp [Poly.quot,Poly.quotL,Poly.coeff];grind
    | cons c cs ih =>
      change (Poly.mk cs).coeff i=
        ((Poly.mk cs)+Poly.smul a ((Poly.mk cs).quot a)).coeff i-
          a*((Poly.mk cs)+Poly.smul a ((Poly.mk cs).quot a)).coeff (i+1)
      rw [Poly.coeff_add,Poly.coeff_add,Poly.coeff_smul,Poly.coeff_smul]
      grind

/-- Formal zero follows from a zero quotient and zero remainder, even over
finite fields where the zero function need not be the zero polynomial. -/
theorem synthetic_zero_from_quotient (p : Poly K) (a : K)
    (root : p.eval a=0) (zero : (p.quot a).IsZero) : p.IsZero := by
  have higher : ∀ i,p.coeff (i+1)=0 := by
    intro i
    rw [synthetic_quotient_coefficient,zero i,zero (i+1)]
    grind
  cases p with
  | mk cs =>
    cases cs with
    | nil => intro i;simp [Poly.coeff]
    | cons c cs =>
      have tail : (Poly.mk cs).IsZero := fun i=>higher i
      have ev:=Poly.eval_of_isZero tail a
      change c+a*(Poly.mk cs).eval a=0 at root
      rw [ev] at root
      have hc : c=0 := by grind
      intro i
      cases i with
      | zero => simpa [Poly.coeff] using hc
      | succ i => exact higher i

/-- Root count with repetitions, using checked sequential division. No
ordinary-derivative test is substituted for multiplicity. -/
theorem synthetic_root_certificate_zero (D : Nat) (p : Poly K)
    (degree : p.DegLt D) (nodes : List K) (enough : D≤nodes.length)
    (certificate : SyntheticRootCertificate p nodes) : p.IsZero := by
  induction D generalizing p nodes with
  | zero => exact fun i=>degree i (Nat.zero_le i)
  | succ d ih =>
    cases nodes with
    | nil => simp at enough
    | cons a rest =>
      exact synthetic_zero_from_quotient p a certificate.1
        (ih (p.quot a) (Poly.degLt_quot p a degree) rest (by simpa using enough) certificate.2)

theorem synthetic_taylor_evaluation (D : Nat) (p : Poly K) (a x : K)
    (degree : p.DegLt D) :
    (Poly.mk (syntheticTaylor p a D)).eval x=p.eval (a+x) := by
  induction D generalizing p with
  | zero =>
    have zero : p.IsZero := fun i=>degree i (Nat.zero_le i)
    change 0=p.eval (a+x)
    exact (Poly.eval_of_isZero zero (a+x)).symm
  | succ d ih =>
    have tail:=ih (p.quot a) (Poly.degLt_quot p a degree)
    have division:=Poly.eval_quot p a (a+x)
    change p.eval a+x*(Poly.mk (syntheticTaylor (p.quot a) a d)).eval x=p.eval (a+x)
    rw [tail]
    grind

theorem synthetic_taylor_coefficient (D : Nat) (p : Poly K) (a : K)
    (i : Nat) (index : i<D) :
    (Poly.mk (syntheticTaylor p a D)).coeff i=syntheticJet p a i := by
  induction D generalizing p i with
  | zero => omega
  | succ d ih =>
    cases i with
    | zero => rfl
    | succ i => exact ih (p.quot a) i (by omega)

/-- Vanishing jets are equivalent to a repeated-root certificate. -/
theorem synthetic_jets_certificate (m : Nat) (p : Poly K) (a : K) :
    (∀ i<m,syntheticJet p a i=0) ↔ SyntheticRootCertificate p (List.replicate m a) := by
  induction m generalizing p with
  | zero => simp [SyntheticRootCertificate]
  | succ m ih =>
    simp only [List.replicate_succ,SyntheticRootCertificate]
    constructor
    · intro jets
      refine ⟨jets 0 (by omega),(ih (p.quot a)).mp ?_⟩
      intro i hi
      exact jets (i+1) (by omega)
    · intro cert i hi
      cases i with
      | zero => exact cert.1
      | succ i => exact (ih (p.quot a)).mpr cert.2 i (by omega)

/-- A nonzero degree-<D polynomial has fewer than D vanishing synthetic jets
at any one point. This is valid in all field characteristics. -/
theorem synthetic_multiplicity_bound (D m : Nat) (p : Poly K) (a : K)
    (degree : p.DegLt D) (nonzero : ¬p.IsZero)
    (jets : ∀ i<m,syntheticJet p a i=0) : m<D := by
  apply Classical.byContradiction
  intro large
  exact nonzero (synthetic_root_certificate_zero D p degree (List.replicate m a)
    (by simp;omega) ((synthetic_jets_certificate m p a).mp jets))
end NearCompression
