import ZkFormal.Algebra.PolyLemmas
import ZkFormal.Algebra.PolyRoots

/-! Deterministic full-domain terminal checks for scalar Reed--Solomon data.
Authenticated oracle values and their degree-bounded polynomial relation are
explicit hypotheses; this module proves no hash binding or security claim.
Equality is coefficientwise, allowing polynomial lists with trailing zeroes. -/
set_option autoImplicit false
namespace NearCompression
open Lean.Grind ZkFormal.Algebra
variable {K : Type} [Field K]

/-- At least D distinct checked scalar points uniquely determine degree < D. -/
theorem scalar_rs_domain_unique (left right : Poly K) (D : Nat) (domain : List K)
    (leftDegree : left.DegLt D) (rightDegree : right.DegLt D)
    (distinct : domain.Nodup) (enough : D≤domain.length)
    (equal : ∀ x∈domain,left.eval x=right.eval x) :
    (∀ i,left.coeff i=right.coeff i) ∧ (∀ x,left.eval x=right.eval x) := by
  have zero : (left-right).IsZero :=
    PolyRoots.eqZeroOfRoots_of polyEval polyDeg quotFacts isZeroEval K (left-right) D domain
      (Poly.degLt_sub leftDegree rightDegree) distinct enough (by
        intro x hx
        rw [Poly.eval_sub,equal x hx]
        grind)
  constructor
  · intro i
    have h:=zero i
    rw [Poly.coeff_sub] at h
    grind
  · intro x
    have h:=Poly.eval_of_isZero zero x
    rw [Poly.eval_sub] at h
    grind

/-- Concrete verifier loop over every scalar oracle location, with no random
sampling or probability side condition. -/
def scalarRSTerminalChecks [DecidableEq K] (coefficients : List K)
    (domain : List K) (oracle : K → K) : Bool :=
  domain.all (fun x => decide ((Poly.mk coefficients).eval x=oracle x))

/-- The disclosed list itself supplies its strict degree bound. `binding`
identifies the checked oracle values with the claimed committed polynomial;
it must come from the external commitment/extraction argument. -/
theorem scalar_rs_terminal_unique [DecidableEq K]
    (coefficients : List K) (committed : Poly K) (D : Nat) (domain : List K) (oracle : K → K)
    (shape : coefficients.length≤D) (degree : committed.DegLt D)
    (distinct : domain.Nodup) (enough : D≤domain.length)
    (binding : ∀ x∈domain,oracle x=committed.eval x)
    (checked : scalarRSTerminalChecks coefficients domain oracle=true) :
    (∀ i,(Poly.mk coefficients).coeff i=committed.coeff i) ∧
      (∀ x,(Poly.mk coefficients).eval x=committed.eval x) := by
  apply scalar_rs_domain_unique _ committed D domain
    ((Poly.degLt_length _).mono shape) degree distinct enough
  intro x hx
  have h := List.all_eq_true.mp checked x hx
  have eq : (Poly.mk coefficients).eval x=oracle x := of_decide_eq_true h
  exact eq.trans (binding x hx)

/-- Explicit residual coefficient linear functional. Its weights encode the
remaining opening equation, and are fixed by the caller's protocol state. -/
def scalarRSResidualFrom (p : Poly K) : Nat → List K → K
  | _,[] => 0
  | i,w::ws => w*p.coeff i+scalarRSResidualFrom p (i+1) ws

def scalarRSResidual (weights : List K) (p : Poly K) : K := scalarRSResidualFrom p 0 weights

theorem scalar_rs_residual_congr (left right : Poly K) (weights : List K)
    (equal : ∀ i,left.coeff i=right.coeff i) :
    scalarRSResidual weights left=scalarRSResidual weights right := by
  unfold scalarRSResidual
  generalize 0 = offset
  induction weights generalizing offset with
  | nil => rfl
  | cons w ws ih => simp only [scalarRSResidualFrom,equal,ih]

theorem scalar_rs_residual_add (left right : Poly K) (weights : List K) :
    scalarRSResidual weights (left+right)=scalarRSResidual weights left+scalarRSResidual weights right := by
  unfold scalarRSResidual
  generalize 0 = offset
  induction weights generalizing offset with
  | nil => simp only [scalarRSResidualFrom]; grind
  | cons w ws ih => simp only [scalarRSResidualFrom,Poly.coeff_add,ih]; grind

theorem scalar_rs_residual_scale (p : Poly K) (weights : List K) (scalar : K) :
    scalarRSResidual weights (Poly.smul scalar p)=scalar*scalarRSResidual weights p := by
  unfold scalarRSResidual
  generalize 0 = offset
  induction weights generalizing offset with
  | nil => simp only [scalarRSResidualFrom]; grind
  | cons w ws ih => simp only [scalarRSResidualFrom,Poly.coeff_smul,ih]; grind

/-- Full-domain scalar checks plus the actual residual functional equality
establish the committed polynomial's terminal claim, conditional only on the
explicit degree/domain/binding interfaces. No abstract `verified` predicate. -/
theorem scalar_rs_terminal_claim [DecidableEq K]
    (coefficients : List K) (committed : Poly K) (D : Nat) (domain : List K) (oracle : K → K)
    (shape : coefficients.length≤D) (degree : committed.DegLt D)
    (distinct : domain.Nodup) (enough : D≤domain.length)
    (binding : ∀ x∈domain,oracle x=committed.eval x)
    (checked : scalarRSTerminalChecks coefficients domain oracle=true)
    (weights : List K) (claim : K)
    (residual : scalarRSResidual weights (Poly.mk coefficients)=claim) :
    scalarRSResidual weights committed=claim := by
  have same := scalar_rs_terminal_unique coefficients committed D domain oracle
    shape degree distinct enough binding checked
  rw [←scalar_rs_residual_congr (Poly.mk coefficients) committed weights same.1]
  exact residual
/-- Finite-word entrypoint: the explicit length guard prevents truncated zip
checks from silently dropping domain points. -/
def scalarRSWordChecks [DecidableEq K] (coefficients : List K) (domain values : List K) : Bool :=
  decide (domain.length=values.length) &&
    (domain.zip values).all (fun pair => decide ((Poly.mk coefficients).eval pair.1=pair.2))

theorem scalar_rs_word_checks_complete [DecidableEq K]
    (coefficients : List K) (committed : Poly K) (domain values : List K)
    (binding : ∀ pair∈domain.zip values,pair.2=committed.eval pair.1)
    (checked : scalarRSWordChecks coefficients domain values=true) :
    ∀ x∈domain,(Poly.mk coefficients).eval x=committed.eval x := by
  induction domain generalizing values with
  | nil => simp
  | cons x xs ih =>
    cases values with
    | nil => simp [scalarRSWordChecks] at checked
    | cons y ys =>
      simp only [scalarRSWordChecks,List.length_cons,Nat.add_right_cancel_iff,
        List.zip_cons_cons,List.all_cons,Bool.and_eq_true,decide_eq_true_eq] at checked
      have head := binding (x,y) (by simp)
      have tail := ih ys (fun pair hp => binding pair (List.mem_cons_of_mem _ hp)) (by
        simp only [scalarRSWordChecks,Bool.and_eq_true,decide_eq_true_eq]
        exact ⟨checked.1,checked.2.2⟩)
      intro point hp
      rcases List.mem_cons.mp hp with rfl | hp
      · exact checked.2.1.trans head
      · exact tail point hp

/-- Word-level deterministic terminal rule, with explicit authenticated scalar
values, degree bound, complete distinct domain and residual equality. -/
theorem scalar_rs_word_terminal_claim [DecidableEq K]
    (coefficients : List K) (committed : Poly K) (D : Nat) (domain values : List K)
    (shape : coefficients.length≤D) (degree : committed.DegLt D)
    (distinct : domain.Nodup) (enough : D≤domain.length)
    (binding : ∀ pair∈domain.zip values,pair.2=committed.eval pair.1)
    (checked : scalarRSWordChecks coefficients domain values=true)
    (weights : List K) (claim : K)
    (residual : scalarRSResidual weights (Poly.mk coefficients)=claim) :
    (∀ i,(Poly.mk coefficients).coeff i=committed.coeff i) ∧
      scalarRSResidual weights committed=claim := by
  have same := scalar_rs_domain_unique (Poly.mk coefficients) committed D domain
    ((Poly.degLt_length _).mono shape) degree distinct enough
    (scalar_rs_word_checks_complete coefficients committed domain values binding checked)
  refine ⟨same.1,?_⟩
  rw [←scalar_rs_residual_congr (Poly.mk coefficients) committed weights same.1]
  exact residual
end NearCompression
