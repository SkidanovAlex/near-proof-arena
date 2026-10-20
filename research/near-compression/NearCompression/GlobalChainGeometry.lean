import NearCompression.GenericRSPairRepresentation

/-! Natural-domain projection and authenticated pair-side geometry. Domain
root equations are explicit hypotheses; no proximity or hash claim. -/
namespace NearCompression
open Lean.Grind ZkFormal.Algebra
variable {K : Type} [Field K]

theorem global_chain_pow_mod (omega : K) (N s : Nat) (period : omega^N=1) :
    omega^(s%N)=omega^s := by
  conv => rhs; rw [← Nat.mod_add_div s N]
  rw [Semiring.pow_add,pow_mul_eq,period,Semiring.one_pow]
  grind

/-- At stage j the root omega0^(2^j) and reduced index denote the repeated
square of the original full-domain point. -/
theorem global_chain_projection (omega : K) (s j N : Nat)
    (period : (omega^(2^j))^N=1) :
    (omega^(2^j))^(s%N)=(omega^s)^(2^j) := by
  rw [global_chain_pow_mod _ N s period,←pow_mul_eq,←pow_mul_eq]
  congr 1
  exact Nat.mul_comm _ _

theorem global_chain_pair_indices (s D : Nat) (positive : 0<D) :
    (s%(2*D))%D=s%D ∧
    (s%(2*D))/D<2 ∧
    s%(2*D)=s%D+D*((s%(2*D))/D) := by
  have modEq : (s%(2*D))%D=s%D :=
    Nat.mod_mod_of_dvd s (by exact ⟨2, by omega⟩)
  have bound := Nat.mod_lt s (show 0<2*D by omega)
  have division := Nat.mod_add_div (s%(2*D)) D
  rw [modEq] at division
  constructor
  · exact modEq
  constructor
  · exact (Nat.div_lt_iff_lt_mul positive).mpr bound
  · omega

/-- Squaring the source pair's canonical representative lands at the side
selected by the implementation's integer quotient. -/
theorem global_chain_next_pair_side (omega : K) (s D : Nat) (positive : 0<D)
    (halfOrder : (omega*omega)^D = -1) :
    let x := omega^(s%(2*D))
    let y := (omega*omega)^(s%D)
    x*x = if (s%(2*D))/D=0 then y else -y := by
  dsimp only
  have indices := global_chain_pair_indices s D positive
  have square : ∀ i : Nat, omega^i*omega^i=(omega*omega)^i := by
    intro i
    have a : omega*omega=omega^2 := by simp only [Semiring.pow_succ,Semiring.pow_zero]; grind
    rw [a,←pow_mul_eq]
    rw [← Semiring.pow_add]
    congr 1
    omega
  rw [square]
  conv => lhs; rw [indices.2.2,Semiring.pow_add,pow_mul_eq,halfOrder]
  have sideBound := indices.2.1
  by_cases side : (s%(2*D))/D=0
  · simp only [side,ite_true,Semiring.pow_zero]; grind
  · have onlyOne : ∀ q : Nat, q<2 → q≠0 → q=1 := by intro q h h0; omega
    have one : (s%(2*D))/D=1 := onlyOne _ sideBound side
    simp only [one,Semiring.pow_one]
    grind

/-- The full source-domain index and the canonical pair representative
may differ by sign, but have the same square. -/
theorem global_chain_source_square (omega : K) (s D : Nat)
    (period : omega^(4*D)=1) :
    (omega^(s%(4*D)))*(omega^(s%(4*D))) =
      (omega^(s%(2*D)))*(omega^(s%(2*D))) := by
  have square : ∀ i : Nat, omega^i*omega^i=(omega^2)^i := by
    intro i
    rw [← Semiring.pow_add,←pow_mul_eq]
    congr 1
    omega
  have squaredPeriod : (omega^2)^(2*D)=1 := by
    rw [←pow_mul_eq]
    have exponent : 2*(2*D)=4*D := by omega
    rw [exponent,period]
  have fullPeriod : (omega^2)^(4*D)=1 := by
    rw [←pow_mul_eq]
    have exponent : 2*(4*D)=(4*D)*2 := by omega
    rw [exponent,pow_mul_eq,period,Semiring.one_pow]
  rw [square,square,global_chain_pow_mod _ _ _ fullPeriod,
    global_chain_pow_mod _ _ _ squaredPeriod]

def globalChainFoldPolynomial (r : K) (coefficients : List K) : Poly K :=
  Poly.smul (1-r) (Poly.mk (monomialEvenCoefficients coefficients))+
    Poly.smul r (Poly.mk (monomialOddCoefficients coefficients))

theorem global_chain_decode_fold (r x : K) (coefficients : List K)
    (h2 : (2 : K) ≠ 0) (hx : x ≠ 0) :
    let eo := rsPairDecode x ((Poly.mk coefficients).eval x,(Poly.mk coefficients).eval (-x))
    eo.1+r*(eo.2-eo.1)=(globalChainFoldPolynomial r coefficients).eval (x*x) := by
  dsimp only
  rw [rs_polynomial_pair_decode coefficients x h2 hx]
  simp only [globalChainFoldPolynomial,Poly.eval_add,Poly.eval_smul]
  grind

/-- Exact meaning of the selected component of an authenticated next pair. -/
theorem global_chain_next_pair_evaluation (omega : K) (s D : Nat) (positive : 0<D)
    (halfOrder : (omega*omega)^D = -1) (next : Poly K) :
    let x := omega^(s%(2*D))
    let y := (omega*omega)^(s%D)
    (if (s%(2*D))/D=0 then next.eval y else next.eval (-y))=next.eval (x*x) := by
  dsimp only
  rw [global_chain_next_pair_side omega s D positive halfOrder]
  split <;> rfl

/-- The local pair check is precisely equality of the folded source
polynomial and next polynomial at the squared FULL-domain chain point.
It holds for any candidate next polynomial, without assuming consistency. -/
theorem global_chain_pair_check_iff (omega r : K) (s D : Nat) (positive : 0<D)
    (period : omega^(4*D)=1) (halfOrder : (omega*omega)^D = -1)
    (h2 : (2 : K) ≠ 0) (hx : omega^(s%(2*D)) ≠ 0)
    (coefficients : List K) (next : Poly K) :
    let x := omega^(s%(2*D))
    let y := (omega*omega)^(s%D)
    let full := omega^(s%(4*D))
    let eo := rsPairDecode x ((Poly.mk coefficients).eval x,(Poly.mk coefficients).eval (-x))
    (eo.1+r*(eo.2-eo.1) =
      (if (s%(2*D))/D=0 then next.eval y else next.eval (-y))) ↔
    (globalChainFoldPolynomial r coefficients).eval (full*full)=next.eval (full*full) := by
  dsimp only
  rw [global_chain_decode_fold r _ coefficients h2 hx,
    global_chain_next_pair_evaluation omega s D positive halfOrder next,
    global_chain_source_square omega s D period]

end NearCompression
