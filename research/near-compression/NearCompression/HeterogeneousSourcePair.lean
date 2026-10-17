import NearCompression.FunctionalOpeningFold
import NearCompression.GlobalChainGeometry

/-! Concrete source-pair projection for weighted_joint/derived_weight_joint.
The committed source lanes are arbitrary fixed functions. Exact authenticated
leaf contents and root geometry are explicit contracts; no proximity, Merkle,
Fiat--Shamir, or pre-GKR assignment claim is inferred. -/
namespace NearCompression
open Lean.Grind ZkFormal.Algebra
variable {K : Type} [Field K]

def betaWidePair (coefficients : List K) (leaf : List (K×K)) : K×K :=
  (weightedLaneValues coefficients (leaf.map Prod.fst),
    weightedLaneValues coefficients (leaf.map Prod.snd))

def liftedSourceFunctions (k : Nat) (sources : List (K → K)) : List (K → K) :=
  sources.map (fun f => fun x => f (x^(2^k)))

/-- Source leaves are lane-major adjacent plus/minus pairs, matching
check_opening's positions 2*lane and 2*lane+1. -/
def sourceWideLeaf (sources : List (K → K)) (x : K) : List (K×K) :=
  sources.map (fun f => (f x,f (-x)))

def projectedBetaPair (k d s : Nat) (coefficients : List K) (leaf : List (K×K)) : K×K :=
  let pair := betaWidePair coefficients leaf
  if k=0 then pair else
    let chosen := if (s%(4*d))/(2*d)=0 then pair.1 else pair.2
    (chosen,chosen)

theorem beta_wide_pair_exact (coefficients : List K) (sources : List (K → K)) (x : K) :
    betaWidePair coefficients (sourceWideLeaf sources x)=
      (weightedVirtualOracle coefficients sources x,weightedVirtualOracle coefficients sources (-x)) := by
  simp only [betaWidePair,sourceWideLeaf,weightedVirtualOracle,List.map_map,Function.comp_def]

private theorem weighted_lifted_eval (coefficients : List K) (sources : List (K → K)) (k : Nat) (x : K) :
    weightedVirtualOracle coefficients (liftedSourceFunctions k sources) x=
      weightedVirtualOracle coefficients sources (x^(2^k)) := by
  simp only [weightedVirtualOracle,liftedSourceFunctions,List.map_map,Function.comp_def]

/-- The quotient selects the canonical plus/minus source pair at its full
source-domain index; this is the precise side expression in the verifier. -/
theorem source_pair_full_index (eta : K) (d s : Nat) (positive : 0<d)
    (halfOrder : eta^(2*d)= -1) :
    eta^(s%(4*d))=
      if (s%(4*d))/(2*d)=0 then eta^(s%(2*d)) else -(eta^(s%(2*d))) := by
  have geometry := global_chain_pair_indices s (2*d) (by omega)
  have full : 2*(2*d)=4*d := by omega
  rw [full] at geometry
  have expand : eta^(s%(4*d))=eta^(s%(2*d))*(eta^(2*d))^((s%(4*d))/(2*d)) := by
    calc
      eta^(s%(4*d))=eta^(s%(2*d)+(2*d)*((s%(4*d))/(2*d))) := congrArg (fun e => eta^e) geometry.2.2
      _ = _ := by rw [Semiring.pow_add,pow_mul_eq]
  rw [expand,halfOrder]
  by_cases zero : (s%(4*d))/(2*d)=0
  · simp only [zero,ite_true,Semiring.pow_zero]; grind
  · have one : (s%(4*d))/(2*d)=1 := by
      have onlyOne : ∀ q : Nat,q<2 → q≠0 → q=1 := by intro q h h0; omega
      exact onlyOne _ geometry.2.1 zero
    simp only [one,Nat.reduceEqDiff,ite_false,Semiring.pow_one]
    grind

private theorem half_order_period (eta : K) (d : Nat) (halfOrder : eta^(2*d)= -1) :
    eta^(4*d)=1 := by
  have exp : 4*d=(2*d)*2 := by omega
  rw [exp,pow_mul_eq,halfOrder]
  simp only [Semiring.pow_succ,Semiring.pow_zero]
  grind

private theorem even_power_neg (x : K) (k : Nat) : (-x)^(2^(k+1))=x^(2^(k+1)) := by
  rw [Nat.pow_succ,pow_mul_eq,pow_mul_eq]
  have square : ∀ y : K,(-y)^2=y^2 := by intro y; simp only [Semiring.pow_succ,Semiring.pow_zero]; grind
  have exp : 2^(k+1)=2*2^k := by rw [Nat.pow_succ]; omega
  rw [←pow_mul_eq,←pow_mul_eq,←Nat.pow_succ,exp,pow_mul_eq,pow_mul_eq,square]

/-- A smaller branch's source-domain point is the sparse-lift power of the
common domain's canonical pair representative. -/
theorem heterogeneous_source_projection (omega : K) (k d D s : Nat)
    (degree : D=2^(k+1)*d) (halfOrder : (omega^(2^(k+1)))^(2*d)= -1) :
    (omega^(s%(2*D)))^(2^(k+1))=(omega^(2^(k+1)))^(s%(4*d)) := by
  let eta := omega^(2^(k+1))
  have period : eta^(4*d)=1 := half_order_period eta d halfOrder
  have bigPeriod : eta^(2*D)=1 := by
    have exp : 2*D=(4*d)*2^k := by rw [degree,Nat.pow_succ]; grind
    rw [exp,pow_mul_eq,period,Semiring.one_pow]
  have commute : (omega^(s%(2*D)))^(2^(k+1))=eta^(s%(2*D)) := by
    unfold eta
    rw [←pow_mul_eq,←pow_mul_eq]
    congr 1
    exact Nat.mul_comm _ _
  rw [commute,global_chain_pow_mod eta (2*D) s bigPeriod,
    global_chain_pow_mod eta (4*d) s period]

/-- Exact source-side refinement: the verifier's actual duplicate-side rule
and arbitrary beta combination produce the lifted virtual oracle at ±x.
Authentication is equality to one fixed wide oracle at the requested leaf;
no honest or nearby polynomial is required. -/
theorem heterogeneous_beta_pair_exact (omega : K) (k d D s : Nat) (positive : 0<d)
    (degree : D=2^k*d) (halfOrder : (omega^(2^k))^(2*d)= -1)
    (coefficients : List K) (sources : List (K → K)) (leaf : List (K×K))
    (authenticated : leaf=sourceWideLeaf sources ((omega^(2^k))^(s%(2*d)))) :
    projectedBetaPair k d s coefficients leaf=
      (weightedVirtualOracle coefficients (liftedSourceFunctions k sources) (omega^(s%(2*D))),
       weightedVirtualOracle coefficients (liftedSourceFunctions k sources) (-(omega^(s%(2*D))))) := by
  rw [authenticated]
  unfold projectedBetaPair
  rw [beta_wide_pair_exact,weighted_lifted_eval,weighted_lifted_eval]
  cases k with
  | zero => simp only [Nat.pow_zero,Semiring.pow_one,Nat.one_mul] at degree ⊢; subst D; rfl
  | succ k =>
    simp only [Nat.succ_ne_zero,ite_false]
    rw [even_power_neg,heterogeneous_source_projection omega k d D s degree halfOrder]
    rw [source_pair_full_index _ d s positive halfOrder]
    split <;> rfl

omit [Field K] in
/-- All actual source query indices are within their declared arrays, and the
selector is a bit. Domain binding still has to authenticate these indices. -/
theorem heterogeneous_source_query_indices (d s : Nat) (positive : 0<d) :
    s%(2*d)<2*d ∧ s%(4*d)<4*d ∧ (s%(4*d))/(2*d)<2 := by
  refine ⟨Nat.mod_lt _ (by omega),Nat.mod_lt _ (by omega),?_⟩
  have indices := global_chain_pair_indices s (2*d) (by omega)
  simpa only [show 2*(2*d)=4*d by omega] using indices.2.1

/-- Common-root half-order implies the smaller branch's half-order after its
sparse-lift power. No independently chosen branch root is permitted here. -/
theorem heterogeneous_half_order (omega : K) (k d D : Nat)
    (degree : D=2^k*d) (halfOrder : omega^(2*D)= -1) :
    (omega^(2^k))^(2*d)= -1 := by
  rw [←pow_mul_eq]
  have exponent : 2^k*(2*d)=2*D := by rw [degree]; grind
  rw [exponent,halfOrder]

/-- Direct instantiation of the initial oracle definition consumed by
FunctionalOpeningFold. The scalar beta coefficients are its exact MLE-derived
coefficients; the source functions are the branch's fixed lifted functions.
The plus/minus result is expressed as the actual initial-oracle indices used
by the first global-chain consistency check. -/
theorem heterogeneous_bound_initial_pair (omega : K) (k d D s n : Nat)
    (positive : 0<d) (degree : D=2^k*d) (halfOrder : omega^(2*D)= -1)
    (tables : List (Nat → K)) (sources : List (K → K)) (claim : List K → K)
    (point : List K) (tr : FoldTranscript K) (leaf : List (K×K))
    (authenticated : leaf=sourceWideLeaf sources ((omega^(2^k))^(s%(2*d)))) :
    projectedBetaPair k d s (functionalBatchCoefficients n tables (fun i => point.getD i 0)) leaf=
      ((bindFunctionalOpening omega n tables (liftedSourceFunctions k sources) claim point tr).oracles 0 (s%(2*D)),
       (bindFunctionalOpening omega n tables (liftedSourceFunctions k sources) claim point tr).oracles 0 (s%(2*D)+2*D)) := by
  have pair := heterogeneous_beta_pair_exact omega k d D s positive degree
    (heterogeneous_half_order omega k d D degree halfOrder)
    (functionalBatchCoefficients n tables (fun i => point.getD i 0)) sources leaf authenticated
  rw [pair]
  change (_,_) = (_,weightedVirtualOracle _ _ (omega^(s%(2*D)+2*D)))
  rw [Semiring.pow_add,halfOrder]
  have sign : omega^(s%(2*D))*(-1)= -(omega^(s%(2*D))) := by grind
  rw [sign]
  rfl

/-- Ordered lane concatenation corresponds exactly to the verifier's branch
accumulator when each branch's beta vector has the required lane count. -/
theorem weighted_virtual_append (a b : List K) (left right : List (K → K)) (x : K)
    (shape : a.length=left.length) :
    weightedVirtualOracle (a++b) (left++right) x=
      weightedVirtualOracle a left x+weightedVirtualOracle b right x := by
  unfold weightedVirtualOracle
  rw [List.map_append]
  induction a generalizing left with
  | nil => cases left <;> simp_all [weightedLaneValues]; grind
  | cons c cs ih =>
    cases left with
    | nil => simp at shape
    | cons f fs =>
      have tail : cs.length=fs.length := by simpa using shape
      simp only [List.cons_append,List.map_cons,weightedLaneValues,ih fs tail]
      grind

end NearCompression
