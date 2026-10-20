import NearCompression.HeterogeneousSourcePair
import NearCompression.GroupedCosetFold

/-! Deterministic original-source query bridge into a code-switch stage.
Authenticated source functions may be arbitrary. Polynomial honesty remains
an explicit additional premise where coefficient evaluation is concluded. -/
namespace NearCompression
open Lean.Grind ZkFormal.Algebra
variable {K : Type} [Field K]

def switchPairSum : List (K × K) → K × K
  | [] => (0,0)
  | a::rest => let b:=switchPairSum rest; (a.1+b.1,a.2+b.2)

def switchFoldSum (x r : K) : List (K × K) → K
  | [] => 0
  | a::rest => derivedFoldValue x r a+switchFoldSum x r rest

theorem switch_fold_pair_add (x r : K) (a b : K × K) :
    derivedFoldValue x r (a.1+b.1,a.2+b.2)=derivedFoldValue x r a+derivedFoldValue x r b := by
  simp only [derivedFoldValue,rsPairDecode]
  grind

/-- Combining authenticated branch pairs before folding is exactly the sum
of their folded contributions; no independent scalar source root is needed. -/
theorem switch_fold_pair_sum (x r : K) (pairs : List (K × K)) :
    derivedFoldValue x r (switchPairSum pairs)=switchFoldSum x r pairs := by
  induction pairs with
  | nil => simp only [switchPairSum,switchFoldSum,derivedFoldValue,rsPairDecode]; grind
  | cons a rest ih =>
    simp only [switchPairSum,switchFoldSum]
    rw [switch_fold_pair_add,ih]

/-- The literal short-source selector/duplication rule feeds the same affine
fold as the fixed lifted source oracle, even for non-polynomial source data. -/
theorem heterogeneous_switch_query (omega r : K) (k d D s : Nat) (positive : 0<d)
    (degree : D=2^k*d) (halfOrder : (omega^(2^k))^(2*d)= -1)
    (coefficients : List K) (sources : List (K → K)) (leaf : List (K×K))
    (authenticated : leaf=sourceWideLeaf sources ((omega^(2^k))^(s%(2*d)))) :
    derivedFoldValue (omega^(s%(2*D))) r (projectedBetaPair k d s coefficients leaf)=
      derivedFoldValue (omega^(s%(2*D))) r
        (weightedVirtualOracle coefficients (liftedSourceFunctions k sources) (omega^(s%(2*D))),
         weightedVirtualOracle coefficients (liftedSourceFunctions k sources) (-(omega^(s%(2*D))))) := by
  rw [heterogeneous_beta_pair_exact omega k d D s positive degree halfOrder coefficients sources leaf authenticated]

/-- Once an independently established polynomial representation identifies
the combined pair, the query is the actual folded coefficient evaluation.
The representation premise is not inferred merely from Merkle binding. -/
theorem weighted_switch_polynomial_query (cs : List K) (pairs : List (K × K)) (x r : K)
    (even : cs.length%2=0) (h2 : (2:K)≠0) (hx : x≠0)
    (represented : switchPairSum pairs=((Poly.mk cs).eval x,(Poly.mk cs).eval (-x))) :
    switchFoldSum x r pairs=(Poly.mk (affineFoldValues r cs)).eval (x*x) := by
  rw [←switch_fold_pair_sum,represented]
  exact grouped_affine_pair_eval cs r x even h2 hx
end NearCompression
