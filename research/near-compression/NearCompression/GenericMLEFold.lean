import NearCompression.GenericRowMLE

/-! Prover-side low-bit folding. Each fold halves the relevant evaluation
table and preserves the remaining multilinear evaluation exactly. -/
namespace NearCompression
open Lean.Grind

section Ring
variable {K : Type} [CommRing K]

/-- Consume the lowest row bit using adjacent even/odd evaluations. -/
def genericMLEFoldOne (values : Nat → K) (r : K) (i : Nat) : K :=
  (1-r)*values (2*i)+r*values (2*i+1)

/-- Prepend a challenge to an infinite point; only the requested finite prefix
is read by genericRowMLE. -/
def genericMLEPointCons (r : K) (point : Nat → K) : Nat → K
  | 0 => r
  | i+1 => point i

theorem generic_mle_fold_one (n : Nat) (values : Nat → K) (r : K) (point : Nat → K) :
    genericRowMLE n (genericMLEFoldOne values r) point=
      genericRowMLE (n+1) values (genericMLEPointCons r point) := by
  change genericRowMLE n (fun i => (1-r)*values (2*i)+r*values (2*i+1)) point=_
  rw [generic_row_mle_add,generic_row_mle_scale,generic_row_mle_scale]
  rfl

/-- Challenges are consumed in list order, lowest row bit first. -/
def genericMLEFoldPrefix : List K → (Nat → K) → Nat → K
  | [],values => values
  | r::rs,values => genericMLEFoldPrefix rs (genericMLEFoldOne values r)

def genericMLEPointPrefix : List K → (Nat → K) → Nat → K
  | [],point => point
  | r::rs,point => genericMLEPointCons r (genericMLEPointPrefix rs point)

/-- Any prefix may be folded once and reused for all subsequent evaluations. -/
theorem generic_mle_fold_prefix (prefixValues : List K) (n : Nat)
    (values point : Nat → K) :
    genericRowMLE n (genericMLEFoldPrefix prefixValues values) point=
      genericRowMLE (n+prefixValues.length) values (genericMLEPointPrefix prefixValues point) := by
  induction prefixValues generalizing values with
  | nil => rfl
  | cons r rs ih =>
    simp only [genericMLEFoldPrefix,genericMLEPointPrefix,List.length_cons]
    rw [ih,generic_mle_fold_one]
    rfl

/-- Folding every row bit leaves exactly the original MLE value at index zero. -/
theorem generic_mle_fold_complete (challenges : List K) (values : Nat → K) :
    genericMLEFoldPrefix challenges values 0=
      genericRowMLE challenges.length values (genericMLEPointPrefix challenges (fun _ => 0)) := by
  simpa only [genericRowMLE,Nat.zero_add] using generic_mle_fold_prefix challenges 0 values (fun _ => 0)

/-- The multiply-add form used by the executable prover is the same fold. -/
theorem generic_mle_fold_affine (values : Nat → K) (r : K) (i : Nat) :
    genericMLEFoldOne values r i = values (2*i)+r*(values (2*i+1)-values (2*i)) := by
  unfold genericMLEFoldOne
  grind

end Ring
end NearCompression
