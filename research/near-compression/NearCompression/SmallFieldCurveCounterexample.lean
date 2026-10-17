/-! Exhaustive modular-arithmetic certificate over F5 for degree<2 candidates.
This is a finite regression against zero-exception transfer, not a general
field/concentration theorem. Coefficients are canonical residues 0,...,4. -/
namespace NearCompression

def curveF5Polynomials : List (Nat × Nat) :=
  (List.range 5).flatMap (fun a => (List.range 5).map (fun b => (a,b)))

def curveF5Eval (p : Nat × Nat) (x : Nat) : Nat := (p.1+p.2*x)%5

def curveF5Even (x : Nat) : Nat := if x=3 then 1 else 0

def curveF5Odd (x : Nat) : Nat := if x=2 then 1 else if x=3 then 2 else 0

def curveF5Fold (r x : Nat) : Nat :=
  (((6-r)%5)*curveF5Even x+r*curveF5Odd x)%5

def curveF5Success (r : Nat) : Bool := curveF5Polynomials.any (fun p =>
  3≤((List.range 4).filter (fun x => curveF5Eval p x==curveF5Fold r x)).length)

def curveF5Joint : Bool := curveF5Polynomials.any (fun p =>
  curveF5Polynomials.any (fun q =>
    3≤((List.range 4).filter (fun x =>
      curveF5Eval p x==curveF5Even x && curveF5Eval q x==curveF5Odd x)).length))

/-- Positive Johnson gap T²-N(D-1)=5, but four of five challenges have a
proximate folded polynomial while no jointly agreeing parent pair exists. -/
theorem curve_f5_zero_exception_transfer_counterexample :
    4*(2-1)<3*3 ∧
    ((List.range 5).filter curveF5Success)=[0,1,2,4] ∧ curveF5Joint=false := by
  decide

end NearCompression
