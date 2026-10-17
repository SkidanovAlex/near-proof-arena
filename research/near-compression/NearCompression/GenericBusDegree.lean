import ZkFormal.Algebra.PolyLemmas

/-! Concrete degree bounds for bus auxiliary polynomials. Throughout, a
non-strict degree bound `d` is represented by `Poly.DegLt (d+1)`. These results
concern the displayed polynomials, not an entire AIR lowering or protocol. -/
namespace NearCompression
open Lean.Grind ZkFormal.Algebra

section Ring
variable {K : Type} [CommRing K]

/-- Select the interaction factor p when b=1, and the neutral factor when b=0. -/
def genericBusSelectedFactor (b p : Poly K) : Poly K := Poly.C 1+b*(p-Poly.C 1)

def genericBusFirstResidual (pi b0 p0 b1 p1 : Poly K) : Poly K :=
  pi-genericBusSelectedFactor b0 p0*genericBusSelectedFactor b1 p1

def genericBusAccumulatorGate (gate current next factor : Poly K) : Poly K :=
  gate*(next-current*factor)

theorem generic_bus_selected_factor_eval (b p : Poly K) (x : K) :
    (genericBusSelectedFactor b p).eval x=1+b.eval x*(p.eval x-1) := by
  simp only [genericBusSelectedFactor,Poly.eval_add,Poly.eval_mul,Poly.eval_sub,Poly.eval_C]

theorem generic_bus_first_residual_eval (pi b0 p0 b1 p1 : Poly K) (x : K) :
    (genericBusFirstResidual pi b0 p0 b1 p1).eval x=
      pi.eval x-(1+b0.eval x*(p0.eval x-1))*(1+b1.eval x*(p1.eval x-1)) := by
  simp only [genericBusFirstResidual,Poly.eval_sub,Poly.eval_mul,generic_bus_selected_factor_eval]

theorem generic_bus_accumulator_gate_eval (gate current next factor : Poly K) (x : K) :
    (genericBusAccumulatorGate gate current next factor).eval x=
      gate.eval x*(next.eval x-current.eval x*factor.eval x) := by
  simp only [genericBusAccumulatorGate,Poly.eval_mul,Poly.eval_sub]

/-- Selection adds the degree bounds of the bit and its factor. -/
theorem generic_bus_selected_factor_degree (b p : Poly K) (db dp : Nat)
    (hb : b.DegLt (db+1)) (hp : p.DegLt (dp+1)) :
    (genericBusSelectedFactor b p).DegLt (db+dp+1) := by
  have one : (Poly.C (1 : K)).DegLt 1 := Poly.degLt_length _
  have difference := Poly.degLt_sub hp (one.mono (by omega : 1≤dp+1))
  exact Poly.degLt_add (one.mono (by omega)) (Poly.degLt_mul hb difference)

/-- With affine pi and p1, the first two-factor residual has degree at most
`db0+dp0+db1+1`, including the case of constant source expressions. -/
theorem generic_bus_first_residual_degree (pi b0 p0 b1 p1 : Poly K) (db0 dp0 db1 : Nat)
    (hpi : pi.DegLt 2) (hb0 : b0.DegLt (db0+1)) (hp0 : p0.DegLt (dp0+1))
    (hb1 : b1.DegLt (db1+1)) (hp1 : p1.DegLt 2) :
    (genericBusFirstResidual pi b0 p0 b1 p1).DegLt (db0+dp0+db1+2) := by
  have first := generic_bus_selected_factor_degree b0 p0 db0 dp0 hb0 hp0
  have second := generic_bus_selected_factor_degree b1 p1 db1 1 hb1 hp1
  have product := Poly.degLt_mul first second
  have product' : (genericBusSelectedFactor b0 p0*genericBusSelectedFactor b1 p1).DegLt
      (db0+dp0+db1+2) := by
    simpa only [Nat.add_assoc] using product
  exact Poly.degLt_sub (hpi.mono (by omega)) product'

/-- Multiplying the accumulator recurrence by an affine selector adds two to
the interaction-factor degree bound. -/
theorem generic_bus_accumulator_gate_degree (gate current next factor : Poly K) (d : Nat)
    (hgate : gate.DegLt 2) (hcurrent : current.DegLt 2) (hnext : next.DegLt 2)
    (hfactor : factor.DegLt (d+1)) :
    (genericBusAccumulatorGate gate current next factor).DegLt (d+3) := by
  have product := Poly.degLt_mul hcurrent hfactor
  have recurrence := Poly.degLt_sub (hnext.mono (by omega : 2≤1+d+1)) product
  have result := Poly.degLt_mul hgate recurrence
  exact result.mono (by omega)

end Ring
end NearCompression
