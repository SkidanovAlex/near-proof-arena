import NearCompression.AirSelectorProducts
import ZkFormal.Algebra.Fp8

namespace NearCompression
open Lean.Grind ZkFormal.Air ZkFormal.Algebra

def airExt8Trace (tr : Trace Fp) : Trace Fp8 where
  log:=tr.log
  cell:=fun t r c=>Fp8.ofBase (tr.cell t r c)

/-- Base-to-extension evaluation preserves the actual AIR semantics,
including arbitrary field-valued public inputs and cyclic row selection. -/
theorem air_expression_ext8_lift (tr : Trace Fp) (t r : Nat) (pub : List Fp) (e : Expr) :
    e.eval (airExt8Trace tr) t r (pub.map Fp8.ofBase)=Fp8.ofBase (e.eval tr t r pub) := by
  induction e with
  | const n => rfl
  | col c next => rfl
  | pub i =>
    change (pub.map Fp8.ofBase).getD i 0=Fp8.ofBase (pub.getD i 0)
    induction pub generalizing i with
    | nil => rfl
    | cons x xs ih => cases i <;> simp_all
  | isFirst => change (if r=0 then (1:Fp8) else 0)=Fp8.ofBase (if r=0 then 1 else 0);split <;> rfl
  | isLast =>
    change (if r+1=tr.height t then (1:Fp8) else 0)=Fp8.ofBase (if r+1=tr.height t then 1 else 0)
    split <;> rfl
  | isTransition =>
    change (if r+1=tr.height t then (0:Fp8) else 1)=Fp8.ofBase (if r+1=tr.height t then 0 else 1)
    split <;> rfl
  | add a b ha hb => simp only [Expr.eval] at ha hb; change _+_=Fp8.ofBase (_+_);rw [Fp8.ofBase_add,ha,hb]
  | mul a b ha hb => simp only [Expr.eval] at ha hb; change _*_=Fp8.ofBase (_*_);rw [Fp8.ofBase_mul,ha,hb]
  | neg a ha => simp only [Expr.eval] at ha; change -_=Fp8.ofBase (-_);rw [Fp8.ofBase_neg,ha]

/-- The product-selector Ext8 evaluator agrees on Boolean rows with the
original BabyBear Expr.eval, not merely with an unrelated extension trace. -/
theorem air_ext8_product_expression_boolean (tr : Trace Fp) (t : Nat) (pub : List Fp)
    (point : List Fp8) (length : point.length=tr.log t)
    (boolean : ∀ x∈point,x=0 ∨ x=1) (e : Expr) :
    e.evalWith (airProductSelectorEnv (airExt8Trace tr) t (pub.map Fp8.ofBase) point)=
      Fp8.ofBase (e.eval tr t (airBooleanIndex point) pub) := by
  rw [air_product_selector_expression_boolean (airExt8Trace tr) t (pub.map Fp8.ofBase) point length boolean e]
  exact air_expression_ext8_lift tr t (airBooleanIndex point) pub e

end NearCompression
