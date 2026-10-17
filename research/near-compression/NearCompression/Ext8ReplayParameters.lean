import NearCompression.PowerTwoRootOrder
import ZkFormal.Algebra.Fp8
namespace NearCompression
open Lean.Grind ZkFormal.Algebra
/-- Base twiddles stay in BabyBear while coefficients/challenges use certified Fp8. -/
theorem ext8_base_pow (a : Fp) (n : Nat) : Fp8.ofBase (a^n)=(Fp8.ofBase a)^n := by
  induction n with
  | zero=>rfl
  | succ n ih=>rw [Semiring.pow_succ,Fp8.ofBase_mul,ih,Semiring.pow_succ]
theorem ext8_native_root_order (k : Nat) (supported : k≤27) (j : Nat) :
    (Fp8.ofBase (nativeBabyBearRoot k))^j=1 ↔ 2^k∣j := by
  rw [←ext8_base_pow]
  constructor
  · intro h
    exact (native_babybear_root_order k supported j).mp (Fp8.ofBase_inj h)
  · intro h
    rw [(native_babybear_root_order k supported j).mpr h]
    rfl
/-- Exact numerator budget for the largest currently supported replay D=262144.
This is a field-count bound, not a Fiat--Shamir or full-protocol security claim. -/
theorem ext8_replay_extraction_227 : 1048572*2^227≤Fp8.all.length := by
  rw [Fp8.length_all]
  decide +kernel
theorem ext8_replay_extraction_not_228 : ¬1048572*2^228≤Fp8.all.length := by
  rw [Fp8.length_all]
  decide +kernel
/-- Exact combined replay arithmetic, allocating 130 bits to this one error term.
Other protocol errors and quantum reductions are excluded. -/
theorem ext8_replay_314_budget :
    2^130*(1048572*4^314+Fp8.all.length*3^314)≤Fp8.all.length*4^314 := by
  rw [Fp8.length_all]
  decide +kernel
end NearCompression
