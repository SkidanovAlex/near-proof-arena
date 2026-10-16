import NearCompression.ProjectedRSDomain
import ZkFormal.Algebra.Fp
namespace NearCompression
open Lean.Grind ZkFormal.Algebra
variable {K : Type} [Field K]

/-- Compact primitive-root certificate. Period plus the half-order equation
imply exact order at EVERY natural exponent, not just sampled indices. -/
theorem power_two_exact_order (g : K) (k : Nat)
    (period : g^(2^k)=1) (half : 1≤k → g^(2^(k-1)) = -1)
    (characteristic : (-1:K)≠1) (j : Nat) : g^j=1 ↔ 2^k∣j := by
  constructor
  · intro one
    have equal : g^(j%(2^k))=g^0 := by
      rw [global_chain_pow_mod g (2^k) j period,one,Semiring.pow_zero]
    have remainder := pow_inj_of_half g k half characteristic
      (Nat.mod_lt j (Nat.two_pow_pos k)) (Nat.two_pow_pos k) equal
    exact Nat.dvd_of_mod_eq_zero remainder
  · intro divides
    rw [←global_chain_pow_mod g (2^k) j period,Nat.mod_eq_zero_of_dvd divides,Semiring.pow_zero]

/-- For positive k the half-order check alone already implies the period. -/
theorem power_two_order_from_half (g : K) (k : Nat) (positive : 1≤k)
    (half : g^(2^(k-1)) = -1) (characteristic : (-1:K)≠1) (j : Nat) :
    g^j=1 ↔ 2^k∣j := by
  have period : g^(2^k)=1 := by
    have exp : 2^k=2^(k-1)*2 := by
      rw [←Nat.pow_succ,show (k-1).succ=k by omega]
    rw [exp,pow_mul_eq,half]
    grind
  exact power_two_exact_order g k period (fun _ => half) characteristic j

/-- The literal generator used by rs_commit.rs and the Python verifiers is
main's certified BabyBear generator. This closed computation is kernel checked. -/
theorem native_babybear_generator : (440564289 : Fp)=Fp.twoAdicGen27 := by
  decide +kernel

/-- Literal native root formula, with the same integer division. -/
def nativeBabyBearRoot (k : Nat) : Fp := (440564289 : Fp)^((2^27)/(2^k))

theorem native_babybear_root_eq (k : Nat) (supported : k≤27) :
    nativeBabyBearRoot k=Fp.twoAdicGen k := by
  rw [nativeBabyBearRoot,native_babybear_generator,Nat.pow_div supported (by decide)]
  rfl

theorem native_babybear_root_order (k : Nat) (supported : k≤27) (j : Nat) :
    (nativeBabyBearRoot k)^j=1 ↔ 2^k∣j := by
  rw [native_babybear_root_eq k supported]
  exact power_two_exact_order _ k (Fp.twoAdicGen_pow supported)
    (fun positive => Fp.twoAdicGen_pow_half positive supported) Fp.neg_one_ne_one j

/-- Exact modular integer value computed by pow(440564289,2^27//2^k,P).
This bridges the root expression, not the entire Rust pow implementation. -/
theorem native_babybear_root_value (k : Nat) :
    (nativeBabyBearRoot k).toNat=440564289^((2^27)/(2^k))%2013265921 := by
  rw [nativeBabyBearRoot,Fp.toNat_pow]
  rfl

/-- Natural RS domain distinctness for every supported native power-of-two
size. No new numerical primitive-root assumption is supplied. -/
theorem native_babybear_domain_distinct (k : Nat) (supported : k≤27) :
    (naturalRSDomain (nativeBabyBearRoot k) (2^k)).Nodup :=
  natural_rs_distinct _ _ (native_babybear_root_order k supported)

/-- Closed numerical half-order equation for the exact native constant. -/
theorem native_babybear_half_mod :
    440564289^(2^26)%2013265921=2013265920 := by
  rw [←powMod_eq (by decide)]
  decide +kernel

/-- Closed numerical period equation for the exact native constant. -/
theorem native_babybear_period_mod :
    440564289^(2^27)%2013265921=1 := by
  rw [←powMod_eq (by decide)]
  decide +kernel

/-- The prover sets N=4*degree, with degree=2^n. This is the identical
root expression, not a different generator with the same order. -/
theorem native_babybear_rate_four_value (n : Nat) :
    (nativeBabyBearRoot (n+2)).toNat=
      440564289^((2^27)/(4*(2^n)))%2013265921 := by
  rw [native_babybear_root_value,Nat.pow_add]
  congr 3
  grind
end NearCompression
