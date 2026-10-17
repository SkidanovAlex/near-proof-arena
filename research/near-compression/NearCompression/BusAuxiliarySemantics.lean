import NearCompression.GenericBusAccumulator
import ZkFormal.Algebra.Transport
namespace NearCompression
open Lean.Grind ZkFormal.Algebra
variable {K : Type} [Field K]

/-- Value of an arbitrary (not necessarily Boolean) multiplicity bit. -/
def busBitSelect (bit power : K) : K := 1+bit*(power-1)

def busBitFactor (power : K) : List K → K
  | [] => 1
  | bit::rest => busBitSelect bit power*busBitFactor (power*power) rest

def busChainFold (power accumulator : K) : List K → K
  | [] => accumulator
  | bit::rest => busChainFold (power*power) (accumulator*busBitSelect bit (power*power)) rest

/-- Exact ordered square/product residual equations. Equal list shapes are
encoded in constructors, so no zip truncation is silently admitted. -/
inductive BusAuxChainHolds : K → K → List K → List K → List K → Prop where
  | empty (power accumulator) : BusAuxChainHolds power accumulator [] [] []
  | step {power accumulator bit rest nextPower nextProduct powers products} :
      nextPower-power*power=0 →
      nextProduct-accumulator*busBitSelect bit nextPower=0 →
      BusAuxChainHolds nextPower nextProduct rest powers products →
      BusAuxChainHolds power accumulator (bit::rest) (nextPower::powers) (nextProduct::products)

theorem bus_chain_fold_factor (power accumulator : K) (bits : List K) :
    busChainFold power accumulator bits=accumulator*busBitFactor (power*power) bits := by
  induction bits generalizing power accumulator with
  | nil => simp only [busChainFold,busBitFactor]; grind
  | cons bit rest ih => simp only [busChainFold,busBitFactor,ih]; grind

theorem bus_aux_chain_final (power accumulator : K) (bits powers products : List K)
    (holds : BusAuxChainHolds power accumulator bits powers products) :
    products.getLastD accumulator=busChainFold power accumulator bits := by
  induction holds with
  | empty => rfl
  | @step power accumulator bit rest nextPower nextProduct powers products square product tail ih =>
    have hp : nextPower=power*power := by grind
    have hv : nextProduct=accumulator*busBitSelect bit nextPower := by grind
    simp only [List.getLastD_cons]
    rw [ih,hv,hp]
    rfl

/-- For k>=1 bits, the actual final pi column (or first factor when k=1)
computes the same multiplicity factor, including p0=0. -/
theorem bus_aux_factor (power first : K) (bits powers products : List K)
    (holds : BusAuxChainHolds power (busBitSelect first power) bits powers products) :
    products.getLastD (busBitSelect first power)=busBitFactor power (first::bits) := by
  rw [bus_aux_chain_final power (busBitSelect first power) bits powers products holds,bus_chain_fold_factor]
  rfl

def busBooleanMultiplicity : List Bool → Nat
  | [] => 0
  | bit::rest => (if bit then 1 else 0)+2*busBooleanMultiplicity rest

def busBooleanValue (bit : Bool) : K := if bit then 1 else 0

theorem bus_boolean_factor (power : K) (bits : List Bool) :
    busBitFactor power (bits.map (busBooleanValue (K:=K)))=power^(busBooleanMultiplicity bits) := by
  induction bits generalizing power with
  | nil => simp [busBitFactor,busBooleanMultiplicity,Semiring.pow_zero]
  | cons bit rest ih =>
    simp only [List.map_cons,busBitFactor,ih,busBooleanMultiplicity]
    have powers : (power*power)^busBooleanMultiplicity rest=power^(2*busBooleanMultiplicity rest) := by
      rw [←Semiring.pow_two,←pow_mul_eq]
    rw [powers]
    cases bit <;> simp only [busBooleanValue,busBitSelect,Bool.false_eq_true,ite_false,ite_true,Nat.zero_add]
    · grind
    · rw [Semiring.pow_add]
      simp only [Semiring.pow_one]
      grind
/-- The separately emitted source bit constraint forces a genuine Boolean
value. No nonzero fingerprint or nonzero product hypothesis is needed. -/
theorem bus_bit_constraint_boolean (bit : K) (constraint : bit*(bit-1)=0) :
    ∃ b : Bool,bit=busBooleanValue b := by
  rcases Field.of_mul_eq_zero constraint with h | h
  · exact ⟨false,h⟩
  · refine ⟨true,?_⟩
    change bit=1
    grind

theorem bus_aux_boolean_factor (power : K) (first : Bool) (bits : List Bool)
    (powers products : List K)
    (holds : BusAuxChainHolds power (busBitSelect (busBooleanValue first) power)
      (bits.map (busBooleanValue (K:=K))) powers products) :
    products.getLastD (busBitSelect (busBooleanValue first) power)=
      power^busBooleanMultiplicity (first::bits) := by
  rw [bus_aux_factor power (busBooleanValue first) _ powers products holds]
  exact bus_boolean_factor power (first::bits)
end NearCompression
