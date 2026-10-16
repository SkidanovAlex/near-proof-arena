import NearCompression.BusSourceFormulaLowering
import NearCompression.BusTraceMultiset

namespace NearCompression
open Lean.Grind ZkFormal.Air ZkFormal.Udr ZkFormal.Algebra
variable {K : Type} [Field K] [DecidableEq K]

def busValueMultiplicity : List K → Nat
  | [] => 0
  | bit::rest => (if bit=1 then 1 else 0)+2*busValueMultiplicity rest

/-- Boolean source values turn the auxiliary arithmetic factor into a power
with a natural exponent. No reduction of the exponent modulo the field. -/
theorem bus_value_factor (power : K) (bits : List K)
    (boolean : ∀ b∈bits,b=0 ∨ b=1) :
    busBitFactor power bits=power^(busValueMultiplicity bits) := by
  induction bits generalizing power with
  | nil => simp [busBitFactor,busValueMultiplicity,Semiring.pow_zero]
  | cons bit rest ih =>
    have tail := ih (power*power) (fun b hb=>boolean b (List.mem_cons_of_mem _ hb))
    have powers : (power*power)^busValueMultiplicity rest=power^(2*busValueMultiplicity rest) := by
      rw [←Semiring.pow_two,←pow_mul_eq]
    simp only [busBitFactor,tail,powers,busValueMultiplicity]
    rcases boolean bit (List.mem_cons_self ..) with h | h
    · subst bit
      simp only [show (0:K)≠1 from by grind,ite_false,Nat.zero_add,busBitSelect]
      grind
    · subst bit
      simp only [ite_true,busBitSelect,Semiring.pow_add,Semiring.pow_one]
      grind

/-- Equality to the source definition's weighted natural sum, for arbitrary
values (Booleanity is only needed for the field-factor identity). -/
theorem bus_value_multiplicity_source (tr : Trace K) (t r : Nat) (pubValues : List K)
    (bits : List Expr) (k : Nat) :
    Interaction.multNat.go tr t r pubValues bits k=
      2^k*busValueMultiplicity (bits.map (fun e=>e.eval tr t r pubValues)) := by
  induction bits generalizing k with
  | nil => simp [Interaction.multNat.go,busValueMultiplicity]
  | cons bit rest ih =>
    simp only [Interaction.multNat.go,List.map_cons,busValueMultiplicity,ih,Nat.pow_succ]
    split <;> simp_all [Nat.mul_add,Nat.mul_assoc]

/-- The actual source bit constraints suffice; no pre-decoded Boolean witness
or separate multiplicity certificate is assumed. -/
theorem bus_source_natural_factor (tr : Trace K) (t r : Nat) (pubValues : List K)
    (i : Interaction) (power : K)
    (bits : ∀ b∈i.mult,(b.eval tr t r pubValues)*(b.eval tr t r pubValues-1)=0) :
    busBitFactor power (i.mult.map (fun e=>e.eval tr t r pubValues))=
      power^(i.multNat tr t r pubValues) := by
  have boolean : ∀ v∈i.mult.map (fun e=>e.eval tr t r pubValues),v=0 ∨ v=1 := by
    intro v hv
    obtain ⟨b,hb,rfl⟩:=List.mem_map.mp hv
    rcases Field.of_mul_eq_zero (bits b hb) with h | h
    · exact Or.inl h
    · exact Or.inr (by grind)
  rw [bus_value_factor power _ boolean]
  have natural := bus_value_multiplicity_source tr t r pubValues i.mult 0
  simpa [Interaction.multNat] using congrArg (fun n=>power^n) natural.symm

private theorem replicate_product (value : K) (n : Nat) :
    (List.replicate n value).prod=value^n := by
  induction n with
  | zero => simp [Semiring.pow_zero]
  | succ n ih => simp only [List.replicate_succ,List.prod_cons,ih,Semiring.pow_succ]; grind

/-- Extracts the multiplicity equation from the actual allConstraints list. -/
theorem bus_table_source_bits (table : Table) (tr : Trace K) (t r : Nat) (pubValues : List K)
    (localZero : ∀ e∈table.allConstraints,e.eval tr t r pubValues=0)
    (i : Interaction) (hi : i∈table.interactions) (b : Expr) (hb : b∈i.mult) :
    b.eval tr t r pubValues*(b.eval tr t r pubValues-1)=0 := by
  have h := localZero (.mul b (.add b (.neg (.const 1))))
    (List.mem_append_right _ (List.mem_flatMap.mpr ⟨i,hi,List.mem_map.mpr ⟨b,hb,rfl⟩⟩))
  simp only [Expr.eval,Expr.evalWith,rowEnv] at h ⊢
  grind

/-- Generated source interaction factors are products over the exact natural
number of copies used by busTraceRow, including zero multiplicity/fingerprint. -/
theorem bus_source_factor_expanded (tr : Trace K) (t r : Nat) (pubValues : List K)
    (alpha gamma : K) (i : Interaction) (offset : Nat)
    (bits : ∀ b∈i.mult,(b.eval tr t r pubValues)*(b.eval tr t r pubValues-1)=0)
    (zero : ∀ e∈(buildBusInteraction (lowerBusInteraction pubValues alpha gamma i).power
      (lowerBusInteraction pubValues alpha gamma i).bits offset).chain,
      busProgramFormulaValue (busRowProgramEnv tr t r) e=0) :
    busProgramFormulaValue (busRowProgramEnv tr t r)
      (buildBusInteraction (lowerBusInteraction pubValues alpha gamma i).power
        (lowerBusInteraction pubValues alpha gamma i).bits offset).factor=
      ((List.replicate (i.multNat tr t r pubValues) (i.msgVal tr t r pubValues++
        [(@Nat.cast K Semiring.natCast (i.bus+1))])).map (fun m=>gamma-fp alpha m)).prod := by
  rw [bus_source_interaction_factor _ _ _ _ _ _ _ _ zero,bus_source_natural_factor _ _ _ _ _ _ bits]
  simp [List.map_replicate,replicate_product]

/-- Actual source rows and generated auxiliary residuals imply the final
product with natural multiplicities. Row selector and cyclic-next bindings
are discharged from rowEnv, rather than supplied as extra certificates. -/
theorem bus_source_table_natural_product (table : Table) (tr : Trace K) (t : Nat)
    (pubValues : List K) (alpha gamma : K) (finals : Nat→K)
    (localZero : ∀ r, r<tr.height t → ∀ e∈table.allConstraints,e.eval tr t r pubValues=0)
    (auxZero : ∀ r, r<tr.height t → ∀ e∈busTableResiduals
      (table.interactions.map (lowerBusInteraction pubValues alpha gamma)) table.width finals,
      busProgramFormulaValue (busRowProgramEnv tr t r) e=0)
    (b : BusBoundInteraction K)
    (hb : b∈busTableBindings (table.interactions.map (lowerBusInteraction pubValues alpha gamma)) table.width finals) :
    ∃ i∈table.interactions, b.allocated.interaction=lowerBusInteraction pubValues alpha gamma i ∧
      b.final=((List.range (tr.height t)).map (fun r=>
        (gamma-fp alpha (i.msgVal tr t r pubValues++[(@Nat.cast K Semiring.natCast (i.bus+1))]))^
          (i.multNat tr t r pubValues))).prod := by
  have positive : 1≤tr.height t := by unfold Trace.height; exact Nat.one_le_two_pow
  obtain ⟨i,hi,source,product⟩:=bus_source_table_product table.interactions pubValues alpha gamma
    table.width finals (tr.height t) positive (busRowProgramEnv tr t)
    (by intro r hr; rfl) (by intro r hr; rfl) (by intro r hr; rfl)
    (by intro r c hr; simp [busRowProgramEnv,rowEnv,Nat.mod_eq_of_lt hr]) auxZero b hb
  refine ⟨i,hi,source,?_⟩
  rw [product]
  congr 1
  apply List.map_congr_left
  intro r hr
  have evalSource (e : Expr) :
      e.evalWith (airProgramEnv (busRowProgramEnv tr t r) pubValues)=e.eval tr t r pubValues := by
    rw [←bus_source_formula_value,bus_source_formula_row]
  simp only [evalSource]
  exact bus_source_natural_factor tr t r pubValues i _
    (bus_table_source_bits table tr t r pubValues (localZero r (List.mem_range.mp hr)) i hi)

end NearCompression
