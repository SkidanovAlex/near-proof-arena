import NearCompression.BusBoundFinalProducts
import NearCompression.AirAuxCoordinateTrace

namespace NearCompression
open Lean.Grind ZkFormal.Air ZkFormal.Algebra

private theorem ofBase_one (x : Fp) : Fp8.ofBase x=1 ↔ x=1 :=
  ⟨fun h=>Fp8.ofBase_inj h,fun h=>congrArg Fp8.ofBase h⟩

/-- Multiplicity is preserved as a natural number, even for nonboolean source
values. Reconstructed auxiliary columns cannot affect bounded source bits. -/
theorem bus_ext8_coordinate_mult (raw : Trace Fp) (sourceWidth : Nat→Nat)
    (t r : Nat) (pubValues : List Fp) (i : Interaction)
    (bounds : ∀ e∈i.mult,e.colBound≤sourceWidth t) :
    i.multNat (airAuxCoordinateTrace raw sourceWidth) t r (pubValues.map Fp8.ofBase)=
      i.multNat raw t r pubValues := by
  have go (bits : List Expr) (k : Nat) (bound : ∀ e∈bits,e.colBound≤sourceWidth t) :
      Interaction.multNat.go (airAuxCoordinateTrace raw sourceWidth) t r (pubValues.map Fp8.ofBase) bits k=
        Interaction.multNat.go raw t r pubValues bits k := by
    induction bits generalizing k with
    | nil => rfl
    | cons bit rest ih =>
      simp only [Interaction.multNat.go,
        air_aux_coordinate_source_eval raw sourceWidth t r pubValues bit (bound bit (List.mem_cons_self ..)),ofBase_one]
      rw [ih (k+1) (fun e he=>bound e (List.mem_cons_of_mem _ he))]
  exact go i.mult 0 bounds

theorem bus_ext8_coordinate_message (raw : Trace Fp) (sourceWidth : Nat→Nat)
    (t r : Nat) (pubValues : List Fp) (i : Interaction)
    (bounds : ∀ e∈i.msg,e.colBound≤sourceWidth t) :
    i.msgVal (airAuxCoordinateTrace raw sourceWidth) t r (pubValues.map Fp8.ofBase)=
      (i.msgVal raw t r pubValues).map Fp8.ofBase := by
  simp only [Interaction.msgVal,List.map_map,Function.comp_def]
  apply List.map_congr_left
  intro e he
  exact air_aux_coordinate_source_eval raw sourceWidth t r pubValues e (bounds e he)

/-- A semantic interaction final over the reconstructed extension trace is
exactly the embedded-base message product used by the Ext8 bus bound. -/
theorem bus_ext8_coordinate_final (raw : Trace Fp) (sourceWidth : Nat→Nat)
    (t : Nat) (pubValues : List Fp) (alpha gamma : Fp8) (i : Interaction)
    (bounds : ∀ e∈i.exprs,e.colBound≤sourceWidth t) :
    busInteractionFinalPower (airAuxCoordinateTrace raw sourceWidth) (pubValues.map Fp8.ofBase)
      t id (fun b=>((b+1:Nat):Fp8)) alpha gamma i=
    busInteractionFinalPower raw pubValues t Fp8.ofBase (fun b=>((b+1:Nat):Fp8)) alpha gamma i := by
  unfold busInteractionFinalPower
  change ((List.range (raw.height t)).map _).prod=_
  congr 1
  apply List.map_congr_left
  intro r _
  simp only [busInteractionRowPower,busMessageFactor,busEncodeMessage,List.map_id]
  rw [bus_ext8_coordinate_mult raw sourceWidth t r pubValues i
      (fun e he=>bounds e (List.mem_append_left _ he)),
    bus_ext8_coordinate_message raw sourceWidth t r pubValues i
      (fun e he=>bounds e (List.mem_append_right _ he))]

/-- Concrete base-to-Ext8 composition: source constraints are checked over
BabyBear, auxiliaries over the reconstructed coordinate trace, and claimed
final products are expressed over the original BabyBear message traffic. -/
theorem bus_ext8_bound_side_product (table : Table) (raw : Trace Fp) (sourceWidth : Nat→Nat)
    (t : Nat) (pubValues : List Fp) (alpha gamma : Fp8) (finals : Nat→Fp8) (side : Bool)
    (constraintBounds : ∀ e∈table.allConstraints,e.colBound≤sourceWidth t)
    (interactionBounds : ∀ i∈table.interactions,∀ e∈i.exprs,e.colBound≤sourceWidth t)
    (localZero : ∀ r, r<raw.height t → ∀ e∈table.allConstraints,e.eval raw t r pubValues=0)
    (auxZero : ∀ r, r<raw.height t → ∀ e∈busTableResiduals
      (table.interactions.map (lowerBusInteraction (pubValues.map Fp8.ofBase) alpha gamma)) table.width finals,
      busProgramFormulaValue (busRowProgramEnv (airAuxCoordinateTrace raw sourceWidth) t r) e=0) :
    busBoundSideProduct (table.interactions.map (lowerBusInteraction (pubValues.map Fp8.ofBase) alpha gamma)) table.width finals side=
      (table.interactions.map (fun i=>if i.send=side then
        busInteractionFinalPower raw pubValues t Fp8.ofBase (fun b=>((b+1:Nat):Fp8)) alpha gamma i else 1)).prod := by
  have sourceZero : ∀ r, r<(airAuxCoordinateTrace raw sourceWidth).height t →
      ∀ e∈table.allConstraints,e.eval (airAuxCoordinateTrace raw sourceWidth) t r (pubValues.map Fp8.ofBase)=0 := by
    intro r hr e he
    rw [air_aux_coordinate_source_eval raw sourceWidth t r pubValues e (constraintBounds e he),localZero r hr e he]
    rfl
  rw [bus_bound_side_natural_product table (airAuxCoordinateTrace raw sourceWidth) t
    (pubValues.map Fp8.ofBase) alpha gamma finals side sourceZero auxZero]
  congr 1
  apply List.map_congr_left
  intro i hi
  rw [bus_ext8_coordinate_final raw sourceWidth t pubValues alpha gamma i (interactionBounds i hi)]

/-- Concrete source bounds and residual validity for every table, retaining
the original BabyBear public vector for all public-message processing. -/
def busExt8TablesResidualsZero (raw : Trace Fp) (sourceWidth : Nat→Nat)
    (pubValues : List Fp) (alpha gamma : Fp8) (finals : Nat→Nat→Fp8) : List Table → Nat → Prop
  | [],_ => True
  | table::rest,t =>
    (∀ e∈table.allConstraints,e.colBound≤sourceWidth t) ∧
    (∀ i∈table.interactions,∀ e∈i.exprs,e.colBound≤sourceWidth t) ∧
    (∀ r, r<raw.height t → ∀ e∈table.allConstraints,e.eval raw t r pubValues=0) ∧
    (∀ r, r<raw.height t → ∀ e∈busTableResiduals
      (table.interactions.map (lowerBusInteraction (pubValues.map Fp8.ofBase) alpha gamma)) table.width (finals t),
      busProgramFormulaValue (busRowProgramEnv (airAuxCoordinateTrace raw sourceWidth) t r) e=0) ∧
    busExt8TablesResidualsZero raw sourceWidth pubValues alpha gamma finals rest (t+1)

theorem bus_ext8_bound_tables_product (tables : List Table) (raw : Trace Fp) (sourceWidth : Nat→Nat)
    (t : Nat) (pubValues : List Fp) (alpha gamma : Fp8) (finals : Nat→Nat→Fp8) (side : Bool)
    (holds : busExt8TablesResidualsZero raw sourceWidth pubValues alpha gamma finals tables t) :
    busBoundTablesProduct (airAuxCoordinateTrace raw sourceWidth) (pubValues.map Fp8.ofBase)
      alpha gamma finals side tables t=
    busTablesFinalPower raw pubValues side Fp8.ofBase (fun b=>((b+1:Nat):Fp8)) alpha gamma tables t := by
  induction tables generalizing t with
  | nil => rfl
  | cons table rest ih =>
    simp only [busBoundTablesProduct,busTablesFinalPower]
    rw [bus_ext8_bound_side_product table raw sourceWidth t pubValues alpha gamma (finals t) side
      holds.1 holds.2.1 holds.2.2.1 holds.2.2.2.1,ih (t+1) holds.2.2.2.2]

/-- Concrete Ext8 claimed side product: public records are formed from the
original BabyBear vector, exactly as in the challenge-budget theorem. -/
def busExt8ClaimedSideProduct (air : ZkFormal.V2.AirP) (raw : Trace Fp) (sourceWidth : Nat→Nat)
    (pubValues : List Fp) (alpha gamma : Fp8) (finals : Nat→Nat→Fp8) (side : Bool) : Fp8 :=
  busBoundTablesProduct (airAuxCoordinateTrace raw sourceWidth) (pubValues.map Fp8.ofBase)
      alpha gamma finals side air.tables 0 *
    ((busTracePublic air pubValues side).map
      (busMessageFactor Fp8.ofBase (fun b=>((b+1:Nat):Fp8)) alpha gamma)).prod

theorem bus_ext8_claimed_global_product (air : ZkFormal.V2.AirP) (raw : Trace Fp) (sourceWidth : Nat→Nat)
    (pubValues : List Fp) (alpha gamma : Fp8) (finals : Nat→Nat→Fp8) (side : Bool)
    (holds : busExt8TablesResidualsZero raw sourceWidth pubValues alpha gamma finals air.tables 0) :
    busExt8ClaimedSideProduct air raw sourceWidth pubValues alpha gamma finals side=
      busGlobalSideProduct air raw pubValues side Fp8.ofBase (fun b=>((b+1:Nat):Fp8)) alpha gamma := by
  unfold busExt8ClaimedSideProduct busGlobalSideProduct
  rw [bus_ext8_bound_tables_product _ _ _ _ _ _ _ _ _ holds]

end NearCompression
