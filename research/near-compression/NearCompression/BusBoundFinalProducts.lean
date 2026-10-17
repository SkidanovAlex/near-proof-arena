import NearCompression.BusExpandedProducts

namespace NearCompression
open Lean.Grind ZkFormal.Air ZkFormal.V2
variable {K : Type} [Field K]

private theorem perm_product {xs ys : List K} (h : xs.Perm ys) : xs.prod=ys.prod := by
  induction h with
  | nil => rfl
  | cons x h ih => simp only [List.prod_cons,ih]
  | swap x y xs => simp only [List.prod_cons]; grind
  | trans h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂

def busFormulaFinal (n : Nat) (env : Nat→TerminalProgramEnvironment K) (i : BusFormulaInteraction K) : K :=
  ((List.range n).map (fun r=>busBitFactor (busProgramFormulaValue (env r) i.power)
    (i.bits.map (busProgramFormulaValue (env r))))).prod

def busBoundSideProduct (interactions : List (BusFormulaInteraction K)) (sourceWidth : Nat)
    (finals : Nat→K) (side : Bool) : K :=
  ((busTableBindings interactions sourceWidth finals).map
    (fun b=>if b.allocated.interaction.send=side then b.final else 1)).prod

/-- Grouping and allocation preserve every interaction with multiplicity.
This fold uses actual bound finals and derives their semantic replacement. -/
theorem bus_bound_side_formula_product (interactions : List (BusFormulaInteraction K))
    (sourceWidth : Nat) (finals : Nat→K) (side : Bool) (n : Nat) (positive : 1≤n)
    (env : Nat→TerminalProgramEnvironment K)
    (hfirst : ∀ r, r<n → (env r).first=if r=0 then 1 else 0)
    (htransition : ∀ r, r<n → (env r).transition=if r+1=n then 0 else 1)
    (hlast : ∀ r, r<n → (env r).last=if r+1=n then 1 else 0)
    (hnext : ∀ r c, r+1<n → (env r).next c=(env (r+1)).current c)
    (zero : ∀ r, r<n → ∀ e∈busTableResiduals interactions sourceWidth finals,
      busProgramFormulaValue (env r) e=0) :
    busBoundSideProduct interactions sourceWidth finals side=
      (interactions.map (fun i=>if i.send=side then busFormulaFinal n env i else 1)).prod := by
  let weight := fun i : BusFormulaInteraction K=>if i.send=side then busFormulaFinal n env i else 1
  have mapped : (busTableBindings interactions sourceWidth finals).map
      (fun b=>if b.allocated.interaction.send=side then b.final else 1)=
      (busTableBindings interactions sourceWidth finals).map (fun b=>weight b.allocated.interaction) := by
    apply List.map_congr_left
    intro b hb
    have final:=bus_table_layout_product interactions sourceWidth finals n positive env
      hfirst htransition hlast hnext zero b hb
    simp only [weight,busFormulaFinal,final]
  have sourceOrder : ((busTableBindings interactions sourceWidth finals).map
      (fun b=>b.allocated.interaction)).Perm interactions := by
    have allocated := (bus_table_binding_pairs
      (busTableGroupOrder (allocateBusInteractions interactions sourceWidth))
      (sourceWidth+busTableChainColumns interactions) finals).2
    have grouped := (bus_table_group_permutation (allocateBusInteractions interactions sourceWidth)).map
      (fun a=>a.interaction)
    rw [bus_table_allocation_sources] at grouped
    have lifted := congrArg (List.map (fun a : BusAllocatedInteraction K=>a.interaction)) allocated
    simp only [List.map_map,Function.comp_def] at lifted
    exact lifted ▸ grouped
  unfold busBoundSideProduct
  rw [mapped]
  have ordered:=perm_product (sourceOrder.map weight)
  simpa only [List.map_map,Function.comp_def] using ordered

/-- The real source table and auxiliary constraints imply the directional
product of bound final values equals the natural-multiplicity source product. -/
theorem bus_bound_side_natural_product [DecidableEq K] (table : Table) (tr : Trace K) (t : Nat)
    (pubValues : List K) (alpha gamma : K) (finals : Nat→K) (side : Bool)
    (localZero : ∀ r, r<tr.height t → ∀ e∈table.allConstraints,e.eval tr t r pubValues=0)
    (auxZero : ∀ r, r<tr.height t → ∀ e∈busTableResiduals
      (table.interactions.map (lowerBusInteraction pubValues alpha gamma)) table.width finals,
      busProgramFormulaValue (busRowProgramEnv tr t r) e=0) :
    busBoundSideProduct (table.interactions.map (lowerBusInteraction pubValues alpha gamma)) table.width finals side=
      (table.interactions.map (fun i=>if i.send=side then
        busInteractionFinalPower tr pubValues t id (fun b=>(@Nat.cast K Semiring.natCast (b+1))) alpha gamma i else 1)).prod := by
  rw [bus_bound_side_formula_product _ _ _ _ (tr.height t)
    (by unfold Trace.height; exact Nat.one_le_two_pow) (busRowProgramEnv tr t)
    (by intro r hr; rfl) (by intro r hr; rfl) (by intro r hr; rfl)
    (by intro r c hr; simp [busRowProgramEnv,rowEnv,Nat.mod_eq_of_lt hr]) auxZero]
  simp only [List.map_map,Function.comp_def]
  congr 1
  apply List.map_congr_left
  intro i hi
  change (if i.send=side then _ else _) = _
  by_cases direction : i.send=side
  · simp only [direction,ite_true,busFormulaFinal,busInteractionFinalPower]
    congr 1
    apply List.map_congr_left
    intro r hr
    have values:=bus_lowered_interaction_values (busRowProgramEnv tr t r) pubValues alpha gamma i
    rw [values.1,values.2]
    have ev (e : Expr) : e.evalWith (airProgramEnv (busRowProgramEnv tr t r) pubValues)=e.eval tr t r pubValues := by
      rw [←bus_source_formula_value,bus_source_formula_row]
    simp only [ev]
    have natural:=bus_source_natural_factor tr t r pubValues i
      (gamma-ZkFormal.Udr.fp alpha (i.msgVal tr t r pubValues++[(@Nat.cast K Semiring.natCast (i.bus+1))]))
      (bus_table_source_bits table tr t r pubValues (localZero r (List.mem_range.mp hr)) i hi)
    simpa only [busInteractionRowPower,busMessageFactor,busEncodeMessage,List.map_id,Interaction.msgVal] using natural
  · simp [direction]

def busBoundTablesProduct (tr : Trace K) (pubValues : List K) (alpha gamma : K)
    (finals : Nat→Nat→K) (side : Bool) : List Table → Nat → K
  | [],_ => 1
  | table::rest,t => busBoundSideProduct
      (table.interactions.map (lowerBusInteraction pubValues alpha gamma)) table.width (finals t) side *
      busBoundTablesProduct tr pubValues alpha gamma finals side rest (t+1)

/-- All premises refer to the same trace and challenge values. This predicate
records residual validity, not cryptographic acceptance. -/
def busTablesResidualsZero (tr : Trace K) (pubValues : List K) (alpha gamma : K)
    (finals : Nat→Nat→K) : List Table → Nat → Prop
  | [],_ => True
  | table::rest,t =>
    (∀ r, r<tr.height t → ∀ e∈table.allConstraints,e.eval tr t r pubValues=0) ∧
    (∀ r, r<tr.height t → ∀ e∈busTableResiduals
      (table.interactions.map (lowerBusInteraction pubValues alpha gamma)) table.width (finals t),
      busProgramFormulaValue (busRowProgramEnv tr t r) e=0) ∧
    busTablesResidualsZero tr pubValues alpha gamma finals rest (t+1)

theorem bus_bound_tables_natural_product [DecidableEq K] (tables : List Table) (tr : Trace K)
    (pubValues : List K) (alpha gamma : K) (finals : Nat→Nat→K) (side : Bool) (t : Nat)
    (holds : busTablesResidualsZero tr pubValues alpha gamma finals tables t) :
    busBoundTablesProduct tr pubValues alpha gamma finals side tables t=
      busTablesFinalPower tr pubValues side id (fun b=>(@Nat.cast K Semiring.natCast (b+1))) alpha gamma tables t := by
  induction tables generalizing t with
  | nil => rfl
  | cons table rest ih =>
    simp only [busBoundTablesProduct,busTablesFinalPower]
    rw [bus_bound_side_natural_product table tr t pubValues alpha gamma (finals t) side holds.1 holds.2.1,
      ih (t+1) holds.2.2]

/-- The actual constructed finals, multiplied by public factors on each side,
equal the expanded global message product under source/auxiliary residuals. -/
theorem bus_bound_global_product [DecidableEq K] [PubVal K] (air : AirP) (tr : Trace K)
    (pubValues : List K) (alpha gamma : K) (finals : Nat→Nat→K) (side : Bool)
    (holds : busTablesResidualsZero tr pubValues alpha gamma finals air.tables 0) :
    busBoundTablesProduct tr pubValues alpha gamma finals side air.tables 0 *
      ((busTracePublic air pubValues side).map
        (busMessageFactor id (fun b=>(@Nat.cast K Semiring.natCast (b+1))) alpha gamma)).prod=
    ((((busTraceMessages air tr pubValues side).map
      (busEncodeMessage id (fun b=>(@Nat.cast K Semiring.natCast (b+1))))).map
        (ZkFormal.Udr.fp alpha)).map (gamma-·)).prod := by
  rw [bus_bound_tables_natural_product _ _ _ _ _ _ _ _ holds]
  exact (bus_expanded_global_product air tr pubValues side id _ alpha gamma).symm

end NearCompression
