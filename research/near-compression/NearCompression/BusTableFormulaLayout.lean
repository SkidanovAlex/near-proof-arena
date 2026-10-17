import NearCompression.BusInteractionFormulaLayout

namespace NearCompression
open Lean.Grind
variable {K : Type} [Field K]

structure BusFormulaInteraction (K : Type) where
  power : BusProgramFormula K
  bits : List (BusProgramFormula K)
  send : Bool

structure BusAllocatedInteraction (K : Type) where
  interaction : BusFormulaInteraction K
  offset : Nat

def allocateBusInteractions : List (BusFormulaInteraction K) → Nat → List (BusAllocatedInteraction K)
  | [],_ => []
  | i::rest,offset => ⟨i,offset⟩::allocateBusInteractions rest (offset+2*(i.bits.length-1))

def busTableChainColumns (interactions : List (BusFormulaInteraction K)) : Nat :=
  (interactions.map (fun i=>2*(i.bits.length-1))).sum

def busTableGroupOrder (allocated : List (BusAllocatedInteraction K)) : List (BusAllocatedInteraction K) :=
  allocated.filter (fun a=>a.interaction.send) ++ allocated.filter (fun a=> !a.interaction.send)

structure BusBoundInteraction (K : Type) where
  allocated : BusAllocatedInteraction K
  accumulator : Nat
  final : K

def bindBusAccumulators : List (BusAllocatedInteraction K) → Nat → (Nat→K) → List (BusBoundInteraction K)
  | [],_,_ => []
  | a::rest,column,finals => ⟨a,column,finals 0⟩::bindBusAccumulators rest (column+1) (fun i=>finals (i+1))

def busTableBindings (interactions : List (BusFormulaInteraction K)) (sourceWidth : Nat) (finals : Nat→K) :=
  bindBusAccumulators (busTableGroupOrder (allocateBusInteractions interactions sourceWidth))
    (sourceWidth+busTableChainColumns interactions) finals

def busAllocatedChain (a : BusAllocatedInteraction K) :=
  (buildBusInteraction a.interaction.power a.interaction.bits a.offset).chain

def busBoundBoundary (b : BusBoundInteraction K) :=
  busBoundaryFormulas (.current b.accumulator) (.next b.accumulator)
    (buildBusInteraction b.allocated.interaction.power b.allocated.interaction.bits b.allocated.offset).factor b.final

/-- Chain residuals retain source interaction order. Accumulator residuals use
stable send-then-receive order, with all accumulator columns after all chains. -/
def busTableResiduals (interactions : List (BusFormulaInteraction K)) (sourceWidth : Nat) (finals : Nat→K) :=
  (allocateBusInteractions interactions sourceWidth).flatMap busAllocatedChain ++
  (busTableBindings interactions sourceWidth finals).flatMap busBoundBoundary

theorem bus_table_allocation_sources (interactions : List (BusFormulaInteraction K)) (offset : Nat) :
    (allocateBusInteractions interactions offset).map (fun a=>a.interaction)=interactions := by
  induction interactions generalizing offset with
  | nil => rfl
  | cons i rest ih => simp only [allocateBusInteractions,List.map_cons,ih]

theorem bus_table_chain_length (interactions : List (BusFormulaInteraction K)) (offset : Nat) :
    ((allocateBusInteractions interactions offset).flatMap busAllocatedChain).length=
      busTableChainColumns interactions := by
  induction interactions generalizing offset with
  | nil => rfl
  | cons i rest ih =>
    simp only [allocateBusInteractions,List.flatMap_cons,List.length_append,busAllocatedChain,
      bus_interaction_layout_length,ih,busTableChainColumns,List.map_cons,List.sum_cons]

theorem bus_table_group_permutation (xs : List (BusAllocatedInteraction K)) :
    (busTableGroupOrder xs).Perm xs := by
  exact List.filter_append_perm (fun a=>a.interaction.send) xs

/-- Accumulator/final pairs are consecutive and preserve the entire grouped
list, so neither omitted interactions nor truncated finals can be hidden. -/
theorem bus_table_binding_pairs (xs : List (BusAllocatedInteraction K))
    (column : Nat) (finals : Nat→K) :
    (bindBusAccumulators xs column finals).map (fun b=>(b.accumulator,b.final))=
      (List.range xs.length).map (fun i=>(column+i,finals i)) ∧
    (bindBusAccumulators xs column finals).map (fun b=>b.allocated)=xs := by
  induction xs generalizing column finals with
  | nil => simp [bindBusAccumulators]
  | cons a rest ih =>
    have tail:=ih (column+1) (fun i=>finals (i+1))
    simp only [bindBusAccumulators,List.map_cons,List.length_cons,List.range_succ_eq_map,
      List.map_map,Function.comp_def,Nat.add_zero,tail.1,tail.2]
    constructor
    · congr 2; funext i; congr 1 <;> omega
    · trivial

private theorem group_mem (a : BusAllocatedInteraction K) (xs : List (BusAllocatedInteraction K))
    (h : a∈busTableGroupOrder xs) : a∈xs := by
  rcases List.mem_append.mp h with h | h
  · exact (List.mem_filter.mp h).1
  · exact (List.mem_filter.mp h).1

private theorem binding_mem (b : BusBoundInteraction K) (xs : List (BusAllocatedInteraction K))
    (column : Nat) (finals : Nat→K) (h : b∈bindBusAccumulators xs column finals) : b.allocated∈xs := by
  induction xs generalizing column finals with
  | nil => simp [bindBusAccumulators] at h
  | cons a rest ih =>
    rcases List.mem_cons.mp h with h | h
    · subst b; exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (ih _ _ h)

/-- Every bound interaction's full residuals occur in the table's actual
ordered residual list; no separately supplied membership/route certificate. -/
theorem bus_table_interaction_residual_mem (interactions : List (BusFormulaInteraction K))
    (sourceWidth : Nat) (finals : Nat→K) (b : BusBoundInteraction K)
    (hb : b∈busTableBindings interactions sourceWidth finals)
    (e : BusProgramFormula K)
    (he : e∈busInteractionResiduals b.allocated.interaction.power b.allocated.interaction.bits
      b.allocated.offset b.accumulator b.final) :
    e∈busTableResiduals interactions sourceWidth finals := by
  have ha := group_mem b.allocated _ (binding_mem b _ _ _ hb)
  rcases List.mem_append.mp he with he | he
  · exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨b.allocated,ha,he⟩)
  · exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨b,hb,he⟩)

/-- Vanishing table residuals imply every bound interaction's final product.
The full table's column and residual allocation is constructed above. -/
theorem bus_table_layout_product (interactions : List (BusFormulaInteraction K))
    (sourceWidth : Nat) (finals : Nat→K) (n : Nat) (positive : 1≤n)
    (env : Nat→TerminalProgramEnvironment K)
    (hfirst : ∀ r, r<n → (env r).first=if r=0 then 1 else 0)
    (htransition : ∀ r, r<n → (env r).transition=if r+1=n then 0 else 1)
    (hlast : ∀ r, r<n → (env r).last=if r+1=n then 1 else 0)
    (hnext : ∀ r c, r+1<n → (env r).next c=(env (r+1)).current c)
    (zero : ∀ r, r<n → ∀ e∈busTableResiduals interactions sourceWidth finals,
      busProgramFormulaValue (env r) e=0)
    (b : BusBoundInteraction K) (hb : b∈busTableBindings interactions sourceWidth finals) :
    b.final=((List.range n).map (fun r=>busBitFactor
      (busProgramFormulaValue (env r) b.allocated.interaction.power)
      (b.allocated.interaction.bits.map (busProgramFormulaValue (env r))))).prod := by
  exact bus_interaction_layout_product n positive env _ _ _ _ _ hfirst htransition hlast
    (fun r hr=>hnext r _ hr)
    (fun r hr e he=>zero r hr e (bus_table_interaction_residual_mem interactions sourceWidth finals b hb e he))

end NearCompression
