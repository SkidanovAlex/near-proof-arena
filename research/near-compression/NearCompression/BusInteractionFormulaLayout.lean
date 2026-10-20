import NearCompression.BusChainFormulaLayout

namespace NearCompression
open Lean.Grind
variable {K : Type} [Field K]

structure BusInteractionFormulaLayout (K : Type) where
  chain : List (BusProgramFormula K)
  factor : BusProgramFormula K

def buildBusInteraction (power : BusProgramFormula K)
    (bits : List (BusProgramFormula K)) (offset : Nat) : BusInteractionFormulaLayout K :=
  match bits with
  | [] => ⟨[],.literal 1⟩
  | headBit::rest =>
    let initial := BusProgramFormula.add (.literal 1) (.mul headBit (.sub power (.literal 1)))
    let chain := buildBusChain power initial rest offset (offset+rest.length)
    ⟨chain.squares++chain.links,chain.products.getLastD initial⟩

private theorem map_last {α β : Type} (f : α→β) (xs : List α) (default : α) :
    f (xs.getLastD default)=(xs.map f).getLastD (f default) := by
  induction xs generalizing default with
  | nil => rfl
  | cons x xs ih => simpa only [List.getLastD_cons,List.map_cons] using ih x

/-- Derived factor for arbitrary multiplicity values, including empty lists and
zero fingerprints. Booleanity is a separate source constraint. -/
theorem bus_interaction_layout_factor (env : TerminalProgramEnvironment K)
    (power : BusProgramFormula K) (bits : List (BusProgramFormula K)) (offset : Nat)
    (zero : ∀ e∈(buildBusInteraction power bits offset).chain,busProgramFormulaValue env e=0) :
    busProgramFormulaValue env (buildBusInteraction power bits offset).factor=
      busBitFactor (busProgramFormulaValue env power) (bits.map (busProgramFormulaValue env)) := by
  cases bits with
  | nil => rfl
  | cons headBit rest =>
    let initial := BusProgramFormula.add (.literal 1) (.mul headBit (.sub power (.literal 1)))
    have hs : ∀ e∈(buildBusChain power initial rest offset (offset+rest.length)).squares,
        busProgramFormulaValue env e=0 := fun e he => zero e (List.mem_append_left _ he)
    have hl : ∀ e∈(buildBusChain power initial rest offset (offset+rest.length)).links,
        busProgramFormulaValue env e=0 := fun e he => zero e (List.mem_append_right _ he)
    have h := bus_chain_layout_zero env power initial rest offset (offset+rest.length) hs hl
    change busProgramFormulaValue env ((buildBusChain power initial rest offset (offset+rest.length)).products.getLastD initial)=_
    rw [map_last (busProgramFormulaValue env)]
    exact bus_aux_factor _ _ _ _ _ h

theorem bus_interaction_layout_length (power : BusProgramFormula K)
    (bits : List (BusProgramFormula K)) (offset : Nat) :
    (buildBusInteraction power bits offset).chain.length=2*(bits.length-1) := by
  cases bits with
  | nil => rfl
  | cons headBit rest =>
    simp only [buildBusInteraction,List.length_append]
    rw [(bus_chain_layout_lengths _ _ _ _ _).1,(bus_chain_layout_lengths _ _ _ _ _).2]
    simp only [List.length_cons]
    omega

/-- Boundary gates consume the factor derived from the generated chain, not a
separately assumed multiplicity product. The caller allocates accumulator
columns after all interaction chain columns, matching the table layout. -/
def busInteractionResiduals (power : BusProgramFormula K)
    (bits : List (BusProgramFormula K)) (offset accumulator : Nat) (final : K) :
    List (BusProgramFormula K) :=
  let built:=buildBusInteraction power bits offset
  built.chain++busBoundaryFormulas (.current accumulator) (.next accumulator) built.factor final

theorem bus_interaction_residuals_zero (env : TerminalProgramEnvironment K)
    (power : BusProgramFormula K) (bits : List (BusProgramFormula K))
    (offset accumulator : Nat) (final : K)
    (zero : ∀ e∈busInteractionResiduals power bits offset accumulator final,
      busProgramFormulaValue env e=0) :
    let factor:=busBitFactor (busProgramFormulaValue env power) (bits.map (busProgramFormulaValue env))
    env.first*(env.current accumulator-1)=0 ∧
    env.transition*(env.next accumulator-env.current accumulator*factor)=0 ∧
    env.last*(env.current accumulator*factor-final)=0 := by
  have factor := bus_interaction_layout_factor env power bits offset
    (fun e he => zero e (List.mem_append_left _ he))
  have gates : ∀ e∈busBoundaryFormulas (.current accumulator) (.next accumulator)
      (buildBusInteraction power bits offset).factor final,busProgramFormulaValue env e=0 :=
    fun e he => zero e (List.mem_append_right _ he)
  have a := gates _ (List.mem_cons_self ..)
  have b := gates _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  have c := gates _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
  simp only [busProgramFormulaValue] at a b c
  rw [factor] at b c
  exact ⟨a,b,c⟩

/-- All generated per-row residuals imply the advertised final interaction
product. Selector and next-row hypotheses are explicit environment bindings. -/
theorem bus_interaction_layout_product (n : Nat) (positive : 1≤n)
    (env : Nat→TerminalProgramEnvironment K) (power : BusProgramFormula K)
    (bits : List (BusProgramFormula K)) (offset accumulator : Nat) (final : K)
    (hfirst : ∀ r, r<n → (env r).first=if r=0 then 1 else 0)
    (htransition : ∀ r, r<n → (env r).transition=if r+1=n then 0 else 1)
    (hlast : ∀ r, r<n → (env r).last=if r+1=n then 1 else 0)
    (hnext : ∀ r, r+1<n → (env r).next accumulator=(env (r+1)).current accumulator)
    (zero : ∀ r, r<n → ∀ e∈busInteractionResiduals power bits offset accumulator final,
      busProgramFormulaValue (env r) e=0) :
    final=((List.range n).map (fun r=>busBitFactor (busProgramFormulaValue (env r) power)
      (bits.map (busProgramFormulaValue (env r))))).prod := by
  have gates := fun r hr => bus_interaction_residuals_zero (env r) power bits offset accumulator final (zero r hr)
  exact generic_bus_product_of_gates n positive
    (fun r=>(env r).current accumulator) (fun r=>(env r).next accumulator)
    (fun r=>busBitFactor (busProgramFormulaValue (env r) power) (bits.map (busProgramFormulaValue (env r))))
    (fun r=>(env r).first) (fun r=>(env r).transition) (fun r=>(env r).last) final
    hfirst htransition hlast hnext
    (fun r hr=>(gates r hr).1) (fun r hr=>(gates r hr).2.1) (fun r hr=>(gates r hr).2.2)

end NearCompression
