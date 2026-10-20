import NearCompression.BusProgramFormulas

namespace NearCompression
open Lean.Grind
variable {K : Type} [Field K]

structure BusChainFormulaLayout (K : Type) where
  squares : List (BusProgramFormula K)
  links : List (BusProgramFormula K)
  powers : List (BusProgramFormula K)
  products : List (BusProgramFormula K)

/-- Deterministic layout of a multiplicity tail. Power columns and product
columns are separate contiguous runs; squares precede links in the residuals. -/
def buildBusChain (power accumulator : BusProgramFormula K) :
    List (BusProgramFormula K) → Nat → Nat → BusChainFormulaLayout K
  | [],_,_ => ⟨[],[],[],[]⟩
  | bit::rest,powerColumn,productColumn =>
    let p : BusProgramFormula K:=.current powerColumn
    let v : BusProgramFormula K:=.current productColumn
    let tail:=buildBusChain p v rest (powerColumn+1) (productColumn+1)
    ⟨busSquareFormula power p::tail.squares,busProductFormula bit p accumulator v::tail.links,
      p::tail.powers,v::tail.products⟩

/-- Exact column order, including nonzero offsets. No zip truncation or
supplied shape certificate is used. -/
theorem bus_chain_layout_columns (power accumulator : BusProgramFormula K)
    (bits : List (BusProgramFormula K)) (powerColumn productColumn : Nat) :
    (buildBusChain power accumulator bits powerColumn productColumn).powers=
      (List.range bits.length).map (fun i=>BusProgramFormula.current (powerColumn+i)) ∧
    (buildBusChain power accumulator bits powerColumn productColumn).products=
      (List.range bits.length).map (fun i=>BusProgramFormula.current (productColumn+i)) := by
  induction bits generalizing power accumulator powerColumn productColumn with
  | nil => simp [buildBusChain]
  | cons bit rest ih =>
    have tail:=ih (.current powerColumn) (.current productColumn) (powerColumn+1) (productColumn+1)
    simp only [buildBusChain,List.length_cons,List.range_succ_eq_map,List.map_cons,List.map_map,
      Function.comp_def,Nat.add_zero,tail.1,tail.2]
    constructor <;> congr 2 <;> funext i <;> congr 1 <;> omega

theorem bus_chain_layout_lengths (power accumulator : BusProgramFormula K)
    (bits : List (BusProgramFormula K)) (powerColumn productColumn : Nat) :
    (buildBusChain power accumulator bits powerColumn productColumn).squares.length=bits.length ∧
    (buildBusChain power accumulator bits powerColumn productColumn).links.length=bits.length := by
  induction bits generalizing power accumulator powerColumn productColumn with
  | nil => simp [buildBusChain]
  | cons bit rest ih =>
    have tail:=ih (.current powerColumn) (.current productColumn) (powerColumn+1) (productColumn+1)
    simp only [buildBusChain,List.length_cons,tail.1,tail.2,and_self]

/-- Vanishing generated residuals imply the actual auxiliary chain equations.
The chain is derived from the builder, rather than assumed via a route. -/
theorem bus_chain_layout_zero (env : TerminalProgramEnvironment K)
    (power accumulator : BusProgramFormula K) (bits : List (BusProgramFormula K))
    (powerColumn productColumn : Nat)
    (squareZero : ∀ e∈(buildBusChain power accumulator bits powerColumn productColumn).squares,
      busProgramFormulaValue env e=0)
    (linkZero : ∀ e∈(buildBusChain power accumulator bits powerColumn productColumn).links,
      busProgramFormulaValue env e=0) :
    BusAuxChainHolds (busProgramFormulaValue env power) (busProgramFormulaValue env accumulator)
      (bits.map (busProgramFormulaValue env))
      ((buildBusChain power accumulator bits powerColumn productColumn).powers.map (busProgramFormulaValue env))
      ((buildBusChain power accumulator bits powerColumn productColumn).products.map (busProgramFormulaValue env)) := by
  induction bits generalizing power accumulator powerColumn productColumn with
  | nil => exact .empty _ _
  | cons bit rest ih =>
    have square:=squareZero (busSquareFormula power (.current powerColumn)) (by simp [buildBusChain])
    have product:=linkZero (busProductFormula bit (.current powerColumn) accumulator (.current productColumn))
      (by simp [buildBusChain])
    have tail:=ih (.current powerColumn) (.current productColumn) (powerColumn+1) (productColumn+1)
      (fun e he=>squareZero e (by simp only [buildBusChain];exact List.mem_cons_of_mem _ he))
      (fun e he=>linkZero e (by simp only [buildBusChain];exact List.mem_cons_of_mem _ he))
    simp only [buildBusChain,List.map_cons]
    exact .step square product tail

end NearCompression
