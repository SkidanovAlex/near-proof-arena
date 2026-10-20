import NearCompression.BusTableFormulaLayout
import NearCompression.BusTaggedChallengeBound
import NearCompression.AirCombinedResidualRows

namespace NearCompression
open Lean.Grind ZkFormal.Air ZkFormal.Udr
variable {K : Type} [Field K]

/-- Public values become fixed constants; all other source AST operations
retain the same current/next and selector environment. -/
def lowerBusSource (pubValues : List K) : Expr → BusProgramFormula K
  | .const n => .literal (@Nat.cast K Semiring.natCast n)
  | .pub p => .literal (pubValues.getD p 0)
  | .col c nx => if nx then .next c else .current c
  | .isFirst => .first
  | .isLast => .last
  | .isTransition => .transition
  | .add a b => .add (lowerBusSource pubValues a) (lowerBusSource pubValues b)
  | .mul a b => .mul (lowerBusSource pubValues a) (lowerBusSource pubValues b)
  | .neg a => .sub (.literal 0) (lowerBusSource pubValues a)

theorem bus_source_formula_value (env : TerminalProgramEnvironment K) (pubValues : List K) (e : Expr) :
    busProgramFormulaValue env (lowerBusSource pubValues e)=e.evalWith (airProgramEnv env pubValues) := by
  induction e with
  | const n | pub p | isFirst | isLast | isTransition => rfl
  | col c nx => cases nx <;> rfl
  | add a b ha hb | mul a b ha hb =>
    simp only [lowerBusSource,busProgramFormulaValue,Expr.evalWith,airProgramEnv,ha,hb]
  | neg a ha =>
    simp only [lowerBusSource,busProgramFormulaValue,Expr.evalWith,airProgramEnv,ha]
    grind

/-- Horner form with the bus tag as the terminal coefficient. -/
def busTaggedFormula (alpha tag : K) : List (BusProgramFormula K) → BusProgramFormula K
  | [] => .literal tag
  | x::xs => .add x (.mul (.literal alpha) (busTaggedFormula alpha tag xs))

theorem bus_tagged_formula_value (env : TerminalProgramEnvironment K) (alpha tag : K)
    (message : List (BusProgramFormula K)) :
    busProgramFormulaValue env (busTaggedFormula alpha tag message)=
      fp alpha (message.map (busProgramFormulaValue env)++[tag]) := by
  induction message with
  | nil => simp only [busTaggedFormula,busProgramFormulaValue,List.map_nil,List.nil_append,
      fp,List.foldr_cons,List.foldr_nil]; grind
  | cons x xs ih =>
    simp only [busTaggedFormula,busProgramFormulaValue,List.map_cons,List.cons_append,fp_cons,ih]

def lowerBusInteraction (pubValues : List K) (alpha gamma : K) (i : Interaction) : BusFormulaInteraction K :=
  ⟨.sub (.literal gamma) (busTaggedFormula alpha (@Nat.cast K Semiring.natCast (i.bus+1))
      (i.msg.map (lowerBusSource pubValues))),
    i.mult.map (lowerBusSource pubValues),i.send⟩

theorem bus_lowered_interaction_values (env : TerminalProgramEnvironment K) (pubValues : List K)
    (alpha gamma : K) (i : Interaction) :
    busProgramFormulaValue env (lowerBusInteraction pubValues alpha gamma i).power=
      gamma-fp alpha (i.msg.map (fun e=>e.evalWith (airProgramEnv env pubValues))++
        [(@Nat.cast K Semiring.natCast (i.bus+1))]) ∧
    (lowerBusInteraction pubValues alpha gamma i).bits.map (busProgramFormulaValue env)=
      i.mult.map (fun e=>e.evalWith (airProgramEnv env pubValues)) := by
  simp only [lowerBusInteraction,busProgramFormulaValue,bus_tagged_formula_value,List.map_map,
    Function.comp_def,bus_source_formula_value,and_self]

private theorem source_row_env (tr : Trace K) (t r : Nat) (pubValues : List K) :
    airProgramEnv (busRowProgramEnv tr t r) pubValues=rowEnv tr t r pubValues := by
  unfold airProgramEnv busRowProgramEnv rowEnv
  congr 1
  funext c nx
  cases nx <;> rfl

/-- Specialization to the actual source row semantics, including cyclic next
rows and arbitrary field-valued public inputs. -/
theorem bus_source_formula_row (tr : Trace K) (t r : Nat) (pubValues : List K) (e : Expr) :
    busProgramFormulaValue (busRowProgramEnv tr t r) (lowerBusSource pubValues e)=
      e.eval tr t r pubValues := by
  rw [bus_source_formula_value,source_row_env]
  rfl

/-- A lowered interaction's generated chain computes the exact tagged source
factor, not a separately supplied message/factor certificate. -/
theorem bus_source_interaction_factor (tr : Trace K) (t r : Nat) (pubValues : List K)
    (alpha gamma : K) (i : Interaction) (offset : Nat)
    (zero : ∀ e∈(buildBusInteraction (lowerBusInteraction pubValues alpha gamma i).power
      (lowerBusInteraction pubValues alpha gamma i).bits offset).chain,
      busProgramFormulaValue (busRowProgramEnv tr t r) e=0) :
    busProgramFormulaValue (busRowProgramEnv tr t r)
      (buildBusInteraction (lowerBusInteraction pubValues alpha gamma i).power
        (lowerBusInteraction pubValues alpha gamma i).bits offset).factor=
      busBitFactor (gamma-fp alpha (i.msgVal tr t r pubValues++
        [(@Nat.cast K Semiring.natCast (i.bus+1))]))
        (i.mult.map (fun e=>e.eval tr t r pubValues)) := by
  rw [bus_interaction_layout_factor _ _ _ _ zero]
  have values:=bus_lowered_interaction_values (busRowProgramEnv tr t r) pubValues alpha gamma i
  rw [values.1,values.2,source_row_env]
  rfl

/-- Every generated table binding comes from an actual source interaction;
its final product is expressed in that interaction's source AST semantics. -/
theorem bus_source_table_product (interactions : List Interaction) (pubValues : List K)
    (alpha gamma : K) (sourceWidth : Nat) (finals : Nat→K)
    (n : Nat) (positive : 1≤n) (env : Nat→TerminalProgramEnvironment K)
    (hfirst : ∀ r, r<n → (env r).first=if r=0 then 1 else 0)
    (htransition : ∀ r, r<n → (env r).transition=if r+1=n then 0 else 1)
    (hlast : ∀ r, r<n → (env r).last=if r+1=n then 1 else 0)
    (hnext : ∀ r c, r+1<n → (env r).next c=(env (r+1)).current c)
    (zero : ∀ r, r<n → ∀ e∈busTableResiduals
      (interactions.map (lowerBusInteraction pubValues alpha gamma)) sourceWidth finals,
      busProgramFormulaValue (env r) e=0)
    (b : BusBoundInteraction K)
    (hb : b∈busTableBindings (interactions.map (lowerBusInteraction pubValues alpha gamma)) sourceWidth finals) :
    ∃ i∈interactions, b.allocated.interaction=lowerBusInteraction pubValues alpha gamma i ∧
      b.final=((List.range n).map (fun r=>busBitFactor
        (gamma-fp alpha (i.msg.map (fun e=>e.evalWith (airProgramEnv (env r) pubValues))++
          [(@Nat.cast K Semiring.natCast (i.bus+1))]))
        (i.mult.map (fun e=>e.evalWith (airProgramEnv (env r) pubValues))))).prod := by
  have ha : b.allocated∈(busTableBindings (interactions.map (lowerBusInteraction pubValues alpha gamma)) sourceWidth finals).map (fun x=>x.allocated) :=
    List.mem_map.mpr ⟨b,hb,rfl⟩
  unfold busTableBindings at ha
  rw [(bus_table_binding_pairs _ _ _).2] at ha
  have original := (bus_table_group_permutation _).mem_iff.mp ha
  have hi : b.allocated.interaction∈(allocateBusInteractions
      (interactions.map (lowerBusInteraction pubValues alpha gamma)) sourceWidth).map (fun a=>a.interaction) :=
    List.mem_map.mpr ⟨b.allocated,original,rfl⟩
  rw [bus_table_allocation_sources] at hi
  obtain ⟨i,hi,equal⟩:=List.mem_map.mp hi
  refine ⟨i,hi,equal.symm,?_⟩
  rw [bus_table_layout_product _ _ _ n positive env hfirst htransition hlast hnext zero b hb]
  rw [←equal]
  congr 1
  apply List.map_congr_left
  intro r _
  have values:=bus_lowered_interaction_values (env r) pubValues alpha gamma i
  rw [values.1,values.2]

end NearCompression
