import NearCompression.PreparedHistoryBranchBudget
import NearCompression.TwoTableAuxiliaryBranch
namespace NearCompression
open Lean.Grind ZkFormal.Air ZkFormal.V2 ZkFormal.Algebra ZkFormal.Near
open ArenaCore.Security ZkFormal.Udr NearSpecV3.Wasm

/-- TableLocal already supplies explicit constraints and Boolean multiplicities;
no second source-residual validity assumption is needed. -/
theorem table_local_all_constraints_zero (table : Table) (tr : Trace Fp) (t : Nat)
    (pub : List Fp) (localChecks : TableLocal table tr t pub) :
    ∀ row,row<tr.height t → ∀ e∈table.allConstraints,e.eval tr t row pub=0 := by
  intro row hr e he
  rcases List.mem_append.mp he with constraint | bit
  · exact localChecks.constr row hr e constraint
  · obtain ⟨interaction,hi,member⟩ := List.mem_flatMap.mp bit
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp member
    have boolean := localChecks.bits row hr interaction hi b hb
    change b.eval tr t row pub*(b.eval tr t row pub + -1)=0
    grind

/-- Instantiate the history partition with fixed actual auxiliary residuals.
Accepted witnesses need coordinate/source binding and equal final products;
bus residual validity is derived from exact checks on the none branch. Local
branch budgets and the shared downstream budget remain explicit. -/
theorem prepared_checked_history_budget {R : Type}
    (codeCount : Nat) (sourceWidth : Nat → Nat) (source : Trace Fp) (pub : List Fp)
    (locals : ∀ t (ht : t<(preparedLiteralAir codeCount).tables.length),
      TableLocal (preparedLiteralAir codeCount).tables[t] source t pub)
    (fits : pubFit (preparedLiteralAir codeCount) pub=true)
    (cfg : NearCfg) (code : ByteArray) (method : String) (ctx : CallCtx)
    (blockLevel full : Bool) (eligible : PreparedRunCallEligible)
    (prepared : preparedLiteralRunCallCheck cfg code method ctx pub blockLevel=some eligible)
    (fuel : Nat) (enoughFuel : source.height 0≤fuel)
    (wrong : ¬∃ final error,runCall cfg code method ctx fuel blockLevel full none=.done final error ∧
      PreparedExecPublishedOutput pub final error)
    (sample : List Fp8) (distinct : sample.Nodup) (continuations : List R)
    (fixed : (Fp8 × Fp8) → Trace Fp) (coordinateWidth : Nat → Nat)
    (formulas : (Fp8 × Fp8) → Nat → List (BusProgramFormula Fp8))
    (finals : (Fp8 × Fp8) → Nat → Nat → Fp8)
    (widths : ∀ j,∀ hj : j<(preparedLiteralAir codeCount).tables.length,
      (preparedLiteralAir codeCount).tables[j].width=sourceWidth j)
    (sourceChecks : ∀ j,∀ hj : j<(preparedLiteralAir codeCount).tables.length,
      (∀ e∈(preparedLiteralAir codeCount).tables[j].allConstraints,e.colBound≤sourceWidth j) ∧
      (∀ i∈(preparedLiteralAir codeCount).tables[j].interactions,∀ e∈i.exprs,e.colBound≤sourceWidth j))
    (checked : ∀ alpha∈sample,∀ gamma∈sample,∀ j,∀ hj : j<(preparedLiteralAir codeCount).tables.length,
      generatedExt8BusSpecCheck
        ((preparedLiteralAir codeCount).tables[j].interactions.map
          (lowerBusInteraction (pub.map Fp8.ofBase) alpha gamma))
        (sourceWidth j) (finals (alpha,gamma) j) (formulas (alpha,gamma) j)=true)
    (bounds : ∀ alpha∈sample,∀ gamma∈sample,∀ j,∀ hj : j<(preparedLiteralAir codeCount).tables.length,
      ∀ e∈formulas (alpha,gamma) j,busFormulaColumnBound e≤coordinateWidth j)
    (accept failure : (Fp8 × Fp8) → R → Prop)
    (witness : ∀ alpha∈sample,∀ gamma∈sample,∀ r∈continuations,
      accept (alpha,gamma) r → failure (alpha,gamma) r ∨
      ∃ decoded : Trace Fp8,
        decoded.log=source.log ∧
        (∀ t row column,column<sourceWidth t → decoded.cell t row column=Fp8.ofBase (source.cell t row column)) ∧
        decoded.log=(fixed (alpha,gamma)).log ∧
        (∀ t row column,column<coordinateWidth t →
          decoded.cell t row column=Fp8.ofBase ((fixed (alpha,gamma)).cell t row column)) ∧
        busExt8ClaimedSideProduct (preparedLiteralAir codeCount) (decodedBaseTrace decoded) sourceWidth pub alpha gamma (finals (alpha,gamma)) true=
          busExt8ClaimedSideProduct (preparedLiteralAir codeCount) (decodedBaseTrace decoded) sourceWidth pub alpha gamma (finals (alpha,gamma)) false)
    (localBudget : Bool → Nat) (pcsBudget : Nat)
    (invalidBranches : ∀ b : Bool,
      count ((sample.flatMap (fun alpha=>sample.map (fun gamma=>(alpha,gamma)))).flatMap
        (fun pair=>continuations.map (fun r=>(pair,r))))
        (fun x=>twoTableAuxiliaryBranch (airExt8Trace (fixed x.1)) (formulas x.1) 0=some b ∧ accept x.1 x.2)*sample.length≤localBudget b+
      count ((sample.flatMap (fun alpha=>sample.map (fun gamma=>(alpha,gamma)))).flatMap
        (fun pair=>continuations.map (fun r=>(pair,r))))
        (fun x=>twoTableAuxiliaryBranch (airExt8Trace (fixed x.1)) (formulas x.1) 0=some b ∧ (accept x.1 x.2 ∧ failure x.1 x.2))*sample.length)
    (joint : count ((sample.flatMap (fun alpha=>sample.map (fun gamma=>(alpha,gamma)))).flatMap
        (fun pair=>continuations.map (fun r=>(pair,r))))
        (fun x=>accept x.1 x.2 ∧ failure x.1 x.2)*sample.length≤pcsBudget) :
    let pairs := sample.flatMap (fun alpha=>sample.map (fun gamma=>(alpha,gamma)))
    let experiment := pairs.flatMap (fun pair=>continuations.map (fun r=>(pair,r)))
    count experiment (fun x=>accept x.1 x.2)*sample.length≤
      busTraceErrorBudget (preparedLiteralAir codeCount) source pub 28*
        sample.length*continuations.length*sample.length+
      localBudget false+localBudget true+pcsBudget := by
  let branch := fun pair=>twoTableAuxiliaryBranch (airExt8Trace (fixed pair)) (formulas pair) 0
  apply prepared_history_branch_budget codeCount sourceWidth source pub locals fits cfg code method ctx
    blockLevel full eligible prepared fuel enoughFuel wrong sample distinct continuations branch accept failure
    _ localBudget pcsBudget invalidBranches joint
  intro alpha ha gamma hg r hr selected accepted
  rcases witness alpha ha gamma hg r hr accepted with failed | ⟨decoded,sourceLogs,sourceCells,fixedLogs,fixedCells,equal⟩
  · exact Or.inl failed
  · apply Or.inr
    refine ⟨decoded,finals (alpha,gamma),sourceLogs,sourceCells,?_,equal⟩
    apply unselected_auxiliary_decoded_bus_validity (preparedLiteralAir codeCount).tables rfl
      (fixed (alpha,gamma)) decoded coordinateWidth fixedLogs fixedCells sourceWidth pub alpha gamma
      (finals (alpha,gamma)) (formulas (alpha,gamma)) 0
    · simpa only [Nat.zero_add] using widths
    · intro j hj
      have sc := sourceChecks j hj
      simp only [Nat.zero_add]
      refine ⟨sc.1,sc.2,?_⟩
      intro row hrow e he
      rw [decoded_base_trace_attached source sourceWidth decoded sourceLogs sourceCells,
        bus_attached_source_eval source sourceWidth _ j row pub e (sc.1 e he)]
      exact table_local_all_constraints_zero _ source j pub (locals j hj) row
        (by simpa only [Trace.height,decodedBaseTrace,sourceLogs] using hrow) e he
    · simpa only [Nat.zero_add] using checked alpha ha gamma hg
    · simpa only [Nat.zero_add] using bounds alpha ha gamma hg
    · exact selected

end NearCompression
