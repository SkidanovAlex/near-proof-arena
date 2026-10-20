import NearCompression.PreparedDecodedBusContinuation
import NearCompression.TwoTableConcretePCS
namespace NearCompression
open Lean.Grind ZkFormal.Air ZkFormal.V2 ZkFormal.Algebra ZkFormal.Near
open ArenaCore.Security ZkFormal.Udr NearSpecV3.Wasm

/-- Branch choice is determined by one fixed source before all bus/local
challenges. Therefore pay the maximum of the two local budgets and the bus
budget, with the same accepted downstream failure count charged only once.
The local budgets and joint error bound must cover this full experiment. -/
theorem prepared_fixed_source_branch_budget {R : Type}
    (codeCount : Nat) (sourceWidth : Nat → Nat) (source : Trace Fp) (pub : List Fp)
    (fits : pubFit (preparedLiteralAir codeCount) pub=true)
    (cfg : NearCfg) (code : ByteArray) (method : String) (ctx : CallCtx)
    (blockLevel full : Bool) (eligible : PreparedRunCallEligible)
    (prepared : preparedLiteralRunCallCheck cfg code method ctx pub blockLevel=some eligible)
    (fuel : Nat) (enoughFuel : source.height 0≤fuel)
    (wrong : ¬∃ final error,runCall cfg code method ctx fuel blockLevel full none=.done final error ∧
      PreparedExecPublishedOutput pub final error)
    (sample : List Fp8) (distinct : sample.Nodup) (continuations : List R)
    (accept failure : (Fp8 × Fp8) → R → Prop)
    (witness : ∀ alpha∈sample,∀ gamma∈sample,∀ r∈continuations,
      accept (alpha,gamma) r → failure (alpha,gamma) r ∨
      ∃ decoded : Trace Fp8,∃ finals : Nat → Nat → Fp8,
        decoded.log=source.log ∧
        (∀ t row column,column<sourceWidth t → decoded.cell t row column=Fp8.ofBase (source.cell t row column)) ∧
        busExt8TablesResidualsZero (decodedBaseTrace decoded) sourceWidth pub alpha gamma finals
          (preparedLiteralAir codeCount).tables 0 ∧
        busExt8ClaimedSideProduct (preparedLiteralAir codeCount) (decodedBaseTrace decoded) sourceWidth pub alpha gamma finals true=
          busExt8ClaimedSideProduct (preparedLiteralAir codeCount) (decodedBaseTrace decoded) sourceWidth pub alpha gamma finals false)
    (localBudget : Nat → Nat) (pcsBudget : Nat)
    (invalidLocal : ∀ t,∀ ht : t<(preparedLiteralAir codeCount).tables.length,
      ¬TableLocal (preparedLiteralAir codeCount).tables[t] source t pub →
      count ((sample.flatMap (fun alpha=>sample.map (fun gamma=>(alpha,gamma)))).flatMap
        (fun pair=>continuations.map (fun r=>(pair,r)))) (fun x=>accept x.1 x.2)*sample.length ≤
        localBudget t+
        count ((sample.flatMap (fun alpha=>sample.map (fun gamma=>(alpha,gamma)))).flatMap
          (fun pair=>continuations.map (fun r=>(pair,r))))
          (fun x=>accept x.1 x.2 ∧ failure x.1 x.2)*sample.length)
    (jointErrors : count ((sample.flatMap (fun alpha=>sample.map (fun gamma=>(alpha,gamma)))).flatMap
        (fun pair=>continuations.map (fun r=>(pair,r))))
        (fun x=>accept x.1 x.2 ∧ failure x.1 x.2)*sample.length≤pcsBudget) :
    let pairs := sample.flatMap (fun alpha=>sample.map (fun gamma=>(alpha,gamma)))
    let experiment := pairs.flatMap (fun pair=>continuations.map (fun r=>(pair,r)))
    count experiment (fun x=>accept x.1 x.2)*sample.length ≤
      max (max (localBudget 0) (localBudget 1))
        (busTraceErrorBudget (preparedLiteralAir codeCount) source pub 28*
          sample.length*continuations.length*sample.length)+pcsBudget := by
  classical
  intro pairs experiment
  by_cases locals : ∀ t (ht : t<(preparedLiteralAir codeCount).tables.length),
      TableLocal (preparedLiteralAir codeCount).tables[t] source t pub
  · have bus := prepared_decoded_bus_continuation_bound codeCount sourceWidth source pub locals fits
      cfg code method ctx blockLevel full eligible prepared fuel enoughFuel wrong sample distinct
      continuations accept failure witness
    dsimp only at bus
    have scaled := Nat.mul_le_mul_right sample.length bus
    rw [Nat.add_mul] at scaled
    have result := Nat.le_trans scaled (Nat.add_le_add_left jointErrors _)
    exact Nat.le_trans result (Nat.add_le_add_right (Nat.le_max_right _ _) _)
  · have failed : ∃ t,∃ ht : t<(preparedLiteralAir codeCount).tables.length,
        ¬TableLocal (preparedLiteralAir codeCount).tables[t] source t pub := by
      exact Classical.byContradiction (fun absent=>locals (fun t ht=>
        Classical.byContradiction (fun bad=>absent ⟨t,ht,bad⟩)))
    obtain ⟨t,ht,bad⟩ := failed
    have bound := invalidLocal t ht bad
    have result := Nat.le_trans bound (Nat.add_le_add_left jointErrors _)
    have two : t<2 := ht
    have selected : localBudget t≤max (localBudget 0) (localBudget 1) := by
      have cases : t=0 ∨ t=1 := by omega
      rcases cases with h | h
      · subst t;exact Nat.le_max_left _ _
      · subst t;exact Nat.le_max_right _ _
    exact Nat.le_trans result (Nat.add_le_add_right (Nat.le_trans selected (Nat.le_max_left _ _)) _)

end NearCompression
