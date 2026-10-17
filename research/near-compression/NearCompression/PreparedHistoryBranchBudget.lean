import NearCompression.HistoryBranchBudget
namespace NearCompression
open Lean.Grind ZkFormal.Air ZkFormal.V2 ZkFormal.Algebra ZkFormal.Near
open ArenaCore.Security ZkFormal.Udr NearSpecV3.Wasm

/-- For a locally valid fixed source, restrict the actual prepared-Wasm bus
bound to valid-auxiliary histories and add the two disjoint invalid-table
bounds. The shared accepted failure event is charged once after aggregation.
Branch selection and local bounds must be justified by earlier commitments. -/
theorem prepared_history_branch_budget {R : Type}
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
    (branch : (Fp8 × Fp8) → Option Bool)
    (accept failure : (Fp8 × Fp8) → R → Prop)
    (witness : ∀ alpha∈sample,∀ gamma∈sample,∀ r∈continuations,
      branch (alpha,gamma)=none → accept (alpha,gamma) r → failure (alpha,gamma) r ∨
      ∃ decoded : Trace Fp8,∃ finals : Nat → Nat → Fp8,
        decoded.log=source.log ∧
        (∀ t row column,column<sourceWidth t → decoded.cell t row column=Fp8.ofBase (source.cell t row column)) ∧
        busExt8TablesResidualsZero (decodedBaseTrace decoded) sourceWidth pub alpha gamma finals
          (preparedLiteralAir codeCount).tables 0 ∧
        busExt8ClaimedSideProduct (preparedLiteralAir codeCount) (decodedBaseTrace decoded) sourceWidth pub alpha gamma finals true=
          busExt8ClaimedSideProduct (preparedLiteralAir codeCount) (decodedBaseTrace decoded) sourceWidth pub alpha gamma finals false)
    (localBudget : Bool → Nat) (pcsBudget : Nat)
    (invalidBranches : ∀ b : Bool,
      count ((sample.flatMap (fun alpha=>sample.map (fun gamma=>(alpha,gamma)))).flatMap
        (fun pair=>continuations.map (fun r=>(pair,r))))
        (fun x=>branch x.1=some b ∧ accept x.1 x.2)*sample.length≤localBudget b+
      count ((sample.flatMap (fun alpha=>sample.map (fun gamma=>(alpha,gamma)))).flatMap
        (fun pair=>continuations.map (fun r=>(pair,r))))
        (fun x=>branch x.1=some b ∧ (accept x.1 x.2 ∧ failure x.1 x.2))*sample.length)
    (joint : count ((sample.flatMap (fun alpha=>sample.map (fun gamma=>(alpha,gamma)))).flatMap
        (fun pair=>continuations.map (fun r=>(pair,r))))
        (fun x=>accept x.1 x.2 ∧ failure x.1 x.2)*sample.length≤pcsBudget) :
    let pairs := sample.flatMap (fun alpha=>sample.map (fun gamma=>(alpha,gamma)))
    let experiment := pairs.flatMap (fun pair=>continuations.map (fun r=>(pair,r)))
    count experiment (fun x=>accept x.1 x.2)*sample.length≤
      busTraceErrorBudget (preparedLiteralAir codeCount) source pub 28*
        sample.length*continuations.length*sample.length+
      localBudget false+localBudget true+pcsBudget := by
  intro pairs experiment
  apply history_three_branch_budget pairs continuations branch accept failure sample.length
    (busTraceErrorBudget (preparedLiteralAir codeCount) source pub 28*
      sample.length*continuations.length*sample.length)
    (localBudget false) (localBudget true) pcsBudget _ joint
  intro tag
  cases tag with
  | none =>
    have bus := prepared_decoded_bus_continuation_bound codeCount sourceWidth source pub locals fits
      cfg code method ctx blockLevel full eligible prepared fuel enoughFuel wrong sample distinct
      continuations (fun pair r=>branch pair=none ∧ accept pair r) failure
      (fun alpha ha gamma hg r hr accepted=>witness alpha ha gamma hg r hr accepted.1 accepted.2)
    dsimp only at bus
    have scaled := Nat.mul_le_mul_right sample.length bus
    simpa only [Nat.add_mul,and_assoc] using scaled
  | some b =>
    cases b
    · exact invalidBranches false
    · exact invalidBranches true

end NearCompression
