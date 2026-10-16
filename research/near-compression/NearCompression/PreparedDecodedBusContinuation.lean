import NearCompression.IndexedDecodedProvenance
namespace NearCompression
open Lean.Grind ZkFormal.Air ZkFormal.V2 ZkFormal.Algebra ZkFormal.Near
open ArenaCore.Security ZkFormal.Udr NearSpecV3.Wasm

/-- Counting a prefix-only event over a chronological product introduces
exactly the continuation length, without fixing any later challenges. -/
theorem prefix_event_continuation_count {A R : Type} (prefixes : List A)
    (continuations : List R) (event : A → Prop) :
    count (prefixes.flatMap (fun p=>continuations.map (fun r=>(p,r))))
      (fun x=>event x.1)=count prefixes event*continuations.length := by
  classical
  induction prefixes with
  | nil => simp [count]
  | cons p ps ih =>
    simp only [List.flatMap_cons,count_append,count_map,ih,count_cons]
    rw [count_const]
    by_cases h : event p <;> simp [h,Nat.add_mul,Nat.add_comm]

/-- For a locally valid fixed source with wrong prepared-Wasm output, every
accepted continuation either belongs to the explicitly retained downstream
failure event or yields the existing adaptive bus event. Decoded witnesses
and finals may depend on the entire continuation. This is the locally valid
source branch, not a complete verifier-acceptance theorem. -/
theorem prepared_decoded_bus_continuation_bound {R : Type}
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
    (accept failure : (Fp8 × Fp8) → R → Prop)
    (witness : ∀ alpha∈sample,∀ gamma∈sample,∀ r∈continuations,
      accept (alpha,gamma) r → failure (alpha,gamma) r ∨
      ∃ decoded : Trace Fp8,∃ finals : Nat → Nat → Fp8,
        decoded.log=source.log ∧
        (∀ t row column,column<sourceWidth t → decoded.cell t row column=Fp8.ofBase (source.cell t row column)) ∧
        busExt8TablesResidualsZero (decodedBaseTrace decoded) sourceWidth pub alpha gamma finals
          (preparedLiteralAir codeCount).tables 0 ∧
        busExt8ClaimedSideProduct (preparedLiteralAir codeCount) (decodedBaseTrace decoded) sourceWidth pub alpha gamma finals true=
          busExt8ClaimedSideProduct (preparedLiteralAir codeCount) (decodedBaseTrace decoded) sourceWidth pub alpha gamma finals false) :
    let pairs := sample.flatMap (fun alpha=>sample.map (fun gamma=>(alpha,gamma)))
    let experiment := pairs.flatMap (fun pair=>continuations.map (fun r=>(pair,r)))
    count experiment (fun x=>accept x.1 x.2) ≤
      busTraceErrorBudget (preparedLiteralAir codeCount) source pub 28*sample.length*continuations.length+
      count experiment (fun x=>accept x.1 x.2 ∧ failure x.1 x.2) := by
  classical
  intro pairs experiment
  let bus := fun pair : Fp8 × Fp8 =>
    busAdaptiveAuxiliaryAccept (preparedLiteralAir codeCount) source sourceWidth pub pair.1 pair.2
  have inclusion : count experiment (fun x=>accept x.1 x.2) ≤
      count experiment (fun x=>bus x.1 ∨ (accept x.1 x.2 ∧ failure x.1 x.2)) := by
    apply count_mono_mem
    intro x hx accepted
    simp only [experiment,pairs,List.mem_flatMap,List.mem_map] at hx
    obtain ⟨pair,⟨alpha,ha,gamma,hg,rfl⟩,r,hr,rfl⟩ := hx
    rcases witness alpha ha gamma hg r hr accepted with bad | good
    · exact Or.inr ⟨accepted,bad⟩
    · obtain ⟨decoded,finals,logs,fixed,holds,equal⟩ := good
      exact Or.inl (decoded_bus_implies_adaptive_accept (preparedLiteralAir codeCount) source sourceWidth
        decoded logs fixed pub alpha gamma finals holds equal)
  have union := count_or_le experiment (fun x=>bus x.1) (fun x=>accept x.1 x.2 ∧ failure x.1 x.2)
  have lift := prefix_event_continuation_count pairs continuations bus
  have bound := prepared_literal_wrong_output_adaptive_bus_bound codeCount sourceWidth source pub locals fits
    cfg code method ctx blockLevel full eligible prepared fuel enoughFuel wrong sample distinct
  have scaled := Nat.mul_le_mul_right continuations.length bound
  change count pairs bus*continuations.length≤_ at scaled
  change count experiment (fun x=>bus x.1)=_ at lift
  rw [lift] at union
  omega

end NearCompression
