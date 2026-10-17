import NearCompression.SecondTableFixedSourcePCS
namespace NearCompression
open Lean.Grind ZkFormal.Near ZkFormal.Udr ZkFormal.V2 ZkFormal.Air ZkFormal.Algebra ArenaCore.Security

/-- Everything after the first local protocol, preserving chronological order. -/
def firstTablePCSContinuations (sample : List Fp8) (secondRows : Nat)
    (layout : GKRJointLayout) (earlierRounds : List Nat) (queries : Nat) :=
  (decodedLocalPrefixes sample secondRows).flatMap (fun q=>
    (twoTablePCSContinuations sample layout earlierRounds queries).map (fun r=>(q,r)))

/-- A failed first source table has the same full two-table PCS error budget
as the second-table branch. The entire second local protocol is downstream;
its messages may depend on the first prefix. Earlier bus choices are fixed. -/
theorem first_table_fixed_source_pcs_budget
    (sample : List Fp8) (distinct : sample.Nodup) (layout : GKRJointLayout)
    (secondRows : Nat) (earlierRounds : List Nat) (queries : Nat)
    (table : Table) (sourceTrace : Trace Fp) (sourceWidth : Nat → Nat) (t n : Nat)
    (rowShape : layout.rowCoordinates=(n+1)+secondRows)
    (log : sourceTrace.log t=n+1) (upper : sourceTrace.log t≤table.maxLog)
    (pub : List Fp) (invalid : ¬TableLocal table sourceTrace t pub)
    (bounds : ∀ e∈tableSourceResiduals table,e.colBound≤sourceWidth t)
    (trace : Trace Fp8) (logs : trace.log=sourceTrace.log)
    (fixed : ∀ s row column,column<sourceWidth s → trace.cell s row column=Fp8.ofBase (sourceTrace.cell s row column))
    (auxiliary : List (BusProgramFormula Fp8)) (residuals : List (AIRBusResidual Fp8 × Nat))
    (order : residuals.map Prod.fst=(tableSourceResiduals table).map Sum.inl++auxiliary.map Sum.inr)
    (d : Nat) (sourceDegrees : ∀ e∈tableSourceResiduals table,e.degree≤d)
    (auxDegrees : ∀ e∈auxiliary,busFormulaDegree e≤d)
    (sent : Fp8 → List Fp8 → List Fp8 → Poly Fp8) (claim : Fp8 → List Fp8 → List Fp8 → Fp8)
    (initialZero : ∀ mixing tau,claim mixing tau []=0)
    (accept : LocalChallengePrefix Fp8 → LocalChallengePrefix Fp8 →
      (Fp8 × (List (GKRBlock Fp8) × (List Fp8 × (List Fp8 × List Nat)))) → Prop)
    (checks : ∀ p∈decodedLocalPrefixes sample (n+1),∀ q∈decodedLocalPrefixes sample secondRows,
      ∀ r∈twoTablePCSContinuations sample layout earlierRounds queries,
      accept p q r → decodedLocalChecks d sent claim p)
    (repair budget : Nat)
    (event : LocalChallengePrefix Fp8 → LocalChallengePrefix Fp8 → Fp8 →
      List (GKRBlock Fp8) → List Fp8 → List Fp8 → List Nat → Prop)
    (wrongTerminal : ∀ p∈decodedLocalPrefixes sample (n+1),
      ¬decodedLocalTerminalCorrect (n+1) (fun column row=>trace.cell t row column)
        (pub.map Fp8.ofBase) residuals claim p →
      count (firstTablePCSContinuations sample secondRows layout earlierRounds queries)
        (fun x=>accept p x.1 x.2)*sample.length ≤ repair+
      count (firstTablePCSContinuations sample secondRows layout earlierRounds queries)
        (fun x=>event p x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2)*sample.length)
    (joint : ∀ first∈airLocalInitialChallenges sample (n+1),
      ∀ second∈airLocalInitialChallenges sample secondRows,∀ rho∈sample,
      ∀ earlier∈gkrChallengePaths sample earlierRounds,
      count (gkrConcretePCSSamples sample layout queries) (fun item=>
        event (first,item.1.take (n+1)) (second,item.1.drop (n+1)) rho
          (earlier++[item.2.1]) item.2.2.1 item.2.2.2.1 item.2.2.2.2)*sample.length≤budget) :
    count ((decodedLocalPrefixes sample (n+1)).flatMap (fun p=>
      (decodedLocalPrefixes sample secondRows).flatMap (fun q=>
        (twoTablePCSContinuations sample layout earlierRounds queries).map (fun r=>(p,q,r)))))
      (fun x=>accept x.1 x.2.1 x.2.2)*sample.length ≤
      (((tableSourceResiduals table).length+auxiliary.length-1+(n+1)+(d+1)*(n+1))*
        sample.length^(2*(n+1)+1))*(firstTablePCSContinuations sample secondRows layout earlierRounds queries).length+
      (decodedLocalPrefixes sample (n+1)).length*repair+
      (airLocalInitialChallenges sample (n+1)).length*((airLocalInitialChallenges sample secondRows).length*
        (sample.length*((gkrChallengePaths sample earlierRounds).length*budget))) := by
  classical
  obtain ⟨row,hr,lane,hl,nonzero⟩ := fixed_source_invalid_residual_index table sourceTrace sourceWidth t n
    log upper pub invalid bounds [()] (fun _=>trace) (fun _ _=>logs) (fun _ _=>fixed)
  have pcs := two_table_gkr_pcs_joint_budget sample layout (n+1) secondRows rowShape
    earlierRounds queries event sample.length budget joint
  have bound := decoded_invalid_trace_continuation_budget sample distinct (fun column row=>trace.cell t row column)
    (pub.map Fp8.ofBase) (tableSourceResiduals table) auxiliary residuals order d n row lane
    (by omega) hr (nonzero () (by simp) auxiliary) sourceDegrees auxDegrees sent claim initialZero
    (firstTablePCSContinuations sample secondRows layout earlierRounds queries)
    (fun p x=>accept p x.1 x.2) (by
      intro p hp x hx accepted
      obtain ⟨q,hq,r,hr,rfl⟩ : ∃ q∈decodedLocalPrefixes sample secondRows,
        ∃ r∈twoTablePCSContinuations sample layout earlierRounds queries,(q,r)=x := by
          simpa only [firstTablePCSContinuations,List.mem_flatMap,List.mem_map] using hx
      exact checks p hp q hq r hr accepted) repair _
    (fun p=>count (firstTablePCSContinuations sample secondRows layout earlierRounds queries)
      (fun x=>event p x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2)) wrongTerminal (by
        simpa only [firstTablePCSContinuations,count,List.countP_flatMap,List.countP_map,Function.comp_def] using pcs)
  simpa only [firstTablePCSContinuations,count,List.countP_flatMap,List.countP_map,Function.comp_def] using bound

end NearCompression
