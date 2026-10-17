import NearCompression.FixedSourceLocalBudget
namespace NearCompression
open Lean.Grind ZkFormal.Near ZkFormal.Udr ZkFormal.V2 ZkFormal.Air ZkFormal.Algebra ArenaCore.Security

/-- The second table's invalid-source bound uses the full first-table prefix
as earlier randomness. Its residual error sum is discharged by the existing
joint two-table PCS lifting theorem, never by a fixed-rowpoint estimate.
The concrete PCS fiber bound and wrong-terminal repair remain explicit. -/
theorem second_table_fixed_source_pcs_budget
    (sample : List Fp8) (distinct : sample.Nodup) (layout : GKRJointLayout) (firstRows : Nat) (earlierRounds : List Nat) (queries : Nat)
    (table : Table) (sourceTrace : Trace Fp) (sourceWidth : Nat → Nat) (t n : Nat)
    (rowShape : layout.rowCoordinates=firstRows+(n+1))
    (log : sourceTrace.log t=n+1) (upper : sourceTrace.log t≤table.maxLog)
    (pub : List Fp) (invalid : ¬TableLocal table sourceTrace t pub)
    (bounds : ∀ e∈tableSourceResiduals table,e.colBound≤sourceWidth t)
    (traces : LocalChallengePrefix Fp8 → Trace Fp8)
    (logs : ∀ a∈decodedLocalPrefixes sample firstRows,(traces a).log=sourceTrace.log)
    (fixed : ∀ a∈decodedLocalPrefixes sample firstRows,∀ s row column,column<sourceWidth s →
      (traces a).cell s row column=Fp8.ofBase (sourceTrace.cell s row column)) (auxiliary : LocalChallengePrefix Fp8 → List (BusProgramFormula Fp8))
    (auxiliaryLength : Nat) (auxiliaryShape : ∀ a∈decodedLocalPrefixes sample firstRows,(auxiliary a).length=auxiliaryLength)
    (residuals : LocalChallengePrefix Fp8 → List (AIRBusResidual Fp8 × Nat))
    (order : ∀ a∈decodedLocalPrefixes sample firstRows,(residuals a).map Prod.fst=(tableSourceResiduals table).map Sum.inl++(auxiliary a).map Sum.inr)
    (d : Nat)
    (sourceDegrees : ∀ e∈tableSourceResiduals table,e.degree≤d) (auxDegrees : ∀ a∈decodedLocalPrefixes sample firstRows,∀ e∈auxiliary a,busFormulaDegree e≤d)
    (sent : LocalChallengePrefix Fp8 → Fp8 → List Fp8 → List Fp8 → Poly Fp8) (claim : LocalChallengePrefix Fp8 → Fp8 → List Fp8 → List Fp8 → Fp8)
    (initialZero : ∀ a∈decodedLocalPrefixes sample firstRows,∀ mixing tau,claim a mixing tau []=0)
    (accept : LocalChallengePrefix Fp8 → LocalChallengePrefix Fp8 → (Fp8 × (List (GKRBlock Fp8) × (List Fp8 × (List Fp8 × List Nat)))) → Prop)
    (checks : ∀ a∈decodedLocalPrefixes sample firstRows,∀ p∈decodedLocalPrefixes sample (n+1),∀ r∈(twoTablePCSContinuations sample layout earlierRounds queries),
      accept a p r → decodedLocalChecks d (sent a) (claim a) p)
    (repair budget : Nat)
    (event : LocalChallengePrefix Fp8 → LocalChallengePrefix Fp8 → Fp8 →
      List (GKRBlock Fp8) → List Fp8 → List Fp8 → List Nat → Prop)
    (wrongTerminal : ∀ a∈decodedLocalPrefixes sample firstRows,∀ p∈decodedLocalPrefixes sample (n+1),
      ¬decodedLocalTerminalCorrect (n+1) (fun column row=>(traces a).cell t row column) (pub.map Fp8.ofBase) (residuals a) (claim a) p →
      count (twoTablePCSContinuations sample layout earlierRounds queries) (accept a p)*sample.length≤repair+(fun a p => count (twoTablePCSContinuations sample layout earlierRounds queries) (fun r => event a p r.1 r.2.1 r.2.2.1 r.2.2.2.1 r.2.2.2.2)) a p*sample.length)
    (joint : ∀ first∈airLocalInitialChallenges sample firstRows,
      ∀ second∈airLocalInitialChallenges sample (n+1),∀ rho∈sample,
      ∀ earlier∈gkrChallengePaths sample earlierRounds,
      count (gkrConcretePCSSamples sample layout queries) (fun item =>
        event (first,item.1.take firstRows) (second,item.1.drop firstRows) rho
          (earlier++[item.2.1]) item.2.2.1 item.2.2.2.1 item.2.2.2.2)*sample.length≤budget) :
    count ((decodedLocalPrefixes sample firstRows).flatMap (fun a => (decodedLocalPrefixes sample (n+1)).flatMap (fun p =>
      (twoTablePCSContinuations sample layout earlierRounds queries).map (fun r => (a,p,r))))) (fun x => accept x.1 x.2.1 x.2.2)*sample.length≤
      (decodedLocalPrefixes sample firstRows).length*
        ((((tableSourceResiduals table).length+auxiliaryLength-1+(n+1)+(d+1)*(n+1))*sample.length^(2*(n+1)+1))*(twoTablePCSContinuations sample layout earlierRounds queries).length+
          (decodedLocalPrefixes sample (n+1)).length*repair)+((airLocalInitialChallenges sample firstRows).length*((airLocalInitialChallenges sample (n+1)).length*(sample.length*((gkrChallengePaths sample earlierRounds).length*budget)))) := by
  have pcs := two_table_gkr_pcs_joint_budget sample layout firstRows (n+1) rowShape
    earlierRounds queries event sample.length budget joint
  apply fixed_source_invalid_local_budget sample distinct (decodedLocalPrefixes sample firstRows)
    table sourceTrace sourceWidth t n log upper pub invalid bounds traces logs fixed
    auxiliary auxiliaryLength auxiliaryShape residuals order d sourceDegrees auxDegrees sent claim initialZero
    (twoTablePCSContinuations sample layout earlierRounds queries) accept checks repair _
    (fun a p => count (twoTablePCSContinuations sample layout earlierRounds queries)
      (fun r => event a p r.1 r.2.1 r.2.2.1 r.2.2.2.1 r.2.2.2.2)) wrongTerminal
  rw [earlier_local_error_count]
  exact pcs

end NearCompression
