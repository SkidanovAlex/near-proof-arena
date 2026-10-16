import NearCompression.TwoTableAuxiliaryBranch
namespace NearCompression
open Lean.Grind ZkFormal.Air ZkFormal.Algebra ArenaCore.Security

/-- Selected auxiliary invalidity yields the local acceptance bound with the
actual shared accepted-failure count retained. No independent numerical PCS
budget is charged per selected table or earlier history. -/
theorem selected_auxiliary_local_error_count {A R : Type}
    (sample : List Fp8) (distinct : sample.Nodup) (earlier : List A)
    (fixed : A → Trace Fp) (tr : A → Trace Fp8) (width : Nat → Nat)
    (start : Nat) (b : Bool) (publicValues : List Fp8)
    (formulas : A → Nat → List (BusProgramFormula Fp8))
    (selected : ∀ a∈earlier,twoTableAuxiliaryBranch (airExt8Trace (fixed a)) (formulas a) start=some b)
    (logs : ∀ a∈earlier,(tr a).log=(fixed a).log)
    (cells : ∀ a∈earlier,∀ t row column,column<width t →
      (tr a).cell t row column=Fp8.ofBase ((fixed a).cell t row column))
    (source : List Expr)
    (auxiliaryLength : Nat) (auxiliaryShape : ∀ a∈earlier,(formulas a (start+(if b then 1 else 0))).length=auxiliaryLength)
    (residuals : A → List (AIRBusResidual Fp8 × Nat))
    (order : ∀ a∈earlier,(residuals a).map Prod.fst=source.map Sum.inl++(formulas a (start+(if b then 1 else 0))).map Sum.inr)
    (d n : Nat) (positive : 0<source.length+auxiliaryLength)
    (rowLogs : ∀ a∈earlier,(tr a).log (start+(if b then 1 else 0))=n+1)
    (bounds : ∀ a∈earlier,∀ e∈formulas a (start+(if b then 1 else 0)),
      busFormulaColumnBound e≤width (start+(if b then 1 else 0)))
    (sourceDegrees : ∀ e∈source,e.degree≤d) (auxDegrees : ∀ a∈earlier,∀ e∈formulas a (start+(if b then 1 else 0)),busFormulaDegree e≤d)
    (sent : A → Fp8 → List Fp8 → List Fp8 → Poly Fp8) (claim : A → Fp8 → List Fp8 → List Fp8 → Fp8)
    (initialZero : ∀ a∈earlier,∀ mixing tau,claim a mixing tau []=0)
    (continuations : List R) (accept failure : A → LocalChallengePrefix Fp8 → R → Prop)
    (checks : ∀ a∈earlier,∀ p∈decodedLocalPrefixes sample (n+1),∀ r∈continuations,
      accept a p r → decodedLocalChecks d (sent a) (claim a) p)
    (repair : Nat)
    (wrongTerminal : ∀ a∈earlier,∀ p∈decodedLocalPrefixes sample (n+1),
      ¬decodedLocalTerminalCorrect (n+1) (fun column row=>(tr a).cell (start+(if b then 1 else 0)) row column) publicValues (residuals a) (claim a) p →
      count continuations (accept a p)*sample.length≤repair+count continuations (fun r=>accept a p r ∧ failure a p r)*sample.length)
 :
    count (earlier.flatMap (fun a => (decodedLocalPrefixes sample (n+1)).flatMap (fun p =>
      continuations.map (fun r => (a,p,r))))) (fun x => accept x.1 x.2.1 x.2.2)*sample.length≤
      earlier.length*
        (((source.length+auxiliaryLength-1+(n+1)+(d+1)*(n+1))*sample.length^(2*(n+1)+1))*continuations.length+
          (decodedLocalPrefixes sample (n+1)).length*repair)+count (earlier.flatMap (fun a => (decodedLocalPrefixes sample (n+1)).flatMap (fun p =>
            continuations.map (fun r => (a,p,r)))))
            (fun x=>accept x.1 x.2.1 x.2.2 ∧ failure x.1 x.2.1 x.2.2)*sample.length := by
  have invalidRows : ∀ a∈earlier,¬∀ row,row<2^(n+1) → ∀ lane,
      (airCombinedRowResiduals
        (decodedTableTrace (n+1) (fun column row=>(tr a).cell (start+(if b then 1 else 0)) row column)) 0
        publicValues source (formulas a (start+(if b then 1 else 0))) row).getD lane 0=0 := by
    intro a ha zero
    have witness := selected_auxiliary_decoded_witness (fixed a) (tr a) width (logs a ha) (cells a ha)
      (formulas a) start b (selected a ha) (bounds a ha) publicValues source
    dsimp only at witness
    rw [rowLogs a ha] at witness
    obtain ⟨_,row,hr,lane,wrong⟩ := witness
    exact wrong (zero row hr lane)
  apply decoded_adaptive_invalid_rows_budget sample distinct earlier
    (fun a column row=>(tr a).cell (start+(if b then 1 else 0)) row column) publicValues source
    (fun a=>formulas a (start+(if b then 1 else 0))) auxiliaryLength auxiliaryShape residuals order
    d n positive invalidRows sourceDegrees auxDegrees sent claim initialZero continuations accept checks
    repair _ (fun a p=>count continuations (fun r=>accept a p r ∧ failure a p r)) wrongTerminal
  rw [earlier_local_error_count]
  exact Nat.le_refl _

end NearCompression
