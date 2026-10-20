import NearCompression.CloseFamilySumcheck

/-! Finite interactive reduction for fixed coefficient weight tables. The
statement is functional representability, not a pre-GKR AIR witness claim.
No commitment binding or Fiat–Shamir theorem is assumed or concluded. -/
namespace NearCompression
open Lean.Grind ZkFormal.Algebra ArenaCore.Security
variable {K : Type} [Field K]

omit [Field K] in
private theorem unit_mass_count (domain : List K) (event : K → Prop) :
    consistencyMass domain (fun _ => 1) event=count domain event := by
  classical
  induction domain with
  | nil => simp [consistencyMass,count]
  | cons x xs ih =>
    simp only [consistencyMass,List.map_cons,List.sum_cons] at *
    simp only [count,List.countP_cons] at *
    by_cases h : event x <;> simp [h] at * <;> omega

omit [Field K] in
private theorem unit_mass_total (domain : List K) : (domain.map (fun _ => 1)).sum=domain.length := by
  induction domain with
  | nil => rfl
  | cons x xs ih => simp [ih,Nat.add_comm]

/-- With no correct fixed functional representative, checked sumcheck paths
that admit a close scalar polynomial with the actual residual are rare. This
joins the far-source tensor extraction and close-source quadratic sumcheck
bounds without an extraction assumption. All source oracles and weight tables
are fixed before these n independent challenges. -/
theorem functional_opening_reduction_count (domain sample : List K)
    (domainDistinct : domain.Nodup) (sampleDistinct : sample.Nodup)
    (n D T : Nat) (tables : List (Nat → K)) (sources : List (K → K))
    (shape : tables.length=sources.length) (threshold : T≤domain.length)
    (interpolation : D-1<T) (extraction : 2*domain.length+(D-1)<3*T)
    (uniqueness : 2*(domain.length-T)+D≤domain.length)
    (sent : List K → Poly K) (claim : List K → K)
    (falseStatement : ¬∃ lanes : List (Poly K),
      fixedWeightFamilyRepresentative domain (fun _ => 1) n D T (fun _ : Unit => tables) sources lanes ∧
      claim []=coefficientTableFunctional n tables lanes) :
    count (uniformTuples sample n) (fun path => weightedSumcheckChecks sent claim [] path ∧
      ∃ candidate : Poly K,candidate.DegLt D ∧
        scalarRSResidual (equalityWeights path) candidate=claim path ∧
        T≤count domain (fun x => weightedVirtualOracle
          (functionalBatchCoefficients n tables (fun i => path.getD i 0)) sources x=candidate.eval x)) *sample.length≤
      (n*max domain.length 2+2*n)*sample.length^n := by
  classical
  by_cases existsRepresentative : ∃ lanes : List (Poly K),
      fixedWeightFamilyRepresentative domain (fun _ => 1) n D T (fun _ : Unit => tables) sources lanes
  · obtain ⟨lanes,representative⟩ := existsRepresentative
    have scalar := fixed_family_scalar_representative domain (fun _ => 1) n D T
      (fun _ : Unit => tables) sources lanes (by intros; omega) (by intro; exact shape)
      threshold representative
    have wrong : claim []≠coefficientTableFunctional n tables lanes := by
      intro equal
      exact falseStatement ⟨lanes,representative,equal⟩
    have bound := close_family_sumcheck_residual_count domain sample domainDistinct sampleDistinct
      n D T tables sources lanes scalar threshold uniqueness sent claim wrong
    exact Nat.le_trans bound (Nat.mul_le_mul_right _ (by omega))
  · have far := structured_beta_far_count domain sample domainDistinct sampleDistinct (fun _ => 1)
      1 n D T (by intros; omega) (fun _ : Unit => tables) sources
      (by simpa using interpolation) (by simpa [unit_mass_total] using extraction) existsRepresentative
    have subset : count (uniformTuples sample n) (fun path => weightedSumcheckChecks sent claim [] path ∧
        ∃ candidate : Poly K,candidate.DegLt D ∧
          scalarRSResidual (equalityWeights path) candidate=claim path ∧
          T≤count domain (fun x => weightedVirtualOracle
            (functionalBatchCoefficients n tables (fun i => path.getD i 0)) sources x=candidate.eval x))≤
        count (uniformTuples sample n) (fun point => ∃ candidate : Unit → Poly K,
          (∀ obligation,(candidate obligation).DegLt D) ∧
          T≤consistencyMass domain (fun _ => 1) (fun x => ∀ obligation,
            weightedVirtualOracle (functionalBatchCoefficients n tables (fun i => point.getD i 0)) sources x=
              (candidate obligation).eval x)) := by
      unfold count
      apply List.countP_mono_left
      intro path hp accepted
      have success := @_root_.of_decide_eq_true _ (Classical.propDecidable _) accepted
      obtain ⟨checks,candidate,degree,residual,agreement⟩ := success
      apply @_root_.decide_eq_true _ (Classical.propDecidable _)
      refine ⟨fun _ => candidate,fun _ => degree,?_⟩
      simpa only [unit_mass_count,forall_const,count] using agreement
    have bound := Nat.mul_le_mul_right sample.length (Nat.le_trans subset far)
    have power : n*max domain.length 2*sample.length^(n-1)*sample.length=
        n*max domain.length 2*sample.length^n := by
      cases n with
      | zero => simp
      | succ n => simp only [Nat.add_sub_cancel,Nat.pow_succ]; ac_rfl
    rw [power] at bound
    exact Nat.le_trans bound (Nat.mul_le_mul_right _ (by omega))

end NearCompression
