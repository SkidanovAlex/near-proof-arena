import NearCompression.RecoveredGKRTable
import NearCompression.JointRepresentativeNearCase
namespace NearCompression
open Lean.Grind ZkFormal.Algebra ArenaCore.Security
variable {K : Type} [Field K]

def liftedHeterogeneousWeights (C m : Nat) (metadata : List GKRSourceLane)
    (rowpoints : GKRSourceLane → Nat → K) (left right : Nat → K) (gamma : K) : List (Nat → K) :=
  metadata.map (fun lane => repeatLowWeights (C-(lane.rowLog+lane.packingLog))
    (heterogeneousLaneWeight m lane (rowpoints lane) left right gamma))

def recoveredLanePrivateClaim (C m : Nat) (lane : GKRSourceLane) (polynomial : Poly K)
    (rowpoint left right : Nat → K) (gamma : K) : K :=
  let decoded := recoverProjectedPolynomial (2^(C-(lane.rowLog+lane.packingLog)))
    (2^(lane.rowLog+lane.packingLog)) polynomial
  let table := recoveredGKRTable lane.rowLog lane.packingLog decoded
  cubeSum lane.packingLog (fun col =>
    heterogeneousColumnWeight m lane false left right gamma col*
      genericRowMLE lane.rowLog (fun row => table row col) rowpoint+
    heterogeneousColumnWeight m lane true left right gamma col*
      genericRowNextMLE lane.rowLog (fun row => table row col) rowpoint)

/-- One fixed decoded table per packed lane; rowpoints/GKR weights only
select current/next functionals of these tables. Invalid padded columns are
masked by the actual heterogeneous column weights. -/
def recoveredHeterogeneousClaim (C m : Nat) (entries : List (GKRSourceLane × Poly K))
    (rowpoints : GKRSourceLane → Nat → K) (left right : Nat → K) (gamma : K) : K :=
  (entries.map (fun entry => recoveredLanePrivateClaim C m entry.1 entry.2 (rowpoints entry.1) left right gamma)).sum

private theorem sum_add (xs : List Nat) (f g : Nat → K) :
    (xs.map (fun i => f i+g i)).sum=(xs.map f).sum+(xs.map g).sum := by
  induction xs with
  | nil => simp; grind
  | cons x xs ih => simp only [List.map_cons,List.sum_cons,ih]; grind

private theorem functional_cons (n : Nat) (w : Nat → K) (ws : List (Nat → K))
    (p : Poly K) (ps : List (Poly K)) :
    coefficientTableFunctional n (w::ws) (p::ps)=
      coefficientTableFunctional n [w] [p]+coefficientTableFunctional n ws ps := by
  unfold coefficientTableFunctional
  simp only [List.map_cons,List.map_nil,weightedLaneValues]
  rw [sum_add]
  congr 1
  congr 1
  apply List.map_congr_left
  intro i hi
  grind

private theorem functional_nil (n : Nat) :
    coefficientTableFunctional n ([] : List (Nat → K)) []=0 := by
  unfold coefficientTableFunctional
  simp only [List.map_nil,weightedLaneValues]
  induction List.range (2^n) with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons,List.sum_cons,ih]; grind

/-- Exact complete heterogeneous opening functional on the decoded tuple,
including source/aux slot offsets, arbitrary rowpoints and partial lanes.
The sparse image comes from recovery; no equality with arbitrary committed
source values is inferred from proximity. -/
theorem recovered_heterogeneous_functional (C m : Nat) (entries : List (GKRSourceLane × Poly K))
    (fits : ∀ entry∈entries,entry.1.rowLog+entry.1.packingLog≤C)
    (degrees : ∀ entry∈entries,entry.2.DegLt (2^C))
    (sparse : ∀ entry∈entries,∀ i,¬2^(C-(entry.1.rowLog+entry.1.packingLog))∣i → entry.2.coeff i=0)
    (rowpoints : GKRSourceLane → Nat → K) (left right : Nat → K) (gamma : K) :
    coefficientTableFunctional C
      (liftedHeterogeneousWeights C m (entries.map Prod.fst) rowpoints left right gamma)
      (entries.map Prod.snd)=recoveredHeterogeneousClaim C m entries rowpoints left right gamma := by
  induction entries with
  | nil => exact functional_nil C
  | cons entry entries ih =>
    have bound := fits entry (by simp)
    have dim : C-(entry.1.rowLog+entry.1.packingLog)+(entry.1.rowLog+entry.1.packingLog)=C := by omega
    have degree : entry.2.DegLt (2^(C-(entry.1.rowLog+entry.1.packingLog))*2^(entry.1.rowLog+entry.1.packingLog)) := by
      rw [←Nat.pow_add,dim]
      exact degrees entry (by simp)
    have head := recovered_lifted_heterogeneous_functional (C-(entry.1.rowLog+entry.1.packingLog)) m
      entry.1 entry.2 degree (sparse entry (by simp)) (rowpoints entry.1) left right gamma
    rw [dim] at head
    change coefficientTableFunctional C
      ((repeatLowWeights (C-(entry.1.rowLog+entry.1.packingLog))
        (heterogeneousLaneWeight m entry.1 (rowpoints entry.1) left right gamma))::
        liftedHeterogeneousWeights C m (entries.map Prod.fst) rowpoints left right gamma)
      (entry.2::entries.map Prod.snd)=_
    rw [functional_cons,head,ih (by intro e he; exact fits e (by simp [he]))
      (by intro e he; exact degrees e (by simp [he]))
      (by intro e he; exact sparse e (by simp [he]))]
    rfl

/-- Wrong whole private-input claim about the SAME decoded heterogeneous
tuple reduces to the checked weighted-sumcheck residual-candidate bound.
The sparse certificate is the output of projected-source recovery; it is
explicit here so the theorem cannot assume source honesty implicitly. -/
theorem recovered_heterogeneous_near_count (layout : GKRJointLayout)
    (entries : List (GKRSourceLane × Poly K))
    (valid : ∀ lane∈entries.map Prod.fst,lane.WellFormed layout)
    (geometry : CanonicalLaneSelectors layout (entries.map Prod.fst))
    (domain sample : List K) (domainDistinct : domain.Nodup) (sampleDistinct : sample.Nodup)
    (T : Nat) (sources : List (K → K)) (sourceShape : sources.length=entries.length)
    (representative : JointBetaRepresentative domain (fun _ => 1) (heterogeneousJointDimension layout)
      (2^layout.commonLog) T ((entries.map Prod.fst).map (heterogeneousJointBeta layout)) sources (entries.map Prod.snd))
    (sparse : ∀ entry∈entries,∀ i,¬2^(layout.commonLog-(entry.1.rowLog+entry.1.packingLog))∣i → entry.2.coeff i=0)
    (rowpoints : GKRSourceLane → Nat → K) (left right : Nat → K) (gamma : K)
    (threshold : T≤domain.length) (separation : 2*(domain.length-T)+2^layout.commonLog≤domain.length)
    (sent : List K → Poly K) (claim : List K → K)
    (wrong : claim []≠recoveredHeterogeneousClaim layout.commonLog layout.inputLog entries rowpoints left right gamma) :
    let tables := liftedHeterogeneousWeights layout.commonLog layout.inputLog (entries.map Prod.fst) rowpoints left right gamma
    count (uniformTuples sample layout.commonLog) (fun path => weightedSumcheckChecks sent claim [] path ∧
      ∃ candidate : Poly K,candidate.DegLt (2^layout.commonLog) ∧
        scalarRSResidual (equalityWeights path) candidate=claim path ∧
        T≤count domain (fun x => weightedVirtualOracle
          (functionalBatchCoefficients layout.commonLog tables (fun i => path.getD i 0)) sources x=candidate.eval x)) *sample.length≤
      (2*layout.commonLog)*sample.length^layout.commonLog := by
  dsimp only
  apply joint_representative_near_sumcheck_count layout (entries.map Prod.fst) valid geometry domain sample
    domainDistinct sampleDistinct (2^layout.commonLog) T layout.commonLog sources (entries.map Prod.snd)
    (by simpa using sourceShape) representative
    (liftedHeterogeneousWeights layout.commonLog layout.inputLog (entries.map Prod.fst) rowpoints left right gamma)
    (by simp [liftedHeterogeneousWeights]) threshold separation sent claim
  rw [recovered_heterogeneous_functional layout.commonLog layout.inputLog entries
    (by intro entry he; exact (valid entry.1 (List.mem_map.mpr ⟨entry,he,rfl⟩)).2.1)
    (by intro entry he; exact representative.2.1 entry.2 (List.mem_map.mpr ⟨entry,he,rfl⟩)) sparse]
  exact wrong
end NearCompression
