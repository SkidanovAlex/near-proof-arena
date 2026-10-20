import NearCompression.FixedJointSourceRepresentative
import NearCompression.ProjectedRSDomain
import NearCompression.GKRTerminalNearCase
namespace NearCompression
open Lean.Grind ZkFormal.Algebra ArenaCore.Security
variable {K : Type} [Field K]

/-- Sparse image is derived for every lane from the common representative,
actual source projection, and natural-domain geometry; it is not a caller
certificate for each individually selected polynomial. -/
theorem joint_source_entries_sparse (layout : GKRJointLayout) (metadata : List GKRSourceLane)
    (valid : ∀ lane∈metadata,lane.WellFormed layout)
    (geometry : CanonicalLaneSelectors layout metadata)
    (omega : K) (rootOrder : ∀ j,omega^j=1 ↔ 4*2^layout.commonLog∣j)
    (T : Nat) (sources : List (K→K)) (polys : List (Poly K))
    (sourceShape : sources.length=metadata.length)
    (representative : JointBetaRepresentative (naturalRSDomain omega (4*2^layout.commonLog)) (fun _=>1)
      (heterogeneousJointDimension layout) (2^layout.commonLog) T
      (metadata.map (heterogeneousJointBeta layout)) sources polys)
    (original : GKRSourceLane→K→K)
    (projection : ∀ i,∀ hi : i<metadata.length,∀ x,
      (sources[i]'(by omega)) x=original metadata[i] (x^(2^(layout.commonLog-(metadata[i].rowLog+metadata[i].packingLog)))))
    (separation : 2*(4*2^layout.commonLog-T)+2^layout.commonLog≤4*2^layout.commonLog) :
    ∀ entry∈metadata.zip polys,∀ j,
      ¬2^(layout.commonLog-(entry.1.rowLog+entry.1.packingLog))∣j → entry.2.coeff j=0 := by
  have shape : polys.length=metadata.length := representative.1.trans sourceShape
  intro entry he j absent
  obtain ⟨i,hi,same⟩ := List.mem_iff_getElem.mp he
  rw [List.getElem_zip] at same
  have bound : i<metadata.length := List.lt_length_left_of_zip hi
  subst entry
  have fits := (valid metadata[i] (List.getElem_mem bound)).2.1
  let L := 2^(layout.commonLog-(metadata[i].rowLog+metadata[i].packingLog))
  let d := 2^(metadata[i].rowLog+metadata[i].packingLog)
  have product : L*d=2^layout.commonLog := by
    dsimp [L,d]
    rw [←Nat.pow_add,Nat.sub_add_cancel fits]
  have domain : L*(4*d)=4*2^layout.commonLog := by rw [←product];simp [Nat.mul_assoc,Nat.mul_comm]
  have recovery := natural_rs_joint_projected_recovery layout metadata valid geometry L d T
    (Nat.two_pow_pos _) (Nat.two_pow_pos _) omega (by simpa only [domain] using rootOrder)
    sources polys sourceShape shape (by simpa only [domain,product] using representative) i bound
    (original metadata[i]) (projection i bound) (by rw [domain,product];omega)
  have equality := recovery.2 j
  simp only [show ¬L∣j from absent,ite_false] at equality
  exact equality

/-- One prechallenge mathematical choice supplies the decoded GKR input and
all PCS near-case obligations. Sparse image is derived from actual source
projection. The event remains the explicit close residual-candidate event,
NOT executable PCS acceptance; no Fiat-Shamir sampling claim is made. -/
theorem chosen_gkr_terminal_near_count (layout : GKRJointLayout) (metadata : List GKRSourceLane)
    (valid : ∀ lane∈metadata,lane.WellFormed layout)
    (geometry : CanonicalLaneSelectors layout metadata)
    (omega : K) (rootOrder : ∀ j,omega^j=1 ↔ 4*2^layout.commonLog∣j)
    (sample : List K) (sampleDistinct : sample.Nodup)
    (T : Nat) (sources : List (K→K)) (sourceShape : sources.length=metadata.length)
    (existsRep : ∃ polys,JointBetaRepresentative (naturalRSDomain omega (4*2^layout.commonLog)) (fun _=>1)
      (heterogeneousJointDimension layout) (2^layout.commonLog) T
      (metadata.map (heterogeneousJointBeta layout)) sources polys)
    (original : GKRSourceLane→K→K)
    (projection : ∀ i,∀ hi : i<metadata.length,∀ x,
      (sources[i]'(by omega)) x=original metadata[i] (x^(2^(layout.commonLog-(metadata[i].rowLog+metadata[i].packingLog)))))
    (threshold : T≤4*2^layout.commonLog)
    (separation : 2*(4*2^layout.commonLog-T)+2^layout.commonLog≤4*2^layout.commonLog)
    (rowpoints : GKRSourceLane→Nat→K) (left right : Nat→K) (gamma : K)
    (sent : List K→Poly K) (claim : List K→K)
    (constants : List (Nat×K)) (bounds : ∀ entry∈constants,entry.1<2^layout.inputLog)
    (terminalClaim : K)
    (initial : claim []=gkrRemoveConstants layout.inputLog left right gamma constants terminalClaim) :
    let polys := chosenJointSourceRepresentative layout metadata (naturalRSDomain omega (4*2^layout.commonLog))
      (2^layout.commonLog) T sources
    let entries := metadata.zip polys
    let tables := liftedHeterogeneousWeights layout.commonLog layout.inputLog metadata rowpoints left right gamma
    terminalClaim≠gkrInputFunctional layout.inputLog left right gamma
      (fun i=>gkrScatter (recoveredPrivateSlots layout.commonLog entries rowpoints) i+gkrScatter constants i) →
    count (uniformTuples sample layout.commonLog) (fun path=>weightedSumcheckChecks sent claim [] path ∧
      ∃ candidate : Poly K,candidate.DegLt (2^layout.commonLog) ∧
        scalarRSResidual (equalityWeights path) candidate=claim path ∧
        T≤count (naturalRSDomain omega (4*2^layout.commonLog)) (fun x=>weightedVirtualOracle
          (functionalBatchCoefficients layout.commonLog tables (fun i=>path.getD i 0)) sources x=candidate.eval x))
      *sample.length≤(2*layout.commonLog)*sample.length^layout.commonLog := by
  let domain := naturalRSDomain omega (4*2^layout.commonLog)
  let polys := chosenJointSourceRepresentative layout metadata domain (2^layout.commonLog) T sources
  let entries := metadata.zip polys
  have representative := chosen_joint_source_representative_valid layout metadata domain
    (2^layout.commonLog) T sources existsRep
  have shape : polys.length=metadata.length := representative.1.trans sourceShape
  have firsts : entries.map Prod.fst=metadata := List.map_fst_zip (by omega)
  have seconds : entries.map Prod.snd=polys := List.map_snd_zip (by omega)
  have sparse := joint_source_entries_sparse layout metadata valid geometry omega rootOrder T sources polys
    sourceShape representative original projection separation
  dsimp only
  intro wrong
  have result := gkr_terminal_recovered_near_count layout entries (by simpa only [firsts] using valid)
    (by simpa only [firsts] using geometry) domain sample (natural_rs_distinct omega _ rootOrder) sampleDistinct
    T sources (by dsimp [entries];simp only [List.length_zip,shape,sourceShape,Nat.min_self])
    (by simpa only [firsts,seconds] using representative) sparse rowpoints left right gamma
    (by simpa [domain,naturalRSDomain] using threshold)
    (by simpa [domain,naturalRSDomain] using separation) sent claim constants bounds terminalClaim initial wrong
  simpa only [firsts] using result
end NearCompression
