import NearCompression.IndexedFoldExtraction
import NearCompression.WeightedUniqueExtraction
import NearCompression.FiniteIndexTransport

/-! Discharges the actual IndexedFoldExtraction contract in the explicit
stricter weighted unique-decoding regime. No extraction hypothesis remains. -/
namespace NearCompression
open Lean.Grind ZkFormal.Algebra ArenaCore.Security
variable {K : Type} [Field K]

theorem indexed_unique_extraction (sample : List K) (sampleDistinct : sample.Nodup)
    (N D T B : Nat) (weight : Nat → Nat) (source : Nat → K)
    (root childRoot : K) (weights : List K) (w0 w1 : K) (sent : Poly K)
    (pointInjective : ∀ i<N,∀ j<N,childRoot^i=childRoot^j → i=j)
    (bounded : ∀ i<N,weight i+weight (i+N)≤B)
    (sentDegree : sent.DegLt 3)
    (separation : 2*((List.range N).map (fun i => weight i+weight (i+N))).sum+B*(D-1)<3*T) :
    IndexedFoldExtraction sample (max N 2) N D T weight source root childRoot weights w0 w1 sent := by
  classical
  intro many
  let point : Nat → K := fun i => childRoot^i
  let index := finitePointIndex N point
  let domain := (List.range N).map point
  let projected : Nat → Nat := fun i => weight i+weight (i+N)
  let evenSource : K → K := fun x => (rsPairDecode (root^(index x)) (source (index x),source (index x+N))).1
  let oddSource : K → K := fun x => (rsPairDecode (root^(index x)) (source (index x),source (index x+N))).2
  have transport (event : Nat → K → Prop) :
      consistencyMass domain (fun x => projected (index x)) (fun x => event (index x) x)=
      consistencyMass (List.range N) projected (fun i => event i (point i)) :=
    finite_index_mass_transport N point pointInjective projected event
  have fieldBound : ∀ x∈domain,projected (index x)≤B := by
    intro x hx
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hx
    change projected (finitePointIndex N point (point i))≤B
    rw [finite_point_index_inverse N point pointInjective i (List.mem_range.mp hi)]
    exact bounded i (List.mem_range.mp hi)
  have fieldSeparation : 2*(domain.map (fun x => projected (index x))).sum+B*(D-1)<3*T := by
    rw [finite_index_weight_sum N point pointInjective projected]
    exact separation
  have successTransfer (r : K)
      (success : indexedFoldSuccess N D T weight source root childRoot weights w0 w1 sent r) :
      weightedCurveSuccess domain (fun x => projected (index x)) evenSource oddSource D T weights w0 w1 sent r := by
    obtain ⟨p,degree,agree,residual⟩ := success
    refine ⟨p,degree,?_,residual⟩
    change T≤consistencyMass domain (fun x => projected (index x))
      (fun x => p.eval x=(1-r)*(rsPairDecode (root^(index x)) (source (index x),source (index x+N))).1+
        r*(rsPairDecode (root^(index x)) (source (index x),source (index x+N))).2)
    rw [transport (fun i x => p.eval x=(1-r)*(rsPairDecode (root^i) (source i,source (i+N))).1+
      r*(rsPairDecode (root^i) (source i,source (i+N))).2)]
    apply Nat.le_trans agree
    apply consistency_mass_mono
    intro i hi eq
    exact eq.symm
  have fieldMany : max domain.length 2<count sample
      (weightedCurveSuccess domain (fun x => projected (index x)) evenSource oddSource D T weights w0 w1 sent) := by
    have subset : count sample (indexedFoldSuccess N D T weight source root childRoot weights w0 w1 sent)≤
        count sample (weightedCurveSuccess domain (fun x => projected (index x)) evenSource oddSource D T weights w0 w1 sent) := by
      apply count_mono
      exact successTransfer
    have length : domain.length=N := by simp [domain]
    rw [length]
    omega
  obtain ⟨even,odd,de,do_,agree,identity⟩ := weighted_unique_extraction_count domain sample
    (finite_point_domain_nodup N point pointInjective) sampleDistinct
    (fun x => projected (index x)) B D T fieldBound evenSource oddSource weights w0 w1 sent
    sentDegree fieldSeparation fieldMany
  refine ⟨even,odd,de,do_,?_,identity⟩
  change T≤consistencyMass domain (fun x => projected (index x))
    (fun x => (rsPairDecode (root^(index x)) (source (index x),source (index x+N))).1=even.eval x ∧
      (rsPairDecode (root^(index x)) (source (index x),source (index x+N))).2=odd.eval x) at agree
  rw [transport (fun i x => (rsPairDecode (root^i) (source i,source (i+N))).1=even.eval x ∧
    (rsPairDecode (root^i) (source i,source (i+N))).2=odd.eval x)] at agree
  apply Nat.le_trans agree
  apply consistency_mass_mono
  intro i hi h
  exact Prod.ext h.1 h.2

/-- The formerly conditional per-round concentration bad count now has a
proved max(N,2) bound under explicit finite-domain and separation certificates. -/
theorem indexed_unique_bad_count (sample : List K) (sampleDistinct : sample.Nodup)
    (N D T B : Nat) (weight : Nat → Nat) (source : Nat → K)
    (root childRoot : K) (weights : List K) (w0 w1 : K) (sent : Poly K)
    (pointInjective : ∀ i<N,∀ j<N,childRoot^i=childRoot^j → i=j)
    (bounded : ∀ i<N,weight i+weight (i+N)≤B)
    (sentDegree : sent.DegLt 3)
    (separation : 2*((List.range N).map (fun i => weight i+weight (i+N))).sum+B*(D-1)<3*T) :
    count sample (indexedFoldBad N D T weight source root childRoot weights w0 w1 sent)≤max N 2 :=
  indexed_fold_bad_count sample (max N 2) N D T weight source root childRoot weights w0 w1 sent
    (indexed_unique_extraction sample sampleDistinct N D T B weight source root childRoot weights
      w0 w1 sent pointInjective bounded sentDegree separation)

end NearCompression
