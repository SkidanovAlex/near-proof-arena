import NearCompression.FunctionalBatchRepresentative

/-! Reconstruct one original lane tuple from compressed polynomial rows, using
D distinct COMMON agreement points. This does not assert individual source
proximity. The row index can include all obligations and Boolean cube slots.
The interpolants depend only on those fixed inputs and selected points, not
on any later PCS challenge. Earlier GKR randomness is not erased by this fact. -/
namespace NearCompression
open Lean.Grind ZkFormal.Algebra ArenaCore.Security
variable {K Row : Type} [Field K]

noncomputable def interpolateSourceLanes (points : List K) (sources : List (K → K)) : List (Poly K) := by
  classical
  exact sources.map (fun source => Poly.lagrange points source)

theorem interpolate_source_shape (points : List K) (sources : List (K → K)) :
    (interpolateSourceLanes points sources).length=sources.length := by
  classical
  simp [interpolateSourceLanes]

theorem interpolate_source_degree (points : List K) (sources : List (K → K))
    (p : Poly K) (hp : p∈interpolateSourceLanes points sources) : p.DegLt points.length := by
  classical
  obtain ⟨source,hs,rfl⟩ := List.mem_map.mp hp
  exact (PolyRoots.lagrange_of polyEval polyDeg K points source).1

theorem interpolate_source_values (points : List K) (distinct : points.Nodup)
    (sources : List (K → K)) (x : K) (hx : x∈points) :
    (interpolateSourceLanes points sources).map (fun p => p.eval x)=sources.map (fun source => source x) := by
  classical
  simp only [interpolateSourceLanes,List.map_map,Function.comp_def]
  apply List.map_congr_left
  intro source hs
  exact (PolyRoots.lagrange_of polyEval polyDeg K points source).2 distinct x hx

/-- SAME interpolation points and original lane tuple for EVERY compressed row.
A row can be any externally fixed coefficient vector, including all obligations
and every Boolean coefficient index of their weight tables. -/
theorem common_points_reconstruct_rows (points : List K) (distinct : points.Nodup)
    (sources : List (K → K)) (coefficients : Row → List K) (decoded : Row → Poly K)
    (D : Nat) (size : points.length=D)
    (degrees : ∀ row,(decoded row).DegLt D)
    (agreement : ∀ x∈points,∀ row,weightedVirtualOracle (coefficients row) sources x=(decoded row).eval x) :
    ∀ row i,(weightedLanePolynomial (coefficients row) (interpolateSourceLanes points sources)).coeff i=
      (decoded row).coeff i := by
  classical
  intro row
  let p := weightedLanePolynomial (coefficients row) (interpolateSourceLanes points sources)
  have degreeP : p.DegLt D := weighted_lane_degree _ _ D (by
    intro q hq
    have h := interpolate_source_degree points sources q hq
    simpa [size] using h)
  have zero : (p-decoded row).IsZero := by
    apply PolyRoots.eqZeroOfRoots_of polyEval polyDeg quotFacts isZeroEval K
      (p-decoded row) D points (Poly.degLt_sub degreeP (degrees row)) distinct
    · omega
    · intro x hx
      have equal : p.eval x=(decoded row).eval x := by
        rw [weighted_lane_eval,interpolate_source_values points distinct sources x hx]
        exact agreement x hx row
      rw [Poly.eval_sub,equal]
      grind
  intro i
  have equal := zero i
  rw [Poly.coeff_sub] at equal
  grind

/-- Choose a shared D-point subset from an actual finite agreement count.
Unweighted count is explicit: a weighted threshold cannot be substituted here
without separately converting it using a cap on the weights. -/
theorem shared_lane_reconstruction (domain : List K) (distinct : domain.Nodup)
    (sources : List (K → K)) (coefficients : Row → List K) (decoded : Row → Poly K)
    (D : Nat) (degrees : ∀ row,(decoded row).DegLt D)
    (enough : D≤count domain (fun x => ∀ row,
      weightedVirtualOracle (coefficients row) sources x=(decoded row).eval x)) :
    ∃ points : List K,points.Nodup ∧ points.length=D ∧ (∀ x∈points,x∈domain) ∧
      (∀ p∈interpolateSourceLanes points sources,p.DegLt D) ∧
      ∀ row i,(weightedLanePolynomial (coefficients row) (interpolateSourceLanes points sources)).coeff i=
        (decoded row).coeff i := by
  classical
  let good := domain.filter (fun x => decide (∀ row,
    weightedVirtualOracle (coefficients row) sources x=(decoded row).eval x))
  let points := good.take D
  have goodLength : good.length=count domain (fun x => ∀ row,
      weightedVirtualOracle (coefficients row) sources x=(decoded row).eval x) :=
    List.countP_eq_length_filter.symm
  have size : points.length=D := by
    simp only [points,List.length_take]
    omega
  have unique : points.Nodup := List.Sublist.nodup (List.take_sublist D good)
    (List.Sublist.nodup List.filter_sublist distinct)
  have member : ∀ x∈points,x∈good := fun x hx => List.mem_of_mem_take hx
  have agree : ∀ x∈points,∀ row,weightedVirtualOracle (coefficients row) sources x=(decoded row).eval x := by
    intro x hx
    exact @_root_.of_decide_eq_true _ (Classical.propDecidable _) (List.mem_filter.mp (member x hx)).2
  refine ⟨points,unique,size,?_,?_,common_points_reconstruct_rows points unique sources coefficients decoded D size degrees agree⟩
  · intro x hx
    exact (List.mem_filter.mp (member x hx)).1
  · intro p hp
    simpa [size] using interpolate_source_degree points sources p hp

omit [Field K] in
/-- Exact cap conversion sufficient for interpolation: T > B*(D-1)
forces at least D distinct agreeing domain entries. The caller separately
supplies domain.Nodup before selecting interpolation points. -/
theorem weighted_mass_implies_enough_points (domain : List K) (weight : K → Nat)
    (event : K → Prop) (B D T : Nat)
    (bounded : ∀ x∈domain,weight x≤B)
    (mass : T≤consistencyMass domain weight event) (threshold : B*(D-1)<T) :
    D≤count domain event := by
  classical
  have cap : consistencyMass domain weight event≤B*count domain event := by
    clear mass threshold
    induction domain with
    | nil => simp [consistencyMass,count]
    | cons x xs ih =>
      have head := bounded x (by simp)
      have tail := ih (fun y hy => bounded y (by simp [hy]))
      simp only [consistencyMass,count,List.map_cons,List.sum_cons,List.countP_cons] at tail ⊢
      by_cases h : event x <;> simp_all <;> grind
  apply Nat.le_of_not_gt
  intro few
  have countBound : count domain event≤D-1 := by omega
  have scaled := Nat.mul_le_mul_left B countBound
  omega

/-- Composed weighted-to-distinct-points reconstruction. The witness points
are selected once and interpolate ALL original lanes and compressed rows. -/
theorem weighted_shared_lane_reconstruction (domain : List K) (distinct : domain.Nodup)
    (weight : K → Nat) (B D T : Nat) (bounded : ∀ x∈domain,weight x≤B)
    (sources : List (K → K)) (coefficients : Row → List K) (decoded : Row → Poly K)
    (degrees : ∀ row,(decoded row).DegLt D)
    (mass : T≤consistencyMass domain weight (fun x => ∀ row,
      weightedVirtualOracle (coefficients row) sources x=(decoded row).eval x))
    (threshold : B*(D-1)<T) :
    ∃ points : List K,points.Nodup ∧ points.length=D ∧ (∀ x∈points,x∈domain) ∧
      (∀ p∈interpolateSourceLanes points sources,p.DegLt D) ∧
      ∀ row i,(weightedLanePolynomial (coefficients row) (interpolateSourceLanes points sources)).coeff i=
        (decoded row).coeff i := by
  apply shared_lane_reconstruction domain distinct sources coefficients decoded D degrees
  exact weighted_mass_implies_enough_points domain weight _ B D T bounded mass threshold

end NearCompression
