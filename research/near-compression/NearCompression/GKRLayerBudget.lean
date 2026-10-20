import NearCompression.GKRLayerSoundness
namespace NearCompression
open Lean.Grind ArenaCore.Security

/-- A conditional finite sum bound with a common challenge denominator.
The per-prefix bad-event bound may vary with the complete earlier history. -/
theorem conditional_scaled_sum {A : Type} (xs : List A) (bad : A → Prop)
    (f : A → Nat) (maximum scale limit : Nat)
    (bounded : ∀ x∈xs,f x≤maximum)
    (good : ∀ x∈xs,¬bad x → f x*scale≤limit) :
    (xs.map f).sum*scale≤count xs bad*maximum*scale+xs.length*limit := by
  classical
  induction xs with
  | nil => simp [count]
  | cons x xs ih =>
    have tail := ih (fun y hy => bounded y (by simp [hy]))
      (fun y hy => good y (by simp [hy]))
    have head := bounded x (by simp)
    have hg := good x (by simp)
    simp only [List.map_cons,List.sum_cons,List.length_cons,count,List.countP_cons] at tail ⊢
    by_cases h : bad x
    · have scaled := Nat.mul_le_mul_right scale head
      simp only [h,decide_true,ite_true,Nat.add_mul,Nat.one_mul] at ⊢
      omega
    · have scaled := hg h
      simp only [h,decide_false,Bool.false_eq_true,ite_false,Nat.add_zero,Nat.add_mul,Nat.one_mul] at ⊢
      omega

/-- Exact nested Cartesian count for two equal-length axes followed by one
fresh challenge. No division, independence approximation or nonadaptive
message assumption is hidden here. -/
theorem two_axis_fresh_budget {A B C : Type} (left : List A) (right : List B) (fresh : List C)
    (badLeft : A → Prop) (badRight : A → B → Prop) (accept : A → B → C → Prop)
    (scale axisMass error : Nat)
    (leftSize : left.length=axisMass) (rightSize : right.length=axisMass)
    (freshSize : fresh.length=scale)
    (leftBound : count left badLeft*scale≤error*axisMass)
    (rightBound : ∀ a∈left,count right (badRight a)*scale≤error*axisMass)
    (freshBound : ∀ a∈left,∀ b∈right,¬badLeft a → ¬badRight a b → count fresh (accept a b)≤1) :
    (left.map (fun a => (right.map (fun b => count fresh (accept a b))).sum)).sum*scale≤
      (2*error+1)*axisMass*axisMass*scale := by
  have max (a : A) : (right.map (fun b => count fresh (accept a b))).sum≤axisMass*scale := by
    have point : ∀ b∈right,count fresh (accept a b)≤scale := by
      intro b hb
      rw [←freshSize]
      exact List.countP_le_length
    have sumBound : ∀ xs : List B,(∀ b∈xs,count fresh (accept a b)≤scale) →
        (xs.map (fun b => count fresh (accept a b))).sum≤xs.length*scale := by
      intro xs
      induction xs with
      | nil => simp
      | cons b bs ih =>
        intro point
        have h := point b (by simp)
        have t := ih (by intro c hc;exact point c (by simp [hc]))
        simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.add_mul,Nat.one_mul]
        omega
    have sum := sumBound right point
    rwa [rightSize] at sum
  have conditional (a : A) (ha : a∈left) (goodLeft : ¬badLeft a) :
      (right.map (fun b => count fresh (accept a b))).sum*scale≤(error+1)*axisMass*scale := by
    have h := conditional_scaled_sum right (badRight a) (fun b => count fresh (accept a b)) scale scale scale
      (by intro b hb;rw [←freshSize];exact List.countP_le_length)
      (by intro b hb goodRight;have e:=freshBound a ha b hb goodLeft goodRight; simpa only [Nat.one_mul] using Nat.mul_le_mul_right scale e)
    rw [rightSize] at h
    have scaled := Nat.mul_le_mul_right scale (rightBound a ha)
    grind
  have total := conditional_scaled_sum left badLeft
    (fun a => (right.map (fun b => count fresh (accept a b))).sum)
    (axisMass*scale) scale ((error+1)*axisMass*scale)
    (fun a _ => max a) conditional
  rw [leftSize] at total
  have scaled := Nat.mul_le_mul_right (axisMass*scale) leftBound
  grind
open ZkFormal.Algebra
variable {K : Type} [Field K]

/-- Full checked layer repair event. a and b depend on both axis histories,
but neither depends on the fresh gamma. -/
def gkrLayerRepair (m : Nat) (values : Nat → K) (gates : List (GKRWiringGate × K))
    (sentLeft : List K → Poly K) (claimLeft : List K → K)
    (sentRight : List K → List K → Poly K) (claimRight : List K → List K → K)
    (a b : List K → List K → K) (ru rv : List K) (gamma : K) : Prop :=
  weightedSumcheckChecks sentLeft claimLeft [] ru ∧
  claimRight ru []=claimLeft ru ∧
  weightedSumcheckChecks (sentRight ru) (claimRight ru) [] rv ∧
  gkrLayerWiring m gates (fun i => ru.getD i 0) (fun i => rv.getD i 0) (a ru rv) (b ru rv)=claimRight ru rv ∧
  a ru rv+gamma*b ru rv=gkrInputFunctional m (fun i => ru.getD i 0) (fun i => rv.getD i 0) gamma values

omit [Field K] in
private theorem path_length (sample : List K) (n : Nat) (path : List K)
    (member : path∈uniformTuples sample n) : path.length=n := by
  induction n generalizing path with
  | zero => simp [uniformTuples] at member;subst path;rfl
  | succ n ih =>
    obtain ⟨r,hr,rest⟩ := List.mem_flatMap.mp member
    obtain ⟨tail,ht,eq⟩ := List.mem_map.mp rest
    subst path
    simp only [List.length_cons,ih tail ht]

/-- Unconditional ideal layer bound (4*m+1)/|S| for m rounds per axis and
one fresh gamma. Messages adapt to past prefixes only. The event is repair of
a false claim, not acceptance of an entire cryptographic proof. -/
theorem gkr_layer_repair_count (sample : List K) (distinct : sample.Nodup) (m : Nat)
    (values : Nat → K) (gates : List (GKRWiringGate × K))
    (leftBounds : ∀ item∈gates,item.1.left<2^m)
    (rightBounds : ∀ item∈gates,item.1.right<2^m)
    (sentLeft : List K → Poly K) (claimLeft : List K → K)
    (sentRight : List K → List K → Poly K) (claimRight : List K → List K → K)
    (a b : List K → List K → K)
    (wrong : claimLeft []≠(gates.map (fun item => item.2*gkrGateValue item.1.op
      (values item.1.left) (values item.1.right))).sum) :
    ((uniformTuples sample m).map (fun ru => ((uniformTuples sample m).map (fun rv =>
      count sample (gkrLayerRepair m values gates sentLeft claimLeft sentRight claimRight a b ru rv))).sum)).sum
        *sample.length≤(4*m+1)*sample.length^(2*m+1) := by
  let badLeft := adaptivePathBad
    (gkrAdaptiveRoundBad values (gkrLeftAxisTerms values gates) sentLeft claimLeft) []
  let badRight := fun ru => adaptivePathBad
    (gkrAdaptiveRoundBad values (gkrRightAxisTerms m values (fun i => ru.getD i 0) gates)
      (sentRight ru) (claimRight ru)) []
  have fresh (ru : List K) (hu : ru∈uniformTuples sample m)
      (rv : List K) (hv : rv∈uniformTuples sample m)
      (gu : ¬badLeft ru) (gv : ¬badRight ru rv) :
      count sample (gkrLayerRepair m values gates sentLeft claimLeft sentRight claimRight a b ru rv)≤1 := by
    have lu := path_length sample m ru hu
    have lv := path_length sample m rv hv
    by_cases checked : weightedSumcheckChecks sentLeft claimLeft [] ru ∧
        claimRight ru []=claimLeft ru ∧ weightedSumcheckChecks (sentRight ru) (claimRight ru) [] rv
    · have roots := gkr_two_axes_gamma_bad_count sample distinct values gates sentLeft claimLeft
        sentRight claimRight ru rv (lv.trans lu.symm)
        (by simpa only [lu] using leftBounds) (by simpa only [lu] using rightBounds)
        wrong checked.1 checked.2.1 checked.2.2 gu
        (by simpa only [lu] using gv) (a ru rv) (b ru rv)
      rw [lu] at roots
      apply Nat.le_trans (m:=count sample (fun gamma =>
        gkrLayerWiring m gates (fun i => ru.getD i 0) (fun i => rv.getD i 0) (a ru rv) (b ru rv)=claimRight ru rv ∧
          a ru rv+gamma*b ru rv=gkrInputFunctional m (fun i => ru.getD i 0) (fun i => rv.getD i 0) gamma values)) _ roots
      apply count_mono
      intro gamma accepted
      exact accepted.2.2.2
    · have zero : count sample (gkrLayerRepair m values gates sentLeft claimLeft sentRight claimRight a b ru rv)=0 := by
        classical
        unfold count
        apply List.countP_eq_zero.mpr
        intro gamma hg dec
        have accepted := @_root_.of_decide_eq_true _ (Classical.propDecidable _) dec
        exact checked ⟨accepted.1,accepted.2.1,accepted.2.2.1⟩
      omega
  have total := two_axis_fresh_budget (uniformTuples sample m) (uniformTuples sample m) sample
    badLeft badRight (gkrLayerRepair m values gates sentLeft claimLeft sentRight claimRight a b)
    sample.length (sample.length^m) (2*m)
    (uniform_tuples_length sample m) (uniform_tuples_length sample m) rfl
    (gkr_adaptive_bad_paths_count sample distinct values (gkrLeftAxisTerms values gates) sentLeft claimLeft m)
    (by
      intro ru hu
      exact gkr_adaptive_bad_paths_count sample distinct values
        (gkrRightAxisTerms m values (fun i => ru.getD i 0) gates) (sentRight ru) (claimRight ru) m) fresh
  have factor : (2*(2*m)+1)*(sample.length^m)*(sample.length^m)*sample.length=
      (4*m+1)*sample.length^(2*m+1) := by
    rw [Nat.pow_succ,show 2*m=m+m by omega,Nat.pow_add]
    grind
  rwa [factor] at total
end NearCompression
