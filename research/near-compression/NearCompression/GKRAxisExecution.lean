import NearCompression.GKRRoundState
namespace NearCompression
open Lean.Grind ZkFormal.Algebra
variable {K : Type} [Field K]

def gkrAxisValues : Nat → (Nat → K) → (Nat → K) → (Nat → K)
  | 0,values,_ => values
  | n+1,values,point => gkrAxisValues n (gkrFoldInput values (point 0)) (fun i => point (i+1))

def gkrAxisTerm : Nat → GKRIndexedTerm K → (Nat → K) → GKRIndexedTerm K
  | 0,t,_ => t
  | n+1,t,point => gkrAxisTerm n (gkrAdvanceTerm (point 0) t) (fun i => point (i+1))

theorem gkr_mle_first_fold (n : Nat) (values point : Nat → K) :
    genericRowMLE n (gkrFoldInput values (point 0)) (fun i => point (i+1))=
      genericRowMLE (n+1) values point := by
  have eq : gkrFoldInput values (point 0) =
      fun i => (1-point 0)*values (2*i)+point 0*values (2*i+1) := by
    funext i
    unfold gkrFoldInput
    grind
  rw [eq,generic_row_mle_add,generic_row_mle_scale,generic_row_mle_scale]
  rfl

theorem gkr_axis_values_mle (n : Nat) (values point : Nat → K) :
    gkrAxisValues n values point 0=genericRowMLE n values point := by
  induction n generalizing values point with
  | zero => rfl
  | succ n ih => rw [gkrAxisValues,ih,gkr_mle_first_fold]

/-- All gate fields, including the opposite input, remain fixed during an axis.
The current index is shifted and its equality-basis factors accumulate. -/
theorem gkr_axis_term_exact (n : Nat) (t : GKRIndexedTerm K) (point : Nat → K) :
    gkrAxisTerm n t point=
      ⟨t.op,t.axis,t.index/(2^n),t.weight*rowEqualityWeight n point t.index,t.other⟩ := by
  induction n generalizing t point with
  | zero => simp [gkrAxisTerm,rowEqualityWeight]; congr 1 <;> grind
  | succ n ih =>
    rw [gkrAxisTerm,ih]
    dsimp only [gkrAdvanceTerm]
    have index : (t.index/2)/(2^n)=t.index/(2^(n+1)) := by
      rw [Nat.div_div_eq_div_mul,Nat.pow_succ']
    rw [index]
    have bit : (if t.index%2=1 then point 0 else 1-point 0)=
        (if t.index%2=0 then 1-point 0 else point 0) := by
      have h := Nat.mod_lt t.index (by decide : 0<2)
      by_cases h0 : t.index%2=0 <;> by_cases h1 : t.index%2=1 <;> simp_all
    simp only [bit,rowEqualityWeight]
    congr 1 <;> grind

theorem gkr_axis_contribution (n : Nat) (values point : Nat → K) (t : GKRIndexedTerm K)
    (bound : t.index<2^n) :
    gkrIndexedContribution (gkrAxisValues n values point) (gkrAxisTerm n t point)=
      (t.weight*rowEqualityWeight n point t.index)*
        (if t.axis then gkrGateValue t.op t.other (genericRowMLE n values point)
        else gkrGateValue t.op (genericRowMLE n values point) t.other) := by
  rw [gkr_axis_term_exact]
  dsimp only [gkrIndexedContribution]
  rw [Nat.div_eq_of_lt bound,gkr_axis_values_mle]

/-- Initial first-axis state is the actual weighted gate evaluation. -/
def gkrLeftAxisTerms (values : Nat → K) (gates : List (GKRWiringGate × K)) : List (GKRIndexedTerm K) :=
  gates.map (fun (g,w) => ⟨g.op,false,g.left,w,values g.right⟩)

theorem gkr_left_initial_claim (values : Nat → K) (gates : List (GKRWiringGate × K)) :
    gkrStateClaim values (gkrLeftAxisTerms values gates)=
      (gates.map (fun item => item.2*gkrGateValue item.1.op
        (values item.1.left) (values item.1.right))).sum := by
  simp [gkrStateClaim,gkrLeftAxisTerms,List.map_map,Function.comp_def,gkrIndexedContribution]

/-- After the left axis, the right array resets to the original values. The
fixed opposite input is the computed left MLE; gate weights retain eq(ru). -/
def gkrRightAxisTerms (n : Nat) (values ru : Nat → K)
    (gates : List (GKRWiringGate × K)) : List (GKRIndexedTerm K) :=
  gates.map (fun (g,w) => ⟨g.op,true,g.right,w*rowEqualityWeight n ru g.left,
    genericRowMLE n values ru⟩)

theorem gkr_axis_reset (n : Nat) (values ru : Nat → K) (gates : List (GKRWiringGate × K))
    (bounds : ∀ item∈gates,item.1.left<2^n) :
    gkrStateClaim (gkrAxisValues n values ru)
      ((gkrLeftAxisTerms values gates).map (fun t => gkrAxisTerm n t ru))=
      gkrStateClaim values (gkrRightAxisTerms n values ru gates) := by
  unfold gkrStateClaim gkrLeftAxisTerms gkrRightAxisTerms
  simp only [List.map_map]
  congr 1
  apply List.map_congr_left
  intro item hi
  exact gkr_axis_contribution n values ru _ (bounds item hi)

theorem gkr_axes_terminal_wiring (n : Nat) (values ru rv : Nat → K)
    (gates : List (GKRWiringGate × K)) (bounds : ∀ item∈gates,item.1.right<2^n) :
    gkrStateClaim (gkrAxisValues n values rv)
      ((gkrRightAxisTerms n values ru gates).map (fun t => gkrAxisTerm n t rv))=
      gkrLayerWiring n gates ru rv (genericRowMLE n values ru) (genericRowMLE n values rv) := by
  unfold gkrStateClaim gkrRightAxisTerms gkrLayerWiring
  simp only [List.map_map]
  congr 1
  apply List.map_congr_left
  intro item hi
  have h := gkr_axis_contribution n values rv
    (⟨item.1.op,true,item.1.right,item.2*rowEqualityWeight n ru item.1.left,
      genericRowMLE n values ru⟩ : GKRIndexedTerm K) (bounds item hi)
  dsimp only [Function.comp_apply] at h ⊢
  rw [h]
  grind
end NearCompression
