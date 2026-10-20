import NearCompression.GenericRowMLE
import NearCompression.InstructionSumcheckSoundness

/-! Fixed claim vectors and polynomial restrictions of their interpolants.
This is deterministic algebra. The line-root theorem is NOT a bound for
independently sampled coordinates, nor a PCS or Fiat--Shamir theorem. -/
namespace NearCompression
open Lean.Grind ZkFormal.Algebra ArenaCore.Security

variable {K : Type} [Field K]

theorem packed_claim_lane_bits (n lane : Nat) (valid : lane < 2^n) :
    ∃ bits : Nat → Bool, genericRowBitIndex n bits=lane := by
  induction n generalizing lane with
  | zero =>
    refine ⟨fun _ => false, ?_⟩
    simp only [genericRowBitIndex]
    simp only [Nat.pow_zero] at valid
    omega
  | succ n ih =>
    have half : lane/2 < 2^n := by rw [Nat.pow_succ] at valid; omega
    obtain ⟨bits, hb⟩ := ih (lane/2) half
    by_cases odd : lane%2=1
    · refine ⟨(fun i => match i with | 0 => true | j+1 => bits j), ?_⟩
      simp only [genericRowBitIndex,ite_true,hb]
      omega
    · refine ⟨(fun i => match i with | 0 => false | j+1 => bits j), ?_⟩
      simp only [genericRowBitIndex,Bool.false_eq_true,ite_false,hb]
      omega

def packedClaimRestriction : Nat → (Nat → K) → (Nat → Poly K) → Poly K
  | 0, values, _ => Poly.C (values 0)
  | n+1, values, coords =>
      (Poly.C 1-coords 0)*packedClaimRestriction n (fun i => values (2*i)) (fun i => coords (i+1)) +
      coords 0*packedClaimRestriction n (fun i => values (2*i+1)) (fun i => coords (i+1))

theorem packed_claim_restriction_eval (n : Nat) (values : Nat → K)
    (coords : Nat → Poly K) (r : K) :
    (packedClaimRestriction n values coords).eval r =
      genericRowMLE n values (fun i => (coords i).eval r) := by
  induction n generalizing values coords with
  | zero => exact Poly.eval_C _ _
  | succ n ih =>
    simp only [packedClaimRestriction,Poly.eval_add,Poly.eval_mul,Poly.eval_sub,
      Poly.eval_C,ih,genericRowMLE]

theorem packed_claim_restriction_degree (n : Nat) (values : Nat → K)
    (coords : Nat → Poly K) (affine : ∀ i, (coords i).DegLt 2) :
    (packedClaimRestriction n values coords).DegLt (n+1) := by
  induction n generalizing values coords with
  | zero => exact Poly.degLt_length _
  | succ n ih =>
    have hc : (Poly.C (1 : K)).DegLt 2 :=
      (Poly.degLt_length _).mono (by change 1 ≤ 2; decide)
    apply Poly.degLt_add
    · have h := Poly.degLt_mul (Poly.degLt_sub hc (affine 0))
        (ih (fun i => values (2*i)) _ (fun i => affine (i+1)))
      simpa [Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using h
    · have h := Poly.degLt_mul (affine 0)
        (ih (fun i => values (2*i+1)) _ (fun i => affine (i+1)))
      simpa [Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using h

/-- A differing Boolean lane explicitly witnesses distinct multilinear
functions, even when evaluation elsewhere happens to agree. -/
theorem packed_claim_interpolants_differ (n : Nat) (sent source : Nat → K)
    (bits : Nat → Bool)
    (wrong : sent (genericRowBitIndex n bits) ≠ source (genericRowBitIndex n bits)) :
    genericRowMLE n sent ≠ genericRowMLE n source := by
  intro same
  have eq := congrArg (fun f => f (genericRowBooleanPoint bits)) same
  rw [generic_row_mle_boolean,generic_row_mle_boolean] at eq
  exact wrong eq

theorem packed_claim_valid_lane_nonzero (n lane : Nat) (sent source : Nat → K)
    (valid : lane < 2^n) (wrong : sent lane ≠ source lane) :
    genericRowMLE n sent ≠ genericRowMLE n source := by
  obtain ⟨bits,hb⟩ := packed_claim_lane_bits n lane valid
  apply packed_claim_interpolants_differ n sent source bits
  simpa only [hb] using wrong

theorem packed_claim_restriction_nonzero (n : Nat) (sent source : Nat → K)
    (coords : Nat → Poly K) (bits : Nat → Bool) (witness : K)
    (through : ∀ i, (coords i).eval witness = genericRowBooleanPoint bits i)
    (wrong : sent (genericRowBitIndex n bits) ≠ source (genericRowBitIndex n bits)) :
    ¬ (packedClaimRestriction n sent coords-packedClaimRestriction n source coords).IsZero := by
  intro zero
  have eq := Poly.eval_of_isZero zero witness
  rw [Poly.eval_sub,packed_claim_restriction_eval,packed_claim_restriction_eval] at eq
  have point : (fun i => (coords i).eval witness)=genericRowBooleanPoint bits := funext through
  rw [point,generic_row_mle_boolean,generic_row_mle_boolean] at eq
  apply wrong
  grind

/-- At most n distinct line parameters hide a discrepancy, provided the
chosen affine restriction passes through a differing Boolean lane. -/
theorem packed_claim_line_bad_roots (n : Nat) (sent source : Nat → K)
    (coords : Nat → Poly K) (affine : ∀ i, (coords i).DegLt 2)
    (bits : Nat → Bool) (witness : K)
    (through : ∀ i, (coords i).eval witness = genericRowBooleanPoint bits i)
    (wrong : sent (genericRowBitIndex n bits) ≠ source (genericRowBitIndex n bits))
    (candidates : List K) (distinct : candidates.Nodup) :
    count candidates (fun r => genericRowMLE n sent (fun i => (coords i).eval r) =
      genericRowMLE n source (fun i => (coords i).eval r)) ≤ n := by
  have nz := packed_claim_restriction_nonzero n sent source coords bits witness through wrong
  have degree := Poly.degLt_sub (packed_claim_restriction_degree n sent coords affine)
    (packed_claim_restriction_degree n source coords affine)
  have roots := PolyRoots.cardRootsLe_of polyEval polyDeg quotFacts isZeroEval
    K _ (n+1) candidates nz degree distinct
  have subset : count candidates (fun r => genericRowMLE n sent (fun i => (coords i).eval r) =
      genericRowMLE n source (fun i => (coords i).eval r)) ≤
      count candidates (fun r =>
        (packedClaimRestriction n sent coords-packedClaimRestriction n source coords).eval r=0) := by
    apply count_mono
    intro r eq
    rw [Poly.eval_sub,packed_claim_restriction_eval,packed_claim_restriction_eval,eq]
    grind
  omega

end NearCompression
