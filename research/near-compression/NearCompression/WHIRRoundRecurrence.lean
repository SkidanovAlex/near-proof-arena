import NearCompression.WHIRTerminalWeight

/-! Concrete three-coefficient WHIR round arithmetic. Endpoint acceptance is
not treated as a proof of an honest polynomial: its deterministic recurrence
and honest polynomial construction are separate theorems. -/
set_option autoImplicit false
namespace NearCompression
open Lean.Grind
variable {K : Type} [CommRing K]

structure WhirQuadratic (K : Type) where
  c0 : K
  c1 : K
  c2 : K

def WhirQuadratic.eval (p : WhirQuadratic K) (x : K) : K := p.c0+x*(p.c1+x*p.c2)
def WhirQuadratic.endpoints (p : WhirQuadratic K) : K := p.eval 0+p.eval 1

/-- Honest degree-two coefficient vector for the product of two affine folds.
Each function is evaluated on the remaining Boolean tail. -/
def whirHonestQuadratic (n : Nat) (f0 f1 w0 w1 : List K → K) : WhirQuadratic K where
  c0 := whirCubeSum n (fun b => f0 b*w0 b)
  c1 := whirCubeSum n (fun b => f0 b*(w1 b-w0 b)+(f1 b-f0 b)*w0 b)
  c2 := whirCubeSum n (fun b => (f1 b-f0 b)*(w1 b-w0 b))

/-- Direct equality between the three coefficients' Horner evaluation and
the folded product. No polynomial agreement or verification hypothesis. -/
theorem whir_honest_quadratic_eval (n : Nat) (f0 f1 w0 w1 : List K → K) (r : K) :
    (whirHonestQuadratic n f0 f1 w0 w1).eval r =
    whirCubeSum n (fun b => ((1-r)*f0 b+r*f1 b)*((1-r)*w0 b+r*w1 b)) := by
  have h : (fun b => ((1-r)*f0 b+r*f1 b)*((1-r)*w0 b+r*w1 b)) =
    (fun b => f0 b*w0 b+r*(f0 b*(w1 b-w0 b)+(f1 b-f0 b)*w0 b)+
      (r*r)*((f1 b-f0 b)*(w1 b-w0 b))) := by funext; grind
  rw [h,whir_cube_add,whir_cube_add,whir_cube_scale,whir_cube_scale]
  simp only [WhirQuadratic.eval,whirHonestQuadratic]
  grind

theorem whir_honest_quadratic_endpoints (n : Nat) (f0 f1 w0 w1 : List K → K) :
    (whirHonestQuadratic n f0 f1 w0 w1).endpoints =
    whirCubeSum n (fun b => f0 b*w0 b)+whirCubeSum n (fun b => f1 b*w1 b) := by
  unfold WhirQuadratic.endpoints
  rw [whir_honest_quadratic_eval,whir_honest_quadratic_eval]
  have z : (fun b => ((1-(0:K))*f0 b+0*f1 b)*((1-0)*w0 b+0*w1 b))=(fun b => f0 b*w0 b) := by funext; grind
  have o : (fun b => ((1-(1:K))*f0 b+1*f1 b)*((1-1)*w0 b+1*w1 b))=(fun b => f1 b*w1 b) := by funext; grind
  rw [z,o]

/-- OOD uses gamma; the eight query folds use gamma²,...,gamma⁹. -/
def whirQueryAdditions (gamma power : K) : List K → K
  | [] => 0
  | value::values => power*value+whirQueryAdditions gamma (power*gamma) values

def whirStageAddition (gamma ood : K) (queryValues : List K) : K :=
  gamma*ood+whirQueryAdditions gamma (gamma*gamma) queryValues

/-- Literal left-to-right query additions performed by the verifier. -/
def whirAccumulateQueries (claim gamma power : K) : List K → K
  | [] => claim
  | value::values => whirAccumulateQueries (claim+power*value) gamma (power*gamma) values

theorem whir_accumulate_queries (values : List K) (claim gamma power : K) :
    whirAccumulateQueries claim gamma power values=claim+whirQueryAdditions gamma power values := by
  induction values generalizing claim power with
  | nil => simp only [whirAccumulateQueries,whirQueryAdditions]; grind
  | cons v vs ih => simp only [whirAccumulateQueries,whirQueryAdditions,ih]; grind

theorem whir_stage_update (claim gamma ood : K) (queryValues : List K) :
    whirAccumulateQueries (claim+gamma*ood) gamma (gamma*gamma) queryValues =
      claim+whirStageAddition gamma ood queryValues := by
  rw [whir_accumulate_queries]
  unfold whirStageAddition
  grind

structure WhirArithmeticRound (K : Type) where
  polynomial : WhirQuadratic K
  challenge : K
  /-- Zero for an ordinary fold; actual gamma/OOD/query sum at a stage boundary. -/
  addition : K

def whirRoundDelta (r : WhirArithmeticRound K) : K :=
  r.polynomial.eval r.challenge-r.polynomial.endpoints+r.addition

def whirRoundLedger : List (WhirArithmeticRound K) → K
  | [] => 0
  | r::rs => whirRoundDelta r+whirRoundLedger rs

/-- Literal endpoint test and claim replacement of the scheduled verifier.
The transcript supplies challenges separately; this function draws none. -/
def whirRunArithmetic [DecidableEq K] (claim : K) : List (WhirArithmeticRound K) → Option K
  | [] => some claim
  | r::rs => if r.polynomial.endpoints=claim then
      whirRunArithmetic (r.polynomial.eval r.challenge+r.addition) rs else none

theorem whir_run_arithmetic_ledger [DecidableEq K] (rounds : List (WhirArithmeticRound K))
    (initial terminal : K) (accepted : whirRunArithmetic initial rounds=some terminal) :
    terminal=initial+whirRoundLedger rounds := by
  induction rounds generalizing initial with
  | nil =>
    simp only [whirRunArithmetic,Option.some.injEq] at accepted
    simp only [whirRoundLedger]; grind
  | cons r rs ih =>
    simp only [whirRunArithmetic] at accepted
    split at accepted
    · rename_i endpoint
      have rest := ih _ accepted
      simp only [whirRoundLedger,whirRoundDelta]
      rw [rest]
      grind
    · cases accepted

/-- Executing an honestly constructed fold succeeds and updates the claim to
the actual folded Boolean-tail sum. This theorem has no acceptance premise. -/
theorem whir_honest_fold_step [DecidableEq K] (n : Nat) (f w : List K → K)
    (challenge addition : K) :
    whirRunArithmetic (whirCubeSum (n+1) (fun b => f b*w b))
      [{polynomial:=whirHonestQuadratic n (fun b => f (0::b)) (fun b => f (1::b))
          (fun b => w (0::b)) (fun b => w (1::b)),challenge:=challenge,addition:=addition}] =
    some (whirCubeSum n (fun b => ((1-challenge)*f (0::b)+challenge*f (1::b))*
      ((1-challenge)*w (0::b)+challenge*w (1::b))) + addition) := by
  simp only [whirRunArithmetic,whir_honest_quadratic_endpoints,whirCubeSum,ite_true]
  rw [whir_honest_quadratic_eval]

/-- A semantically correct injected opening contributes exactly its weighted
value to the claim. This is an algebraic identity, not a promise that a received
OOD/query value is correct. -/
theorem whir_honest_weight_injection (point : List K) (c : Nat → K)
    (weight : List K → K) (power : K) :
    whirCubeSum point.length (fun b => whirTensor b c*(weight b+power*whirKernel point b)) =
    whirCubeSum point.length (fun b => whirTensor b c*weight b)+power*whirTensor point c := by
  have h : (fun b => whirTensor b c*(weight b+power*whirKernel point b))=
    (fun b => whirTensor b c*weight b+power*(whirTensor b c*whirKernel point b)) := by
    funext; grind
  rw [h,whir_cube_add,whir_cube_scale,whir_tensor_reproducing]

/-- Acceptance forces the precise recurrence into the already proved final
weight expression. This is a deterministic consistency theorem, not soundness:
a malicious polynomial can still satisfy its endpoint test. -/
theorem whir_accepted_terminal_recurrence [DecidableEq K]
    (rounds : List (WhirArithmeticRound K)) (initial : K) (c : Nat → K)
    (zPrefix zTail challenges : List K) (same : zPrefix.length=challenges.length)
    (terms : List (WhirInjection K)) (offsets : ∀ t∈terms,t.start≤challenges.length)
    (accepted : whirRunArithmetic initial rounds=some
      (whirCubeSum zTail.length (fun tail => whirTensor tail c*
        (whirKernel (zPrefix++zTail) (challenges++tail)+whirScheduledWeight (challenges++tail) terms)))) :
    initial+whirRoundLedger rounds =
      whirKernel zPrefix challenges*whirTensor zTail c+
        whirInjectedTerminal zTail.length c challenges terms := by
  have recurrence := whir_run_arithmetic_ledger rounds initial _ accepted
  rw [whir_scheduled_terminal_identity c zPrefix zTail challenges same terms offsets] at recurrence
  exact recurrence.symm
/-- Scheduled specialization: the terminal coordinates are exactly the
challenges used by the checked round recurrence, not an independent input. -/
theorem whir_scheduled_accepted_recurrence [DecidableEq K]
    (rounds : List (WhirArithmeticRound K)) (initial : K) (c : Nat → K)
    (zPrefix zTail : List K) (same : zPrefix.length=rounds.length)
    (terms : List (WhirInjection K)) (offsets : ∀ t∈terms,t.start≤rounds.length)
    (accepted : whirRunArithmetic initial rounds=some
      (whirCubeSum zTail.length (fun tail => whirTensor tail c*
        (whirKernel (zPrefix++zTail) (rounds.map WhirArithmeticRound.challenge++tail)+
          whirScheduledWeight (rounds.map WhirArithmeticRound.challenge++tail) terms)))) :
    initial+whirRoundLedger rounds =
      whirKernel zPrefix (rounds.map WhirArithmeticRound.challenge)*whirTensor zTail c+
        whirInjectedTerminal zTail.length c (rounds.map WhirArithmeticRound.challenge) terms := by
  exact whir_accepted_terminal_recurrence rounds initial c zPrefix zTail _
    (by simpa using same) terms (by simpa using offsets) accepted
end NearCompression
