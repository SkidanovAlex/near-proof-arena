import NearCompression.SHA512Round
import NearCompression.SHA512RoundWitness
import NearCompression.InstructionAddTrace

namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra

/-- Check that an expression uses only constants and current columns. -/
def sha512CurrentExpr : Expr → Bool
  | .const _ => true
  | .col _ nx => !nx
  | .add a b | .mul a b => sha512CurrentExpr a && sha512CurrentExpr b
  | .neg a => sha512CurrentExpr a
  | _ => false

theorem sha512_current_expr_local (e : Expr) (h : sha512CurrentExpr e = true) :
    instructionLocalExpr e := by
  induction e with
  | const n => trivial
  | col c nx => simpa [sha512CurrentExpr, instructionLocalExpr] using h
  | add a b ia ib | mul a b ia ib =>
    have hs : sha512CurrentExpr a = true ∧ sha512CurrentExpr b = true := by
      simpa [sha512CurrentExpr] using h
    exact ⟨ia hs.1, ib hs.2⟩
  | neg a ia => exact ia h
  | pub i => simp [sha512CurrentExpr] at h
  | isFirst => simp [sha512CurrentExpr] at h
  | isLast => simp [sha512CurrentExpr] at h
  | isTransition => simp [sha512CurrentExpr] at h

set_option maxRecDepth 65536 in
set_option maxHeartbeats 4000000 in
theorem sha512_round_constraints_current :
    sha512RoundConstraints.all sha512CurrentExpr = true := by decide

theorem sha512_round_constraints_local (e : Expr) (he : e ∈ sha512RoundConstraints) :
    instructionLocalExpr e :=
  sha512_current_expr_local e (List.all_eq_true.mp sha512_round_constraints_current e he)

/-- The actual AIR trace predicate supplies every row constraint of the round. -/
theorem sha512_round_trace_holds (air : Air) (tr : Trace Fp) (pub : List Fp)
    (t : Nat) (ht : t < air.tables.length)
    (table : air.tables[t] = sha512RoundTable)
    (holds : Holds air pub tr) (r : Nat) (hr : r < tr.height t) :
    sha512RoundHolds (tr.cell t r) := by
  intro e he
  have hc := holds.constr t ht r hr e
  rw [table] at hc
  have hv := hc he
  rw [instruction_local_eval e tr t r pub (sha512_round_constraints_local e he)] at hv
  exact hv

/-- Actual trace soundness; connections between consecutive rows are separate. -/
theorem sha512_round_trace_sound (air : Air) (tr : Trace Fp) (pub : List Fp)
    (t : Nat) (ht : t < air.tables.length)
    (table : air.tables[t] = sha512RoundTable)
    (holds : Holds air pub tr) (r : Nat) (hr : r < tr.height t) :
    NearSpecV3.SHA512.round (sha512RoundVars (tr.cell t r))
      (sha512RoundK (tr.cell t r)) (sha512RoundW (tr.cell t r)) =
      sha512RoundOutput (tr.cell t r) :=
  sha512_round_full_output _ (sha512_round_trace_holds air tr pub t ht table holds r hr)

/-- An isolated round table; there is no schedule or cross-row bus yet. -/
def sha512RoundAir : Air := ⟨[sha512RoundTable], 0, 0⟩

/-- Every family of satisfying rows yields an actual AIR trace at a legal height. -/
theorem sha512_round_trace_complete (tr : Trace Fp) (pub : List Fp)
    (height : 1 ≤ tr.log 0 ∧ tr.log 0 ≤ 22)
    (rows : ∀ r, r < tr.height 0 → sha512RoundHolds (tr.cell 0 r)) :
    Holds sha512RoundAir pub tr := by
  constructor
  · intro t ht
    have hzero : t = 0 := by simpa [sha512RoundAir] using ht
    subst t
    exact height
  · intro t ht r hr e he
    have hzero : t = 0 := by simpa [sha512RoundAir] using ht
    subst t
    rw [instruction_local_eval e tr 0 r pub (sha512_round_constraints_local e he)]
    exact rows r hr e he
  · intro t ht r hr i hi
    have hzero : t = 0 := by simpa [sha512RoundAir] using ht
    subst t
    simp [sha512RoundAir, sha512RoundTable] at hi
  · intro b m
    simp [busCount, busCount.go, sha512RoundAir, sha512RoundTable, tableBusCount]

/-- A family of honest round witnesses, with no assertion that rows are chained. -/
def sha512RoundWitnessTrace (logSize : Nat) (v : Nat → NearSpecV3.SHA512.Vars)
    (k w : Nat → Nat) : Trace Fp :=
  ⟨fun _ => logSize, fun _ r col => sha512RoundWitness (v r) (k r) (w r) col⟩

/-- Bounded inputs construct an actual satisfying trace, not just abstract rows. -/
theorem sha512_round_witness_trace_holds (logSize : Nat)
    (v : Nat → NearSpecV3.SHA512.Vars) (k w : Nat → Nat)
    (height : 1 ≤ logSize ∧ logSize ≤ 22)
    (bounds : ∀ r, r < 2^logSize → sha512RoundInputBounds (v r) (k r) (w r)) :
    Holds sha512RoundAir [] (sha512RoundWitnessTrace logSize v k w) := by
  apply sha512_round_trace_complete _ [] height
  intro r hr
  exact sha512_round_witness_holds (v r) (k r) (w r) (bounds r hr)

end NearCompression
