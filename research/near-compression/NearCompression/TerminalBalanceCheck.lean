import NearCompression.TerminalExpansionCheck
namespace NearCompression

def terminalJoinCheck {K : Type} [Lean.Grind.Field K] [DecidableEq K]
    (nodes : List (TerminalDAGNode K)) (a b c : Nat × Bool)
    (w : TerminalArithmeticWitness K) : Bool :=
  if a.2=b.2 then decide (c.2=a.2) && terminalStoredArithmeticCheck nodes .add a.1 b.1 c.1 w
  else if a.2 then decide (c.2=true) && terminalStoredArithmeticCheck nodes .sub a.1 b.1 c.1 w
  else decide (c.2=true) && terminalStoredArithmeticCheck nodes .sub b.1 a.1 c.1 w

theorem terminal_join_checked {K : Type} [Lean.Grind.Field K] [DecidableEq K]
    (nodes : List (TerminalDAGNode K)) (a b c : Nat × Bool)
    (w : TerminalArithmeticWitness K) (h : terminalJoinCheck nodes a b c w=true) :
    TerminalJoinRoute (fun i => nodes.getD i (.constant 0)) a b c := by
  rcases a with ⟨x,s⟩; rcases b with ⟨y,t⟩; rcases c with ⟨z,u⟩
  cases s <;> cases t <;> simp only [terminalJoinCheck, Bool.false_eq_true, Bool.true_eq_false,
    ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq] at h
  · obtain ⟨rfl,h⟩ := h
    exact .same (terminal_stored_arithmetic_checked nodes _ _ _ _ w h).2
  · obtain ⟨rfl,h⟩ := h
    exact .negativePositive (terminal_stored_arithmetic_checked nodes _ _ _ _ w h).2
  · obtain ⟨rfl,h⟩ := h
    exact .positiveNegative (terminal_stored_arithmetic_checked nodes _ _ _ _ w h).2
  · obtain ⟨rfl,h⟩ := h
    exact .same (terminal_stored_arithmetic_checked nodes _ _ _ _ w h).2

inductive TerminalPassCertificate (K : Type) where
  | empty
  | singleton (term : Nat × Bool)
  | pair (a b c : Nat × Bool) (witness : TerminalArithmeticWitness K) (rest : TerminalPassCertificate K)

def TerminalPassCertificate.input {K : Type} : TerminalPassCertificate K → List (Nat × Bool)
  | .empty => [] | .singleton a => [a] | .pair a b _ _ rest => a::b::rest.input

def TerminalPassCertificate.output {K : Type} : TerminalPassCertificate K → List (Nat × Bool)
  | .empty => [] | .singleton a => [a] | .pair _ _ c _ rest => c::rest.output

def terminalPassCheck {K : Type} [Lean.Grind.Field K] [DecidableEq K]
    (nodes : List (TerminalDAGNode K)) : TerminalPassCertificate K → Bool
  | .empty => true
  | .singleton a => decide (a.1<nodes.length)
  | .pair a b c w rest => terminalJoinCheck nodes a b c w && terminalPassCheck nodes rest

theorem terminal_pass_checked {K : Type} [Lean.Grind.Field K] [DecidableEq K]
    (nodes : List (TerminalDAGNode K)) (cert : TerminalPassCertificate K)
    (h : terminalPassCheck nodes cert=true) :
    TerminalPassRoute (fun i => nodes.getD i (.constant 0)) cert.input cert.output := by
  induction cert with
  | empty => exact .empty
  | singleton a => exact .singleton a
  | pair a b c w rest ih =>
    simp only [terminalPassCheck,Bool.and_eq_true] at h
    exact .pair (terminal_join_checked nodes a b c w h.1) (ih h.2)

inductive TerminalBalanceCertificate (K : Type) where
  | empty (result : Nat)
  | positive (register : Nat)
  | negative (register zeroNode result : Nat) (witness : TerminalArithmeticWitness K)
  | pass (stage : TerminalPassCertificate K) (rest : TerminalBalanceCertificate K)

def TerminalBalanceCertificate.terms {K : Type} : TerminalBalanceCertificate K → List (Nat × Bool)
  | .empty _ => [] | .positive x => [(x,true)] | .negative x _ _ _ => [(x,false)]
  | .pass stage _ => stage.input

def TerminalBalanceCertificate.result {K : Type} : TerminalBalanceCertificate K → Nat
  | .empty z => z | .positive x => x | .negative _ _ z _ => z | .pass _ rest => rest.result

def terminalBalanceCheck {K : Type} [Lean.Grind.Field K] [DecidableEq K]
    (nodes : List (TerminalDAGNode K)) : TerminalBalanceCertificate K → Bool
  | .empty z => decide (z<nodes.length ∧ nodes.getD z (.constant 0)=.constant 0)
  | .positive x => decide (x<nodes.length)
  | .negative x zeroNode z w => decide (nodes.getD zeroNode (.constant 0)=.constant 0) &&
      terminalStoredArithmeticCheck nodes .sub zeroNode x z w
  | .pass stage rest => decide (2≤stage.input.length ∧ stage.output=rest.terms) &&
      terminalPassCheck nodes stage && terminalBalanceCheck nodes rest

theorem terminal_balance_checked {K : Type} [Lean.Grind.Field K] [DecidableEq K]
    (nodes : List (TerminalDAGNode K)) (cert : TerminalBalanceCertificate K)
    (h : terminalBalanceCheck nodes cert=true) :
    TerminalBalanceRoute (fun i => nodes.getD i (.constant 0)) cert.terms cert.result := by
  induction cert with
  | empty z =>
    simp only [terminalBalanceCheck,decide_eq_true_eq] at h
    exact .empty h.2
  | positive x => exact .positive x
  | negative x zeroNode z w =>
    simp only [terminalBalanceCheck,Bool.and_eq_true,decide_eq_true_eq] at h
    exact .negative h.1 (terminal_stored_arithmetic_checked nodes _ _ _ _ w h.2).2
  | pass stage rest ih =>
    simp only [terminalBalanceCheck,Bool.and_eq_true,decide_eq_true_eq] at h
    have route := terminal_pass_checked nodes stage h.1.2
    have final := ih h.2
    rw [←h.1.1.2] at final
    cases stage with
    | empty => simp [TerminalPassCertificate.input] at h
    | singleton a => simp [TerminalPassCertificate.input] at h
    | pair a b c w tail => exact .pass route final

theorem terminal_balance_checked_value {K : Type} [Lean.Grind.Field K] [DecidableEq K]
    (inputs : Nat → K) (nodes : List (TerminalDAGNode K)) (cert : TerminalBalanceCertificate K)
    (acyclic : terminalAcyclicCheck 0 nodes=true) (checked : terminalBalanceCheck nodes cert=true) :
    terminalDAGRun inputs 0 (fun _ => 0) nodes cert.result=
      terminalRegisterSignedSum (terminalDAGRun inputs 0 (fun _ => 0) nodes) cert.terms :=
  terminal_balance_route_value inputs _ _
    (terminal_dag_total_equations inputs nodes (terminal_acyclic_checked nodes 0 acyclic))
    cert.terms cert.result (terminal_balance_checked nodes cert checked)

private def balanceSmokeNodes : List (TerminalDAGNode Rat) :=
  [.constant 0,.input 0,.input 1,.binary .add 1 2,.binary .sub 1 2,
   .binary .sub 2 1,.binary .sub 0 1,.binary .add 3 1]
private def balanceSmokeCert : TerminalBalanceCertificate Rat :=
  .pass (.pair (1,true) (2,true) (3,true) .direct (.singleton (1,true)))
    (.pass (.pair (3,true) (1,true) (7,true) .direct .empty) (.positive 7))

/-- All four sign pairs, an odd carry through two stages, and terminal empty,
positive and negative cases are evaluated by the kernel. -/
theorem terminal_balance_check_regressions :
    terminalJoinCheck balanceSmokeNodes (1,true) (2,true) (3,true) .direct=true ∧
    terminalJoinCheck balanceSmokeNodes (1,false) (2,false) (3,false) .direct=true ∧
    terminalJoinCheck balanceSmokeNodes (1,true) (2,false) (4,true) .direct=true ∧
    terminalJoinCheck balanceSmokeNodes (1,false) (2,true) (5,true) .direct=true ∧
    terminalBalanceCheck balanceSmokeNodes balanceSmokeCert=true ∧
    balanceSmokeCert.terms=[(1,true),(2,true),(1,true)] ∧
    balanceSmokeCert.result=7 ∧
    terminalBalanceCheck balanceSmokeNodes (.empty 0)=true ∧
    terminalBalanceCheck balanceSmokeNodes (.positive 1)=true ∧
    terminalBalanceCheck balanceSmokeNodes (.negative 1 0 6 .direct)=true ∧
    terminalJoinCheck balanceSmokeNodes (1,false) (2,true) (4,true) .direct=false ∧
    terminalJoinCheck balanceSmokeNodes (1,true) (2,true) (3,false) .direct=false ∧
    terminalBalanceCheck balanceSmokeNodes (.pass
      (.pair (1,true) (2,true) (3,true) .direct .empty) (.positive 4))=false ∧
    terminalBalanceCheck balanceSmokeNodes (.pass (.singleton (1,true)) (.positive 1))=false ∧
    terminalBalanceCheck balanceSmokeNodes (.pass .empty (.empty 0))=false ∧
    terminalBalanceCheck balanceSmokeNodes (.negative 1 2 5 .direct)=false ∧
    terminalBalanceCheck balanceSmokeNodes (.positive 99)=false ∧
    terminalBalanceCheck balanceSmokeNodes (.empty 99)=false ∧
    terminalPassCheck balanceSmokeNodes (.singleton (99,true))=false := by decide +kernel

end NearCompression
