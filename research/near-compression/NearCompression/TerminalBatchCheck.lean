import NearCompression.TerminalRebuildCheck
namespace NearCompression

/-- Weights and claims are expected public transcript values supplied by the
caller; the checker binds their physical constant nodes to those values. -/
structure TerminalBatchEntry (K : Type) where
  root : Nat
  weight : K
  claim : K
  weightNode : Nat
  claimNode : Nat
  powerNode : Nat
  weightedNode : Nat
  deltaNode : Nat
  termNode : Nat
  weightedWitness : TerminalArithmeticWitness K
  deltaWitness : TerminalArithmeticWitness K
  termWitness : TerminalArithmeticWitness K

def terminalBatchEntryCheck {K : Type} [Lean.Grind.Field K] [DecidableEq K]
    (nodes : List (TerminalDAGNode K)) (power : K) (e : TerminalBatchEntry K) : Bool :=
  decide (nodes.getD e.weightNode (.input 0)=.constant e.weight ∧
    nodes.getD e.claimNode (.input 0)=.constant e.claim ∧
    nodes.getD e.powerNode (.input 0)=.constant power) &&
  terminalStoredArithmeticCheck nodes .mul e.root e.weightNode e.weightedNode e.weightedWitness &&
  terminalStoredArithmeticCheck nodes .sub e.weightedNode e.claimNode e.deltaNode e.deltaWitness &&
  terminalStoredArithmeticCheck nodes .mul e.powerNode e.deltaNode e.termNode e.termWitness

theorem terminal_batch_entry_checked {K : Type} [Lean.Grind.Field K] [DecidableEq K]
    (nodes : List (TerminalDAGNode K)) (inputs values : Nat → K)
    (equations : ∀ i,values i=terminalNodeValue inputs values (nodes.getD i (.constant 0)))
    (power : K) (e : TerminalBatchEntry K) (h : terminalBatchEntryCheck nodes power e=true) :
    values e.termNode=power*(values e.root*e.weight-e.claim) := by
  simp only [terminalBatchEntryCheck,Bool.and_eq_true,decide_eq_true_eq] at h
  have weightRoute := terminal_stored_arithmetic_checked nodes _ _ _ _ _ h.1.1.2
  have deltaRoute := terminal_stored_arithmetic_checked nodes _ _ _ _ _ h.1.2
  have termRoute := terminal_stored_arithmetic_checked nodes _ _ _ _ _ h.2
  have fallback (i : Nat) (bound : i<nodes.length) :
      nodes.getD i (.constant 0)=nodes.getD i (.input 0) := by simp [List.getD,bound]
  have ew := equations e.weightNode
  have ec := equations e.claimNode
  have ep := equations e.powerNode
  rw [fallback e.weightNode weightRoute.1.2.1,h.1.1.1.1] at ew
  rw [fallback e.claimNode deltaRoute.1.2.1,h.1.1.1.2.1] at ec
  rw [fallback e.powerNode termRoute.1.1,h.1.1.1.2.2] at ep
  have w := terminal_arithmetic_route_value _ inputs values equations _ _ _ _ weightRoute.2
  have d := terminal_arithmetic_route_value _ inputs values equations _ _ _ _ deltaRoute.2
  have t := terminal_arithmetic_route_value _ inputs values equations _ _ _ _ termRoute.2
  simp only [terminalNodeValue] at ew ec ep
  simpa only [gkrGateValue,ew,ec,ep,w,d] using t

def terminalBatchEntriesCheck {K : Type} [Lean.Grind.Field K] [DecidableEq K]
    (nodes : List (TerminalDAGNode K)) (rho : K) : K → List (TerminalBatchEntry K) → Bool
  | _,[] => true
  | power,e::rest => terminalBatchEntryCheck nodes power e && terminalBatchEntriesCheck nodes rho (power*rho) rest

theorem terminal_batch_entries_checked {K : Type} [Lean.Grind.Field K] [DecidableEq K]
    (nodes : List (TerminalDAGNode K)) (inputs values : Nat → K)
    (equations : ∀ i,values i=terminalNodeValue inputs values (nodes.getD i (.constant 0)))
    (rho power : K) (entries : List (TerminalBatchEntry K))
    (h : terminalBatchEntriesCheck nodes rho power entries=true) :
    terminalRegisterSignedSum values (entries.map (fun e => (e.termNode,true)))=
      terminalResidualValue rho power (entries.map (fun e => (values e.root*e.weight,e.claim))) := by
  induction entries generalizing power with
  | nil => rfl
  | cons e rest ih =>
    simp only [terminalBatchEntriesCheck,Bool.and_eq_true] at h
    have value := terminal_batch_entry_checked nodes inputs values equations power e h.1
    have tail := ih (power*rho) h.2
    simp only [List.map_cons,terminalResidualValue,terminalRegisterSignedSum,List.map_cons,
      List.sum_cons,terminalSignedValue,ite_true] at tail ⊢
    rw [value,tail]

def terminalBatchRootCheck {K : Type} [Lean.Grind.Field K] [DecidableEq K]
    (nodes : List (TerminalDAGNode K)) (result root zeroNode : Nat) : Bool :=
  decide (root=result) || (decide (nodes.getD zeroNode (.input 0)=.constant 0) &&
    terminalStoredArithmeticCheck nodes .add result zeroNode root .direct)

theorem terminal_batch_root_checked {K : Type} [Lean.Grind.Field K] [DecidableEq K]
    (nodes : List (TerminalDAGNode K)) (inputs values : Nat → K)
    (equations : ∀ i,values i=terminalNodeValue inputs values (nodes.getD i (.constant 0)))
    (result root zeroNode : Nat) (h : terminalBatchRootCheck nodes result root zeroNode=true) :
    values root=values result := by
  simp only [terminalBatchRootCheck,Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq] at h
  rcases h with h | ⟨zero,h⟩
  · rw [h]
  · have route := terminal_stored_arithmetic_checked nodes _ _ _ _ _ h
    have eq := terminal_arithmetic_route_value _ inputs values equations _ _ _ _ route.2
    have ez := equations zeroNode
    have lookup : nodes.getD zeroNode (.constant 0)=nodes.getD zeroNode (.input 0) := by
      simp [List.getD,route.1.2.1]
    rw [lookup,zero] at ez
    simp only [terminalNodeValue] at ez
    simp only [gkrGateValue,ez] at eq
    grind

/-- Exact residual identity, not a probability bound or a claim that individual
residuals vanish when their random linear combination vanishes. -/
theorem terminal_batch_checked_value {K : Type} [Lean.Grind.Field K] [DecidableEq K]
    (nodes : List (TerminalDAGNode K)) (inputs : Nat → K) (rho : K)
    (entries : List (TerminalBatchEntry K)) (balance : TerminalBalanceCertificate K)
    (root zeroNode : Nat)
    (acyclic : terminalAcyclicCheck 0 nodes=true)
    (entryCheck : terminalBatchEntriesCheck nodes rho 1 entries=true)
    (terms : balance.terms=entries.map (fun e => (e.termNode,true)))
    (balanceCheck : terminalBalanceCheck nodes balance=true)
    (rootCheck : terminalBatchRootCheck nodes balance.result root zeroNode=true) :
    terminalDAGRun inputs 0 (fun _ => 0) nodes root=
      terminalResidualValue rho 1 (entries.map (fun e =>
        (terminalDAGRun inputs 0 (fun _ => 0) nodes e.root*e.weight,e.claim))) := by
  have equations := terminal_dag_total_equations inputs nodes (terminal_acyclic_checked nodes 0 acyclic)
  rw [terminal_batch_root_checked nodes inputs _ equations balance.result root zeroNode rootCheck]
  rw [terminal_balance_checked_value inputs nodes balance acyclic balanceCheck,terms]
  exact terminal_batch_entries_checked nodes inputs _ equations rho 1 entries entryCheck

private def batchSmokeNodes : List (TerminalDAGNode Rat) :=
  [.input 0,.constant 2,.constant 3,.constant 1,.binary .mul 0 1,
   .binary .sub 4 2,.binary .mul 3 5,.constant 0,.binary .add 6 7]
private def batchSmokeEntry : TerminalBatchEntry Rat :=
  ⟨0,2,3,1,2,3,4,5,6,.direct,.direct,.direct⟩

/-- The second entry must use the next rho power, even when all other fields
match. Weight, claim, arithmetic output and forced-zero root are also bound. -/
theorem terminal_batch_check_regressions :
    terminalBatchEntriesCheck batchSmokeNodes 7 1 [batchSmokeEntry]=true ∧
    terminalBatchEntriesCheck batchSmokeNodes 1 1 [batchSmokeEntry,batchSmokeEntry]=true ∧
    terminalBatchEntriesCheck batchSmokeNodes 2 1 [batchSmokeEntry,batchSmokeEntry]=false ∧
    terminalBatchEntryCheck batchSmokeNodes 1 {batchSmokeEntry with weight:=3}=false ∧
    terminalBatchEntryCheck batchSmokeNodes 1 {batchSmokeEntry with claim:=2}=false ∧
    terminalBatchEntryCheck batchSmokeNodes 1 {batchSmokeEntry with termNode:=5}=false ∧
    terminalBatchEntryCheck batchSmokeNodes 1 {batchSmokeEntry with powerNode:=99}=false ∧
    terminalBatchRootCheck batchSmokeNodes 6 6 7=true ∧
    terminalBatchRootCheck batchSmokeNodes 6 8 7=true ∧
    terminalBatchRootCheck batchSmokeNodes 6 8 1=false ∧
    terminalBatchRootCheck batchSmokeNodes 6 5 7=false := by decide +kernel

end NearCompression
