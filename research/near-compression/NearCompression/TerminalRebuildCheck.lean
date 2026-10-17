import NearCompression.TerminalBalanceCheck
namespace NearCompression

inductive TerminalRebuildRecipe (K : Type) where
  | constant (value : K)
  | input (slot : Nat)
  | binary (op : GKRBinaryOp) (left right x y : Nat) (w : TerminalArithmeticWitness K)
  | expanded (tree : TerminalExpansionTree) (mapping : List Nat) (balance : TerminalBalanceCertificate K)

structure TerminalRebuildRecord (K : Type) where
  source : Nat
  target : Nat
  recipe : TerminalRebuildRecipe K

def terminalRebuildRecordCheck {K : Type} [Lean.Grind.Field K] [DecidableEq K]
    (source target : List (TerminalDAGNode K)) (inputs : Nat → K)
    (known : List (Nat × Nat)) (record : TerminalRebuildRecord K) : Bool :=
  decide (record.source<source.length ∧ record.target<target.length) &&
  match record.recipe with
  | .constant value => decide (source.getD record.source (.constant 0)=.constant value ∧
      target.getD record.target (.constant 0)=.constant value)
  | .input slot => decide (source.getD record.source (.constant 0)=.constant (inputs slot) ∧
      target.getD record.target (.constant 0)=.input slot)
  | .binary op left right x y w =>
      decide (source.getD record.source (.constant 0)=.binary op left right ∧
        (left,x)∈known ∧ (right,y)∈known) &&
      terminalStoredArithmeticCheck target op x y record.target w
  | .expanded tree mapping balance =>
      decide (tree.root=record.source ∧ tree.sign=true ∧ balance.result=record.target ∧
        balance.terms=tree.terms.map (fun t => (mapping.getD t.1 0,t.2))) &&
      tree.terms.all (fun t => decide (t.1<mapping.length ∧ (t.1,mapping.getD t.1 0)∈known)) &&
      terminalExpansionCheck source tree && terminalBalanceCheck target balance

theorem terminal_rebuild_record_checked {K : Type} [Lean.Grind.Field K] [DecidableEq K]
    (source target : List (TerminalDAGNode K)) (inputs : Nat → K)
    (known : List (Nat × Nat)) (record : TerminalRebuildRecord K)
    (prior : ∀ p∈known,TerminalRebuildRoute (fun i => source.getD i (.constant 0))
      (fun i => target.getD i (.constant 0)) inputs p.1 p.2)
    (h : terminalRebuildRecordCheck source target inputs known record=true) :
    TerminalRebuildRoute (fun i => source.getD i (.constant 0))
      (fun i => target.getD i (.constant 0)) inputs record.source record.target := by
  rcases record with ⟨i,z,recipe⟩
  cases recipe with
  | constant value =>
    simp only [terminalRebuildRecordCheck,Bool.and_eq_true,decide_eq_true_eq] at h
    exact .constant h.2.1 h.2.2
  | input slot =>
    simp only [terminalRebuildRecordCheck,Bool.and_eq_true,decide_eq_true_eq] at h
    exact .input h.2.1 h.2.2
  | binary op left right x y w =>
    simp only [terminalRebuildRecordCheck,Bool.and_eq_true,decide_eq_true_eq] at h
    exact .binary h.2.1.1 (prior (left,x) h.2.1.2.1) (prior (right,y) h.2.1.2.2)
      (terminal_stored_arithmetic_checked target op x y z w h.2.2).2
  | expanded tree mapping balance =>
    simp only [terminalRebuildRecordCheck,Bool.and_eq_true,decide_eq_true_eq] at h
    obtain ⟨bounds,⟨⟨⟨⟨root,sign,result,terms⟩,leaves⟩,expand⟩,balanced⟩⟩ := h
    have expansion := terminal_expansion_checked source tree expand
    rw [root,sign] at expansion
    have route := terminal_balance_checked target balance balanced
    rw [result,terms] at route
    apply TerminalRebuildRoute.expanded (mapping := fun j => mapping.getD j 0) expansion ?_ route
    intro t ht
    have leaf := List.all_eq_true.mp leaves t ht
    simp only [decide_eq_true_eq] at leaf
    exact prior (t.1,mapping.getD t.1 0) leaf.2

def terminalRebuildRecordsCheck {K : Type} [Lean.Grind.Field K] [DecidableEq K]
    (source target : List (TerminalDAGNode K)) (inputs : Nat → K) :
    List (Nat × Nat) → List (TerminalRebuildRecord K) → Nat → Nat → Bool
  | known,[],i,z => decide ((i,z)∈known)
  | known,record::rest,i,z => terminalRebuildRecordCheck source target inputs known record &&
      terminalRebuildRecordsCheck source target inputs ((record.source,record.target)::known) rest i z

theorem terminal_rebuild_records_checked {K : Type} [Lean.Grind.Field K] [DecidableEq K]
    (source target : List (TerminalDAGNode K)) (inputs : Nat → K)
    (records : List (TerminalRebuildRecord K)) (known : List (Nat × Nat)) (i z : Nat)
    (prior : ∀ p∈known,TerminalRebuildRoute (fun j => source.getD j (.constant 0))
      (fun j => target.getD j (.constant 0)) inputs p.1 p.2)
    (h : terminalRebuildRecordsCheck source target inputs known records i z=true) :
    TerminalRebuildRoute (fun j => source.getD j (.constant 0))
      (fun j => target.getD j (.constant 0)) inputs i z := by
  induction records generalizing known with
  | nil =>
    simp only [terminalRebuildRecordsCheck,decide_eq_true_eq] at h
    exact prior (i,z) h
  | cons record rest ih =>
    simp only [terminalRebuildRecordsCheck,Bool.and_eq_true] at h
    apply ih ((record.source,record.target)::known) ?_ h.2
    intro p hp
    rcases List.mem_cons.mp hp with hp | hp
    · subst p
      exact terminal_rebuild_record_checked source target inputs known record prior h.1
    · exact prior p hp

/-- No reconstruction-route premise: every used route is derived from checked
finite records. Input leaves are checked against this explicit assignment;
this does not establish committed-data extraction or universal parser refinement. -/
theorem terminal_program_rebuild_checked_value {K : Type} [Lean.Grind.Field K] [DecidableEq K]
    (env : TerminalProgramEnvironment K) (program : List (TerminalInstruction K))
    (nodes : List (TerminalDAGNode K)) (inputs constants : Nat → K)
    (sourceRoot targetRoot capacity : Nat) (live positions : List Nat)
    (zeroSlot : Nat) (stages : List TerminalStoredPlan) (outputSlot : Nat)
    (records : List (TerminalRebuildRecord K))
    (sourceChecked : terminalAcyclicCheck 0 (program.map (terminalProgramNode env))=true)
    (bundleChecked : terminalStoredBundleCheck nodes capacity constants live positions zeroSlot stages targetRoot outputSlot=true)
    (rebuildChecked : terminalRebuildRecordsCheck (program.map (terminalProgramNode env)) nodes inputs [] records sourceRoot targetRoot=true) :
    gkrFiniteCircuit (terminalInitialValues capacity inputs constants) (stages.map (fun s => s.gates)) outputSlot=
      terminalProgramRun env 0 (fun _ => 0) program sourceRoot := by
  apply terminal_program_checked_bundle_value env program nodes inputs constants sourceRoot targetRoot
    capacity live positions zeroSlot stages outputSlot sourceChecked bundleChecked
  exact terminal_rebuild_records_checked _ nodes inputs records [] sourceRoot targetRoot
    (by intro p hp; simp at hp) rebuildChecked

private def rebuildSmokeSource : List (TerminalDAGNode Rat) :=
  [.constant 3,.constant 5,.binary .mul 0 1,.binary .sub 2 0]
private def rebuildSmokeTarget : List (TerminalDAGNode Rat) :=
  [.input 0,.input 1,.binary .mul 0 1,.binary .sub 2 0,.constant 3]
private def rebuildSmokeInputs (i : Nat) : Rat := if i=0 then 3 else 5
private def rebuildSmokeExpansion (mapping : List Nat) : TerminalRebuildRecord Rat :=
  ⟨3,3,.expanded (.branch 3 true (.leaf 2 true) (.leaf 0 false)) mapping
    (.pass (.pair (2,true) (0,false) (3,true) .direct .empty) (.positive 3))⟩
private def rebuildSmokeRecords : List (TerminalRebuildRecord Rat) :=
  [⟨0,4,.constant 3⟩,⟨0,0,.input 0⟩,⟨1,1,.input 1⟩,
   ⟨2,2,.binary .mul 0 1 0 1 .direct⟩,rebuildSmokeExpansion [0,1,2]]

/-- Complete constant/input/binary/expanded reconstruction, with assignment,
dependency, mapping, finite bounds and final root rejection cases. -/
theorem terminal_rebuild_check_regressions :
    terminalRebuildRecordsCheck rebuildSmokeSource rebuildSmokeTarget rebuildSmokeInputs
      [] rebuildSmokeRecords 3 3=true ∧
    terminalRebuildRecordsCheck rebuildSmokeSource rebuildSmokeTarget (fun _ => 7)
      [] rebuildSmokeRecords 3 3=false ∧
    terminalRebuildRecordsCheck rebuildSmokeSource rebuildSmokeTarget rebuildSmokeInputs
      [] [⟨2,2,.binary .mul 0 1 0 1 .direct⟩] 2 2=false ∧
    terminalRebuildRecordsCheck rebuildSmokeSource rebuildSmokeTarget rebuildSmokeInputs
      [] rebuildSmokeRecords 3 2=false ∧
    terminalRebuildRecordCheck rebuildSmokeSource rebuildSmokeTarget rebuildSmokeInputs
      [(0,0),(2,2)] (rebuildSmokeExpansion [0])=false ∧
    terminalRebuildRecordCheck rebuildSmokeSource rebuildSmokeTarget rebuildSmokeInputs
      [(0,0)] (rebuildSmokeExpansion [0,1,2])=false ∧
    terminalRebuildRecordCheck rebuildSmokeSource rebuildSmokeTarget rebuildSmokeInputs
      [] ⟨0,4,.constant 7⟩=false ∧
    terminalRebuildRecordCheck rebuildSmokeSource rebuildSmokeTarget rebuildSmokeInputs
      [] ⟨99,99,.constant 0⟩=false ∧
    terminalRebuildRecordsCheck rebuildSmokeSource rebuildSmokeTarget rebuildSmokeInputs
      [] [] 0 0=false := by decide +kernel

end NearCompression
