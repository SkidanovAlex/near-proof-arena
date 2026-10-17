import NearCompression.TerminalArithmeticCheck
namespace NearCompression

/-- The collect certificate retains each source register and its sign. -/
inductive TerminalExpansionTree where
  | leaf (register : Nat) (sign : Bool)
  | branch (register : Nat) (sign : Bool) (left right : TerminalExpansionTree)

def TerminalExpansionTree.root : TerminalExpansionTree → Nat
  | .leaf i _ | .branch i _ _ _ => i

def TerminalExpansionTree.sign : TerminalExpansionTree → Bool
  | .leaf _ s | .branch _ s _ _ => s

def TerminalExpansionTree.terms : TerminalExpansionTree → List (Nat × Bool)
  | .leaf i s => [(i,s)]
  | .branch _ _ left right => left.terms++right.terms

def terminalExpansionCheck {K : Type} [Zero K] [DecidableEq K]
    (nodes : List (TerminalDAGNode K)) : TerminalExpansionTree → Bool
  | .leaf i _ => decide (i<nodes.length)
  | .branch i s left right =>
      decide (i<nodes.length ∧
        ((nodes.getD i (.constant 0)=.binary .add left.root right.root ∧ left.sign=s ∧ right.sign=s) ∨
         (nodes.getD i (.constant 0)=.binary .sub left.root right.root ∧ left.sign=s ∧ right.sign=(!s)))) &&
      terminalExpansionCheck nodes left && terminalExpansionCheck nodes right

theorem terminal_expansion_checked {K : Type} [Lean.Grind.Field K] [DecidableEq K]
    (nodes : List (TerminalDAGNode K)) (tree : TerminalExpansionTree)
    (checked : terminalExpansionCheck nodes tree=true) :
    TerminalSignedExpansion (fun i => nodes.getD i (.constant 0)) tree.root tree.sign tree.terms := by
  induction tree with
  | leaf i s => exact .leaf i s
  | branch i s left right hl hr =>
    simp only [terminalExpansionCheck,Bool.and_eq_true,decide_eq_true_eq] at checked
    have l := hl checked.1.2
    have r := hr checked.2
    change TerminalSignedExpansion _ i s (left.terms++right.terms)
    rcases checked.1.1.2 with ⟨node,ls,rs⟩ | ⟨node,ls,rs⟩
    · rw [ls] at l; rw [rs] at r
      exact .add node l r
    · rw [ls] at l; rw [rs] at r
      exact .sub node l r

/-- Root and retained leaves are in range; default lookup cannot invent a
register at either boundary of an accepted expansion. -/
theorem terminal_expansion_checked_bounds {K : Type} [Zero K] [DecidableEq K]
    (nodes : List (TerminalDAGNode K)) (tree : TerminalExpansionTree)
    (checked : terminalExpansionCheck nodes tree=true) :
    tree.root<nodes.length ∧ ∀ t∈tree.terms,t.1<nodes.length := by
  induction tree with
  | leaf i s =>
    simp only [terminalExpansionCheck,decide_eq_true_eq] at checked
    refine ⟨checked,?_⟩
    intro t ht
    have eq : t=(i,s) := List.mem_singleton.mp ht
    subst t
    exact checked
  | branch i s left right hl hr =>
    simp only [terminalExpansionCheck,Bool.and_eq_true,decide_eq_true_eq] at checked
    have l := hl checked.1.2
    have r := hr checked.2
    refine ⟨checked.1.1.1,?_⟩
    intro t ht
    rcases List.mem_append.mp ht with ht | ht
    · exact l.2 t ht
    · exact r.2 t ht

theorem terminal_expansion_checked_value {K : Type} [Lean.Grind.Field K] [DecidableEq K]
    (inputs : Nat → K) (nodes : List (TerminalDAGNode K)) (tree : TerminalExpansionTree)
    (acyclic : terminalAcyclicCheck 0 nodes=true)
    (checked : terminalExpansionCheck nodes tree=true) :
    terminalRegisterSignedSum (terminalDAGRun inputs 0 (fun _ => 0) nodes) tree.terms=
      terminalSignedValue (terminalDAGRun inputs 0 (fun _ => 0) nodes tree.root,tree.sign) :=
  terminal_signed_expansion_executed inputs nodes (terminal_acyclic_checked nodes 0 acyclic)
    tree.root tree.sign tree.terms (terminal_expansion_checked nodes tree checked)

private def expansionSmokeNodes : List (TerminalDAGNode Nat) :=
  [.input 0,.input 1,.input 2,.binary .sub 0 1,.binary .add 3 2,.binary .mul 0 1]
private def expansionSmokeTree : TerminalExpansionTree :=
  .branch 4 true (.branch 3 true (.leaf 0 true) (.leaf 1 false)) (.leaf 2 true)

/-- Nested subtraction signs, retained internal nodes and negative roots are
accepted. Wrong signs, dependencies, multiplication expansion and missing
registers reject. -/
theorem terminal_expansion_check_regressions :
    terminalExpansionCheck expansionSmokeNodes expansionSmokeTree=true ∧
    expansionSmokeTree.terms=[(0,true),(1,false),(2,true)] ∧
    terminalExpansionCheck expansionSmokeNodes (.leaf 4 true)=true ∧
    terminalExpansionCheck expansionSmokeNodes (.branch 3 false (.leaf 0 false) (.leaf 1 true))=true ∧
    terminalExpansionCheck expansionSmokeNodes (.branch 3 true (.leaf 0 true) (.leaf 1 true))=false ∧
    terminalExpansionCheck expansionSmokeNodes (.branch 3 true (.leaf 1 true) (.leaf 0 false))=false ∧
    terminalExpansionCheck expansionSmokeNodes (.branch 5 true (.leaf 0 true) (.leaf 1 true))=false ∧
    terminalExpansionCheck expansionSmokeNodes (.leaf 99 true)=false ∧
    terminalExpansionCheck expansionSmokeNodes (.branch 99 true (.leaf 0 true) (.leaf 1 true))=false := by decide +kernel

end NearCompression
