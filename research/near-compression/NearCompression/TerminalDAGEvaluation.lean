import NearCompression.GKRLayerTransition
namespace NearCompression
open Lean.Grind
variable {K : Type} [Field K]

/-- Actual terminal compiler node vocabulary. Arithmetic dependencies are
absolute earlier node indices; constants are full challenge-field elements. -/
inductive TerminalDAGNode (K : Type) where
  | constant (value : K)
  | input (slot : Nat)
  | binary (op : GKRBinaryOp) (left right : Nat)

def terminalNodeValue (inputs previous : Nat → K) : TerminalDAGNode K → K
  | .constant value => value
  | .input slot => inputs slot
  | .binary op left right => gkrGateValue op (previous left) (previous right)

def terminalStore (previous : Nat → K) (index : Nat) (value : K) : Nat → K :=
  fun i => if i=index then value else previous i

/-- Sequential node evaluator; index starts at zero in the concrete DAG. -/
def terminalDAGRun (inputs : Nat → K) : Nat → (Nat → K) → List (TerminalDAGNode K) → (Nat → K)
  | _,previous,[] => previous
  | index,previous,node::rest => terminalDAGRun inputs (index+1)
      (terminalStore previous index (terminalNodeValue inputs previous node)) rest

def TerminalNodeBefore (bound : Nat) : TerminalDAGNode K → Prop
  | .constant _ | .input _ => True
  | .binary _ left right => left<bound ∧ right<bound

def TerminalDAGAcyclic : Nat → List (TerminalDAGNode K) → Prop
  | _,[] => True
  | index,node::rest => TerminalNodeBefore index node ∧ TerminalDAGAcyclic (index+1) rest

theorem terminal_dag_preserves_earlier (inputs previous : Nat → K)
    (nodes : List (TerminalDAGNode K)) (index i : Nat) (earlier : i<index) :
    terminalDAGRun inputs index previous nodes i=previous i := by
  induction nodes generalizing index previous with
  | nil => rfl
  | cons node rest ih =>
    rw [terminalDAGRun,ih _ _ (by omega)]
    simp [terminalStore,show i≠index by omega]

theorem terminal_node_value_congr (inputs a b : Nat → K) (node : TerminalDAGNode K) (index : Nat)
    (bounded : TerminalNodeBefore index node) (same : ∀ i,i<index → a i=b i) :
    terminalNodeValue inputs a node=terminalNodeValue inputs b node := by
  cases node with
  | constant v => rfl
  | input slot => rfl
  | binary op left right =>
    simp only [terminalNodeValue,same left bounded.1,same right bounded.2]

/-- Every emitted node satisfies its own equation in the FINAL DAG valuation,
proved from acyclicity and execution, not assumed as circuit correctness. -/
theorem terminal_dag_node_equation (inputs previous : Nat → K)
    (nodes : List (TerminalDAGNode K)) (index : Nat) (acyclic : TerminalDAGAcyclic index nodes)
    (offset : Nat) (bound : offset<nodes.length) :
    let final := terminalDAGRun inputs index previous nodes
    final (index+offset)=terminalNodeValue inputs final nodes[offset] := by
  induction nodes generalizing index previous offset with
  | nil => simp at bound
  | cons node rest ih =>
    cases offset with
    | zero =>
      dsimp only
      simp only [Nat.add_zero,List.getElem_cons_zero]
      have earlier : ∀ i,i<index →
          terminalDAGRun inputs index previous (node::rest) i=previous i :=
        fun i h => terminal_dag_preserves_earlier inputs previous (node::rest) index i h
      rw [terminal_node_value_congr inputs _ previous node index acyclic.1 earlier]
      rw [terminalDAGRun,terminal_dag_preserves_earlier inputs _ rest (index+1) index (by omega)]
      simp [terminalStore]
    | succ offset =>
      have h := ih (previous := terminalStore previous index (terminalNodeValue inputs previous node))
        (index := index+1) acyclic.2 (offset := offset) (by simpa using bound)
      simpa only [terminalDAGRun,List.getElem_cons_succ,Nat.add_assoc,Nat.add_comm 1 offset] using h
end NearCompression
