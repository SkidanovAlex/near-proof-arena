import NearCompression.RecursiveFixedConjunction
import NearCompression.TerminalDAGTotalSemantics
namespace NearCompression
open Lean.Grind ZkFormal.Algebra
variable {K : Type} [Field K]

/-- Exact unsimplified vocabulary emitted by recursive_source_batch_trace.derive. -/
inductive RecursiveSourceExpr where
  | zero
  | input (slot : Nat)
  | binary (op : GKRBinaryOp) (left right : RecursiveSourceExpr)

def recursiveSourceExprEval (values : Nat → K) : RecursiveSourceExpr → K
  | .zero => 0
  | .input i => values i
  | .binary op a b => gkrGateValue op (recursiveSourceExprEval values a) (recursiveSourceExprEval values b)

/-- Structural certificate contains node shapes and edges, not value equalities. -/
inductive RecursiveSourceRoute (nodes : Nat → TerminalDAGNode K) : RecursiveSourceExpr → Nat → Prop where
  | zero {i} : nodes i=.constant 0 → RecursiveSourceRoute nodes .zero i
  | input {i slot} : nodes i=.input slot → RecursiveSourceRoute nodes (.input slot) i
  | binary {op a b ai bi i} : RecursiveSourceRoute nodes a ai → RecursiveSourceRoute nodes b bi →
      nodes i=.binary op ai bi → RecursiveSourceRoute nodes (.binary op a b) i

theorem recursive_source_route_value (nodes : Nat → TerminalDAGNode K)
    (inputs values : Nat → K) (equations : ∀ i,values i=terminalNodeValue inputs values (nodes i))
    (expr : RecursiveSourceExpr) (index : Nat) (route : RecursiveSourceRoute nodes expr index) :
    values index=recursiveSourceExprEval inputs expr := by
  induction route with
  | @zero i h => simpa only [h,terminalNodeValue,recursiveSourceExprEval] using equations i
  | @input i slot h => simpa only [h,terminalNodeValue,recursiveSourceExprEval] using equations i
  | @binary op a b ai bi i _ _ h ih1 ih2 => simpa only [h,terminalNodeValue,recursiveSourceExprEval,ih1,ih2] using equations i

/-- Execution supplies node equations; no oracle/execution equality is assumed. -/
theorem recursive_source_route_executed (nodes : List (TerminalDAGNode K))
    (inputs : Nat → K) (acyclic : TerminalDAGAcyclic 0 nodes)
    (expr : RecursiveSourceExpr) (index : Nat)
    (route : RecursiveSourceRoute (fun i=>nodes.getD i (.constant 0)) expr index) :
    terminalDAGRun inputs 0 (fun _=>0) nodes index=recursiveSourceExprEval inputs expr :=
  recursive_source_route_value _ inputs _ (terminal_dag_total_equations inputs nodes acyclic) expr index route

structure RecursiveSourceBranch where
  slotStart : Nat
  laneCount : Nat
  projection : Option Bool

structure RecursiveSourceQuery where
  branches : List RecursiveSourceBranch
  expectedStart : Nat

def recursiveSourceLaneExpr (start : Nat) (side : Bool) (acc : RecursiveSourceExpr) : Nat → RecursiveSourceExpr
  | 0 => acc
  | n+1 => .binary .add (recursiveSourceLaneExpr start side acc n)
      (.binary .mul (.input (start+3*n)) (.input (start+3*n+(if side then 2 else 1))))

def recursiveSourceLaneValue (values : Nat → K) (start : Nat) (side : Bool) (acc : K) : Nat → K
  | 0 => acc
  | n+1 => recursiveSourceLaneValue values start side acc n+
      values (start+3*n)*values (start+3*n+(if side then 2 else 1))

theorem recursive_source_lane_eval (values : Nat → K) (start : Nat) (side : Bool)
    (acc : RecursiveSourceExpr) (n : Nat) :
    recursiveSourceExprEval values (recursiveSourceLaneExpr start side acc n)=
      recursiveSourceLaneValue values start side (recursiveSourceExprEval values acc) n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [recursiveSourceLaneExpr,recursiveSourceExprEval,gkrGateValue,recursiveSourceLaneValue,ih]

def recursiveSourceBranchExpr (branch : RecursiveSourceBranch) (side : Bool) : RecursiveSourceExpr :=
  recursiveSourceLaneExpr branch.slotStart (branch.projection.getD side) .zero branch.laneCount

def recursiveSourceBranchValue (values : Nat → K) (branch : RecursiveSourceBranch) (side : Bool) : K :=
  recursiveSourceLaneValue values branch.slotStart (branch.projection.getD side) 0 branch.laneCount

def recursiveSourceQueryExpr (side : Bool) (acc : RecursiveSourceExpr) : List RecursiveSourceBranch → RecursiveSourceExpr
  | [] => acc
  | branch::rest => recursiveSourceQueryExpr side (.binary .add acc (recursiveSourceBranchExpr branch side)) rest

def recursiveSourceQueryValue (values : Nat → K) (side : Bool) (acc : K) : List RecursiveSourceBranch → K
  | [] => acc
  | branch::rest => recursiveSourceQueryValue values side (acc+recursiveSourceBranchValue values branch side) rest

theorem recursive_source_query_eval (values : Nat → K) (side : Bool)
    (acc : RecursiveSourceExpr) (branches : List RecursiveSourceBranch) :
    recursiveSourceExprEval values (recursiveSourceQueryExpr side acc branches)=
      recursiveSourceQueryValue values side (recursiveSourceExprEval values acc) branches := by
  induction branches generalizing acc with
  | nil => rfl
  | cons branch rest ih =>
    simp only [recursiveSourceQueryExpr,recursiveSourceQueryValue,ih,recursiveSourceExprEval,gkrGateValue,
      recursiveSourceBranchExpr,recursive_source_lane_eval,recursiveSourceBranchValue]

def recursiveSourceOutputExpr (query : RecursiveSourceQuery) (side : Bool) : RecursiveSourceExpr :=
  .binary .sub (recursiveSourceQueryExpr side .zero query.branches)
    (.input (query.expectedStart+(if side then 1 else 0)))

def recursiveSourceOutputValue (values : Nat → K) (query : RecursiveSourceQuery) (side : Bool) : K :=
  recursiveSourceQueryValue values side 0 query.branches-values (query.expectedStart+(if side then 1 else 0))

theorem recursive_source_output_eval (values : Nat → K) (query : RecursiveSourceQuery) (side : Bool) :
    recursiveSourceExprEval values (recursiveSourceOutputExpr query side)=recursiveSourceOutputValue values query side := by
  simp only [recursiveSourceOutputExpr,recursiveSourceExprEval,gkrGateValue,recursive_source_query_eval,recursiveSourceOutputValue]

/-- Concrete callback on the same whole flat operand vector, after the fold
region. False/true outputs preserve the emitted even/odd ordering. -/
def recursiveSourceProgramPairs (offset : Nat) (queries : List RecursiveSourceQuery)
    (values : Nat → K) : List (K×K) :=
  queries.flatMap (fun q=>[false,true].map (fun side=>
    (recursiveSourceQueryValue (fun i=>values (offset+i)) side 0 q.branches,
      values (offset+q.expectedStart+(if side then 1 else 0)))))

theorem recursive_source_program_length (offset : Nat) (queries : List RecursiveSourceQuery)
    (values : Nat → K) : (recursiveSourceProgramPairs offset queries values).length=2*queries.length := by
  induction queries with
  | nil => rfl
  | cons q qs ih =>
    simp only [recursiveSourceProgramPairs,List.flatMap_cons,List.map_cons,List.map_nil,List.length_append,
      List.length_cons,List.length_nil] at *
    omega

/-- Actual source DAG output, with its input slots shifted into the combined
committed vector. This is the source-evaluator refinement boundary. -/
theorem recursive_source_output_executed (nodes : List (TerminalDAGNode K))
    (offset : Nat) (values : Nat → K) (acyclic : TerminalDAGAcyclic 0 nodes)
    (query : RecursiveSourceQuery) (side : Bool) (index : Nat)
    (route : RecursiveSourceRoute (fun i=>nodes.getD i (.constant 0)) (recursiveSourceOutputExpr query side) index) :
    terminalDAGRun (fun i=>values (offset+i)) 0 (fun _=>0) nodes index=
      recursiveSourceOutputValue (fun i=>values (offset+i)) query side := by
  rw [recursive_source_route_executed nodes _ acyclic _ index route,recursive_source_output_eval]

/-- Sixteen canonical queries discharge the previous32-output interface by
construction, rather than a supplied source callback or count. -/
theorem recursive_source_program_fixed_escape (queries : List RecursiveSourceQuery)
    (queryCount : queries.length=16) (slot : Nat) (values expected : Nat → K)
    (valid : slot<12144) (fixed : ¬recursiveFreeOperand 256 slot)
    (wrong : values slot≠expected slot) (sample : List K) (distinct : sample.Nodup) :
    ArenaCore.Security.count (packedGrid sample 14) (fun point=>recursiveResidualEval 14
      (recursiveSingleRootResiduals 256 12144 values expected (recursiveSourceProgramPairs 1792 queries)) point=0)
      ≤14*sample.length^13 := by
  apply recursive_single_root_same_vector_escape_count slot values expected _ _ valid fixed wrong sample distinct
  rw [recursive_source_program_length,queryCount]


/-- Pair subtraction is exactly the emitted32-output vector, in even/odd order. -/
theorem recursive_source_program_residuals (offset : Nat) (queries : List RecursiveSourceQuery)
    (values : Nat → K) :
    recursiveSourceResiduals (recursiveSourceProgramPairs offset queries values)=
      queries.flatMap (fun q=>[false,true].map
        (fun side=>recursiveSourceOutputValue (fun i=>values (offset+i)) q side)) := by
  induction queries with
  | nil => rfl
  | cons q qs ih =>
    simp only [recursiveSourceResiduals,recursiveSourceProgramPairs,List.flatMap_cons,
      List.map_append,List.map_cons,List.map_nil,recursiveSourceOutputValue] at *
    have same (side : Bool) : values (offset+q.expectedStart+(if side then 1 else 0))=
        values (offset+(q.expectedStart+(if side then 1 else 0))) := by congr 1;omega
    simp only [same]
    rw [ih]
    simp only [Nat.add_assoc]

end NearCompression
