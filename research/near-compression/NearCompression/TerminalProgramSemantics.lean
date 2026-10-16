import NearCompression.TerminalDAGTotalSemantics
namespace NearCompression
open Lean.Grind
variable {K : Type} [Field K]

inductive TerminalOpcode where
  | constant | current | next | first | last | transition | add | sub | mul

def terminalDecodeOpcode : Nat → Option TerminalOpcode
  | 0 => some .constant | 1 => some .current | 2 => some .next
  | 3 => some .first | 4 => some .last | 5 => some .transition
  | 6 => some .add | 7 => some .sub | 8 => some .mul | _ => none

/-- Typed contents of the seven-word ABI. Constant decoding/field embedding is
an explicit caller-supplied partial function, not an assumed integer cast. -/
structure TerminalInstruction (K : Type) where
  opcode : TerminalOpcode
  left : Nat
  right : Nat
  constant : K

def terminalDecodeInstruction (decodeConstant : List Nat → Option K) : List Nat → Option (TerminalInstruction K)
  | [op,x,y,c0,c1,c2,c3] => do
    let code ← terminalDecodeOpcode op
    let constant ← decodeConstant [c0,c1,c2,c3]
    return ⟨code,x,y,constant⟩
  | _ => none

structure TerminalProgramEnvironment (K : Type) where
  current : Nat → K
  next : Nat → K
  first : K
  last : K
  transition : K

def terminalProgramInstructionValue (env : TerminalProgramEnvironment K)
    (registers : Nat → K) (instruction : TerminalInstruction K) : K :=
  match instruction.opcode with
  | .constant => instruction.constant
  | .current => env.current instruction.left
  | .next => env.next instruction.left
  | .first => env.first | .last => env.last | .transition => env.transition
  | .add => registers instruction.left+registers instruction.right
  | .sub => registers instruction.left-registers instruction.right
  | .mul => registers instruction.left*registers instruction.right

/-- Independent program semantics specializes row/selector leaves to values;
this is not the emitted DAG, whose current/next leaves are physical inputs. -/
def terminalProgramNode (env : TerminalProgramEnvironment K) (instruction : TerminalInstruction K) : TerminalDAGNode K :=
  match instruction.opcode with
  | .constant => .constant instruction.constant
  | .current => .constant (env.current instruction.left)
  | .next => .constant (env.next instruction.left)
  | .first => .constant env.first | .last => .constant env.last | .transition => .constant env.transition
  | .add => .binary .add instruction.left instruction.right
  | .sub => .binary .sub instruction.left instruction.right
  | .mul => .binary .mul instruction.left instruction.right

theorem terminal_program_instruction_lower (env : TerminalProgramEnvironment K)
    (registers unusedInputs : Nat → K) (instruction : TerminalInstruction K) :
    terminalNodeValue unusedInputs registers (terminalProgramNode env instruction)=
      terminalProgramInstructionValue env registers instruction := by
  rcases instruction with ⟨code,left,right,constant⟩
  cases code <;> rfl

def terminalProgramRun (env : TerminalProgramEnvironment K) : Nat → (Nat → K) → List (TerminalInstruction K) → (Nat → K)
  | _,registers,[] => registers
  | index,registers,instruction::rest => terminalProgramRun env (index+1)
      (terminalStore registers index (terminalProgramInstructionValue env registers instruction)) rest

theorem terminal_program_run_lower (env : TerminalProgramEnvironment K) (program : List (TerminalInstruction K))
    (index : Nat) (registers : Nat → K) :
    terminalProgramRun env index registers program=
      terminalDAGRun (fun _ => 0) index registers (program.map (terminalProgramNode env)) := by
  induction program generalizing index registers with
  | nil => rfl
  | cons instruction rest ih =>
    simp only [terminalProgramRun,List.map_cons,terminalDAGRun,terminal_program_instruction_lower,ih]

/-- Execution entails register equations for the exact ABI opcode semantics. -/
theorem terminal_program_register_equation (env : TerminalProgramEnvironment K)
    (program : List (TerminalInstruction K))
    (acyclic : TerminalDAGAcyclic 0 (program.map (terminalProgramNode env)))
    (i : Nat) (bound : i<program.length) :
    terminalProgramRun env 0 (fun _ => 0) program i=
      terminalProgramInstructionValue env (terminalProgramRun env 0 (fun _ => 0) program) program[i] := by
  rw [terminal_program_run_lower]
  have h := terminal_dag_node_equation (fun _ => 0) (fun _ => 0)
    (program.map (terminalProgramNode env)) 0 acyclic i (by simpa using bound)
  simpa only [Nat.zero_add,List.getElem_map,terminal_program_instruction_lower] using h
end NearCompression
