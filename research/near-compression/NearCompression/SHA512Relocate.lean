import NearCompression.InstructionAdd

namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra

/-- Relocate all columns when embedding a gadget in a wider row. -/
def sha512RelocateExpr (offset : Nat) : Expr → Expr
  | .const n => .const n
  | .col c nx => .col (offset + c) nx
  | .pub i => .pub i
  | .isFirst => .isFirst
  | .isLast => .isLast
  | .isTransition => .isTransition
  | .add a b => .add (sha512RelocateExpr offset a) (sha512RelocateExpr offset b)
  | .mul a b => .mul (sha512RelocateExpr offset a) (sha512RelocateExpr offset b)
  | .neg a => .neg (sha512RelocateExpr offset a)

theorem sha512_relocate_eval (offset : Nat) (e : Expr) (row : Nat → Fp) :
    (sha512RelocateExpr offset e).evalWith (instructionAddEnv row) =
      e.evalWith (instructionAddEnv (fun c => row (offset + c))) := by
  induction e <;> simp_all [sha512RelocateExpr, Expr.evalWith, instructionAddEnv]

end NearCompression
