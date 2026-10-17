import NearCompression.SHA384EndpointSplit

/-! Experimental batched core relation. Public payload expansion is a separate
verifier-derived wrapper. Full reset/phase/routing refinement is not yet proved.
The existing endpoint profile and its semantics remain unchanged. -/
namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 NearSpecV3.SHA512

def sha384BatchActive : Expr := .col 5232 false
def sha384BatchTag : Expr := .col 5233 false
def sha384BatchPhase (i : Nat) : Expr := .col (5152+i) false
def sha384BatchContinue : Expr := .mul .isTransition (.add (.const 1) (.neg (sha384BatchPhase 79)))

/-- Only original transition selectors are replaced. All original constraints
are retained, with an outer active gate. No current/next column is remapped. -/
def sha384BatchGate : Expr → Expr
  | .isTransition => sha384BatchContinue
  | .add a b => .add (sha384BatchGate a) (sha384BatchGate b)
  | .mul a b => .mul (sha384BatchGate a) (sha384BatchGate b)
  | .neg a => .neg (sha384BatchGate a)
  | e => e

def sha384BatchStop : Expr := .mul sha384BatchActive
  (.add .isLast (.mul .isTransition (.add (.const 1) (.neg (.col 5232 true)))))

def sha384BatchCoreConstraints (blocks : Nat) : List Expr :=
  sha512CombinedConstraints.map (fun e => .mul sha384BatchActive (sha384BatchGate e)) ++
  (List.range 80).map (fun i => .mul .isFirst
    (.add (sha384BatchPhase i) (.neg (.const (if i=0 then 1 else 0))))) ++
  (List.range 80).map (fun i => .mul .isTransition
    (.add (.col (5152+i) true) (.neg (.mul (.col 5232 true) (sha384BatchPhase (if i=0 then 79 else i-1)))))) ++
  (List.range 80).map (fun i => instructionBitConstraint (5152+i)) ++
  (List.range 4).map (fun limb => .mul sha384BatchActive
    (.add (.col (4116+limb) false) (.neg (sha512ConstantSum limb 80)))) ++
  [instructionBitConstraint 5232,
   .mul .isFirst (.add sha384BatchActive (.neg (.const 1))),
   .mul .isFirst sha384BatchTag,
   .mul .isTransition (.mul (.col 5232 true) (.add (.const 1) (.neg sha384BatchActive))),
   .mul .isTransition (.mul (.col 5232 true)
     (.add (.col 5233 true) (.neg (.add sha384BatchTag (sha384BatchPhase 79))))),
   .mul sha384BatchStop (.add (sha384BatchPhase 79) (.neg (.const 1))),
   .mul sha384BatchStop (.add sha384BatchTag (.neg (.const (blocks-1))))]

def sha384BatchState (output : Bool) (previous : Bool := false) : List Expr :=
  (if previous then .add sha384BatchTag (.neg (.const 1)) else sha384BatchTag) ::
  (sha384CoreStateMessage 0 output).tail

def sha384BatchMessage : List Expr := sha384BatchTag ::
  (List.range 16).flatMap (fun i => (List.range 4).map (fun limb =>
    instructionBitExpr (sha512ScheduleWindowBase i+16*limb) 16))

def sha384BatchCoreTable (n : Nat) : Table := {
  width := 5234
  maxLog := 22
  constraints := sha384BatchCoreConstraints (sha384PaddedLength n/128)
  interactions := [
    ⟨0,[sha384BatchPhase 0],sha384BatchState false,true⟩,
    ⟨1,[sha384BatchPhase 79],sha384BatchState true,true⟩,
    ⟨2,[.mul (sha384BatchPhase 0) (.add (.const 1) (.neg .isFirst))],sha384BatchState false true,false⟩,
    ⟨4,[sha384BatchPhase 0],sha384BatchMessage,false⟩,
    ⟨5,[.isFirst],(sha384CoreStateMessage 0 false).tail,false⟩] }

def sha384BatchedAir (n : Nat) : AirP := {
  tables := [sha384BatchCoreTable n,sha384EndpointTable n]
  numBuses := 6
  numPub := n+92+64*(sha384PaddedLength n/128)
  maxPub := n+92+64*(sha384PaddedLength n/128)
  pubSegs := [
    {bus:=3,send:=false,width:=48,countAt:=n+48,start:=n},
    {bus:=4,send:=true,width:=64,countAt:=n+52+64*(sha384PaddedLength n/128),start:=n+52,indexBase:=some 0},
    {bus:=5,send:=true,width:=32,countAt:=n+88+64*(sha384PaddedLength n/128),start:=n+56+64*(sha384PaddedLength n/128)}] }

end NearCompression
