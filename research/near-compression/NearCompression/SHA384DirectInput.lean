import NearCompression.SHA384CommittedInput

/-! A separate committed-input component. Padded words are expressions of the
same input bits, rather than a second trace. Input root authentication remains
an external mandatory verifier interface, not an AIR assumption. -/
namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2

def sha384DirectByte (n i : Nat) : Expr :=
  if i<n then instructionBitExpr (8*i) 8 else .const (sha384PadConstByte n i)

def sha384DirectLimb (n block word limb : Nat) : Expr :=
  .add (.mul (.const 256) (sha384DirectByte n (128*block+8*word+6-2*limb)))
    (sha384DirectByte n (128*block+8*word+7-2*limb))

def sha384DirectInputTable (n : Nat) (fixed : List (Nat × Nat)) : Table := {
  sha384CommittedInputTable n fixed with
  interactions := (List.range (sha384PaddedLength n/128)).map (fun block =>
    ⟨4,[.isFirst],.const block :: (List.range 16).flatMap (fun word =>
      (List.range 4).map (sha384DirectLimb n block word)),true⟩) }

def sha384DirectInputAir (n : Nat) (fixed : List (Nat × Nat)) : AirP := {
  tables := [sha384BatchCoreTable n,sha384EndpointTable n,sha384DirectInputTable n fixed]
  numBuses := 6
  numPub := 88
  maxPub := 88
  pubSegs := [
    {bus:=3,send:=false,width:=48,countAt:=48,start:=0},
    {bus:=5,send:=true,width:=32,countAt:=84,start:=52}] }

end NearCompression
