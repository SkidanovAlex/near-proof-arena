import NearCompression.SHA384BatchedCore

/-! Experimental committed-input SHA384 component. The input-table commitment
must be supplied by the caller before Fiat-Shamir challenges. This relation
routes bytes into constrained padding and the batched hash core, but does not
implement the enclosing recursive verifier's input-to-commitment routing. -/
namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2
set_option maxRecDepth 65536

def sha384CommittedInputTable (n : Nat) (fixed : List (Nat × Nat)) : Table := {
  width := 8*n
  maxLog := 1
  constraints := (List.range (8*n)).map instructionBitConstraint ++ fixed.map (fun p =>
    .mul .isFirst (.add (instructionBitExpr (8*p.1) 8) (.neg (.const p.2))))
  interactions := (List.range n).map (fun i => ⟨6,[.isFirst],[.const i,instructionBitExpr (8*i) 8],true⟩) }

def sha384PadSelect (block : Nat) : Expr := .col (1024+block) false

def sha384PadSum (tag : Bool) : Nat → Expr
  | 0 => .const 0
  | k+1 => .add (sha384PadSum tag k)
      (if tag then .mul (.const k) (sha384PadSelect k) else sha384PadSelect k)

def sha384PadConstByte (n i : Nat) : Nat :=
  if i=n then 128 else if sha384PaddedLength n-16≤i then
    (8*n)/256^(sha384PaddedLength n-1-i)%256 else 0

def sha384CommittedPadTable (n : Nat) : Table := {
  width := 1024+sha384PaddedLength n/128
  maxLog := 22
  constraints := (List.range 1024).map instructionBitConstraint ++
    (List.range (sha384PaddedLength n/128)).map (fun b => .mul .isFirst
      (.add (sha384PadSelect b) (.neg (.const (if b=0 then 1 else 0))))) ++
    (List.range (sha384PaddedLength n/128)).map (fun b => .mul .isTransition
      (.add (.col (1024+b) true) (.neg (if b=0 then .const 0 else sha384PadSelect (b-1))))) ++
    (List.range (sha384PaddedLength n/128)).flatMap (fun b => (List.range 128).filterMap (fun j =>
      if 128*b+j<n then none else some (.mul (sha384PadSelect b)
        (.add (instructionBitExpr (8*j) 8) (.neg (.const (sha384PadConstByte n (128*b+j))))))))
  interactions :=
    (List.range (sha384PaddedLength n/128)).flatMap (fun b => (List.range 128).filterMap (fun j =>
      if 128*b+j<n then some ⟨6,[sha384PadSelect b],[.const (128*b+j),instructionBitExpr (8*j) 8],false⟩ else none)) ++
    [⟨4,[sha384PadSum false (sha384PaddedLength n/128)],
      sha384PadSum true (sha384PaddedLength n/128) ::
        (List.range 16).flatMap (fun word => (List.range 4).map (fun limb =>
          .add (.mul (.const 256) (instructionBitExpr (8*(8*word+6-2*limb)) 8))
            (instructionBitExpr (8*(8*word+7-2*limb)) 8))),true⟩] }

def sha384CommittedInputAir (n : Nat) (fixed : List (Nat × Nat)) : AirP := {
  tables := [sha384BatchCoreTable n,sha384EndpointTable n,sha384CommittedInputTable n fixed,sha384CommittedPadTable n]
  numBuses := 7
  numPub := 88
  maxPub := 88
  pubSegs := [
    {bus:=3,send:=false,width:=48,countAt:=48,start:=0},
    {bus:=5,send:=true,width:=32,countAt:=84,start:=52}] }

end NearCompression
