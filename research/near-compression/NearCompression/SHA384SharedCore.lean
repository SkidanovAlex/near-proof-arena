import NearCompression.SHA384DirectInput
import NearCompression.SHA384BatchedPublic
import Lean

namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 NearSpecV3.SHA512
set_option maxRecDepth 65536

def sharedSub (a b : Expr) : Expr := .add a (.neg b)
def sharedCols (base count : Nat) : List Expr := (List.range count).map (fun i => .col (base+i) false)
def sharedStop (a : Nat) : Expr := .mul (.col a false)
  (.add .isLast (.mul .isTransition (sharedSub (.const 1) (.col a true))))
/-- Canonical nonempty active prefix, unique consecutive IDs and exact last ID. -/
def sharedPrefix (active tag count : Nat) : List Expr := [
  instructionBitConstraint active,
  .mul .isFirst (sharedSub (.col active false) (.const 1)),
  .mul .isFirst (.col tag false),
  .mul .isTransition (.mul (.col active true) (sharedSub (.const 1) (.col active false))),
  .mul .isTransition (.mul (.col active true)
    (sharedSub (.col tag true) (.add (.col tag false) (.const 1)))),
  .mul (sharedStop active) (sharedSub (.col tag false) (.const (count-1)))]

def sha384SharedCore : Table := {
  width := 5234, maxLog := 9
  constraints := sha384BatchCoreConstraints 5
  interactions := [
    ⟨0,[sha384BatchPhase 0],sha384BatchState false,false⟩,
    ⟨1,[sha384BatchPhase 79],sha384BatchState true,true⟩,
    ⟨2,[sha384BatchPhase 0],sha384BatchMessage,false⟩] }

def sha384SharedEndpoint : Table := {
  width := 1666, maxLog := 3
  constraints := (List.range 8).flatMap (fun i => instructionAdd64Constraints.map (sha512RelocateExpr (208*i))) ++
    sharedPrefix 1665 1664 5
  interactions := [
    ⟨0,[.col 1665 false],sha384EndpointLimbMessage 0,false⟩,
    ⟨1,[.col 1665 false],sha384EndpointLimbMessage 4,false⟩,
    ⟨3,[.col 1665 false],sha384EndpointLimbMessage 8 ++ sha384EndpointDigestMessage,true⟩] }

/-- Record layout: nodeID,active,fanout2bits,A32,M64,C32,D48. -/
def sha384SharedRecords : Table := {
  width := 180, maxLog := 3
  constraints := sharedPrefix 1 0 5 ++ [instructionBitConstraint 2,instructionBitConstraint 3,
    .mul (sharedSub (.const 1) (.col 1 false)) (.col 2 false),
    .mul (sharedSub (.const 1) (.col 1 false)) (.col 3 false)]
  interactions := [
    ⟨0,[.const 0,.col 1 false],.col 0 false :: sharedCols 4 32,true⟩,
    ⟨2,[.col 1 false],.col 0 false :: sharedCols 36 64,true⟩,
    ⟨3,[.col 1 false],.col 0 false :: sharedCols 100 80,false⟩,
    ⟨4,[.col 2 false,.col 3 false],.col 0 false :: sharedCols 4 176,true⟩] }

/-- Call layout: callID,nodeID,active,phase3,A32,M64,C32,D48. -/
def sha384SharedCalls : Table := {
  width := 182, maxLog := 3
  constraints :=
    (List.range 3).map (fun i => instructionBitConstraint (3+i)) ++
    (List.range 3).map (fun i => .mul .isFirst (sharedSub (.col (3+i) false) (.const (if i=0 then 1 else 0)))) ++
    (List.range 3).map (fun i => .mul .isTransition
      (sharedSub (.col (3+i) true) (.mul (.col 2 true) (.col (3+(if i=0 then 2 else i-1)) false)))) ++
    [instructionBitConstraint 2,instructionBitConstraint 0,
     .mul .isFirst (sharedSub (.col 2 false) (.const 1)),
     .mul .isFirst (.col 0 false),
     .mul .isTransition (.mul (.col 2 true) (sharedSub (.const 1) (.col 2 false))),
     .mul .isTransition (.mul (.col 2 true)
       (sharedSub (.col 0 true) (.add (.col 0 false) (.col 5 false)))),
     .mul (sharedStop 2) (sharedSub (.col 5 false) (.const 1)),
     .mul (sharedStop 2) (sharedSub (.col 0 false) (.const 1))] ++
    (List.range 32).map (fun i => .mul (.col 3 false)
      (sharedSub (.col (6+i) false) (.const (sha384BatchIVPayload[i]!)))) ++
    (List.range 32).map (fun i => .mul .isTransition
      (.mul (.add (.col 3 false) (.col 4 false))
        (sharedSub (.col (6+i) true) (.col (102+i) false)))) ++
    (List.range 48).map (fun i => .mul (.col 5 false)
      (sharedSub (.col (134+i) false)
        (.add (.mul (sharedSub (.const 1) (.col 0 false)) (.pub i))
          (.mul (.col 0 false) (.pub (48+i))))))
  interactions := [
    ⟨4,[.col 2 false],.col 1 false :: sharedCols 6 176,false⟩,
    ⟨5,[.col 2 false],[.col 0 false,.add (.col 4 false) (.mul (.const 2) (.col 5 false))] ++ sharedCols 38 64,false⟩] }

def sha384SharedInput (call : Nat) (fixed : List (Nat × Nat)) : Table := {
  sha384CommittedInputTable 267 fixed with
  interactions := (List.range 3).map (fun block =>
    ⟨5,[.isFirst],[.const call,.const block] ++ (List.range 16).flatMap (fun word =>
      (List.range 4).map (sha384DirectLimb 267 block word)),true⟩) }

def sha384SharedAir (fixed0 fixed1 : List (Nat × Nat)) : AirP := {
  tables := [sha384SharedCore,sha384SharedEndpoint,sha384SharedRecords,sha384SharedCalls,
    sha384SharedInput 0 fixed0,sha384SharedInput 1 fixed1]
  numBuses := 6,numPub := 96,maxPub := 96,pubSegs := [] }

/-- The shared primitive retains every canonical combined/phase constraint. -/
theorem sha384_shared_core_constraints :
    sha384SharedCore.constraints=sha384BatchCoreConstraints 5 := rfl

/-- Endpoint output limbs and digest bytes come from the same Add64 output bits. -/
theorem sha384_shared_endpoint_constraints :
    sha384SharedEndpoint.constraints=
      (List.range 8).flatMap (fun i => instructionAdd64Constraints.map (sha512RelocateExpr (208*i))) ++
      sharedPrefix 1665 1664 5 := rfl

theorem sha384_shared_constraint (f0 f1 : List (Nat × Nat)) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384SharedAir f0 f1) pub tr) (r : Nat) (hr : r<tr.height 0)
    (e : Expr) (he : e∈sha384BatchCoreConstraints 5) : e.eval tr 0 r pub=0 :=
  h.constr 0 (by simp [sha384SharedAir]) r hr e he

theorem sha384_shared_add_holds (f0 f1 : List (Nat × Nat)) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384SharedAir f0 f1) pub tr) (r i : Nat) (hr : r<tr.height 1) (hi : i<8) :
    instructionAdd64Holds (fun col => tr.cell 1 r (208*i+col)) := by
  intro e he
  have hc := h.constr 1 (by simp [sha384SharedAir]) r hr (sha512RelocateExpr (208*i) e)
  have hv := hc (List.mem_append_left _
    (List.mem_flatMap.mpr ⟨i,List.mem_range.mpr hi,List.mem_map.mpr ⟨e,he,rfl⟩⟩))
  rw [sha512_combined_relocate_eval] at hv
  rw [instruction_local_eval e _ 0 r pub (sha512_current_expr_local e
    (List.all_eq_true.mp sha512_ff_add_local e he))] at hv
  exact hv

theorem sha384_shared_add_sound (f0 f1 : List (Nat × Nat)) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384SharedAir f0 f1) pub tr) (r i : Nat) (hr : r<tr.height 1) (hi : i<8) :
    add64 (instructionAdd64Word (fun col => tr.cell 1 r (208*i+col)) 0)
      (instructionAdd64Word (fun col => tr.cell 1 r (208*i+col)) 4)=
      instructionAdd64Word (fun col => tr.cell 1 r (208*i+col)) 8 :=
  sha512_add_air_sound _ (sha384_shared_add_holds f0 f1 pub tr h r i hr hi)

end NearCompression
