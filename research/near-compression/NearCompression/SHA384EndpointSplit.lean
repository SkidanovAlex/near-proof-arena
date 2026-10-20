import NearCompression.SHA384MultiBlock
import ZkFormal.V2.VerifierDefs

/-! Endpoint-only feed-forward. Core tables execute the existing128-row
constant/schedule/round AIR. One separate table batches eight additions per
active block, with exact tagged routing on four buses. Digest public count
bytes are supplied by the fixed statement adapter. -/
namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 NearSpecV3.SHA512
set_option maxRecDepth 65536

def sha384CoreStateMessage (tag : Nat) (output : Bool) : List Expr :=
  .const tag :: (List.range 8).flatMap (fun i => (List.range 4).map (fun limb =>
    instructionBitExpr ((if output then sha512FeedForwardResultBase i else sha512FeedForwardInputBase i)+16*limb) 16))

def sha384EndpointCoreTable (n block : Nat) : Table := {
  width := 5280
  maxLog := 7
  constraints := sha512ConstantsConstraints ++ (List.range 128).map (sha384BlockByteConstraint n block) ++
    (if block=0 then (List.range 8).flatMap (fun i => (List.range 4).map (sha384IVConstraint i)) else [])
  interactions := [⟨0,[.isFirst],sha384CoreStateMessage block false,true⟩,
    ⟨1,[.col 5231 false],sha384CoreStateMessage block true,true⟩] ++
    (if 0<block then [⟨2,[.isFirst],sha384CoreStateMessage (block-1) false,false⟩] else []) }

def sha384EndpointLimbMessage (offset : Nat) : List Expr :=
  .col 1664 false :: (List.range 8).flatMap (fun i => (List.range 4).map
    (fun limb => .col (208*i+offset+limb) false))

def sha384EndpointDigestMessage : List Expr :=
  (List.range 48).map (fun j => instructionBitExpr (208*(j/8)+144+8*(7-j%8)) 8)

def sha384EndpointLastDiff (n : Nat) : Expr :=
  .add (.col 1664 false) (.neg (.const (sha384PaddedLength n/128-1)))

def sha384EndpointTable (n : Nat) : Table := {
  width := 1668
  maxLog := 22
  constraints := (List.range 8).flatMap (fun i => instructionAdd64Constraints.map (sha512RelocateExpr (208*i))) ++
    [instructionBitConstraint 1665,instructionBitConstraint 1666,
     .mul (.col 1666 false) (sha384EndpointLastDiff n),
     .add (.mul (.col 1667 false) (sha384EndpointLastDiff n))
       (.neg (.add (.const 1) (.neg (.col 1666 false))))]
  interactions := [
    ⟨0,[.col 1665 false],sha384EndpointLimbMessage 0,false⟩,
    ⟨1,[.col 1665 false],sha384EndpointLimbMessage 4,false⟩,
    ⟨2,[.mul (.col 1665 false) (.add (.const 1) (.neg (.col 1666 false)))],sha384EndpointLimbMessage 8,true⟩,
    ⟨3,[.mul (.col 1665 false) (.col 1666 false)],sha384EndpointDigestMessage,true⟩] }

def sha384EndpointAir (n : Nat) : AirP := {
  tables := (List.range (sha384PaddedLength n/128)).map (sha384EndpointCoreTable n) ++ [sha384EndpointTable n]
  numBuses := 4
  numPub := n+52
  maxPub := n+52
  pubSegs := [ {bus := 3,send := false,width := 48,countAt := n+48,start := n} ] }

/-- Core projection retains the existing exact80-round theorem and phase/height
proofs; endpoint routing is an additional, separate semantic composition. -/
theorem sha384_endpoint_core_holds (air : AirP) (tr : Trace Fp) (pub : List Fp)
    (t : Nat) (ht : t<air.tables.length) (n block : Nat)
    (table : air.tables[t]=sha384EndpointCoreTable n block) (holds : HoldsP air pub tr) :
    Holds ⟨[sha512ConstantsTable],0,0⟩ pub (sha512CombinedProjection tr t 0) := by
  constructor
  · intro j hj
    have hz : j=0 := by simpa using hj
    subst j
    have h := holds.logBound t ht
    rw [table] at h
    exact h
  · intro j hj r hr e he
    have hz : j=0 := by simpa using hj
    subst j
    rw [←sha512_combined_relocate_eval,sha512_relocate_zero]
    have hc := holds.constr t ht r hr e
    rw [table] at hc
    exact hc (List.mem_append_left _ (List.mem_append_left _ he))
  · intro j hj r hr i hi
    have hz : j=0 := by simpa using hj
    subst j
    simp [sha512ConstantsTable] at hi
  · intro b m
    simp [busCount,busCount.go,tableBusCount,sha512ConstantsTable]

theorem sha384_endpoint_core_rounds (air : AirP) (tr : Trace Fp) (pub : List Fp)
    (t : Nat) (ht : t<air.tables.length) (n block : Nat)
    (table : air.tables[t]=sha384EndpointCoreTable n block) (holds : HoldsP air pub tr) :
    rounds (sha512CombinedVars (tr.cell t 0)) K (sha512CombinedWindow (tr.cell t 0))=
      sha512CombinedOutput (tr.cell t 79) := by
  have core := sha384_endpoint_core_holds air tr pub t ht n block table holds
  have result := sha512_constants_endpoint _ _ pub 0 (by decide) rfl core
  simpa only [sha512CombinedProjection,Nat.zero_add] using result

theorem sha384_endpoint_add_holds (air : AirP) (tr : Trace Fp) (pub : List Fp)
    (t : Nat) (ht : t<air.tables.length) (n : Nat)
    (table : air.tables[t]=sha384EndpointTable n) (holds : HoldsP air pub tr)
    (r i : Nat) (hr : r<tr.height t) (hi : i<8) :
    instructionAdd64Holds (fun col => tr.cell t r (208*i+col)) := by
  intro e he
  have hc := holds.constr t ht r hr (sha512RelocateExpr (208*i) e)
  rw [table] at hc
  have hv := hc (List.mem_append_left _
    (List.mem_flatMap.mpr ⟨i,List.mem_range.mpr hi,List.mem_map.mpr ⟨e,he,rfl⟩⟩))
  rw [sha512_combined_relocate_eval] at hv
  rw [instruction_local_eval e _ 0 r pub (sha512_current_expr_local e
    (List.all_eq_true.mp sha512_ff_add_local e he))] at hv
  exact hv

theorem sha384_endpoint_add_sound (air : AirP) (tr : Trace Fp) (pub : List Fp)
    (t : Nat) (ht : t<air.tables.length) (n : Nat)
    (table : air.tables[t]=sha384EndpointTable n) (holds : HoldsP air pub tr)
    (r i : Nat) (hr : r<tr.height t) (hi : i<8) :
    add64 (instructionAdd64Word (fun col => tr.cell t r (208*i+col)) 0)
      (instructionAdd64Word (fun col => tr.cell t r (208*i+col)) 4)=
      instructionAdd64Word (fun col => tr.cell t r (208*i+col)) 8 :=
  sha512_add_air_sound _ (sha384_endpoint_add_holds air tr pub t ht n table holds r i hr hi)

theorem sha384_endpoint_last_iff (air : AirP) (tr : Trace Fp) (pub : List Fp)
    (t : Nat) (ht : t<air.tables.length) (n : Nat)
    (table : air.tables[t]=sha384EndpointTable n) (holds : HoldsP air pub tr)
    (r : Nat) (hr : r<tr.height t) :
    tr.cell t r 1666=1 ↔ tr.cell t r 1664=Fp.ofNat (sha384PaddedLength n/128-1) := by
  have constrain (e : Expr) (member : e ∈ (sha384EndpointTable n).constraints) : e.eval tr t r pub=0 := by
    have hc := holds.constr t ht r hr e
    rw [table] at hc
    exact hc member
  have zero := constrain (.mul (.col 1666 false) (sha384EndpointLastDiff n))
    (List.mem_append_right _ (by simp))
  have inverse := constrain (.add (.mul (.col 1667 false) (sha384EndpointLastDiff n))
    (.neg (.add (.const 1) (.neg (.col 1666 false))))) (List.mem_append_right _ (by simp))
  change tr.cell t r 1666*(tr.cell t r 1664 + -Fp.ofNat (sha384PaddedLength n/128-1))=0 at zero
  change tr.cell t r 1667*(tr.cell t r 1664 + -Fp.ofNat (sha384PaddedLength n/128-1))+
    -(1 + -tr.cell t r 1666)=0 at inverse
  constructor <;> intro value <;> grind

end NearCompression
