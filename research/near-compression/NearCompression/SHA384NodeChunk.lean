import NearCompression.SHA384SharedCompression
import NearCompression.SHA384SharedPrefix

namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 NearSpecV3.SHA512
set_option maxRecDepth 65536

def chunkLog (n : Nat) : Nat := ((List.range 14).find? (fun l => n<2^l)).getD 14

def chunkGlobal (base : Nat) (message : List Expr) : List Expr :=
  .add (.const base) (message.headD (.const 0)) :: message.drop 1

def sha384NodeChunkAir (base count fanoutBits uses : Nat) : AirP :=
  let data := 2+fanoutBits
  let core : Table := {sha384SharedCore with
    maxLog := chunkLog (80*count)
    constraints:=sha384BatchCoreConstraints count
    interactions:=[
      ⟨0,[sha384BatchPhase 0],chunkGlobal base (sha384BatchState false),false⟩,
      ⟨1,[sha384BatchPhase 79],chunkGlobal base (sha384BatchState true),true⟩,
      ⟨2,[sha384BatchPhase 0],chunkGlobal base sha384BatchMessage,false⟩]}
  let endpoint : Table := {sha384SharedEndpoint with
    maxLog := chunkLog count
    constraints:=(List.range 8).flatMap (fun i=>instructionAdd64Constraints.map (sha512RelocateExpr (208*i))) ++ sharedPrefix 1665 1664 count
    interactions:=[
      ⟨0,[.col 1665 false],chunkGlobal base (sha384EndpointLimbMessage 0),false⟩,
      ⟨1,[.col 1665 false],chunkGlobal base (sha384EndpointLimbMessage 4),false⟩,
      ⟨3,[.col 1665 false],chunkGlobal base (sha384EndpointLimbMessage 8 ++ sha384EndpointDigestMessage),true⟩]}
  let records : Table := {
    width := data+176
    maxLog := chunkLog count
    constraints:=sharedPrefix 1 0 count ++ (List.range fanoutBits).flatMap (fun b=>
      [instructionBitConstraint (2+b),.mul (sharedSub (.const 1) (.col 1 false)) (.col (2+b) false)])
    interactions:=[
      ⟨0,[.const 0,.col 1 false],chunkGlobal base (.col 0 false::sharedCols data 32),true⟩,
      ⟨2,[.col 1 false],chunkGlobal base (.col 0 false::sharedCols (data+32) 64),true⟩,
      ⟨3,[.col 1 false],chunkGlobal base (.col 0 false::sharedCols (data+96) 80),false⟩,
      ⟨4,(List.range fanoutBits).map (fun b=>.col (2+b) false),chunkGlobal base (.col 0 false::sharedCols data 176),true⟩]}
  let useTable : Table := {
    width := 179
    maxLog := chunkLog uses
    constraints:=sharedPrefix 1 0 uses
    interactions:=[⟨4,[.col 1 false],sharedCols 2 177,false⟩]}
  {tables:=[core,endpoint,records,useTable],numBuses:=5,numPub:=0,maxPub:=0,pubSegs:=[]}

/-- Bounded renderer log, even for configurations outside the executable profile. -/
theorem chunk_log_bound (n : Nat) : chunkLog n≤14 := by
  unfold chunkLog
  cases eq : (List.range 14).find? (fun l => decide (n<2^l)) with
  | none => simp
  | some l =>
    have mem := List.mem_of_find?_eq_some eq
    have bound := List.mem_range.mp mem
    simp only [Option.getD_some]
    omega

theorem sha384_chunk_height_small (base count bits uses : Nat) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384NodeChunkAir base count bits uses) pub tr) (t : Nat) (ht : t<4) : tr.height t<P := by
  have log := h.logBound t (by simpa [sha384NodeChunkAir] using ht)
  have upper : tr.log t≤14 := by
    have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 := by omega
    have b0 := chunk_log_bound (80*count)
    have b1 := chunk_log_bound count
    have b3 := chunk_log_bound uses
    rcases cases with rfl | rfl | rfl | rfl
    all_goals simp [sha384NodeChunkAir] at log
    all_goals omega
  have power := Nat.pow_le_pow_right (by decide : 0<2) upper
  change 2^tr.log t<P
  unfold P
  omega

theorem sha384_chunk_core_local (base count bits uses : Nat) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384NodeChunkAir base count bits uses) pub tr) (positive : 0<count) :
    SHA384CoreLocal count pub tr := by
  refine ⟨positive,?_,?_⟩
  · have log := h.logBound 0 (by simp [sha384NodeChunkAir])
    change 1≤tr.log 0 ∧ tr.log 0≤chunkLog (80*count) at log
    have upper := chunk_log_bound (80*count)
    omega
  · intro r hr e he
    exact h.constr 0 (by simp [sha384NodeChunkAir]) r hr e he

theorem sha384_chunk_record_prefix (base count bits uses : Nat) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384NodeChunkAir base count bits uses) pub tr) (positive : 0<count) (small : count<P) :
    SharedPrefixLocal count 1 0 2 pub tr := by
  refine ⟨positive,small,sha384_chunk_height_small base count bits uses pub tr h 2 (by decide),?_⟩
  intro r hr e he
  exact h.constr 2 (by simp [sha384NodeChunkAir]) r hr e (List.mem_append_left _ he)

theorem sha384_chunk_endpoint_prefix (base count bits uses : Nat) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384NodeChunkAir base count bits uses) pub tr) (positive : 0<count) (small : count<P) :
    SharedPrefixLocal count 1665 1664 1 pub tr := by
  refine ⟨positive,small,sha384_chunk_height_small base count bits uses pub tr h 1 (by decide),?_⟩
  intro r hr e he
  exact h.constr 1 (by simp [sha384NodeChunkAir]) r hr e (List.mem_append_right _ he)

theorem sha384_chunk_use_prefix (base count bits uses : Nat) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384NodeChunkAir base count bits uses) pub tr) (positive : 0<uses) (small : uses<P) :
    SharedPrefixLocal uses 1 0 3 pub tr := by
  refine ⟨positive,small,sha384_chunk_height_small base count bits uses pub tr h 3 (by decide),?_⟩
  intro r hr e he
  exact h.constr 3 (by simp [sha384NodeChunkAir]) r hr e he
theorem sha384_chunk_add_holds (base count bits uses : Nat) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384NodeChunkAir base count bits uses) pub tr) (r i : Nat) (hr : r<tr.height 1) (hi : i<8) :
    instructionAdd64Holds (fun col => tr.cell 1 r (208*i+col)) := by
  intro e he
  have hc := h.constr 1 (by simp [sha384NodeChunkAir]) r hr (sha512RelocateExpr (208*i) e)
  have hv := hc (List.mem_append_left _
    (List.mem_flatMap.mpr ⟨i,List.mem_range.mpr hi,List.mem_map.mpr ⟨e,he,rfl⟩⟩))
  rw [sha512_combined_relocate_eval] at hv
  rw [instruction_local_eval e _ 0 r pub (sha512_current_expr_local e
    (List.all_eq_true.mp sha512_ff_add_local e he))] at hv
  exact hv

theorem sha384_chunk_add_sound (base count bits uses : Nat) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384NodeChunkAir base count bits uses) pub tr) (r i : Nat) (hr : r<tr.height 1) (hi : i<8) :
    add64 (instructionAdd64Word (fun col => tr.cell 1 r (208*i+col)) 0)
      (instructionAdd64Word (fun col => tr.cell 1 r (208*i+col)) 4)=
      instructionAdd64Word (fun col => tr.cell 1 r (208*i+col)) 8 :=
  sha512_add_air_sound _ (sha384_chunk_add_holds base count bits uses pub tr h r i hr hi)


end NearCompression
