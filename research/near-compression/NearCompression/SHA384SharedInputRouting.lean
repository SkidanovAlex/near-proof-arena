import NearCompression.SHA384SharedRouting
import NearCompression.SHA384SharedCore
import NearCompression.SHA384DirectSemantics

namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 NearSpecV3.SHA512
set_option maxRecDepth 65536

def sha384SharedMessage (pub : List Fp) (tr : Trace Fp) (call : Nat) : List Nat :=
  sha384CommittedMessage 267 pub (sha512CombinedProjection tr (4+call) 0)

theorem sha384_shared_input_projection_eval (tr : Trace Fp) (pub : List Fp) (call r : Nat) (e : Expr) :
    e.eval (sha512CombinedProjection tr (4+call) 0) 2 r pub=e.eval tr (4+call) r pub := by
  simp [Expr.eval,rowEnv,sha512CombinedProjection,Trace.height]
  rfl

theorem sha384_shared_message_length (pub : List Fp) (tr : Trace Fp) (call : Nat) :
    (sha384SharedMessage pub tr call).length=267 := sha384_committed_message_length _ _ _

theorem sha384_shared_input_bits (f0 f1 : List (Nat × Nat)) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384SharedAir f0 f1) pub tr) (call r bit : Nat)
    (hc : call<2) (hr : r<tr.height (4+call)) (hb : bit<8*267) :
    (tr.cell (4+call) r bit).toNat≤1 := by
  have ht : 4+call<(sha384SharedAir f0 f1).tables.length := by simp [sha384SharedAir];omega
  have member : instructionBitConstraint bit∈(sha384SharedAir f0 f1).tables[4+call].constraints := by
    have cases : call=0 ∨ call=1 := by omega
    rcases cases with rfl | rfl <;>
      exact List.mem_append_left _ (List.mem_map.mpr ⟨bit,List.mem_range.mpr hb,rfl⟩)
  have eq := h.constr (4+call) (by simp [sha384SharedAir];omega) r hr (instructionBitConstraint bit) member
  change tr.cell (4+call) r bit*(tr.cell (4+call) r bit+ -(1:Fp))=0 at eq
  have cases : tr.cell (4+call) r bit=0 ∨ tr.cell (4+call) r bit=1 := by grind
  rcases cases with z | z <;> rw [z] <;> decide

theorem sha384_shared_message_byte_bound (f0 f1 : List (Nat × Nat)) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384SharedAir f0 f1) pub tr) (call byte : Nat) (hc : call<2) (hb : byte<267) :
    (sha384SharedMessage pub tr call).getD byte 0<256 := by
  rw [sha384SharedMessage,sha384_committed_message_byte _ _ _ byte hb,sha384_shared_input_projection_eval,
    sha384_committed_bitexpr_eval]
  exact instruction_bit_expr_bound _ 8 (8*byte) (by decide)
    (fun k hk => sha384_shared_input_bits f0 f1 pub tr h call 0 (8*byte+k) hc (Nat.two_pow_pos _) (by omega))

theorem sha384_shared_direct_limb (pub : List Fp) (tr : Trace Fp) (call block word limb : Nat)
    (hb : block<3) (hw : word<16) (hl : limb<4) :
    (sha384DirectLimb 267 block word limb).eval tr (4+call) 0 pub=
      Fp.ofNat (256*(pad (sha384SharedMessage pub tr call)).getD (128*block+8*word+6-2*limb) 0+
        (pad (sha384SharedMessage pub tr call)).getD (128*block+8*word+7-2*limb) 0) := by
  have eq := sha384_direct_limb 267 pub (sha512CombinedProjection tr (4+call) 0) block word limb hb hw hl
  rw [sha384_shared_input_projection_eval] at eq
  exact eq

def sharedInputSend (call block : Nat) : Interaction :=
  ⟨5,[.isFirst],[.const call,.const block] ++ (List.range 16).flatMap (fun word =>
    (List.range 4).map (sha384DirectLimb 267 block word)),true⟩

theorem sha384_shared_input_sender (f0 f1 : List (Nat × Nat)) (t : Nat)
    (ht : t<(sha384SharedAir f0 f1).tables.length) (i : Interaction)
    (hi : i∈(sha384SharedAir f0 f1).tables[t]!.interactions) (hb : i.bus=5) (hs : i.send=true) :
    ∃ call,call<2 ∧ ∃ block,block<3 ∧ t=4+call ∧ i=sharedInputSend call block := by
  have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by
    simp only [sha384SharedAir,List.length_cons,List.length_nil] at ht;omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp only [sha384SharedAir,List.getElem!_cons_zero,List.getElem!_cons_succ,
    sha384SharedCore,sha384SharedEndpoint,sha384SharedRecords,sha384SharedCalls,sha384SharedInput,
    List.mem_cons,List.not_mem_nil,or_false] at hi
  · rcases hi with rfl | rfl | rfl <;> simp_all
  · rcases hi with rfl | rfl | rfl <;> simp_all
  · rcases hi with rfl | rfl | rfl | rfl <;> simp_all
  · rcases hi with rfl | rfl <;> simp_all
  · obtain ⟨block,bound,rfl⟩ := List.mem_map.mp hi
    exact ⟨0,by decide,block,List.mem_range.mp bound,rfl,rfl⟩
  · obtain ⟨block,bound,rfl⟩ := List.mem_map.mp hi
    exact ⟨1,by decide,block,List.mem_range.mp bound,rfl,rfl⟩

theorem sha384_shared_sender_row (tr : Trace Fp) (pub : List Fp) (call block r : Nat)
    (hm : (sharedInputSend call block).multNat tr (4+call) r pub≠0) : r=0 := by
  by_cases zero : r=0
  · exact zero
  · simp [sharedInputSend,Interaction.multNat,Interaction.multNat.go,Expr.eval,Expr.evalWith,rowEnv,zero] at hm
    exact False.elim ((by decide : (0:Fp)≠1) hm)

theorem sha384_shared_input_send_eval (tr : Trace Fp) (pub : List Fp) (call block : Nat) :
    (sharedInputSend call block).msgVal tr (4+call) 0 pub=
      Fp.ofNat call :: Fp.ofNat block :: (List.range 16).flatMap (fun word =>
        (List.range 4).map (fun limb => (sha384DirectLimb 267 block word limb).eval tr (4+call) 0 pub)) := by
  simp only [sharedInputSend,Interaction.msgVal,List.cons_append,List.nil_append,List.map_cons,
    List.map_flatMap,List.map_map,Function.comp_def]
  rfl

end NearCompression
