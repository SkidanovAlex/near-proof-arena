import NearCompression.SHA384SharedInputRouting
import NearCompression.SHA384SharedCalls

namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 NearSpecV3.SHA512
set_option maxRecDepth 65536

/-- Bus5 matching includes ordered callID and blockID, not just block content. -/
theorem sha384_shared_block_receive (f0 f1 : List (Nat × Nat)) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384SharedAir f0 f1) pub tr) {t r : Nat}
    (ht : t<(sha384SharedAir f0 f1).tables.length) (hr : r<tr.height t)
    {i : Interaction} (hi : i∈(sha384SharedAir f0 f1).tables[t]!.interactions)
    (hb : i.bus=5) (hs : i.send=false) (hm : i.multNat tr t r pub≠0) :
    ∃ call,call<2 ∧ ∃ block,block<3 ∧ i.msgVal tr t r pub=
      Fp.ofNat call :: Fp.ofNat block :: (List.range 16).flatMap (fun word =>
        (List.range 4).map (fun limb => (sha384DirectLimb 267 block word limb).eval tr (4+call) 0 pub)) := by
  obtain ⟨u,hu,s,hs',j,hj,bus,send,msg,mult⟩ := sha384_shared_receive_match f0 f1 pub tr h ht hr hi hs hm
  obtain ⟨call,hc,block,hblock,table,interaction⟩ := sha384_shared_input_sender f0 f1 u hu j hj (bus.trans hb) send
  subst u
  subst j
  have row := sha384_shared_sender_row tr pub call block s mult
  subst s
  exact ⟨call,hc,block,hblock,msg.symm.trans (sha384_shared_input_send_eval tr pub call block)⟩

/-- Each call's actual M64 is its own canonical committed input block. -/
theorem sha384_shared_call_M (f0 f1 : List (Nat × Nat)) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384SharedAir f0 f1) pub tr) (call block : Nat) (hc : call<2) (hb : block<3) :
    (List.range 64).map (fun j => tr.cell 3 (3*call+block) (38+j))=
      (List.range 16).flatMap (fun word => (List.range 4).map
        (fun limb => (sha384DirectLimb 267 block word limb).eval tr (4+call) 0 pub)) := by
  have metadata := sha384_call_segment_metadata f0 f1 pub tr h call block hc hb
  let i : Interaction := ⟨5,[.col 2 false],
    [.col 0 false,.add (.col 4 false) (.mul (.const 2) (.col 5 false))] ++ sharedCols 38 64,false⟩
  have hi : i∈(sha384SharedAir f0 f1).tables[3]!.interactions := by simp [i,sha384SharedAir,sha384SharedCalls]
  have hm : i.multNat tr 3 (3*call+block) pub≠0 := by
    simp [i,Interaction.multNat,Interaction.multNat.go,Expr.eval,Expr.evalWith,rowEnv,metadata.2.1]
  have p1 := metadata.2.2.2 1 (by decide)
  have p2 := metadata.2.2.2 2 (by decide)
  have index : tr.cell 3 (3*call+block) 4+Fp.ofNat 2*tr.cell 3 (3*call+block) 5=Fp.ofNat block := by
    change tr.cell 3 (3*call+block) 4=(if 1=block then 1 else 0) at p1
    change tr.cell 3 (3*call+block) 5=(if 2=block then 1 else 0) at p2
    rw [p1,p2]
    have cases : block=0 ∨ block=1 ∨ block=2 := by omega
    rcases cases with rfl | rfl | rfl <;> decide
  have value : i.msgVal tr 3 (3*call+block) pub=
      Fp.ofNat call :: Fp.ofNat block :: (List.range 64).map (fun j => tr.cell 3 (3*call+block) (38+j)) := by
    simp only [i,Interaction.msgVal,List.cons_append,List.nil_append,List.map_cons,sharedCols,List.map_map,Function.comp_def]
    change tr.cell 3 (3*call+block) 0 ::
      (tr.cell 3 (3*call+block) 4+Fp.ofNat 2*tr.cell 3 (3*call+block) 5) :: _ = _
    rw [metadata.2.2.1,index]
    rfl
  obtain ⟨sc,hsc,sb,hsb,msg⟩ := sha384_shared_block_receive f0 f1 pub tr h
    (by simp [sha384SharedAir]) metadata.1 hi rfl rfl hm
  rw [value] at msg
  have eqCall := congrArg Fp.toNat (List.cons.inj msg).1
  rw [Fp.toNat_ofNat,Fp.toNat_ofNat,Nat.mod_eq_of_lt (by unfold P;omega : call<P),
    Nat.mod_eq_of_lt (by unfold P;omega : sc<P)] at eqCall
  subst sc
  have eqBlock := congrArg Fp.toNat (List.cons.inj (List.cons.inj msg).2).1
  rw [Fp.toNat_ofNat,Fp.toNat_ofNat,Nat.mod_eq_of_lt (by unfold P;omega : block<P),
    Nat.mod_eq_of_lt (by unfold P;omega : sb<P)] at eqBlock
  subst sb
  exact (List.cons.inj (List.cons.inj msg).2).2

theorem sha384_shared_call_padded_limbs (f0 f1 : List (Nat × Nat)) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384SharedAir f0 f1) pub tr) (call block : Nat) (hc : call<2) (hb : block<3) :
    (List.range 64).map (fun j => tr.cell 3 (3*call+block) (38+j))=
      (List.range 16).flatMap (fun word => (List.range 4).map (fun limb =>
        Fp.ofNat (256*(pad (sha384SharedMessage pub tr call)).getD (128*block+8*word+6-2*limb) 0+
          (pad (sha384SharedMessage pub tr call)).getD (128*block+8*word+7-2*limb) 0))) := by
  rw [sha384_shared_call_M f0 f1 pub tr h call block hc hb]
  unfold List.flatMap
  congr 1
  apply List.map_congr_left
  intro word hw
  apply List.map_congr_left
  intro limb hl
  exact sha384_shared_direct_limb pub tr call block word limb hb (List.mem_range.mp hw) (List.mem_range.mp hl)

end NearCompression
