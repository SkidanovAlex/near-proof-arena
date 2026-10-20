import NearCompression.SHA384SharedDecode

namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 NearSpecV3.SHA512
set_option maxRecDepth 65536

/-- Transport exact limbs; all four16-bit limbs of every word are retained. -/
theorem shared_flat_words_transfer (a b : Nat → Fp) (left right words : Nat)
    (cells : ∀ j,j<4*words → a (left+j)=b (right+j)) :
    sharedFlatWords a left words=sharedFlatWords b right words := by
  unfold sharedFlatWords
  apply List.map_congr_left
  intro word hw
  have bound := List.mem_range.mp hw
  unfold instructionAdd64Word
  simp only [Nat.add_assoc]
  rw [cells (4*word) (by omega),cells (4*word+1) (by omega),
    cells (4*word+2) (by omega),cells (4*word+3) (by omega)]

/-- Every active call row names a bounded unique certified record and preserves
all of A32/M64/C32/D48 coordinate-by-coordinate. -/
theorem sha384_shared_call_record_cells (f0 f1 : List (Nat × Nat)) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384SharedAir f0 f1) pub tr) (r : Nat) (hr : r<tr.height 3)
    (active : tr.cell 3 r 2=1) :
    ∃ node,node<5 ∧ tr.cell 3 r 1=Fp.ofNat node ∧
      ∀ j,j<176 → tr.cell 3 r (6+j)=tr.cell 2 node (4+j) := by
  obtain ⟨node,hn,on,tag,values⟩ := sha384_shared_call_record f0 f1 pub tr h r hr active
  have pf := sha384_shared_record_prefix f0 f1 pub tr h
  have bound := shared_prefix_bounded pf node hn on
  have nodeTag := shared_prefix_tag pf node hn on
  refine ⟨node,bound,tag.symm.trans nodeTag,?_⟩
  intro j hj
  have eq := congrArg (fun xs : List Fp => xs.getD j 0) values
  simpa [List.getD,hj] using eq.symm

/-- Fixed field equality uniquely identifies the bounded node. -/
theorem sha384_shared_node_tag_unique (r : Nat) (tr : Trace Fp) (a b : Nat)
    (ha : a<5) (hb : b<5) (atag : tr.cell 3 r 1=Fp.ofNat a) (btag : tr.cell 3 r 1=Fp.ofNat b) : a=b := by
  have eq := congrArg Fp.toNat (atag.symm.trans btag)
  simpa only [Fp.toNat_ofNat,Nat.mod_eq_of_lt (by unfold P;omega : a<P),
    Nat.mod_eq_of_lt (by unfold P;omega : b<P)] using eq

/-- One matching record supplies all three full-width word vectors and digest. -/
theorem sha384_shared_call_word_vectors (f0 f1 : List (Nat × Nat)) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384SharedAir f0 f1) pub tr) (r : Nat) (hr : r<tr.height 3)
    (active : tr.cell 3 r 2=1) :
    ∃ node,node<5 ∧ tr.cell 3 r 1=Fp.ofNat node ∧
      sharedFlatWords (tr.cell 3 r) 6 8=sharedFlatWords (tr.cell 2 node) 4 8 ∧
      sharedFlatWords (tr.cell 3 r) 38 16=sharedFlatWords (tr.cell 2 node) 36 16 ∧
      sharedFlatWords (tr.cell 3 r) 102 8=sharedFlatWords (tr.cell 2 node) 100 8 ∧
      (List.range 48).map (fun j => (tr.cell 3 r (134+j)).toNat)=
        (List.range 48).map (fun j => (tr.cell 2 node (132+j)).toNat) := by
  obtain ⟨node,hn,tag,cells⟩ := sha384_shared_call_record_cells f0 f1 pub tr h r hr active
  refine ⟨node,hn,tag,?_,?_,?_,?_⟩
  · apply shared_flat_words_transfer
    intro j hj
    exact cells j (by omega)
  · apply shared_flat_words_transfer
    intro j hj
    simpa only [←Nat.add_assoc] using cells (32+j) (by omega)
  · apply shared_flat_words_transfer
    intro j hj
    simpa only [←Nat.add_assoc] using cells (96+j) (by omega)
  · apply List.map_congr_left
    intro j hj
    have eq := cells (128+j) (by have jb:=List.mem_range.mp hj;omega)
    simpa only [←Nat.add_assoc] using congrArg Fp.toNat eq

/-- The call's full C state is the actual independent-node compression result. -/
theorem sha384_shared_call_output (f0 f1 : List (Nat × Nat)) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384SharedAir f0 f1) pub tr) (r : Nat) (hr : r<tr.height 3)
    (active : tr.cell 3 r 2=1) :
    ∃ node,node<5 ∧ tr.cell 3 r 1=Fp.ofNat node ∧
      sharedFlatWords (tr.cell 3 r) 102 8=sha384BatchCompression tr node ∧
      ((digestBytes (sharedFlatWords (tr.cell 3 r) 102 8)).take 48).map UInt8.toNat=
        (List.range 48).map (fun j => (tr.cell 3 r (134+j)).toNat) := by
  obtain ⟨node,hn,tag,a,m,c,d⟩ := sha384_shared_call_word_vectors f0 f1 pub tr h r hr active
  refine ⟨node,hn,tag,c.trans (sha384_shared_record_C_words f0 f1 pub tr h node hn),?_⟩
  rw [c,sha384_shared_record_D_bytes f0 f1 pub tr h node hn,d]

end NearCompression
