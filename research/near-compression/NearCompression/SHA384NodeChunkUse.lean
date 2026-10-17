import NearCompression.SHA384NodeChunkDecode
import NearCompression.SHA384SharedCallRecords
namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 NearSpecV3.SHA512
set_option maxRecDepth 65536

/-- Every active use is tied to one bounded, uniquely indexed record. -/
theorem sha384_chunk_use_cells (base count bits uses : Nat) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384NodeChunkAir base count bits uses) pub tr) (positive : 0<count) (small : count<P)
    (r : Nat) (hr : r<tr.height 3) (active : tr.cell 3 r 1=1) :
    ∃ node,node<count ∧ Fp.ofNat base+Fp.ofNat node=tr.cell 3 r 2 ∧
      ∀ j,j<176 → tr.cell 3 r (3+j)=tr.cell 2 node (2+bits+j) := by
  obtain ⟨node,hn,on,tag,values⟩ := sha384_chunk_use_record base count bits uses pub tr h r hr active
  have pf := sha384_chunk_record_prefix base count bits uses pub tr h positive small
  have bound := shared_prefix_bounded pf node hn on
  rw [shared_prefix_tag pf node hn on] at tag
  refine ⟨node,bound,tag,?_⟩
  intro j hj
  have eq := congrArg (fun xs : List Fp=>xs.getD j 0) values
  simpa [List.getD,hj] using eq.symm

/-- Full512-bit input/output state and full128-byte block word vectors transfer
without truncation. The D48 byte vector is retained separately. -/
theorem sha384_chunk_use_words (base count bits uses : Nat) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384NodeChunkAir base count bits uses) pub tr) (positive : 0<count) (small : count<P)
    (r : Nat) (hr : r<tr.height 3) (active : tr.cell 3 r 1=1) :
    ∃ node,node<count ∧ Fp.ofNat base+Fp.ofNat node=tr.cell 3 r 2 ∧
      sharedFlatWords (tr.cell 3 r) 3 8=sharedFlatWords (tr.cell 2 node) (2+bits) 8 ∧
      sharedFlatWords (tr.cell 3 r) 35 16=sharedFlatWords (tr.cell 2 node) (2+bits+32) 16 ∧
      sharedFlatWords (tr.cell 3 r) 99 8=sharedFlatWords (tr.cell 2 node) (2+bits+96) 8 ∧
      (List.range 48).map (fun j=>(tr.cell 3 r (131+j)).toNat)=
        (List.range 48).map (fun j=>(tr.cell 2 node (2+bits+128+j)).toNat) := by
  obtain ⟨node,hn,tag,cells⟩ := sha384_chunk_use_cells base count bits uses pub tr h positive small r hr active
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
    have eq := cells (128+j) (by have bound:=List.mem_range.mp hj;omega)
    simpa only [←Nat.add_assoc] using congrArg Fp.toNat eq

theorem sha384_chunk_block_byte_bound (base count bits uses : Nat) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384NodeChunkAir base count bits uses) pub tr) (positive : 0<count) (small : count<P)
    (node : Nat) (hn : node<count) (byte : Nat) (hb : byte∈sha512DecodedBlock (tr.cell 0 (80*node))) : byte<256 := by
  obtain ⟨word,hw,hbyte⟩ := List.mem_flatMap.mp hb
  exact sha512_word_bytes_bound _ _
    (fun bit hbit=>sha384_chunk_message_bits base count bits uses pub tr h positive small node word bit hn
      (List.mem_range.mp hw) hbit) byte hbyte

/-- Semantic compression certificate for an actual active use row. The no-wrap
condition is explicit and only concerns the natural global ID interpretation. -/
theorem sha384_chunk_active_use_sound (base count bits uses : Nat) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384NodeChunkAir base count bits uses) pub tr) (positive : 0<count) (small : count<P)
    (nowrap : base+count≤P) (r : Nat) (hr : r<tr.height 3) (active : tr.cell 3 r 1=1) :
    ∃ node,node<count ∧ (tr.cell 3 r 2).toNat=base+node ∧
      ∃ block : List Nat,block.length=128 ∧ (∀ byte,byte∈block → byte<256) ∧
        sharedFlatWords (tr.cell 3 r) 3 8=sha512DecodedState (tr.cell 0 (80*node)) ∧
        sharedFlatWords (tr.cell 3 r) 35 16=words block ∧
        sharedFlatWords (tr.cell 3 r) 99 8=compress (sharedFlatWords (tr.cell 3 r) 3 8) block ∧
        ((digestBytes (sharedFlatWords (tr.cell 3 r) 99 8)).take 48).map UInt8.toNat=
          (List.range 48).map (fun j=>(tr.cell 3 r (131+j)).toNat) := by
  obtain ⟨node,hn,tag,a,m,c,d⟩ := sha384_chunk_use_words base count bits uses pub tr h positive small r hr active
  have cast : Fp.ofNat (base+node)=Fp.ofNat base+Fp.ofNat node := Lean.Grind.Semiring.natCast_add _ _
  have id := congrArg Fp.toNat (tag.symm.trans cast.symm)
  rw [Fp.toNat_ofNat,Nat.mod_eq_of_lt (by omega : base+node<P)] at id
  have aa := a.trans (sha384_chunk_record_A_words base count bits uses pub tr h positive small node hn)
  have mm := m.trans (sha384_chunk_record_M_words base count bits uses pub tr h positive small node hn)
  have cc := c.trans (sha384_chunk_record_C_words base count bits uses pub tr h positive small node hn)
  refine ⟨node,hn,id,sha512DecodedBlock (tr.cell 0 (80*node)),sha512_decoded_block_length _,
    sha384_chunk_block_byte_bound base count bits uses pub tr h positive small node hn,aa,mm,?_,?_⟩
  · rw [aa]
    exact cc
  · rw [c,sha384_chunk_record_D_bytes base count bits uses pub tr h positive small node hn,d]

/-- Declared use rows need no caller-supplied activity or routing premise. Exact
active-prefix constraints derive both row availability and its active selector. -/
theorem sha384_chunk_declared_use_sound (base count bits uses : Nat) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384NodeChunkAir base count bits uses) pub tr) (positive : 0<count) (small : count<P)
    (nowrap : base+count≤P) (useSmall : uses<P) (r : Nat) (hr : r<uses) :
    ∃ node,node<count ∧ (tr.cell 3 r 2).toNat=base+node ∧
      ∃ block : List Nat,block.length=128 ∧ (∀ byte,byte∈block → byte<256) ∧
        sharedFlatWords (tr.cell 3 r) 3 8=sha512DecodedState (tr.cell 0 (80*node)) ∧
        sharedFlatWords (tr.cell 3 r) 35 16=words block ∧
        sharedFlatWords (tr.cell 3 r) 99 8=compress (sharedFlatWords (tr.cell 3 r) 3 8) block ∧
        ((digestBytes (sharedFlatWords (tr.cell 3 r) 99 8)).take 48).map UInt8.toNat=
          (List.range 48).map (fun j=>(tr.cell 3 r (131+j)).toNat) := by
  have pf := sha384_chunk_use_prefix base count bits uses pub tr h (by omega) useSmall
  have cap := shared_prefix_capacity pf
  exact sha384_chunk_active_use_sound base count bits uses pub tr h positive small nowrap r (by omega)
    (shared_prefix_required pf r (by omega) hr)

end NearCompression
