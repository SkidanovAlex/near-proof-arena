import NearCompression.SHA512Compression
import NearCompression.SHA512Bytes

/-! Public initial state, message block, and compression output as 128 canonical
sixteen-bit limbs. Each 64-bit word uses four little-endian limbs; message
words retain SHA-512's big-endian byte order. -/
namespace NearCompression
set_option maxRecDepth 65536
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Sound ZkFormal.Sha.View NearSpecV3.SHA512

def sha512PublicStateConstraint (i limb : Nat) : Expr :=
  .mul .isFirst (.add (instructionBitExpr (sha512FeedForwardInputBase i+16*limb) 16)
    (.neg (.pub (4*i+limb))))
def sha512PublicMessageConstraint (i limb : Nat) : Expr :=
  .mul .isFirst (.add (instructionBitExpr (sha512ScheduleWindowBase i+16*limb) 16)
    (.neg (.pub (32+4*i+limb))))
def sha512PublicOutputConstraint (i limb : Nat) : Expr :=
  .mul (.col 5231 false) (.add (.col (sha512FeedForwardBase i+8+limb) false)
    (.neg (.pub (96+4*i+limb))))
def sha512PublicStateConstraints : List Expr :=
  (List.range 8).flatMap (fun i => (List.range 4).map (sha512PublicStateConstraint i))
def sha512PublicMessageConstraints : List Expr :=
  (List.range 16).flatMap (fun i => (List.range 4).map (sha512PublicMessageConstraint i))
def sha512PublicOutputConstraints : List Expr :=
  (List.range 8).flatMap (fun i => (List.range 4).map (sha512PublicOutputConstraint i))
def sha512PublicConstraints : List Expr :=
  sha512FeedForwardConstraints ++ sha512PublicStateConstraints ++ sha512PublicMessageConstraints ++
    sha512PublicOutputConstraints

def sha512PublicTable : Table := ⟨6944,sha512PublicConstraints,[],7⟩
def sha512PublicAir : Air := ⟨[sha512PublicTable],0,128⟩
def sha512PublicWord (pub : List Fp) (base : Nat) : Nat :=
  (pub.getD base 0).toNat+65536*(pub.getD (base+1) 0).toNat+
    4294967296*(pub.getD (base+2) 0).toNat+281474976710656*(pub.getD (base+3) 0).toNat
def sha512PublicState (pub : List Fp) : List Nat := (List.range 8).map (fun i => sha512PublicWord pub (4*i))
def sha512PublicOutput (pub : List Fp) : List Nat := (List.range 8).map (fun i => sha512PublicWord pub (96+4*i))

theorem sha512_public_ff_holds (air : Air) (tr : Trace Fp) (pub : List Fp)
    (t : Nat) (ht : t<air.tables.length) (table : air.tables[t]=sha512PublicTable)
    (holds : Holds air pub tr) :
    Holds ⟨[sha512FeedForwardTable],0,0⟩ pub (sha512CombinedProjection tr t 0) := by
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
    exact hc (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ he)))
  · intro j hj r hr i hi
    have hz : j=0 := by simpa using hj
    subst j
    simp [sha512FeedForwardTable] at hi
  · intro b m
    simp [busCount,busCount.go,tableBusCount,sha512FeedForwardTable]

theorem sha512_public_bitexpr_eval (tr : Trace Fp) (pub : List Fp) (t r base n : Nat) :
    (instructionBitExpr base n).eval tr t r pub =
      (instructionBitExpr base n).evalWith (instructionAddEnv (tr.cell t r)) := by
  apply instruction_local_eval
  induction n generalizing base with
  | zero => trivial
  | succ n ih => exact ⟨rfl,⟨trivial,ih (base+1)⟩⟩

theorem sha512_public_state_field (air : Air) (tr : Trace Fp) (pub : List Fp)
    (t : Nat) (ht : t<air.tables.length) (table : air.tables[t]=sha512PublicTable)
    (holds : Holds air pub tr) (i limb : Nat) (hi : i<8) (hl : limb<4) :
    pub.getD (4*i+limb) 0 = (instructionBitExpr (sha512FeedForwardInputBase i+16*limb) 16).evalWith
      (instructionAddEnv (tr.cell t 0)) := by
  have hc := holds.constr t ht 0 (Nat.two_pow_pos _) (sha512PublicStateConstraint i limb)
  rw [table] at hc
  have hv := hc (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
    (List.mem_flatMap.mpr ⟨i,List.mem_range.mpr hi,List.mem_map.mpr ⟨limb,List.mem_range.mpr hl,rfl⟩⟩))))
  change (1 : Fp)*((instructionBitExpr (sha512FeedForwardInputBase i+16*limb) 16).eval tr t 0 pub+
    -pub.getD (4*i+limb) 0)=0 at hv
  rw [sha512_public_bitexpr_eval] at hv
  grind

theorem sha512_public_message_field (air : Air) (tr : Trace Fp) (pub : List Fp)
    (t : Nat) (ht : t<air.tables.length) (table : air.tables[t]=sha512PublicTable)
    (holds : Holds air pub tr) (i limb : Nat) (hi : i<16) (hl : limb<4) :
    pub.getD (32+4*i+limb) 0 = (instructionBitExpr (sha512ScheduleWindowBase i+16*limb) 16).evalWith
      (instructionAddEnv (tr.cell t 0)) := by
  have hc := holds.constr t ht 0 (Nat.two_pow_pos _) (sha512PublicMessageConstraint i limb)
  rw [table] at hc
  have hv := hc (List.mem_append_left _ (List.mem_append_right _
    (List.mem_flatMap.mpr ⟨i,List.mem_range.mpr hi,List.mem_map.mpr ⟨limb,List.mem_range.mpr hl,rfl⟩⟩)))
  change (1 : Fp)*((instructionBitExpr (sha512ScheduleWindowBase i+16*limb) 16).eval tr t 0 pub+
    -pub.getD (32+4*i+limb) 0)=0 at hv
  rw [sha512_public_bitexpr_eval] at hv
  grind

theorem sha512_public_height (air : Air) (tr : Trace Fp) (pub : List Fp)
    (t : Nat) (ht : t<air.tables.length) (table : air.tables[t]=sha512PublicTable)
    (holds : Holds air pub tr) : tr.height t=128 := by
  have ff := sha512_public_ff_holds air tr pub t ht table holds
  have constants := sha512_ff_constants_holds _ _ pub 0 (by decide) rfl ff
  exact sha512_constants_height _ _ pub 0 (by decide) rfl constants

theorem sha512_public_output_field (air : Air) (tr : Trace Fp) (pub : List Fp)
    (t : Nat) (ht : t<air.tables.length) (table : air.tables[t]=sha512PublicTable)
    (holds : Holds air pub tr) (i limb : Nat) (hi : i<8) (hl : limb<4) :
    pub.getD (96+4*i+limb) 0 = tr.cell t 79 (sha512FeedForwardBase i+8+limb) := by
  have height := sha512_public_height air tr pub t ht table holds
  have ff := sha512_public_ff_holds air tr pub t ht table holds
  have constants := sha512_ff_constants_holds _ _ pub 0 (by decide) rfl ff
  have phase := sha512_constants_phase _ _ pub 0 (by decide) rfl constants 79
    (by change 79<tr.height t; omega) 79 (by decide)
  have gate : tr.cell t 79 5231=1 := by simpa only [sha512CombinedProjection,Nat.zero_add,ite_true] using phase
  have hc := holds.constr t ht 79 (by omega) (sha512PublicOutputConstraint i limb)
  rw [table] at hc
  have hv := hc (List.mem_append_right _
    (List.mem_flatMap.mpr ⟨i,List.mem_range.mpr hi,List.mem_map.mpr ⟨limb,List.mem_range.mpr hl,rfl⟩⟩))
  change tr.cell t 79 5231*(tr.cell t 79 (sha512FeedForwardBase i+8+limb)+ -pub.getD (96+4*i+limb) 0)=0 at hv
  rw [gate] at hv
  grind

/-- Exact public-limb decoding relies on a sixteen-bit bound below BabyBear's modulus. -/
theorem sha512_public_limb_decode (row : Nat → Fp) (value : Fp) (source : Nat)
    (bits : ∀ bit,bit<16 → (row (source+bit)).toNat≤1)
    (eq : value=(instructionBitExpr source 16).evalWith (instructionAddEnv row)) :
    value.toNat=ofBits (fun bit => (row (source+bit)).toNat) 16 ∧ value.toNat<65536 := by
  have bound := ofBits_lt bits
  have fieldBound : ofBits (fun bit => (row (source+bit)).toNat) 16<P := by unfold P; omega
  rw [eq,sha512_bit_expr_field,Fp.toNat_ofNat,Nat.mod_eq_of_lt fieldBound]
  exact ⟨rfl,bound⟩

theorem sha512_public_word_decode (row : Nat → Fp) (pub : List Fp) (base source : Nat)
    (bits : ∀ bit,bit<64 → (row (source+bit)).toNat≤1)
    (eq : ∀ limb,limb<4 → pub.getD (base+limb) 0 =
      (instructionBitExpr (source+16*limb) 16).evalWith (instructionAddEnv row)) :
    sha512PublicWord pub base=sha512BitsWord row source ∧
      ∀ limb,limb<4 → (pub.getD (base+limb) 0).toNat<65536 := by
  have limb (i : Nat) (hi : i<4) := sha512_public_limb_decode row (pub.getD (base+i) 0)
    (source+16*i) (fun bit hb => by simpa only [Nat.add_assoc] using bits (16*i+bit) (by omega)) (eq i hi)
  constructor
  · have l0 := (limb 0 (by decide)).1; have l1 := (limb 1 (by decide)).1
    have l2 := (limb 2 (by decide)).1; have l3 := (limb 3 (by decide)).1
    simp only [Nat.add_zero,Nat.mul_zero,Nat.reduceMul] at l0 l1 l2 l3
    rw [sha512_word_bits_split]
    unfold sha512PublicWord
    rw [l0,l1,l2,l3]
  · intro i hi
    exact (limb i hi).2

theorem sha512_public_state_bits (air : Air) (tr : Trace Fp) (pub : List Fp)
    (t : Nat) (ht : t<air.tables.length) (table : air.tables[t]=sha512PublicTable)
    (holds : Holds air pub tr) (i bit : Nat) (hi : i<8) (hb : bit<64) :
    (tr.cell t 0 (sha512FeedForwardInputBase i+bit)).toNat≤1 := by
  have ff := sha512_public_ff_holds air tr pub t ht table holds
  have add := sha512_ff_add_holds _ _ pub 0 (by decide) rfl ff 0 i (Nat.two_pow_pos _) hi
  have bound := sha512_add_word_bit _ add 0 bit (by decide) hb
  have first := sha512_ff_first_bit _ _ pub 0 (by decide) rfl ff i bit hi hb
  have bound' : (tr.cell t 0 (sha512FeedForwardBase i+16+bit)).toNat≤1 := by
    simpa only [sha512CombinedProjection,sha512FeedForwardRow,Nat.zero_add,Nat.mul_zero,
      Nat.add_zero,Nat.add_assoc] using bound
  have first' : tr.cell t 0 (sha512FeedForwardBase i+16+bit)=tr.cell t 0 (sha512FeedForwardInputBase i+bit) := by
    simpa only [sha512CombinedProjection,Nat.zero_add] using first
  rwa [first'] at bound'

theorem sha512_public_message_bits (air : Air) (tr : Trace Fp) (pub : List Fp)
    (t : Nat) (ht : t<air.tables.length) (table : air.tables[t]=sha512PublicTable)
    (holds : Holds air pub tr) (i bit : Nat) (hi : i<16) (hb : bit<64) :
    (tr.cell t 0 (sha512ScheduleWindowBase i+bit)).toNat≤1 := by
  have ff := sha512_public_ff_holds air tr pub t ht table holds
  have constants := sha512_ff_constants_holds _ _ pub 0 (by decide) rfl ff
  have combined := sha512_constants_combined_holds _ _ pub 0 (by decide) rfl constants
  have schedule := sha512_combined_schedule_holds _ _ pub 0 (by decide) rfl combined
  have bound := sha512_window_bit_boolean _ _ pub 0 (by decide) rfl schedule 0 (Nat.two_pow_pos _) i hi bit hb
  simpa only [sha512CombinedProjection,Nat.zero_add] using bound

theorem sha512_public_state_word (air : Air) (tr : Trace Fp) (pub : List Fp)
    (t : Nat) (ht : t<air.tables.length) (table : air.tables[t]=sha512PublicTable)
    (holds : Holds air pub tr) (i : Nat) (hi : i<8) :
    sha512PublicWord pub (4*i)=sha512FeedForwardVarsWord (sha512CombinedVars (tr.cell t 0)) i ∧
      ∀ limb,limb<4 → (pub.getD (4*i+limb) 0).toNat<65536 := by
  have decode := sha512_public_word_decode (tr.cell t 0) pub (4*i) (sha512FeedForwardInputBase i)
    (fun bit hb => sha512_public_state_bits air tr pub t ht table holds i bit hi hb)
    (fun limb hl => sha512_public_state_field air tr pub t ht table holds i limb hi hl)
  have ff := sha512_public_ff_holds air tr pub t ht table holds
  have round := sha512_ff_round_holds _ _ pub 0 (by decide) rfl ff 0 (Nat.two_pow_pos _)
  have round' : sha512RoundHolds (sha512CombinedRoundRow (tr.cell t 0)) := by
    simpa only [sha512CombinedProjection,Nat.zero_add] using round
  exact ⟨decode.1.trans (sha512_ff_input_words _ round' i hi),decode.2⟩

theorem sha512_public_message_word (air : Air) (tr : Trace Fp) (pub : List Fp)
    (t : Nat) (ht : t<air.tables.length) (table : air.tables[t]=sha512PublicTable)
    (holds : Holds air pub tr) (i : Nat) (hi : i<16) :
    sha512PublicWord pub (32+4*i)=sha512ScheduleWindowWord (tr.cell t 0) i ∧
      ∀ limb,limb<4 → (pub.getD (32+4*i+limb) 0).toNat<65536 :=
  sha512_public_word_decode (tr.cell t 0) pub (32+4*i) (sha512ScheduleWindowBase i)
    (fun bit hb => sha512_public_message_bits air tr pub t ht table holds i bit hi hb)
    (fun limb hl => sha512_public_message_field air tr pub t ht table holds i limb hi hl)

theorem sha512_public_output_word (air : Air) (tr : Trace Fp) (pub : List Fp)
    (t : Nat) (ht : t<air.tables.length) (table : air.tables[t]=sha512PublicTable)
    (holds : Holds air pub tr) (i : Nat) (hi : i<8) :
    sha512PublicWord pub (96+4*i)=instructionAdd64Word (sha512FeedForwardRow (tr.cell t 79) i) 8 ∧
      ∀ limb,limb<4 → (pub.getD (96+4*i+limb) 0).toNat<65536 := by
  have field (limb : Nat) (hl : limb<4) := sha512_public_output_field air tr pub t ht table holds i limb hi hl
  constructor
  · have l0 := field 0 (by decide); have l1 := field 1 (by decide)
    have l2 := field 2 (by decide); have l3 := field 3 (by decide)
    simp only [Nat.add_zero] at l0
    unfold sha512PublicWord
    rw [l0,l1,l2,l3]
    simp only [instructionAdd64Word,sha512FeedForwardRow,Nat.add_assoc]
  · intro limb hl
    rw [field limb hl]
    have height := sha512_public_height air tr pub t ht table holds
    have ff := sha512_public_ff_holds air tr pub t ht table holds
    have add := sha512_ff_add_holds _ _ pub 0 (by decide) rfl ff 79 i
      (by change 79<tr.height t; omega) hi
    have bound := instruction_add64_ranges _ add (8+limb) (by omega)
    simpa only [sha512CombinedProjection,sha512FeedForwardRow,Nat.zero_add,Nat.add_assoc] using bound

theorem sha512_public_state_binding (air : Air) (tr : Trace Fp) (pub : List Fp)
    (t : Nat) (ht : t<air.tables.length) (table : air.tables[t]=sha512PublicTable)
    (holds : Holds air pub tr) : sha512PublicState pub=sha512DecodedState (tr.cell t 0) := by
  apply List.map_congr_left
  intro i hi
  exact (sha512_public_state_word air tr pub t ht table holds i (List.mem_range.mp hi)).1

theorem sha512_public_output_binding (air : Air) (tr : Trace Fp) (pub : List Fp)
    (t : Nat) (ht : t<air.tables.length) (table : air.tables[t]=sha512PublicTable)
    (holds : Holds air pub tr) : sha512PublicOutput pub=sha512FeedForwardOutput (tr.cell t 79) := by
  apply List.map_congr_left
  intro i hi
  exact (sha512_public_output_word air tr pub t ht table holds i (List.mem_range.mp hi)).1

def sha512PublicBlock (pub : List Fp) : List Nat :=
  (List.range 16).flatMap (fun i => sha512NatWordBytes (sha512PublicWord pub (32+4*i)))

/-- Public input length is checked in addition to AIR satisfaction: rowEnv uses
getD with a zero default, so Holds alone cannot reject short/extra public lists. -/
def sha512PublicClaim (pub : List Fp) (tr : Trace Fp) : Prop :=
  pub.length=128 ∧ Holds sha512PublicAir pub tr

theorem sha512_public_block_binding (air : Air) (tr : Trace Fp) (pub : List Fp)
    (t : Nat) (ht : t<air.tables.length) (table : air.tables[t]=sha512PublicTable)
    (holds : Holds air pub tr) : sha512PublicBlock pub=sha512DecodedBlock (tr.cell t 0) := by
  have point (i : Nat) (hi : i<16) : sha512NatWordBytes (sha512PublicWord pub (32+4*i)) =
      sha512WindowWordBytes (tr.cell t 0) (sha512ScheduleWindowBase i) := by
    rw [(sha512_public_message_word air tr pub t ht table holds i hi).1]
    exact sha512_nat_word_bytes_bits _ _ (fun bit hb => sha512_public_message_bits air tr pub t ht table holds i bit hi hb)
  have all (indices : List Nat) (hi : ∀ i ∈ indices,i<16) :
      indices.flatMap (fun i => sha512NatWordBytes (sha512PublicWord pub (32+4*i))) =
      indices.flatMap (fun i => sha512WindowWordBytes (tr.cell t 0) (sha512ScheduleWindowBase i)) := by
    induction indices with
    | nil => rfl
    | cons i rest ih =>
      rw [List.flatMap_cons,List.flatMap_cons,point i (hi i (List.mem_cons_self ..)),
        ih (fun j hj => hi j (List.mem_cons_of_mem _ hj))]
  exact all (List.range 16) (fun _ hi => List.mem_range.mp hi)

theorem sha512_public_limb_ranges (air : Air) (tr : Trace Fp) (pub : List Fp)
    (t : Nat) (ht : t<air.tables.length) (table : air.tables[t]=sha512PublicTable)
    (holds : Holds air pub tr) (index : Nat) (hi : index<128) :
    (pub.getD index 0).toNat<65536 := by
  by_cases first : index<32
  · have eq : 4*(index/4)+index%4=index := by omega
    have bound := (sha512_public_state_word air tr pub t ht table holds (index/4) (by omega)).2
      (index%4) (Nat.mod_lt _ (by decide))
    rwa [eq] at bound
  by_cases middle : index<96
  · have eq : 32+4*((index-32)/4)+(index-32)%4=index := by omega
    have bound := (sha512_public_message_word air tr pub t ht table holds ((index-32)/4) (by omega)).2
      ((index-32)%4) (Nat.mod_lt _ (by decide))
    rwa [eq] at bound
  · have eq : 96+4*((index-96)/4)+(index-96)%4=index := by omega
    have bound := (sha512_public_output_word air tr pub t ht table holds ((index-96)/4) (by omega)).2
      ((index-96)%4) (Nat.mod_lt _ (by decide))
    rwa [eq] at bound

theorem sha512_public_word_bound (pub : List Fp) (base : Nat)
    (ranges : ∀ limb,limb<4 → (pub.getD (base+limb) 0).toNat<65536) :
    sha512PublicWord pub base<2^64 := by
  have h0 := ranges 0 (by decide); have h1 := ranges 1 (by decide)
  have h2 := ranges 2 (by decide); have h3 := ranges 3 (by decide)
  simp only [Nat.add_zero] at h0
  unfold sha512PublicWord
  omega

/-- The public claim identifies exact bounded limbs, rather than residues of
arbitrary unbounded external integers. -/
theorem sha512_public_claim_canonical (pub : List Fp) (tr : Trace Fp)
    (claim : sha512PublicClaim pub tr) :
    pub.length=128 ∧ (∀ index,index<128 → (pub.getD index 0).toNat<65536) ∧
      (∀ i,i<32 → sha512PublicWord pub (4*i)<2^64) := by
  refine ⟨claim.1,?_,?_⟩
  · exact sha512_public_limb_ranges sha512PublicAir tr pub 0 (by decide) rfl claim.2
  · intro i hi
    apply sha512_public_word_bound
    intro limb hl
    exact sha512_public_limb_ranges sha512PublicAir tr pub 0 (by decide) rfl claim.2 _ (by omega)

/-- Actual compression of the public state and block equals the public output. -/
theorem sha512_public_compression (pub : List Fp) (tr : Trace Fp)
    (claim : sha512PublicClaim pub tr) :
    sha512PublicOutput pub=compress (sha512PublicState pub) (sha512PublicBlock pub) := by
  rw [sha512_public_output_binding sha512PublicAir tr pub 0 (by decide) rfl claim.2,
    sha512_public_state_binding sha512PublicAir tr pub 0 (by decide) rfl claim.2,
    sha512_public_block_binding sha512PublicAir tr pub 0 (by decide) rfl claim.2]
  have ff := sha512_public_ff_holds sha512PublicAir tr pub 0 (by decide) rfl claim.2
  have result := sha512_compression_sound _ _ pub 0 (by decide) rfl ff
  simpa only [sha512CombinedProjection,Nat.zero_add] using result

theorem sha512_public_block_bytes (pub : List Fp) :
    (sha512PublicBlock pub).length=128 ∧ ∀ byte ∈ sha512PublicBlock pub,byte<256 := by
  constructor
  · simp only [sha512PublicBlock,sha512NatWordBytes,List.length_flatMap,List.length_cons,List.length_nil]
    decide
  · intro byte hb
    obtain ⟨i,hi,hb⟩ := List.mem_flatMap.mp hb
    exact sha512_nat_word_bytes_bound _ byte hb

set_option maxHeartbeats 16000000 in
theorem sha512_public_table_wf : sha512PublicTable.wf sha512PublicAir 3=true := by decide

theorem sha512_public_table_size :
    sha512PublicTable.width=6944 ∧ sha512PublicTable.constraints.length=10469 ∧ sha512PublicAir.numPub=128 := by decide

end NearCompression
