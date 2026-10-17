import NearCompression.SHA384ChunkCallCheck
namespace NearCompression
open Lean.Grind ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 NearSpecV3.SHA512

/-- Little-endian sixteen-bit limbs used by the Python call compiler. -/
def callWordLimb (word limb : Nat) : Fp := Fp.ofNat (word/65536^limb%65536)

theorem call_word_limb_nat (word limb : Nat) :
    (callWordLimb word limb).toNat=word/65536^limb%65536 := by
  rw [callWordLimb,Fp.toNat_ofNat]
  apply Nat.mod_eq_of_lt
  have bound := Nat.mod_lt (word/65536^limb) (by decide : 0<65536)
  unfold P
  omega

/-- Canonical64-bit constants are recovered exactly; field reduction cannot
change any of their sixteen-bit limbs. -/
theorem call_word_limbs_decode (word : Nat) (bound : word<2^64) :
    instructionAdd64Word (callWordLimb word) 0=word := by
  simp only [instructionAdd64Word,Nat.zero_add,call_word_limb_nat]
  simp only [Nat.pow_succ,Nat.pow_zero,Nat.div_one] at *
  omega

/-- Literal constant-limb equations recover every expected word. -/
theorem call_constant_limbs_words (row : Nat→Fp) (base : Nat) (expected : List Nat)
    (bounded : ∀ w,w∈expected → w<2^64)
    (cells : ∀ i,i<expected.length → ∀ j,j<4 →
      row (base+4*i+j)=callWordLimb (expected.getD i 0) j) :
    sharedFlatWords row base expected.length=expected := by
  have word (i : Nat) (hi : i<expected.length) :
      instructionAdd64Word row (base+4*i)=expected.getD i 0 := by
    have small : expected.getD i 0<2^64 := by
      apply bounded
      simp only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi,Option.getD_some]
      exact List.getElem_mem hi
    have decoded := call_word_limbs_decode (expected.getD i 0) small
    unfold instructionAdd64Word
    rw [show row (base+4*i)=callWordLimb (expected.getD i 0) 0 from by simpa using cells i hi 0 (by decide),
      cells i hi 1 (by decide),cells i hi 2 (by decide),cells i hi 3 (by decide)]
    exact decoded
  apply List.ext_getElem
  · simp [sharedFlatWords]
  · intro i hi hj
    simp only [sharedFlatWords,List.getElem_map,List.getElem_range]
    have result:=word i hj
    simpa [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hj] using result

/-- The exact state-copy equations generated for adjacent uses. -/
def callStateLinkResiduals (row : Nat→Nat→Fp) (previous next : Nat) : List Fp :=
  (List.range 32).map (fun j=>row next (3+j)-row previous (99+j))

theorem call_state_link_residuals_sound (row : Nat→Nat→Fp) (previous next : Nat)
    (zero : ∀ v,v∈callStateLinkResiduals row previous next → v=0) :
    sharedFlatWords (row next) 3 8=sharedFlatWords (row previous) 99 8 := by
  apply shared_flat_words_transfer
  intro j hj
  have eq:=zero _ (List.mem_map.mpr ⟨j,List.mem_range.mpr (by omega),rfl⟩)
  grind

/-- Row-low/column-high slots are injective for bounded row indices, so the
compiler cannot alias a hidden state limb with another row or column. -/
theorem call_input_slot_injective (rows r s c d : Nat)
    (hr : r<rows) (hs : s<rows) (same : r+rows*c=s+rows*d) : r=s ∧ c=d := by
  have mod := congrArg (fun x=>x%rows) same
  have div := congrArg (fun x=>x/rows) same
  simp [Nat.add_mod,Nat.mod_eq_of_lt hr,Nat.mod_eq_of_lt hs] at mod
  rw [Nat.add_mul_div_left r c (by omega),Nat.add_mul_div_left s d (by omega),
    Nat.div_eq_of_lt hr,Nat.div_eq_of_lt hs,Nat.zero_add,Nat.zero_add] at div
  exact ⟨mod,div⟩

/-- Exact flattened constant constraints emitted for IV and block words. -/
def callConstantResiduals (row : Nat→Fp) (base : Nat) (expected : List Nat) : List Fp :=
  (List.range (4*expected.length)).map (fun j=>
    row (base+j)-callWordLimb (expected.getD (j/4) 0) (j%4))

theorem call_constant_residuals_words (row : Nat→Fp) (base : Nat) (expected : List Nat)
    (bounded : ∀ w,w∈expected → w<2^64)
    (zero : ∀ v,v∈callConstantResiduals row base expected → v=0) :
    sharedFlatWords row base expected.length=expected := by
  apply call_constant_limbs_words row base expected bounded
  intro i hi j hj
  have eq:=zero _ (List.mem_map.mpr ⟨4*i+j,List.mem_range.mpr (by omega),rfl⟩)
  have div : (4*i+j)/4=i := by omega
  have mod : (4*i+j)%4=j := by omega
  simp only [div,mod] at eq
  rw [←Nat.add_assoc] at eq
  grind

/-- Concatenate the32limb equalities for every adjacent pair of ordered uses. -/
def callLinkResiduals (row : Nat→Nat→Fp) : List (Nat × List Nat)→List Fp
  | [] => []
  | [_] => []
  | a::b::rest => callStateLinkResiduals row a.1 b.1 ++ callLinkResiduals row (b::rest)

/-- State linking is now obtained from the generated field equations, rather
than supplied as a semantic chain premise. Blocks are handled independently. -/
theorem call_link_residuals_wiring (nodes : List Nat) (payload : Nat→Nat→Fp)
    (first : Nat × List Nat) (rest : List (Nat × List Nat)) (initial : List Nat)
    (start : sharedFlatWords (chunkGlobalUseRow nodes payload first.1) 3 8=initial)
    (zero : ∀ v,v∈callLinkResiduals (chunkGlobalUseRow nodes payload) (first::rest) → v=0) :
    chunkCallWiring nodes payload initial (first::rest)
      ((first::rest).foldl (fun _ item=>sharedFlatWords (chunkGlobalUseRow nodes payload item.1) 99 8) initial) := by
  induction rest generalizing first initial with
  | nil => exact ⟨start,rfl⟩
  | cons next rest ih =>
    have link:=call_state_link_residuals_sound (chunkGlobalUseRow nodes payload) first.1 next.1
      (fun v hv=>zero v (List.mem_append_left _ hv))
    have tail:=ih next (sharedFlatWords (chunkGlobalUseRow nodes payload first.1) 99 8) link
      (fun v hv=>zero v (List.mem_append_right _ hv))
    exact ⟨start,tail⟩

/-- The compiler's constant IV equations establish the first state of a call. -/
theorem call_iv_residuals_sound (row : Nat→Fp)
    (zero : ∀ v,v∈callConstantResiduals row 3 sha384ChainIV → v=0) :
    sharedFlatWords row 3 8=sha384ChainIV := by
  exact call_constant_residuals_words row 3 sha384ChainIV (by decide) zero

end NearCompression
