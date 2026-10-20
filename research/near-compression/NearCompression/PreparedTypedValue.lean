import NearCompression.InstructionAdd64
import NearCompression.SHA512LimbDecode
import NearCompression.PreparedLocalsStep

namespace NearCompression
set_option maxRecDepth 8192
open ZkFormal.Air ZkFormal.Algebra NearSpecV3.Wasm

/-- Isolated typed-word/eqz gadget. Limbs0..3, type12 (0=i32,1=i64),
eqz result13, inverse14, bits16..79. No whole EXEC refinement is claimed. -/
def preparedTypedValueConstraints : List Expr :=
  (List.range 4).flatMap instructionAdd64RangeConstraints ++
  [instructionBitConstraint 12,
   .mul (.add (.const 1) (.neg (.col 12 false))) (.col 2 false),
   .mul (.add (.const 1) (.neg (.col 12 false))) (.col 3 false)]

def preparedTypedLimbSum : Expr :=
  .add (.add (.col 0 false) (.col 1 false)) (.add (.col 2 false) (.col 3 false))

def preparedTypedEqzConstraints : List Expr := preparedTypedValueConstraints ++
  [instructionBitConstraint 13,
   .add (.mul preparedTypedLimbSum (.col 14 false)) (.neg (.add (.const 1) (.neg (.col 13 false)))),
   .mul preparedTypedLimbSum (.col 13 false)]

def preparedTypedEqzTable : Table := ⟨80,preparedTypedEqzConstraints,[],22⟩
def preparedTypedEqzHolds (row : Nat→Fp) : Prop :=
  ∀e∈preparedTypedEqzConstraints,e.evalWith (instructionAddEnv row)=0

def preparedTypedValue (row : Nat→Fp) : Val :=
  if row 12=0 then .i32 (UInt32.ofNat (instructionAdd64Word row 0))
  else .i64 (UInt64.ofNat (instructionAdd64Word row 0))

theorem prepared_typed_ranges (row : Nat→Fp) (h : preparedTypedEqzHolds row)
    (i : Nat) (hi : i<4) : (row i).toNat<65536 := by
  have localH : ∀e∈instructionAdd64RangeConstraints i,e.evalWith (instructionAddEnv row)=0 := by
    intro e he
    apply h e
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_flatMap.mpr
      ⟨i,List.mem_range.mpr hi,he⟩))
  have bits : ∀k,k<16 → (row (16+16*i+k)).toNat≤1 := by
    intro k hk
    exact instruction_add_boolean_bound _ (localH (instructionBitConstraint (16+16*i+k)) (List.mem_cons_of_mem _
      (List.mem_map.mpr ⟨k,List.mem_range.mpr hk,rfl⟩)))
  have bound:=instruction_bit_expr_bound row 16 (16+16*i) (by decide) bits
  have eq:=localH _ (List.mem_cons_self ..)
  change row i+ -(instructionBitExpr (16+16*i) 16).evalWith (instructionAddEnv row)=0 at eq
  have same : row i=(instructionBitExpr (16+16*i) 16).evalWith (instructionAddEnv row):=by grind
  rw [same];exact bound

theorem prepared_typed_word_bound (row : Nat→Fp) (h : preparedTypedEqzHolds row) :
    instructionAdd64Word row 0<2^64 :=
  sha512_word_limb_bound row 0 (by simpa using prepared_typed_ranges row h)

theorem prepared_typed_i32_bound (row : Nat→Fp) (h : preparedTypedEqzHolds row)
    (tag : row 12=0) : instructionAdd64Word row 0<2^32 := by
  have lo:=prepared_typed_ranges row h 0 (by decide)
  have hi:=prepared_typed_ranges row h 1 (by decide)
  have z2:=h (.mul (.add (.const 1) (.neg (.col 12 false))) (.col 2 false))
    (by simp [preparedTypedEqzConstraints,preparedTypedValueConstraints])
  have z3:=h (.mul (.add (.const 1) (.neg (.col 12 false))) (.col 3 false))
    (by simp [preparedTypedEqzConstraints,preparedTypedValueConstraints])
  change ((1:Fp)+ -row 12)*row 2=0 at z2
  change ((1:Fp)+ -row 12)*row 3=0 at z3
  rw [tag] at z2 z3
  have a : row 2=0:=by grind
  have b : row 3=0:=by grind
  simp only [instructionAdd64Word,Nat.reduceAdd,a,b]
  change (row 0).toNat+65536*(row 1).toNat+4294967296*0+281474976710656*0<4294967296
  omega

/-- The small limb SUM, unlike a packed64-bit field element, cannot wrap. -/
theorem prepared_typed_sum_no_wrap (row : Nat→Fp) (h : preparedTypedEqzHolds row) :
    (preparedTypedLimbSum.evalWith (instructionAddEnv row)).toNat=
      (row 0).toNat+(row 1).toNat+((row 2).toNat+(row 3).toNat) := by
  have h0:=prepared_typed_ranges row h 0 (by decide)
  have h1:=prepared_typed_ranges row h 1 (by decide)
  have h2:=prepared_typed_ranges row h 2 (by decide)
  have h3:=prepared_typed_ranges row h 3 (by decide)
  change (Fp.add (Fp.add (row 0) (row 1)) (Fp.add (row 2) (row 3))).toNat=_
  simp only [Fp.toNat_add]
  rw [Nat.mod_eq_of_lt (show (row 0).toNat+(row 1).toNat<ZkFormal.Algebra.P by unfold ZkFormal.Algebra.P;omega),
    Nat.mod_eq_of_lt (show (row 2).toNat+(row 3).toNat<ZkFormal.Algebra.P by unfold ZkFormal.Algebra.P;omega),
    Nat.mod_eq_of_lt (by unfold ZkFormal.Algebra.P;omega)]

theorem prepared_typed_eqz (row : Nat→Fp) (h : preparedTypedEqzHolds row) :
    row 13=if instructionAdd64Word row 0=0 then 1 else 0 := by
  have inv:=h (.add (.mul preparedTypedLimbSum (.col 14 false)) (.neg (.add (.const 1) (.neg (.col 13 false)))))
    (by simp [preparedTypedEqzConstraints])
  have zero:=h (.mul preparedTypedLimbSum (.col 13 false)) (by simp [preparedTypedEqzConstraints])
  change preparedTypedLimbSum.evalWith (instructionAddEnv row)*row 14+ -((1:Fp)+ -row 13)=0 at inv
  change preparedTypedLimbSum.evalWith (instructionAddEnv row)*row 13=0 at zero
  have noWrap:=prepared_typed_sum_no_wrap row h
  have iffZero : preparedTypedLimbSum.evalWith (instructionAddEnv row)=0 ↔ instructionAdd64Word row 0=0 := by
    constructor
    · intro eq
      rw [eq] at noWrap
      change 0=_ at noWrap
      unfold instructionAdd64Word
      simp only [Nat.reduceAdd]
      omega
    · intro eq
      apply Fp.ext
      change _=0
      rw [noWrap]
      unfold instructionAdd64Word at eq
      simp only [Nat.reduceAdd] at eq
      omega
  split
  · rename_i eq
    rw [iffZero.mpr eq] at inv
    grind
  · rename_i ne
    have nonzero : preparedTypedLimbSum.evalWith (instructionAddEnv row)≠0:=by intro z;exact ne (iffZero.mp z)
    grind

theorem prepared_typed_value_exact (row : Nat→Fp) (h : preparedTypedEqzHolds row) :
    match preparedTypedValue row with
    | .i32 value=>value.toNat=instructionAdd64Word row 0
    | .i64 value=>value.toNat=instructionAdd64Word row 0
    | .ref _=>False := by
  by_cases tag : row 12=0
  · simp only [preparedTypedValue,if_pos tag]
    exact Nat.mod_eq_of_lt (prepared_typed_i32_bound row h tag)
  · simp only [preparedTypedValue,if_neg tag]
    exact Nat.mod_eq_of_lt (prepared_typed_word_bound row h)

theorem prepared_typed_tag_boolean (row : Nat→Fp) (h : preparedTypedEqzHolds row) :
    (row 12).toNat≤1 := by
  exact instruction_add_boolean_bound _ (h (instructionBitConstraint 12)
    (by simp [preparedTypedEqzConstraints,preparedTypedValueConstraints]))

theorem prepared_typed_eqz_shape : preparedTypedEqzTable.width=80 ∧
    preparedTypedEqzTable.constraints.length=74 := by decide

theorem prepared_typed_eqz_wf : preparedTypedEqzTable.wf ⟨[preparedTypedEqzTable],0,0⟩ 2=true := by decide

end NearCompression
