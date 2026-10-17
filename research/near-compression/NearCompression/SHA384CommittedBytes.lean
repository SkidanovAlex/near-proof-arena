import NearCompression.SHA384CommittedPadPhase

namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2

theorem sha384_committed_input_constraint (n : Nat) (fixed : List (Nat × Nat))
    (pub : List Fp) (tr : Trace Fp) (h : HoldsP (sha384CommittedInputAir n fixed) pub tr)
    (r : Nat) (hr : r<tr.height 2) (e : Expr)
    (he : e∈(sha384CommittedInputTable n fixed).constraints) : e.eval tr 2 r pub=0 :=
  h.constr 2 (by simp [sha384CommittedInputAir]) r hr e he

theorem sha384_committed_input_bits (n : Nat) (fixed : List (Nat × Nat))
    (pub : List Fp) (tr : Trace Fp) (h : HoldsP (sha384CommittedInputAir n fixed) pub tr)
    (r c : Nat) (hr : r<tr.height 2) (hc : c<8*n) :
    (tr.cell 2 r c).toNat≤1 := by
  have bit:=sha384_committed_input_constraint n fixed pub tr h r hr (instructionBitConstraint c)
    (List.mem_append_left _ (List.mem_map.mpr ⟨c,List.mem_range.mpr hc,rfl⟩))
  change tr.cell 2 r c*(tr.cell 2 r c+ -(1:Fp))=0 at bit
  have cases : tr.cell 2 r c=0 ∨ tr.cell 2 r c=1 := by grind
  rcases cases with z|z <;> rw [z] <;> decide

theorem sha384_committed_pad_bits (n : Nat) (fixed : List (Nat × Nat))
    (pub : List Fp) (tr : Trace Fp) (h : HoldsP (sha384CommittedInputAir n fixed) pub tr)
    (r c : Nat) (hr : r<tr.height 3) (hc : c<1024) :
    (tr.cell 3 r c).toNat≤1 := by
  have bit:=sha384_committed_pad_constraint n fixed pub tr h r hr (instructionBitConstraint c)
    (by simp only [sha384CommittedPadTable,List.mem_append];exact Or.inl (Or.inl (Or.inl (List.mem_map.mpr ⟨c,List.mem_range.mpr hc,rfl⟩))))
  change tr.cell 3 r c*(tr.cell 3 r c+ -(1:Fp))=0 at bit
  have cases : tr.cell 3 r c=0 ∨ tr.cell 3 r c=1 := by grind
  rcases cases with z|z <;> rw [z] <;> decide

theorem sha384_committed_fixed_byte (n : Nat) (fixed : List (Nat × Nat))
    (pub : List Fp) (tr : Trace Fp) (h : HoldsP (sha384CommittedInputAir n fixed) pub tr)
    (i value : Nat) (member : (i,value)∈fixed) :
    (instructionBitExpr (8*i) 8).eval tr 2 0 pub=Fp.ofNat value := by
  have hc:=sha384_committed_input_constraint n fixed pub tr h 0 (Nat.two_pow_pos _)
    (.mul .isFirst (.add (instructionBitExpr (8*i) 8) (.neg (.const value))))
    (List.mem_append_right _ (List.mem_map.mpr ⟨(i,value),member,rfl⟩))
  change (1:Fp)*((instructionBitExpr (8*i) 8).eval tr 2 0 pub+ -Fp.ofNat value)=0 at hc
  grind

theorem sha384_committed_bitexpr_eval (tr : Trace Fp) (pub : List Fp) (t r base k : Nat) :
    (instructionBitExpr base k).eval tr t r pub=
      (instructionBitExpr base k).evalWith (instructionAddEnv (tr.cell t r)) := by
  induction k generalizing base with
  | zero => rfl
  | succ k ih =>
    change tr.cell t r base+Fp.ofNat 2*(instructionBitExpr (base+1) k).eval tr t r pub=_
    rw [ih];rfl

theorem sha384_committed_input_byte_bound (n : Nat) (fixed : List (Nat × Nat))
    (pub : List Fp) (tr : Trace Fp) (h : HoldsP (sha384CommittedInputAir n fixed) pub tr)
    (r i : Nat) (hr : r<tr.height 2) (hi : i<n) :
    ((instructionBitExpr (8*i) 8).eval tr 2 r pub).toNat<256 := by
  rw [sha384_committed_bitexpr_eval]
  exact instruction_bit_expr_bound _ 8 (8*i) (by decide)
    (fun k hk => sha384_committed_input_bits n fixed pub tr h r (8*i+k) hr (by omega))

theorem sha384_committed_pad_byte_bound (n : Nat) (fixed : List (Nat × Nat))
    (pub : List Fp) (tr : Trace Fp) (h : HoldsP (sha384CommittedInputAir n fixed) pub tr)
    (r i : Nat) (hr : r<tr.height 3) (hi : i<128) :
    ((instructionBitExpr (8*i) 8).eval tr 3 r pub).toNat<256 := by
  rw [sha384_committed_bitexpr_eval]
  exact instruction_bit_expr_bound _ 8 (8*i) (by decide)
    (fun k hk => sha384_committed_pad_bits n fixed pub tr h r (8*i+k) hr (by omega))

/-- A trusted byte-sized framing constant is recovered exactly, with no
field aliasing. Out-of-range fixed values are not silently interpreted as bytes. -/
theorem sha384_committed_fixed_byte_nat (n : Nat) (fixed : List (Nat × Nat))
    (pub : List Fp) (tr : Trace Fp) (h : HoldsP (sha384CommittedInputAir n fixed) pub tr)
    (i value : Nat) (member : (i,value)∈fixed) (bound : value<256) :
    ((instructionBitExpr (8*i) 8).eval tr 2 0 pub).toNat=value := by
  rw [sha384_committed_fixed_byte n fixed pub tr h i value member,Fp.toNat_ofNat]
  exact Nat.mod_eq_of_lt (by unfold P;omega)

theorem sha384_committed_pad_constant_bound (n i : Nat) : sha384PadConstByte n i<256 := by
  unfold sha384PadConstByte
  split
  · decide
  · split
    · exact Nat.mod_lt _ (by decide)
    · decide

/-- The delimiter, zero fill and length bytes are natural byte equalities,
not just equalities modulo the AIR field. -/
theorem sha384_committed_pad_constant_nat (n : Nat) (fixed : List (Nat × Nat))
    (pub : List Fp) (tr : Trace Fp) (h : HoldsP (sha384CommittedInputAir n fixed) pub tr)
    (b j : Nat) (hr : b<tr.height 3) (hb : b<sha384PaddedLength n/128)
    (hj : j<128) (padding : n≤128*b+j) :
    ((instructionBitExpr (8*j) 8).eval tr 3 b pub).toNat=sha384PadConstByte n (128*b+j) := by
  rw [sha384_committed_pad_constant n fixed pub tr h b j hr hb hj padding,Fp.toNat_ofNat]
  have bound:=sha384_committed_pad_constant_bound n (128*b+j)
  exact Nat.mod_eq_of_lt (by unfold P;omega)

end NearCompression
