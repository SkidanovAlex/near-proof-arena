import NearCompression.PreparedAddTableLocal

namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near

def preparedCodeBits (base : Nat) (next : Bool := false) : Expr :=
  preparedGasSumTree (fun i=>.mul (.const (2^i)) (.col (base+i) next)) 4 0

def preparedCodeFirstPC (i : Nat) : Expr :=
  .mul .isFirst (.add (.col (1+i) false) (.neg (.const 0)))
def preparedCodeNoResume : Expr :=
  .mul .isTransition (.add (.mul (.add (.const 1) (.neg (.col 0 false))) (.col 0 true)) (.neg (.const 0)))
def preparedCodePCStepLow : Expr :=
  .mul (.mul .isTransition (.col 0 true))
    (.add (.add (preparedCodeBits 1) (.const 1))
      (.neg (.add (preparedCodeBits 1 true) (.mul (.const 65536) (.col 197 false)))))
def preparedCodePCStepHigh : Expr :=
  .mul (.mul .isTransition (.col 0 true))
    (.add (preparedCodeBits 17 true) (.neg (.add (preparedCodeBits 17) (.col 197 false))))

/-- Literal subset of the frozen CODE table, not an assumed semantic transition. -/
structure PreparedCodeOrderSource (table : Table) : Prop where
  boolean : ∀ i,i<198 → preparedGasBoolean i∈table.constraints
  firstPC : ∀ i,i<32 → preparedCodeFirstPC i∈table.constraints
  noResume : preparedCodeNoResume∈table.constraints
  low : preparedCodePCStepLow∈table.constraints
  high : preparedCodePCStepHigh∈table.constraints

def preparedCodeLimb (row : Nat → Fp) (base : Nat) : Fp :=
  (instructionBitExpr base 16).evalWith (instructionAddEnv row)
def preparedCodePC (row : Nat → Fp) : Nat :=
  (preparedCodeLimb row 1).toNat+65536*(preparedCodeLimb row 17).toNat

theorem prepared_code_bits_eval (tr : Trace Fp) (t r : Nat) (pub : List Fp) (base : Nat) (next : Bool) :
    (preparedCodeBits base next).eval tr t r pub=
      preparedCodeLimb (tr.cell t (if next then (r+1)%tr.height t else r)) base := by
  cases next <;>
    simp only [preparedCodeBits,preparedGasSumTree,preparedCodeLimb,instructionBitExpr,Expr.eval,
      Expr.evalWith,rowEnv,instructionAddEnv,Nat.reduceAdd,Nat.reducePow,Nat.add_zero,Nat.add_assoc,
      Bool.false_eq_true,ite_false,ite_true] <;>
    simp only [←Fp.ofNat_def] <;> grind

theorem prepared_code_boolean (table : Table) (tr : Trace Fp) (t : Nat) (pub : List Fp)
    (source : PreparedCodeOrderSource table) (localH : TableLocal table tr t pub)
    (r : Nat) (hr : r<tr.height t) (i : Nat) (hi : i<198) : (tr.cell t r i).toNat≤1 := by
  have h:=localH.constr r hr _ (source.boolean i hi)
  change tr.cell t r i*(tr.cell t r i+ -(1:Fp))+ -(0:Fp)=0 at h
  apply instruction_add_boolean_bound
  grind

theorem prepared_code_limb_bound (table : Table) (tr : Trace Fp) (t : Nat) (pub : List Fp)
    (source : PreparedCodeOrderSource table) (localH : TableLocal table tr t pub)
    (r : Nat) (hr : r<tr.height t) (base : Nat) (fits : base+16≤198) :
    (preparedCodeLimb (tr.cell t r) base).toNat<65536 := by
  exact instruction_bit_expr_bound _ 16 base (by decide) (fun k hk=>
    prepared_code_boolean table tr t pub source localH r hr _ (by omega))

theorem prepared_code_active_previous (table : Table) (tr : Trace Fp) (t : Nat) (pub : List Fp)
    (source : PreparedCodeOrderSource table) (localH : TableLocal table tr t pub)
    (r : Nat) (next : r+1<tr.height t) (active : tr.cell t (r+1) 0=1) : tr.cell t r 0=1 := by
  have h:=localH.constr r (by omega) _ source.noResume
  have notLast : ¬r+1=tr.height t:=by omega
  simp only [preparedCodeNoResume,Expr.eval,Expr.evalWith,rowEnv,Nat.mod_eq_of_lt next,
    if_neg notLast,Bool.false_eq_true,ite_true,ite_false] at h
  rw [active] at h
  grind

theorem prepared_code_pc_successor (table : Table) (tr : Trace Fp) (t : Nat) (pub : List Fp)
    (source : PreparedCodeOrderSource table) (localH : TableLocal table tr t pub)
    (r : Nat) (next : r+1<tr.height t) (active : tr.cell t (r+1) 0=1) :
    preparedCodePC (tr.cell t (r+1))=preparedCodePC (tr.cell t r)+1 := by
  have notLast : ¬r+1=tr.height t:=by omega
  have low:=localH.constr r (by omega) _ source.low
  have high:=localH.constr r (by omega) _ source.high
  change ((.mul (.mul .isTransition (.col 0 true))
    (.add (.add (preparedCodeBits 1) (.const 1))
      (.neg (.add (preparedCodeBits 1 true) (.mul (.const 65536) (.col 197 false)))))):Expr).eval tr t r pub=0 at low
  simp only [Expr.eval,Expr.evalWith] at low high
  -- Restore opaque bit expressions before reducing the selectors.
  change (if r+1=tr.height t then (0:Fp) else 1)*tr.cell t ((r+1)%tr.height t) 0*
    ((preparedCodeBits 1).eval tr t r pub+1+
      -((preparedCodeBits 1 true).eval tr t r pub+65536*tr.cell t r 197))=0 at low
  change (if r+1=tr.height t then (0:Fp) else 1)*tr.cell t ((r+1)%tr.height t) 0*
    ((preparedCodeBits 17 true).eval tr t r pub+
      -((preparedCodeBits 17).eval tr t r pub+tr.cell t r 197))=0 at high
  rw [if_neg notLast,Nat.mod_eq_of_lt next,active] at low high
  rw [prepared_code_bits_eval,prepared_code_bits_eval] at low high
  simp only [Bool.false_eq_true,ite_false,ite_true,Nat.mod_eq_of_lt next] at low high
  have lo : preparedCodeLimb (tr.cell t r) 1+(1:Fp)+0=
      preparedCodeLimb (tr.cell t (r+1)) 1+65536*tr.cell t r 197 := by grind
  have hi : preparedCodeLimb (tr.cell t r) 17+(0:Fp)+tr.cell t r 197=
      preparedCodeLimb (tr.cell t (r+1)) 17+65536*(0:Fp) := by grind
  have carry:=prepared_code_boolean table tr t pub source localH r (by omega) 197 (by decide)
  have l:=instruction_add_limb_sound _ 1 0 _ _
    (prepared_code_limb_bound table tr t pub source localH r (by omega) 1 (by decide)) (by decide)
    (by decide) (prepared_code_limb_bound table tr t pub source localH (r+1) next 1 (by decide)) carry lo
  have h:=instruction_add_limb_sound _ 0 _ _ 0
    (prepared_code_limb_bound table tr t pub source localH r (by omega) 17 (by decide)) (by decide)
    carry (prepared_code_limb_bound table tr t pub source localH (r+1) next 17 (by decide)) (by decide) hi
  change (preparedCodeLimb (tr.cell t r) 1).toNat+1+0=
    (preparedCodeLimb (tr.cell t (r+1)) 1).toNat+65536*(tr.cell t r 197).toNat at l
  change (preparedCodeLimb (tr.cell t r) 17).toNat+0+(tr.cell t r 197).toNat=
    (preparedCodeLimb (tr.cell t (r+1)) 17).toNat+65536*0 at h
  unfold preparedCodePC
  omega

theorem prepared_code_pc_initial (table : Table) (tr : Trace Fp) (t : Nat) (pub : List Fp)
    (source : PreparedCodeOrderSource table) (localH : TableLocal table tr t pub) :
    preparedCodePC (tr.cell t 0)=0 := by
  have positive : 0<tr.height t:=Nat.two_pow_pos _
  have zero (i : Nat) (hi : 1≤i) (bound : i<33) : tr.cell t 0 i=0 := by
    have h:=localH.constr 0 positive _ (source.firstPC (i-1) (by omega))
    change (1:Fp)*(tr.cell t 0 (1+(i-1))+ -(0:Fp))=0 at h
    rw [show 1+(i-1)=i by omega] at h
    grind
  have lo : preparedCodeLimb (tr.cell t 0) 1=0 := by
    simp (disch:=omega) [preparedCodeLimb,instructionBitExpr,Expr.evalWith,instructionAddEnv,zero]
    simp only [←Fp.ofNat_def]
    grind
  have hi : preparedCodeLimb (tr.cell t 0) 17=0 := by
    simp (disch:=omega) [preparedCodeLimb,instructionBitExpr,Expr.evalWith,instructionAddEnv,zero]
    simp only [←Fp.ofNat_def]
    grind
  unfold preparedCodePC
  rw [lo,hi]
  decide

/-- Every active CODE row has its literal natural row index as PC. This includes
arbitrarily long active prefixes up to the table height, with no field alias. -/
theorem prepared_code_pc_index (table : Table) (tr : Trace Fp) (t : Nat) (pub : List Fp)
    (source : PreparedCodeOrderSource table) (localH : TableLocal table tr t pub)
    (r : Nat) (hr : r<tr.height t) (active : tr.cell t r 0=1) :
    preparedCodePC (tr.cell t r)=r := by
  induction r with
  | zero => exact prepared_code_pc_initial table tr t pub source localH
  | succ r ih =>
    have previous:=prepared_code_active_previous table tr t pub source localH r hr active
    have eq:=ih (by omega) previous
    have step:=prepared_code_pc_successor table tr t pub source localH r hr active
    omega

theorem prepared_code_key_injective (table : Table) (tr : Trace Fp) (t : Nat) (pub : List Fp)
    (source : PreparedCodeOrderSource table) (localH : TableLocal table tr t pub)
    (r s : Nat) (hr : r<tr.height t) (hs : s<tr.height t)
    (activeR : tr.cell t r 0=1) (activeS : tr.cell t s 0=1)
    (samePC : preparedCodePC (tr.cell t r)=preparedCodePC (tr.cell t s)) : r=s := by
  rw [prepared_code_pc_index table tr t pub source localH r hr activeR,
    prepared_code_pc_index table tr t pub source localH s hs activeS] at samePC
  exact samePC

end NearCompression
