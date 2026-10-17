import NearCompression.PreparedGasBorrow
import NearCompression.PackedByteLift
import NearCompression.PackedExprRewrite

/-! The concrete balanced 16-bit macro used by the Python AIR. This module
proves its field semantics for either row selector and range-checked bytes.
The concrete whole-layout rewrite certificate remains a separate obligation. -/
namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra

def packedSourceLimb (base : Nat) (nx : Bool) : Expr :=
  preparedGasSumTree (fun i => .mul (.const (2^i)) (.col (base+i) nx)) 4 0

def packedTargetLimb (loCol hiCol : Nat) (nx : Bool) : Expr :=
  .add (.col loCol nx) (.mul (.const 256) (.col hiCol nx))

/-- Selection of a current or next row does not alter the balanced-to-Horner
identity. The environment's arithmetic is the actual BabyBear field. -/
theorem packed_source_horner (env : Env Fp) (base : Nat) (nx : Bool)
    (hn : env.ofNat=Fp.ofNat) (ha : env.add=(·+·))
    (hm : env.mul=(·*·)) :
    (packedSourceLimb base nx).evalWith env =
      (instructionBitExpr base 16).evalWith
        (instructionAddEnv (fun c=>env.col c nx)) := by
  simp only [packedSourceLimb,preparedGasSumTree,instructionBitExpr,Expr.evalWith,
    instructionAddEnv,Nat.reduceAdd,Nat.reducePow,Nat.add_zero,Nat.add_assoc,hn,ha,hm]
  simp only [←Fp.ofNat_def]
  grind

/-- Canonical byte decomposition agrees with the bits of the combined limb. -/
theorem packed_pair_bit (lo hi k : Nat) (hl : lo<256) (_hh : hi<256) (hk : k<16) :
    (lo+256*hi)/2^k%2 =
      if k<8 then lo/2^k%2 else hi/2^(k-8)%2 := by
  have cases : k=0 ∨ k=1 ∨ k=2 ∨ k=3 ∨ k=4 ∨ k=5 ∨ k=6 ∨ k=7 ∨
      k=8 ∨ k=9 ∨ k=10 ∨ k=11 ∨ k=12 ∨ k=13 ∨ k=14 ∨ k=15 := by omega
  rcases cases with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst k <;>
    simp only [Nat.reducePow,Nat.reduceLT,ite_true,ite_false,Nat.reduceSub] <;> omega

/-- The actual source macro evaluates to lo+256*hi when original bit columns
are reconstructed independently from the two bounded bytes. -/
theorem packed_source_limb_value (env : Env Fp) (base lo hi : Nat) (nx : Bool)
    (hn : env.ofNat=Fp.ofNat) (ha : env.add=(·+·)) (hm : env.mul=(·*·))
    (hl : lo<256) (hh : hi<256)
    (bits : ∀ k,k<16 → env.col (base+k) nx = Fp.ofNat
      (if k<8 then lo/2^k%2 else hi/2^(k-8)%2)) :
    (packedSourceLimb base nx).evalWith env=Fp.ofNat (lo+256*hi) := by
  rw [packed_source_horner env base nx hn ha hm]
  apply instruction_bit_expr_complete _ 16 base (lo+256*hi)
  · exact (packed_byte_limb_canonical lo hi hl hh).1
  · intro k hk
    rw [bits k hk,packed_pair_bit lo hi k hl hh hk]

/-- Discharges a concrete 16-bit macro replacement, including next-row uses. -/
theorem packed_byte_macro_eval (old packed : Env Fp)
    (base loCol hiCol lo hi : Nat) (nx : Bool)
    (ohn : old.ofNat=Fp.ofNat) (oha : old.add=(·+·)) (ohm : old.mul=(·*·))
    (phn : packed.ofNat=Fp.ofNat) (pha : packed.add=(·+·)) (phm : packed.mul=(·*·))
    (hl : lo<256) (hh : hi<256)
    (bits : ∀ k,k<16 → old.col (base+k) nx = Fp.ofNat
      (if k<8 then lo/2^k%2 else hi/2^(k-8)%2))
    (low : packed.col loCol nx=Fp.ofNat lo)
    (high : packed.col hiCol nx=Fp.ofNat hi) :
    (packedTargetLimb loCol hiCol nx).evalWith packed =
      (packedSourceLimb base nx).evalWith old := by
  rw [packed_source_limb_value old base lo hi nx ohn oha ohm hl hh bits]
  simp only [packedTargetLimb,Expr.evalWith,phn,pha,phm,low,high]
  have ca (a b : Nat) : Fp.ofNat (a+b)=Fp.ofNat a+Fp.ofNat b :=
    Lean.Grind.Semiring.natCast_add a b
  have cm (a b : Nat) : Fp.ofNat (a*b)=Fp.ofNat a*Fp.ofNat b :=
    Lean.Grind.Semiring.natCast_mul a b
  rw [ca,cm]

end NearCompression
