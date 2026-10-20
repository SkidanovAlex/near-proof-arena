import NearCompression.PowerTwoRootOrder
import ZkFormal.Algebra.Fp8

/-! The diagnostic X^4=11 challenge field uses main's certified Fp4 tower.
The flat coordinate model matches Python's [1,v,v^2,v^3] order. This is
an algebra/loop-schedule refinement, not a 128-bit soundness assertion. -/
namespace NearCompression
open Lean.Grind ZkFormal.Algebra

structure DiagnosticExt4 where
  c0 : Fp
  c1 : Fp
  c2 : Fp
  c3 : Fp
  deriving DecidableEq

def diagnosticExt4ToTower (a : DiagnosticExt4) : Fp4 := ⟨⟨a.c0,a.c2⟩,⟨a.c1,a.c3⟩⟩
def diagnosticExt4FromTower (a : Fp4) : DiagnosticExt4 := ⟨a.a.a,a.b.a,a.a.b,a.b.b⟩
def diagnosticExt4Base (a : Fp) : DiagnosticExt4 := ⟨a,0,0,0⟩
def diagnosticExt4Embed (a : Fp) : Fp4 := diagnosticExt4ToTower (diagnosticExt4Base a)

theorem diagnostic_ext4_roundtrip (a : DiagnosticExt4) :
    diagnosticExt4FromTower (diagnosticExt4ToTower a)=a := by cases a; rfl

theorem diagnostic_ext4_tower_roundtrip (a : Fp4) :
    diagnosticExt4ToTower (diagnosticExt4FromTower a)=a := by
  cases a with | mk a b => cases a; cases b; rfl

theorem diagnostic_ext4_embed_injective {a b : Fp}
    (same : diagnosticExt4Embed a=diagnosticExt4Embed b) : a=b :=
  congrArg (fun a : Fp4 => a.a.a) same

theorem diagnostic_ext4_embed_one : diagnosticExt4Embed 1=1 := rfl

theorem diagnostic_ext4_embed_mul (a b : Fp) :
    diagnosticExt4Embed (a*b)=diagnosticExt4Embed a*diagnosticExt4Embed b := by
  apply QuadExt.ext <;> apply QuadExt.ext <;>
    simp [diagnosticExt4Embed,diagnosticExt4ToTower,diagnosticExt4Base] <;> grind

theorem diagnostic_ext4_embed_pow (a : Fp) (n : Nat) :
    diagnosticExt4Embed (a^n)=(diagnosticExt4Embed a)^n := by
  induction n with
  | zero => exact diagnostic_ext4_embed_one
  | succ n ih => rw [Semiring.pow_succ,diagnostic_ext4_embed_mul,ih,Semiring.pow_succ]

def diagnosticExt4Root (k : Nat) : Fp4 := diagnosticExt4Embed (nativeBabyBearRoot k)

/-- Exact order in the actual diagnostic challenge field, not only in Fp. -/
theorem diagnostic_ext4_root_order (k : Nat) (supported : k≤27) (j : Nat) :
    (diagnosticExt4Root k)^j=1 ↔ 2^k∣j := by
  rw [diagnosticExt4Root,←diagnostic_ext4_embed_pow]
  constructor
  · intro equal
    have same : diagnosticExt4Embed ((nativeBabyBearRoot k)^j)=diagnosticExt4Embed 1 := equal
    exact (native_babybear_root_order k supported j).mp (diagnostic_ext4_embed_injective same)
  · intro divides
    rw [(native_babybear_root_order k supported j).mpr divides,diagnostic_ext4_embed_one]

def diagnosticExt4Get (a : DiagnosticExt4) (i : Nat) : Fp :=
  match i with | 0 => a.c0 | 1 => a.c1 | 2 => a.c2 | 3 => a.c3 | _ => 0

/-- Literal pure model of the two nested four-coordinate accumulation loops.
The seven accumulator cells are addressed by i+j. -/
def diagnosticExt4Product (a b : DiagnosticExt4) : Nat → Fp :=
  (List.range 4).foldl (fun acc i => (List.range 4).foldl
    (fun acc j => fun k => if k=i+j then acc k+diagnosticExt4Get a i*diagnosticExt4Get b j else acc k)
    acc) (fun _ => 0)

/-- Literal descending [6,5,4] reduction by X^4=11, then the first four cells. -/
def diagnosticExt4Mul (a b : DiagnosticExt4) : DiagnosticExt4 :=
  let acc := [6,5,4].foldl
    (fun acc i => fun k => if k=i-4 then acc k+11*acc i else acc k)
    (diagnosticExt4Product a b)
  ⟨acc 0,acc 1,acc 2,acc 3⟩

private theorem fp_mul_notation (a b : Fp) : Fp.mul a b=a*b := rfl

/-- Full mixed-coordinate multiplication, not just embedded constants.
Fp arithmetic supplies exact modular operations; Python integer execution
and canonical input decoding remain separate implementation obligations. -/
theorem diagnostic_ext4_mul_refinement (a b : DiagnosticExt4) :
    diagnosticExt4ToTower (diagnosticExt4Mul a b)=diagnosticExt4ToTower a*diagnosticExt4ToTower b := by
  simp only [diagnosticExt4ToTower]
  apply QuadExt.ext <;> apply QuadExt.ext <;>
    dsimp only [HMul.hMul,instHMul,Mul.mul,QuadExt.instMul] <;>
    simp [diagnosticExt4Mul,diagnosticExt4Product,
      diagnosticExt4Get,List.range_succ,List.foldl_cons,QuadExt.t,fp_mul_notation] <;> grind

def diagnosticExt4Add (a b : DiagnosticExt4) : DiagnosticExt4 :=
  ⟨a.c0+b.c0,a.c1+b.c1,a.c2+b.c2,a.c3+b.c3⟩
def diagnosticExt4Sub (a b : DiagnosticExt4) : DiagnosticExt4 :=
  ⟨a.c0-b.c0,a.c1-b.c1,a.c2-b.c2,a.c3-b.c3⟩

theorem diagnostic_ext4_add_refinement (a b : DiagnosticExt4) :
    diagnosticExt4ToTower (diagnosticExt4Add a b)=diagnosticExt4ToTower a+diagnosticExt4ToTower b := rfl

theorem diagnostic_ext4_sub_refinement (a b : DiagnosticExt4) :
    diagnosticExt4ToTower (diagnosticExt4Sub a b)=diagnosticExt4ToTower a-diagnosticExt4ToTower b := rfl

/-- The extension domain is exactly the coordinatewise embedding of source
Fp domain points, preserving natural FFT order. -/
theorem diagnostic_ext4_domain_embedding (k : Nat) :
    (naturalRSDomain (nativeBabyBearRoot k) (2^k)).map diagnosticExt4Embed=
      naturalRSDomain (diagnosticExt4Root k) (2^k) := by
  simp only [naturalRSDomain,List.map_map,Function.comp_def]
  apply List.map_congr_left
  intro i hi
  exact diagnostic_ext4_embed_pow _ _

/-- Concrete challenge field and concrete native root: near-case branch
recovery has no remaining abstract field-embedding or root-order premise.
Metadata, source projection and fixed representative premises remain explicit. -/
theorem diagnostic_ext4_projected_recovery (layout : GKRJointLayout) (metadata : List GKRSourceLane)
    (valid : ∀ lane∈metadata,lane.WellFormed layout)
    (geometry : CanonicalLaneSelectors layout metadata)
    (L d T k : Nat) (positiveL : 0<L) (positiveD : 0<d)
    (supported : k≤27) (domainSize : 2^k=L*(4*d))
    (sources : List (Fp4 → Fp4)) (polys : List (Poly Fp4))
    (sourceShape : sources.length=metadata.length) (polyShape : polys.length=metadata.length)
    (representative : JointBetaRepresentative (naturalRSDomain (diagnosticExt4Root k) (L*(4*d)))
      (fun _ => 1) (heterogeneousJointDimension layout) (L*d) T
      (metadata.map (heterogeneousJointBeta layout)) sources polys)
    (i : Nat) (hi : i<metadata.length)
    (source : Fp4 → Fp4) (projection : ∀ x,sources[i] x=source (x^L))
    (separation : (L*(4*d)-T)+(L*(4*d)-T)+L*d≤L*(4*d)) :
    let recovered := recoverProjectedPolynomial L d polys[i]
    recovered.DegLt d ∧
      (∀ j,polys[i].coeff j=if L∣j then recovered.coeff (j/L) else 0) := by
  apply natural_rs_joint_projected_recovery layout metadata valid geometry L d T positiveL positiveD
    (diagnosticExt4Root k) _ sources polys sourceShape polyShape representative i hi source projection separation
  intro j
  rw [←domainSize]
  exact diagnostic_ext4_root_order k supported j
end NearCompression
