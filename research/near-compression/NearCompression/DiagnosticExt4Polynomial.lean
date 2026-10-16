import NearCompression.DiagnosticExt4Embedding
import NearCompression.PackedSourceExecution
import NearCompression.SHA384NativeProjectedSource
namespace NearCompression
open Lean.Grind ZkFormal.Algebra

theorem diagnostic_ext4_embed_zero : diagnosticExt4Embed 0=0 := rfl

theorem diagnostic_ext4_embed_add (a b : Fp) :
    diagnosticExt4Embed (a+b)=diagnosticExt4Embed a+diagnosticExt4Embed b := by
  apply QuadExt.ext <;> apply QuadExt.ext <;>
    simp [diagnosticExt4Embed,diagnosticExt4ToTower,diagnosticExt4Base] <;> grind

theorem diagnostic_ext4_embed_neg (a : Fp) :
    diagnosticExt4Embed (-a)= -diagnosticExt4Embed a := by
  apply QuadExt.ext <;> apply QuadExt.ext <;>
    simp [diagnosticExt4Embed,diagnosticExt4ToTower,diagnosticExt4Base] <;> grind

theorem diagnostic_ext4_embed_sub (a b : Fp) :
    diagnosticExt4Embed (a-b)=diagnosticExt4Embed a-diagnosticExt4Embed b := by
  rw [Ring.sub_eq_add_neg,diagnostic_ext4_embed_add,diagnostic_ext4_embed_neg,Ring.sub_eq_add_neg]

/-- The actual tower's natural cast is the same canonical source-word embedding. -/
theorem diagnostic_ext4_embed_word (a : Fp) :
    (@Nat.cast Fp4 Semiring.natCast a.toNat)=diagnosticExt4Embed a := by
  change (⟨⟨Fp.ofNat a.toNat,0⟩,⟨0,0⟩⟩ : Fp4)=_
  rw [Fp.ofNat_toNat]
  rfl

theorem diagnostic_ext4_embed_nat (n : Nat) :
    (@Nat.cast Fp4 Semiring.natCast n)=diagnosticExt4Embed (Fp.ofNat n) := rfl

theorem diagnostic_ext4_characteristic :
    (@Nat.cast Fp4 Semiring.natCast 2013265921)=0 := by decide +kernel

def diagnosticExt4Polynomial (f : Poly Fp) : Poly Fp4 :=
  ⟨f.coeffs.map diagnosticExt4Embed⟩

private theorem eval_list (cs : List Fp) (x : Fp) :
    Poly.evalL (diagnosticExt4Embed x) (cs.map diagnosticExt4Embed)=
      diagnosticExt4Embed (Poly.evalL x cs) := by
  induction cs with
  | nil => exact diagnostic_ext4_embed_zero.symm
  | cons c cs ih =>
    simp only [List.map_cons,Poly.evalL,ih,diagnostic_ext4_embed_add,diagnostic_ext4_embed_mul]

theorem diagnostic_ext4_polynomial_eval (f : Poly Fp) (x : Fp) :
    (diagnosticExt4Polynomial f).eval (diagnosticExt4Embed x)=diagnosticExt4Embed (f.eval x) :=
  eval_list f.coeffs x

theorem diagnostic_ext4_mobius (n : Nat) (values : Nat→Fp) (index : Nat) :
    mobiusCoefficients n (fun i=>diagnosticExt4Embed (values i)) index=
      diagnosticExt4Embed (mobiusCoefficients n values index) := by
  induction n generalizing values index with
  | zero => rfl
  | succ n ih =>
    simp only [mobiusCoefficients]
    split
    · exact ih _ _
    · rw [show (fun j=>diagnosticExt4Embed (values (2*j+1))-diagnosticExt4Embed (values (2*j)))=
          (fun j=>diagnosticExt4Embed (values (2*j+1)-values (2*j))) by funext j;rw [diagnostic_ext4_embed_sub]]
      exact ih _ _

theorem diagnostic_ext4_packed_values (n p width group index : Nat) (table : Nat→Nat→Fp) :
    genericPackedValues n p width group (fun r c=>diagnosticExt4Embed (table r c)) index=
      diagnosticExt4Embed (genericPackedValues n p width group table index) := by
  unfold genericPackedValues genericPackedColumn
  split <;> simp [diagnostic_ext4_embed_zero]

theorem diagnostic_ext4_packed_polynomial (n p width group : Nat) (table : Nat→Nat→Fp) :
    packedComputedPolynomial n p width group (fun r c=>diagnosticExt4Embed (table r c))=
      diagnosticExt4Polynomial (packedComputedPolynomial n p width group table) := by
  unfold packedComputedPolynomial diagnosticExt4Polynomial packedComputedCoefficients
  congr 1
  rw [List.map_map]
  apply List.map_congr_left
  intro i hi
  have bound := List.mem_range.mp hi
  simp only [Function.comp_def]
  rw [mutable_lower_mobius _ _ i bound,mutable_lower_mobius _ _ i bound]
  have inputs : genericPackedValues n p width group (fun r c=>diagnosticExt4Embed (table r c))=
      (fun i=>diagnosticExt4Embed (genericPackedValues n p width group table i)) := by
    funext j;exact diagnostic_ext4_packed_values _ _ _ _ _ _
  rw [inputs,diagnostic_ext4_mobius]

/-- Genuine Fp4 polynomial evaluation, including the zero-padded final lane. -/
theorem diagnostic_ext4_packed_eval (n p width group : Nat) (table : Nat→Nat→Fp) (x : Fp) :
    (packedComputedPolynomial n p width group (fun r c=>diagnosticExt4Embed (table r c))).eval
      (diagnosticExt4Embed x)=diagnosticExt4Embed ((packedComputedPolynomial n p width group table).eval x) := by
  rw [diagnostic_ext4_packed_polynomial,diagnostic_ext4_polynomial_eval]

theorem diagnostic_ext4_source_pair (n p width : Nat) (table : Nat→Nat→Fp) (x : Fp) :
    sha384WordLiftFpPairs (K:=Fp4) (sourceWideLeaf (packedComputedSources n p width table) x)=
      sourceWideLeaf (packedComputedSources n p width (fun r c=>diagnosticExt4Embed (table r c)))
        (diagnosticExt4Embed x) := by
  unfold sha384WordLiftFpPairs sourceWideLeaf packedComputedSources
  simp only [List.map_map,Function.comp_def]
  apply List.map_congr_left
  intro group hgroup
  simp only [diagnostic_ext4_embed_word,←diagnostic_ext4_embed_neg,diagnostic_ext4_packed_eval]
end NearCompression
