import NearCompression.SHA384CallEquations
import NearCompression.CallPadding
import ZkFormal.Algebra.Fp8
namespace NearCompression
open Lean.Grind ZkFormal.Algebra ArenaCore.Security

/-- Copy descriptors must carry zero constant: the source semantics ignores
that field on copies, whereas the batching format always subtracts it. -/
def CallLinearEquation.Valid (e : CallLinearEquation) : Prop :=
  e.right.isSome=true → e.value=0

private theorem constants_valid (rows row base : Nat) (words : List Nat) :
    ∀ e∈callConstantEquations rows row base words,e.Valid := by
  intro e he
  obtain ⟨j,_,rfl⟩:=List.mem_map.mp he
  simp [CallLinearEquation.Valid]

private theorem states_valid (rows previous next : Nat) :
    ∀ e∈callStateEquations rows previous next,e.Valid := by
  intro e he
  obtain ⟨j,_,rfl⟩:=List.mem_map.mp he
  simp [CallLinearEquation.Valid]

private theorem digest_valid (rows row : Nat) (digest : List UInt8) :
    ∀ e∈callDigestEquations rows row digest,e.Valid := by
  intro e he
  obtain ⟨j,_,rfl⟩:=List.mem_map.mp he
  simp [CallLinearEquation.Valid]

theorem call_block_descriptors_valid (rows : Nat) (previous : Option Nat)
    (items : List (Nat × List Nat)) : ∀ e∈callBlockEquations rows previous items,e.Valid := by
  induction items generalizing previous with
  | nil => simp [callBlockEquations]
  | cons item rest ih =>
    intro e he
    simp only [callBlockEquations,List.mem_append] at he
    rcases he with (first | block) | tail
    · cases previous with
      | none => exact constants_valid _ _ _ _ e first
      | some p => exact states_valid _ _ _ e first
    · exact constants_valid _ _ _ _ e block
    · exact ih _ e tail

theorem call_descriptors_valid (rows : Nat) (items : List (Nat × List Nat))
    (digest : List UInt8) : ∀ e∈callEquations rows items digest,e.Valid := by
  intro e he
  simp only [callEquations,List.mem_append] at he
  rcases he with block | final
  · exact call_block_descriptors_valid _ _ _ e block
  · cases h:items.getLast? with
    | none => simp [h] at final
    | some item => exact digest_valid _ _ _ e (by simpa [h] using final)

def CallLinearEquation.lift {K : Type} (embed : Fp→K) (e : CallLinearEquation) : CallBatchEquation K :=
  ⟨e.left,e.right,embed (Fp.ofNat e.value)⟩

/-- No extension representation is assumed here; only preservation of zero
and subtraction. This identifies the two distinct descriptor semantics. -/
theorem call_descriptor_lift {K : Type} [Field K] (embed : Fp→K)
    (zero : embed 0=0) (sub : ∀ a b,embed (a-b)=embed a-embed b)
    (e : CallLinearEquation) (valid : e.Valid) (v : Nat→Fp) :
    (e.lift embed).residual (fun i=>embed (v i))=embed (e.eval v) := by
  cases h:e.right with
  | none =>
    simp only [CallLinearEquation.lift,CallBatchEquation.residual,CallLinearEquation.eval,h,
      Option.map_none,Option.getD_none,sub]
    grind
  | some right =>
    have value : e.value=0 := valid (by simp [h])
    have z : Fp.ofNat e.value=0 := by rw [value];rfl
    simp only [CallLinearEquation.lift,CallBatchEquation.residual,CallLinearEquation.eval,h,
      Option.map_some,Option.getD_some,z,zero,sub]
    grind

theorem call_descriptor_ext8_nonzero (e : CallLinearEquation) (valid : e.Valid)
    (v : Nat→Fp) (wrong : e.eval v≠0) :
    (e.lift Fp8.ofBase).residual (fun i=>Fp8.ofBase (v i))≠0 := by
  rw [call_descriptor_lift Fp8.ofBase rfl Fp8.ofBase_sub e valid v]
  intro h
  exact wrong (Fp8.ofBase_inj h)

/-- Generated descriptors preserve every base residual in the certified Ext8
field model. This does not certify the separate diagnostic Ext4 implementation. -/
theorem call_generated_ext8_residuals (rows : Nat) (items : List (Nat × List Nat))
    (digest : List UInt8) (v : Nat→Fp) :
    ((callEquations rows items digest).map (CallLinearEquation.lift Fp8.ofBase)).map
      (fun e=>e.residual (fun i=>Fp8.ofBase (v i)))=
    ((callEquations rows items digest).map (fun e=>e.eval v)).map Fp8.ofBase := by
  simp only [List.map_map,Function.comp_def]
  apply List.map_congr_left
  intro e he
  exact call_descriptor_lift Fp8.ofBase rfl Fp8.ofBase_sub e (call_descriptors_valid _ _ _ e he) v
/-- The array compiler cancellation bound now starts from a failed source
Fp descriptor, rather than assuming an unrelated extension residual is nonzero. -/
theorem call_descriptor_array_zero_count (capacity n index : Nat)
    (equations : List CallLinearEquation) (v : Nat→Fp)
    (fits : equations.length≤2^(n+1)) (indexBound : index<equations.length)
    (valid : equations[index].Valid) (wrong : equations[index].eval v≠0)
    (bounds : ∀ point,∀ e∈callCompiledEntries
      (callShortBatch (n+1) (equations.map (CallLinearEquation.lift Fp8.ofBase)) point),e.1<capacity)
    (sample : List Fp8) (distinct : sample.Nodup) :
    count (packedGrid sample (n+1)) (fun point=>
      callShortArrayScore capacity (n+1) (equations.map (CallLinearEquation.lift Fp8.ofBase))
        (fun i=>Fp8.ofBase (v i)) (fun i=>point.getD i 0)=0)≤
      (n+1)*sample.length^n := by
  have mappedBound : index<(equations.map (CallLinearEquation.lift Fp8.ofBase)).length := by
    simpa using indexBound
  have same : callPaddedEquation (equations.map (CallLinearEquation.lift Fp8.ofBase)) index=
      equations[index].lift Fp8.ofBase := by
    simp [callPaddedEquation,List.getD,List.getElem?_eq_getElem mappedBound]
  apply call_short_array_zero_count capacity n index _ _ (by simpa using fits) mappedBound _ bounds sample distinct
  rw [same]
  exact call_descriptor_ext8_nonzero _ valid v wrong

end NearCompression
