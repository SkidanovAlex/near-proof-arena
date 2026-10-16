import NearCompression.PreparedTypedLiteral
import NearCompression.PreparedTypedValue
import NearCompression.PreparedLocalsDepth
namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.V2 NearSpecV3.Wasm
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

def preparedTypedBooleanColumns : List Nat :=
  List.range 682 ++ (List.range 600).map (683+·) ++ [1284]

private theorem boolean_prefix : ∀count:Fin 5,
    (preparedTypedLiteralExec count).take 1283=preparedTypedBooleanColumns.map preparedGasBoolean := by
  intro ⟨n,hn⟩
  have cases : n=0 ∨ n=1 ∨ n=2 ∨ n=3 ∨ n=4:=by omega
  rcases cases with rfl|rfl|rfl|rfl|rfl <;> rfl


/-- Both inverse witnesses are deliberately excluded; every bit and type
column is covered by the exact literal source Boolean prefix. -/
theorem prepared_typed_source_boolean (count : Nat) (hc : count≤4)
    (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : TableLocal (preparedTypedLiteralExecTable count) tr t pub) (hr : r<tr.height t)
    (col : Nat) (bound : col<1285) (inverse32 : col≠682) (inverse64 : col≠1283) :
    (tr.cell t r col).toNat≤1 := by
  have member : col∈preparedTypedBooleanColumns := by
    by_cases low:col<682
    · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_range.mpr low))
    · by_cases last:col=1284
      · exact List.mem_append_right _ (by simp [last])
      · apply List.mem_append_left
        apply List.mem_append_right
        exact List.mem_map.mpr ⟨col-683,List.mem_range.mpr (by omega),by omega⟩
  have e : preparedGasBoolean col∈preparedTypedBooleanColumns.map preparedGasBoolean :=
    List.mem_map.mpr ⟨col,member,rfl⟩
  rw [←boolean_prefix ⟨count,by omega⟩] at e
  have h:=localH.constr r hr _ (List.mem_of_mem_take e)
  change tr.cell t r col*(tr.cell t r col+ -(1:Fp))+ -(0:Fp)=0 at h
  apply instruction_add_boolean_bound
  grind


theorem prepared_typed_source_limb (count : Nat) (hc : count≤4)
    (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : TableLocal (preparedTypedLiteralExecTable count) tr t pub) (hr : r<tr.height t)
    (base : Nat) (range : base+16≤1285) (noInverse : ∀i,i<16 → base+i≠682 ∧ base+i≠1283) :
    (preparedCodeLimb (tr.cell t r) base).toNat<65536 := by
  apply instruction_bit_expr_bound _ 16 base (by decide)
  intro i hi
  exact prepared_typed_source_boolean count hc tr t r pub localH hr _ (by omega) (noInverse i hi).1 (noInverse i hi).2


private theorem sp_at : ∀count:Fin 5,(preparedTypedLiteralExec count)[1283]?=some preparedLocalsLiteralExec0817 := by decide
private theorem sp_source (count:Fin 5) : preparedLocalsLiteralExec0817∈preparedTypedLiteralExec count :=
  List.mem_of_getElem? (sp_at count)


theorem prepared_typed_source_sp (count : Nat) (hc : count≤4)
    (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : TableLocal (preparedTypedLiteralExecTable count) tr t pub) (hr : r<tr.height t) :
    ∃sp,sp<9 ∧ ∀i,i<9 → tr.cell t r (32+i)=if i=sp then 1 else 0 := by
  have h:=localH.constr r hr _ (sp_source ⟨count,by omega⟩)
  apply prepared_onehot 9 32 (tr.cell t r) (by decide)
  · intro i hi
    exact prepared_typed_source_boolean count hc tr t r pub localH hr _ (by omega) (by omega) (by omega)
  · change (((tr.cell t r 32+tr.cell t r 33)+(tr.cell t r 34+tr.cell t r 35))+
      ((tr.cell t r 36+tr.cell t r 37)+(tr.cell t r 38+tr.cell t r 39))+tr.cell t r 40)+ -(1:Fp)=0 at h
    simp only [preparedFieldSum,Nat.reduceAdd]
    grind

private theorem type_at : ∀count:Fin 5,∀i:Fin 4,
    (preparedTypedLiteralExec count)[1294-count.val+i.val+(i.val-count.val)]?=
      some (Expr.add (.col (1210+i.val) false) (.neg (.pub (114+i.val)))) := by decide
private theorem type_source (count:Fin 5) (i:Fin 4) :
    Expr.add (.col (1210+i.val) false) (.neg (.pub (114+i.val)))∈preparedTypedLiteralExec count :=
  List.mem_of_getElem? (type_at count i)

/-- All rows use the same public local type; setup checking binds this field
to actual pf.locals. This theorem is source-derived, including padding rows. -/
theorem prepared_typed_source_local_type (count : Nat) (hc : count≤4)
    (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : TableLocal (preparedTypedLiteralExecTable count) tr t pub) (hr : r<tr.height t)
    (i : Nat) (hi : i<4) : tr.cell t r (1210+i)=pub.getD (114+i) 0 := by
  have h:=localH.constr r hr _ (type_source ⟨count,by omega⟩ ⟨i,hi⟩)
  change tr.cell t r (1210+i)+ -pub.getD (114+i) 0=0 at h
  grind

def preparedTypedStackBase (slot limb : Nat) : Nat :=
  (if limb<2 then 43 else 818)+32*slot+16*(limb%2)
def preparedTypedStackLimb (row : Nat→Fp) (slot limb : Nat) : Fp :=
  preparedCodeLimb row (preparedTypedStackBase slot limb)
def preparedTypedStackWord (row : Nat→Fp) (slot : Nat) : Nat :=
  instructionAdd64Word (preparedTypedStackLimb row slot) 0

theorem prepared_typed_stack_limb_bound (count : Nat) (hc : count≤4)
    (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : TableLocal (preparedTypedLiteralExecTable count) tr t pub) (hr : r<tr.height t)
    (slot limb : Nat) (hs : slot<8) (hl : limb<4) :
    (preparedTypedStackLimb (tr.cell t r) slot limb).toNat<65536 := by
  apply prepared_typed_source_limb count hc tr t r pub localH hr
  · unfold preparedTypedStackBase
    split <;> omega
  · intro i hi
    unfold preparedTypedStackBase
    split <;> constructor <;> omega

theorem prepared_typed_stack_word_bound (count : Nat) (hc : count≤4)
    (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : TableLocal (preparedTypedLiteralExecTable count) tr t pub) (hr : r<tr.height t)
    (slot : Nat) (hs : slot<8) : preparedTypedStackWord (tr.cell t r) slot<2^64 := by
  exact sha512_word_limb_bound (preparedTypedStackLimb (tr.cell t r) slot) 0
    (by
      intro i hi
      simpa only [Nat.zero_add] using prepared_typed_stack_limb_bound count hc tr t r pub localH hr slot i hs hi)
end NearCompression
