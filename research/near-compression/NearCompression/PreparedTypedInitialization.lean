import NearCompression.PreparedTypedLocalPreserve
import NearCompression.PreparedTypedCode
import NearCompression.PreparedWasmEntry
namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near NearSpecV3.Wasm
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
private theorem bits_slice : ∀count:Fin 5,∀bank:Fin 2,
    ((preparedTypedLiteralExec count).drop (if bank.val=0 then 1294+2*(4-count.val) else 1422+34*(4-count.val))).take 128=
      (List.range 128).map (fun i=>Expr.mul .isFirst (.add (.col ((if bank.val=0 then 686 else 1082)+i) false) (.neg (.const 0)))) := by
  intro ⟨count,hc⟩ ⟨bank,hb⟩
  have cc : count=0 ∨ count=1 ∨ count=2 ∨ count=3 ∨ count=4:=by omega
  have bc : bank=0 ∨ bank=1:=by omega
  rcases cc with rfl|rfl|rfl|rfl|rfl <;> rcases bc with rfl|rfl <;> rfl

theorem prepared_typed_initial_local_bit (count : Nat) (hc : count≤4)
    (tr : Trace Fp) (t : Nat) (pub : List Fp)
    (localH : TableLocal (preparedTypedLiteralExecTable count) tr t pub)
    (bank i : Nat) (hb : bank<2) (hi : i<128) :
    tr.cell t 0 ((if bank=0 then 686 else 1082)+i)=0 := by
  have member : Expr.mul .isFirst (.add (.col ((if bank=0 then 686 else 1082)+i) false) (.neg (.const 0)))∈preparedTypedLiteralExec count := by
    apply List.mem_of_mem_drop (i:=(if bank=0 then 1294+2*(4-count) else 1422+34*(4-count)))
    apply List.mem_of_mem_take (i:=128)
    rw [bits_slice ⟨count,by omega⟩ ⟨bank,hb⟩]
    exact List.mem_map.mpr ⟨i,List.mem_range.mpr hi,rfl⟩
  have h:=localH.constr 0 (Nat.two_pow_pos _) _ member
  change (1:Fp)*(tr.cell t 0 ((if bank=0 then 686 else 1082)+i)+ -(0:Fp))=0 at h
  grind

private theorem zero_bits (row : Nat→Fp) (base n : Nat) (zero : ∀i,i<n → row (base+i)=0) :
    (instructionBitExpr base n).evalWith (instructionAddEnv row)=0 := by
  induction n generalizing base with
  | zero=>rfl
  | succ n ih=>
    have head : row base=0:=by simpa using zero 0 (by omega)
    have tail:=ih (base+1) (by intro i hi;have h:=zero (i+1) (by omega);simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h)
    change row base+Fp.ofNat 2*(instructionBitExpr (base+1) n).evalWith (instructionAddEnv row)=0
    rw [head,tail];grind

theorem prepared_typed_initial_local_limb (count : Nat) (hc : count≤4)
    (tr : Trace Fp) (t : Nat) (pub : List Fp)
    (localH : TableLocal (preparedTypedLiteralExecTable count) tr t pub)
    (slot limb : Nat) (hs : slot<4) (hl : limb<4) :
    preparedTypedLocalLimb (tr.cell t 0) slot limb=0 := by
  apply zero_bits
  intro i hi
  have bank: (if limb<2 then 0 else 1)<2:=by split <;> decide
  have index:32*slot+16*(limb%2)+i<128:=by have hm:=Nat.mod_lt limb (by decide : 0<2);omega
  have h:=prepared_typed_initial_local_bit count hc tr t pub localH (if limb<2 then 0 else 1) (32*slot+16*(limb%2)+i) bank index
  unfold preparedTypedLocalBase
  split <;> rename_i z
  all_goals simp only [z,ite_true,ite_false,Nat.reduceEqDiff] at h ⊢
  all_goals simpa only [Nat.add_assoc] using h

theorem prepared_typed_initial_local_word (count : Nat) (hc : count≤4)
    (tr : Trace Fp) (t : Nat) (pub : List Fp)
    (localH : TableLocal (preparedTypedLiteralExecTable count) tr t pub)
    (slot : Nat) (hs : slot<4) : preparedTypedLocalWord (tr.cell t 0) slot=0 := by
  unfold preparedTypedLocalWord instructionAdd64Word
  rw [prepared_typed_initial_local_limb count hc tr t pub localH slot 0 hs (by decide),
    prepared_typed_initial_local_limb count hc tr t pub localH slot 1 hs (by decide),
    prepared_typed_initial_local_limb count hc tr t pub localH slot 2 hs (by decide),
    prepared_typed_initial_local_limb count hc tr t pub localH slot 3 hs (by decide)]
  rfl

/-- First-row words and authenticated public type tags equal the real prepared
function's i32/i64 default locals, not an untyped zero array. -/
theorem prepared_typed_entry_frame (count : Nat) (pf : PFunc) (fn : Nat) (pub : List Fp)
    (checked : preparedTypedCodeCheck count pf fn pub=true)
    (tr : Trace Fp) (t : Nat) (localH : TableLocal (preparedTypedLiteralExecTable count) tr t pub)
    (p : Prepared) (fi : Nat) :
    (preparedWasmEntryFrame p fi pf).locals=preparedTypedLocalArray (tr.cell t 0) count := by
  obtain ⟨_,bound,size,_,_,types,_⟩:=prepared_typed_code_shape count pf fn pub checked
  change pf.locals.map Val.default=preparedTypedLocalArray (tr.cell t 0) count
  apply Array.ext
  · simp [preparedTypedLocalArray,size]
  · intro i hi hj
    have hidx:i<pf.locals.size:=by simpa using hi
    have ic:i<count:=by omega
    have word:=prepared_typed_initial_local_word count bound tr t pub localH i (by omega)
    have tag:tr.cell t 0 (1210+i)=(if pf.locals[i]?=some VT.i64 then 1 else 0):=
      (prepared_typed_source_local_type count bound tr t 0 pub localH (Nat.two_pow_pos _) i (by omega)).trans
        (prepared_typed_local_type count pf fn pub checked i (by omega))
    have ty:=types (pf.locals[i]) (by simpa using Array.getElem_mem hidx)
    simp only [Array.getElem_map,preparedTypedLocalArray,List.getElem_toArray,List.getElem_map,List.getElem_range,
      preparedTypedLocalValue,tag,word]
    rw [Array.getElem?_eq_getElem hidx]
    rcases ty with z|z
    all_goals simp [z,Val.default]
    all_goals decide
end NearCompression
