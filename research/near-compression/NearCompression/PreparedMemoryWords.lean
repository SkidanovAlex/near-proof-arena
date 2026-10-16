import NearCompression.PreparedMemoryResultBits
import NearCompression.PreparedMemoryExec
import ZkFormal.Sha.Sound.Bits
namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Sha.View ZkFormal.Sha.Sound NearSpecV3.Wasm

def preparedMemoryWord (row : Nat→Fp) (base : Nat) : Nat := ofBits (fun b=>(row (base+b)).toNat) 64

private theorem bits_zero (n : Nat) : ofBits (fun _=>0) n=0 := by
  induction n with
  | zero=>rfl
  | succ n ih=>rw [ofBits_succ,ih];omega

/-- Zero extension of a bit prefix preserves its natural value. -/
theorem prepared_memory_bits_prefix (f : Nat→Nat) (k n : Nat) (bound:k≤n) :
    ofBits (fun b=>if b<k then f b else 0) n=ofBits f k := by
  have split : n=k+(n-k):=by omega
  rw [split,ofBits_add]
  have low : ofBits (fun b=>if b<k then f b else 0) k=ofBits f k :=
    ofBits_congr (by intro b hb;rw [if_pos hb])
  have high : ofBits (fun b=>if k+b<k then f (k+b) else 0) (n-k)=0 := by
    have eq : (fun b=>if k+b<k then f (k+b) else 0)=(fun _=>0) := by
      funext b;rw [if_neg (by omega)]
    rw [eq,bits_zero]
  rw [low,high];omega

theorem prepared_memory_bits_mod (f : Nat→Nat) (k n : Nat) (bound:k≤n)
    (bits:∀b,b<n→f b≤1) : ofBits f k=ofBits f n%2^k := by
  rw [←ofBits_bt]
  apply ofBits_congr
  intro b hb
  exact (bt_ofBits bits (by omega)).symm

/-- The unsigned MEM payload of every store equals actual interpreter
narrowing of the source value, including all seven supported store widths. -/
theorem prepared_memory_store_word (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : TableLocal preparedMemoryLiteralTable tr t pub) (hr:r<tr.height t)
    (selected : Fin 19) (hot:∀i,i<19→tr.cell t r i=if i=selected.val then 1 else 0)
    (store:12≤selected.val) :
    preparedMemoryWord (tr.cell t r) 293=
      preparedMemoryWord (tr.cell t r) 229%256^(storeWidth (preparedMemoryOpcode selected)) := by
  have h:=prepared_memory_literal_bounds tr t r pub localH hr
  have bits : ∀b,b<64→(tr.cell t r (229+b)).toNat≤1 := by
    intro b hb;exact prepared_memory_address_boolean _ h.1 _ (by omega)
  have wb : 8*preparedMemoryWidth selected≤64 := by
    have all : ∀i:Fin 19,8*preparedMemoryWidth i≤64:=by decide
    exact all selected
  have raw : preparedMemoryWord (tr.cell t r) 293=
      ofBits (fun b=>if b<8*preparedMemoryWidth selected then (tr.cell t r (229+b)).toNat else 0) 64 := by
    apply ofBits_congr
    intro b hb
    rw [prepared_memory_store_raw_bits tr t r pub localH hr selected hot store b hb]
    split <;> rfl
  rw [raw,prepared_memory_bits_prefix _ _ _ wb,prepared_memory_bits_mod _ _ _ wb bits]
  have widths : ∀i:Fin 19,12≤i.val→2^(8*preparedMemoryWidth i)=256^(storeWidth (preparedMemoryOpcode i)) := by decide
  rw [widths selected store]
  rfl
end NearCompression
