import ZkFormal.Sha.Sound.Bits
import NearSpecV3.Wasm.Numerics
namespace NearCompression
open ZkFormal.Sha.View ZkFormal.Sha.Sound NearSpecV3.Wasm

private theorem constant_bits (s m : Nat) :
    ofBits (fun _=>s) m+s=2^m*s := by
  induction m with
  | zero=>simp [ofBits]
  | succ m ih=>
    rw [ofBits_succ,Nat.pow_succ,Nat.mul_right_comm (2^m) 2 s]
    omega

private theorem extended_sum (f : Nat→Nat) (k n m : Nat) (kn:k≤n) (nm:n≤m) :
    ofBits (fun b=>if b<k then f b else if b<n then f (k-1) else 0) m=
      ofBits f k+(2^n-2^k)*f (k-1) := by
  let g:=fun b=>if b<k then f b else if b<n then f (k-1) else 0
  have low : ofBits g k=ofBits f k := ofBits_congr (by intro b hb;simp [g,hb])
  have mid : ofBits (fun b=>g (k+b)) (n-k)=ofBits (fun _=>f (k-1)) (n-k) :=
    ofBits_congr (by intro b hb;simp [g,show ¬k+b<k by omega,show k+b<n by omega])
  have high : ofBits (fun b=>g (n+b)) (m-n)=0 := by
    have eq := ofBits_congr (f:=fun b=>g (n+b)) (g:=fun _=>0) (n:=m-n)
      (by intro b hb;simp [g,show ¬n+b<k by omega,show ¬n+b<n by omega])
    rw [eq]
    have zero:=constant_bits 0 (m-n)
    omega
  have split1:=ofBits_add g n (m-n)
  have split2:=ofBits_add g k (n-k)
  rw [Nat.add_sub_of_le nm,high,Nat.mul_zero,Nat.add_zero] at split1
  rw [Nat.add_sub_of_le kn,low,mid] at split2
  change ofBits g m=_
  rw [split1,split2]
  have cp:=constant_bits (f (k-1)) (n-k)
  have pow : 2^n=2^k*2^(n-k) := by rw [←Nat.pow_add,Nat.add_sub_of_le kn]
  have order : 2^k≤2^n := Nat.pow_le_pow_right (by decide) kn
  have scaled:=congrArg (fun x=>2^k*x) cp
  simp only [Nat.mul_add] at scaled
  rw [←Nat.mul_assoc] at scaled
  rw [←pow] at scaled
  rw [Nat.sub_mul]
  omega

/-- Exact bit replication agrees with the actual Wasm signed-load operation.
Only legal integer load widths are admitted; there is no signed-field cast. -/
theorem prepared_memory_sign_extension (f : Nat→Nat) (k n : Nat)
    (bits : ∀b,b<k→f b≤1) (ks:k∈[8,16,32]) (ns:n∈[32,64]) (kn:k≤n) :
    ofBits (fun b=>if b<k then f b else if b<n then f (k-1) else 0) 64=
      Num.extendS n k (ofBits f k) := by
  have small:ofBits f k<2^k:=ofBits_lt bits
  have sign:=bits (k-1) (by simp only [List.mem_cons,List.not_mem_nil,or_false] at ks;omega)
  have top:=ofBits_succ f (k-1)
  have kp:0<k:=by simp only [List.mem_cons,List.not_mem_nil,or_false] at ks;omega
  rw [Nat.sub_add_cancel kp] at top
  have low:ofBits f (k-1)<2^(k-1):=ofBits_lt (by intro b hb;exact bits b (by omega))
  have nm:n≤64:=by simp only [List.mem_cons,List.not_mem_nil,or_false] at ns;omega
  rw [extended_sum f k n 64 kn nm]
  unfold Num.extendS Num.signed Num.wrap
  rw [Nat.mod_eq_of_lt small]
  simp only [List.mem_cons,List.not_mem_nil,or_false] at ks ns
  rcases ks with rfl|rfl|rfl <;> rcases ns with rfl|rfl <;>
    simp only [Nat.reduceSub,Nat.reducePow] at * <;>
    split <;> omega
end NearCompression
