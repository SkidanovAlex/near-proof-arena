import NearCompression.SHA384BatchedPhase

namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 NearSpecV3.SHA512

/-- Padding rows cannot activate a phase or the initial-IV receive. These
are the selectors used by every batched core interaction. -/
theorem sha384_batch_padding_selectors (n : Nat) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384BatchedAir n) pub tr) (bound : sha384PaddedLength n/128<P)
    (r : Nat) (hr : r<tr.height 0) (padding : 80*(sha384PaddedLength n/128)≤r) :
    tr.cell 0 r 5232=0 ∧ Expr.isFirst.eval tr 0 r pub=0 ∧
    ∀ i,i<80 → tr.cell 0 r (5152+i)=0 := by
  have inactive : tr.cell 0 r 5232=0 := by
    rcases sha384_batch_active_boolean n pub tr h r hr with zero | one
    · exact zero
    · have small := (sha384_batch_active_iff n pub tr h bound r hr).mp one
      omega
  have positive : 0<sha384PaddedLength n/128 := by unfold sha384PaddedLength;omega
  have nonzero : r≠0 := by omega
  refine ⟨inactive,?_,sha384_batch_inactive_phase n pub tr h r hr inactive⟩
  simp [Expr.eval,Expr.evalWith,rowEnv,nonzero]

/-- The active row's block number is uniquely recovered from its field tag;
height and block-count bounds rule out modular aliases. -/
theorem sha384_batch_tag_identifies_block (n : Nat) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384BatchedAir n) pub tr) (bound : sha384PaddedLength n/128<P)
    (r block : Nat) (hr : r<tr.height 0) (active : tr.cell 0 r 5232=1)
    (hb : block<sha384PaddedLength n/128)
    (tag : tr.cell 0 r 5233=Fp.ofNat block) :
    r/80=block ∧ 80*block≤r ∧ r<80*block+80 := by
  have actual := sha384_batch_active_tag n pub tr h r hr active
  have small := sha384_batch_height_small n pub tr h
  have eq := congrArg Fp.toNat (actual.symm.trans tag)
  rw [Fp.toNat_ofNat,Fp.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : r/80<P),Nat.mod_eq_of_lt (by omega : block<P)] at eq
  exact ⟨eq,by omega,by omega⟩

end NearCompression
