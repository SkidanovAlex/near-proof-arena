import ZkFormal.NearV3.Render.CodecDefs

/-! Integer pass of the codec record rows inside a field (`gg < 7`). -/
namespace ZkFormal.NearV3.Render.Cdc
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen
open ZkFormal.NearV3.Sched.Codec ZkFormal.Chacha.Table.E ZkFormal.NearV3.Candidates.SchedSetAll

set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Record row `(f, gg)`, `gg < 7`, followed by `(f, gg + 1)` of the same link. -/
theorem rec_in_int (I : Inst) (R : Rec) (f gg bpo bpr apv apostv bigv bpo' bpr' apv' apostv' bigv' : Nat)
    (hf : f < 3) (hg : gg < 7) (Z : ZEnv)
    (hcur : ∀ c, Z.cur c = lookup (recA I R f gg bpo bpr apv apostv bigv) c 0)
    (hnxt : ∀ c, Z.nxt c = lookup (recA I R f (gg + 1) bpo' bpr' apv' apostv' bigv') c 0)
    (hl : Z.last = 0) (hfi : Z.first = 0) (hbpo : bpo < 256) (hbpr : bpr < 256)
    (hid : f < 2 → bpr = b2n I.pres * bpo) (hpz0 : I.pres = false → bpr = 0) (hpz : f = 2 → 3 ≤ gg → bpo = 0)
    (hap : f = 2 → apv' = apv + (if gg < 3 then 256 ^ gg * bpr else 0))
    (hapost : f = 2 → apostv' = apostv + (if gg < 3 then 256 ^ gg * bpo else 0))
    (hbig : f = 2 → bigv' = if bigv = 1 ∨ (3 ≤ gg ∧ bpr ≠ 0) then 1 else 0) (hbig1 : bigv ≤ 1)
    (hA0r : R.hasC = false → apRv R = 0) (hA0b : R.hasC = false → bigRv R = 0) :
    ∀ e ∈ constraints, e ∉ modE → zev Z e = 0 := by
  have hzt := zt0_le I
  have htz := tv_zt0 I
  have hcbv := cbv_le I R
  have hbrv := bigRv_le R
  rcases (show f = 0 ∨ f = 1 ∨ f = 2 by omega) with rfl | rfl | rfl <;>
  rcases (show gg = 0 ∨ gg = 1 ∨ gg = 2 ∨ gg = 3 ∨ gg = 4 ∨ gg = 5 ∨ gg = 6 by omega)
    with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  (try simp only [Nat.reduceLT, Nat.reduceLeDiff, forall_const, OfNat.ofNat_ne_zero, Nat.succ_ne_self,
    reduceCtorEq, false_implies, true_implies, ite_true, ite_false, Nat.reducePow, Nat.reduceMul,
    Nat.add_zero, Nat.zero_add, Nat.one_mul] at hid hpz hap hapost hbig) <;>
  codec_int

end ZkFormal.NearV3.Render.Cdc
