import ZkFormal.NearV3.Render.CodecFast

/-! Integer pass of the codec record rows inside a field (`gg < 7`). -/
namespace ZkFormal.NearV3.Render.Cdc
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen
open ZkFormal.NearV3.Sched.Codec ZkFormal.Chacha.Table.E ZkFormal.NearV3.Candidates.SchedSetAll

set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-! One theorem per row case `(f, gg)`: `rec_in_int` used to prove all 21 cases in a single proof
term, which the independent kernel lean4lean (a judge rechecker) could not check in the memory
available (> 31 GB; its caches live per declaration). Each `rec_in_int_F_G` has the hypotheses of
`rec_in_int` plus `f = F`, `gg = G`, and runs the original tactic script on exactly the context the
original case split produced (docs/logs/v3-recheck-2026-10.md); the integer pass is `codec_fast`
(`CodecFast`, docs/logs/v3-elab-budget-2026-10.md). -/

set_option hygiene false in
/-- `rec_in_case n F G`: the theorem `n`, case `f = F`, `gg = G` of `rec_in_int`. -/
local macro "rec_in_case " n:ident fv:num gv:num : command => `(
theorem $n:ident (I : Inst) (R : Rec) (f gg bpo bpr apv apostv bigv bpo' bpr' apv' apostv' bigv' : Nat)
    (hf : f < 3) (hg : gg < 7) (Z : ZEnv)
    (hcur : ∀ c, Z.cur c = lookup (recA I R f gg bpo bpr apv apostv bigv) c 0)
    (hnxt : ∀ c, Z.nxt c = lookup (recA I R f (gg + 1) bpo' bpr' apv' apostv' bigv') c 0)
    (hl : Z.last = 0) (hfi : Z.first = 0) (hbpo : bpo < 256) (hbpr : bpr < 256)
    (hid : f < 2 → bpr = b2n I.pres * bpo) (hpz0 : I.pres = false → bpr = 0) (hpz : f = 2 → 3 ≤ gg → bpo = 0)
    (hap : f = 2 → apv' = apv + (if gg < 3 then 256 ^ gg * bpr else 0))
    (hapost : f = 2 → apostv' = apostv + (if gg < 3 then 256 ^ gg * bpo else 0))
    (hbig : f = 2 → bigv' = if bigv = 1 ∨ (3 ≤ gg ∧ bpr ≠ 0) then 1 else 0) (hbig1 : bigv ≤ 1)
    (hA0r : R.hasC = false → apRv R = 0) (hA0b : R.hasC = false → bigRv R = 0)
    (ef : f = $fv) (eg : gg = $gv) :
    ∀ e ∈ constraints, e ∉ modE → zev Z e = 0 := by
  have hzt := zt0_le I
  have htz := tv_zt0 I
  have hcbv := cbv_le I R
  have hbrv := bigRv_le R
  subst ef; subst eg
  (try simp only [Nat.reduceLT, Nat.reduceLeDiff, forall_const, OfNat.ofNat_ne_zero, Nat.succ_ne_self,
    reduceCtorEq, false_implies, true_implies, ite_true, ite_false, Nat.reducePow, Nat.reduceMul,
    Nat.add_zero, Nat.zero_add, Nat.one_mul] at hid hpz hap hapost hbig)
  codec_fast)

rec_in_case rec_in_int_0_0 0 0
rec_in_case rec_in_int_0_1 0 1
rec_in_case rec_in_int_0_2 0 2
rec_in_case rec_in_int_0_3 0 3
rec_in_case rec_in_int_0_4 0 4
rec_in_case rec_in_int_0_5 0 5
rec_in_case rec_in_int_0_6 0 6
rec_in_case rec_in_int_1_0 1 0
rec_in_case rec_in_int_1_1 1 1
rec_in_case rec_in_int_1_2 1 2
rec_in_case rec_in_int_1_3 1 3
rec_in_case rec_in_int_1_4 1 4
rec_in_case rec_in_int_1_5 1 5
rec_in_case rec_in_int_1_6 1 6
rec_in_case rec_in_int_2_0 2 0
rec_in_case rec_in_int_2_1 2 1
rec_in_case rec_in_int_2_2 2 2
rec_in_case rec_in_int_2_3 2 3
rec_in_case rec_in_int_2_4 2 4
rec_in_case rec_in_int_2_5 2 5
rec_in_case rec_in_int_2_6 2 6

set_option hygiene false in
/-- `rec_in_apply n`: close the current case of `rec_in_int` with the case theorem `n`. -/
local macro "rec_in_apply " n:ident : tactic => `(tactic|
  exact $n:ident I R f gg bpo bpr apv apostv bigv bpo' bpr' apv' apostv' bigv' hf hg Z hcur hnxt hl hfi
    hbpo hbpr hid hpz0 hpz hap hapost hbig hbig1 hA0r hA0b ef eg)

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
  rcases (show f = 0 ∨ f = 1 ∨ f = 2 by omega) with ef | ef | ef <;>
  rcases (show gg = 0 ∨ gg = 1 ∨ gg = 2 ∨ gg = 3 ∨ gg = 4 ∨ gg = 5 ∨ gg = 6 by omega)
    with eg | eg | eg | eg | eg | eg | eg
  · rec_in_apply rec_in_int_0_0
  · rec_in_apply rec_in_int_0_1
  · rec_in_apply rec_in_int_0_2
  · rec_in_apply rec_in_int_0_3
  · rec_in_apply rec_in_int_0_4
  · rec_in_apply rec_in_int_0_5
  · rec_in_apply rec_in_int_0_6
  · rec_in_apply rec_in_int_1_0
  · rec_in_apply rec_in_int_1_1
  · rec_in_apply rec_in_int_1_2
  · rec_in_apply rec_in_int_1_3
  · rec_in_apply rec_in_int_1_4
  · rec_in_apply rec_in_int_1_5
  · rec_in_apply rec_in_int_1_6
  · rec_in_apply rec_in_int_2_0
  · rec_in_apply rec_in_int_2_1
  · rec_in_apply rec_in_int_2_2
  · rec_in_apply rec_in_int_2_3
  · rec_in_apply rec_in_int_2_4
  · rec_in_apply rec_in_int_2_5
  · rec_in_apply rec_in_int_2_6

end ZkFormal.NearV3.Render.Cdc
