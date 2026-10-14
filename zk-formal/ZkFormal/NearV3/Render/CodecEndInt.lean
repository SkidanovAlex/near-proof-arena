import ZkFormal.NearV3.Render.CodecFast

/-! Integer pass of the codec rows at the block boundaries: field ends, record ends, header → record,
hash and `sha256(all_shards)` rows. -/
namespace ZkFormal.NearV3.Render.Cdc
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen
open ZkFormal.NearV3.Sched.Codec ZkFormal.Chacha.Table.E ZkFormal.NearV3.Candidates.SchedSetAll

set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- The last byte of the sender (`f = 0`) or receiver (`f = 1`) field, followed by the next field's
first byte. -/
theorem rec_fend_int (I : Inst) (R : Rec) (f bpo bpr apv apostv bigv bpo' bpr' apv' apostv' bigv' : Nat)
    (hf : f < 2) (Z : ZEnv)
    (hcur : ∀ c, Z.cur c = lookup (recA I R f 7 bpo bpr apv apostv bigv) c 0)
    (hnxt : ∀ c, Z.nxt c = lookup (recA I R (f + 1) 0 bpo' bpr' apv' apostv' bigv') c 0)
    (hl : Z.last = 0) (hfi : Z.first = 0) (hbpo : bpo < 256) (hbpr : bpr < 256)
    (hid : bpr = b2n I.pres * bpo) (hpz0 : I.pres = false → bpr = 0)
    (h0 : f = 1 → apv' = 0 ∧ apostv' = 0 ∧ bigv' = 0)
    (hA0r : R.hasC = false → apRv R = 0) (hA0b : R.hasC = false → bigRv R = 0) :
    ∀ e ∈ constraints, e ∉ modE → zev Z e = 0 := by
  have hzt := zt0_le I
  have htz := tv_zt0 I
  have hcbv := cbv_le I R
  have hbrv := bigRv_le R
  rcases (show f = 0 ∨ f = 1 by omega) with rfl | rfl
  · codec_fast
  · obtain ⟨h1, h2, h3⟩ := h0 rfl
    subst h1; subst h2; subst h3
    codec_fast

/-- The record end (`f = 2, gg = 7`) followed by the next record's first row. -/
theorem rec_end_int (I : Inst) (R R' : Rec) (bpo bpr apv apostv bigv bpo' bpr' apv' apostv' bigv' : Nat)
    (Z : ZEnv)
    (hcur : ∀ c, Z.cur c = lookup (recA I R 2 7 bpo bpr apv apostv bigv) c 0)
    (hnxt : ∀ c, Z.nxt c = lookup (recA I R' 0 0 bpo' bpr' apv' apostv' bigv') c 0)
    (hl : Z.last = 0) (hfi : Z.first = 0) (hbpo : bpo = 0) (hbpr : bpr < 256)
    (hpz0 : I.pres = false → bpr = 0) (hbig1 : bigv ≤ 1) (hapost : apostv = R.afin)
    (hk : R'.kk = R.kk + 1) (hkN : R.kk + 1 < I.N) (hft : R.ft < 2 ^ 24)
    (hab : b2n R.al * I.base ≤ a1v I R)
    (hA0r : R.hasC = false → apRv R = 0) (hA0b : R.hasC = false → bigRv R = 0) :
    ∀ e ∈ constraints, e ∉ modE → zev Z e = 0 := by
  have hzt := zt0_le I
  have htz := tv_zt0 I
  have hcbv := cbv_le I R
  have hbrv := bigRv_le R
  have ha1 := a1v_def I R
  rcases (show zt0 I = 0 ∨ zt0 I = 1 by omega) with hz | hz <;>
  rcases (show bigRv R = 0 ∨ bigRv R = 1 by omega) with hb | hb <;>
  rcases (show cbv I R = 0 ∨ cbv I R = 1 by omega) with hc | hc <;>
  codec_fast

/-- The last record's end followed by the first sanity-hash row. -/
theorem rec_last_int (I : Inst) (R : Rec) (dig hpre : List Nat) (bpo bpr apv apostv bigv : Nat)
    (Z : ZEnv)
    (hcur : ∀ c, Z.cur c = lookup (recA I R 2 7 bpo bpr apv apostv bigv) c 0)
    (hnxt : ∀ c, Z.nxt c = lookup (hashA I dig hpre 0) c 0)
    (hl : Z.last = 0) (hfi : Z.first = 0) (hbpo : bpo = 0) (hbpr : bpr < 256)
    (hpz0 : I.pres = false → bpr = 0) (hbig1 : bigv ≤ 1) (hapost : apostv = R.afin)
    (hkN : R.kk + 1 = I.N) (hft : R.ft < 2 ^ 24)
    (hab : b2n R.al * I.base ≤ a1v I R)
    (hA0r : R.hasC = false → apRv R = 0) (hA0b : R.hasC = false → bigRv R = 0) :
    ∀ e ∈ constraints, e ∉ modE → zev Z e = 0 := by
  have hzt := zt0_le I
  have htz := tv_zt0 I
  have hcbv := cbv_le I R
  have hbrv := bigRv_le R
  have ha1 := a1v_def I R
  rcases (show zt0 I = 0 ∨ zt0 I = 1 by omega) with hz | hz <;>
  rcases (show bigRv R = 0 ∨ bigRv R = 1 by omega) with hb | hb <;>
  rcases (show cbv I R = 0 ∨ cbv I R = 1 by omega) with hc | hc <;>
  codec_fast

/-- The last header row followed by the first record row (link `0`). -/
theorem hdr_last_int (I : Inst) (R : Rec) (bpo bpr apv apostv bigv : Nat) (Z : ZEnv)
    (hcur : ∀ c, Z.cur c = lookup (hdrA I 4) c 0)
    (hnxt : ∀ c, Z.nxt c = lookup (recA I R 0 0 bpo bpr apv apostv bigv) c 0)
    (hl : Z.last = 0) (hfi : Z.first = 0) (hk : R.kk = 0) (hN : I.N < 65536)
    (hNN : (I.n : Int) * I.n = I.N) (hb : I.base < 2^24) (hfa : I.fair < 2^24) :
    ∀ e ∈ constraints, e ∉ modE → zev Z e = 0 := by
  have hzt := zt0_le I
  have htz := tv_zt0 I
  codec_fast

/-- Sanity-hash row `j < 31` followed by row `j + 1`. -/
theorem hash_int (I : Inst) (dig hpre : List Nat) (j : Nat) (hj : j < 31) (Z : ZEnv)
    (hcur : ∀ c, Z.cur c = lookup (hashA I dig hpre j) c 0)
    (hnxt : ∀ c, Z.nxt c = lookup (hashA I dig hpre (j + 1)) c 0)
    (hl : Z.last = 0) (hfi : Z.first = 0) (hd : dig.getD j 0 < 256) (hp : hpre.getD j 0 < 256) :
    ∀ e ∈ constraints, e ∉ modE → zev Z e = 0 := by
  have hzt := zt0_le I
  have htz := tv_zt0 I
  have hj' : j ≠ 31 := by omega
  have hj'' : j + 1 ≠ 0 := by omega
  codec_fast

/-- The last sanity-hash row followed by the first `sha256(all_shards)` row. -/
theorem hash_last_int (I : Inst) (dig hpre ash : List Nat) (Z : ZEnv)
    (hcur : ∀ c, Z.cur c = lookup (hashA I dig hpre 31) c 0)
    (hnxt : ∀ c, Z.nxt c = lookup (ashA I ash 0) c 0)
    (hl : Z.last = 0) (hfi : Z.first = 0) (hd : dig.getD 31 0 < 256) (hp : hpre.getD 31 0 < 256) :
    ∀ e ∈ constraints, e ∉ modE → zev Z e = 0 := by
  have hzt := zt0_le I
  have htz := tv_zt0 I
  codec_fast

/-- `sha256(all_shards)` row `j < 31` followed by row `j + 1`. -/
theorem ash_int (I : Inst) (ash : List Nat) (j : Nat) (hj : j < 31) (Z : ZEnv)
    (hcur : ∀ c, Z.cur c = lookup (ashA I ash j) c 0)
    (hnxt : ∀ c, Z.nxt c = lookup (ashA I ash (j + 1)) c 0)
    (hl : Z.last = 0) (hfi : Z.first = 0) :
    ∀ e ∈ constraints, e ∉ modE → zev Z e = 0 := by
  have hzt := zt0_le I
  have htz := tv_zt0 I
  have hj' : j ≠ 31 := by omega
  codec_fast

/-- The last `sha256(all_shards)` row followed by the next instance's first header row. -/
theorem ash_last_int (I I' : Inst) (ash : List Nat) (Z : ZEnv)
    (hcur : ∀ c, Z.cur c = lookup (ashA I ash 31) c 0)
    (hnxt : ∀ c, Z.nxt c = lookup (hdrA I' 0) c 0) (hl : Z.last = 0) (hfi : Z.first = 0) :
    ∀ e ∈ constraints, e ∉ modE → zev Z e = 0 := by
  have hzt := zt0_le I
  have htz := tv_zt0 I
  codec_fast

/-- The last `sha256(all_shards)` row of the last instance, followed by zero padding. -/
theorem ash_pad_int (I : Inst) (ash : List Nat) (Z : ZEnv)
    (hcur : ∀ c, Z.cur c = lookup (ashA I ash 31) c 0)
    (hnxt : ∀ c, Z.nxt c = lookup [] c 0) (hl : Z.last = 0) (hfi : Z.first = 0) :
    ∀ e ∈ constraints, e ∉ modE → zev Z e = 0 := by
  have hzt := zt0_le I
  have htz := tv_zt0 I
  codec_fast

end ZkFormal.NearV3.Render.Cdc
