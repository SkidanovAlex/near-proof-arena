import ZkFormal.NearV3.Render.CodecFast

/-! Integer pass of the codec header rows. -/
namespace ZkFormal.NearV3.Render.Cdc
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen
open ZkFormal.NearV3.Sched.Codec ZkFormal.Chacha.Table.E ZkFormal.NearV3.Candidates.SchedSetAll

set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Header rows `p < 4` (next row: header `p + 1`). -/
theorem hdr_int (I : Inst) (p : Nat) (hp : p < 4) (Z : ZEnv)
    (hcur : ∀ c, Z.cur c = lookup (hdrA I p) c 0) (hnxt : ∀ c, Z.nxt c = lookup (hdrA I (p+1)) c 0)
    (hl : Z.last = 0) (hf : p = 0 ∨ Z.first = 0) (hN : I.N < 65536)
    (hNN : (I.n : Int) * I.n = I.N) (hb : I.base < 2^24) (hfa : I.fair < 2^24) :
    ∀ e ∈ constraints, e ∉ modE → zev Z e = 0 := by
  have hzt := zt0_le I
  have htz := tv_zt0 I
  rcases (show p = 0 ∨ p = 1 ∨ p = 2 ∨ p = 3 by omega) with rfl | rfl | rfl | rfl
  · codec_fast
  all_goals (have hf : Z.first = 0 := by simpa using hf
             codec_fast)

end ZkFormal.NearV3.Render.Cdc
