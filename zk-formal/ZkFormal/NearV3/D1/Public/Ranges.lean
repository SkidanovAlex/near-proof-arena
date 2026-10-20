import ZkFormal.NearV3.D1.Prep.Spec
import ZkFormal.NearV3.D1.Public.ExtPrep
import ZkFormal.NearV3.Rcpt.Extract.V.PreparedRanges

/-!
# `ZkFormal.NearV3.D1.Public.Ranges` — `ReceiptPublicRanges` of the verifier's tape (P0)

Lane `v3-d1-phase2`, item P0.  The hypothesis `ReceiptPublicRanges` of `RcptD1.rcptD1_view`:
the header's receipt count `PH_N` and body length `PH_BLEN` decode below `P`.

* Below position 202 and from position 26 on (after the tag), the D1 tape is D0a's tape of
  `p.base` (`preparedD1_getD_hdr`), so both fields read as in D0a (`header_receipt_count`,
  `header_body_length` at `p.base`).
* `PH_N = M0 + n`: `M0 ≤ 2·NT0` (`prepD1_m0_t0`), and `n` is bounded by the compute guard
  `(|locals| + n − 1)·G < gasLimit ≤ 10¹⁵` (`prepClaimD1_gas_limit`): `PH_N ≤ 2·NT0 + 4,500`.
* `PH_BLEN = |body|`, which is below D0a's tape of `p.base`, hence below the D1 tape, hence
  below `P`.
-/

namespace ZkFormal.NearV3.D1.Public

open NearSpec NearSpecV3 ZkFormal.V2 ZkFormal.Algebra ZkFormal.NearV3.Public ZkFormal.NearV3.D1
open ZkFormal.NearV3.Sched

set_option maxHeartbeats 4000000 in
/-- `prepClaimD1` enforces the chunk gas limit `≤ 10¹⁵` on the context it returns. -/
theorem prepClaimD1_gas_limit {cb : Bytes} {pc : PrepCD1} (h : prepClaimD1 cb = .ok pc) :
    pc.pc.ctxB2.gasLimit ≤ maxGasLimitD0 := by
  unfold prepClaimD1 at h
  repeat' (first
    | (obtain ⟨_, hs, hn⟩ := bind_ok h; clear h; have h := hn; clear hn
       try (have hg := check_ok hs)
       try (exact False.elim (throw_ne hs))
       clear hs)
    | (split at h)
    | (dsimp only at h))
  all_goals try (cases h; done)
  all_goals try (exfalso; exact throw_ne (by assumption))
  all_goals
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    dsimp only [blockCtx]
    grind only [Bool.decide_eq_true]

/-- **The receipt count of a successful `prepD1`**: `PH_N = M0 + n ≤ 2·NT0 + 5000`. -/
theorem prepD1_count_bound {cb : Bytes} {h : HintD1} {p : PrepD1} (hp : prepD1 cb h = .ok p) :
    p.base.hdr.n = p.m0 + h.n ∧ p.base.hdr.n ≤ 2 * NT0 + 5000 := by
  have hm := (prepD1_m0_t0 hp).1
  obtain ⟨w, hw, rfl⟩ := prepD1_spec hp
  have hg := prepClaimD1_gas_limit hw.claim
  have hc := hw.compute
  refine ⟨rfl, ?_⟩
  change w.loc.leaves.length + h.n ≤ _
  change w.loc.leaves.length ≤ _ at hm
  change w.pc.ctxB2.gasLimit ≤ _ at hg
  unfold PrepD1Run.nr at hc
  unfold maxGasLimitD0 at hg
  unfold Params.G Params.newActionReceiptExec Params.transferExec at hc
  unfold NT0 at hm ⊢
  omega

/-- Below the descriptors and after the tag, the D1 tape is D0a's tape of `p.base`. -/
theorem preparedD1_getD_hdr (p : PrepD1) (ov : Nat) (hr : RootsSized p.base) {j : Nat}
    (h1 : 26 ≤ j) (h2 : j < 202) :
    (preparedBytesD1 p ov).getD j 0 = (preparedBytes p.base ov).getD j 0 := by
  rw [preparedD1_header p ov hr h2, headerD1_getD p ov (by rw [prep_tag_prefix_length]; exact h1),
    prepared_header p.base ov hr h2]

theorem pubBytes_hdr (p : PrepD1) (ov : Nat) (hr : RootsSized p.base) {off : Nat}
    (h1 : 26 ≤ off) (h2 : off + 4 ≤ 202) :
    ZkFormal.Near.pubBytes (ZkFormal.Udr.pubOf Fp (preparedBytesD1 p ov)) off 4 =
      ZkFormal.Near.pubBytes (ZkFormal.Udr.pubOf Fp (preparedBytes p.base ov)) off 4 := by
  rw [pubBytes_pubOf, pubBytes_pubOf]
  apply List.map_congr_left
  intro j hj
  rw [List.mem_range] at hj
  rw [preparedD1_getD_hdr p ov hr (by omega) (by omega)]

/-- The D1 tape's `PH_N` field is `p.base.hdr.n`. -/
theorem preparedD1_receipt_count (p : PrepD1) (ov : Nat) (hr : RootsSized p.base)
    (hn : p.base.hdr.n < 256 ^ 4) :
    ZkFormal.Near.leN' (ZkFormal.Near.pubBytes (ZkFormal.Udr.pubOf Fp (preparedBytesD1 p ov))
      ZkFormal.NearV3.PH_N 4) = p.base.hdr.n := by
  rw [pubBytes_hdr p ov hr (by unfold ZkFormal.NearV3.PH_N; omega) (by unfold ZkFormal.NearV3.PH_N; omega)]
  apply ZkFormal.NearV3.RcptV3Proof.public_u32_native _ _ _ hn
  intro k hk
  rw [pub_getD, prepared_header p.base ov hr (by unfold ZkFormal.NearV3.PH_N; omega),
    ZkFormal.NearV3.RcptV3Proof.header_receipt_count p.base ov hk]

/-- The D1 tape's `PH_BLEN` field is the body length. -/
theorem preparedD1_body_count (p : PrepD1) (ov : Nat) (hr : RootsSized p.base)
    (hb : p.base.body.length < 256 ^ 4) :
    ZkFormal.Near.leN' (ZkFormal.Near.pubBytes (ZkFormal.Udr.pubOf Fp (preparedBytesD1 p ov))
      ZkFormal.NearV3.PH_BLEN 4) = p.base.body.length := by
  rw [pubBytes_hdr p ov hr (by unfold ZkFormal.NearV3.PH_BLEN; omega)
    (by unfold ZkFormal.NearV3.PH_BLEN; omega)]
  apply ZkFormal.NearV3.RcptV3Proof.public_u32_native _ _ _ hb
  intro k hk
  rw [pub_getD, prepared_header p.base ov hr (by unfold ZkFormal.NearV3.PH_BLEN; omega),
    header_body_length p.base ov hr hk]

/-- **`ReceiptPublicRanges` of the verifier's tape** (the hypothesis of `RcptD1.rcptD1_view`),
from a successful `prepD1` and a tape below `P`. -/
theorem prepD1_receipt_ranges {cb : Bytes} {h : HintD1} {p : PrepD1} (hp : prepD1 cb h = .ok p)
    (ov : Nat) (hlen : (preparedBytesD1 p ov).length < ZkFormal.Algebra.P) :
    ZkFormal.NearV3.RcptV3Proof.ReceiptPublicRanges (ZkFormal.Udr.pubOf Fp (preparedBytesD1 p ov)) := by
  have hr := prepD1_roots hp
  have hs := prepD1_source_roots hp
  have hP : ZkFormal.Algebra.P < 256 ^ 4 := by unfold ZkFormal.Algebra.P; omega
  have hb0 := prepared_body_size_le p.base ov hr
  have hb1 := prepared_base_length_le p ov hr hs (by omega)
  have hn := (prepD1_count_bound hp).2
  have hnP : p.base.hdr.n < ZkFormal.Algebra.P := by unfold NT0 at hn; unfold ZkFormal.Algebra.P; omega
  constructor
  · rw [preparedD1_receipt_count p ov hr (by omega)]; exact hnP
  · rw [preparedD1_body_count p ov hr (by omega)]; omega

end ZkFormal.NearV3.D1.Public
