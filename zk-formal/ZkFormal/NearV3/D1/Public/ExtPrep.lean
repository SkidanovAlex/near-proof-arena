import ZkFormal.NearV3.D1.Public.NewSegs
import ZkFormal.NearV3.D1.Prep.Bounds

/-!
# `ZkFormal.NearV3.D1.Public.ExtPrep` — `ExtOk` of the verifier's tape (P0 × P2)

Lane `v3-d1-phase2`.  For a successful `prepD1` and a tape below the field size:

* `prepD1_o0_le`: `O0 ≤ |body|`. The body is `u32 |newTxs| ‖ newTxs ‖ u32 |out| ‖ fwd ‖
  local refunds ‖ refunds`, and `O0` is the offset of the incoming refunds;
* the tape carries the body twice: once from position 8 (D0a's body segment), once from 8 to
  `O0` (the D1 body-prefix segment). Hence `2·O0 ≤ |tape| + 16 < P + 16` and `O0 < 2^30`
  (`prepD1_o0_lt`);
* `extOk_of_prepD1`: `ExtOk` with `M0, T0 ≤ 2·NT0 < 2^24` (`prepD1_m0_t0`). This is the
  hypothesis of `RcptD1.rcptD1_view`.
-/

namespace ZkFormal.NearV3.D1.Public

open NearSpec NearSpecV3 ZkFormal.V2 ZkFormal.Algebra ZkFormal.NearV3.Public ZkFormal.NearV3.D1
open ZkFormal.NearV3.D1.RcptD1

theorem concatAll_append_length (a b : List Bytes) :
    (concatAll (a ++ b)).length = (concatAll a).length + (concatAll b).length := by
  induction a with
  | nil => simp [concatAll]
  | cons x a ih => simp [concatAll, ih]; omega

set_option maxHeartbeats 4000000 in
/-- `O0` (the incoming refunds' body offset) is at most the body length, and at least `8`. -/
theorem prepD1_o0_le {cb : Bytes} {h : HintD1} {p : PrepD1} (hp : prepD1 cb h = .ok p) :
    8 ≤ p.o0 ∧ p.o0 ≤ p.base.body.length := by
  unfold prepD1 at hp
  repeat' (first
    | (obtain ⟨_, _, hp⟩ := ZkFormal.NearV3.Sched.bind_ok hp)
    | (split at hp)
    | (dsimp only at hp))
  all_goals try (cases hp; done)
  all_goals try (exfalso; exact ZkFormal.NearV3.Sched.throw_ne (by assumption))
  all_goals
    simp only [pure, Except.pure, Except.ok.injEq] at hp
    subst hp
    dsimp only
    simp only [encodeReceipts, List.length_append, u32, leN_length, List.map_append,
      concatAll_append_length]
    omega

theorem dataBytes_length_ge {blocks : List Payload} {i j : Nat} (hij : i < j) (hj : j < blocks.length) :
    (payloadBytes (blocks.getD i [])).length + (payloadBytes (blocks.getD j [])).length ≤
      (dataBytes blocks).length := by
  induction blocks generalizing i j with
  | nil => simp at hj
  | cons b bs ih =>
    cases i with
    | zero =>
      cases j with
      | zero => omega
      | succ j =>
        have hb := data_block_bound bs (i := j) (by simpa using hj)
        simp only [dataBytes, List.flatMap_cons, List.length_append, List.getD_cons_zero,
          List.getD_cons_succ] at hb ⊢
        omega
    | succ i =>
      cases j with
      | zero => omega
      | succ j =>
        have := ih (i := i) (j := j) (by omega) (by simpa using hj)
        simp only [dataBytes, List.flatMap_cons, List.length_append, List.getD_cons_succ] at this ⊢
        omega

theorem prepD1_o0_lt {cb : Bytes} {h : HintD1} {p : PrepD1} (hp : prepD1 cb h = .ok p) (ov : Nat)
    (hlen : (preparedBytesD1 p ov).length < ZkFormal.Algebra.P) : p.o0 < 2 ^ 30 := by
  obtain ⟨h8, hb⟩ := prepD1_o0_le hp
  have hd := dataBytes_length_ge (blocks := preparedBlocksD1 p) (i := 2) (j := 9) (by decide)
    (by rw [preparedBlocksD1_length]; decide)
  have e1 : preparedBytesD1 p ov = encodeD1 (headerBytesD1 p ov) (extBytes p) (preparedBlocksD1 p) := rfl
  have hl := encodeD1_length (headerBytesD1 p ov) (extBytes p) (preparedBlocksD1 p)
  rw [← e1] at hl
  have h2 : (payloadBytes ((preparedBlocksD1 p).getD 2 [])).length = p.base.body.length - 8 := by
    change (payloadBytes (bodyPayload p.base.body)).length = _
    rw [payload_length _ 1 (bodyPayload_width p.base.body), bodyPayload_length, Nat.mul_one]
  have h9 : (payloadBytes ((preparedBlocksD1 p).getD 9 [])).length = p.o0 - 8 := by
    change (payloadBytes (prefixPayload p.base.body p.o0)).length = _
    rw [payload_length _ 1 (prefix_width _ _), Nat.mul_one]
    simp only [prefixPayload, List.length_map, List.length_drop, List.length_take]
    omega
  unfold dataStartD1 at hl
  rw [h2, h9] at hd
  unfold ZkFormal.Algebra.P at hlen
  omega

/-- **`ExtOk` of the verifier's tape**, from a successful `prepD1` (the hypothesis of
`RcptD1.rcptD1_view`). -/
theorem extOk_of_prepD1 {cb : Bytes} {h : HintD1} {p : PrepD1} (hp : prepD1 cb h = .ok p) (ov : Nat)
    (hlen : (preparedBytesD1 p ov).length < ZkFormal.Algebra.P) :
    ExtOk (ZkFormal.Udr.pubOf Fp (preparedBytesD1 p ov)) := by
  obtain ⟨hm, ht⟩ := prepD1_m0_t0 hp
  exact extOk_prepared p ov (prepD1_roots hp) (by unfold NT0 at hm; omega) (by unfold NT0 at ht; omega)
    (prepD1_o0_lt hp ov hlen)

end ZkFormal.NearV3.D1.Public
