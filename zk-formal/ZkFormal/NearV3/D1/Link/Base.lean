import ZkFormal.NearV3.D1.Public.Ranges
import ZkFormal.NearV3.Rcpt.Tables.Size
import ZkFormal.NearV3.D1.Prep.Bounds

/-!
# `ZkFormal.NearV3.D1.Link.Base` — support for the generated link copies (L1)

Lane `v3-d1-phase2`, item L1 (`scripts/rcpt_d1_copy.py --profile link`).  In the copies,
`p : Prep` stands for `q.base` (`q : PrepD1`, the verifier's prepared statement); statements
without a preparation hypothesis take `q.base = p` as an auto-param:

* `d1_base`: closes `q.base = p` from a hypothesis `q.base = p` or `prepD1 _ _ = .ok q ∧ q.base = p`;
* `d1_hdr`: closes `26 ≤ j` for a header position `PH_* + k` (after the tag);
* `preparedD1_header_base` / `bodyD1_le`: the D1 tape's header (after the tag) and body size, in
  the form of D0a's `prepared_header` / `prepared_body_size_le`.
-/

namespace ZkFormal.NearV3.D1.Link

open NearSpec NearSpecV3 ZkFormal.V2 ZkFormal.NearV3.Public ZkFormal.NearV3.D1 ZkFormal.NearV3.D1.Public

macro "d1_base" : tactic =>
  `(tactic| first
    | assumption
    | exact (‹ZkFormal.NearV3.D1.prepD1 _ _ = .ok _ ∧ _›).2)

macro "d1_leaves" : tactic =>
  `(tactic| first
    | assumption
    | exact ZkFormal.NearV3.D1.prepD1_leaves (‹ZkFormal.NearV3.D1.prepD1 _ _ = .ok _ ∧ _›).1)

macro "d1_hdr" : tactic =>
  `(tactic| first
    | omega
    | (simp only [ZkFormal.NearV3.PH_N, ZkFormal.NearV3.PH_OWN, ZkFormal.NearV3.PH_HEIGHT,
        ZkFormal.NearV3.PH_GP, ZkFormal.NearV3.PH_OUT, ZkFormal.NearV3.PH_BURNT, ZkFormal.NearV3.PH_BLEN,
        ZkFormal.NearV3.SizeV3.PH_WOVH] at *; omega))

/-- The D1 tape's header after the tag is D0a's header of `q.base`. -/
theorem preparedD1_header_base (p : Prep) {q : PrepD1} (ov : Nat) (hr : RootsSized p) {j : Nat}
    (hj : j < 202) (h26 : 26 ≤ j) (hq : q.base = p) :
    (preparedBytesD1 q ov).getD j 0 = (headerBytes p ov).getD j 0 := by
  subst hq
  rw [preparedD1_getD_hdr q ov hr h26 hj, prepared_header q.base ov hr hj]

/-- The body is no longer than the D1 tape. -/
theorem bodyD1_le (p : Prep) {q : PrepD1} (ov : Nat) (hr : RootsSized p) (hq : q.base = p) :
    p.body.length ≤ (preparedBytesD1 q ov).length := by
  subst hq
  have hb := data_block_bound (preparedBlocksD1 q) (i := 2) (by rw [preparedBlocksD1_length]; decide)
  change (dataBytes ((preparedBlocksD1 q).take 2)).length +
    (payloadBytes (bodyPayload q.base.body)).length ≤ _ at hb
  rw [payload_length _ 1 (bodyPayload_width q.base.body), bodyPayload_length, Nat.mul_one] at hb
  have hl := encodeD1_length (headerBytesD1 q ov) (extBytes q) (preparedBlocksD1 q)
  have e1 : preparedBytesD1 q ov = encodeD1 (headerBytesD1 q ov) (extBytes q) (preparedBlocksD1 q) := rfl
  rw [← e1] at hl
  unfold dataStartD1 at hl
  rw [headerBytesD1_length q ov hr] at hl
  omega

end ZkFormal.NearV3.D1.Link
