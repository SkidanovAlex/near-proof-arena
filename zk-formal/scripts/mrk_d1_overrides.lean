/-
Hand-written deltas for the generated `mrkV3` copies (`scripts/rcpt_d1_copy.py --profile mrk`,
lane v3-d1-phase2, V5).  Not a Lean module; format as `scripts/rcpt_d1_overrides.lean`.

The only change of `nearAirV3D1`'s table 23 is the height cap `2^20` (D0a: `2^19`).
-/

-- @override ZkFormal.NearV3.Candidates.MerkleLog19.height_le
theorem height_le_m20 (hL : TableLocal ZkFormal.NearV3.D1.MrkD1.tableB tr T_MRK pub) : tr.height T_MRK ≤ 2 ^ 20 := by
  have := hL.log_le; unfold Trace.height; exact Nat.pow_le_pow_right (by omega) this
