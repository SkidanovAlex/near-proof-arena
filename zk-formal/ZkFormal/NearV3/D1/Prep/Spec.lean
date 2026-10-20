import ZkFormal.NearV3.D1.Prep.SpecDefs
import ZkFormal.NearV3.D1.Prep.Bounds

/-!
# `ZkFormal.NearV3.D1.Prep.Spec` — `prepD1` decomposed (P2)

Lane `v3-d1-phase2`, item P2.  **`prepD1_spec`**: a successful `prepD1 cb h = .ok p` binds
values `w : PrepD1Run` that pass every check (`w.Ok cb h`), and `p = w.prep h`.
-/

namespace ZkFormal.NearV3.D1

open NearSpec NearSpecV3 Sched ZkFormal.NearV3.D1.Public

set_option maxHeartbeats 4000000 in
/-- **The decomposition of a successful `prepD1`.** -/
theorem prepD1_spec {cb : Bytes} {h : HintD1} {p : PrepD1} (hp : prepD1 cb h = .ok p) :
    ∃ w : PrepD1Run, w.Ok cb h ∧ p = w.prep h := by
  unfold prepD1 at hp
  obtain ⟨⟨pc, txValid, txRoot⟩, hc, hp⟩ := bind_ok hp
  dsimp only at hp
  obtain ⟨txs, htxs, hp⟩ := bind_ok hp
  obtain ⟨newTxs, hntxs, hp⟩ := bind_ok hp
  obtain ⟨refunds, hrf, hp⟩ := bind_ok hp
  obtain ⟨_, hNT, hp⟩ := bind_ok hp
  obtain ⟨_, hTV, hp⟩ := bind_ok hp
  obtain ⟨_, hTR, hp⟩ := bind_ok hp
  obtain ⟨_, hNS, hp⟩ := bind_ok hp
  obtain ⟨st, hst, hp⟩ := bind_ok hp
  obtain ⟨_, hBI, hp⟩ := bind_ok hp
  obtain ⟨_, hNA, hp⟩ := bind_ok hp
  obtain ⟨loc, hloc, hp⟩ := bind_ok hp
  obtain ⟨_, hSH, hp⟩ := bind_ok hp
  obtain ⟨_, hFG, hp⟩ := bind_ok hp
  obtain ⟨_, hFD, hp⟩ := bind_ok hp
  obtain ⟨_, hCO, hp⟩ := bind_ok hp
  obtain ⟨_, hPR, hp⟩ := bind_ok hp
  obtain ⟨_, hGL, hp⟩ := bind_ok hp
  obtain ⟨_, hGU, hp⟩ := bind_ok hp
  obtain ⟨_, hOR, hp⟩ := bind_ok hp
  obtain ⟨_, hCG, hp⟩ := bind_ok hp
  obtain ⟨_, hBW, hp⟩ := bind_ok hp
  obtain ⟨_, hSP, hp⟩ := bind_ok hp
  obtain ⟨_, hTX, hp⟩ := bind_ok hp
  let w : PrepD1Run := ⟨pc, txValid, txRoot, txs, newTxs, refunds, st, loc⟩
  have key : encodedMerkleRoot w.pc.rsData w.pc.rsTotal w.body =
      some (w.pc.H.encodedMerkleRoot, w.pc.H.encodedLength) ∧ p = w.prep h := by
    split at hp
    · exact absurd hp (fun h' => throw_ne h')
    · rename_i emr len he
      obtain ⟨_, h1, hx⟩ := bind_ok hp
      obtain ⟨_, h2, hx⟩ := bind_ok hx
      have e1 := check_ok h1
      have e2 := check_ok h2
      simp only [beq_iff_eq] at e1 e2
      simp only [pure, Except.pure, Except.ok.injEq] at hx
      refine ⟨?_, hx.symm⟩
      subst e1 e2; exact he
  obtain ⟨hrs, hpe⟩ := key
  refine ⟨w, ⟨hc, htxs, hntxs, hrf, ?_, ?_, ?_, check_ok hNS, hst, ?_, check_ok hNA, hloc,
    check_ok hSH, check_ok hFG, check_ok hFD, ?_, check_ok hPR, ?_, ?_, ?_, check_ok hCG,
    check_ok hBW, check_ok hSP, ?_, hrs⟩, hpe⟩
  · exact of_decide_eq_true (check_ok hNT)
  · exact beq_iff_eq.mp (check_ok hTV)
  · exact beq_iff_eq.mp (check_ok hTR)
  · exact List.isEmpty_iff.mp (check_ok hBI)
  · have := check_ok hCO
    simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at this
    exact this
  · exact beq_iff_eq.mp (check_ok hGL)
  · exact beq_iff_eq.mp (check_ok hGU)
  · exact beq_iff_eq.mp (check_ok hOR)
  · exact beq_iff_eq.mp (check_ok hTX)

end ZkFormal.NearV3.D1
