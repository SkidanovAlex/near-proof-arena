import ZkFormal.NearV3.Assembly.RenderV3RcptSide
import ZkFormal.NearV3.Rcpt.Candidates.NativePreparedBody

/-!
# The non-table conjuncts of `RenderWitnessV3`: hint codec bounds and header admissibility

* **Hint codec bounds** (`nativeHint_bounds`, `AcceptedV3.hint_bounds`): for an accepted witness,
  the native hint `nativeHint k w m` has `n ≤ 4481 < 256^4`, body `≤ 1,295,017 < 256^4` bytes
  (`accepted_native_body_bound`, the proved `Size.V3.bodyMax`), hence
  `|Hint.encode h| = 8 + |body| ≤ 1,295,025 ≤ v3MaxHintBytes = 1,972,603`.
* **Header admissibility** (`bundle_headerOk`): for any `R : RenderBundleV3 pub` in which some
  table has `log ≥ 4`, the verifier `(VdP nearAirV3).headerOk` accepts `trHdr nearAirV3.toAir
  R.trace`: lengths, `1 ≤ log ≤ maxLog` (each table's `TableLocal`), `log + 4 ≤ 26` (every
  `maxLog ≤ 22`), `nearAirV3_air_wf`, the constraint degrees `≤ 16` at `auxGroup = 2`, and the
  query domain `minQueryLog = 8 ≤ max (log + 4)`.  The header check alone cannot drop the extra
  premise: a header with every table at `log = 1` has query log `5 < 8` and is rejected (whether
  some locally legal bundle has all tables at `log = 1` is a per-table question not settled here).  It holds for
  every bundle whose table 16 is the honest receipt render (log 22, `bundle_headerOk_rcpt`).
-/

namespace ZkFormal.NearV3.Assembly
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Stark ZkFormal.V2 RcptSkeleton

/-- The certificate's auxiliary-group parameter (`g = 2`, as in `RenderV3Bundle.lean`). -/
local instance : ZkFormal.Prover.Np.G.AuxG := ⟨2, by decide⟩

/-! ## Hint codec bounds -/

theorem hint_encode_length (h : Hint) : (Hint.encode h).length = 8 + h.body.length := by
  simp [Hint.encode, borshBytes, u32, leN]
  omega

/-- **Hint codec bounds for the native hint of an accepted witness.** -/
theorem nativeHint_bounds {cb wb : Bytes} {k : WalkD0} {w : StateWitness}
    {m : MainExecutionV3} {p : Prep}
    (hp : prepD0 cb (nativeHint k w m) = .ok p) (hk : walkD0 cb = .ok k)
    (hw : decodeW wb = .ok w) (h : checkD0a B0 cb wb = .ok ()) (hm : m.NativeValid k w) :
    (nativeHint k w m).n < 256 ^ 4 ∧ (nativeHint k w m).body.length < 256 ^ 4 ∧
      (Hint.encode (nativeHint k w m)).length ≤ v3MaxHintBytes := by
  have hrel : RelD0a B0 cb wb := (relD0a_iff B0 cb wb).mpr h
  have hg : k.slotB2.gasLimit ≤ maxGasLimitD0 := by
    simpa only [a1, hk, decide_eq_true_eq] using hrel.2.1
  have hn := applyNewChunk_receipt_bound hm.run hg
  have hb := ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.accepted_native_body_bound hp hk hw h hm
  rw [ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate.prepD0_body_eq hp] at hb
  refine ⟨?_, ?_, ?_⟩
  · change (appliedReceipts k w).length < 256 ^ 4
    omega
  · omega
  · rw [hint_encode_length]
    unfold v3MaxHintBytes
    omega

theorem AcceptedV3.hint_bounds {cb wb : Bytes} (A : AcceptedV3 cb wb) :
    (nativeHint A.k A.w A.m).n < 256 ^ 4 ∧ (nativeHint A.k A.w A.m).body.length < 256 ^ 4 ∧
      (Hint.encode (nativeHint A.k A.w A.m)).length ≤ v3MaxHintBytes :=
  nativeHint_bounds A.hp A.hk A.hw A.h A.hm

/-! ## Header admissibility -/

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
/-- Every table cap of `nearAirV3` is at most 22. -/
theorem nearAirV3_maxLog_le : nearAirV3Air.tables.all (fun T => decide (T.maxLog ≤ 22)) = true := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
/-- Every table's constraint degree at `auxGroup = 2` is at most the blowup `16`. -/
theorem nearAirV3_degree_le :
    nearAirV3Air.tables.all (fun T => decide (T.degree 2 ≤ 2 ^ 4)) = true := by
  decide +kernel

theorem le_foldr_max {l : List Nat} {x : Nat} (h : x ∈ l) : x ≤ l.foldr max 0 := by
  induction l with
  | nil => simp at h
  | cons a l ih =>
    simp only [List.foldr_cons]
    rcases List.mem_cons.mp h with rfl | h
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih h) (Nat.le_max_right _ _)

/-- **Header admissibility of a render bundle** in which some table has `log ≥ 4`. -/
theorem bundle_headerOk {pub : List Fp} (R : RenderBundleV3 pub)
    (hq : ∃ t, t < nearAirV3.tables.length ∧ 4 ≤ R.trace.log t) :
    (ZkFormal.Prover.Np.G.VdP nearAirV3).headerOk (ZkFormal.Prover.trHdr nearAirV3.toAir R.trace) = true := by
  rw [ZkFormal.V2.headerOk_eqP]
  change (Stark.headerOk nearAirV3Air _ _ && decide (minQueryLog ≤ queryLog nearAirV3Air _ _)) = true
  have hlen : nearAirV3Air.tables.length = 25 := rfl
  have hhdr : ZkFormal.Prover.trHdr nearAirV3.toAir R.trace = (List.range 25).map R.trace.log := rfl
  rw [hhdr]
  have hmax := List.all_eq_true.mp nearAirV3_maxLog_le
  have hloc : ∀ t (ht : t < 25), 1 ≤ R.trace.log t ∧ R.trace.log t ≤ (nearAirV3Air.tables[t]'(by rw [hlen]; exact ht)).maxLog :=
    fun t ht => ⟨(R.local_at t ht).log_ge, (R.local_at t ht).log_le⟩
  have hA : Stark.headerOk nearAirV3Air ZkFormal.Prover.Np.G.dp ((List.range 25).map R.trace.log) = true := by
    unfold Stark.headerOk
    rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true]
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
    · simp [hlen]
    · apply List.all_eq_true.mpr
      rintro ⟨T, l⟩ hm
      obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp hm
      simp only [List.length_zip, List.length_map, List.length_range, hlen, Nat.min_self] at hi
      simp only [List.getElem_zip, List.getElem_map, List.getElem_range, Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      have h1 := hloc i hi
      have h2 : (nearAirV3Air.tables[i]'(by rw [hlen]; exact hi)).maxLog ≤ 22 := by
        have := hmax _ (List.getElem_mem (by rw [hlen]; exact hi))
        simpa using this
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      change ((1 ≤ R.trace.log i ∧ R.trace.log i ≤ _) ∧ R.trace.log i + 4 ≤ 26) ∧ R.trace.log i + 4 ≤ 26
      omega
    · exact nearAirV3_air_wf
    · apply List.all_eq_true.mpr
      intro T hT
      show decide (T.degree 2 ≤ 2 ^ 4) = true
      exact List.all_eq_true.mp nearAirV3_degree_le T hT
  have hB : minQueryLog ≤ queryLog nearAirV3Air ZkFormal.Prover.Np.G.dp ((List.range 25).map R.trace.log) := by
    obtain ⟨t, ht, h4⟩ := hq
    change 8 ≤ ((layout nearAirV3Air _ ((List.range 25).map R.trace.log)).map (·.lde)).foldr max 0
    apply Nat.le_trans _ (le_foldr_max (x := R.trace.log t + 4) ?_)
    · omega
    · simp only [layout, List.map_map, List.mem_map]
      refine ⟨(nearAirV3Air.tables[t]'(by rw [hlen]; exact ht), R.trace.log t), ?_, rfl⟩
      apply List.mem_iff_getElem.mpr
      refine ⟨t, by simp [hlen]; exact ht, ?_⟩
      simp [List.getElem_zip, List.getElem_map, List.getElem_range]
  simp only [hA, hB, decide_true, Bool.and_self]
/-- **Header admissibility of every bundle using the honest receipt render** (table 16 has log
`22`). -/
theorem bundle_headerOk_rcpt {cb wb : Bytes} (A : AcceptedV3 cb wb) (R : RenderBundleV3 A.pub)
    (h16 : R ⟨16, by decide⟩ = A.rcptRenders.rcpt) :
    (ZkFormal.Prover.Np.G.VdP nearAirV3).headerOk (ZkFormal.Prover.trHdr nearAirV3.toAir R.trace) = true := by
  apply bundle_headerOk R
  refine ⟨16, by decide, ?_⟩
  rw [(R.trace_at 16 (by decide)).1, h16]
  show 4 ≤ (rcptTraceAlignedQ A.pub A.rcptInput).log 16
  rw [rcptTraceAlignedQ_log]
  omega

end ZkFormal.NearV3.Assembly
