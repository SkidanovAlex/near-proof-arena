import ZkFormal.NearV3.Render.ChachaWords
import ZkFormal.NearV3.Render.BundleSched
import ZkFormal.NearV3.Assembly.TrieBusBalance

/-!
# ZkFormal.NearV3.Render.ChachaBusBalance — the ChaCha-lane buses of the honest bundle

Buses 45 `SSIN` (13 → 10), 46 `SSOUT` (10 → 13), 47 `SSMEM` (10 ↔ 10), 48 `SGEN` (9 → 10),
49 `SSHUF` (10 → 13), 50 `SCHACHA` (8 → 9) of `nearAirV3`.  For a bundle whose table 13 is the
process table `procTraceV3 rs` of the native runs `rs` and whose tables 8, 9, 10 are the ChaCha,
RNG and shuffle renders of `laneReqs rs`, `laneCalls rs`, `laneInsts rs`:

* `balancedAt_ssin`, `balancedAt_ssout`, `balancedAt_sshuf`: process ↔ shuffle (`ChachaLane.in_run`,
  `out_run`, `shuf_run`);
* `balancedAt_ssmem`: the shuffle table's private memory (`Shuffle.Complete.rows_perm`);
* `balancedAt_sgen`: RNG ↔ shuffle (`gen_perm`);
* `balancedAt_schacha`: ChaCha ↔ RNG (`words_lane`, `chacha_lane_perm`);
* **`chacha_buses_balanced`**: on the accepted instance (same premises as `balancedAt_scmp`:
  `PriorCore` blocks of `A`'s trace), the three renders exist (`hW : rngRows ≤ W0` from RelD0a A9,
  `kfin_W0`) and every bundle containing them and the process table balances the six buses.
-/

namespace ZkFormal.NearV3.Assembly
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near ZkFormal.NearV3.Render
open ZkFormal.NearV3.Render.ChachaBus ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen
open ZkFormal.NearV3.Candidates ZkFormal.Chacha.Shuffle.Complete ZkFormal.NearV3.Assembly.CodecDigest
open ZkFormal.NearV3.Sched.Complete (padPV)

theorem covers_ssin_send : Covers B_SSIN true (fun t => t == 13) = true := by decide +kernel
theorem covers_ssin_recv : Covers B_SSIN false (fun t => t == 10) = true := by decide +kernel
theorem covers_ssout_send : Covers B_SSOUT true (fun t => t == 10) = true := by decide +kernel
theorem covers_ssout_recv : Covers B_SSOUT false (fun t => t == 13) = true := by decide +kernel
theorem covers_sshuf_send : Covers B_SSHUF true (fun t => t == 10) = true := by decide +kernel
theorem covers_sshuf_recv : Covers B_SSHUF false (fun t => t == 13) = true := by decide +kernel
theorem covers_ssmem (s : Bool) : Covers B_SSMEM s (fun t => t == 10) = true := by cases s <;> decide +kernel
theorem covers_sgen_send : Covers B_SGEN true (fun t => t == 9) = true := by decide +kernel
theorem covers_sgen_recv : Covers B_SGEN false (fun t => t == 10) = true := by decide +kernel
theorem covers_schacha_send : Covers B_SCHACHA true (fun t => t == 8) = true := by decide +kernel
theorem covers_schacha_recv : Covers B_SCHACHA false (fun t => t == 9) = true := by decide +kernel

theorem pub_lane (b : Nat) (hb : b = B_SSIN ∨ b = B_SSOUT ∨ b = B_SSMEM ∨ b = B_SGEN ∨ b = B_SSHUF ∨ b = B_SCHACHA)
    (s : Bool) (pub m : List Fp) : pubCount nearAirV3 pub b s m = 0 := by
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact pub_off _ _ (by cases s <;> decide +kernel) pub m

theorem filt (k : Nat) (hk : k < 25) : (List.range 25).filter (fun t => t == k) = [k] := by
  revert k; decide

namespace RenderBundleV3
variable {pub : List Fp} (R : RenderBundleV3 pub)

theorem tf_at (t : Nat) (ht : t < nearAirV3.tables.length) : R.tf t = (R ⟨t, ht⟩).tf := by
  simp only [tf, ht, ↓reduceDIte]

/-- One sending and one receiving table. -/
theorem balanced_one (b : Nat) (hb : b = B_SSIN ∨ b = B_SSOUT ∨ b = B_SSMEM ∨ b = B_SGEN ∨ b = B_SSHUF ∨ b = B_SCHACHA)
    (ts tr : Nat) (hts : ts < 25) (htr : tr < 25)
    (h1 : Covers b true (fun t => t == ts) = true) (h2 : Covers b false (fun t => t == tr) = true)
    (h : ∀ m, cnt (sel true (R.tf ts) b) m = cnt (sel false (R.tf tr) b) m) : R.BalancedAt b := by
  intro m
  rw [R.sum_tables true _ m _ h1, R.sum_tables false _ m _ h2, pub_lane b hb, pub_lane b hb, filt ts hts,
    filt tr htr]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
  exact h m

theorem proc_cnt (rs : List Run) (h13 : (R ⟨13, by decide⟩).tr = procTraceV3 rs)
    (hcap : (ProcConcatGeometry.rows rs).length ≤ 2 ^ 22) (b : Nat) (s : Bool)
    (hev : ∀ X t r pub, rowTraffic ProcBoundaryRepair.table.interactions (pvTrace X) t r pub b s = pmsgs b s X)
    (F : Run → List (List Fp)) (hq : pmsgs b s (ProcConcatGeometry.tail rs) = [] ∧ pmsgs b s padPV = [])
    (hrun : ∀ R, (Sched.Complete.procVs R).flatMap (pmsgs b s) = F R) (m : List Fp) :
    cnt (sel s (R.tf 13) b) m = (rs.flatMap F).count m := by
  rw [R.cnt_tf 13 (by decide) s, h13]
  exact table_count rs hcap b s hev F hq hrun 13 pub m

theorem expectedIn_lane (rs : List Run) : expectedIn (laneInsts rs) = rs.flatMap (expectedIn ∘ runInsts) := by
  unfold expectedIn laneInsts; rw [List.flatMap_assoc]; rfl
theorem expectedOut_lane (rs : List Run) : expectedOut (laneInsts rs) = rs.flatMap (expectedOut ∘ runInsts) := by
  unfold expectedOut laneInsts; rw [List.flatMap_assoc]; rfl
theorem expectedShuf_lane (rs : List Run) : expectedShuf (laneInsts rs) = rs.flatMap (expectedShuf ∘ runInsts) := by
  unfold expectedShuf laneInsts; rw [List.map_flatMap]; rfl

theorem cnt_nat (l : List (List Fp)) (m : List Fp) : cnt (natMsgs l) m = l.count m := by
  unfold cnt; rw [natMsgs_toFp]


theorem balancedAt_ssin (rs : List Run) (hR : ∀ R ∈ rs, RunOk R) (hcap : (ProcConcatGeometry.rows rs).length ≤ 2 ^ 22)
    (h13 : (R ⟨13, by decide⟩).tr = procTraceV3 rs) (h10 : R.tf 10 = shufTraffic (laneInsts rs)) : R.BalancedAt B_SSIN := by
  apply R.balanced_one B_SSIN (by simp) 13 10 (by decide) (by decide) covers_ssin_send covers_ssin_recv
  intro m
  rw [R.proc_cnt rs h13 hcap B_SSIN true (fun X t r pub => by rw [eval_in]; rfl) runIn
    ⟨(tail_quiet rs).2.1, (quiet padPV rfl rfl).2.1⟩ run_in m, h10]
  simp only [sel, shufTraffic, ite_true, Bool.false_eq_true, ite_false]
  rw [cnt_nat, expectedIn_lane]
  congr 1
  exact (ZkFormal.Near.flatMap_congr' (fun R hR' => in_run (hR R hR'))).symm

theorem balancedAt_ssout (rs : List Run) (hR : ∀ R ∈ rs, RunOk R) (hcap : (ProcConcatGeometry.rows rs).length ≤ 2 ^ 22)
    (h13 : (R ⟨13, by decide⟩).tr = procTraceV3 rs) (h10 : R.tf 10 = shufTraffic (laneInsts rs)) : R.BalancedAt B_SSOUT := by
  apply R.balanced_one B_SSOUT (by simp) 10 13 (by decide) (by decide) covers_ssout_send covers_ssout_recv
  intro m
  rw [R.proc_cnt rs h13 hcap B_SSOUT false (fun X t r pub => by rw [eval_out]; rfl) runOut
    ⟨(tail_quiet rs).2.2, (quiet padPV rfl rfl).2.2⟩ run_out m, h10]
  simp only [sel, shufTraffic, ite_true]
  rw [cnt_nat, expectedOut_lane]
  congr 1
  exact ZkFormal.Near.flatMap_congr' (fun R hR' => out_run (hR R hR'))

theorem balancedAt_sshuf (rs : List Run) (hR : ∀ R ∈ rs, RunOk R) (hcap : (ProcConcatGeometry.rows rs).length ≤ 2 ^ 22)
    (h13 : (R ⟨13, by decide⟩).tr = procTraceV3 rs) (h10 : R.tf 10 = shufTraffic (laneInsts rs)) : R.BalancedAt B_SSHUF := by
  apply R.balanced_one B_SSHUF (by simp) 10 13 (by decide) (by decide) covers_sshuf_send covers_sshuf_recv
  intro m
  rw [R.proc_cnt rs h13 hcap B_SSHUF false (fun X t r pub => by rw [eval_shuf]; rfl) runShuf
    ⟨(tail_quiet rs).1, (quiet padPV rfl rfl).1⟩ run_shuf m, h10]
  simp only [sel, shufTraffic, ite_true]
  simp only [B_SSHUF, B_SSOUT, B_SSMEM, ite_true, ite_false, show (49 : Nat) ≠ 46 by decide,
    show (49 : Nat) ≠ 47 by decide]
  rw [cnt_nat, expectedShuf_lane]
  congr 1
  exact ZkFormal.Near.flatMap_congr' (fun R hR' => shuf_run (hR R hR'))

theorem balancedAt_ssmem (rs : List Run) (hR : ∀ R ∈ rs, RunOk R) (h10 : R.tf 10 = shufTraffic (laneInsts rs)) : R.BalancedAt B_SSMEM := by
  apply R.balanced_one B_SSMEM (by simp) 10 10 (by decide) (by decide) (covers_ssmem true) (covers_ssmem false)
  intro m
  rw [h10]
  simp only [sel, shufTraffic, ite_true, Bool.false_eq_true, ite_false]
  simp only [B_SSMEM, B_SSOUT, B_SSIN, show (47 : Nat) ≠ 46 by decide, show (47 : Nat) ≠ 45 by decide,
    ite_true, ite_false]
  rw [cnt_nat, cnt_nat]
  exact ((rows_perm (laneInsts rs) 0 (lane_inst_ok rs hR)).map (List.map Fp.ofNat)).count_eq m

theorem balancedAt_sgen (rs : List Run) (hR : ∀ R ∈ rs, RunOk R) (h9 : R.tf 9 = rngTraffic (laneCalls rs)) (h10 : R.tf 10 = shufTraffic (laneInsts rs)) :
    R.BalancedAt B_SGEN := by
  apply R.balanced_one B_SGEN (by simp) 9 10 (by decide) (by decide) covers_sgen_send covers_sgen_recv
  intro m
  rw [h9, h10]
  simp only [sel, shufTraffic, rngTraffic, ite_true, Bool.false_eq_true, ite_false]
  simp only [B_SGEN, B_SSIN, B_SSMEM, show (48 : Nat) ≠ 45 by decide, show (48 : Nat) ≠ 47 by decide,
    ite_true, ite_false]
  rw [cnt_nat, cnt_nat]
  exact (gen_perm (laneInsts rs) (lane_draws rs hR)).count_eq m

theorem balancedAt_schacha (rs : List Run) (hR : ∀ R ∈ rs, RunOk R) (h8 : R.tf 8 = chachaTraffic (laneReqs rs)) (h9 : R.tf 9 = rngTraffic (laneCalls rs)) :
    R.BalancedAt B_SCHACHA := by
  apply R.balanced_one B_SCHACHA (by simp) 8 9 (by decide) (by decide) covers_schacha_send covers_schacha_recv
  intro m
  rw [h8, h9]
  simp only [sel, chachaTraffic, rngTraffic, ite_true, Bool.false_eq_true, ite_false]
  rw [cnt_nat, cnt_nat, words_lane rs hR]
  exact (chacha_lane_perm rs).count_eq m

end RenderBundleV3

open NearSpec NearSpecV3 in
/-- **The ChaCha-lane buses of the honest bundle** (`SSIN`, `SSOUT`, `SSMEM`, `SGEN`, `SSHUF`,
`SCHACHA`).  On the accepted instance, for the `PriorCore` blocks `bs` of `A`'s trace (the premises of
`balancedAt_scmp` / `sched_renders_on`): the RNG render's word bound holds (`hW`, from RelD0a A9), the
ChaCha, RNG and shuffle renders of the runs' lane instances exist, and every bundle with these
three renders and the process table of the same runs balances the six buses. -/
theorem chacha_buses_balanced {cb wb : Bytes} (A : AcceptedV3 cb wb) {bs : List NativeBlock}
    (hc : PriorCore A.p NearSpecV3.B0 bs)
    (hctx : bs.map (fun b => (b.witness.ctx, b.witness.pre)) =
      (A.m.ctx A.k, A.m.pre) :: A.steps.map (fun e => (implicitCtx A.k e, e.pre))) :
    rngRows (laneCalls (bs.map NativeBlock.run)) ≤ NearSpecV3.W0 ∧
    ∃ (r8 : TableRenderV3 A.pub 8 (by decide)) (r9 : TableRenderV3 A.pub 9 (by decide))
      (r10 : TableRenderV3 A.pub 10 (by decide)),
      r8.tr = chachaTraceAligned (laneReqs (bs.map NativeBlock.run)) ∧
      r8.tf = chachaTraffic (laneReqs (bs.map NativeBlock.run)) ∧
      r9.tr = rngTraceW0 (laneCalls (bs.map NativeBlock.run)) 9 ∧
      r9.tf = rngTraffic (laneCalls (bs.map NativeBlock.run)) ∧
      r10.tr = shufTraceAligned (laneInsts (bs.map NativeBlock.run)) ∧
      r10.tf = shufTraffic (laneInsts (bs.map NativeBlock.run)) ∧
      ∀ R : RenderBundleV3 A.pub, R ⟨8, by decide⟩ = r8 → R ⟨9, by decide⟩ = r9 → R ⟨10, by decide⟩ = r10 →
        (R ⟨13, by decide⟩).tr = procTraceV3 (bs.map NativeBlock.run) →
        R.BalancedAt B_SSIN ∧ R.BalancedAt B_SSOUT ∧ R.BalancedAt B_SSMEM ∧ R.BalancedAt B_SGEN ∧
        R.BalancedAt B_SSHUF ∧ R.BalancedAt B_SCHACHA := by
  have hR := runOk_all A hc hctx
  have hW := kfin_W0 A hc hctx
  have hcap := (prior_run_capacities A.hp _ bs hc).2
  have hlen := hc.length
  have hrng : rngRows (laneCalls (bs.map NativeBlock.run)) ≤ NearSpecV3.W0 := by
    rw [rngRows_lane _ hR]; exact hW
  have hW0 : NearSpecV3.W0 = 770000 := rfl
  have hshuf : shufRows (laneInsts (bs.map NativeBlock.run)) ≤ 2 ^ 22 :=
    Nat.le_trans (shufRows_le _) (by omega)
  have hreq : 86 * (laneReqs (bs.map NativeBlock.run)).length ≤ 2 ^ 22 := by
    have h1 := reqs_sum (bs.map NativeBlock.run)
    rw [reqs_lane]
    simp only [List.length_map, show (fun x : Run => x.kfin) = Run.kfin from rfl] at h1
    omega
  refine ⟨hrng, chachaRenderV3 A.pub _ (lane_req_ok _ hR) hreq,
    rngRenderV3 A.pub _ (lane_call_ok _ hR) (by omega) (by have : Chacha.Rng.Table.W0 = 770000 := rfl; omega),
    shufRenderV3 A.pub _ (lane_inst_ok _ hR) hshuf, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  intro R h8 h9 h10 h13
  have t8 : R.tf 8 = chachaTraffic (laneReqs (bs.map NativeBlock.run)) := by rw [R.tf_at 8 (by decide), h8]; rfl
  have t9 : R.tf 9 = rngTraffic (laneCalls (bs.map NativeBlock.run)) := by rw [R.tf_at 9 (by decide), h9]; rfl
  have t10 : R.tf 10 = shufTraffic (laneInsts (bs.map NativeBlock.run)) := by
    rw [R.tf_at 10 (by decide), h10]; rfl
  have hc' : (ProcConcatGeometry.rows (bs.map NativeBlock.run)).length ≤ 2 ^ 22 := by omega
  exact ⟨R.balancedAt_ssin _ hR hc' h13 t10, R.balancedAt_ssout _ hR hc' h13 t10, R.balancedAt_ssmem _ hR t10,
    R.balancedAt_sgen _ hR t9 t10, R.balancedAt_sshuf _ hR hc' h13 t10, R.balancedAt_schacha _ hR t8 t9⟩
end ZkFormal.NearV3.Assembly
