import ZkFormal.NearV3.Render.ChachaRun
import ZkFormal.NearV3.Render.ChachaProcBus
import ZkFormal.NearV3.Sched.Gen.Lane
import ZkFormal.Chacha.Shuffle.Complete.Count
import ZkFormal.Chacha.Rng.Complete.Basic
import ZkFormal.NearV3.Render.PaddedChacha

/-!
# ZkFormal.NearV3.Render.ChachaLane — the lane instances of the native runs and their traffic

For a list of native scheduler runs `rs` (each `RunOk`: its key is `leWords seed`, `Stamped` rounds,
every round `RoundOk` with entry indices and list id `< p`, `kfin < 2^30`):

* `laneInsts rs` (one `shufV3` instance per round, `= Sched.Gen.Lane.shufInsts`), `laneCalls rs` (the
  `gen_index` calls of each instance in drawing order), `laneReqs rs` (`Sched.Gen.Lane.chachaReqs`:
  every drawn word `0 … kfin − 1` once), `laneWords rs` (the `SCHACHA` messages of those words);
* the process table's messages are the shuffle table's: **`shuf_run`** (`SSHUF`), **`in_run`**
  (`SSIN`), **`out_run`** (`SSOUT`);
* **`gen_perm`**: the `genV3` `SGEN` sends are a permutation of the `shufV3` receives;
* **`words_lane`**: the `genV3` `SCHACHA` receives are exactly `laneWords rs`;
  **`chacha_lane_perm`**: the `chachaV3` sends are a permutation of them;
* `inst_ok`, `call_ok`, `req_ok` (the generators' support conditions), the row counts
  `shufRows_le`, `rngRows_lane` (`= Σ kfin`), `reqs_lane`, `reqs_sum`, and `round_T`.
-/

namespace ZkFormal.NearV3.Render.ChachaBus
open ZkFormal.Algebra NearSpecV3 ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen ZkFormal.NearV3.Candidates
open ZkFormal.Chacha ZkFormal.Chacha.Shuffle.Gen ZkFormal.Chacha.Shuffle.Complete
open ZkFormal.NearV3.Sched.Complete (procVs roundVs keyVs)

/-! ## The lane instances of a list of runs -/

def roundInst (R : Run) (rd : Gen.RoundD) : SInst :=
  instOf (lidOf R.tau rd.T) R.key rd.kst (rd.entries.map (·.ein))
def runInsts (R : Run) : List SInst := R.rounds.map (roundInst R)
def laneInsts (rs : List Run) : List SInst := rs.flatMap runInsts

/-- The `gen_index` calls of an instance, in drawing order (`e = 0 … L−2`, `n = L − e`). -/
def instCalls (I : SInst) : List Rng.Gen.Call :=
  (List.range (I.L - 1)).map fun e => ⟨I.key, I.kAt e, I.L - e⟩
def laneCalls (rs : List Run) : List Rng.Gen.Call := (laneInsts rs).flatMap instCalls

/-- The ChaCha block requests: per run, every drawn word `0 … kfin − 1` once. -/
def laneReqs (rs : List Run) : List Chacha.Gen.Req := rs.flatMap Gen.Lane.chachaReqs

/-- The `SCHACHA` message of stream word `k`. -/
def wmsg (key : List Nat) (k : Nat) : List Fp := Sound.chachaMsg key (k / 16) (k % 16) (streamWord key k)
def laneWords (rs : List Run) : List (List Fp) := rs.flatMap fun R => (List.range R.kfin).map (wmsg R.key)

/-! ## Per-round and per-run facts of the native runs -/

structure RdOk (R : Run) (rd : Gen.RoundD) : Prop where
  ok : RoundOk R.key R.conv.length rd
  idx : ∀ i, i < rd.entries.length → (rd.entries.toArray[i]!).x = i
  lid : lidOf R.tau rd.T < 2013265921

structure RunOk (R : Run) : Prop where
  key : R.key = leWords R.seed
  key8 : (leWords R.seed).length = 8
  conv : R.conv.length ≤ 4096
  kfin : R.kfin < 2 ^ 30
  chain : ∃ T Kq zq, ProcActualReplayChain.Stamped T R.kfin Kq zq R.rounds
  rds : ∀ rd ∈ R.rounds, RdOk R rd

theorem rd_draws {R : Run} {rd : Gen.RoundD} (h : RdOk R rd) :
    Draws (roundInst R rd) ∧ rd.entries.map (·.eout) = (roundInst R rd).final ∧
      rd.kend = (roundInst R rd).kBefore 0 :=
  replay_inst _ _ _ _ _ _ h.ok.replay

theorem rd_L {R : Run} (rd : Gen.RoundD) : (roundInst R rd).L = rd.entries.length := by
  simp [roundInst, instOf, SInst.L]

/-! ## `SSHUF`, `SSIN`, `SSOUT` -/

theorem shuf_round {R : Run} (hR : RunOk R) {rd : Gen.RoundD} (h : RdOk R rd) :
    shufMsg (roundInst R rd) = hdrShuf R rd := by
  unfold shufMsg hdrShuf
  rw [← (rd_draws h).2.2]
  have hl : (roundInst R rd).L = rd.Lr := by rw [rd_L, h.ok.len]
  rw [hl]
  simp only [roundInst, instOf]
  rw [lid_fp, hR.key, keyN_leWords _ hR.key8]

theorem shuf_run {R : Run} (hR : RunOk R) : expectedShuf (runInsts R) = runShuf R := by
  unfold expectedShuf runInsts runShuf
  rw [List.map_map]
  exact List.map_congr_left (fun rd hrd => shuf_round hR (hR.rds rd hrd))

theorem in_round {R : Run} {rd : Gen.RoundD} (h : RdOk R rd) :
    (List.range (roundInst R rd).L).map (inMsg (roundInst R rd)) =
      (List.range rd.entries.toArray.size).map fun i => entIn R rd rd.entries.toArray[i]! := by
  rw [rd_L, List.size_toArray]
  apply List.map_congr_left
  intro q hq
  have hq := List.mem_range.mp hq
  unfold inMsg entIn
  rw [h.idx q hq, getElem!_pos rd.entries.toArray q (by simpa using hq)]
  simp only [roundInst, instOf, lid_fp, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eq_getElem hq, Option.map_some, Option.getD_some, List.getElem_toArray]

theorem out_round {R : Run} {rd : Gen.RoundD} (h : RdOk R rd) :
    (List.range (roundInst R rd).L).map (outMsg (roundInst R rd)) =
      (List.range rd.entries.toArray.size).map fun i => entOut R rd rd.entries.toArray[i]! := by
  rw [rd_L, List.size_toArray]
  apply List.map_congr_left
  intro q hq
  have hq := List.mem_range.mp hq
  unfold outMsg entOut
  rw [h.idx q hq, getElem!_pos rd.entries.toArray q (by simpa using hq), ← (rd_draws h).2.1]
  simp only [roundInst, instOf, lid_fp, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eq_getElem hq, Option.map_some, Option.getD_some, List.getElem_toArray]

theorem in_run {R : Run} (hR : RunOk R) : expectedIn (runInsts R) = runIn R := by
  unfold expectedIn runInsts runIn
  rw [List.flatMap_map]
  exact ZkFormal.Near.flatMap_congr' (fun rd hrd => in_round (hR.rds rd hrd))

theorem out_run {R : Run} (hR : RunOk R) : expectedOut (runInsts R) = runOut R := by
  unfold expectedOut runInsts runOut
  rw [List.flatMap_map]
  exact ZkFormal.Near.flatMap_congr' (fun rd hrd => out_round (hR.rds rd hrd))


/-! ## `SGEN`: the calls of an instance are its draws -/

theorem perm_flatMap_congr {α β : Type} {f g : α → List β} :
    ∀ {l : List α}, (∀ x ∈ l, (f x).Perm (g x)) → (l.flatMap f).Perm (l.flatMap g)
  | [], _ => List.Perm.refl _
  | x :: xs, h => by
    simp only [List.flatMap_cons]
    exact (h x (List.mem_cons_self ..)).append (perm_flatMap_congr (fun y hy => h y (List.mem_cons_of_mem _ hy)))

theorem call_result {I : SInst} (hd : Draws I) {e : Nat} (he : e + 1 < I.L) :
    Rng.Gen.result ⟨I.key, I.kAt e, I.L - e⟩ = (I.js (I.L - 1 - e), I.kAt (e + 1)) := by
  obtain ⟨-, j, hj⟩ := kAt_succ_ge hd he
  rw [Rng.Complete.result_eq (C := ⟨I.key, I.kAt e, I.L - e⟩) hj]
  have hjs : I.js (I.L - 1 - e) = j := by
    have e1 : I.kBefore (I.L - 1 - e) = I.kAt e := by
      unfold SInst.kBefore; rw [show I.L - 1 - (I.L - 1 - e) = e by omega]
    unfold SInst.js
    rw [e1, show I.L - 1 - e + 1 = I.L - e by omega, hj]
    rfl
  rw [hjs]

theorem gen_inst {I : SInst} (hd : Draws I) :
    (instCalls I).map Rng.Gen.genOut =
      (List.range (I.L - 1)).map (fun e => (fun i => genStep I (i + 1)) (I.L - 1 - 1 - e)) := by
  unfold instCalls
  rw [List.map_map]
  apply List.map_congr_left
  intro e he
  have he := List.mem_range.mp he
  simp only [Function.comp, Rng.Gen.genOut, genStep]
  rw [call_result hd (by omega)]
  unfold SInst.kBefore
  rw [show I.L - 1 - 1 - e + 1 = I.L - 1 - e by omega, show I.L - 1 - (I.L - 1 - e) = e by omega,
    show I.L - 1 - e + 1 = I.L - e by omega, show I.L - 1 - (I.L - 1 - e - 1) = e + 1 by omega]

theorem gen_perm (insts : List SInst) (hd : ∀ I ∈ insts, Draws I) :
    ((insts.flatMap instCalls).map Rng.Gen.genOut).Perm (expectedGen insts) := by
  unfold expectedGen
  rw [List.map_flatMap]
  apply perm_flatMap_congr
  intro I hI
  rw [gen_inst (hd I hI)]
  exact rev_perm (I.L - 1) (fun i => genStep I (i + 1))

/-! ## `SCHACHA`: the drawn words -/

theorem nd_call {I : SInst} (hd : Draws I) {e : Nat} (he : e + 1 < I.L) :
    Rng.Gen.nd ⟨I.key, I.kAt e, I.L - e⟩ = I.kAt (e + 1) - I.kAt e := by
  unfold Rng.Gen.nd; rw [call_result hd he]

theorem words_call {I : SInst} (hd : Draws I) {e : Nat} (he : e + 1 < I.L) :
    (List.range (Rng.Gen.nd ⟨I.key, I.kAt e, I.L - e⟩)).map (Rng.Gen.wordMsg ⟨I.key, I.kAt e, I.L - e⟩) =
      (List.range' (I.kAt e) (I.kAt (e + 1) - I.kAt e)).map (wmsg I.key) := by
  rw [nd_call hd he, List.range'_eq_map_range, List.map_map]
  rfl

theorem range'_chain {a b c : Nat} (h1 : a ≤ b) (h2 : b ≤ c) :
    List.range' a (b - a) ++ List.range' b (c - b) = List.range' a (c - a) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h1
  rw [Nat.add_sub_cancel_left, List.range'_append_1]
  congr 1; omega

theorem words_tele {I : SInst} (hd : Draws I) : ∀ m, m + 1 ≤ I.L →
    ((List.range m).flatMap fun e => List.range' (I.kAt e) (I.kAt (e + 1) - I.kAt e)) =
      List.range' (I.kAt 0) (I.kAt m - I.kAt 0)
  | 0, _ => by simp
  | m + 1, h => by
    rw [List.range_succ, List.flatMap_append, words_tele hd m (by omega), List.flatMap_singleton]
    have h1 := (kAt_succ_ge hd (m := m) (by omega)).1
    have h2 := kAt_le_top hd 0 m (by omega)
    rw [Nat.zero_add] at h2
    exact range'_chain h2 (by omega)

theorem words_inst {I : SInst} (hd : Draws I) (hL : 1 ≤ I.L) :
    (instCalls I).flatMap (fun C => (List.range (Rng.Gen.nd C)).map (Rng.Gen.wordMsg C)) =
      (List.range' I.kstart (I.kBefore 0 - I.kstart)).map (wmsg I.key) := by
  unfold instCalls
  rw [List.flatMap_map]
  rw [show ((List.range (I.L - 1)).flatMap fun e =>
      (List.range (Rng.Gen.nd ⟨I.key, I.kAt e, I.L - e⟩)).map (Rng.Gen.wordMsg ⟨I.key, I.kAt e, I.L - e⟩)) =
      ((List.range (I.L - 1)).flatMap fun e => List.range' (I.kAt e) (I.kAt (e + 1) - I.kAt e)).map (wmsg I.key) from by
    rw [List.map_flatMap]
    exact ZkFormal.Near.flatMap_congr' (fun e he => words_call hd (by have := List.mem_range.mp he; omega))]
  rw [words_tele hd (I.L - 1) (by omega)]
  rfl


/-! ## Per run: the cursor chain -/

theorem stamped_facts {T kp Kq zq : Nat} {rs : List Gen.RoundD}
    (h : ProcActualReplayChain.Stamped T kp Kq zq rs) (hk : ∀ rd ∈ rs, rd.kst ≤ rd.kend) :
    rs.flatMap (fun rd => List.range' rd.kst (rd.kend - rd.kst)) = List.range' 0 kp ∧
      (∀ rd ∈ rs, rd.kend ≤ kp) ∧ T = T0 + (rs.map (·.Lr)).sum ∧ ∀ rd ∈ rs, rd.T + rd.Lr ≤ T := by
  induction h with
  | nil => simp
  | @snoc T kp Kq zq rs h K z L kend es ih =>
    obtain ⟨i1, i2, i3, i4⟩ := ih (fun rd hrd => hk rd (List.mem_append_left _ hrd))
    have hl := hk ⟨K, z, T, L, kp, kend, Kq, zq, es⟩ (List.mem_append_right _ (List.mem_singleton_self _))
    simp only at hl
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [List.flatMap_append, i1, List.flatMap_singleton]
      exact range'_chain (Nat.zero_le _) hl
    · intro rd hrd
      rcases List.mem_append.mp hrd with hrd | hrd
      · have := i2 rd hrd; omega
      · rw [List.mem_singleton.mp hrd]; exact Nat.le_refl _
    · rw [List.map_append, List.sum_append, i3]; simp; omega
    · intro rd hrd
      rcases List.mem_append.mp hrd with hrd | hrd
      · have := i4 rd hrd; omega
      · rw [List.mem_singleton.mp hrd]; exact Nat.le_refl _

theorem kst_le {R : Run} {rd : Gen.RoundD} (h : RdOk R rd) : rd.kst ≤ rd.kend := by
  have hd := rd_draws h
  have hL : 0 < (roundInst R rd).L := by rw [rd_L, h.ok.len]; exact h.ok.L_pos
  rw [hd.2.2]
  exact (kBefore_le hd.1 hL).1

theorem words_run {R : Run} (hR : RunOk R) :
    (runInsts R).flatMap (fun I => (instCalls I).flatMap fun C => (List.range (Rng.Gen.nd C)).map (Rng.Gen.wordMsg C)) =
      (List.range R.kfin).map (wmsg R.key) := by
  obtain ⟨T, Kq, zq, hs⟩ := hR.chain
  have hf := (stamped_facts hs (fun rd hrd => kst_le (hR.rds rd hrd))).1
  unfold runInsts
  rw [List.flatMap_map]
  have e : ∀ rd ∈ R.rounds, ((instCalls (roundInst R rd)).flatMap fun C =>
      (List.range (Rng.Gen.nd C)).map (Rng.Gen.wordMsg C)) =
      (List.range' rd.kst (rd.kend - rd.kst)).map (wmsg R.key) := by
    intro rd hrd
    have h := hR.rds rd hrd
    have hd := rd_draws h
    rw [words_inst hd.1 (by rw [rd_L, h.ok.len]; exact h.ok.L_pos), ← hd.2.2]
    rfl
  rw [ZkFormal.Near.flatMap_congr' e, ← List.map_flatMap, hf, List.range_eq_range']

theorem words_lane (rs : List Run) (hR : ∀ R ∈ rs, RunOk R) :
    Rng.Gen.expectedWords (laneCalls rs) = laneWords rs := by
  unfold Rng.Gen.expectedWords laneCalls laneInsts laneWords
  simp only [List.flatMap_assoc]
  exact ZkFormal.Near.flatMap_congr' (fun R hR' => words_run (hR R hR'))

/-! ## `SCHACHA`: the ChaCha requests provide the drawn words -/

theorem used_getD (ctr K j kk : Nat) (hj : j < 4) (hk : kk < 4) :
    ((List.range 16).map fun w => decide (16 * ctr + w < K)).getD (4 * kk + j) false =
      decide (16 * ctr + (4 * kk + j) < K) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by omega)]
  rfl

theorem fmsgs_eq (key : List Nat) (ctr K j : Nat) (hj : j < 4) :
    Chacha.Gen.fMsgs ⟨key, ctr, (List.range 16).map fun w => decide (16 * ctr + w < K)⟩ j =
      (((List.range 4).map (fun kk => 4 * kk + j)).filter (fun w => decide (16 * ctr + w < K))).map
        (fun w => Sound.chachaMsg key ctr w ((chachaBlock key ctr)[w]!)) := by
  unfold Chacha.Gen.fMsgs
  rw [List.filter_map, List.map_map]
  congr 1
  apply List.filter_congr
  intro kk hk
  exact used_getD ctr K j kk hj (List.mem_range.mp hk)

theorem idx_perm : ((List.range 4).flatMap (fun j => (List.range 4).map (fun kk => 4 * kk + j))).Perm
    (List.range 16) := by decide

theorem block_msg (key : List Nat) (ctr w : Nat) :
    Sound.chachaMsg key ctr w ((chachaBlock key ctr)[w]!) = wmsg key (16 * ctr + w) ∨ 16 ≤ w := by
  by_cases hw : w < 16
  · left
    unfold wmsg streamWord
    rw [show (16 * ctr + w) / 16 = ctr by omega, show (16 * ctr + w) % 16 = w by omega,
      List.getElem!_eq_getElem?_getD, List.getD_eq_getElem?_getD]
    rfl
  · right; omega

theorem req_perm (key : List Nat) (ctr K : Nat) :
    ((List.range 4).flatMap (Chacha.Gen.fMsgs ⟨key, ctr, (List.range 16).map fun w => decide (16 * ctr + w < K)⟩)).Perm
      (((List.range 16).filter (fun w => decide (16 * ctr + w < K))).map (fun w => wmsg key (16 * ctr + w))) := by
  rw [ZkFormal.Near.flatMap_congr' (fun j hj => fmsgs_eq key ctr K j (List.mem_range.mp hj)),
    ← List.map_flatMap, ← List.filter_flatMap]
  refine ((idx_perm.filter _).map _).trans (List.Perm.of_eq ?_)
  apply List.map_congr_left
  intro w hw
  have := (List.mem_range.mp (List.mem_filter.mp hw).1)
  rcases block_msg key ctr w with h | h
  · exact h
  · omega

theorem filter_range_lt (K : Nat) : ∀ M, (List.range M).filter (fun w => decide (w < K)) = List.range (min M K)
  | 0 => by simp
  | M + 1 => by
    rw [List.range_succ, List.filter_append, filter_range_lt K M]
    by_cases h : M < K
    · rw [show min (M + 1) K = min M K + 1 by omega, List.range_succ, show min M K = M by omega]
      simp [h]
    · rw [show min (M + 1) K = min M K by omega]
      simp [h]

theorem blocks_eq (key : List Nat) (K : Nat) : ∀ n,
    ((List.range n).flatMap fun ctr =>
      ((List.range 16).filter (fun w => decide (16 * ctr + w < K))).map (fun w => wmsg key (16 * ctr + w))) =
      ((List.range (16 * n)).filter (fun w => decide (w < K))).map (wmsg key)
  | 0 => by simp
  | n + 1 => by
    rw [show List.range (n + 1) = List.range n ++ [n] from List.range_succ, List.flatMap_append,
      blocks_eq key K n, List.flatMap_singleton,
      show 16 * (n + 1) = 16 * n + 16 by omega, List.range_add, List.filter_append, List.map_append,
      List.filter_map, List.map_map]
    rfl

theorem chacha_run_perm (R : Run) :
    (Chacha.Gen.expected (Gen.Lane.chachaReqs R)).Perm ((List.range R.kfin).map (wmsg R.key)) := by
  unfold Chacha.Gen.expected Gen.Lane.chachaReqs
  rw [List.flatMap_map]
  refine (perm_flatMap_congr (fun ctr _ => req_perm R.key ctr R.kfin)).trans (List.Perm.of_eq ?_)
  rw [blocks_eq, filter_range_lt, show min (16 * ((R.kfin + 15) / 16)) R.kfin = R.kfin by omega]

theorem chacha_lane_perm (rs : List Run) : (Chacha.Gen.expected (laneReqs rs)).Perm (laneWords rs) := by
  unfold laneReqs laneWords
  have e : ∀ l : List Chacha.Gen.Req, Chacha.Gen.expected l = l.flatMap fun R => (List.range 4).flatMap (Chacha.Gen.fMsgs R) :=
    fun _ => rfl
  rw [e, List.flatMap_assoc]
  exact perm_flatMap_congr (fun R _ => by rw [← e]; exact chacha_run_perm R)


/-! ## Supported instances, calls and requests -/

theorem kend_le {R : Run} (hR : RunOk R) {rd : Gen.RoundD} (hrd : rd ∈ R.rounds) : rd.kend ≤ R.kfin := by
  obtain ⟨T, Kq, zq, hs⟩ := hR.chain
  exact (stamped_facts hs (fun rd hrd => kst_le (hR.rds rd hrd))).2.1 rd hrd

theorem inst_ok {R : Run} (hR : RunOk R) {rd : Gen.RoundD} (hrd : rd ∈ R.rounds) : InstOk (roundInst R rd) := by
  have h := hR.rds rd hrd
  have hd := rd_draws h
  have hk := kend_le hR hrd
  have hfin := hR.kfin
  have hL : (roundInst R rd).L = rd.Lr := by rw [rd_L, h.ok.len]
  have h0 := h.ok.L_pos
  have h1 := h.ok.L_lt
  refine ⟨by omega, by omega, ?_, ?_, h.lid, ?_, ?_, ?_⟩
  · show R.key.length = 8; rw [hR.key]; exact hR.key8
  · show ∀ x ∈ R.key, x < 2 ^ 32; rw [hR.key]; exact leWords_lt _
  · intro v hv
    have hv' := (final_perm (roundInst R rd)).symm.subset hv
    rw [← hd.2.1] at hv'
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hv'
    have := h.ok.cid e he
    have := hR.conv
    omega
  · have := kst_le h
    show rd.kst < 2 ^ 30
    omega
  · intro q h1q h2q
    obtain ⟨j, k', hg⟩ := hd.1 q h1q h2q
    refine ⟨j, k', hg, ?_⟩
    have hk' : (roundInst R rd).kBefore (q - 1) = k' := by
      rw [kBefore_pred h1q h2q, hg]; rfl
    have := (kBefore_le hd.1 (q := q - 1) (by omega)).2
    rw [hk', ← hd.2.2] at this
    omega

theorem call_ok {R : Run} (hR : RunOk R) {rd : Gen.RoundD} (hrd : rd ∈ R.rounds) :
    ∀ C ∈ instCalls (roundInst R rd), Rng.Gen.CallOk C := by
  intro C hC
  have hI := inst_ok hR hrd
  have hd := (rd_draws (hR.rds rd hrd)).1
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hC
  have he := List.mem_range.mp he
  obtain ⟨-, j, hj⟩ := kAt_succ_ge hd (m := e) (by omega)
  have hlt := kAt_lt hI (e + 1) (by omega)
  have hL : (roundInst R rd).L < 16384 := by
    rw [rd_L, (hR.rds rd hrd).ok.len]; exact (hR.rds rd hrd).ok.L_lt
  exact ⟨hI.key_len, hI.key_lt, by simp only; omega, by simp only; omega, j, _, hj, hlt⟩

theorem req_ok {R : Run} (hR : RunOk R) : ∀ Q ∈ Gen.Lane.chachaReqs R, Chacha.Gen.ReqOk Q := by
  intro Q hQ
  obtain ⟨ctr, hc, rfl⟩ := List.mem_map.mp hQ
  have hc := List.mem_range.mp hc
  have := hR.kfin
  refine ⟨?_, ?_, by simp only; omega, by simp⟩
  · show R.key.length = 8; rw [hR.key]; exact hR.key8
  · show ∀ x ∈ R.key, x < 2 ^ 32; rw [hR.key]; exact leWords_lt _

theorem lane_inst_ok (rs : List Run) (hR : ∀ R ∈ rs, RunOk R) : ∀ I ∈ laneInsts rs, InstOk I := by
  intro I hI
  obtain ⟨R, hRm, hI⟩ := List.mem_flatMap.mp hI
  obtain ⟨rd, hrd, rfl⟩ := List.mem_map.mp hI
  exact inst_ok (hR R hRm) hrd

theorem lane_draws (rs : List Run) (hR : ∀ R ∈ rs, RunOk R) : ∀ I ∈ laneInsts rs, Draws I := by
  intro I hI
  obtain ⟨R, hRm, hI⟩ := List.mem_flatMap.mp hI
  obtain ⟨rd, hrd, rfl⟩ := List.mem_map.mp hI
  exact (rd_draws ((hR R hRm).rds rd hrd)).1

theorem lane_call_ok (rs : List Run) (hR : ∀ R ∈ rs, RunOk R) : ∀ C ∈ laneCalls rs, Rng.Gen.CallOk C := by
  intro C hC
  obtain ⟨I, hI, hC⟩ := List.mem_flatMap.mp hC
  obtain ⟨R, hRm, hI⟩ := List.mem_flatMap.mp hI
  obtain ⟨rd, hrd, rfl⟩ := List.mem_map.mp hI
  exact call_ok (hR R hRm) hrd C hC

theorem lane_req_ok (rs : List Run) (hR : ∀ R ∈ rs, RunOk R) : ∀ Q ∈ laneReqs rs, Chacha.Gen.ReqOk Q := by
  intro Q hQ
  obtain ⟨R, hRm, hQ⟩ := List.mem_flatMap.mp hQ
  exact req_ok (hR R hRm) Q hQ

/-! ## Row counts -/

theorem honestRowsFrom_length : ∀ (insts : List SInst) (s : Nat),
    (honestRowsFrom insts s).length = (insts.map SInst.L).sum
  | [], _ => rfl
  | I :: Is, s => by
    simp [honestRowsFrom, instRows, honestRowsFrom_length Is]

theorem shufRows_lane (rs : List Run) :
    shufRows (laneInsts rs) = (rs.map fun R => (R.rounds.map fun rd => rd.entries.length).sum).sum := by
  unfold shufRows honestRows
  rw [honestRowsFrom_length]
  induction rs with
  | nil => rfl
  | cons R rs ih =>
    simp only [laneInsts, List.flatMap_cons, List.map_append, List.sum_append, List.map_cons,
      List.sum_cons] at ih ⊢
    rw [ih]
    congr 1
    unfold runInsts
    rw [List.map_map]
    congr 1
    apply List.map_congr_left
    intro rd _
    exact rd_L rd

theorem rngRows_eq (calls : List Rng.Gen.Call) : rngRows calls = (Rng.Gen.expectedWords calls).length := by
  unfold rngRows Rng.Gen.honestRows Rng.Gen.expectedWords
  simp [List.length_flatMap, Rng.Gen.callRows]

theorem rngRows_lane (rs : List Run) (hR : ∀ R ∈ rs, RunOk R) :
    rngRows (laneCalls rs) = (rs.map (·.kfin)).sum := by
  rw [rngRows_eq, words_lane rs hR]
  unfold laneWords
  simp [List.length_flatMap]

theorem reqs_lane (rs : List Run) : (laneReqs rs).length = (rs.map fun R => (R.kfin + 15) / 16).sum := by
  unfold laneReqs Gen.Lane.chachaReqs
  simp [List.length_flatMap]

theorem reqs_sum : ∀ (rs : List Run),
    16 * (rs.map fun R => (R.kfin + 15) / 16).sum ≤ (rs.map (·.kfin)).sum + 15 * rs.length
  | [] => by simp
  | R :: rs => by
    have := reqs_sum rs
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    omega


theorem entries_le_procVs (R : Run) : (R.rounds.map fun rd => rd.entries.length).sum + 16 ≤ (procVs R).length := by
  have e : ∀ l : List Gen.RoundD, (l.map fun rd => rd.entries.length).sum ≤ (l.flatMap (roundVs R)).length := by
    intro l
    induction l with
    | nil => simp
    | cons rd l ih =>
      simp only [List.map_cons, List.sum_cons, List.flatMap_cons, List.length_append, roundVs,
        List.length_cons, List.length_map, List.length_range, List.size_toArray]
      omega
  have := e R.rounds
  simp only [procVs, List.length_append, keyVs, List.length_map, List.length_range]
  omega

theorem shufRows_le (rs : List Run) : shufRows (laneInsts rs) ≤ (ProcConcatGeometry.rows rs).length := by
  rw [shufRows_lane]
  unfold ProcConcatGeometry.rows
  induction rs with
  | nil => simp
  | cons R rs ih =>
    simp only [List.map_cons, List.sum_cons, List.flatMap_cons, List.length_append]
    have := entries_le_procVs R
    omega

/-- The round starts of a run stay below `T0 + |procVs R|`. -/
theorem round_T {R : Run} {T Kq zq : Nat} (hs : ProcActualReplayChain.Stamped T R.kfin Kq zq R.rounds)
    (hk : ∀ rd ∈ R.rounds, rd.kst ≤ rd.kend) (hlen : ∀ rd ∈ R.rounds, rd.entries.length = rd.Lr) :
    ∀ rd ∈ R.rounds, rd.T < T0 + (procVs R).length := by
  obtain ⟨-, -, hT, hle⟩ := stamped_facts hs hk
  intro rd hrd
  have h1 := hle rd hrd
  have h2 : (R.rounds.map (·.Lr)).sum = (R.rounds.map fun rd => rd.entries.length).sum := by
    congr 1; exact List.map_congr_left (fun rd hrd => (hlen rd hrd).symm)
  have h3 := entries_le_procVs R
  have h4 : 16 ≤ (procVs R).length := ProcConcatGeometry.row_length R
  omega

end ZkFormal.NearV3.Render.ChachaBus
