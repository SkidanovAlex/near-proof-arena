import ZkFormal.NearV3.Assembly.TrieUpsRoot
import ZkFormal.NearV3.Assembly.UpsertShaJobs
import ZkFormal.NearV3.Render.Ups.SchedulerShaInstances

/-!
# ZkFormal.NearV3.Assembly.TrieUpsSched — the ups side of `S0F`, `SPLEN`, `SPOST`

`upsV3` talks to the scheduler codec table on three buses:
* `S0F` (send, `sf` = row `W0`): `[τ, pres, vid]`, `pres = 1` iff the `W3` step is a value step,
  `vid` its value id (`e₃`), else `0`;
* `SPLEN` (receive, `W0`): `[τ, L]` (the new state's length);
* `SPOST` (receive, every value row `p < L`): `[τ, p, v_p]` (the new state's bytes).

`aligned_view_bus` (generic: the aligned view's traffic on a bus is the per-instance generated
traffic, for any bus whose messages read columns `< 200`) and **`view_s0f_send`**,
**`view_splen_recv`**, **`view_spost_recv`**: the exact ups traffic of the aligned view
(`upsTraffic (viewOf (upsTraceAligned Is) t (segsOf Is))`, the base traffic of the ups component),
plus the silent sides (`view_s0f_recv`, `view_splen_send`, `view_spost_send`).
-/

namespace ZkFormal.NearV3.Assembly.TrieUpsSched

open ZkFormal.Near ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3 ZkFormal.NearV3.Assembly
  Render Render.UpsGen Render.UpsRelay UpsRows Rcpt.Candidates Rcpt.Candidates.NodePostUpdate ZkFormal.Size
  TrieUpsRoot

set_option maxHeartbeats 800000

/-! ## Interaction-level equations -/

theorem uMsgs_s0f (C D : URow) :
    uMsgs C D B_S0F true =
      if Fp.ofNat (C UpsV3.sf) = 1 then [reduceMessage [C UpsV3.tau, C UpsV3.pres, C UpsV3.vid]] else [] := by
  simp [uMsgs, UpsV3.interactions, Dsl.send, Dsl.recv,
    B_EDGE, B_BMAP, B_MIDROOT, B_ROOT, B_DIGEST, B_S0F, B_SPLEN, B_SPOST, B_BYTES, B_UPB, B_MEMD,
    uMult, uev, Expr.evalWith, uEnv, Dsl.c, reduceMessage]
  split <;> simp_all

theorem uMsgs_s0f_recv (C D : URow) : uMsgs C D B_S0F false = [] := by
  simp [uMsgs, UpsV3.interactions, Dsl.send, Dsl.recv,
    B_EDGE, B_BMAP, B_MIDROOT, B_ROOT, B_DIGEST, B_S0F, B_SPLEN, B_SPOST, B_BYTES, B_UPB, B_MEMD]

theorem uMsgs_splen (C D : URow) :
    uMsgs C D B_SPLEN false =
      if Fp.ofNat (C UpsV3.sf) = 1 then
        [[C UpsV3.tau % Algebra.P, (uev C D UpsV3.Lexpr).toNat]] else [] := by
  simp [uMsgs, UpsV3.interactions, Dsl.send, Dsl.recv,
    B_EDGE, B_BMAP, B_MIDROOT, B_ROOT, B_DIGEST, B_S0F, B_SPLEN, B_SPOST, B_BYTES, B_UPB, B_MEMD,
    uMult]
  split <;> simp_all [uev, Expr.evalWith, uEnv, Dsl.c]

theorem uMsgs_splen_send (C D : URow) : uMsgs C D B_SPLEN true = [] := by
  simp [uMsgs, UpsV3.interactions, Dsl.send, Dsl.recv,
    B_EDGE, B_BMAP, B_MIDROOT, B_ROOT, B_DIGEST, B_S0F, B_SPLEN, B_SPOST, B_BYTES, B_UPB, B_MEMD]

theorem uMsgs_spost (C D : URow) :
    uMsgs C D B_SPOST false =
      if Fp.ofNat (C UpsV3.vb) = 1 then [reduceMessage [C UpsV3.tau, C UpsV3.qpos, C UpsV3.b]] else [] := by
  simp [uMsgs, UpsV3.interactions, Dsl.send, Dsl.recv,
    B_EDGE, B_BMAP, B_MIDROOT, B_ROOT, B_DIGEST, B_S0F, B_SPLEN, B_SPOST, B_BYTES, B_UPB, B_MEMD,
    uMult, uev, Expr.evalWith, uEnv, Dsl.c, reduceMessage]
  split <;> simp_all

theorem uMsgs_spost_send (C D : URow) : uMsgs C D B_SPOST true = [] := by
  simp [uMsgs, UpsV3.interactions, Dsl.send, Dsl.recv,
    B_EDGE, B_BMAP, B_MIDROOT, B_ROOT, B_DIGEST, B_S0F, B_SPLEN, B_SPOST, B_BYTES, B_UPB, B_MEMD]


/-! ## Row-level messages of the generated rows -/

def presN (I : UpsInst) : Nat := if (step I 3).mode = 0 then 1 else 0
def vidN (I : UpsInst) : Nat := if (step I 3).mode = 0 then (step I 3).e.getD 3 0 else 0

theorem cast_toNat (n : Nat) : (((n : Int) : Fp)).toNat = n % Algebra.P := by
  exact Fp.toNat_ofNat _

theorem s0f_row (Is : List UpsInst) (q i : Nat) (rk : RK) (D : URow) :
    uMsgs (generatedRow Is q (i, rk)) D B_S0F true =
      if rk = .w 0 then [reduceMessage [(inst Is i).tau, presN (inst Is i), vidN (inst Is i)]] else [] := by
  rw [uMsgs_s0f]
  cases rk with
  | w t =>
    by_cases ht : t = 0
    · subst ht
      have hsf : generatedRow Is q (i, .w 0) UpsV3.sf = 1 := rfl
      rw [hsf, show Fp.ofNat 1 = 1 from rfl]
      simp only [ite_true]
      have h1 : generatedRow Is q (i, .w 0) UpsV3.tau = (inst Is i).tau % Algebra.P := by
        simp [generatedRow, rowCell, UpsV3.tau, isSeg, segCell]; exact Fp.toNat_ofNat _
      have h2 : generatedRow Is q (i, .w 0) UpsV3.pres = presN (inst Is i) % Algebra.P := by
        simp only [generatedRow, rowCell, UpsV3.pres, isSeg, segCell, presV, presN]
        by_cases hm : (step (inst Is i) 3).mode = 0 <;> simp [hm, ind] <;> rfl
      have h3 : generatedRow Is q (i, .w 0) UpsV3.vid = vidN (inst Is i) % Algebra.P := by
        simp only [generatedRow, rowCell, UpsV3.vid, isSeg, segCell, vidV, vidN]
        by_cases hm : (step (inst Is i) 3).mode = 0 <;> simp [hm, ind] <;> exact Fp.toNat_ofNat _
      rw [h1, h2, h3]
      simp [reduceMessage, Nat.mod_mod]
    · have hsf : generatedRow Is q (i, .w t) UpsV3.sf = 0 := by
        simp [generatedRow, rowCell, isSeg, UpsV3.sf, wCell, ind, ht]; rfl
      rw [hsf]; simp [ht]; decide
  | v p =>
    have hsf : generatedRow Is q (i, .v p) UpsV3.sf = 0 := rfl
    rw [hsf]; simp; decide
  | q k p =>
    have hsf : generatedRow Is q (i, .q k p) UpsV3.sf = 0 := rfl
    rw [hsf]; simp; decide

theorem ofNat_mod_P (n : Nat) : Fp.ofNat (n % Algebra.P) = Fp.ofNat n := by
  simp only [Fp.ofNat, Nat.mod_mod]

theorem lexpr_val (L : Nat) (hL : L < 2 ^ 24) :
    (Fp.ofNat (((((L : Int) % 256 : Int)) : Fp)).toNat +
      ((256 : Nat) * Fp.ofNat (((((L : Int) / 256 % 256 : Int)) : Fp)).toNat +
        (65536 : Nat) * Fp.ofNat (((((L : Int) / 65536 : Int)) : Fp)).toNat)).toNat = L % Algebra.P := by
  have e1 : ((L : Int) % 256) = ((L % 256 : Nat) : Int) := by omega
  have e2 : ((L : Int) / 256 % 256) = ((L / 256 % 256 : Nat) : Int) := by omega
  have e3 : ((L : Int) / 65536) = ((L / 65536 : Nat) : Int) := by omega
  rw [e1, e2, e3, cast_toNat, cast_toNat, cast_toNat, ofNat_mod_P, ofNat_mod_P, ofNat_mod_P]
  show (Fp.add (Fp.ofNat (L % 256)) (Fp.add (Fp.mul (Fp.ofNat 256) (Fp.ofNat (L / 256 % 256)))
    (Fp.mul (Fp.ofNat 65536) (Fp.ofNat (L / 65536))))).toNat = _
  simp only [Fp.toNat_add, Fp.toNat_mul, Fp.toNat_ofNat]
  have hP : Algebra.P = 2013265921 := rfl
  have p1 : L % 256 % Algebra.P = L % 256 := Nat.mod_eq_of_lt (by omega)
  have p2 : L / 256 % 256 % Algebra.P = L / 256 % 256 := Nat.mod_eq_of_lt (by omega)
  have p3 : L / 65536 % Algebra.P = L / 65536 := Nat.mod_eq_of_lt (by omega)
  have p4 : 256 % Algebra.P = 256 := Nat.mod_eq_of_lt (by omega)
  have p5 : 65536 % Algebra.P = 65536 := Nat.mod_eq_of_lt (by omega)
  have q1 : L / 256 % 256 ≤ 255 := by omega
  have q2 : L / 65536 ≤ 255 := by omega
  have p6 : 256 * (L / 256 % 256) % Algebra.P = 256 * (L / 256 % 256) := Nat.mod_eq_of_lt (by omega)
  have p7 : 65536 * (L / 65536) % Algebra.P = 65536 * (L / 65536) := Nat.mod_eq_of_lt (by omega)
  rw [p1, p2, p3, p4, p5, p6, p7]
  have hsum : L % 256 + (256 * (L / 256 % 256) + 65536 * (L / 65536)) = L := by omega
  rw [show (256 * (L / 256 % 256) + 65536 * (L / 65536)) % Algebra.P = 256 * (L / 256 % 256) + 65536 * (L / 65536)
    from Nat.mod_eq_of_lt (by omega), hsum]

theorem spost_row (Is : List UpsInst) (q i : Nat) (rk : RK) (D : URow) :
    uMsgs (generatedRow Is q (i, rk)) D B_SPOST false =
      match rk with
      | .v p => [reduceMessage [(inst Is i).tau, p, (inst Is i).v.getD p 0]]
      | _ => [] := by
  rw [uMsgs_spost]
  cases rk with
  | w t =>
    have hvb : generatedRow Is q (i, .w t) UpsV3.vb = 0 := rfl
    rw [hvb]; simp; decide
  | v p =>
    have hvb : generatedRow Is q (i, .v p) UpsV3.vb = 1 := rfl
    rw [hvb, show Fp.ofNat 1 = 1 from rfl]
    simp only [ite_true]
    have h1 : generatedRow Is q (i, .v p) UpsV3.tau = (inst Is i).tau % Algebra.P := by
      simp [generatedRow, rowCell, UpsV3.tau, isSeg, segCell]; exact Fp.toNat_ofNat _
    have h2 : generatedRow Is q (i, .v p) UpsV3.qpos = p % Algebra.P := by
      simp [generatedRow, rowCell, UpsV3.qpos, isSeg, vCell]; exact Fp.toNat_ofNat _
    have h3 : generatedRow Is q (i, .v p) UpsV3.b = (inst Is i).v.getD p 0 % Algebra.P := by
      simp [generatedRow, rowCell, UpsV3.b, isSeg, vCell]; exact Fp.toNat_ofNat _
    rw [h1, h2, h3]
    simp [reduceMessage, Nat.mod_mod]
  | q k p =>
    have hvb : generatedRow Is q (i, .q k p) UpsV3.vb = 0 := rfl
    rw [hvb]; simp; decide

theorem splen_row (Is : List UpsInst) (q i : Nat) (rk : RK) (D : URow) (hL : L (inst Is i) < 2 ^ 24) :
    uMsgs (generatedRow Is q (i, rk)) D B_SPLEN false =
      if rk = .w 0 then [reduceMessage [(inst Is i).tau, L (inst Is i)]] else [] := by
  rw [uMsgs_splen]
  cases rk with
  | w t =>
    by_cases ht : t = 0
    · subst ht
      have hsf : generatedRow Is q (i, .w 0) UpsV3.sf = 1 := rfl
      rw [hsf, show Fp.ofNat 1 = 1 from rfl]
      simp only [ite_true]
      have h1 : generatedRow Is q (i, .w 0) UpsV3.tau = (inst Is i).tau % Algebra.P := by
        simp [generatedRow, rowCell, UpsV3.tau, isSeg, segCell]; exact Fp.toNat_ofNat _
      have hL : (uev (generatedRow Is q (i, .w 0)) D UpsV3.Lexpr).toNat = L (inst Is i) % Algebra.P := by
        simp only [uev, Expr.evalWith, uEnv, UpsV3.Lexpr, Dsl.c, Dsl.smul, generatedRow, rowCell,
          UpsV3.L0, UpsV3.L1, UpsV3.L2, isSeg, segCell, Lb]
        simp
        exact lexpr_val _ hL
      rw [h1, hL]
      simp [reduceMessage, Nat.mod_mod]
    · have hsf : generatedRow Is q (i, .w t) UpsV3.sf = 0 := by
        simp [generatedRow, rowCell, isSeg, UpsV3.sf, wCell, ind, ht]; rfl
      rw [hsf]; simp [ht]; decide
  | v p =>
    have hsf : generatedRow Is q (i, .v p) UpsV3.sf = 0 := rfl
    rw [hsf]; simp; decide
  | q k p =>
    have hsf : generatedRow Is q (i, .q k p) UpsV3.sf = 0 := rfl
    rw [hsf]; simp; decide

/-! ## The aligned view -/

private theorem map_range_getD'' {α : Type} (xs : List α) (d : α) :
    (List.range xs.length).map (fun i => xs.getD i d) = xs := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp only [List.getElem_map, List.getElem_range]
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]

private theorem flat_congr'' {α β : Type} (xs : List α) (f g : α → List β)
    (h : ∀ x ∈ xs, f x = g x) : xs.flatMap f = xs.flatMap g := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.flatMap_cons]; rw [h x (by simp), ih (fun y hy => h y (by simp [hy]))]

/-- The aligned view's traffic on a bus whose messages read only columns `< 200`. -/
theorem aligned_view_bus (Is : List UpsInst) (hok : UpsRenderOk Is) (t b : Nat) (sd : Bool)
    (f : Nat → RK → List ZkFormal.Near.Msg)
    (hrow : ∀ q i rk D, i < Is.length → uMsgs (generatedRow Is q (i, rk)) D b sd = f i rk)
    (hcongr : ∀ C C' D D' : URow, (∀ x < 200, C x = C' x) → uMsgs C D b sd = uMsgs C' D' b sd) :
    (viewOf (upsTraceAligned Is) t (segsOf Is)).flatMap (fun s => s.msgs b sd) =
      (List.range Is.length).flatMap (fun i => (recsI (inst Is i)).flatMap (f i)) := by
  simp only [viewOf, segsOf, List.flatMap_map]
  apply flat_congr''
  intro i hi
  have hi' := List.mem_range.mp hi
  unfold UpsSeg.msgs
  rw [segOf_len]
  have he := congrArg (List.flatMap (f i)) (map_range_getD'' (recsI (inst Is i)) default)
  rw [List.flatMap_map] at he
  rw [← he]
  apply flat_congr''
  intro d hd
  rw [hcongr _ (generatedRow Is (start Is i + d) (i, (recsI (inst Is i)).getD d default)) _ (fun _ => 0)
    (aligned_rows Is hok t i hi' d (List.mem_range.mp hd)), hrow _ _ _ _ hi']

private theorem range_flat_single {β : Type} (Is : List UpsInst) (g : UpsInst → β) :
    (List.range Is.length).flatMap (fun i => [g (inst Is i)]) = Is.map g := by
  simp only [← List.map_eq_flatMap]
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.length_map, List.length_range] at h1
  simp [inst, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1]

private theorem range_flat_map {β : Type} (Is : List UpsInst) (g : UpsInst → List β) :
    (List.range Is.length).flatMap (fun i => g (inst Is i)) = Is.flatMap g := by
  have : (List.range Is.length).map (fun i => inst Is i) = Is := by
    simpa [inst] using map_range_getD'' Is default
  rw [show List.flatMap g Is = List.flatMap g ((List.range Is.length).map fun i => inst Is i) by rw [this],
    List.flatMap_map]

private theorem nilF {α : Type} (xs : List α) : xs.flatMap (fun _ => ([] : List ZkFormal.Near.Msg)) = [] := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simpa using ih

/-- **`S0F` sends of the aligned ups view**: one `[τ, pres, vid]` per instance. -/
theorem view_s0f_send (Is : List UpsInst) (hok : UpsRenderOk Is) (t : Nat) :
    (viewOf (upsTraceAligned Is) t (segsOf Is)).flatMap (fun s => s.msgs B_S0F true) =
      Is.map (fun I => reduceMessage [I.tau, presN I, vidN I]) := by
  rw [aligned_view_bus Is hok t B_S0F true
    (fun i rk => if rk = .w 0 then [reduceMessage [(inst Is i).tau, presN (inst Is i), vidN (inst Is i)]] else [])
    (fun q i rk D _ => s0f_row Is q i rk D)
    (fun C C' D D' h => by rw [uMsgs_s0f, uMsgs_s0f, h UpsV3.sf (by decide), h UpsV3.tau (by decide),
      h UpsV3.pres (by decide), h UpsV3.vid (by decide)])]
  rw [← range_flat_single Is (fun I => reduceMessage [I.tau, presN I, vidN I])]
  apply flat_congr''
  intro i _
  simp [recsI, List.range_succ]
  try (intro x a _ b _ h; subst h; simp)

/-- **`SPLEN` receives of the aligned ups view**: one `[τ, L]` per instance. -/
theorem view_splen_recv (Is : List UpsInst) (hok : UpsRenderOk Is) (t : Nat) :
    (viewOf (upsTraceAligned Is) t (segsOf Is)).flatMap (fun s => s.msgs B_SPLEN false) =
      Is.map (fun I => reduceMessage [I.tau, L I]) := by
  have hL : ∀ i, i < Is.length → L (inst Is i) < 2 ^ 24 := by
    intro i hi
    have hm : inst Is i ∈ Is := by
      simp only [inst, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
      exact List.getElem_mem hi
    exact (hok.ok.inst _ hm).Lsmall
  rw [aligned_view_bus Is hok t B_SPLEN false
    (fun i rk => if rk = .w 0 then [reduceMessage [(inst Is i).tau, L (inst Is i)]] else [])
    (fun q i rk D hi => splen_row Is q i rk D (hL i hi))
    (fun C C' D D' h => by
      rw [uMsgs_splen, uMsgs_splen]
      simp only [uev, Expr.evalWith, uEnv, UpsV3.Lexpr, Dsl.c, Dsl.smul, Bool.false_eq_true, ↓reduceIte]
      rw [h UpsV3.sf (by decide), h UpsV3.tau (by decide), h UpsV3.L0 (by decide), h UpsV3.L1 (by decide),
        h UpsV3.L2 (by decide)])]
  rw [← range_flat_single Is (fun I => reduceMessage [I.tau, L I])]
  apply flat_congr''
  intro i _
  simp [recsI, List.range_succ]
  try (intro x a _ b _ h; subst h; simp)

/-- **`SPOST` receives of the aligned ups view**: `[τ, p, v_p]` for every value byte. -/
theorem view_spost_recv (Is : List UpsInst) (hok : UpsRenderOk Is) (t : Nat) :
    (viewOf (upsTraceAligned Is) t (segsOf Is)).flatMap (fun s => s.msgs B_SPOST false) =
      Is.flatMap (fun I => (List.range (L I)).map fun p => reduceMessage [I.tau, p, I.v.getD p 0]) := by
  rw [aligned_view_bus Is hok t B_SPOST false
    (fun i rk => match rk with
      | .v p => [reduceMessage [(inst Is i).tau, p, (inst Is i).v.getD p 0]]
      | _ => [])
    (fun q i rk D _ => spost_row Is q i rk D)
    (fun C C' D D' h => by rw [uMsgs_spost, uMsgs_spost, h UpsV3.vb (by decide), h UpsV3.tau (by decide),
      h UpsV3.qpos (by decide), h UpsV3.b (by decide)])]
  rw [← range_flat_map Is (fun I => (List.range (L I)).map fun p => reduceMessage [I.tau, p, I.v.getD p 0])]
  apply flat_congr''
  intro i _
  simp only [recsI, List.flatMap_append, List.flatMap_map, Function.comp_def]
  have hq : List.flatMap
        (fun rk => match rk with
          | RK.v p => [reduceMessage [(inst Is i).tau, p, (inst Is i).v.getD p 0]]
          | _ => [])
        (List.flatMap (fun k => List.map (RK.q k) (List.range (part (inst Is i) k).q.length))
          (List.range (nQ (inst Is i)))) = [] := by
    rw [List.flatMap_eq_nil_iff]
    intro rk hrk
    obtain ⟨k, -, hk⟩ := List.mem_flatMap.mp hrk
    obtain ⟨x, -, rfl⟩ := List.mem_map.mp hk
    rfl
  rw [hq, nilF, List.nil_append, List.append_nil, List.map_eq_flatMap]

theorem view_s0f_recv (Is : List UpsInst) (t : Nat) :
    (viewOf (upsTraceAligned Is) t (segsOf Is)).flatMap (fun s => s.msgs B_S0F false) = [] := by
  simp [viewOf, UpsSeg.msgs, uMsgs_s0f_recv]
theorem view_splen_send (Is : List UpsInst) (t : Nat) :
    (viewOf (upsTraceAligned Is) t (segsOf Is)).flatMap (fun s => s.msgs B_SPLEN true) = [] := by
  simp [viewOf, UpsSeg.msgs, uMsgs_splen_send]
theorem view_spost_send (Is : List UpsInst) (t : Nat) :
    (viewOf (upsTraceAligned Is) t (segsOf Is)).flatMap (fun s => s.msgs B_SPOST true) = [] := by
  simp [viewOf, UpsSeg.msgs, uMsgs_spost_send]

/-! ## `BYTES` (the ups jobs: value job `0`, part `k` = job `k + 1`) -/

theorem uMsgs_bytes (C D : URow) :
    uMsgs C D B_BYTES true =
      if uev C D (.add (Dsl.c UpsV3.vb) (Dsl.c UpsV3.qb)) = 1 then
        [[(uev C D (UpsV3.upsId (Dsl.c UpsV3.j))).toNat, C UpsV3.qpos % Algebra.P, C UpsV3.b % Algebra.P]]
      else [] := by
  simp [uMsgs, UpsV3.interactions, Dsl.send, Dsl.recv,
    B_EDGE, B_BMAP, B_MIDROOT, B_ROOT, B_DIGEST, B_S0F, B_SPLEN, B_SPOST, B_BYTES, B_UPB, B_MEMD, uMult]
  split <;> simp_all [uev, Expr.evalWith, uEnv, Dsl.c]

theorem uMsgs_bytes_recv (C D : URow) : uMsgs C D B_BYTES false = [] := by
  simp [uMsgs, UpsV3.interactions, Dsl.send, Dsl.recv,
    B_EDGE, B_BMAP, B_MIDROOT, B_ROOT, B_DIGEST, B_S0F, B_SPLEN, B_SPOST, B_BYTES, B_UPB, B_MEMD]

theorem id_val (a b : Nat) :
    (Fp.ofNat 12 + Fp.ofNat 16 * (Fp.ofNat 512 * Fp.ofNat (a % Algebra.P) + Fp.ofNat (b % Algebra.P))).toNat =
      ZkFormal.NearV3.Assembly.upsertJobId a b % Algebra.P := by
  show (Fp.add (Fp.ofNat 12) (Fp.mul (Fp.ofNat 16) (Fp.add (Fp.mul (Fp.ofNat 512) (Fp.ofNat (a % Algebra.P)))
    (Fp.ofNat (b % Algebra.P))))).toNat = _
  simp only [Fp.toNat_add, Fp.toNat_mul, Fp.toNat_ofNat, ZkFormal.NearV3.Assembly.upsertJobId]
  have hP : Algebra.P = 2013265921 := rfl
  rw [hP]
  omega

theorem uev_upsId (C D : URow) :
    (uev C D (UpsV3.upsId (Dsl.c UpsV3.j))).toNat =
      ZkFormal.NearV3.Assembly.upsertJobId (C UpsV3.tau) (C UpsV3.j) % Algebra.P := by
  show (Fp.add (Fp.ofNat 12) (Fp.mul (Fp.ofNat 16) (Fp.add (Fp.mul (Fp.ofNat 512) (Fp.ofNat (C UpsV3.tau)))
    (Fp.ofNat (C UpsV3.j))))).toNat = _
  simp only [Fp.toNat_add, Fp.toNat_mul, Fp.toNat_ofNat, ZkFormal.NearV3.Assembly.upsertJobId]
  have hP : Algebra.P = 2013265921 := rfl
  rw [hP]
  omega

theorem jobId_mod (a b : Nat) :
    ZkFormal.NearV3.Assembly.upsertJobId (a % Algebra.P) (b % Algebra.P) % Algebra.P =
      ZkFormal.NearV3.Assembly.upsertJobId a b % Algebra.P := by
  simp only [ZkFormal.NearV3.Assembly.upsertJobId]
  have hP : Algebra.P = 2013265921 := rfl
  rw [hP]
  omega

theorem bytes_row (Is : List UpsInst) (q i : Nat) (rk : RK) (D : URow) :
    uMsgs (generatedRow Is q (i, rk)) D B_BYTES true =
      match rk with
      | .w _ => []
      | .v p => [reduceMessage [ZkFormal.NearV3.Assembly.upsertJobId (inst Is i).tau 0, p, (inst Is i).v.getD p 0]]
      | .q k p => [reduceMessage [ZkFormal.NearV3.Assembly.upsertJobId (inst Is i).tau (k + 1), p,
          (part (inst Is i) k).q.getD p 0]] := by
  rw [uMsgs_bytes]
  have ht : ∀ r, generatedRow Is q (i, r) UpsV3.tau = (inst Is i).tau % Algebra.P := by
    intro r
    simp [generatedRow, rowCell, UpsV3.tau, isSeg, segCell]; exact Fp.toNat_ofNat _
  cases rk with
  | w t =>
    have h1 : generatedRow Is q (i, .w t) UpsV3.vb = 0 := rfl
    have h2 : generatedRow Is q (i, .w t) UpsV3.qb = 0 := rfl
    simp only [uev, Expr.evalWith, uEnv, Dsl.c, h1, h2, Bool.false_eq_true, ↓reduceIte]
    rw [if_neg (by decide)]
  | v p =>
    have h1 : generatedRow Is q (i, .v p) UpsV3.vb = 1 := rfl
    have h2 : generatedRow Is q (i, .v p) UpsV3.qb = 0 := rfl
    have h3 : generatedRow Is q (i, .v p) UpsV3.j = 0 := rfl
    have h4 : generatedRow Is q (i, .v p) UpsV3.qpos = p % Algebra.P := by
      simp [generatedRow, rowCell, UpsV3.qpos, isSeg, vCell]; exact Fp.toNat_ofNat _
    have h5 : generatedRow Is q (i, .v p) UpsV3.b = (inst Is i).v.getD p 0 % Algebra.P := by
      simp [generatedRow, rowCell, UpsV3.b, isSeg, vCell]; exact Fp.toNat_ofNat _
    rw [if_pos (by simp only [uev, Expr.evalWith, uEnv, Dsl.c, h1, h2, Bool.false_eq_true, ↓reduceIte]; decide),
      uev_upsId, ht, h3, h4, h5]
    simp only [reduceMessage, List.map_cons, List.map_nil, Fp.toNat_ofNat, Nat.mod_mod]
    have := jobId_mod (inst Is i).tau 0
    rw [Nat.zero_mod] at this
    rw [this]
  | q k p =>
    have h1 : generatedRow Is q (i, .q k p) UpsV3.vb = 0 := rfl
    have h2 : generatedRow Is q (i, .q k p) UpsV3.qb = 1 := rfl
    have h3 : generatedRow Is q (i, .q k p) UpsV3.j = (k + 1) % Algebra.P := by
      simp [generatedRow, rowCell, UpsV3.j, isSeg, qCell, isPC, pcCell]; exact Fp.toNat_ofNat _
    have h4 : generatedRow Is q (i, .q k p) UpsV3.qpos = p % Algebra.P := by
      simp [generatedRow, rowCell, UpsV3.qpos, isSeg, qCell, isPC, qRowCell, qRow]; exact Fp.toNat_ofNat _
    have h5 : generatedRow Is q (i, .q k p) UpsV3.b = (part (inst Is i) k).q.getD p 0 % Algebra.P := by
      simp [generatedRow, rowCell, UpsV3.b, isSeg, qCell, isPC, qRowCell, qRow]; exact Fp.toNat_ofNat _
    rw [if_pos (by simp only [uev, Expr.evalWith, uEnv, Dsl.c, h1, h2, Bool.false_eq_true, ↓reduceIte]; decide),
      uev_upsId, ht, h3, h4, h5, jobId_mod]
    simp only [reduceMessage, List.map_cons, List.map_nil, Fp.toNat_ofNat, Nat.mod_mod]

/-- The ups `BYTES` messages of one instance: the new value (job `0`), then part `k` (job `k + 1`). -/
def upsBytes (I : UpsInst) : List ZkFormal.Near.Msg :=
  (List.range (L I)).map (fun p => reduceMessage [ZkFormal.NearV3.Assembly.upsertJobId I.tau 0, p, I.v.getD p 0]) ++
    (List.range (nQ I)).flatMap (fun k => (List.range (part I k).q.length).map (fun p =>
      reduceMessage [ZkFormal.NearV3.Assembly.upsertJobId I.tau (k + 1), p, (part I k).q.getD p 0]))

/-- **`BYTES` sends of the aligned ups view.** -/
theorem view_bytes_send (Is : List UpsInst) (hok : UpsRenderOk Is) (t : Nat) :
    (viewOf (upsTraceAligned Is) t (segsOf Is)).flatMap (fun s => s.msgs B_BYTES true) = Is.flatMap upsBytes := by
  rw [aligned_view_bus Is hok t B_BYTES true
    (fun i rk => match rk with
      | .w _ => []
      | .v p => [reduceMessage [ZkFormal.NearV3.Assembly.upsertJobId (inst Is i).tau 0, p, (inst Is i).v.getD p 0]]
      | .q k p => [reduceMessage [ZkFormal.NearV3.Assembly.upsertJobId (inst Is i).tau (k + 1), p,
          (part (inst Is i) k).q.getD p 0]])
    (fun q i rk D _ => bytes_row Is q i rk D)
    (fun C C' D D' h => by
      rw [uMsgs_bytes, uMsgs_bytes, uev_upsId, uev_upsId]
      simp only [uev, Expr.evalWith, uEnv, Dsl.c, Bool.false_eq_true, ↓reduceIte]
      rw [h UpsV3.vb (by decide), h UpsV3.qb (by decide), h UpsV3.tau (by decide), h UpsV3.j (by decide),
        h UpsV3.qpos (by decide), h UpsV3.b (by decide)])]
  rw [← range_flat_map Is upsBytes]
  apply flat_congr''
  intro i _
  simp only [recsI, upsBytes, List.flatMap_append, List.flatMap_map]
  simp [List.map_eq_flatMap, List.flatMap_assoc]

theorem view_bytes_recv (Is : List UpsInst) (t : Nat) :
    (viewOf (upsTraceAligned Is) t (segsOf Is)).flatMap (fun s => s.msgs B_BYTES false) = [] := by
  simp [viewOf, UpsSeg.msgs, uMsgs_bytes_recv]

/-! ## The ups `BYTES` messages are the upsert SHA jobs' bytes -/

theorem toFp_reduce (m : ZkFormal.Near.Msg) : Msg.toFp (reduceMessage m) = Msg.toFp m := by
  simp only [Msg.toFp, reduceMessage, List.map_map, Function.comp_def, Fp.ofNat_toNat]

/-- **Per instance**: the ups `BYTES` sends are (as field messages) the expected bytes of the
upsert SHA jobs `upsertShaJobs I.tau u.value u.run` (`NativeShaFamily`). -/
theorem ups_bytes_jobs (u : SchedulerUpsertWitness) (I : UpsInst) (hf : NativeShaFamily u I)
    (hv : I.v = u.value.map UInt8.toNat) :
    (upsBytes I).map Msg.toFp = (Sha.Gen.expectedBytes (upsertShaJobs I.tau u.value u.run)).map Msg.toFp := by
  obtain ⟨hn, hk⟩ := hf
  let rest := upsertShaFrom I.tau 1 (u.run.parts.map (fun p => nodeEnc p.output))
  have hsplit : upsertShaJobs I.tau u.value u.run = upsertShaJob I.tau 0 u.value :: rest := rfl
  have hlen : rest.length = nQ I := by simp [rest, hn]
  have hget : ∀ k, k < nQ I → (rest.getD k ⟨0, [], false⟩).id = upsertJobId I.tau (k + 1) ∧
      (rest.getD k ⟨0, [], false⟩).bytes = (part I k).q := by
    intro k hkq
    obtain ⟨M, hM, hid, hb⟩ := hk k hkq
    rw [hsplit] at hM
    simp only [List.getElem?_cons_succ] at hM
    simp only [List.getD_eq_getElem?_getD, hM, Option.getD_some]
    exact ⟨hid, hb⟩
  have hrest : rest = (List.range (nQ I)).map (fun k => rest.getD k ⟨0, [], false⟩) := by
    rw [← hlen]; exact (map_range_getD'' rest ⟨0, [], false⟩).symm
  rw [hsplit, Sha.Gen.expectedBytes, List.flatMap_cons, ← Sha.Gen.expectedBytes, hrest]
  simp only [upsBytes, List.map_append, List.map_map, Sha.Gen.expectedBytes, List.flatMap_map]
  have hb0 : (upsertShaJob I.tau 0 u.value).bytes = I.v := by simp [upsertShaJob, hv]
  have hid0 : (upsertShaJob I.tau 0 u.value).id = upsertJobId I.tau 0 := rfl
  rw [hb0, hid0]
  congr 1
  · simp only [L]
    apply List.map_congr_left
    intro p _
    simp [Function.comp_def, toFp_reduce]
  · simp only [List.map_flatMap]
    apply flat_congr''
    intro k hkr
    obtain ⟨hid, hb⟩ := hget k (List.mem_range.mp hkr)
    rw [hid, hb]
    simp [Function.comp_def, toFp_reduce]

end ZkFormal.NearV3.Assembly.TrieUpsSched
