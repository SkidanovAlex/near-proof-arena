import ZkFormal.NearV3.Assembly.TrieUps
import ZkFormal.NearV3.Candidates.PhysicalWindowBalance
import ZkFormal.NearV3.Rcpt.Candidates.UpsWindowGeneratedAddress
import ZkFormal.NearV3.Candidates.WindowKeyCanonical
import ZkFormal.NearV3.Rcpt.Candidates.UpsWindowBalance
import ZkFormal.NearV3.Rcpt.Candidates.NativeWindowCoverage

/-!
# ZkFormal.NearV3.Assembly.TrieUpb — the `UPB` balance of the aligned ups render

`upsV3` read rows (`rd`) receive `[NPOST(sN), spos, rb, plen, pdep, rcid, u]` and send it with
`u + 1`; `nodeV3` sends every window key with `0` and receives it with its use count.  The aligned
ups render (`upsTraceAligned`) uses the counter `uU` (earlier rows with the same read key
`rkey = (sN, spos)`).

* `aligned_window_row` / `aligned_window_count`: the `UPB` traffic of any `upsV3` trace whose read
  counters are the physical ranks (`physicalWindowRank`), as `physicalWindowMessages`;
* `aligned_upb_balance`: then `window_counter_balance` gives the field-level balance against the
  provider keys;
* `uU_rank`: on the aligned render, **`uU = physicalWindowRank`** on every read row, given the
  part-level coverage `PartCov` (every read byte's natural source key `readerSourceKey` is a node
  window key, with a nonnegative position): equal `(sN, spos)` ⇔ equal six-field key, since window
  keys with the same `(NPOST(n), p)` are equal (`nodeWindowKeys_eq`);
* **`aligned_upbBal`**: the record-level `UpbBal` of `assignList q 0 vs` (with
  `q.windows = PhysicalWindowRequests.keys (upsTraceAligned Js) t`) and the aligned ups view.
-/

namespace ZkFormal.NearV3.Assembly.TrieUpb

open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3 Assembly Render Render.UpsGen
  Render.UpsRelay UpsRows Rcpt.Candidates Rcpt.Candidates.NodePostUpdate

/-! ## Trace level: any `upsV3` trace with ranked read counters -/

theorem aligned_window_row (tr : Trace Fp) (t r : Nat) (pub : List Fp) (sd : Bool) :
    rowTraffic UpsV3.interactions tr t r pub B_UPB sd =
      if tr.cell t r UpsV3.rd = 1 then
        [windowFieldKey tr t r ++ [if sd then tr.cell t r UpsV3.u + 1 else tr.cell t r UpsV3.u]] else [] := by
  cases sd <;> by_cases hr : tr.cell t r UpsV3.rd = 1 <;>
    simp only [UpsV3.rd] at hr <;>
    simp [rowTraffic, UpsV3.interactions, send, recv,
      Interaction.multNat, Interaction.multNat.go, Interaction.msgVal, Expr.eval, Expr.evalWith, rowEnv,
      B_UPB, B_MIDROOT, B_ROOT, B_DIGEST, B_S0F, B_SPLEN, B_SPOST, B_BYTES, B_EDGE, B_BMAP, B_MEMD,
      UpsV3.upbMsg, mid, smul, c, k, hr,
      UpsV3.rd, UpsV3.u, UpsV3.sN, UpsV3.spos, UpsV3.rb, UpsV3.plen, UpsV3.pdep, UpsV3.rcid,
      windowFieldKey]
  all_goals simp only [← ofNat_add', ← ofNat_mul', Fp.ofNat_toNat]
  all_goals first | rfl | exact ⟨rfl, rfl⟩

/-- Read counters are the physical ranks. -/
def Ranked (tr : Trace Fp) (t : Nat) : Prop :=
  ∀ r < tr.height t, tr.cell t r UpsV3.rd = 1 → tr.cell t r UpsV3.u = Fp.ofNat (physicalWindowRank tr t r)

theorem aligned_window_count (tr : Trace Fp) (t : Nat) (pub : List Fp) (sd : Bool) (msg : List Fp)
    (hu : Ranked tr t) :
    tableBusCount UpsV3.interactions tr t pub B_UPB sd msg =
      ((physicalWindowMessages tr t sd).map Msg.toFp).count msg := by
  rw [tableBusCount_eq]
  congr 1
  rw [physicalWindowMessages, List.map_flatMap]
  apply UpsRows.flatMap_congr'
  intro r hr
  change rowTraffic UpsV3.interactions _ _ _ _ _ _ = _
  rw [aligned_window_row]
  by_cases h : tr.cell t r UpsV3.rd = 1
  · simp only [h, ite_true, List.map_cons, List.map_nil]
    congr 1
    simp only [Msg.toFp, List.map_append, List.map_cons, List.map_nil]
    rw [show List.map Fp.ofNat (physicalWindowKey tr t r) = windowFieldKey tr t r from
      physicalWindowKey_toFp tr t r, hu r (List.mem_range.mp hr) h]
    cases sd
    · rfl
    · simp only [ite_true]; rw [← ofNat_add']; rfl
  · simp [h]

theorem aligned_upb_balance (tr : Trace Fp) (t : Nat) (pub : List Fp) (es : List ZkFormal.Near.Msg) (hn : es.Nodup)
    (hc : ∀ r ∈ physicalWindowRows tr t, physicalWindowKey tr t r ∈ es) (hu : Ranked tr t) (msg : List Fp) :
    ((es.map (fun e => e ++ [0])).map Msg.toFp).count msg +
        tableBusCount UpsV3.interactions tr t pub B_UPB true msg =
      tableBusCount UpsV3.interactions tr t pub B_UPB false msg +
        ((es.map (fun e => e ++ [physicalWindowUsers tr t e])).map Msg.toFp).count msg := by
  rw [aligned_window_count _ _ _ _ _ hu, aligned_window_count _ _ _ _ _ hu]
  have h := ((window_counter_balance tr t es hn hc).map Msg.toFp).count_eq msg
  simpa only [List.map_append, List.count_append] using h

/-- Record-level `UpbBal` from a ranked `upsV3` trace whose provider keys cover every read. -/
theorem upbBal_of_trace (q : UseRequests) (vs : List NodeS3) (tr : Trace Fp) (t : Nat) (pub : List Fp)
    (v : List UpsSeg) (hT : TableTraffic UpsV3.interactions tr t pub (upsTraffic v))
    (hq : q.windows = Candidates.PhysicalWindowRequests.keys tr t)
    (hc : ∀ r ∈ physicalWindowRows tr t, physicalWindowKey tr t r ∈ nodeWindowKeys vs)
    (hu : Ranked tr t) :
    UpbBal (assignList q 0 vs) v := by
  apply List.perm_iff_count.mpr
  intro msg
  have hb := aligned_upb_balance tr t pub (nodeWindowKeys vs) (nodeWindowKeys_distinct vs) hc hu msg
  rw [(hT B_UPB msg).1, (hT B_UPB msg).2] at hb
  simp only [List.map_append, List.count_append, Candidates.PhysicalWindowBalance.assigned_send,
    Candidates.PhysicalWindowBalance.assigned_recv, hq, Candidates.PhysicalWindowRequests.count]
  omega

/-! ## Window keys -/

theorem nodeWindowKeys_get {vs : List NodeS3} {key : ZkFormal.Near.Msg} (hk : key ∈ nodeWindowKeys vs) :
    ∃ n p s, vs[n]? = some s ∧ p < (s.v.ser false).length ∧ key = windowKey n p s := by
  obtain ⟨⟨s, n⟩, hs, hk'⟩ := List.mem_flatMap.mp hk
  obtain ⟨p, hp, hkey⟩ := List.mem_map.mp hk'
  obtain ⟨i, hi, hget⟩ := List.mem_iff_getElem.mp hs
  have hil : i < vs.length := by simpa using hi
  have hg : vs[i] = s ∧ i = n := by
    simpa only [List.getElem_zip, List.getElem_range, Prod.mk.injEq] using hget
  obtain ⟨hgs, rfl⟩ := hg
  exact ⟨i, p, s, List.getElem?_eq_some_iff.mpr ⟨hil, hgs⟩, List.mem_range.mp hp, hkey.symm⟩

/-- Window keys with the same `(NPOST(n), p)` are equal. -/
theorem nodeWindowKeys_eq {vs : List NodeS3} {k₁ k₂ : ZkFormal.Near.Msg} (h₁ : k₁ ∈ nodeWindowKeys vs)
    (h₂ : k₂ ∈ nodeWindowKeys vs) (h0 : k₁[0]? = k₂[0]?) (h1 : k₁[1]? = k₂[1]?) : k₁ = k₂ := by
  obtain ⟨n, p, s, hs, -, rfl⟩ := nodeWindowKeys_get h₁
  obtain ⟨n', p', s', hs', -, rfl⟩ := nodeWindowKeys_get h₂
  simp only [windowKey, msgId, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.some.injEq] at h0 h1
  have hn : n = n' := by omega
  subst hn; subst h1
  rw [hs] at hs'
  cases hs'
  rfl

theorem phys_key_eq {vs : List NodeS3} (hw : NodeWf3 vs) (hb : ∀ s ∈ vs, ∀ x ∈ s.v.ser true, x < 256)
    (tr : Trace Fp) (t r : Nat) {key : ZkFormal.Near.Msg} (hk : key ∈ nodeWindowKeys vs)
    (he : windowFieldKey tr t r = key.map Fp.ofNat) : physicalWindowKey tr t r = key := by
  obtain ⟨n, p, s, hs, hp, rfl⟩ := nodeWindowKeys_get hk
  exact Candidates.WindowKeyCanonical.physical_eq hw hs hp (hb s (List.mem_of_getElem? hs)) tr t r he

/-! ## The aligned ups render -/

theorem aligned_cell (Js : List UpsInst) (t r x : Nat) (hr : r < (upsTraceAligned Js).height t)
    (hx : x < 200) : (upsTraceAligned Js).cell t r x = ((cell Js r x : Int) : Fp) := by
  change r < 2 ^ ZkFormal.Size.padLog22 (ZkFormal.Near.Render.logOf (R Js + 1)) at hr
  unfold upsTraceAligned
  rw [rowsTrace_mkTab _ _ _ t r x hr hx, Fp.ofNat_toNat]

theorem aligned_height (Js : List UpsInst) (t : Nat) (hcap : R Js + 1 ≤ 2 ^ 22) :
    R Js + 1 ≤ (upsTraceAligned Js).height t :=
  (padded_log_fits (R Js + 1) hcap).1

/-- The read bit of row `p` of part `k` (the `rkey` / `rd` condition). -/
def rbit (I : UpsInst) (k p : Nat) : Bool :=
  CpB I (part I k) (fieldAt (part I k).shape p).1 (fieldAt (part I k).shape p).2.2.2 ||
    ExtraB I (part I k) (fieldAt (part I k).shape p).1 (fieldAt (part I k).shape p).2.1
      (fieldAt (part I k).shape p).2.2.2

/-- The read position of row `p` of part `k`. -/
def spq (I : UpsInst) (k p : Nat) : Int :=
  sposV I (part I k) (fieldAt (part I k).shape p).1 (fieldAt (part I k).shape p).2.1
    (fieldAt (part I k).shape p).2.2.2 p

theorem rkey_q (Js : List UpsInst) (i k p : Nat) :
    rkey Js (i, .q k p) =
      if rbit (inst Js i) k p then some ((part (inst Js i) k).sN, spq (inst Js i) k p) else none := rfl

/-- Part-level coverage: every read byte's natural source key is a node window key. -/
def PartCov (Js : List UpsInst) (vs : List NodeS3) : Prop :=
  ∀ i k p, i < Js.length → k < nQ (inst Js i) → p < (part (inst Js i) k).q.length →
    rbit (inst Js i) k p = true →
    0 ≤ spq (inst Js i) k p ∧
      readerSourceKey (part (inst Js i) k) (spq (inst Js i) k p).toNat ∈ nodeWindowKeys vs

theorem recs_getD_mem {Js : List UpsInst} {r : Nat} (ha : r < R Js) :
    (recs Js).getD r default ∈ recs Js := by
  have h : r < (recs Js).length := ha
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]
  exact List.getElem_mem h

theorem aligned_read_row (Js : List UpsInst) (t r : Nat) (hr : r < (upsTraceAligned Js).height t)
    (hrd : (upsTraceAligned Js).cell t r UpsV3.rd = 1) :
    r < R Js ∧ ∃ i k p, (recs Js).getD r default = (i, .q k p) ∧ i < Js.length ∧ k < nQ (inst Js i) ∧
      p < (part (inst Js i) k).q.length ∧ rbit (inst Js i) k p = true := by
  rw [aligned_cell Js t r _ hr (by decide)] at hrd
  have ha : r < R Js := by
    by_cases hn : r < R Js
    · exact hn
    simp only [cell, hn, ite_false] at hrd
    exact absurd hrd (by decide)
  refine ⟨ha, ?_⟩
  obtain ⟨hi, hrk⟩ := mem_recs.mp (recs_getD_mem ha)
  rcases mem_recsI.mp hrk with ⟨j, hj, hrow⟩ | ⟨p, hp, hrow⟩ | ⟨k, p, hk, hp, hrow⟩
  · have he : (recs Js).getD r default = (((recs Js).getD r default).1, .w j) := Prod.ext rfl hrow
    rw [cell, if_pos ha, he] at hrd
    simp [rowCell, isSeg, wCell, UpsV3.rd] at hrd
    exact absurd hrd (by decide)
  · have he : (recs Js).getD r default = (((recs Js).getD r default).1, .v p) := Prod.ext rfl hrow
    rw [cell, if_pos ha, he] at hrd
    simp [rowCell, isSeg, vCell, UpsV3.rd] at hrd
    exact absurd hrd (by decide)
  · have he : (recs Js).getD r default = (((recs Js).getD r default).1, .q k p) := Prod.ext rfl hrow
    refine ⟨_, k, p, he, hi, hk, hp, ?_⟩
    rw [cell, if_pos ha, he] at hrd
    simp only [rowCell, show isSeg UpsV3.rd = false by decide, Bool.false_eq_true, ite_false] at hrd
    have hg := qCell_read_gate _ k p _ hrd
    unfold rdV ind at hg
    unfold rbit
    by_cases hb : (CpB (inst Js ((recs Js).getD r default).1) (part (inst Js ((recs Js).getD r default).1) k)
        (fieldAt (part (inst Js ((recs Js).getD r default).1) k).shape p).1
        (fieldAt (part (inst Js ((recs Js).getD r default).1) k).shape p).2.2.2 ||
      ExtraB (inst Js ((recs Js).getD r default).1) (part (inst Js ((recs Js).getD r default).1) k)
        (fieldAt (part (inst Js ((recs Js).getD r default).1) k).shape p).1
        (fieldAt (part (inst Js ((recs Js).getD r default).1) k).shape p).2.1
        (fieldAt (part (inst Js ((recs Js).getD r default).1) k).shape p).2.2.2) = true
    · exact hb
    · rw [if_neg hb] at hg
      exact absurd hg (by decide)

theorem aligned_u (Js : List UpsInst) (t r : Nat) (hr : r < (upsTraceAligned Js).height t) (ha : r < R Js)
    {i k p : Nat} (hrow : (recs Js).getD r default = (i, .q k p)) (hb : rbit (inst Js i) k p = true) :
    (upsTraceAligned Js).cell t r UpsV3.u = Fp.ofNat (UpsGen.uU Js r) := by
  rw [aligned_cell Js t r _ hr (by decide), cell, if_pos ha, hrow]
  unfold rbit at hb
  simp only [rowCell, show isSeg UpsV3.u = false by decide, Bool.false_eq_true, ite_false, qCell,
    show isPC UpsV3.u = false by decide, qRowCell, qRow, UpsV3.u, hb, ite_true]
  rfl

theorem aligned_key (Js : List UpsInst) (t r : Nat) (hr : r < (upsTraceAligned Js).height t) (ha : r < R Js)
    {i k p : Nat} (hrow : (recs Js).getD r default = (i, .q k p)) (hpos : 0 ≤ spq (inst Js i) k p) :
    windowFieldKey (upsTraceAligned Js) t r =
      (readerSourceKey (part (inst Js i) k) (spq (inst Js i) k p).toNat).map Fp.ofNat := by
  simp only [windowFieldKey, aligned_cell Js t r _ hr (by decide : UpsV3.sN < 200),
    aligned_cell Js t r _ hr (by decide : UpsV3.spos < 200), aligned_cell Js t r _ hr (by decide : UpsV3.rb < 200),
    aligned_cell Js t r _ hr (by decide : UpsV3.plen < 200), aligned_cell Js t r _ hr (by decide : UpsV3.pdep < 200),
    aligned_cell Js t r _ hr (by decide : UpsV3.rcid < 200), cell, ha, ite_true, hrow, rowCell]
  unfold spq at hpos ⊢
  have castN (n : Nat) : ((n : Int) : Fp) = Fp.ofNat n := rfl
  have castPos (z : Int) (hz : 0 ≤ z) : (z : Fp) = Fp.ofNat z.toNat := by
    exact (congrArg (fun x : Int => (x : Fp)) (Int.toNat_of_nonneg hz)).symm
  simp [qCell, qRowCell, qRow, isSeg, isPC, pcCell, rbV, readerSourceKey, msgId,
    UpsV3.sN, UpsV3.spos, UpsV3.rb, UpsV3.plen, UpsV3.pdep, UpsV3.rcid,
    castN, castPos _ hpos]

section
variable {Js : List UpsInst} {vs : List NodeS3} (hw : NodeWf3 vs)
  (hb : ∀ s ∈ vs, ∀ x ∈ s.v.ser true, x < 256) (hcov : PartCov Js vs) (t : Nat)
include hw hb hcov

/-- A read row: its part row, its read key, and its physical key = the natural source key. -/
theorem read_info {r : Nat} (hr : r < (upsTraceAligned Js).height t)
    (hrd : (upsTraceAligned Js).cell t r UpsV3.rd = 1) :
    r < R Js ∧ ∃ i k p, (recs Js).getD r default = (i, .q k p) ∧ rbit (inst Js i) k p = true ∧
      rkey Js ((recs Js).getD r default) = some ((part (inst Js i) k).sN, spq (inst Js i) k p) ∧
      0 ≤ spq (inst Js i) k p ∧
      physicalWindowKey (upsTraceAligned Js) t r =
        readerSourceKey (part (inst Js i) k) (spq (inst Js i) k p).toNat ∧
      readerSourceKey (part (inst Js i) k) (spq (inst Js i) k p).toNat ∈ nodeWindowKeys vs := by
  obtain ⟨ha, i, k, p, hrow, hi, hk, hp, hbit⟩ := aligned_read_row Js t r hr hrd
  obtain ⟨hpos, hmem⟩ := hcov i k p hi hk hp hbit
  refine ⟨ha, i, k, p, hrow, hbit, by rw [hrow, rkey_q, if_pos hbit], hpos,
    phys_key_eq hw hb _ t r hmem (aligned_key Js t r hr ha hrow hpos), hmem⟩

end

theorem rd_of_rkey (Js : List UpsInst) (t j : Nat) (hj : j < (upsTraceAligned Js).height t) (ha : j < R Js)
    {x : Nat × Int} (hx : rkey Js ((recs Js).getD j default) = some x) :
    (upsTraceAligned Js).cell t j UpsV3.rd = 1 := by
  obtain ⟨hi, hrk⟩ := mem_recs.mp (recs_getD_mem ha)
  rcases mem_recsI.mp hrk with ⟨j', -, hrow⟩ | ⟨p, -, hrow⟩ | ⟨k, p, -, -, hrow⟩
  · rw [show (recs Js).getD j default = (((recs Js).getD j default).1, .w j') from Prod.ext rfl hrow] at hx
    simp [rkey] at hx
  · rw [show (recs Js).getD j default = (((recs Js).getD j default).1, .v p) from Prod.ext rfl hrow] at hx
    simp [rkey] at hx
  · have he : (recs Js).getD j default = (((recs Js).getD j default).1, .q k p) := Prod.ext rfl hrow
    rw [he, rkey_q] at hx
    have hbit : rbit (inst Js ((recs Js).getD j default).1) k p = true := by
      by_cases h : rbit (inst Js ((recs Js).getD j default).1) k p = true
      · exact h
      · rw [if_neg h] at hx; exact absurd hx (by simp)
    rw [aligned_cell Js t j _ hj (by decide), cell, if_pos ha, he]
    unfold rbit at hbit
    simp only [rowCell, show isSeg UpsV3.rd = false by decide, Bool.false_eq_true, ite_false, qCell,
      show isPC UpsV3.rd = false by decide, qRowCell, qRow, UpsV3.rd, rdV, ind, hbit, ite_true]
    rfl

theorem take_eq_map_getD {α : Type} (l : List α) (d : α) (r : Nat) (h : r ≤ l.length) :
    l.take r = (List.range r).map (fun j => l.getD j d) := by
  apply List.ext_getElem
  · simp; omega
  · intro n h1 h2
    simp only [List.getElem_take, List.getElem_map, List.getElem_range]
    simp only [List.length_map, List.length_range] at h2
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show n < l.length by omega)]

/-- **The aligned render's read counter is the physical rank.** -/
theorem uU_rank {Js : List UpsInst} {vs : List NodeS3} (hw : NodeWf3 vs)
    (hb : ∀ s ∈ vs, ∀ x ∈ s.v.ser true, x < 256) (hcov : PartCov Js vs) (t : Nat)
    (hcap : R Js + 1 ≤ 2 ^ 22) {r : Nat} (hr : r < (upsTraceAligned Js).height t)
    (hrd : (upsTraceAligned Js).cell t r UpsV3.rd = 1) :
    UpsGen.uU Js r = physicalWindowRank (upsTraceAligned Js) t r := by
  obtain ⟨ha, i, k, p, hrow, hbit, hkey, hpos, hpk, hmem⟩ := read_info hw hb hcov t hr hrd
  unfold UpsGen.uU physicalWindowRank
  rw [take_eq_map_getD _ default r (by unfold UpsGen.R at ha; omega), List.filter_map, List.length_map,
    ← List.countP_eq_length_filter]
  apply List.countP_congr
  intro j hj
  have hjr := List.mem_range.mp hj
  have hjH : j < (upsTraceAligned Js).height t := by omega
  have hjR : j < R Js := by omega
  simp only [Function.comp_apply, selectedWindow, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  constructor
  · intro he
    rw [hkey] at he
    have hrdj := rd_of_rkey Js t j hjH hjR he
    obtain ⟨-, i', k', p', -, -, hkey', hpos', hpk', hmem'⟩ := read_info hw hb hcov t hjH hrdj
    rw [hkey'] at he
    simp only [Option.some.injEq, Prod.mk.injEq] at he
    refine ⟨hrdj, ?_⟩
    rw [hpk', hpk]
    apply nodeWindowKeys_eq hmem' hmem
    · simp [readerSourceKey, he.1]
    · simp [readerSourceKey, he.2]
  · rintro ⟨hrdj, he⟩
    obtain ⟨-, i', k', p', -, -, hkey', hpos', hpk', -⟩ := read_info hw hb hcov t hjH hrdj
    rw [hkey', hkey]
    rw [hpk', hpk] at he
    have h0 := congrArg (fun l : List Nat => l[0]?) he
    have h1 := congrArg (fun l : List Nat => l[1]?) he
    simp only [readerSourceKey, msgId, List.getElem?_cons_zero, List.getElem?_cons_succ,
      Option.some.injEq] at h0 h1
    have hs : (part (inst Js i') k').sN = (part (inst Js i) k).sN := by omega
    have hp' : spq (inst Js i') k' p' = spq (inst Js i) k p := by omega
    rw [hs, hp']

/-- **`UpbBal` of native node records and the aligned ups view**, with the window requests the
physical read keys of the aligned render.  The coverage is stated for records `vs₀` whose window
keys are among those of `vs` (e.g. `vs` = `vs₀` with chain metadata). -/
theorem aligned_upbBal (Js : List UpsInst) (hok : UpsRenderOk Js) (t : Nat) {vs₀ vs : List NodeS3}
    (hw : NodeWf3 vs₀) (hb : ∀ s ∈ vs₀, ∀ x ∈ s.v.ser true, x < 256) (hcov : PartCov Js vs₀)
    (hsub : ∀ key ∈ nodeWindowKeys vs₀, key ∈ nodeWindowKeys vs)
    (q : UseRequests) (hq : q.windows = Candidates.PhysicalWindowRequests.keys (upsTraceAligned Js) t) :
    UpbBal (assignList q 0 vs) (viewOf (upsTraceAligned Js) t (segsOf Js)) := by
  apply upbBal_of_trace q vs _ t [] _ (ups_aligned_complete Js hok t []).2.1 hq
  · intro r hr
    have hr' := List.mem_filter.mp hr
    obtain ⟨_, _, _, _, _, _, _, _, hpk, hmem⟩ := read_info hw hb hcov t (List.mem_range.mp hr'.1)
      (by simpa using hr'.2)
    rw [hpk]; exact hsub _ hmem
  · intro r hr hrd
    obtain ⟨ha, i, k, p, hrow, -, -, -, hbit⟩ := aligned_read_row Js t r hr hrd
    rw [aligned_u Js t r hr ha hrow hbit, uU_rank hw hb hcov t hok.ok.cap hr hrd]

/-! ## Native coverage -/

/-- `PartCov` of allocated native instances (the part-level form of `native_window_coverage`). -/
theorem partCov_native (rs : List ReplayTree) (hv : ∀ r ∈ rs, r.Valid)
    (hw : ∀ r ∈ rs, r.pre.wf = true) (hbudget : preBytes (rs.map ReplayTree.post) ≤ 2000000)
    (us : List SchedulerUpsertWitness) (insts : List UpsInst)
    (hforest : us.map SchedulerUpsertWitness.pre = rs.map ReplayTree.post)
    (hgood : ∀ u ∈ us, u.Valid ∧ u.pre.wf = true)
    (hlen : insts.length = us.length)
    (halloc : ∀ tau u I, us[tau]? = some u → insts[tau]? = some I →
      AllocatedNativeInstance us tau u I ∧
      ∃ root, forestRootAt 0 0 (us.map SchedulerUpsertWitness.pre) tau = some root ∧
        NativeReaderOrigin root u.run u.value I) :
    PartCov insts (records (forestOldInputs rs) (initializeList 0 (forestNodes 0 0 0 (rs.map ReplayTree.pre)))) := by
  intro i k p hi hk hp hbit
  have hui : i < us.length := hlen ▸ hi
  have hu : us[i]? = some us[i] := List.getElem?_eq_getElem hui
  have hI : insts[i]? = some (inst insts i) := by
    simp [inst, List.getElem?_eq_getElem hi]
  obtain ⟨a, root, hroot, ho⟩ := halloc i _ _ hu hI
  have ht := forestRootAt_tree 0 0 (us.map SchedulerUpsertWitness.pre) i
  rw [hroot, List.getElem?_map, hu] at ht
  have heq : root.tree = (us[i]).pre := Option.some.inj ht
  obtain ⟨hv', hw'⟩ := hgood _ (List.getElem_mem hui)
  have hr' : traceUpsert root.tree [0, 15] us[i].value = some us[i].run := by
    simpa only [heq, keyBwState_nibbles] using hv'.1
  have hok : InstOk (inst insts i) := a.2.2.2.2.1
  have hfamily : NativePartFamily (inst insts i) := a.2.2.2.2.2.2.2
  have hroom := ho.room hr' (heq ▸ hw') k hk
  obtain ⟨⟨bytes⟩, hf, hplan, _⟩ := hfamily k hk
  have hg : rdV (inst insts i) (part (inst insts i) k) (fieldAt (part (inst insts i) k).shape p).1
      (fieldAt (part (inst insts i) k).shape p).2.1 (fieldAt (part (inst insts i) k).shape p).2.2.2 = 1 := by
    unfold rbit at hbit
    unfold rdV ind
    rw [if_pos hbit]
  obtain ⟨hkind, hpos, hlt⟩ := window_read_bounds hf bytes.sourceLayout hplan bytes.copyFields
    (hok.bits k hk).2.2.2 hroom hp hg
  exact ⟨hpos, ho.provider rs hv hw hbudget (hforest ▸ hroot) hr' k _ hk hkind hlt⟩

/-- The physical read keys are field-bounded window requests. -/
theorem keys_length (Js : List UpsInst) (t : Nat) :
    (Candidates.PhysicalWindowRequests.keys (upsTraceAligned Js) t).length < Algebra.P := by
  unfold Candidates.PhysicalWindowRequests.keys physicalWindowRows
  rw [List.length_map]
  have h1 := List.length_filter_le (fun r => decide ((upsTraceAligned Js).cell t r UpsV3.rd = 1))
    (List.range ((upsTraceAligned Js).height t))
  rw [List.length_range] at h1
  have h2 : (upsTraceAligned Js).height t ≤ 2 ^ 22 := by
    change 2 ^ ZkFormal.Size.padLog22 (ZkFormal.Near.Render.logOf (R Js + 1)) ≤ 2 ^ 22
    exact Nat.pow_le_pow_right (by decide) (by unfold ZkFormal.Size.padLog22; omega)
  have h3 : 2 ^ 22 < Algebra.P := by unfold Algebra.P; decide
  omega

/-! ## Bundle level -/

theorem covers_upb (s : Bool) : Covers B_UPB s (fun t => t == 2 || t == 7) = true := by
  cases s <;> decide +kernel
theorem pub_upb (s : Bool) (pub m : List Fp) : ZkFormal.V2.pubCount nearAirV3 pub B_UPB s m = 0 :=
  pub_off _ _ (by cases s <;> decide +kernel) pub m

namespace RenderBundleV3

variable {pub : List Fp} (R : RenderBundleV3 pub)

/-- **`UPB` balance of a bundle** from the record-level `UpbBal` of its node and (aligned) ups
components. -/
theorem balancedAt_upb (vs : List NodeS3) (Is : List UpsInst)
    (hn : ExtOf (R ⟨T_NODE, by decide⟩).tf (nodeTraffic3 vs))
    (hu : ExtOf (R ⟨T_UPS, by decide⟩).tf (upsTraffic (UpsRows.viewOf (upsTraceAligned Is) T_UPS (UpsGen.segsOf Is))))
    (hbal : UpbBal vs (UpsRows.viewOf (upsTraceAligned Is) T_UPS (UpsGen.segsOf Is))) :
    R.BalancedAt B_UPB := by
  intro m
  rw [R.sum_tables true _ m _ (covers_upb true), R.sum_tables false _ m _ (covers_upb false),
    pub_upb, pub_upb]
  have e2 := R.tf_ext 2 (by decide) hn B_UPB (by decide) (by decide) (by decide)
  have e7 := R.tf_ext 7 (by decide) hu B_UPB (by decide) (by decide) (by decide)
  have hf : (List.range 25).filter (fun t => t == 2 || t == 7) = [2, 7] := by decide
  rw [hf]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, e2.1, e2.2, e7.1, e7.2, sel,
    ite_true, Bool.false_eq_true, ite_false, nodeTraffic3]
  have hp := hbal.count_eq m
  simp only [List.map_append, List.count_append] at hp
  simp only [cnt]
  omega

end RenderBundleV3

end ZkFormal.NearV3.Assembly.TrieUpb
