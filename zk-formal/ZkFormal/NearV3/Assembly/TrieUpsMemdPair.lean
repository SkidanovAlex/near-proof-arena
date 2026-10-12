import ZkFormal.NearV3.Assembly.TrieUpsMemd
import ZkFormal.NearV3.Render.Ups.MemPosition

/-!
# ZkFormal.NearV3.Assembly.TrieUpsMemdPair — the per-instance `MEMD` pairing

Reduction of `MemdPair I` to the per-part native link `MemdLink I` (a receiving part's child
memory `mB` is the child part's exact memory scalar `RV`).

* `mem_field`: with `FieldsOk`, the `MEM` rows of a part are exactly `p = |q| − 8 + ix`, `ix < 8`;
* `part_msgs`: a part's `MEMD` messages (as field messages) are eight `memdS`/`memdR` messages when
  its gate holds, none otherwise;
-/

namespace ZkFormal.NearV3.Assembly.TrieUpsMemdPair

open ZkFormal.Near ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3 ZkFormal.NearV3.Assembly
  Render Render.UpsGen Render.UpsRelay UpsRows Rcpt.Candidates Rcpt.Candidates.NodePostUpdate
  TrieUpsMemd

set_option maxHeartbeats 1600000

/-! ## The `MEM` field rows -/

theorem mem_field {Q : UpsPartI} (ok : FieldsOk Q) (ix : Nat) (hix : ix < 8) :
    8 ≤ Q.q.length ∧ fieldAt Q.shape (Q.q.length - 8 + ix) = (8, ix, 8, nWin Q.shape) := by
  have he : Q.shape = nodeHeader Q.ty Q.qhk ++ (List.replicate (nWin Q.shape) (7,32) ++ [(8,8)]) := by
    rw [← nodeFields_eq_header]; exact ok.shape
  have hl : Q.q.length = fieldsLen (nodeHeader Q.ty Q.qhk) + (32*nWin Q.shape+8) := by
    calc Q.q.length = fieldsLen Q.shape := ok.bytes
      _ = fieldsLen (nodeHeader Q.ty Q.qhk ++ (List.replicate (nWin Q.shape) (7,32) ++ [(8,8)])) :=
          congrArg fieldsLen he
      _ = _ := by rw [fieldsLen_append, fieldsLen_windows]
  refine ⟨by omega, ?_⟩
  have hc := fieldAt_append_after (nodeHeader Q.ty Q.qhk)
    (List.replicate (nWin Q.shape) (7,32) ++ [(8,8)]) (Q.q.length - 8 + ix) (by omega)
  rw [← he, nodeHeader_nWin] at hc
  rw [fieldAt_after_windows _ _ (by omega) (by omega)] at hc
  rw [hc]
  have h1 : Q.q.length - 8 + ix - fieldsLen (nodeHeader Q.ty Q.qhk) - 32 * nWin Q.shape = ix := by omega
  simp only [h1, Nat.add_zero]

theorem not_mem_field {Q : UpsPartI} (ok : FieldsOk Q) {p : Nat} (hp : p < Q.q.length)
    (hlt : p + 8 < Q.q.length) : (fieldAt Q.shape p).1 ≠ 8 := by
  intro hs
  have := ok.mem_position hp hs
  omega

/-! ## Row messages -/

/-- A receiving part (`gMr`). -/
def RecvK (I : UpsInst) (Q : UpsPartI) : Prop :=
  (Q.kind = 0 ∨ Q.kind = 1 ∨ Q.kind = 9 ∨ Q.kind = 11) ∨
    (Q.kind = 10 ∧ (I.ci = 5 ∨ I.ci = 6 ∨ I.ci = 7 ∨ I.ci = 9))

instance (I : UpsInst) (Q : UpsPartI) : Decidable (RecvK I Q) := by unfold RecvK; infer_instance

/-- A sending part (`gMs`). -/
def SendK (I : UpsInst) (k : Nat) : Prop := k + 1 ≠ nQ I ∧ (part I k).kind ≠ 8

instance (I : UpsInst) (k : Nat) : Decidable (SendK I k) := by unfold SendK; infer_instance

/-- The sent message of `MEM` row `ix` of part `k`. -/
def mS (I : UpsInst) (k ix : Nat) : List Fp :=
  [((I.tau : Int) : Fp), (((k + 1 : Nat) : Int) : Fp), ((ix : Int) : Fp), ((limb (RV I (part I k)) ix : Int) : Fp),
    ((memRb (part I k) ix : Int) : Fp), (((part I k).q.length : Int) : Fp)]

/-- The received message of `MEM` row `ix` of part `k`. -/
def mR (I : UpsInst) (k ix : Nat) : List Fp :=
  [((I.tau : Int) : Fp), (((part I k).jm : Int) : Fp), ((ix : Int) : Fp),
    ((limb ((part I k).mB : Int) ix : Int) : Fp), ((memByte (child I (part I k)) ix : Int) : Fp),
    (((part I k).clen : Int) : Fp)]

theorem toFp_cells (C : URow) (xs : List Nat) :
    Msg.toFp (reduceMessage (xs.map C)) = (xs.map C).map Fp.ofNat := by
  simp only [Msg.toFp, reduceMessage, List.map_map, Function.comp_def, Fp.ofNat_toNat]

theorem ofNat_toNat_cast (z : Int) : Fp.ofNat ((z : Fp).toNat) = (z : Fp) := Fp.ofNat_toNat _

theorem cast_ind_one (q : Prop) [Decidable q] : (((ind q : Int)) : Fp) = 1 ↔ q := by
  unfold ind
  by_cases h : q
  · simp [h]; rfl
  · simp only [h, ite_false, iff_false]; decide

theorem row_mem (I : UpsInst) (k p ix n : Nat) (D : URow) (hfa : fieldAt (part I k).shape p = (8, ix, 8, n))
    (sd : Bool) :
    (uMsgs (instRow I (.q k p)) D B_MEMD sd).map Msg.toFp =
      if sd then (if SendK I k then [mS I k ix] else []) else (if RecvK I (part I k) then [mR I k ix] else []) := by
  rw [uMsgs_memd]
  have hcell : ∀ x, isSeg x = false → instRow I (.q k p) x = ((qCell I k p (UpsGen.uU [I] 0) x : Int) : Fp).toNat :=
    fun x hx => by simp [instRow, generatedRow, rowCell, hx, inst]
  have ht : instRow I (.q k p) UpsV3.tau = ((I.tau : Int) : Fp).toNat := by
    simp [instRow, generatedRow, rowCell, UpsV3.tau, isSeg, segCell, inst]
  have hq : ∀ x, isSeg x = false → isPC x = false →
      instRow I (.q k p) x = ((qRow I (part I k) k p 8 ix 8 n (UpsGen.uU [I] 0) x : Int) : Fp).toNat := by
    intro x hx hpc
    rw [hcell x hx]
    simp [qCell, hpc, qRowCell, hfa]
  have hpc : ∀ x, isSeg x = false → isPC x = true →
      instRow I (.q k p) x = ((pcCell I (part I k) k x : Int) : Fp).toNat := by
    intro x hx hpc
    rw [hcell x hx]
    simp [qCell, hpc]
  cases sd
  · simp only [Bool.false_eq_true, ite_false]
    rw [hq _ (by decide) (by decide)]
    simp only [qRow, UpsV3.gMr, ofNat_toNat_cast, cast_ind_one, true_and]
    by_cases hr : RecvK I (part I k)
    · rw [if_pos (by unfold RecvK at hr; exact hr), if_pos hr]
      simp only [List.map_cons, List.map_nil, TrieUpsSched.toFp_reduce, Msg.toFp, mR, ht,
        hpc UpsV3.jm (by decide) (by decide), hpc UpsV3.clen (by decide) (by decide),
        hq UpsV3.idx (by decide) (by decide), hq UpsV3.mBv (by decide) (by decide),
        hq UpsV3.mCv (by decide) (by decide), ofNat_toNat_cast]
      simp [qRow, pcCell, UpsV3.jm, UpsV3.clen, UpsV3.idx, UpsV3.mBv, UpsV3.mCv, Fp.ofNat_toNat, reduceMessage, TrieUpsSched.ofNat_mod_P]
    · rw [if_neg (by unfold RecvK at hr; exact hr), if_neg hr]
      rfl
  · simp only [ite_true]
    rw [hq _ (by decide) (by decide)]
    simp only [qRow, UpsV3.gMs, ofNat_toNat_cast, cast_ind_one, true_and]
    by_cases hr : SendK I k
    · rw [if_pos (by unfold SendK at hr; exact hr), if_pos hr]
      simp only [List.map_cons, List.map_nil, TrieUpsSched.toFp_reduce, Msg.toFp, mS, ht,
        hpc UpsV3.j (by decide) (by decide), hpc UpsV3.qlen (by decide) (by decide),
        hq UpsV3.idx (by decide) (by decide), hq UpsV3.rx (by decide) (by decide),
        hq UpsV3.rb (by decide) (by decide), ofNat_toNat_cast]
      simp [qRow, pcCell, UpsV3.j, UpsV3.qlen, UpsV3.idx, UpsV3.rx, UpsV3.rb, rbV, sposV, memRb, Fp.ofNat_toNat, reduceMessage, TrieUpsSched.ofNat_mod_P]
    · rw [if_neg (by unfold SendK at hr; exact hr), if_neg hr]
      rfl

theorem row_nomem (I : UpsInst) (k p : Nat) (D : URow) (hs : (fieldAt (part I k).shape p).1 ≠ 8) (sd : Bool) :
    uMsgs (instRow I (.q k p)) D B_MEMD sd = [] := by
  rw [uMsgs_memd]
  have hq : ∀ x, isSeg x = false → isPC x = false →
      instRow I (.q k p) x = ((qRowCell I k p (UpsGen.uU [I] 0) x : Int) : Fp).toNat := by
    intro x hx hpc
    simp [instRow, generatedRow, rowCell, hx, inst, qCell, hpc]
  have hg : ∀ x, x = UpsV3.gMs ∨ x = UpsV3.gMr → Fp.ofNat (instRow I (.q k p) x) ≠ 1 := by
    intro x hx
    rcases hx with rfl | rfl
    · rw [hq _ (by decide) (by decide)]
      simp only [qRowCell, qRow, UpsV3.gMs, Fp.ofNat_toNat]
      rw [ind_neg (by intro h; exact hs h.1)]; decide
    · rw [hq _ (by decide) (by decide)]
      simp only [qRowCell, qRow, UpsV3.gMr, Fp.ofNat_toNat]
      rw [ind_neg (by intro h; exact hs h.1)]; decide
  cases sd
  · simp only [Bool.false_eq_true, ite_false]
    rw [if_neg (hg _ (Or.inr rfl))]
  · simp only [ite_true]
    rw [if_neg (hg _ (Or.inl rfl))]

theorem row_w (I : UpsInst) (t : Nat) (D : URow) (sd : Bool) : uMsgs (instRow I (.w t)) D B_MEMD sd = [] := by
  rw [uMsgs_memd]
  cases sd <;> simp [instRow, generatedRow, rowCell, isSeg, wCell, UpsV3.gMs, UpsV3.gMr] <;> decide

theorem row_v (I : UpsInst) (t : Nat) (D : URow) (sd : Bool) : uMsgs (instRow I (.v t)) D B_MEMD sd = [] := by
  rw [uMsgs_memd]
  cases sd <;> simp [instRow, generatedRow, rowCell, isSeg, vCell, UpsV3.gMs, UpsV3.gMr] <;> decide

/-- The eight messages of a part on side `sd` (when its gate holds). -/
def partMsgs (I : UpsInst) (k : Nat) (sd : Bool) : List (List Fp) :=
  if sd then (if SendK I k then (List.range 8).map (mS I k) else [])
  else (if RecvK I (part I k) then (List.range 8).map (mR I k) else [])

theorem part_msgs (I : UpsInst) (k : Nat) (ok : FieldsOk (part I k)) (sd : Bool) :
    ((List.range (part I k).q.length).flatMap (fun p => uMsgs (instRow I (.q k p)) (fun _ => 0) B_MEMD sd)).map
      Msg.toFp = partMsgs I k sd := by
  obtain ⟨h8, -⟩ := mem_field ok 0 (by decide)
  have hsplit : List.range (part I k).q.length =
      List.range ((part I k).q.length - 8) ++ (List.range 8).map (fun ix => (part I k).q.length - 8 + ix) := by
    rw [show (part I k).q.length = ((part I k).q.length - 8) + 8 by omega, List.range_add]
    simp only [Nat.add_sub_cancel]
  rw [hsplit, List.flatMap_append, List.map_append]
  have h1 : (List.range ((part I k).q.length - 8)).flatMap
      (fun p => uMsgs (instRow I (.q k p)) (fun _ => 0) B_MEMD sd) = [] := by
    apply List.flatMap_eq_nil_iff.mpr
    intro p hp
    have hp' := List.mem_range.mp hp
    exact row_nomem I k p _ (not_mem_field ok (by omega) (by omega)) sd
  rw [h1, List.map_nil, List.nil_append, List.flatMap_map, List.map_flatMap]
  have h2 : ∀ ix ∈ List.range 8, (uMsgs (instRow I (.q k ((part I k).q.length - 8 + ix))) (fun _ => 0) B_MEMD sd).map
      Msg.toFp = if sd then (if SendK I k then [mS I k ix] else []) else
        (if RecvK I (part I k) then [mR I k ix] else []) := by
    intro ix hix
    exact row_mem I k _ ix _ _ (mem_field ok ix (List.mem_range.mp hix)).2 sd
  rw [UpsRows.flatMap_congr' h2]
  unfold partMsgs
  cases sd <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;> split <;>
    simp [List.map_eq_flatMap]

/-! ## The part plan: senders and receivers -/

def recvT (ci : Nat) (T : List UKind) (r : Nat) : Bool :=
  let x := (T.getD r .RLP).ix
  (x == 0 || x == 1 || x == 9 || x == 11) || (x == 10 && (ci == 5 || ci == 6 || ci == 7 || ci == 9))

def jmT (T : List UKind) (r : Nat) : Nat :=
  let x := (T.getD r .RLP).ix
  if x == 0 || x == 1 || x == 9 || x == 11 then r else 1

/-- The senders of the terminal receivers. -/
def planA (ci ti : Nat) : List Nat :=
  let T := termPlan (UCase.all.getD ci .LP) ti
  ((List.range T.length).filter (recvT ci T)).map (fun r => jmT T r - 1)

theorem plan_check1 : ∀ ci, ci < 11 → ∀ ti, ti < 3 →
    (planA ci ti ++ [nTof ci ti - 1]).Perm ((List.range (nTof ci ti)).filter
      (fun k => ((termPlan (UCase.all.getD ci .LP) ti).getD k .RLP).ix != 8)) := by decide

theorem plan_check0 : ∀ ci, ci < 11 → ∀ ti, ti < 3 →
    (planA ci ti).Perm ((List.range (nTof ci ti)).filter
      (fun k => k + 1 != nTof ci ti && ((termPlan (UCase.all.getD ci .LP) ti).getD k .RLP).ix != 8)) := by decide

theorem plan_pos : ∀ ci, ci < 11 → ∀ ti, ti < 3 → 1 ≤ nTof ci ti := by decide

theorem plan_jm : ∀ ci, ci < 11 → ∀ ti, ti < 3 → ∀ r, r < nTof ci ti →
    recvT ci (termPlan (UCase.all.getD ci .LP) ti) r = true →
      1 ≤ jmT (termPlan (UCase.all.getD ci .LP) ti) r := by decide

section
variable (I : UpsInst) (ho : InstOk I) (hp : ∀ k, k < nQ I → PartOk I k (part I k))
include ho hp

theorem recv_term {r : Nat} (hr : r < nTof I.ci I.ti) :
    decide (RecvK I (part I r)) = recvT I.ci (termPlan (UCase.all.getD I.ci .LP) I.ti) r := by
  have hk := (hp r (by rw [ho.nQ]; omega)).kindT hr
  rw [Bool.eq_iff_iff, decide_eq_true_iff]
  unfold RecvK recvT
  rw [hk]
  generalize ((termPlan (UCase.all.getD I.ci .LP) I.ti).getD r .RLP).ix = x
  by_cases h1 : x = 0 <;> by_cases h2 : x = 1 <;> by_cases h3 : x = 9 <;> by_cases h4 : x = 11 <;>
    by_cases h5 : x = 10 <;> simp_all [or_assoc]

theorem jm_term {r : Nat} (hr : r < nTof I.ci I.ti) (hR : RecvK I (part I r)) :
    (part I r).jm = jmT (termPlan (UCase.all.getD I.ci .LP) I.ti) r := by
  have hP := hp r (by rw [ho.nQ]; omega)
  have hk := hP.kindT hr
  unfold jmT
  rw [← hk]
  unfold RecvK at hR
  by_cases hd : (part I r).kind = 0 ∨ (part I r).kind = 1 ∨ (part I r).kind = 9 ∨ (part I r).kind = 11
  · rw [hP.jmD hd]
    have : ((part I r).kind == 0 || (part I r).kind == 1 || (part I r).kind == 9 || (part I r).kind == 11) = true := by
      rcases hd with h | h | h | h <;> simp [h]
    simp only [this, ite_true]
  · have hs := hR.resolve_left hd
    rw [hP.jmS hs.1 hs.2]
    have : ((part I r).kind == 0 || (part I r).kind == 1 || (part I r).kind == 9 || (part I r).kind == 11) = false := by
      simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne]; omega
    simp only [this, Bool.false_eq_true, ite_false]

theorem upper_kind {k : Nat} (h1 : nTof I.ci I.ti ≤ k) (h2 : k < nQ I) :
    (part I k).kind = 0 ∨ (part I k).kind = 1 ∨ (part I k).kind = 11 := (hp k h2).kindU h1

theorem upper_recv {k : Nat} (h1 : nTof I.ci I.ti ≤ k) (h2 : k < nQ I) :
    RecvK I (part I k) ∧ (part I k).jm = k := by
  have hu := upper_kind I ho hp h1 h2
  have hd : (part I k).kind = 0 ∨ (part I k).kind = 1 ∨ (part I k).kind = 9 ∨ (part I k).kind = 11 := by omega
  exact ⟨Or.inl hd, (hp k h2).jmD hd⟩

/-- **The receivers' children are exactly the senders** (as index lists, up to order). -/
theorem index_perm :
    (((List.range (nQ I)).filter (fun r => decide (RecvK I (part I r)))).map (fun r => (part I r).jm - 1)).Perm
      ((List.range (nQ I)).filter (fun k => decide (SendK I k))) := by
  have hn := ho.nQ
  have hci := ho.ci
  have hti : I.ti < 3 := ho.ti
  have hpos := plan_pos _ hci _ hti
  generalize hT : termPlan (UCase.all.getD I.ci .LP) I.ti = T at *
  generalize hd : I.dep.getD I.D 0 = d at hn
  have hnT : nTof I.ci I.ti = T.length := by rw [nTof, hT]
  rw [hn, List.range_add, List.filter_append, List.filter_append, List.map_append]
  -- terminal receivers
  have hA : ((List.range (nTof I.ci I.ti)).filter (fun r => decide (RecvK I (part I r)))).map
      (fun r => (part I r).jm - 1) = planA I.ci I.ti := by
    unfold planA
    dsimp only
    rw [hT, ← hnT]
    rw [List.filter_congr (fun r hr => recv_term I ho hp (List.mem_range.mp hr))]
    rw [hT]
    apply List.map_congr_left
    intro r hr
    have hr' := List.mem_filter.mp hr
    have hR : RecvK I (part I r) := by
      have := recv_term I ho hp (List.mem_range.mp hr'.1)
      rw [hT] at this
      rw [← this] at hr'
      exact of_decide_eq_true hr'.2
    rw [jm_term I ho hp (List.mem_range.mp hr'.1) hR, hT]
  rw [hA]
  -- upper receivers
  have hU : ((List.range d).map (nTof I.ci I.ti + ·)).filter (fun r => decide (RecvK I (part I r))) =
      (List.range d).map (nTof I.ci I.ti + ·) := by
    apply List.filter_eq_self.mpr
    intro r hr
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hr
    exact decide_eq_true (upper_recv I ho hp (by omega) (by rw [hn]; have := List.mem_range.mp hj; omega)).1
  rw [hU, List.map_map]
  have hUm : (List.range d).map ((fun r => (part I r).jm - 1) ∘ (nTof I.ci I.ti + ·)) =
      (List.range d).map (fun j => nTof I.ci I.ti + j - 1) := by
    apply List.map_congr_left
    intro j hj
    simp only [Function.comp_apply]
    rw [(upper_recv I ho hp (by omega) (by rw [hn]; have := List.mem_range.mp hj; omega)).2]
  rw [hUm]
  -- senders
  have hS1 : (List.range (nTof I.ci I.ti)).filter (fun k => decide (SendK I k)) =
      (List.range (nTof I.ci I.ti)).filter
        (fun k => k + 1 != nTof I.ci I.ti + d && (T.getD k .RLP).ix != 8) := by
    apply List.filter_congr
    intro k hk
    have hk' := List.mem_range.mp hk
    have hkind := (hp k (by rw [hn]; omega)).kindT hk'
    rw [hT] at hkind
    rw [Bool.eq_iff_iff, decide_eq_true_iff]
    unfold SendK
    rw [hkind, hn]
    simp
  have hS2 : ((List.range d).map (nTof I.ci I.ti + ·)).filter (fun k => decide (SendK I k)) =
      ((List.range d).filter (fun j => j + 1 != d)).map (nTof I.ci I.ti + ·) := by
    rw [List.filter_map]
    congr 1
    apply List.filter_congr
    intro j hj
    have hj' := List.mem_range.mp hj
    have hu := upper_kind I ho hp (k := nTof I.ci I.ti + j) (by omega) (by rw [hn]; omega)
    simp only [Function.comp_apply]
    rw [Bool.eq_iff_iff, decide_eq_true_iff]
    unfold SendK
    rw [hn]
    have : (part I (nTof I.ci I.ti + j)).kind ≠ 8 := by omega
    simp only [this, ne_eq, not_false_eq_true, and_true, bne_iff_ne]
    omega
  rw [hS1, hS2]
  cases d with
  | zero =>
    simp only [List.range_zero, List.map_nil, List.filter_nil, List.append_nil, Nat.add_zero]
    have := plan_check0 _ hci _ hti
    rw [hT] at this
    exact this
  | succ d =>
    have hfl : (List.range (d + 1)).filter (fun j => j + 1 != d + 1) = List.range d := by
      rw [List.range_succ, List.filter_append]
      simp only [List.filter_cons, List.filter_nil, bne_self_eq_false, Bool.false_eq_true, ite_false,
        List.append_nil]
      apply List.filter_eq_self.mpr
      intro j hj
      have := List.mem_range.mp hj
      simp; omega
    rw [hfl]
    have hm : (List.range (d + 1)).map (fun j => nTof I.ci I.ti + j - 1) =
        [nTof I.ci I.ti - 1] ++ (List.range d).map (nTof I.ci I.ti + ·) := by
      rw [List.range_succ_eq_map, List.map_cons, List.map_map]
      simp only [Nat.add_zero, List.singleton_append, List.cons.injEq, true_and]
      apply List.map_congr_left
      intro j _
      simp only [Function.comp_apply]
      omega
    rw [hm, ← List.append_assoc]
    apply List.Perm.append_right
    have hc := plan_check1 _ hci _ hti
    rw [hT] at hc
    have hfilt : (List.range (nTof I.ci I.ti)).filter
        (fun k => k + 1 != nTof I.ci I.ti + (d + 1) && (T.getD k .RLP).ix != 8) =
        (List.range (nTof I.ci I.ti)).filter (fun k => (T.getD k .RLP).ix != 8) := by
      apply List.filter_congr
      intro k hk
      have := List.mem_range.mp hk
      have : (k + 1 != nTof I.ci I.ti + (d + 1)) = true := by simp; omega
      simp [this]
    rw [hfilt]
    exact hc

end

/-! ## The instance -/

theorem memd_parts (I : UpsInst) (hf : ∀ k, k < nQ I → FieldsOk (part I k)) (sd : Bool) :
    (memdI I sd).map Msg.toFp = (List.range (nQ I)).flatMap (fun k => partMsgs I k sd) := by
  unfold memdI recsI
  simp only [List.flatMap_append, List.flatMap_map, List.map_append, row_w, row_v,
    List.map_nil, List.nil_append, List.flatMap_assoc, List.map_flatMap]
  have h0 : ∀ n, (List.range n).flatMap (fun _ => ([] : List (List Fp))) = [] := fun n =>
    List.flatMap_eq_nil_iff.mpr (fun _ _ => rfl)
  rw [h0, h0, List.nil_append, List.nil_append]
  apply UpsRows.flatMap_congr'
  intro k hk
  rw [← part_msgs I k (hf k (List.mem_range.mp hk)) sd, List.map_flatMap]

theorem flat_if {α β : Type} (l : List α) (p : α → Bool) (f : α → List β) :
    l.flatMap (fun a => if p a then f a else []) = (l.filter p).flatMap f := by
  induction l with
  | nil => rfl
  | cons a l ih => cases h : p a <;> simp [List.filter_cons, h, ih]

/-- **The native per-part `MEMD` link** (open, native side): a receiving part's child memory is
the child part's exact memory scalar. -/
def MemdLink (I : UpsInst) : Prop :=
  ∀ k, k < nQ I → RecvK I (part I k) → ((part I k).mB : Int) = RV I (child I (part I k))

theorem jm_pos (I : UpsInst) (ho : InstOk I) (hp : ∀ k, k < nQ I → PartOk I k (part I k)) {r : Nat}
    (hr : r < nQ I) (hR : RecvK I (part I r)) : 1 ≤ (part I r).jm := by
  by_cases ht : r < nTof I.ci I.ti
  · rw [jm_term I ho hp ht hR]
    have h := recv_term I ho hp ht
    rw [decide_eq_true hR] at h
    exact plan_jm _ ho.ci _ ho.ti r ht h.symm
  · rw [(upper_recv I ho hp (by omega) hr).2]
    have := plan_pos _ ho.ci _ ho.ti
    omega

/-- **`MemdPair` from the native per-part link.** -/
theorem memdPair_of (I : UpsInst) (ho : InstOk I) (hfam : NativePartFamily I)
    (hroom : ∀ k, k < nQ I → 8 ≤ (part I k).pb.length) (hlink : MemdLink I) : MemdPair I := by
  have hf : ∀ k, k < nQ I → FieldsOk (part I k) := fun k hk => (hfam k hk).2.1
  have hp : ∀ k, k < nQ I → PartOk I k (part I k) := fun k hk => (hfam k hk).2.2.1
  unfold MemdPair
  rw [memd_parts I hf true, memd_parts I hf false]
  have hR : (List.range (nQ I)).flatMap (fun r => partMsgs I r false) =
      (List.range (nQ I)).flatMap (fun r => if decide (RecvK I (part I r)) then
        (List.range 8).map (mS I ((part I r).jm - 1)) else []) := by
    apply UpsRows.flatMap_congr'
    intro r hr
    have hr' := List.mem_range.mp hr
    unfold partMsgs
    simp only [Bool.false_eq_true, ite_false]
    by_cases hRk : RecvK I (part I r)
    · rw [if_pos hRk, if_pos (decide_eq_true hRk)]
      apply List.map_congr_left
      intro ix hix
      have hpos := jm_pos I ho hp hr' hRk
      have hj := (hfam r hr').2.2.2.2.2.1
      have hcl := (hfam r hr').2.2.2.2.2.2
      have hch : child I (part I r) = part I ((part I r).jm - 1) := rfl
      have hmb := hlink r hr' hRk
      have hm8 := hroom _ hj
      unfold mR mS
      rw [hcl, hmb, hch, memByte_eq_memRb _ hm8,
        show (part I r).jm = (part I r).jm - 1 + 1 by omega]
      simp
    · rw [if_neg hRk, if_neg (by simpa using hRk)]
  have hS : (List.range (nQ I)).flatMap (fun k => partMsgs I k true) =
      (List.range (nQ I)).flatMap (fun k => if decide (SendK I k) then (List.range 8).map (mS I k) else []) := by
    apply UpsRows.flatMap_congr'
    intro k _
    unfold partMsgs
    by_cases hs : SendK I k
    · simp [hs]
    · simp [hs]
  rw [hR, hS, flat_if, flat_if, ← List.flatMap_map (f := fun r => (part I r).jm - 1)
    (g := fun k => (List.range 8).map (mS I k))]
  exact ((index_perm I ho hp).flatMap_right _).symm

end ZkFormal.NearV3.Assembly.TrieUpsMemdPair
