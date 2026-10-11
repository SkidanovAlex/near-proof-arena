import ZkFormal.NearV3.Rcpt.Link.QvPre
import ZkFormal.NearV3.Qv.Extract.NativeQueueAssembly
import ZkFormal.NearV3.Candidates.ProcessRepairQueuePublic

/-!
# ZkFormal.NearV3.Rcpt.Link.QvBal — the `KEYNIB` / `FINAL` premises of the qv assembly from `HoldsP`

In `nearAirV3` the buses `KEYNIB` and `FINAL` are used by walk (5), rcpt (16) and qv (22) only, and
no public segment uses them.  `KEYNIB`: qv and rcpt send, walk receives; `FINAL`: walk sends, rcpt
and qv receive.  The exact balances give the permutations `hkey` / `hfinal` of
`Qv.Extract.assemble_native_queue_reads` (with `others` = rcpt's `FINAL` receives).
-/

namespace ZkFormal.NearV3.RcptLink

open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near ZkFormal.Near.Link
  ZkFormal.NearV3.Assembly

/-- The raw qv rows' traffic on bus `b`, side `s`. -/
def qvRows (tr : Trace Fp) (pub : List Fp) (b : Nat) (s : Bool) : List (List Fp) :=
  (List.range (tr.height T_QV)).flatMap fun x =>
    rowTraffic Qv.Candidates.KeyTrafficRepair.interactions tr T_QV x pub b s

theorem qv_count (tr : Trace Fp) (pub : List Fp) (b : Nat) (s : Bool) (m : List Fp) :
    tableBusCount (isAt T_QV) tr T_QV pub b s m = (qvRows tr pub b s).count m :=
  tableBusCount_eq _ _ _ _ _ _ _

theorem qvRows_nil {tr : Trace Fp} {pub : List Fp} {b : Nat} {s : Bool}
    (h : Qv.Candidates.KeyTrafficRepair.interactions.all (fun i => !(i.bus == b && i.send == s)) = true) :
    qvRows tr pub b s = [] := by
  unfold qvRows
  apply List.flatMap_eq_nil_iff.mpr
  intro x _
  unfold rowTraffic
  apply List.flatMap_eq_nil_iff.mpr
  intro i hi
  have := List.all_eq_true.mp h i hi
  simp only [Bool.not_eq_true', Bool.and_eq_false_iff, beq_eq_false_iff_ne] at this
  rw [if_neg (by rintro ⟨h1, h2⟩; rcases this with h | h <;> contradiction)]

/-- **`hkey`**: qv and rcpt `KEYNIB` sends are a permutation of the walks' receives. -/
theorem qv_hkey {pub : List Fp} {tr : Trace Fp} {r : V3Records} (hH : HoldsP nearAirV3 pub tr)
    (T : V3RecordsTraffic pub tr r) :
    (qvRows tr pub B_KEYNIB true ++ (rcptSends3 pub r.lists B_KEYNIB).map Msg.toFp).Perm
      ((walkRecvs3 r.walks B_KEYNIB).map Msg.toFp) := by
  apply List.perm_iff_count.mpr
  intro m
  have h := bal_users hH (b := B_KEYNIB) (U := [Assembly.T_WALK, Assembly.T_RCPT, T_QV]) (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) m
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero] at h
  rw [show isAt Assembly.T_WALK = WalkV3.interactions from rfl, tcnt_of_traffic T.walks, tcnt_of_traffic T.walks,
    show isAt Assembly.T_RCPT = RcptV3.interactions from rfl, tcnt_of_traffic T.lists,
    tcnt_of_traffic T.lists, qv_count, qv_count,
    qvRows_nil (b := B_KEYNIB) (s := false) (by decide +kernel)] at h
  simp only [tcnt, ite_true, Bool.false_eq_true, ite_false, walkTraffic3, rcptTraffic3] at h
  have w0 : walkSends3 r.walks B_KEYNIB = [] := by simp [walkSends3, B_EDGE, B_BMAP, B_FINAL, B_KEYNIB]
  have r0 : rcptRecvs3 r.lists B_KEYNIB = [] := by
    simp [rcptRecvs3, rRecvs, B_DIGEST, B_FINAL, B_MEM, B_SREC, B_AKC, B_BND, B_KEYNIB]
  rw [w0, r0] at h
  simp only [List.map_nil, List.count_nil, Nat.zero_add, Nat.add_zero] at h
  rw [List.count_append]
  omega

/-- **`hfinal`**: the walks' `FINAL` sends are a permutation of the qv and rcpt receives. -/
theorem qv_hfinal {pub : List Fp} {tr : Trace Fp} {r : V3Records} (hH : HoldsP nearAirV3 pub tr)
    (T : V3RecordsTraffic pub tr r) :
    ((walkSends3 r.walks B_FINAL).map Msg.toFp).Perm
      (qvRows tr pub B_FINAL false ++ (rcptRecvs3 r.lists B_FINAL).map Msg.toFp) := by
  apply List.perm_iff_count.mpr
  intro m
  have h := bal_users hH (b := B_FINAL) (U := [Assembly.T_WALK, Assembly.T_RCPT, T_QV]) (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) m
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero] at h
  rw [show isAt Assembly.T_WALK = WalkV3.interactions from rfl, tcnt_of_traffic T.walks, tcnt_of_traffic T.walks,
    show isAt Assembly.T_RCPT = RcptV3.interactions from rfl, tcnt_of_traffic T.lists,
    tcnt_of_traffic T.lists, qv_count, qv_count,
    qvRows_nil (b := B_FINAL) (s := true) (by decide +kernel)] at h
  simp only [tcnt, ite_true, Bool.false_eq_true, ite_false, walkTraffic3, rcptTraffic3] at h
  have w0 : walkRecvs3 r.walks B_FINAL = [] := by simp [walkRecvs3, B_EDGE, B_BMAP, B_FINAL, B_KEYNIB]
  have r0 : rcptSends3 pub r.lists B_FINAL = [] := by
    simp [rcptSends3, rSends, B_BYTES, B_RCL, B_KEYNIB, B_MEM, B_RIDS, B_MPOS, B_SREC, B_AKC, B_BND, B_FINAL]
  rw [w0, r0] at h
  simp only [List.map_nil, List.count_nil, Nat.zero_add, Nat.add_zero] at h
  rw [List.count_append]
  omega

/-- **`hK`**: the public implicit-block count is `< 64` (`ProcessRepairQueuePublic.queue_count`). -/
theorem qv_hK {cb : NearSpec.Bytes} {h : NearSpecV3.Hint} {p : NearSpecV3.Prep}
    (hp : NearSpecV3.prepD0 cb h = .ok p) (oh : Nat) (tr : Trace Fp) (tt r : Nat) :
    (Qv.Candidates.CombinedTable.kPublic.eval tr tt r
      (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh))).toNat < 64 := by
  obtain ⟨h1, h2⟩ := Candidates.ProcessRepairQueuePublic.queue_count hp oh tr tt r
  rw [h1]; exact h2

end ZkFormal.NearV3.RcptLink
