import ZkFormal.NearV3.Assembly.LinkV3
import ZkFormal.NearV3.Extract.Ups.UpsWalk
import ZkFormal.NearV3.Extract.Ups.UpsReads
import ZkFormal.NearV3.Link.PerTau3

/-!
# ZkFormal.NearV3.Assembly.LinkBus — per-bus balances of `nearAirV3` from `HoldsP`

`HoldsP.balance` is one equation per bus over all 25 tables and the public segments.  For the
link only the tables that actually touch a bus matter:

* `busCount_users` — `busCount nearAirV3` on bus `b` is the sum over an explicit list `U` of
  table indices, given the kernel-checked fact `UsersOk b U` (every other table has no
  interaction on `b`);
* `pubCount_nobus` — no prepared public segment on `b` ⇒ public count `0`;
* `bal_users` — so on a private bus the sends of the users equal their receives.

Instantiated with the exact traffic of the viewed tables (`V3RecordsTraffic`), this gives the
record-level balances the `Link/` layer is stated against:

* `parentBal_of` (`ParentBal`, bus `PARENT`: node, head),
* `vparentBal_of` (`VParentBal`, `VPARENT`: node, val),
* `entBal_of` (`EntBal`, `ENT`: node, val),
* `dupBal_of` (`DupBal`, `DUP`: node, val, uniq),
* `digsBal_of` (`DigsBal`, `DIGS`: node, head, uniq),
* `walkBal_of` (`WalkBal … B_EDGE` / `B_BMAP`: node, head, walk, ups),
* `upbBal_of` (`UpbBal`, `UPB`: node, ups).

The A7 extension interactions of `nodeA7`/`valA7`/`upsA7`/`sizeA7` use only `RPL`, `RPLV` and
`SIZE`, so they drop out of every bus above (`a7_nobus`).
-/

namespace ZkFormal.NearV3.Assembly

open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near

/-! ## Generic: the users of a bus -/

theorem sum_map_range_users (n : Nat) (g : Nat → Nat) (U : List Nat) (hU : U.Nodup)
    (hUn : ∀ t ∈ U, t < n) (hz : ∀ t, t < n → t ∉ U → g t = 0) :
    ((List.range n).map g).sum = (U.map g).sum := by
  have hp : ((List.range n).filter (fun t => decide (t ∈ U))).Perm U := by
    apply (List.perm_ext_iff_of_nodup (List.nodup_range.sublist (List.filter_sublist)) hU).mpr
    intro t
    simp only [List.mem_filter, List.mem_range, decide_eq_true_eq]
    exact ⟨fun h => h.2, fun h => ⟨hUn t h, h⟩⟩
  have hs := ((List.filter_append_perm (fun t => decide (t ∈ U)) (List.range n)).map g).sum_nat
  rw [← hs, List.map_append, List.sum_append, (hp.map g).sum_nat]
  have h0 : (((List.range n).filter (fun t => !decide (t ∈ U))).map g).sum = 0 := by
    apply nat_sum_eq_zero
    intro x hx
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hx
    simp only [List.mem_filter, List.mem_range, Bool.not_eq_true', decide_eq_false_iff_not] at ht
    exact hz t ht.1 ht.2
  omega

theorem mapIdx_eq_range {α β : Type} (l : List α) (f : Nat → α → β) (d : α) :
    l.mapIdx f = (List.range l.length).map fun t => f t (l.getD t d) := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.getElem_mapIdx, List.getElem_map, List.getElem_range]
  congr 1
  simp only [List.length_mapIdx] at h1
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1, Option.getD_some]

/-- `U` lists every table of `nearAirV3` with an interaction on bus `b` (kernel-checkable). -/
def UsersOk (b : Nat) (U : List Nat) : Bool :=
  (List.range nearTablesFull.length).all fun t =>
    U.contains t || (nearTablesFull.getD t default).interactions.all fun i => i.bus != b

/-- The interactions of table `t` of `nearAirV3`. -/
def isAt (t : Nat) : List Interaction := (nearTablesFull.getD t default).interactions

/-- **`busCount` on bus `b` is the sum over its users.** -/
theorem busCount_users {b : Nat} {U : List Nat} (hU : U.Nodup) (hUn : ∀ t ∈ U, t < 25)
    (hok : UsersOk b U = true) (tr : Trace Fp) (pub : List Fp) (s : Bool) (m : List Fp) :
    busCount nearAirV3.toAir tr pub b s m =
      (U.map fun t => tableBusCount (isAt t) tr t pub b s m).sum := by
  rw [busCount_nearAirV3, mapIdx_eq_range _ _ default]
  apply sum_map_range_users _ _ _ hU (fun t ht => hUn t ht)
  intro t ht htU
  apply tableBusCount_nobus
  intro i hi
  have h := List.all_eq_true.mp hok t (List.mem_range.mpr ht)
  have hc : U.contains t = false := by
    cases hct : U.contains t
    · rfl
    · exact absurd (List.contains_iff_mem.mp hct) htU
  rw [hc, Bool.false_or] at h
  have := List.all_eq_true.mp h i hi
  simpa using this

/-- No prepared public segment on bus `b`: public count `0`. -/
theorem pubCount_nobus {b : Nat}
    (hb : ZkFormal.NearV3.Public.preparedSegments.all (fun s => s.bus != b) = true)
    (pub : List Fp) (sd : Bool) (msg : List Fp) : pubCount nearAirV3 pub b sd msg = 0 := by
  unfold pubCount
  suffices ((pubMsgs nearAirV3 pub).filter (fun x => decide (x = (b, sd, msg)))) = [] by
    rw [this]; rfl
  apply List.filter_eq_nil_iff.mpr
  intro x hx
  have hn : x ≠ (b, sd, msg) := by
    intro he
    subst x
    simp only [pubMsgs, List.mem_flatMap, List.mem_map] at hx
    obtain ⟨s, hseg, m, -, he⟩ := hx
    have hsb := congrArg (fun x : Nat × Bool × List Fp => x.1) he
    have := List.all_eq_true.mp hb s hseg
    simp only at hsb
    simp [hsb] at this
  simpa using hn

/-- **Balance on a private bus** (no public segment): the users' sends equal their receives. -/
theorem bal_users {pub : List Fp} {tr : Trace Fp} (hH : HoldsP nearAirV3 pub tr) {b : Nat}
    {U : List Nat} (hU : U.Nodup) (hUn : ∀ t ∈ U, t < 25) (hok : UsersOk b U = true)
    (hpb : ZkFormal.NearV3.Public.preparedSegments.all (fun s => s.bus != b) = true)
    (m : List Fp) :
    (U.map fun t => tableBusCount (isAt t) tr t pub b true m).sum =
      (U.map fun t => tableBusCount (isAt t) tr t pub b false m).sum := by
  have h := hH.balance b m
  rw [pubCount_nobus hpb, pubCount_nobus hpb, busCount_users hU hUn hok,
    busCount_users hU hUn hok] at h
  simpa using h

/-! ## The viewed tables' counts at their indices -/

theorem nobus_of_all {is : List Interaction} {b : Nat} (h : is.all (fun i => i.bus != b) = true) :
    ∀ i ∈ is, i.bus ≠ b := by
  intro i hi; have := List.all_eq_true.mp h i hi; simpa using this

section Counts
variable {pub : List Fp} {tr : Trace Fp} {r : V3Records} (T : V3RecordsTraffic pub tr r)
  (s : Bool) (b : Nat) (m : List Fp)
include T

theorem node_count (hb : ZkFormal.NearV3.UnfoldA7.Node.interactions.all (fun i => i.bus != b) = true) :
    tableBusCount (isAt T_NODE) tr T_NODE pub b s m = tcnt (ZkFormal.NearV3.nodeTraffic3 r.nodes) s b m := by
  rw [show isAt T_NODE = ZkFormal.NearV3.NodeV3.interactions ++ ZkFormal.NearV3.UnfoldA7.Node.interactions
    from rfl, tableBusCount_append, tableBusCount_nobus (nobus_of_all hb), tcnt_of_traffic T.nodes, Nat.add_zero]

theorem val_count (hb : ZkFormal.NearV3.UnfoldA7.Val.interactions.all (fun i => i.bus != b) = true) :
    tableBusCount (isAt T_VAL) tr T_VAL pub b s m = tcnt (ZkFormal.NearV3.valTraffic r.values) s b m := by
  rw [show isAt T_VAL = ZkFormal.NearV3.ValV3.interactions ++ ZkFormal.NearV3.UnfoldA7.Val.interactions
    from rfl, tableBusCount_append, tableBusCount_nobus (nobus_of_all hb), tcnt_of_traffic T.values, Nat.add_zero]

theorem ups_count (hb : ZkFormal.NearV3.UnfoldA7.Ups.interactions.all (fun i => i.bus != b) = true) :
    tableBusCount (isAt T_UPS) tr T_UPS pub b s m = tcnt (ZkFormal.NearV3.upsTraffic r.ups) s b m := by
  rw [show isAt T_UPS = ZkFormal.NearV3.UpsV3.interactions ++ ZkFormal.NearV3.UnfoldA7.Ups.interactions
    from rfl, tableBusCount_append, tableBusCount_nobus (nobus_of_all hb), tcnt_of_traffic T.ups, Nat.add_zero]

theorem size_count (hb : ZkFormal.NearV3.UnfoldA7.Size.interactions.all (fun i => i.bus != b) = true) :
    tableBusCount (isAt T_SIZE) tr T_SIZE pub b s m = tcnt (ZkFormal.NearV3.sizeTraffic r.size) s b m := by
  rw [show isAt T_SIZE = ZkFormal.NearV3.SizeV3.interactions ++ ZkFormal.NearV3.UnfoldA7.Size.interactions
    from rfl, tableBusCount_append, tableBusCount_nobus (nobus_of_all hb), tcnt_of_traffic T.size, Nat.add_zero]

theorem head_count : tableBusCount (isAt T_HEAD) tr T_HEAD pub b s m = tcnt (ZkFormal.NearV3.headTraffic r.heads) s b m :=
  tcnt_of_traffic T.heads s b m

theorem walk_count : tableBusCount (isAt T_WALK) tr T_WALK pub b s m = tcnt (ZkFormal.NearV3.walkTraffic3 r.walks) s b m :=
  tcnt_of_traffic T.walks s b m

theorem uniq_count : tableBusCount (isAt T_UNIQ) tr T_UNIQ pub b s m = tcnt (ZkFormal.NearV3.uniqTraffic r.uniq) s b m :=
  tcnt_of_traffic T.uniq s b m

end Counts

/-! ## Count algebra -/

theorem tcnt_sends (tf : Traffic) (b : Nat) (m : List Fp) :
    tcnt tf true b m = ((tf.sends b).map Msg.toFp).count m := rfl

theorem tcnt_recvs (tf : Traffic) (b : Nat) (m : List Fp) :
    tcnt tf false b m = ((tf.recvs b).map Msg.toFp).count m := rfl

theorem count_map_append (a c : List Msg) (m : List Fp) :
    ((a ++ c).map Msg.toFp).count m = (a.map Msg.toFp).count m + (c.map Msg.toFp).count m := by
  rw [List.map_append, List.count_append]

theorem count_nil_map (m : List Fp) : (([] : List Msg).map Msg.toFp).count m = 0 := rfl

/-! ## The trie buses -/

section Trie
variable {pub : List Fp} {tr : Trace Fp} {r : V3Records}

/-- **`PARENT`**: node sends + head sends = node receives. -/
theorem parentBal_of (hH : HoldsP nearAirV3 pub tr) (T : V3RecordsTraffic pub tr r) :
    ZkFormal.NearV3.Link3.ParentBal r.nodes r.heads := by
  intro m
  have h := bal_users hH (b := B_PARENT) (U := [T_NODE, T_HEAD]) (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) m
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero] at h
  rw [node_count T _ _ _ (by decide +kernel), node_count T _ _ _ (by decide +kernel),
    head_count T, head_count T] at h
  unfold ZkFormal.NearV3.Link3.cnt3
  rw [count_map_append]
  have h0 : tcnt (ZkFormal.NearV3.headTraffic r.heads) false B_PARENT m = 0 := by
    simp [tcnt, ZkFormal.NearV3.headTraffic, ZkFormal.NearV3.headRecvs, B_PARENT, B_DIGEST,
      ZkFormal.NearV3.B_ROOT, B_EDGE]
  rw [h0] at h
  exact h

/-- **`VPARENT`**: node sends = value receives. -/
theorem vparentBal_of (hH : HoldsP nearAirV3 pub tr) (T : V3RecordsTraffic pub tr r) :
    ZkFormal.NearV3.Link3.VParentBal r.nodes r.values := by
  intro m
  have h := bal_users hH (b := ZkFormal.NearV3.B_VPARENT) (U := [T_NODE, T_VAL]) (by decide)
    (by decide) (by decide +kernel) (by decide +kernel) m
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero] at h
  rw [node_count T _ _ _ (by decide +kernel), node_count T _ _ _ (by decide +kernel),
    val_count T _ _ _ (by decide +kernel), val_count T _ _ _ (by decide +kernel)] at h
  have h1 : tcnt (ZkFormal.NearV3.valTraffic r.values) true ZkFormal.NearV3.B_VPARENT m = 0 := by
    simp [tcnt, ZkFormal.NearV3.valTraffic, ZkFormal.NearV3.valSends, ZkFormal.NearV3.B_VPARENT,
      B_BYTES, ZkFormal.NearV3.B_SIZE, ZkFormal.NearV3.B_ENT]
  have h2 : tcnt (ZkFormal.NearV3.nodeTraffic3 r.nodes) false ZkFormal.NearV3.B_VPARENT m = 0 := by
    simp [tcnt, ZkFormal.NearV3.nodeTraffic3, ZkFormal.NearV3.nodeRecvs3, ZkFormal.NearV3.B_VPARENT,
      B_DIGEST, B_PARENT, B_EDGE, ZkFormal.NearV3.B_BMAP, ZkFormal.NearV3.B_DUP, ZkFormal.NearV3.B_ENT,
      ZkFormal.NearV3.B_UPB, B_VSLOT]
  rw [h1, h2, Nat.add_zero, Nat.zero_add] at h
  exact h

/-- Unfold the viewed tables' `tcnt` into counts of their send / receive lists. -/
theorem tcnt_unfold :
    (∀ vs b m, tcnt (ZkFormal.NearV3.nodeTraffic3 vs) true b m = ((ZkFormal.NearV3.nodeSends3 vs b).map Msg.toFp).count m) ∧
    (∀ vs b m, tcnt (ZkFormal.NearV3.nodeTraffic3 vs) false b m = ((ZkFormal.NearV3.nodeRecvs3 vs b).map Msg.toFp).count m) ∧
    (∀ hs b m, tcnt (ZkFormal.NearV3.headTraffic hs) true b m = ((ZkFormal.NearV3.headSends hs b).map Msg.toFp).count m) ∧
    (∀ hs b m, tcnt (ZkFormal.NearV3.headTraffic hs) false b m = ((ZkFormal.NearV3.headRecvs hs b).map Msg.toFp).count m) ∧
    (∀ es b m, tcnt (ZkFormal.NearV3.valTraffic es) true b m = ((ZkFormal.NearV3.valSends es b).map Msg.toFp).count m) ∧
    (∀ es b m, tcnt (ZkFormal.NearV3.valTraffic es) false b m = ((ZkFormal.NearV3.valRecvs es b).map Msg.toFp).count m) ∧
    (∀ us b m, tcnt (ZkFormal.NearV3.uniqTraffic us) true b m = ((ZkFormal.NearV3.uniqSends us b).map Msg.toFp).count m) ∧
    (∀ us b m, tcnt (ZkFormal.NearV3.uniqTraffic us) false b m = ((ZkFormal.NearV3.uniqRecvs us b).map Msg.toFp).count m) ∧
    (∀ ws b m, tcnt (ZkFormal.NearV3.walkTraffic3 ws) true b m = ((ZkFormal.NearV3.walkSends3 ws b).map Msg.toFp).count m) ∧
    (∀ ws b m, tcnt (ZkFormal.NearV3.walkTraffic3 ws) false b m = ((ZkFormal.NearV3.walkRecvs3 ws b).map Msg.toFp).count m) ∧
    (∀ v b m, tcnt (ZkFormal.NearV3.upsTraffic v) true b m = (((ZkFormal.NearV3.upsTraffic v).sends b).map Msg.toFp).count m) ∧
    (∀ v b m, tcnt (ZkFormal.NearV3.upsTraffic v) false b m = (((ZkFormal.NearV3.upsTraffic v).recvs b).map Msg.toFp).count m) :=
  ⟨fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl,
   fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl,
   fun _ _ _ => rfl, fun _ _ _ => rfl⟩

/-- **`ENT`**: node + value sends = node + value receives. -/
theorem entBal_of (hH : HoldsP nearAirV3 pub tr) (T : V3RecordsTraffic pub tr r) :
    ZkFormal.NearV3.Link3.EntBal r.nodes r.values := by
  apply List.perm_iff_count.mpr
  intro m
  have h := bal_users hH (b := ZkFormal.NearV3.B_ENT) (U := [T_NODE, T_VAL]) (by decide)
    (by decide) (by decide +kernel) (by decide +kernel) m
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero] at h
  rw [node_count T _ _ _ (by decide +kernel), node_count T _ _ _ (by decide +kernel),
    val_count T _ _ _ (by decide +kernel), val_count T _ _ _ (by decide +kernel)] at h
  simp only [tcnt_unfold] at h
  rw [count_map_append, count_map_append]
  omega

/-- **`DUP`**: uniq sends = node + value receives. -/
theorem dupBal_of (hH : HoldsP nearAirV3 pub tr) (T : V3RecordsTraffic pub tr r) :
    ZkFormal.NearV3.Link3.DupBal r.uniq r.nodes r.values := by
  apply List.perm_iff_count.mpr
  intro m
  have h := bal_users hH (b := ZkFormal.NearV3.B_DUP) (U := [T_NODE, T_VAL, T_UNIQ]) (by decide)
    (by decide) (by decide +kernel) (by decide +kernel) m
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero] at h
  rw [node_count T _ _ _ (by decide +kernel), node_count T _ _ _ (by decide +kernel),
    val_count T _ _ _ (by decide +kernel), val_count T _ _ _ (by decide +kernel),
    uniq_count T, uniq_count T] at h
  simp only [tcnt_unfold] at h
  have z1 : ZkFormal.NearV3.nodeSends3 r.nodes ZkFormal.NearV3.B_DUP = [] := by
    simp [ZkFormal.NearV3.nodeSends3, ZkFormal.NearV3.B_DUP, B_BYTES, B_PARENT, ZkFormal.NearV3.B_VPARENT,
      B_EDGE, ZkFormal.NearV3.B_BMAP, ZkFormal.NearV3.B_DIGS, ZkFormal.NearV3.B_ENT, ZkFormal.NearV3.B_SIZE,
      ZkFormal.NearV3.B_UPB]
  have z2 : ZkFormal.NearV3.valSends r.values ZkFormal.NearV3.B_DUP = [] := by
    simp [ZkFormal.NearV3.valSends, ZkFormal.NearV3.B_DUP, B_BYTES, ZkFormal.NearV3.B_ENT, ZkFormal.NearV3.B_SIZE]
  have z3 : ZkFormal.NearV3.uniqRecvs r.uniq ZkFormal.NearV3.B_DUP = [] := by
    simp [ZkFormal.NearV3.uniqRecvs, ZkFormal.NearV3.B_DUP, ZkFormal.NearV3.B_DIGS]
  rw [z1, z2, z3] at h
  simp only [count_nil_map] at h
  rw [count_map_append]
  omega

/-- **`DIGS`**: node + head sends = uniq receives. -/
theorem digsBal_of (hH : HoldsP nearAirV3 pub tr) (T : V3RecordsTraffic pub tr r) :
    ZkFormal.NearV3.Link3.DigsBal r.nodes r.heads r.uniq := by
  apply List.perm_iff_count.mpr
  intro m
  have h := bal_users hH (b := ZkFormal.NearV3.B_DIGS) (U := [T_NODE, T_HEAD, T_UNIQ]) (by decide)
    (by decide) (by decide +kernel) (by decide +kernel) m
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero] at h
  rw [node_count T _ _ _ (by decide +kernel), node_count T _ _ _ (by decide +kernel),
    head_count T, head_count T, uniq_count T, uniq_count T] at h
  simp only [tcnt_unfold] at h
  have z1 : ZkFormal.NearV3.nodeRecvs3 r.nodes ZkFormal.NearV3.B_DIGS = [] := by
    simp [ZkFormal.NearV3.nodeRecvs3, ZkFormal.NearV3.B_DIGS, B_DIGEST, B_PARENT, B_EDGE,
      ZkFormal.NearV3.B_BMAP, ZkFormal.NearV3.B_DUP, ZkFormal.NearV3.B_ENT, ZkFormal.NearV3.B_UPB, B_VSLOT]
  have z2 : ZkFormal.NearV3.headRecvs r.heads ZkFormal.NearV3.B_DIGS = [] := by
    simp [ZkFormal.NearV3.headRecvs, ZkFormal.NearV3.B_DIGS, B_DIGEST, ZkFormal.NearV3.B_ROOT, B_EDGE]
  have z3 : ZkFormal.NearV3.uniqSends r.uniq ZkFormal.NearV3.B_DIGS = [] := by
    simp [ZkFormal.NearV3.uniqSends, ZkFormal.NearV3.B_DUP, ZkFormal.NearV3.B_DIGS]
  rw [z1, z2, z3] at h
  simp only [count_nil_map] at h
  rw [count_map_append]
  omega

/-- The users of `EDGE` and `BMAP` (`headV3` has no `BMAP` traffic, which is harmless). -/
theorem walk_users_ok : UsersOk B_EDGE [T_NODE, T_HEAD, T_WALK, T_UPS] = true ∧
    UsersOk ZkFormal.NearV3.B_BMAP [T_NODE, T_HEAD, T_WALK, T_UPS] = true :=
  ⟨by decide +kernel, by decide +kernel⟩

/-- **`EDGE` / `BMAP`**: the balance of node, head, walk and ups traffic (`WalkBal`). -/
theorem walkBal_of (hH : HoldsP nearAirV3 pub tr) (T : V3RecordsTraffic pub tr r) {b : Nat}
    (hb : b = B_EDGE ∨ b = ZkFormal.NearV3.B_BMAP) :
    ZkFormal.NearV3.UpsRows.WalkBal r.nodes r.heads r.walks r.ups b := by
  apply List.perm_iff_count.mpr
  intro m
  have hU : UsersOk b [T_NODE, T_HEAD, T_WALK, T_UPS] = true := by
    rcases hb with rfl | rfl
    · exact walk_users_ok.1
    · exact walk_users_ok.2
  have hpb : ZkFormal.NearV3.Public.preparedSegments.all (fun s => s.bus != b) = true := by
    rcases hb with rfl | rfl <;> decide +kernel
  have hA (is : List Interaction) (hi : is = ZkFormal.NearV3.UnfoldA7.Node.interactions ∨
      is = ZkFormal.NearV3.UnfoldA7.Ups.interactions) : is.all (fun i => i.bus != b) = true := by
    rcases hb with rfl | rfl <;> rcases hi with rfl | rfl <;> decide +kernel
  have h := bal_users hH (b := b) (U := [T_NODE, T_HEAD, T_WALK, T_UPS]) (by decide)
    (by decide) hU hpb m
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero] at h
  rw [node_count T _ _ _ (hA _ (.inl rfl)), node_count T _ _ _ (hA _ (.inl rfl)),
    head_count T, head_count T, walk_count T, walk_count T,
    ups_count T _ _ _ (hA _ (.inr rfl)), ups_count T _ _ _ (hA _ (.inr rfl))] at h
  simp only [tcnt_unfold] at h
  rw [count_map_append, count_map_append, count_map_append, count_map_append,
    count_map_append, count_map_append]
  omega

/-- **`UPB`**: node + ups sends = node + ups receives. -/
theorem upbBal_of (hH : HoldsP nearAirV3 pub tr) (T : V3RecordsTraffic pub tr r) :
    ZkFormal.NearV3.UpsRows.UpbBal r.nodes r.ups := by
  apply List.perm_iff_count.mpr
  intro m
  have h := bal_users hH (b := ZkFormal.NearV3.B_UPB) (U := [T_NODE, T_UPS]) (by decide)
    (by decide) (by decide +kernel) (by decide +kernel) m
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero] at h
  rw [node_count T _ _ _ (by decide +kernel), node_count T _ _ _ (by decide +kernel),
    ups_count T _ _ _ (by decide +kernel), ups_count T _ _ _ (by decide +kernel)] at h
  simp only [tcnt_unfold] at h
  rw [count_map_append, count_map_append]
  omega

end Trie

/-! ## `SIZE`: the size view's totals are the node / value record totals -/

/-- A table whose interactions on `(b, s)` all start with the constant `c0` has no count for a
message with another head. -/
theorem tableBusCount_head_const {is : List Interaction} {tr : Trace Fp} {t : Nat} {pub : List Fp}
    {b : Nat} {s : Bool} {c0 : Nat}
    (hc : ∀ i ∈ is, i.bus = b → i.send = s → i.msg.head? = some (.const c0))
    {m : List Fp} (hm : m.head? ≠ some (Fp.ofNat c0)) : tableBusCount is tr t pub b s m = 0 := by
  rw [tableBusCount_eq]
  apply List.count_eq_zero.mpr
  intro hx
  obtain ⟨r, -, hx⟩ := List.mem_flatMap.mp hx
  unfold rowTraffic at hx
  obtain ⟨i, hi, hx⟩ := List.mem_flatMap.mp hx
  split at hx
  · rename_i hbs
    have he := (List.mem_replicate.mp hx).2
    have hh := hc i hi hbs.1 hbs.2
    apply hm
    rw [he]
    unfold Interaction.msgVal
    rw [List.head?_map, hh]
    rfl
  · simp at hx

theorem size_a7_node : ∀ i ∈ ZkFormal.NearV3.UnfoldA7.Node.interactions,
    i.bus = ZkFormal.NearV3.B_SIZE → i.send = true → i.msg.head? = some (.const 3) := by decide +kernel
theorem size_a7_val : ∀ i ∈ ZkFormal.NearV3.UnfoldA7.Val.interactions,
    i.bus = ZkFormal.NearV3.B_SIZE → i.send = true → i.msg.head? = some (.const 4) := by decide +kernel
theorem size_a7_ups : ∀ i ∈ ZkFormal.NearV3.UnfoldA7.Ups.interactions,
    i.bus = ZkFormal.NearV3.B_SIZE → i.send = true → i.msg.head? = some (.const 5) := by decide +kernel
theorem size_a7_size : ∀ i ∈ ZkFormal.NearV3.UnfoldA7.Size.interactions,
    i.bus = ZkFormal.NearV3.B_SIZE → i.send = true → i.msg.head? = some (.const 7) := by decide +kernel

theorem ofNat_ne {a c : Nat} (ha : a < P) (hc : c < P) (h : a ≠ c) : Fp.ofNat a ≠ Fp.ofNat c :=
  fun e => h (ZkFormal.Near.Link.ofNat_inj ha hc e)

/-- **A received `SIZE` message with tag `0` or `1` is sent by `nodeV3` or `valV3`.** -/
theorem size_sent {pub : List Fp} {tr : Trace Fp} {r : V3Records} (hH : HoldsP nearAirV3 pub tr)
    (T : V3RecordsTraffic pub tr r) {M : List Fp}
    (hM : 0 < tcnt (ZkFormal.NearV3.sizeTraffic r.size) false ZkFormal.NearV3.B_SIZE M)
    (h01 : M.head? = some (Fp.ofNat 0) ∨ M.head? = some (Fp.ofNat 1)) :
    0 < tcnt (ZkFormal.NearV3.nodeTraffic3 r.nodes) true ZkFormal.NearV3.B_SIZE M +
      tcnt (ZkFormal.NearV3.valTraffic r.values) true ZkFormal.NearV3.B_SIZE M := by
  have hne : ∀ c, 2 ≤ c → c < P → M.head? ≠ some (Fp.ofNat c) := by
    intro c h2 hc e
    rcases h01 with h | h <;> rw [h] at e <;> simp only [Option.some.injEq] at e <;>
      exact ofNat_ne (by unfold P; omega) hc (by omega) e
  have h := bal_users hH (b := ZkFormal.NearV3.B_SIZE) (U := [T_NODE, T_VAL, T_UPS, T_SRCP, T_SIZE])
    (by decide) (by decide) (by decide +kernel) (by decide +kernel) M
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero] at h
  have eN : isAt T_NODE = ZkFormal.NearV3.NodeV3.interactions ++ ZkFormal.NearV3.UnfoldA7.Node.interactions := rfl
  have eV : isAt T_VAL = ZkFormal.NearV3.ValV3.interactions ++ ZkFormal.NearV3.UnfoldA7.Val.interactions := rfl
  have eU : isAt T_UPS = ZkFormal.NearV3.UpsV3.interactions ++ ZkFormal.NearV3.UnfoldA7.Ups.interactions := rfl
  have eS : isAt T_SIZE = ZkFormal.NearV3.SizeV3.interactions ++ ZkFormal.NearV3.UnfoldA7.Size.interactions := rfl
  have eR : isAt T_SRCP = ZkFormal.NearV3.SrcpV3.interactions := rfl
  rw [eN, eV, eU, eS, eR] at h
  simp only [tableBusCount_append] at h
  rw [tcnt_of_traffic T.nodes, tcnt_of_traffic T.nodes, tcnt_of_traffic T.values,
    tcnt_of_traffic T.values, tcnt_of_traffic T.srcp, tcnt_of_traffic T.srcp,
    tcnt_of_traffic T.size, tcnt_of_traffic T.size,
    tableBusCount_head_const size_a7_node (hne 3 (by omega) (by unfold P; omega)),
    tableBusCount_head_const size_a7_val (hne 4 (by omega) (by unfold P; omega)),
    tableBusCount_head_const size_a7_ups (hne 5 (by omega) (by unfold P; omega)),
    tableBusCount_head_const size_a7_size (hne 7 (by omega) (by unfold P; omega)),
    tableBusCount_nobus (b := ZkFormal.NearV3.B_SIZE) (is := ZkFormal.NearV3.UpsV3.interactions)
      (nobus_of_all (by decide +kernel))] at h
  have hs0 : tcnt (ZkFormal.NearV3.sizeTraffic r.size) true ZkFormal.NearV3.B_SIZE M = 0 := rfl
  have hr0 : tcnt (ZkFormal.NearV3.srcpTraffic r.srcp) true ZkFormal.NearV3.B_SIZE M = 0 := by
    simp only [tcnt, ZkFormal.NearV3.srcpTraffic, ite_true, List.map_cons, List.map_nil]
    apply List.count_eq_zero.mpr
    simp only [List.mem_singleton]
    intro e
    apply hne 2 (by omega) (by unfold P; omega)
    rw [e]; rfl
  omega

/-- `x0` of the size view: the bytes of the non-duplicate node records (all instances). -/
def nodeStoreSum (vs : List ZkFormal.NearV3.NodeS3) : Nat :=
  ((vs.filter fun s => !s.dup).map fun s => (s.v.ser false).length).sum

/-- `x1` of the size view: the bytes of the non-empty non-duplicate value records. -/
def valStoreSum (es : List ZkFormal.NearV3.ValE) : Nat :=
  ((es.filter fun e => !e.vz && !e.dup).map ZkFormal.NearV3.ValE.len).sum

theorem sum_map_filter_le {α : Type} (p : α → Bool) (f : α → Nat) :
    ∀ l : List α, ((l.filter p).map f).sum ≤ (l.map f).sum
  | [] => by simp
  | a :: l => by
    have := sum_map_filter_le p f l
    by_cases h : p a <;> simp [h] <;> omega

theorem nodeSends3_size (vs : List ZkFormal.NearV3.NodeS3) :
    ZkFormal.NearV3.nodeSends3 vs ZkFormal.NearV3.B_SIZE = [[0, nodeStoreSum vs]] := by
  simp [ZkFormal.NearV3.nodeSends3, nodeStoreSum, ZkFormal.NearV3.B_SIZE, B_BYTES, B_PARENT,
    ZkFormal.NearV3.B_VPARENT, B_EDGE, ZkFormal.NearV3.B_BMAP, ZkFormal.NearV3.B_DIGS, ZkFormal.NearV3.B_ENT]

theorem valSends_size (es : List ZkFormal.NearV3.ValE) :
    ZkFormal.NearV3.valSends es ZkFormal.NearV3.B_SIZE = [[1, valStoreSum es]] := by
  simp [ZkFormal.NearV3.valSends, valStoreSum, ZkFormal.NearV3.B_SIZE, B_BYTES, ZkFormal.NearV3.B_ENT]

theorem nodeStoreSum_lt {vs : List ZkFormal.NearV3.NodeS3} (hw : ZkFormal.NearV3.NodeWf3 vs) :
    nodeStoreSum vs < 2 ^ 22 := by
  have := sum_map_filter_le (fun s : ZkFormal.NearV3.NodeS3 => !s.dup) (fun s => (s.v.ser false).length) vs
  have := hw.rows
  unfold nodeStoreSum; omega

theorem valStoreSum_lt {es : List ZkFormal.NearV3.ValE} (hw : ZkFormal.NearV3.ValWf es) :
    valStoreSum es < 2 ^ 22 := by
  have h1 := sum_map_filter_le (fun e : ZkFormal.NearV3.ValE => !e.vz && !e.dup) ZkFormal.NearV3.ValE.len es
  have h2 : ((es.filter fun e => !e.vz && !e.dup).map ZkFormal.NearV3.ValE.len).sum ≤
      ((es.filter fun e => !e.vz && !e.dup).map fun e => if e.vz then 1 else e.len).sum := by
    apply Nat.le_of_eq; congr 1; apply List.map_congr_left; intro e he
    simp only [List.mem_filter, Bool.and_eq_true, Bool.not_eq_true'] at he
    simp [he.2.1]
  have h3 := sum_map_filter_le (fun e : ZkFormal.NearV3.ValE => !e.vz && !e.dup)
    (fun e : ZkFormal.NearV3.ValE => if e.vz then 1 else e.len) es
  have := hw.rows
  unfold valStoreSum; omega

/-- **The `SIZE` totals.** The size view's `x0` / `x1` are the non-duplicate node / value
record bytes, and their sum is at most `3,000,000` (`checkD0`'s `w.size` for the store). -/
theorem size_totals {pub : List Fp} {tr : Trace Fp} {r : V3Records} (hH : HoldsP nearAirV3 pub tr)
    (T : V3RecordsTraffic pub tr r) (W : V3RecordsWf pub r) :
    r.size.x0 = nodeStoreSum r.nodes ∧ r.size.x1 = valStoreSum r.values ∧
      nodeStoreSum r.nodes + valStoreSum r.values ≤ 3000000 := by
  have hN := nodeStoreSum_lt W.nodes
  have hV := valStoreSum_lt W.values
  have hc := W.size.canon
  have hP : (2 : Nat) ^ 22 < P := by unfold P; omega
  -- tag `j`'s message is received by `sizeV3`
  have recv (j x : Nat) (hj : j < 3) (hx : [j, x] ∈ [[0, r.size.x0], [1, r.size.x1], [2, r.size.x2]]) :
      0 < tcnt (ZkFormal.NearV3.sizeTraffic r.size) false ZkFormal.NearV3.B_SIZE (Msg.toFp [j, x]) := by
    simp only [tcnt, ZkFormal.NearV3.sizeTraffic, ite_true, Bool.false_eq_true, ite_false]
    exact List.count_pos_iff.mpr (List.mem_map.mpr ⟨_, hx, rfl⟩)
  have one (a b x y : Nat) (ha : a < P) (hb : b < P) (hx : x < P) (hy : y < P)
      (h : 0 < (([[a, x]] : List Msg).map Msg.toFp).count (Msg.toFp [b, y])) : a = b ∧ x = y := by
    simp only [List.map_cons, List.map_nil] at h
    have := List.mem_singleton.mp (List.count_pos_iff.mp h)
    simp only [Msg.toFp, List.map_cons, List.map_nil, List.cons.injEq, and_true] at this
    exact ⟨(ZkFormal.Near.Link.ofNat_inj hb ha this.1).symm, (ZkFormal.Near.Link.ofNat_inj hy hx this.2).symm⟩
  have x0 : r.size.x0 = nodeStoreSum r.nodes := by
    have h := size_sent hH T (recv 0 r.size.x0 (by omega) (by simp)) (.inl rfl)
    rw [tcnt_unfold.1, tcnt_unfold.2.2.2.2.1, nodeSends3_size, valSends_size] at h
    rcases Nat.eq_zero_or_pos ((([[0, nodeStoreSum r.nodes]] : List Msg).map Msg.toFp).count
        (Msg.toFp [0, r.size.x0])) with h0 | h0
    · rw [h0, Nat.zero_add] at h
      have := (one 1 0 _ _ (by unfold P; omega) (by unfold P; omega) (by omega) hc.1 h).1
      omega
    · exact ((one 0 0 _ _ (by unfold P; omega) (by unfold P; omega) (by omega) hc.1 h0).2).symm
  have x1 : r.size.x1 = valStoreSum r.values := by
    have h := size_sent hH T (recv 1 r.size.x1 (by omega) (by simp)) (.inr rfl)
    rw [tcnt_unfold.1, tcnt_unfold.2.2.2.2.1, nodeSends3_size, valSends_size] at h
    rcases Nat.eq_zero_or_pos ((([[0, nodeStoreSum r.nodes]] : List Msg).map Msg.toFp).count
        (Msg.toFp [1, r.size.x1])) with h0 | h0
    · rw [h0, Nat.zero_add] at h
      exact ((one 1 1 _ _ (by unfold P; omega) (by unfold P; omega) (by omega) hc.2.1 h).2).symm
    · have := (one 0 1 _ _ (by unfold P; omega) (by unfold P; omega) (by omega) hc.2.1 h0).1
      omega
  refine ⟨x0, x1, ?_⟩
  have := W.size.base_le (by rw [x0, x1]; unfold P; omega)
  rw [x0, x1] at this
  exact this

end ZkFormal.NearV3.Assembly
