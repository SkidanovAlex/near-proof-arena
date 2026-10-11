import ZkFormal.NearV3.Assembly.LinkShaKinds
import ZkFormal.NearV3.Extract.Ups.UpsChain
import ZkFormal.NearV3.Public.RootIndex
import ZkFormal.NearV3.Link.Uniq3Digs
import ZkFormal.NearV3.Assembly.LinkFields
import ZkFormal.NearV3.Extract.Ups.UpsBus
import ZkFormal.NearV3.Extract.Ups.UpsReads

/-!
# ZkFormal.NearV3.Assembly.LinkChain — the `ROOT` / `MIDROOT` instance chain of `nearAirV3`

* `midBal_of`: the `MIDROOT` balance (head sends = ups receives);
* `rootBal_of`: the `ROOT` balance with the two public root records of the prepared statement
  (`[0] ‖ prevStateRoot` sent, `[K+1] ‖ postStateRoot` received);
* **`rootChain_of`**: `RootChain r.heads (r.ups.map upsE) p.hdr.K r0 rK` (`ups_chain`) — one head
  and one ups segment per instance `τ ≤ K`, chained pre/post roots; the `Candidates/**`
  execution bridges take exactly this as a hypothesis;
* `upsTau_lt`: every ups segment's instance is `≤ K < 256`.
-/

namespace ZkFormal.NearV3.Assembly

open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near

section
variable {pub : List Fp} {tr : Trace Fp} {r : V3Records}

/-- **`MIDROOT`**: head sends = ups receives. -/
theorem midBal_of (hH : HoldsP nearAirV3 pub tr) (T : V3RecordsTraffic pub tr r) :
    ((ZkFormal.NearV3.headSends r.heads ZkFormal.NearV3.B_MIDROOT).map Msg.toFp).Perm
      (((ZkFormal.NearV3.upsTraffic r.ups).recvs ZkFormal.NearV3.B_MIDROOT).map Msg.toFp) := by
  apply List.perm_iff_count.mpr
  intro m
  have h := bal_users hH (b := ZkFormal.NearV3.B_MIDROOT) (U := [T_HEAD, T_UPS]) (by decide)
    (by decide) (by decide +kernel) (by decide +kernel) m
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero] at h
  rw [head_count T, head_count T, ups_count T _ _ _ (by decide +kernel),
    ups_count T _ _ _ (by decide +kernel)] at h
  simp only [tcnt_unfold] at h
  have z1 : ZkFormal.NearV3.headRecvs r.heads ZkFormal.NearV3.B_MIDROOT = [] := by
    simp [ZkFormal.NearV3.headRecvs, ZkFormal.NearV3.B_MIDROOT, B_DIGEST, ZkFormal.NearV3.B_ROOT, B_EDGE]
  have z2 : ((ZkFormal.NearV3.upsTraffic r.ups).sends ZkFormal.NearV3.B_MIDROOT).map Msg.toFp = [] := by
    have := tcnt_of_traffic T.ups true ZkFormal.NearV3.B_MIDROOT
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro x hx
    have hc := List.count_pos_iff.mpr hx
    rw [← tcnt_sends, ← this, tableBusCount_noside (by decide +kernel)] at hc
    exact absurd hc (Nat.lt_irrefl 0)
  rw [z1, z2] at h
  simp only [List.map_nil, List.count_nil, Nat.add_zero, Nat.zero_add] at h
  exact h

end

/-- **`ROOT`**: the public pre root and the ups post roots against the head pre roots and the
public post root. -/
theorem rootBal_of {cb : NearSpec.Bytes} {h : NearSpecV3.Hint} {p : NearSpecV3.Prep} {oh : Nat}
    {tr : Trace Fp} {r : V3Records} (hp : NearSpecV3.prepD0 cb h = .ok p)
    (hsz : (ZkFormal.NearV3.Public.preparedBytes p oh).length < P)
    (hH : HoldsP nearAirV3 (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr)
    (T : V3RecordsTraffic (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr r) :
    (([[0] ++ p.hdr.prevStateRoot.map UInt8.toNat] ++
        (ZkFormal.NearV3.upsTraffic r.ups).sends ZkFormal.NearV3.B_ROOT).map Msg.toFp).Perm
      ((ZkFormal.NearV3.headRecvs r.heads ZkFormal.NearV3.B_ROOT ++
        [[p.hdr.K + 1] ++ p.hdr.postStateRoot.map UInt8.toNat]).map Msg.toFp) := by
  have hlen : (ZkFormal.NearV3.Public.preparedBytes p oh).length < 256 ^ 4 := by unfold P at hsz; omega
  have hR := ZkFormal.NearV3.Public.prepared_root_index nearAirV3 oh rfl hp (prepD0_source_roots hp) hlen
  have hI := (ZkFormal.NearV3.Public.prepared_pubIdx nearAirV3 p oh rfl (prepD0_roots hp)
    (prepD0_source_roots hp) hlen).count
  apply List.perm_iff_count.mpr
  intro m
  have h := hH.balance ZkFormal.NearV3.B_ROOT m
  rw [busCount_users (U := [T_HEAD, T_UPS]) (by decide) (by decide) (by decide +kernel),
    busCount_users (U := [T_HEAD, T_UPS]) (by decide) (by decide) (by decide +kernel),
    hI, hI, hR.1, hR.2] at h
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero] at h
  rw [head_count T, head_count T, ups_count T _ _ _ (by decide +kernel),
    ups_count T _ _ _ (by decide +kernel)] at h
  simp only [tcnt_unfold] at h
  have z1 : ZkFormal.NearV3.headSends r.heads ZkFormal.NearV3.B_ROOT = [] := by
    simp [ZkFormal.NearV3.headSends, ZkFormal.NearV3.B_MIDROOT, B_PARENT, ZkFormal.NearV3.B_ROOT, B_EDGE,
      ZkFormal.NearV3.B_DIGS]
  have z2 : ((ZkFormal.NearV3.upsTraffic r.ups).recvs ZkFormal.NearV3.B_ROOT).map Msg.toFp = [] := by
    have := tcnt_of_traffic T.ups false ZkFormal.NearV3.B_ROOT
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro x hx
    have hc := List.count_pos_iff.mpr hx
    rw [← tcnt_recvs, ← this, tableBusCount_noside (by decide +kernel)] at hc
    exact absurd hc (Nat.lt_irrefl 0)
  rw [z1, z2] at h
  simp only [List.map_nil, List.count_nil, Nat.zero_add, List.map_append, List.count_append] at h ⊢
  simp only [List.map_cons, List.map_nil, Msg.toFp, List.map_append] at h ⊢
  omega

theorem pubOf_roots (bs : List UInt8) : ∀ x ∈ bs.map UInt8.toNat, x < P := by
  intro x hx
  obtain ⟨b, -, rfl⟩ := List.mem_map.mp hx
  have := b.toNat_lt; unfold P; omega

/-- **The instance chain** (`RootChain`) of `nearAirV3`. -/
theorem rootChain_of {cb : NearSpec.Bytes} {h : NearSpecV3.Hint} {p : NearSpecV3.Prep} {oh : Nat}
    {tr : Trace Fp} {r : V3Records} (hp : NearSpecV3.prepD0 cb h = .ok p)
    (hsz : (ZkFormal.NearV3.Public.preparedBytes p oh).length < P)
    (hH : HoldsP nearAirV3 (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr)
    (T : V3RecordsTraffic (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr r)
    (W : V3RecordsWf (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r) :
    ZkFormal.NearV3.RootChain r.heads (r.ups.map ZkFormal.NearV3.UpsRows.upsE) p.hdr.K
      (p.hdr.prevStateRoot.map UInt8.toNat) (p.hdr.postStateRoot.map UInt8.toNat) := by
  have hK := ZkFormal.NearV3.Public.prep_root_index_lt hp
  have hhl := ZkFormal.NearV3.Link3.heads_le (parentBal_of hH T)
  have hvc := W.nodes.count
  exact ZkFormal.NearV3.UpsRows.ups_chain W.heads W.ups (by unfold P; omega) (pubOf_roots _)
    (pubOf_roots _) (rootBal_of hp hsz hH T) (midBal_of hH T) (by unfold P; omega)

end ZkFormal.NearV3.Assembly

namespace ZkFormal.NearV3.UpsRows

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.UpsV3

/-- **The id of an `upsV3` `BYTES` message** is `upsIdN τ jj` with `τ < 2^17`, `jj ≤ 512` (the
row analysis of `sha_seg`). -/
theorem ups_bytes_head {v : List UpsSeg} (hw : UpsWf v) (hB : UpsIdBound v) {m : Msg}
    (hm : m ∈ (upsTraffic v).sends B_BYTES) {a : Nat} (ha : m.head? = some a) :
    ∃ τ jj, a = upsIdN τ jj ∧ τ < 2 ^ 17 ∧ jj ≤ 512 := by
  obtain ⟨s', hs', i', hi', hm'⟩ := mem_upsSends.1 hm
  obtain ⟨L', ps', fls', ws', hL'⟩ := ups_layout hw s' hs'
  obtain ⟨ci', ti', di', si', kd', sdx', hP'⟩ := ups_plan hw hs' hL'
  obtain ⟨hτ', hps2⟩ := hB s' hs'
  have hps2' := hps2 L' ps' fls' ws' hL'
  rcases Nat.lt_or_ge i' 4 with h4 | h4
  · rw [hL'.msgsW i' h4 B_BYTES true] at hm'
    simp [B_BYTES, B_MIDROOT, B_ROOT, B_DIGEST, B_S0F, B_SPLEN, B_EDGE, B_BMAP] at hm'
  rcases Nat.lt_or_ge i' (4 + L') with hv | hv
  · rw [show i' = 4 + (i' - 4) by omega, hL'.msgsV (i' - 4) (by omega) B_BYTES true] at hm'
    simp [B_BYTES, B_SPOST] at hm'
    subst hm'
    simp only [List.head?_cons, Option.some.injEq] at ha
    subst ha
    rw [hL'.segc _ (by omega) tau (by decide)]
    exact ⟨_, _, rfl, hτ', by omega⟩
  · rw [hL'.msgsQ i' hv hi' B_BYTES true] at hm'
    simp [B_BYTES, B_DIGEST, B_UPB, B_MEMD] at hm'
    subst hm'
    simp only [List.head?_cons, Option.some.injEq] at ha
    subst ha
    obtain ⟨k', hk', e1, e2⟩ := partRow hw hs' hL' hP' hv hi'
    have hj : s'.row i' j = k' + 1 := by
      rw [show i' = ps'[k'].1 + (i' - ps'[k'].1) by omega, partPc hw hs' hL' hP' k' hk' _ (by omega) (by decide)]
      exact (hL'.part k' hk').1
    rw [hL'.segc _ hi' tau (by decide), hj]
    exact ⟨_, _, rfl, hτ', by omega⟩

end ZkFormal.NearV3.UpsRows

namespace ZkFormal.NearV3.Assembly

open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near

theorem upsKindIn {v : List ZkFormal.NearV3.UpsSeg} (hw : ZkFormal.NearV3.UpsWf v)
    (hB : ZkFormal.NearV3.UpsRows.UpsIdBound v) :
    ∀ x ∈ (ZkFormal.NearV3.upsTraffic v).sends B_BYTES, KindIn [K_VUPS] x := by
  intro x hx a ha
  obtain ⟨τ, jj, rfl, hτ, hj⟩ := ZkFormal.NearV3.UpsRows.ups_bytes_head hw hB hx ha
  refine ⟨ZkFormal.NearV3.UpsRows.upsIdN_lt _ _, ?_⟩
  rw [ZkFormal.NearV3.UpsRows.upsIdN_val hτ hj, List.mem_singleton]
  unfold K_VUPS
  omega

theorem upsKinds {v : List ZkFormal.NearV3.UpsSeg} (hw : ZkFormal.NearV3.UpsWf v)
    (hB : ZkFormal.NearV3.UpsRows.UpsIdBound v) :
    KindsOk ((ZkFormal.NearV3.upsTraffic v).sends B_BYTES) :=
  kindsOk_of_kindIn (upsKindIn hw hB) (by decide)

/-- **The ups registry from `HoldsP`**: the instance chain bounds every segment's `τ` by
`K < 256`, and `ups_idBound` bounds the parts. -/
theorem upsKinds_of {cb : NearSpec.Bytes} {h : NearSpecV3.Hint} {p : NearSpecV3.Prep} {oh : Nat}
    {tr : Trace Fp} {r : V3Records} (hp : NearSpecV3.prepD0 cb h = .ok p)
    (hsz : (ZkFormal.NearV3.Public.preparedBytes p oh).length < P)
    (hH : HoldsP nearAirV3 (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr)
    (T : V3RecordsTraffic (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr r)
    (W : V3RecordsWf (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r) :
    KindsOk ((ZkFormal.NearV3.upsTraffic r.ups).sends B_BYTES) := by
  have hC := rootChain_of hp hsz hH T W
  have hK := ZkFormal.NearV3.Public.prep_root_index_lt hp
  apply upsKinds W.ups
  exact ZkFormal.NearV3.UpsRows.ups_idBound W.nodes W.heads (parentBal_of hH T) W.ups (upbBal_of hH T)
    (fun s hs => by have := ZkFormal.NearV3.UpsRows.ups_tauBound hC s hs; omega)

/-- The ups `BYTES` ids are of kind `K_VUPS` (from `HoldsP`). -/
theorem upsKindIn_of {cb : NearSpec.Bytes} {h : NearSpecV3.Hint} {p : NearSpecV3.Prep} {oh : Nat}
    {tr : Trace Fp} {r : V3Records} (hp : NearSpecV3.prepD0 cb h = .ok p)
    (hsz : (ZkFormal.NearV3.Public.preparedBytes p oh).length < P)
    (hH : HoldsP nearAirV3 (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr)
    (T : V3RecordsTraffic (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr r)
    (W : V3RecordsWf (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r) :
    ∀ x ∈ (ZkFormal.NearV3.upsTraffic r.ups).sends B_BYTES, KindIn [K_VUPS] x := by
  have hC := rootChain_of hp hsz hH T W
  have hK := ZkFormal.NearV3.Public.prep_root_index_lt hp
  apply upsKindIn W.ups
  exact ZkFormal.NearV3.UpsRows.ups_idBound W.nodes W.heads (parentBal_of hH T) W.ups (upbBal_of hH T)
    (fun s hs => by have := ZkFormal.NearV3.UpsRows.ups_tauBound hC s hs; omega)

/-- **`OthersKinds` from `HoldsP`** (all six other `BYTES` senders). -/
theorem othersKinds_holds {cb : NearSpec.Bytes} {h : NearSpecV3.Hint} {p : NearSpecV3.Prep} {oh : Nat}
    {tr : Trace Fp} {r : V3Records} (hp : NearSpecV3.prepD0 cb h = .ok p)
    (hsz : (ZkFormal.NearV3.Public.preparedBytes p oh).length < P)
    (hH : HoldsP nearAirV3 (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr)
    (T : V3RecordsTraffic (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr r)
    (W : V3RecordsWf (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r) :
    OthersKinds tr (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r :=
  othersKinds_of (upsKinds_of hp hsz hH T W) (rcptKinds_of W) (acctKinds hH T W) (srcpKinds W.srcp)
    (mrkKinds W (pubNat_pubOf_lt _)) (codecKinds hp hsz hH)

/-- **`ShaHyp` of the trie tables from `HoldsP`** (no remaining hypothesis): the SHA union, the
exact `BYTES` decomposition with the other senders' messages net of the public body, their
kind registry, and the `DIGEST` provision. -/
theorem shaHyp_holds {cb : NearSpec.Bytes} {h : NearSpecV3.Hint} {p : NearSpecV3.Prep} {oh : Nat}
    {tr : Trace Fp} {r : V3Records} (hp : NearSpecV3.prepD0 cb h = .ok p)
    (hsz : (ZkFormal.NearV3.Public.preparedBytes p oh).length < P)
    (hH : HoldsP nearAirV3 (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr)
    (T : V3RecordsTraffic (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr r)
    (W : V3RecordsWf (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r) :
    ZkFormal.NearV3.Link3.ShaHyp r.nodes r.heads r.values
      (othersBytes tr (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r)
      (shaU tr (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) true)
      (shaU tr (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) false) :=
  shaHyp_of hH T (othersKinds_holds hp hsz hH T W) (bodyOk_of hp hsz W)

end ZkFormal.NearV3.Assembly
