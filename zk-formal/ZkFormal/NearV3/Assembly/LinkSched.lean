import ZkFormal.NearV3.Assembly.LinkVPost
import ZkFormal.NearV3.Sched.Link.CodecSV

/-!
# ZkFormal.NearV3.Assembly.LinkSched — `SchedVal` of the ups records from `HoldsP`

`codec_schedVal_lt` is `Sched.codec_schedVal` (proof copied) with the instance `τ` of every
`SPLEN` / `SPOST` message exported as canonical (`τ = cv … tau < P`), as `SchedVal` needs.
-/

namespace ZkFormal.NearV3.Sched

open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Chacha ZkFormal.Chacha.Table.E

variable {AP : AirP} {pub : List Fp} {tr : Trace Fp}

theorem codec_schedVal_lt (hH : HoldsP AP pub tr) {tc : Nat} (O : CodecValOwn AP tc) (SO : SparOwn AP)
    (I : PubIdx AP pub Fp.ofNat) (Ps : List InstPub) (fwd : List (Nat × Nat))
    (hrec : I.recs B_SPAR true = (render Ps fwd).par) (hlen : Ps.length < 2013265921) :
    ∃ sv : Nat → List Nat, sv = svOf tr tc ∧
      (∀ τ, ∀ x ∈ sv τ, x < 256) ∧ (∀ τ, (sv τ).length < 2 ^ 24) ∧
      (∀ t r (i : Interaction), t < AP.tables.length → r < tr.height t → i ∈ AP.tables[t]!.interactions →
        i.bus = B_SPLEN → i.send = false → i.multNat tr t r pub ≠ 0 →
        ∃ τ, τ < ZkFormal.Algebra.P ∧ i.msgVal tr t r pub = [τ, (sv τ).length].map Fp.ofNat) ∧
      (∀ t r (i : Interaction), t < AP.tables.length → r < tr.height t → i ∈ AP.tables[t]!.interactions →
        i.bus = B_SPOST → i.send = false → i.multNat tr t r pub ≠ 0 →
        ∃ τ d, τ < ZkFormal.Algebra.P ∧ d < (sv τ).length ∧
          i.msgVal tr t r pub = [τ, d, (sv τ).getD d 0].map Fp.ofNat) := by
  have hL := codec_local hH O
  have hH22 := codec_h22 hH O
  refine ⟨svOf tr tc, rfl, ?_, ?_, ?_, ?_⟩
  · intro τ x hx
    unfold svOf at hx
    split at hx
    · rename_i h
      obtain ⟨hf, hF, -⟩ := Classical.choose_spec h
      obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
      have hi' := List.mem_range.1 hi
      obtain ⟨P1, -⟩ := Codec.codec_post hL hH22 hf hF
      obtain ⟨m1, -⟩ := P1 i (by omega)
      have hrow : Classical.choose h + i < tr.height tc := by
        obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hlt, -⟩ := Codec.codec_block hL hH22 hf hF
        omega
      have he := Codec.encG_eval _ (mult1_enc (by rw [m1]; exact Nat.one_ne_zero)) hL hrow
      exact (Codec.bytes hL hrow he).2.1
    · simp at hx
  · intro τ
    unfold svOf
    split
    · rename_i h
      obtain ⟨hf, hF, -⟩ := Classical.choose_spec h
      obtain ⟨-, hN, -⟩ := Codec.codec_block hL hH22 hf hF
      simp only [List.length_map, List.length_range]
      omega
    · simp
  · intro t r i ht hr hi hb hs hm
    obtain ⟨f, hf, hF, hmsg, -, -⟩ := codec_splen_sole hH O ht hr hi hb hs hm
    refine ⟨cv tr tc f Codec.tau, Fp.toNat_lt _, ?_⟩
    rw [hmsg, svOf_block hH O SO I Ps fwd hrec hlen hf hF]
    simp
  · intro t r i ht hr hi hb hs hm
    obtain ⟨r', hr', hm', hmsg⟩ := codec_spost_sole hH O ht hr hi hb hs hm
    have he := Codec.encG_eval _ (mult1_enc hm') hL hr'
    obtain ⟨f, hfr, hF, hlt⟩ := Codec.enc_row hL hH22 hr' he
    have hf : f < tr.height tc := by omega
    obtain ⟨P1, -⟩ := Codec.codec_post hL hH22 hf hF
    obtain ⟨-, hpm⟩ := P1 (r' - f) (by omega)
    rw [show f + (r' - f) = r' by omega, msg1_eq] at hpm
    refine ⟨cv tr tc f Codec.tau, r' - f, Fp.toNat_lt _, ?_, ?_⟩
    · rw [svOf_block hH O SO I Ps fwd hrec hlen hf hF]; simp; omega
    · rw [hmsg, hpm, svOf_block hH O SO I Ps fwd hrec hlen hf hF]
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by omega)]
      simp [show f + (r' - f) = r' by omega]

end ZkFormal.NearV3.Sched

namespace ZkFormal.NearV3.Assembly

open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near

namespace LinkSched

open ZkFormal.NearV3 ZkFormal.NearV3.Link3

/-- A receive of the ups view is a physical row receive of `T_UPS`. -/
theorem ups_recv_row {pub : List Fp} {tr : Trace Fp} {r : V3Records} (T : V3RecordsTraffic pub tr r)
    {b : Nat} (hb : UnfoldA7.Ups.interactions.all (fun i => i.bus != b) = true) {m : Msg}
    (hm : m ∈ (upsTraffic r.ups).recvs b) :
    ∃ q, q < tr.height T_UPS ∧ ∃ i ∈ (nearAirV3.tables[T_UPS]!).interactions, i.bus = b ∧ i.send = false ∧
      i.multNat tr T_UPS q pub ≠ 0 ∧ i.msgVal tr T_UPS q pub = Msg.toFp m := by
  have hc : 0 < tcnt (upsTraffic r.ups) false b (Msg.toFp m) := by
    simp only [tcnt, Bool.false_eq_true, ite_false]
    exact List.count_pos_iff.mpr (List.mem_map_of_mem hm)
  rw [← ups_count T false b _ hb, tableBusCount_eq] at hc
  obtain ⟨q, hq, hy⟩ := List.mem_flatMap.mp (List.count_pos_iff.mp hc)
  unfold rowTraffic at hy
  obtain ⟨i, hi, hy⟩ := List.mem_flatMap.mp hy
  split at hy
  · rename_i hbs
    obtain ⟨hpos, he⟩ := List.mem_replicate.mp hy
    exact ⟨q, List.mem_range.mp hq, i, hi, hbs.1, hbs.2, by omega, he.symm⟩
  · simp at hy

/-- **`SchedVal`** of the ups records, `sv = toB ∘ svOf tr T_CODEC`. -/
theorem schedVal_holds {cb : NearSpec.Bytes} {h : NearSpecV3.Hint} {p : NearSpecV3.Prep} {oh : Nat}
    {tr : Trace Fp} {r : V3Records} (hp : NearSpecV3.prepD0 cb h = .ok p)
    (hsz : (ZkFormal.NearV3.Public.preparedBytes p oh).length < P)
    (hH : HoldsP nearAirV3 (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr)
    (T : V3RecordsTraffic (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr r) :
    ∃ sv : Nat → NearSpec.Bytes, sv = (fun τ => toB (Sched.svOf tr T_CODEC τ)) ∧ UpsRows.SchedVal r.ups sv := by
  have hlen : (ZkFormal.NearV3.Public.preparedBytes p oh).length < 256 ^ 4 := by unfold P at hsz; omega
  have hrec := (ZkFormal.NearV3.Public.prepared_scheduler_index nearAirV3 oh rfl hp (prepD0_roots hp)
    (prepD0_source_roots hp) hlen).2.1
  have hPs := ZkFormal.NearV3.Sched.prepD0_len hp
  obtain ⟨sv, rfl, hby, hln, hsl, hsp⟩ := ZkFormal.NearV3.Sched.codec_schedVal_lt hH codecOwn sparOwn
    (ZkFormal.NearV3.Public.prepared_pubIdx nearAirV3 p oh rfl (prepD0_roots hp) (prepD0_source_roots hp) hlen)
    (p.sched.map ZkFormal.NearV3.Sched.instOf) p.fwd hrec (by simp only [List.length_map]; omega)
  have hups : T_UPS < nearAirV3.tables.length := by decide
  refine ⟨fun τ => toB (Sched.svOf tr T_CODEC τ), rfl, ⟨?_, ?_, ?_⟩⟩
  · intro m hm
    obtain ⟨q, hq, i, hi, hb, hs, hmu, he⟩ := ups_recv_row T (by decide +kernel) hm
    obtain ⟨τ, hτ, hmsg⟩ := hsl T_UPS q i hups hq hi hb hs hmu
    refine ⟨τ, hτ, ?_⟩
    rw [← he, hmsg]
    simp [toB, Msg.toFp]
  · intro m hm
    obtain ⟨q, hq, i, hi, hb, hs, hmu, he⟩ := ups_recv_row T (by decide +kernel) hm
    obtain ⟨τ, d, hτ, hd, hmsg⟩ := hsp T_UPS q i hups hq hi hb hs hmu
    refine ⟨τ, d, hτ, by simpa [toB] using hd, ?_⟩
    rw [← he, hmsg, LinkVPost.toB_bytes _ (hby τ)]
    rfl
  · intro τ
    simpa [toB] using hln τ

end LinkSched

end ZkFormal.NearV3.Assembly

namespace ZkFormal.NearV3.Assembly

open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near

namespace LinkSched

open ZkFormal.NearV3 ZkFormal.NearV3.Link3 ZkFormal.NearV3.UpsRows

/-- **The `upsV3` link from `HoldsP`** (`upsV3_linkB_22` with every hypothesis discharged): for
every instance `τ ≤ K`, the upsert of the scheduler's value into the post record tree is the next
instance's pre root (the final post root at `τ = K`), and the ups `S0F` facts. -/
theorem upsLink_holds {cb : NearSpec.Bytes} {h : NearSpecV3.Hint} {p : NearSpecV3.Prep} {oh : Nat}
    {tr : Trace Fp} {r : V3Records} (hp : NearSpecV3.prepD0 cb h = .ok p)
    (hsz : (ZkFormal.NearV3.Public.preparedBytes p oh).length < P)
    (hH : HoldsP nearAirV3 (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr)
    (T : V3RecordsTraffic (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr r)
    (W : V3RecordsWf (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r) :
    ∃ sv : Nat → NearSpec.Bytes, sv = (fun τ => toB (Sched.svOf tr T_CODEC τ)) ∧ SchedVal r.ups sv ∧
      ∀ τ, τ ≤ p.hdr.K →
      (∃ Q, (fullTree (Rpost r.nodes r.values) (Vpost r.nodes r.values (fun i => toB (LinkVPost.pnOf r.accts i)))
          (headAt r.heads τ).rid).upsert UpsSpec.key (sv τ) = some Q ∧
        (upsAt (r.ups.map upsE) τ).post = Q.hashOf.map UInt8.toNat ∧
        toB (upsAt (r.ups.map upsE) τ).post = Q.hashOf ∧
        (τ < p.hdr.K → (headAt r.heads (τ + 1)).pre = Q.hashOf.map UInt8.toNat) ∧
        (τ = p.hdr.K → p.hdr.postStateRoot.map UInt8.toNat = Q.hashOf.map UInt8.toNat)) ∧
      (∃ s ∈ r.ups, s.row 0 UpsV3.tau = τ ∧ s.msgs B_S0F true = [[τ, s.row 0 UpsV3.pres, s.row 0 UpsV3.vid]] ∧
        ((s.row 0 UpsV3.pres = 1 ∧ (fullTree (Rpost r.nodes r.values)
            (Vpost r.nodes r.values (fun i => toB (LinkVPost.pnOf r.accts i))) (headAt r.heads τ).rid).find
              UpsSpec.key = some (some (valOf (Vpost r.nodes r.values (fun i => toB (LinkVPost.pnOf r.accts i)))
                (vpos (vid0 r.values) (s.row 0 UpsV3.vid))))) ∨
         (s.row 0 UpsV3.pres = 0 ∧ s.row 0 UpsV3.vid = 0 ∧
            (fullTree (Rpost r.nodes r.values) (Vpost r.nodes r.values (fun i => toB (LinkVPost.pnOf r.accts i)))
              (headAt r.heads τ).rid).find UpsSpec.key = some none))) := by
  obtain ⟨sv, hsvd, hsv⟩ := schedVal_holds hp hsz hH T
  have L := trieLink_of hp hsz hH T W
  have hK := ZkFormal.NearV3.Public.prep_root_index_lt hp
  refine ⟨sv, hsvd, hsv, ?_⟩
  apply upsV3_linkB_22 W.nodes W.heads W.values W.ups W.walks W.walkSteps L.parent L.vparent L.upb
    L.edge L.bmap (LinkKeynib.keynibOk_of hp hsz hH T W) (LinkUps.hbytesU_of hp hsz hH T W)
    (LinkUps.hothU_of hp hsz hH T W) ?_ (memdBal_of hH T) (by unfold P; omega) (by omega) ?_ ?_
    (rootBal_of hp hsz hH T) (midBal_of hH T) ?_ L.sha (LinkVPost.vpostOk_holds hp hsz hH T W)
    (LinkVPost.hvpostLen_of hH T W) hsv
  · intro m hm
    apply digest_provided hH (t := T_UPS) (by decide)
    rw [ups_count T _ _ _ (by decide +kernel)]
    simp only [tcnt, Bool.false_eq_true, ite_false]
    exact List.count_pos_iff.mpr (List.mem_map_of_mem hm)
  · intro x hx; obtain ⟨y, -, rfl⟩ := List.mem_map.mp hx; have := UInt8.toNat_lt y; unfold P; omega
  · intro x hx; obtain ⟨y, -, rfl⟩ := List.mem_map.mp hx; have := UInt8.toNat_lt y; unfold P; omega
  · have := heads_le L.parent; have := W.nodes.count; unfold P; omega

end LinkSched

end ZkFormal.NearV3.Assembly
