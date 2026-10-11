import ZkFormal.NearV3.Assembly.LinkSchedCore
import ZkFormal.NearV3.Assembly.SchedulerPreparedContexts

/-!
# ZkFormal.NearV3.Assembly.LinkSchedRead — the scheduler's read of `0x0f` at `nearAirV3`

* **`s0f_codec`** (`S0F` link): the `S0F (τ, pres, vid)` that a codec block receives is sent by an
  ups segment with the same `(tau, pres, vid)` (ups is the only `S0F` sender; no public segment);
* **`codec_read`**: with `ups_tauDistinct` (one ups segment per `τ`) and `upsLink_holds`, the
  codec block of `τ ≤ K` reads `pres = 1` and the value record `vid` iff the `0x0f` key is present in
  the record tree under `headAt τ` (with that value), and `pres = 0`, `vid = 0` iff it is absent.
-/

namespace ZkFormal.NearV3.Assembly

open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near

namespace LinkSchedCore

open ZkFormal.NearV3 ZkFormal.NearV3.Link3 ZkFormal.NearV3.UpsRows ZkFormal.NearV3.Sched

/-- **`S0F` link**: a codec block's `S0F` receive is an ups segment's send. -/
theorem s0f_codec {cb : NearSpec.Bytes} {h : NearSpecV3.Hint} {p : NearSpecV3.Prep} {oh : Nat}
    {tr : Trace Fp} {r : V3Records} (hp : NearSpecV3.prepD0 cb h = .ok p)
    (hsz : (ZkFormal.NearV3.Public.preparedBytes p oh).length < P)
    (hH : HoldsP nearAirV3 (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr)
    (T : V3RecordsTraffic (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr r)
    (W : V3RecordsWf (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r)
    {f : Nat} (hf : f < tr.height T_CODEC) (hF : cv tr T_CODEC f Codec.kF = 1) :
    ∃ s ∈ r.ups, s.row 0 UpsV3.tau = cv tr T_CODEC f Codec.tau ∧
      s.row 0 UpsV3.pres = cv tr T_CODEC f Codec.pres ∧ s.row 0 UpsV3.vid = cv tr T_CODEC f Codec.vid := by
  have hlen : (ZkFormal.NearV3.Public.preparedBytes p oh).length < 256 ^ 4 := by unfold P at hsz; omega
  have hrec := ZkFormal.NearV3.Public.prepared_scheduler_index nearAirV3 oh rfl hp (prepD0_roots hp)
    (prepD0_source_roots hp) hlen
  have hPs := ZkFormal.NearV3.Sched.prepD0_len hp
  obtain ⟨m4, msg4, -⟩ := pvOf_vbytes hH codecOwn sparOwn
    (ZkFormal.NearV3.Public.prepared_pubIdx nearAirV3 p oh rfl (prepD0_roots hp) (prepD0_source_roots hp) hlen)
    (p.sched.map ZkFormal.NearV3.Sched.instOf) p.fwd hrec.2.1 (by simp only [List.length_map]; omega) hf hF
  rcases recv_src hH codecOwn.lt hf (by rw [codecOwn.tab]; exact codec_mem 4 (by decide))
      (by rw [Codec.i4_def]) (by rw [Codec.i4_def]) (by rw [m4]; exact Nat.one_ne_zero) with
    hpub | ⟨t', ht', r', hr', i', hi', hb', hs', hmsg, hm'⟩
  · exact absurd (pubCount_noside (sd := true) (by decide +kernel) _ _) hpub
  have key : ∀ t, t < nearAirV3.tables.length → t = T_UPS ∨
      (∀ i ∈ nearAirV3.tables[t]!.interactions, i.bus = B_S0F → i.send = false) := by decide +kernel
  rcases key t' ht' with e | hno
  · subst e
    have hc := row_send_pos (is := nearAirV3.tables[T_UPS]!.interactions) hr' hi' hb' hs' hm'
    rw [show nearAirV3.tables[T_UPS]!.interactions = isAt T_UPS from rfl,
      ups_count T _ _ _ (by decide +kernel)] at hc
    simp only [tcnt, ite_true] at hc
    obtain ⟨x, hx, hxe⟩ := List.mem_map.mp (List.count_pos_iff.mp hc)
    obtain ⟨s, hs, hxs⟩ := List.mem_flatMap.mp hx
    rw [show Sched.B_S0F = ZkFormal.NearV3.B_S0F from rfl, ups_s0fMsgs W.ups hs, List.mem_singleton] at hxs
    subst hxs
    rw [hmsg, msg4] at hxe
    have hcan := (W.ups.canon s hs).1 0
    have e := ofNat_list_inj (fun x hx => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl <;> exact hcan _)
      (fun x hx => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl <;> exact ZkFormal.Chacha.cv_lt _ _) hxe
    simp only [List.cons.injEq, and_true] at e
    exact ⟨s, hs, e.1, e.2.1, e.2.2⟩
  · rw [hno i' hi' hb'] at hs'; cases hs'

/-- **The codec's read of `0x0f`** for an instance `τ ≤ K`, against the record tree under the
head of `τ` (the tree `upsLink_holds` upserts into). -/
theorem codec_read {cb : NearSpec.Bytes} {h : NearSpecV3.Hint} {p : NearSpecV3.Prep} {oh : Nat}
    {tr : Trace Fp} {r : V3Records} (hp : NearSpecV3.prepD0 cb h = .ok p)
    (hsz : (ZkFormal.NearV3.Public.preparedBytes p oh).length < P)
    (hH : HoldsP nearAirV3 (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr)
    (T : V3RecordsTraffic (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr r)
    (W : V3RecordsWf (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r)
    {f : Nat} (hf : f < tr.height T_CODEC) (hF : cv tr T_CODEC f Codec.kF = 1)
    (hτ : cv tr T_CODEC f Codec.tau ≤ p.hdr.K) :
    (cv tr T_CODEC f Codec.pres = 1 ∧
      (fullTree (Rpost r.nodes r.values) (Vpost r.nodes r.values (fun i => toB (LinkVPost.pnOf r.accts i)))
          (headAt r.heads (cv tr T_CODEC f Codec.tau)).rid).find UpsSpec.key =
        some (some (valOf (Vpost r.nodes r.values (fun i => toB (LinkVPost.pnOf r.accts i)))
          (vpos (vid0 r.values) (cv tr T_CODEC f Codec.vid))))) ∨
    (cv tr T_CODEC f Codec.pres = 0 ∧ cv tr T_CODEC f Codec.vid = 0 ∧
      (fullTree (Rpost r.nodes r.values) (Vpost r.nodes r.values (fun i => toB (LinkVPost.pnOf r.accts i)))
          (headAt r.heads (cv tr T_CODEC f Codec.tau)).rid).find UpsSpec.key = some none) := by
  obtain ⟨s', hs', et, ep, ev⟩ := s0f_codec hp hsz hH T W hf hF
  obtain ⟨sv, -, H⟩ := LinkSched.upsLink_holds hp hsz hH T W
  obtain ⟨-, s, hs, hτs, -, F⟩ := H _ hτ
  have hC := rootChain_of hp hsz hH T W
  have e : s = s' := ups_tauDistinct hC s hs s' hs' (by rw [hτs, et])
  subst e
  rw [ep, ev] at F
  exact F

end LinkSchedCore

end ZkFormal.NearV3.Assembly

/-! ## The prepared scheduler contexts from `block` / `previous` only -/

namespace ZkFormal.NearV3.Assembly

open NearSpec NearSpecV3 Sched

private theorem mapError_ok_iff' {ε ε' α : Type} (f : ε → ε') (x : Except ε α) (a : α) :
    x.mapError f=.ok a ↔ x=.ok a := by cases x <;> simp [Except.mapError]

set_option maxHeartbeats 4000000 in
/-- `prepClaim_contexts` with only the two block facts of the execution (its proof is copied;
it uses nothing else of `NativeValid`). -/
theorem prepClaim_contexts_of {cb : Bytes} {pc : PrepC} {k : WalkD0} {m : MainExecutionV3}
    (hp : prepClaim cb=.ok pc) (hw : walkD0 cb=.ok k)
    (hmb : k.blks[k.b2i]? = some m.block) (hmp : k.blks[k.b2i + 1]? = some m.previous) :
    (schedulerContexts k m).mapM preparedScheduler=.ok pc.sched := by
  unfold prepClaim at hp
  repeat' (first
    | (obtain ⟨_, hs, hn⟩ := bind_ok hp; clear hp; have hp := hn; clear hn)
    | (split at hp)
    | (dsimp only at hp))
  all_goals try (cases hp; done)
  all_goals try (exfalso; exact throw_ne (by assumption))
  all_goals
    simp only [pure, Except.pure, Except.ok.injEq] at hp
    subst hp
    simp_all only [mapError_ok_iff', pure, Except.pure, Except.ok.injEq]
    unfold walkD0 at hw
    simp only [*, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hw
    repeat' (first
      | (have hh := hw; clear hw; obtain ⟨_, _, hw⟩ := bind_ok hh; clear hh)
      | (split at hw)
      | (dsimp only at hw))
    all_goals try (cases hw; done)
    all_goals try (exfalso; exact throw_ne (by assumption))
    all_goals
      simp only [pure, Except.pure, Except.ok.injEq] at hw
      subst hw
      expose_names
      have hb2 : w_22 = i_3 := by grind only
      have hslot : p_1.2 = w_30 := by
        rw [←hb2,heq_2] at heq_8
        simp only [Option.bind_some,heq_5,Option.some.injEq] at heq_8
        grind only
      unfold schedulerContexts MainExecutionV3.ctx preparedScheduler
      simp only [pure,Except.pure]
      grind only

/-- **`schedPub` of every scheduler context** from `prepD0`, `walkD0` and the execution's two
block facts (`prepD0_context_index` without `NativeValid`). -/
theorem prepD0_context_index_of {cb : Bytes} {hint : Hint} {p : Prep} {k : WalkD0} {m : MainExecutionV3}
    (hp : prepD0 cb hint=.ok p) (hw : walkD0 cb=.ok k)
    (hmb : k.blks[k.b2i]? = some m.block) (hmp : k.blks[k.b2i + 1]? = some m.previous)
    (i : Nat) (ctx : ApplyCtx) (hi : (schedulerContexts k m)[i]?=some ctx) :
    ∃sp, p.sched[i]?=some sp ∧ schedPub ctx=some sp := by
  obtain ⟨pc,hpc,hbody⟩ := bind_ok hp
  have h := prepClaim_contexts_of hpc hw hmb hmp
  rw [← prepBody_sched hbody] at h
  exact contexts_index h i ctx hi

end ZkFormal.NearV3.Assembly
