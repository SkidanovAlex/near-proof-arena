import ZkFormal.NearV3.Assembly.A9Air

/-!
# ZkFormal.NearV3.Assembly.A9Words — native words of a scheduler run vs. the AIR (L1), and `A9Link`

* `coreMid` — `coreOf` up to and including `processRequests` (the last RNG use);
  **`runMid_st`**: when the claim-only part `pubOf` of a run is `sp`, `runMid`'s state is
  `coreMid sp …` (the same steps); **`coreMid_lp`**: on a canonical previous state it is
  `processRequests` from the link-pass state `lpState` (as in `Sched.core_compose`);
* **`rngWords_rngAt`**: `rngWords (rngAt key K) = K`; **`rngWords_specSt`**: the spec state after the
  AIR's `m` rounds has drawn `lastK` words (`runL` keeps the generator);
* **`inst_words`** (per instance `τ` of `nearAirV3`): an instance block `(f, m)` with `tau = τ` such
  that every run whose claim-only part is `p.sched[τ]` and whose previous state is the codec's
  `prevOf tr T_CODEC τ` draws at most `lastK tr f m` words;
* **`a9Link_of_native`**: with the native alignment `A9Native` (each scheduler input of
  `schedInsD0` has public part `p.sched[τ]` and previous state `prevOf tr T_CODEC τ`), `A9Link`
  holds (`A9Air.a9_air`).
-/

namespace ZkFormal.NearV3.Assembly

namespace A9Words

open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Chacha
open NearSpecV3 NearSpecV3.Scheduler ZkFormal.NearV3.Sched

/-! ## `runMid` through the claim-only part -/

/-- `coreOf` up to and including `processRequests`. -/
def coreMid (ids : List Nat) (p : Params) (allowed : Array Bool) (reqs : List Req) (seed : NearSpec.Bytes)
    (prevState : Option NearSpec.Bytes) : Option St := do
  let prev ← match prevState with
    | none => some NearSpec.Bandwidth.State.initial
    | some b => NearSpec.Bandwidth.State.decode b
  let n := ids.length
  let links := List.range (n * n)
  let allow0 := prev.links.foldl (fun (a : Array Nat) la =>
      match indexOf ids la.sender, indexOf ids la.receiver with
      | some s, some r => a.set! (s * n + r) la.allowance
      | _, _ => a) (Array.replicate (n * n) 0)
  let st : St := ⟨Array.replicate n p.maxShardBandwidth, Array.replicate n p.maxShardBandwidth,
    allow0, Array.replicate (n * n) 0, Rng.ofSeed seed⟩
  let fair := p.maxShardBandwidth / n
  let st := { st with allowance := st.allowance.map fun a => Nat.min (Nat.min (a + fair) u64Max) p.maxAllowance }
  let st := links.foldl (fun st l => (tryGrant n allowed st l p.base).2) st
  processRequests n allowed st reqs

/-- **`runMid`'s state is `coreMid` of its claim-only part.** -/
theorem runMid_st {cfg : Config} {cc : CongestionConfig} {ids : List Nat} {prev : Option NearSpec.Bytes}
    {cong : List (Nat × CongestionInfo × Nat)} {req : List (Nat × List BandwidthRequest)}
    {seed : NearSpec.Bytes} {sp : SchedPub} (hp : pubOf cfg cc ids cong req seed = some sp) :
    (runMid cfg cc ids prev cong req seed).map Mid.st =
      coreMid sp.ids sp.params sp.allowed (convertRaw sp.values sp.params.base sp.ids sp.raw) sp.seed prev := by
  unfold pubOf at hp
  by_cases hn : ids.length = 0
  · simp [hn] at hp
  · cases hpc : Params.calculate cfg ids.length with
    | none => simp [hn, hpc] at hp
    | some p =>
      simp only [hn, hpc, Option.bind, ↓reduceIte, bind, Option.some.injEq] at hp
      subst hp
      show _ = coreMid ids p _ (convertRequests p ids req) seed prev
      unfold runMid coreMid
      cases prev with
      | none =>
        simp only [hn, hpc, Option.bind, ↓reduceIte, bind]
        generalize processRequests _ _ _ _ = r
        cases r <;> rfl
      | some b =>
        cases hd : NearSpec.Bandwidth.State.decode b with
        | none => simp only [hn, hpc, hd, Option.bind, ↓reduceIte, bind]; rfl
        | some st =>
          simp only [hn, hpc, hd, Option.bind, ↓reduceIte, bind]
          generalize processRequests _ _ _ _ = r
          cases r <;> rfl

/-- **`coreMid` on a canonical previous state** is `processRequests` from `lpState`. -/
theorem coreMid_lp (ids : List Nat) (hn : 1 ≤ ids.length) (hn64 : ids.length ≤ 64)
    (hids : ∀ x ∈ ids, x < 2 ^ 64)
    (p : Params) (hp : Params.calculate Config.pv86 ids.length = some p)
    (allowed : Array Bool) (hA : allowed.size = ids.length * ids.length)
    (reqs : List Req) (seed : NearSpec.Bytes)
    (prev : Option NearSpec.Bytes) (a0 : Nat → Nat) (h0 : NearSpec.Bytes) (hprev : PrevCanon ids prev a0 h0) :
    coreMid ids p allowed reqs seed prev =
      processRequests ids.length allowed (lpState ids p allowed a0 seed) reqs := by
  have hlp := linkPass_eq hn hp allowed (srcArr ids a0) hA (by simp [srcArr]) (Rng.ofSeed seed)
  simp only at hlp
  rcases hprev with ⟨rfl, ha, rfl⟩ | ⟨rfl, hh, ha⟩
  · unfold coreMid
    simp only [Option.bind_some, bind]
    generalize hF : List.foldl _ (Array.replicate _ 0) NearSpec.Bandwidth.State.initial.links = F
    have hFa : F = srcArr ids a0 := by
      rw [← hF]
      apply Array.ext
      · simp [srcArr, NearSpec.Bandwidth.State.initial]
      · intro i h1 h2
        simp only [srcArr, NearSpec.Bandwidth.State.initial, List.foldl_nil, Array.getElem_replicate,
          Array.getElem_map, List.getElem_toArray]
        split <;> simp [ha]
    subst hFa
    rw [hlp]
    rfl
  · unfold coreMid
    simp only []
    rw [decode_encode _ ?_ hh ?_]
    · simp only [Option.bind_some, bind]
      generalize hF : List.foldl _ (Array.replicate _ 0) (canonLinks ids a0) = F
      have hFa : F = srcArr ids a0 := by
        rw [← hF]; exact allow0_src ids a0
      subst hFa
      rw [hlp]
      rfl
    · intro la hla
      simp only [canonLinks, List.mem_map, List.mem_range] at hla
      obtain ⟨l, hl, rfl⟩ := hla
      have hpos : 0 < ids.length := hn
      have hs : l / ids.length < ids.length := (Nat.div_lt_iff_lt_mul hpos).2 hl
      have hr : l % ids.length < ids.length := Nat.mod_lt _ hpos
      have e1 : ids.getD (l / ids.length) 0 = ids[l / ids.length] := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hs]; rfl
      have e2 : ids.getD (l % ids.length) 0 = ids[l % ids.length] := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hr]; rfl
      refine ⟨?_, ?_, ha l⟩
      · show ids.getD (l / ids.length) 0 < 2 ^ 64
        rw [e1]; exact hids _ (List.getElem_mem hs)
      · show ids.getD (l % ids.length) 0 < 2 ^ 64
        rw [e2]; exact hids _ (List.getElem_mem hr)
    · simp only [canonLinks, List.length_map, List.length_range]
      have := Nat.mul_le_mul hn64 hn64
      omega

/-! ## Words of the AIR's rounds -/

theorem rngWords_rngAt (key : List Nat) (K : Nat) : rngWords (rngAt key K) = K := by
  unfold rngAt rngWords
  split
  · simp only [List.length_nil, Nat.sub_zero]; omega
  · simp only [List.length_drop, chachaBlock_length]; omega

theorem rngWords_ofSeed (seed : NearSpec.Bytes) : rngWords (Rng.ofSeed seed) = 0 := rfl

/-- The spec state after the AIR's `m` rounds has drawn `lastK` words. -/
theorem rngWords_specSt {tr : Trace Fp} {f m : Nat} (n : Nat) (allowed : Array Bool) (reqs : List Req)
    (hR : ∀ q ∈ reqs, q.incs.length < 64) (st : St) (hst : rngWords st.rng = 0) :
    rngWords (specSt n allowed reqs tr T_PROC f st m).rng = A9Air.lastK tr f m := by
  unfold A9Air.lastK
  cases m with
  | zero => simpa [specSt] using hst
  | succ k =>
    simp only [specSt, specRound, Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
    rw [(runL_facts n allowed reqs hR _ _ _ _ _).1]
    exact rngWords_rngAt _ _

/-! ## Per instance at `nearAirV3` -/

theorem pubOf_values {cfg : Config} {cc : CongestionConfig} {ids : List Nat}
    {cong : List (Nat × CongestionInfo × Nat)} {req : List (Nat × List BandwidthRequest)}
    {seed : NearSpec.Bytes} {sp : SchedPub} (hp : pubOf cfg cc ids cong req seed = some sp) :
    sp.values = requestValues sp.params := by
  unfold pubOf at hp
  by_cases hn : ids.length = 0
  · simp [hn] at hp
  · cases hpc : Params.calculate cfg ids.length with
    | none => simp [hn, hpc] at hp
    | some p =>
      simp only [hn, hpc, Option.bind, ↓reduceIte, bind, Option.some.injEq] at hp
      subst hp; rfl

section
open LinkSchedCore
variable {cb : NearSpec.Bytes} {h : NearSpecV3.Hint} {p : NearSpecV3.Prep} {oh : Nat}
  {tr : Trace Fp} {r : V3Records}

/-- **One instance**: an instance block `(f, m)` of `procV3` with `tau = τ` bounds the words of every
run with claim-only part `p.sched[τ]` on the codec's previous state. -/
theorem inst_words (hp : NearSpecV3.prepD0 cb h = .ok p)
    (hsz : (ZkFormal.NearV3.Public.preparedBytes p oh).length < ZkFormal.Algebra.P)
    (hH : HoldsP nearAirV3 (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr)
    (T : V3RecordsTraffic (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr r)
    (W : V3RecordsWf (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r)
    {τ : Nat} (hτ : τ < p.sched.length) :
    ∃ f m, cv tr T_PROC f Proc.tau = τ ∧ Proc.Inst tr T_PROC f m ∧
      ∀ (ids : List Nat) (cong : List (Nat × CongestionInfo × Nat))
        (req : List (Nat × List BandwidthRequest)) (seed : NearSpec.Bytes),
        pubOf Config.pv86 CongestionConfig.pv86 ids cong req seed = some p.sched[τ] →
        wordsDrawn Config.pv86 CongestionConfig.pv86 ids (prevOf tr T_CODEC τ) cong req seed ≤
          A9Air.lastK tr f m := by
  obtain ⟨f, m, fc, hf, hk, hc, hτf, Ib, -, -, -, -, H⟩ := schedCore_v3 hp hsz hH T W hτ
  obtain ⟨-, -, hprev, -⟩ := H
  have hlen : (ZkFormal.NearV3.Public.preparedBytes p oh).length < 256 ^ 4 := by unfold ZkFormal.Algebra.P at hsz; omega
  have hrec := ZkFormal.NearV3.Public.prepared_scheduler_index nearAirV3 oh rfl hp (prepD0_roots hp)
    (prepD0_source_roots hp) hlen
  have hlen33 := prepD0_len hp
  have hP := instOk_of hp
  have h256 : (p.sched.map instOf).length ≤ 256 := by rw [List.length_map]; omega
  have PL := proc_link''' hH schedOwn_v3 scanOwn_v3 opOwn_v3 codecOwn sparOwn pubbOwn_v3 initOwn_v3
    (ZkFormal.NearV3.Public.prepared_pubIdx nearAirV3 p oh rfl (prepD0_roots hp) (prepD0_source_roots hp) hlen)
    (p.sched.map instOf) p.fwd hrec.2.1 hrec.1 h256 hP hf hk hc Ib
  have hP0 : (p.sched.map instOf).getD τ instD = instOf p.sched[τ] := getD_map_instOf _ hτ
  have PO : InstOk (instOf p.sched[τ]) := by
    have := hP τ (by rw [List.length_map]; exact hτ); rwa [hP0] at this
  have hτc : ZkFormal.Chacha.cv tr T_PROC f Proc.tau = τ := hτf
  simp only [hτc, hP0] at PL
  have hpr := PL.2.2.2.2.2.2
  refine ⟨f, m, hτf, Ib, ?_⟩
  intro ids cong req seed hpub
  unfold wordsDrawn
  cases hm : runMid Config.pv86 CongestionConfig.pv86 ids (prevOf tr T_CODEC τ) cong req seed with
  | none => exact Nat.zero_le _
  | some md =>
    have e := runMid_st (prev := prevOf tr T_CODEC τ) hpub
    rw [hm, Option.map_some] at e
    have hreq : convertRaw p.sched[τ].values p.sched[τ].params.base p.sched[τ].ids p.sched[τ].raw =
        reqsOf (instOf p.sched[τ]) := by
      rw [pubOf_values hpub, convertRaw_eq_convRaw (ids := p.sched[τ].ids) (p := p.sched[τ].params) PO.n1 PO.params]
      unfold reqsOf
      rw [show (instOf p.sched[τ]).n = p.sched[τ].ids.length from rfl,
        show (instOf p.sched[τ]).params = p.sched[τ].params from rfl, convRaw_instOf]
    rw [hreq, coreMid_lp p.sched[τ].ids PO.n1 PO.n64 PO.ids64 p.sched[τ].params PO.params
      p.sched[τ].allowed PO.asz _ _ _ _ _ hprev] at e
    have e2 := e.trans hpr
    simp only [Option.some.injEq] at e2
    simp only
    rw [e2]
    exact Nat.le_of_eq (rngWords_specSt _ _ _
      (fun q hq => (reqsOf_ok (ScanPubOk.of_pv86 PO.params PO.n64 PO.raw) q hq).2) _ rfl)

end

/-! ## `A9Link` from the native alignment -/

/-- **The native alignment** (open): every scheduler input of `schedInsD0` is the claim-only part
`p.sched[τ]` of instance `τ` on the codec's previous state `prevOf tr T_CODEC τ`, and there are at
most `|p.sched|` of them. -/
def A9Native (cb w : NearSpec.Bytes) (p : NearSpecV3.Prep) (tr : Trace Fp) : Prop :=
  ∀ l, schedInsD0 cb w = .ok l → l.length ≤ p.sched.length ∧
    ∀ τ (hτ : τ < l.length) (hτ' : τ < p.sched.length),
      pubOf Config.pv86 CongestionConfig.pv86 l[τ].shardIds
          (l[τ].statuses.map fun (s, c, m) => (s, toCI c, m))
          (l[τ].requests.map fun (s, rs) => (s, rs.map fun r => ⟨r.toShard, r.bitmap⟩))
          l[τ].prevBlockHash = some p.sched[τ] ∧
        l[τ].prev = prevOf tr T_CODEC τ

theorem sum_le_idx {α : Type} (g : α → Nat) : ∀ (l : List α) (c : Nat → Nat),
    (∀ τ (hτ : τ < l.length), g l[τ] ≤ c τ) →
    (l.map g).sum ≤ ((List.range l.length).map c).sum
  | [], _, _ => by simp
  | a :: l, c, h => by
    have h0 := h 0 (by simp)
    have ih := sum_le_idx g l (fun τ => c (τ + 1)) (fun τ hτ => h (τ + 1) (by simp; omega))
    rw [List.length_cons, List.range_succ_eq_map]
    simp only [List.map_cons, List.sum_cons, List.map_map]
    simp only [List.getElem_cons_zero] at h0
    exact Nat.add_le_add h0 ih

section
variable {cb : NearSpec.Bytes} {h : NearSpecV3.Hint} {p : NearSpecV3.Prep} {oh : Nat}
  {tr : Trace Fp} {r : V3Records}

/-- **`A9Link` from the native alignment.** -/
theorem a9Link_of_native (hp : NearSpecV3.prepD0 cb h = .ok p)
    (hsz : (ZkFormal.NearV3.Public.preparedBytes p oh).length < ZkFormal.Algebra.P)
    (hH : HoldsP nearAirV3 (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr)
    (T : V3RecordsTraffic (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr r)
    (W : V3RecordsWf (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r)
    {w : NearSpec.Bytes} (hN : A9Native cb w p tr) : A9Link cb w tr := by
  unfold A9Link chachaWords
  cases hs : schedInsD0 cb w with
  | error _ => exact Nat.zero_le _
  | ok l =>
    obtain ⟨hlen, hal⟩ := hN l hs
    have hI := fun τ (hτ : τ < p.sched.length) => inst_words hp hsz hH T W hτ
    let F : Nat → Nat := fun τ => if hτ : τ < p.sched.length then Classical.choose (hI τ hτ) else 0
    let M : Nat → Nat := fun τ =>
      if hτ : τ < p.sched.length then Classical.choose (Classical.choose_spec (hI τ hτ)) else 0
    have hFM : ∀ τ (hτ : τ < p.sched.length), cv tr T_PROC (F τ) Proc.tau = τ ∧
        Proc.Inst tr T_PROC (F τ) (M τ) ∧
        ∀ (ids : List Nat) (cong : List (Nat × CongestionInfo × Nat))
          (req : List (Nat × List BandwidthRequest)) (seed : NearSpec.Bytes),
          pubOf Config.pv86 CongestionConfig.pv86 ids cong req seed = some p.sched[τ] →
          wordsDrawn Config.pv86 CongestionConfig.pv86 ids (prevOf tr T_CODEC τ) cong req seed ≤
            A9Air.lastK tr (F τ) (M τ) := by
      intro τ hτ
      simp only [F, M, hτ, ↓reduceDIte]
      exact Classical.choose_spec (Classical.choose_spec (hI τ hτ))
    have h1 : (l.map schedWords).sum ≤
        ((List.range l.length).map fun τ => A9Air.lastK tr (F τ) (M τ)).sum := by
      apply sum_le_idx
      intro τ hτ
      have hτ' : τ < p.sched.length := by omega
      obtain ⟨hpub, hprev⟩ := hal τ hτ hτ'
      unfold schedWords
      rw [hprev]
      exact (hFM τ hτ').2.2 _ _ _ _ hpub
    have h2 : ((List.range l.length).map fun τ => A9Air.lastK tr (F τ) (M τ)).sum ≤
        ((List.range p.sched.length).map fun τ => A9Air.lastK tr (F τ) (M τ)).sum := by
      rw [show p.sched.length = l.length + (p.sched.length - l.length) by omega, A9Air.sum_range_add]
      exact Nat.le_add_right _ _
    exact Nat.le_trans h1 (Nat.le_trans h2
      (A9Air.a9_air hH (fun τ hτ => ⟨(hFM τ hτ).1, (hFM τ hτ).2.1⟩)))

/-- **`RestFieldsV3.chachaWords` from the native alignment.** -/
theorem chachaWords_of_native (hp : NearSpecV3.prepD0 cb h = .ok p)
    (hsz : (ZkFormal.NearV3.Public.preparedBytes p oh).length < ZkFormal.Algebra.P)
    (hH : HoldsP nearAirV3 (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr)
    (T : V3RecordsTraffic (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr r)
    (W : V3RecordsWf (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r)
    {w : NearSpec.Bytes} (hN : A9Native cb w p tr) : chachaWords cb w ≤ W0 :=
  chachaWords_le_of_link hH (a9Link_of_native hp hsz hH T W hN)

end

end A9Words

end ZkFormal.NearV3.Assembly
