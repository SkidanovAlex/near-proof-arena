import ZkFormal.NearV3.Sched.Link.GridLink
import ZkFormal.NearV3.Assembly.LinkSched

/-!
# ZkFormal.NearV3.Assembly.LinkSchedCore — the scheduler core of `nearAirV3`

The Sched lane's `schedCore_sound''` (`Sched/Link/GridLink.lean`) is generic in the AIR, under
decidable ownership conditions.  One of them, `ShaOwn AP tsha` ("table `tsha` is *the* SHA table,
the only `DIGEST` sender"), is **false** for `nearAirV3`, which has two SHA instances
(`T_SHA_T = 0`, `T_SHA_R = 1`, both `DIGEST` senders).  `ShaOwn` is used only in `codec_digest`
(the provider of a codec digest is that SHA table).

* **`ShaOwn2 AP t1 t2`**: tables `t1`, `t2` are the SHA table, the only `DIGEST` senders;
* **`codec_digest2`**: `codec_digest` with the provider either SHA instance (it is located by
  `recv_src`, then L5's digest contract is applied to that instance);
* `codec_hash2`, `sched_post2`, `schedCore_sound2`, `schedCore_sound2'`, **`schedCore_sound2''`**:
  the Sched lane's proofs verbatim (copied; the Sched modules are untouched) with
  `ShaOwn` → `ShaOwn2`;
* **`schedCore_v3`**: `schedCore_sound2''` at `nearAirV3` (`tp = T_PROC`, `tcd = T_CODEC`, …,
  `fwd = p.fwd`) with every ownership condition decided, the kind registry `ShaKind` derived from
  the records' `BYTES` kinds (`shaKind_v3`), and the public records from
  `prepared_scheduler_index`: only `HoldsP` + the views remain.
-/

namespace ZkFormal.NearV3.Sched

open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Chacha ZkFormal.Chacha.Table.E
open NearSpecV3 NearSpecV3.Scheduler

/-- Tables `t1`, `t2` are the SHA table (L5) on `BYTES` / `DIGEST`, the only `DIGEST` senders; no
public `DIGEST` segment. -/
structure ShaOwn2 (AP : AirP) (t1 t2 : Nat) : Prop where
  lt1 : t1 < AP.tables.length
  tab1 : AP.tables[t1]! = ZkFormal.Sha.Table.table ZkFormal.Near.B_BYTES ZkFormal.Near.B_DIGEST
  lt2 : t2 < AP.tables.length
  tab2 : AP.tables[t2]! = ZkFormal.Sha.Table.table ZkFormal.Near.B_BYTES ZkFormal.Near.B_DIGEST
  dig : ∀ t, t < AP.tables.length → t ≠ t1 → t ≠ t2 → ∀ i ∈ AP.tables[t]!.interactions,
    i.bus = ZkFormal.Near.B_DIGEST → i.send = false
  pubDig : ∀ seg ∈ AP.pubSegs, seg.bus ≠ ZkFormal.Near.B_DIGEST

section
variable {AP : AirP} {pub : List Fp} {tr : Trace Fp}

/-- **The hash input and digest of a codec block.** -/
theorem codec_digest2 (hH : HoldsP AP pub tr) {tc tsha tsha2 : Nat} (O : CodecValOwn AP tc) (SO : SparOwn AP)
    (SH : ShaOwn2 AP tsha tsha2) (SK : ShaKind AP pub tr tc)
    (I : PubIdx AP pub Fp.ofNat) (Ps : List InstPub) (fwd : List (Nat × Nat))
    (hrec : I.recs B_SPAR true = (render Ps fwd).par) (h256 : Ps.length ≤ 256)
    {f : Nat} (hf : f < tr.height tc) (hF : cv tr tc f Codec.kF = 1) :
    (∀ j, j < 64 → Codec.shaByte tr tc f j < 256) ∧
      (List.range 32).map (fun j => UInt8.ofNat (cv tr tc (f + 5 + 24 * cv tr tc f Codec.NN) (Codec.reg j))) =
        ArenaCore.sha256 ((List.range 64).map fun j => UInt8.ofNat (Codec.shaByte tr tc f j)) := by
  have hL := codec_local hH O
  have hH22 := codec_h22 hH O
  have hlen : Ps.length < 2013265921 := by omega
  have hτ := (first_par hH O SO I Ps fwd hrec hlen hf hF).1
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hlt, -⟩ := Codec.codec_block hL hH22 hf hF
  obtain ⟨-, -, -, -, m3, msg3, -⟩ := Codec.codec_post hL hH22 hf hF
  generalize hz : f + 5 + 24 * cv tr tc f Codec.NN = z at m3 msg3 hlt
  have hzh : z < tr.height tc := by omega
  -- the digest provider
  obtain ⟨ts, hlts, htabs, d, hd, hdm, hmsg⟩ : ∃ ts, ts < AP.tables.length ∧
      AP.tables[ts]! = ZkFormal.Sha.Table.table ZkFormal.Near.B_BYTES ZkFormal.Near.B_DIGEST ∧
      ∃ d, d < tr.height ts ∧ tr.cell ts d ZkFormal.Sha.Layout.colDmult = 1 ∧
      ZkFormal.Near.shaDigestI.msgVal tr ts d pub = (Codec.interactions[3]!).msgVal tr tc z pub := by
    rcases recv_src hH O.lt hzh (by rw [O.tab]; exact codec_mem 3 (by decide))
        (by rw [Codec.i3_def]) (by rw [Codec.i3_def]) (by rw [m3]; exact Nat.one_ne_zero) with
      hp | ⟨t', ht', r', hr', i', hi', hb', hs', hmsg, hm'⟩
    · exact absurd (pubCount_zero (s := true) (fun seg h1 h2 => absurd h2 (SH.pubDig seg h1)) _) hp
    · have htab : AP.tables[t']! = ZkFormal.Sha.Table.table ZkFormal.Near.B_BYTES ZkFormal.Near.B_DIGEST := by
        by_cases h1 : t' = tsha
        · rw [h1]; exact SH.tab1
        by_cases h2 : t' = tsha2
        · rw [h2]; exact SH.tab2
        have := SH.dig t' ht' h1 h2 i' hi' hb'; rw [this] at hs'; cases hs'
      rw [htab] at hi'
      rcases ZkFormal.Near.sha_mem hi' with ⟨-, h⟩ | e
      · rw [h] at hs'; cases hs'
      · subst e
        exact ⟨t', ht', htab, r', hr', sha_dmult hm', hmsg⟩
  have hLs : ZkFormal.Sha.ShaLocal tr ts pub :=
    { log_ge := (hH.logBound ts hlts).1
      log_le := by have := (hH.logBound ts hlts).2; rw [← tables_get hlts, htabs] at this; exact this
      constr := fun r hr e he => by
        have := local_of_holdsP hH hlts r hr e; rw [htabs] at this; exact this he }
  obtain ⟨msg, dg, -, hdg, hmsg16, hbytes⟩ :=
    ZkFormal.Sha.sha_digest_contract_closed hLs ZkFormal.Near.B_BYTES ZkFormal.Near.B_DIGEST hd hdm
  rw [show ZkFormal.Near.shaDigestI = (ZkFormal.Sha.Table.interactions ZkFormal.Near.B_BYTES
    ZkFormal.Near.B_DIGEST)[16]! from rfl, hmsg16, msg3] at hmsg
  simp only [List.cons_append, List.map_cons, List.cons.injEq, List.nil_append] at hmsg
  obtain ⟨eid, elen, edg⟩ := hmsg
  have hid : 11 + 16 * cv tr tc f Codec.tau < 2013265921 := by omega
  -- every byte of the SHA message comes from τ's codec block
  have src : ∀ i, i < msg.length → ∃ j, j < 64 ∧ Fp.ofNat j = Fp.ofNat i ∧
      Fp.ofNat (Codec.shaByte tr tc f j) = Fp.ofNat (msg[i]!).toNat := by
    intro i hi
    obtain ⟨rr, hrr, q, hq, hfq, hmq⟩ := hbytes i hi
    obtain ⟨hmem, hbus, hsend, -⟩ := ZkFormal.Near.sha_is_bytes q hq
    rcases recv_src hH hlts hrr (by rw [htabs]; exact hmem) hbus hsend (sha_fmult hq hfq) with
      hp | ⟨t', ht', r', hr', i', hi', hb', hs', hmsg', hm'⟩
    · exfalso
      rw [hmq] at hp
      have := SK.pubs _ hp _ rfl
      rw [eid, toNat_ofNat_lt' hid] at this
      omega
    · by_cases htc : t' = tc
      · rw [htc] at hi' hm' hmsg' hr'
        rw [O.tab] at hi'
        have e2 := Codec.bytes_send_i hi' hb' hs'
        subst e2
        obtain ⟨f', j, hf', hF', hj, rfl, hmj⟩ := Codec.bytes_row hL hH22 hr' hm'
        rw [hmj, hmq] at hmsg'
        simp only [List.map_cons, List.map_nil, List.cons.injEq] at hmsg'
        obtain ⟨a1, a2, a3, -⟩ := hmsg'
        have hτ' := (first_par hH O SO I Ps fwd hrec hlen hf' hF').1
        rw [eid] at a1
        have := ofNat_inj' (by omega) hid a1
        have ef : f' = f := block_unique hH O SO I Ps fwd hrec hlen hf' hF' hf hF (by omega)
        subst ef
        exact ⟨j, hj, a2, a3⟩
      · exfalso
        have := SK.tabs t' ht' htc r' hr' i' hi' hb' hs' hm' _ (by rw [hmsg', hmq]; rfl)
        rw [eid, toNat_ofNat_lt' hid] at this
        omega
  -- the length is 64
  have hle : msg.length ≤ 64 := by
    apply Nat.le_of_not_lt; intro h
    obtain ⟨j, hj, hji, -⟩ := src 64 h
    have := ofNat_inj' (by omega) (by omega) hji; omega
  have hml : msg.length = 64 := ofNat_inj' (by omega) (by omega) elen
  -- the bytes
  have hb : ∀ i, i < 64 → Codec.shaByte tr tc f i = (msg[i]!).toNat := by
    intro i hi
    obtain ⟨j, hj, hji, hv⟩ := src i (by omega)
    have := ofNat_inj' (by omega) (by omega) hji; subst this
    exact ofNat_inj' (by unfold Codec.shaByte; split <;> exact cv_lt _ _)
      (by have := (msg[j]!).toNat_lt; omega) hv
  have hmsgEq : msg = (List.range 64).map fun j => UInt8.ofNat (Codec.shaByte tr tc f j) := by
    apply List.ext_getElem (by simp [hml])
    intro i h1 h2
    simp only [List.getElem_map, List.getElem_range]
    rw [hb i (by omega)]
    rw [getElem!_pos msg i h1]
    exact (UInt8.ofNat_toNat).symm
  refine ⟨fun j hj => by rw [hb j hj]; exact (msg[j]!).toNat_lt, ?_⟩
  rw [← hmsgEq, ← hdg]
  -- the digest bytes
  have hdl : dg.length = 32 := by rw [hdg]; exact ArenaCore.sha256_length _
  apply List.ext_getElem (by simp [hdl])
  intro j h1 h2
  simp only [List.length_map, List.length_range] at h1
  have := congrArg (fun L => L[j]?) edg
  simp only [List.getElem?_map, List.getElem?_range h1, List.getElem?_eq_getElem h2, Option.map_some,
    Option.some.injEq] at this
  have e := ofNat_inj' (by have := (dg[j]).toNat_lt; omega) (cv_lt _ _) this
  simp only [List.getElem_map, List.getElem_range]
  rw [← e]
  exact UInt8.ofNat_toNat


/-- **The post sanity hash.** -/
theorem codec_hash2 (hH : HoldsP AP pub tr) {tc tsha tsha2 : Nat} (O : CodecValOwn AP tc) (SO : SparOwn AP)
    (SH : ShaOwn2 AP tsha tsha2) (SK : ShaKind AP pub tr tc) (PB : PubbOwn AP)
    (I : PubIdx AP pub Fp.ofNat) (Ps : List InstPub) (fwd : List (Nat × Nat))
    (hrecP : I.recs B_SPAR true = (render Ps fwd).par) (hrecB : I.recs B_SPUBB true = (render Ps fwd).pubb)
    (h256 : Ps.length ≤ 256)
    {f : Nat} (hf : f < tr.height tc) (hF : cv tr tc f Codec.kF = 1)
    (hash32 : (Ps.getD (cv tr tc f Codec.tau) instD).ash.length = 32) :
    (∀ j, j < 64 → Codec.shaByte tr tc f j < 256) ∧
      (List.range 32).map (fun j => UInt8.ofNat (cv tr tc (f + 5 + 24 * cv tr tc f Codec.NN) (Codec.reg j))) =
        NearSpec.sha256 (h0Of tr tc (cv tr tc f Codec.tau) ++ (Ps.getD (cv tr tc f Codec.tau) instD).ash) := by
  have hlen : Ps.length < 2013265921 := by omega
  obtain ⟨hb, hd⟩ := codec_digest2 hH O SO SH SK I Ps fwd hrecP h256 hf hF
  refine ⟨hb, ?_⟩
  rw [hd]
  show ArenaCore.sha256 _ = ArenaCore.sha256 _
  congr 1
  rw [(pre_block hH O SO I Ps fwd hrecP hlen hf hF).2, Codec.rowBytes_map]
  apply List.ext_getElem (by rw [List.length_append, hash32]; simp)
  intro i h1 h2
  simp only [List.length_map, List.length_range] at h1
  simp only [List.getElem_map, List.getElem_range]
  by_cases hi : i < 32
  · rw [List.getElem_append_left (by simp; exact hi)]
    simp only [List.getElem_map, List.getElem_range]
    unfold Codec.shaByte; rw [if_pos hi]
  · rw [List.getElem_append_right (by simp; omega)]
    simp only [List.length_map, List.length_range]
    have := codec_ash hH O PB I Ps fwd hrecB hlen hf hF (j := i - 32) (by omega)
    rw [show 32 + (i - 32) = i by omega] at this
    rw [this, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [hash32]; omega),
      Option.getD_some]
    exact UInt8.ofNat_toNat


/-- **The post bytes of instance τ are the scheduler core's new state.** -/
theorem sched_post2 {tp tm tcmp ts tch tg tsd tcd tsha tsha2 : Nat} {Ps : List InstPub}
    (C : InitCtx AP pub tr tp tm tcmp ts tch tg tsd tcd Ps) (PB : PubbOwn AP) (DO : SdlOwn AP tcd)
    (SH : ShaOwn2 AP tsha tsha2) (SK : ShaKind AP pub tr tcd)
    (I : PubIdx AP pub Fp.ofNat) (fwd : List (Nat × Nat))
    (hrecP : I.recs B_SPAR true = (render Ps fwd).par) (hrecB : I.recs B_SPUBB true = (render Ps fwd).pubb)
    (hrecD : I.recs B_SDL true = (render Ps fwd).dlSend)
    (hsame : ∀ τ, τ < Ps.length → (Ps.getD τ instD).ids = (Ps.getD 0 instD).ids)
    (hash32 : ∀ τ, τ < Ps.length → (Ps.getD τ instD).ash.length = 32)
    {f m : Nat} (hf : f < tr.height tp) (hk : cv tr tp f Proc.kK = 1) (hc : cv tr tp f Proc.kc = 0)
    (Ib : Proc.Inst tr tp f m) :
    let τ := cv tr tp f Proc.tau
    let P := Ps.getD τ instD
    let stF := specSt P.ids.length P.allowed (reqsOf P) tr tp f
      (lpState P.ids P.params P.allowed (codecA0 tr tcd τ) P.seed) m
    (∀ x ∈ svOf tr tcd τ, x < 256) ∧
    (svOf tr tcd τ).map UInt8.ofNat =
      NearSpec.Bandwidth.State.encode
        ⟨canonLinks P.ids (fun l => stF.allowance[l]!), NearSpec.sha256 (h0Of tr tcd τ ++ P.ash)⟩ := by
  intro τ P stF
  have hH := C.hH
  have h256 := C.h256
  have hlen : Ps.length < 2013265921 := by omega
  have hL := codec_local hH C.OC
  have hH22 := codec_h22 hH C.OC
  obtain ⟨hτ, M⟩ := memCtx_of C PB I fwd hrecP hrecB hf hk hc Ib
  obtain ⟨fc, hfc, hF, hτc⟩ := C.codec_exists I fwd hrecP hτ
  have PO := C.hP _ hτ
  have P0 := C.hP 0 (by omega)
  obtain ⟨-, -, hNN, -⟩ := codec_hdr hH C.OC C.SO I Ps fwd hrecP h256 hfc hF (by rw [hτc]; exact PO)
  rw [hτc] at hNN
  have hsv := svOf_block hH C.OC C.SO I Ps fwd hrecP hlen hfc hF
  rw [hτc] at hsv
  -- bytes
  have hbytes : ∀ x ∈ svOf tr tcd τ, x < 256 := by
    rw [hsv]; intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
    have hi' := List.mem_range.1 hi
    obtain ⟨P1, -⟩ := Codec.codec_post hL hH22 hfc hF
    obtain ⟨m1, -⟩ := P1 i (by omega)
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hlt, -⟩ := Codec.codec_block hL hH22 hfc hF
    have hrow : fc + i < tr.height tcd := by omega
    have he := Codec.encG_eval _ (mult1_enc (by rw [m1]; exact Nat.one_ne_zero)) hL hrow
    exact (Codec.bytes hL hrow he).2.1
  refine ⟨hbytes, ?_⟩
  rw [hsv, List.map_map]
  have e1 : ((List.range (37 + 24 * cv tr tcd fc Codec.NN)).map
      (UInt8.ofNat ∘ fun i => cv tr tcd (fc + i) Codec.bpost)) =
      Codec.rowBytes tr tcd Codec.bpost fc (37 + 24 * cv tr tcd fc Codec.NN) := by
    rw [Codec.rowBytes_map]; rfl
  rw [e1, Codec.codec_post_encode hL hH22 hfc hF]
  have hh := (codec_hash2 hH C.OC C.SO SH SK PB I Ps fwd hrecP hrecB h256 hfc hF
    (by rw [hτc]; exact hash32 _ hτ)).2
  rw [hτc] at hh
  rw [hh]
  congr 2
  -- the links
  unfold Codec.postLinks canonLinks
  rw [hNN, InstPub.n]
  apply List.map_congr_left
  intro k hk
  have hk' := List.mem_range.1 hk
  have hkN : k < cv tr tcd fc Codec.NN := by rw [hNN, InstPub.n]; exact hk'
  have hid := rowLE_idByte (ids := P.ids) (r := fc + 5 + 24 * k) (k := k)
    (by intro x hx; exact PO.ids64 x hx) (fun o ho => by
      rw [hsame _ hτ]
      exact codec_ids hH C.OC C.SO DO I Ps fwd hrecP hrecD h256 P0.n64 _ fc hfc hF rfl k hkN o ho)
  rw [hid.1, hid.2]
  have ha := codec_afin M C.OC hfc hF hτc (by rw [hNN]) hk'
  rw [ha]
  rfl


/-- **`schedCore_sound`.** -/
theorem schedCore_sound2 (hH : HoldsP AP pub tr) {tp tm tcmp ts tch tg tsd tcd tsha tsha2 : Nat}
    -- ownership (decidable on the final AIR)
    (O : SchedOwn AP tp tm tcmp ts tch tg) (OS : ScanOwn AP tsd tp) (OO : OpOwn AP tp tsd tcd)
    (OC : CodecValOwn AP tcd) (SO : SparOwn AP) (PB : PubbOwn AP) (IO : InitOwn AP tcd tsd)
    (DO : SdlOwn AP tcd) (PR : PubbRecv AP tp tcd) (SH : ShaOwn2 AP tsha tsha2)
    -- the kind registry (cross-lane)
    (SK : ShaKind AP pub tr tcd)
    -- the prepared statement and the public records (`PubIdx`, R1)
    {cb : NearSpec.Bytes} {hint : Hint} {p : Prep} (hprep : prepD0 cb hint = .ok p)
    (I : PubIdx AP pub Fp.ofNat) (fwd : List (Nat × Nat))
    (hrecP : I.recs B_SPAR true = (render (p.sched.map instOf) fwd).par)
    (hrecB : I.recs B_SPUBB true = (render (p.sched.map instOf) fwd).pubb)
    (hrecD : I.recs B_SDL true = (render (p.sched.map instOf) fwd).dlSend)
    {τ : Nat} (hτ : τ < p.sched.length) :
    let sp := p.sched[τ]
    let n := sp.ids.length
    ∃ f m, f < tr.height tp ∧ cv tr tp f Proc.kK = 1 ∧ cv tr tp f Proc.kc = 0 ∧
      cv tr tp f Proc.tau = τ ∧ Proc.Inst tr tp f m ∧
      let stF := specSt n sp.allowed (reqsOf (instOf sp)) tr tp f
        (lpState sp.ids sp.params sp.allowed (codecA0 tr tcd τ) sp.seed) m
      let g := gridGrants n sp.allowed stF.senderBudget stF.receiverBudget
        (sordOf n sp.allowed stF.senderBudget) (rordOf n sp.allowed stF.receiverBudget)
      runCore sp (prevOf tr tcd τ) = some
        ⟨(svOf tr tcd τ).map UInt8.ofNat,
          (List.range (n * n)).map (fun l => ((sp.ids.getD (l / n) 0, sp.ids.getD (l % n) 0),
            stF.granted[l]! + (g[l]!).getD 0)),
          sp.params⟩ ∧
      (∀ x ∈ svOf tr tcd τ, x < 256) ∧
      PrevCanon sp.ids (prevOf tr tcd τ) (codecA0 tr tcd τ) (h0Of tr tcd τ) ∧
      (∀ l, l < n * n → stF.granted[l]! + (g[l]!).getD 0 ≤ 4500000) := by
  intro sp n
  -- the `prepD0` facts
  have hlen33 := prepD0_len hprep
  have hP := instOk_of hprep
  have h256 : (p.sched.map instOf).length ≤ 256 := by rw [List.length_map]; omega
  have hlen : (p.sched.map instOf).length < 2013265921 := by omega
  have hτ' : τ < (p.sched.map instOf).length := by rw [List.length_map]; exact hτ
  have hsame : ∀ τ', τ' < (p.sched.map instOf).length →
      ((p.sched.map instOf).getD τ' instD).ids = ((p.sched.map instOf).getD 0 instD).ids := by
    obtain ⟨ids, hids⟩ := prepD0_ids hprep
    intro τ' h'
    rw [List.length_map] at h'
    rw [getD_map_instOf _ h', getD_map_instOf _ (by omega)]
    show p.sched[τ'].ids = p.sched[0].ids
    rw [hids _ (List.getElem_mem h'), hids _ (List.getElem_mem (by omega))]
  have hash32 : ∀ τ', τ' < (p.sched.map instOf).length → ((p.sched.map instOf).getD τ' instD).ash.length = 32 := by
    intro τ' h'
    rw [List.length_map] at h'
    rw [getD_map_instOf _ h']
    exact prepD0_ash hprep _ (List.getElem_mem h')
  have hvals := prepD0_values hprep _ (List.getElem_mem hτ)
  have S := prepD0_sched hprep _ (List.getElem_mem hτ)
  have C : InitCtx AP pub tr tp tm tcmp ts tch tg tsd tcd (p.sched.map instOf) :=
    ⟨hH, O, OS, OO, OC, SO, IO, h256, hP⟩
  have hP0 : (p.sched.map instOf).getD τ instD = instOf sp := getD_map_instOf _ hτ
  -- the process block
  obtain ⟨f, m, hf, hk, hc, hτf, Ib⟩ := proc_exists hH O OC PB PR I _ fwd hrecB hlen hτ'
  refine ⟨f, m, hf, hk, hc, hτf, Ib, ?_⟩
  intro stF g
  -- the previous state
  have hprev := codec_prevCanon C DO I fwd hrecP hrecD hsame hτ'
  rw [hP0] at hprev
  -- the core
  have hcore := proc_core''' hH O OS OO OC SO PB IO I _ fwd hrecP hrecB h256 hP hf hk hc Ib
    (prevOf tr tcd τ) (h0Of tr tcd τ) (by rw [hτf, hP0]; exact hprev)
  have hpost := sched_post2 C PB DO SH SK I fwd hrecP hrecB hrecD hsame hash32 hf hk hc Ib
  have hlink := proc_link''' hH O OS OO OC SO PB IO I _ fwd hrecP hrecB h256 hP hf hk hc Ib
  simp only [hτf, hP0] at hcore hpost hlink
  obtain ⟨hbytes, hpost⟩ := hpost
  obtain ⟨hsim, -⟩ := hlink
  have hG := (core_granted sp.ids S.n1 sp.params S.params sp.allowed (prepD0_asz hprep _ (List.getElem_mem hτ))
    (reqsOf (instOf sp)) sp.seed (codecA0 tr tcd τ) _ _ _ _ hsim).2
  refine ⟨?_, hbytes, hprev, fun l hl => Nat.le_trans (Nat.le_of_eq (hG l hl).1.symm) (hG l hl).2⟩
  rw [runCore_instOf sp S.n1 S.params hvals, hcore, hpost]
  congr 2
  apply List.map_congr_left
  intro l hl
  exact congrArg (Prod.mk _) (hG l (List.mem_range.1 hl)).1


/-- **`schedCore_sound'`.** -/
theorem schedCore_sound2' (hH : HoldsP AP pub tr) {tp tm tcmp ts tch tg tsd tcd tsha tsha2 : Nat}
    -- ownership (decidable on the final AIR)
    (O : SchedOwn AP tp tm tcmp ts tch tg) (OS : ScanOwn AP tsd tp) (OO : OpOwn AP tp tsd tcd)
    (OC : CodecValOwn AP tcd) (SO : SparOwn AP) (PB : PubbOwn AP) (IO : InitOwn AP tcd tsd)
    (DO : SdlOwn AP tcd) (PR : PubbRecv AP tp tcd) (SH : ShaOwn2 AP tsha tsha2)
    -- the kind registry (cross-lane)
    (SK : ShaKind AP pub tr tcd)
    -- the prepared statement and the public records (`PubIdx`, R1)
    {cb : NearSpec.Bytes} {hint : Hint} {p : Prep} (hprep : prepD0 cb hint = .ok p)
    (I : PubIdx AP pub Fp.ofNat) (fwd : List (Nat × Nat))
    (hrecP : I.recs B_SPAR true = (render (p.sched.map instOf) fwd).par)
    (hrecB : I.recs B_SPUBB true = (render (p.sched.map instOf) fwd).pubb)
    (hrecD : I.recs B_SDL true = (render (p.sched.map instOf) fwd).dlSend)
    {τ : Nat} (hτ : τ < p.sched.length) :
    let sp := p.sched[τ]
    let n := sp.ids.length
    ∃ f m fc, f < tr.height tp ∧ cv tr tp f Proc.kK = 1 ∧ cv tr tp f Proc.kc = 0 ∧
      cv tr tp f Proc.tau = τ ∧ Proc.Inst tr tp f m ∧
      fc < tr.height tcd ∧ cv tr tcd fc Codec.kF = 1 ∧ cv tr tcd fc Codec.tau = τ ∧
      cv tr tcd fc Codec.NN = n * n ∧
      let stF := specSt n sp.allowed (reqsOf (instOf sp)) tr tp f
        (lpState sp.ids sp.params sp.allowed (codecA0 tr tcd τ) sp.seed) m
      let g := gridGrants n sp.allowed stF.senderBudget stF.receiverBudget
        (sordOf n sp.allowed stF.senderBudget) (rordOf n sp.allowed stF.receiverBudget)
      runCore sp (prevOf tr tcd τ) = some
        ⟨(svOf tr tcd τ).map UInt8.ofNat,
          (List.range (n * n)).map (fun l => ((sp.ids.getD (l / n) 0, sp.ids.getD (l % n) 0),
            stF.granted[l]! + (g[l]!).getD 0)),
          sp.params⟩ ∧
      (∀ x ∈ svOf tr tcd τ, x < 256) ∧
      PrevCanon sp.ids (prevOf tr tcd τ) (codecA0 tr tcd τ) (h0Of tr tcd τ) ∧
      (∀ l, l < n * n → stF.granted[l]! + (g[l]!).getD 0 ≤ 4500000) ∧
      -- the grants as the AIR holds them
      (∀ l, l < n * n → cv tr tcd (fc + 5 + 24 * l + 23) Codec.gfin = stF.granted[l]! ∧
        cv tr tcd (fc + 5 + 24 * l + 23) Codec.gb < 2 ^ 23) ∧
      -- the forwarding check of instance 0
      (τ = 0 → ∀ l, l < n * n →
        fwdDemand fwd l % 2 ^ 24 ≤ stF.granted[l]! + cv tr tcd (fc + 5 + 24 * l + 23) Codec.gb) := by
  intro sp n
  obtain ⟨f, m, hf, hk, hc, hτf, Ib, H⟩ := schedCore_sound2 hH O OS OO OC SO PB IO DO PR SH SK hprep I fwd
    hrecP hrecB hrecD hτ
  have hlen33 := prepD0_len hprep
  have hP := instOk_of hprep
  have h256 : (p.sched.map instOf).length ≤ 256 := by rw [List.length_map]; omega
  have hτ' : τ < (p.sched.map instOf).length := by rw [List.length_map]; exact hτ
  have S := prepD0_sched hprep _ (List.getElem_mem hτ)
  have hasz := prepD0_asz hprep _ (List.getElem_mem hτ)
  have C : InitCtx AP pub tr tp tm tcmp ts tch tg tsd tcd (p.sched.map instOf) :=
    ⟨hH, O, OS, OO, OC, SO, IO, h256, hP⟩
  have hP0 : (p.sched.map instOf).getD τ instD = instOf sp := getD_map_instOf _ hτ
  have hP00 : (p.sched.map instOf).getD 0 instD = instOf p.sched[0] := getD_map_instOf _ (by omega)
  obtain ⟨-, M⟩ := memCtx_of C PB I fwd hrecP hrecB hf hk hc Ib
  obtain ⟨fc, hfc, hF, hτc⟩ := C.codec_exists I fwd hrecP hτ'
  obtain ⟨-, -, hNN, -⟩ := codec_hdr hH OC SO I _ fwd hrecP h256 hfc hF (by rw [hτc]; exact hP _ hτ')
  rw [hτc, hP0] at hNN
  rw [hτf, hP0] at M
  refine ⟨f, m, fc, hf, hk, hc, hτf, Ib, hfc, hF, hτc, hNN, ?_⟩
  intro stF g
  obtain ⟨hrun, hbytes, hprev, hle⟩ := H
  -- the start state's invariants
  have hG : GInv n 4500000 (lpState sp.ids sp.params sp.allowed (codecA0 tr tcd τ) sp.seed) := by
    have := lpState_ginv sp.ids S.n1 sp.params S.params sp.allowed hasz (codecA0 tr tcd τ) sp.seed
    rw [pv86_maxShard S.params] at this
    exact this
  have hSz : SzOk n (lpState sp.ids sp.params sp.allowed (codecA0 tr tcd τ) sp.seed) := by
    refine ⟨?_, ?_, ?_⟩ <;> simp [lpState, linkPass] <;> rfl
  have hgfin : ∀ l, l < n * n → cv tr tcd (fc + 5 + 24 * l + 23) Codec.gfin = stF.granted[l]! :=
    fun l hl => codec_gfin M hSz hG OC hfc hF (hτc.trans hτf.symm) hNN hl
  have hgb : ∀ l, l < n * n → cv tr tcd (fc + 5 + 24 * l + 23) Codec.gb < 2 ^ 23 :=
    fun l hl => codec_gb_lt hH OC OS IO hfc hF (by rw [hNN]; exact hl)
  refine ⟨hrun, hbytes, hprev, hle, fun l hl => ⟨hgfin l hl, hgb l hl⟩, ?_⟩
  intro h0 l hl
  have hn0 : ((p.sched.map instOf).getD 0 instD).n ≤ 64 := (hP 0 (by omega)).n64
  have hfw := codec_fwd hH OC OS IO O.cmp PB I _ fwd hrecB hn0 hfc hF (by rw [hτc, h0])
    (by rw [hNN]; exact hl) (by rw [hgfin l hl]; exact Nat.le_trans (Nat.le_add_right _ _) (hle l hl))
  rw [hgfin l hl] at hfw
  exact hfw

/-- **`schedCore_sound''`**: `schedCore_sound'` with `GbGrid` discharged. Besides the conclusions of
`schedCore_sound'`, the codec's `gb` of every record is the spec's grid grant, and for τ = 0 every
forwarding demand below `2^24` is at most its link's output grant `stF.granted[l] + grid[l]`.
New hypothesis: `SdlxOwn` (ownership, decidable). -/
theorem schedCore_sound2'' (hH : HoldsP AP pub tr) {tp tm tcmp ts tch tg tsd tcd tsha tsha2 : Nat}
    -- ownership (decidable on the final AIR)
    (O : SchedOwn AP tp tm tcmp ts tch tg) (OS : ScanOwn AP tsd tp) (OO : OpOwn AP tp tsd tcd)
    (OC : CodecValOwn AP tcd) (SO : SparOwn AP) (PB : PubbOwn AP) (IO : InitOwn AP tcd tsd)
    (DO : SdlOwn AP tcd) (PR : PubbRecv AP tp tcd) (SH : ShaOwn2 AP tsha tsha2) (DX : SdlxOwn AP tsd)
    -- the kind registry (cross-lane)
    (SK : ShaKind AP pub tr tcd)
    -- the prepared statement and the public records (`PubIdx`, R1)
    {cb : NearSpec.Bytes} {hint : Hint} {p : Prep} (hprep : prepD0 cb hint = .ok p)
    (I : PubIdx AP pub Fp.ofNat) (fwd : List (Nat × Nat))
    (hrecP : I.recs B_SPAR true = (render (p.sched.map instOf) fwd).par)
    (hrecB : I.recs B_SPUBB true = (render (p.sched.map instOf) fwd).pubb)
    (hrecD : I.recs B_SDL true = (render (p.sched.map instOf) fwd).dlSend)
    {τ : Nat} (hτ : τ < p.sched.length) :
    let sp := p.sched[τ]
    let n := sp.ids.length
    ∃ f m fc, f < tr.height tp ∧ cv tr tp f Proc.kK = 1 ∧ cv tr tp f Proc.kc = 0 ∧
      cv tr tp f Proc.tau = τ ∧ Proc.Inst tr tp f m ∧
      fc < tr.height tcd ∧ cv tr tcd fc Codec.kF = 1 ∧ cv tr tcd fc Codec.tau = τ ∧
      cv tr tcd fc Codec.NN = n * n ∧
      let stF := specSt n sp.allowed (reqsOf (instOf sp)) tr tp f
        (lpState sp.ids sp.params sp.allowed (codecA0 tr tcd τ) sp.seed) m
      let g := gridGrants n sp.allowed stF.senderBudget stF.receiverBudget
        (sordOf n sp.allowed stF.senderBudget) (rordOf n sp.allowed stF.receiverBudget)
      runCore sp (prevOf tr tcd τ) = some
        ⟨(svOf tr tcd τ).map UInt8.ofNat,
          (List.range (n * n)).map (fun l => ((sp.ids.getD (l / n) 0, sp.ids.getD (l % n) 0),
            stF.granted[l]! + (g[l]!).getD 0)),
          sp.params⟩ ∧
      (∀ x ∈ svOf tr tcd τ, x < 256) ∧
      PrevCanon sp.ids (prevOf tr tcd τ) (codecA0 tr tcd τ) (h0Of tr tcd τ) ∧
      (∀ l, l < n * n → stF.granted[l]! + (g[l]!).getD 0 ≤ 4500000) ∧
      -- the grants as the AIR holds them
      (∀ l, l < n * n → cv tr tcd (fc + 5 + 24 * l + 23) Codec.gfin = stF.granted[l]! ∧
        cv tr tcd (fc + 5 + 24 * l + 23) Codec.gb < 2 ^ 23) ∧
      -- `gb` is the grid grant (stage F)
      GbGrid tr tcd fc n g ∧
      -- the forwarding check of instance 0 against the output grants
      (τ = 0 → ∀ l, l < n * n → fwdDemand fwd l < 2 ^ 24 →
        fwdDemand fwd l ≤ stF.granted[l]! + (g[l]!).getD 0) := by
  intro sp n
  obtain ⟨f, m, fc, hf, hk, hc, hτf, Ib, hfc, hF, hτc, hNN, H⟩ := schedCore_sound2' hH O OS OO OC SO PB IO
    DO PR SH SK hprep I fwd hrecP hrecB hrecD hτ
  have hlen33 := prepD0_len hprep
  have hP := instOk_of hprep
  have h256 : (p.sched.map instOf).length ≤ 256 := by rw [List.length_map]; omega
  have hτ' : τ < (p.sched.map instOf).length := by rw [List.length_map]; exact hτ
  have C : InitCtx AP pub tr tp tm tcmp ts tch tg tsd tcd (p.sched.map instOf) :=
    ⟨hH, O, OS, OO, OC, SO, IO, h256, hP⟩
  have hP0 : (p.sched.map instOf).getD τ instD = instOf sp := getD_map_instOf _ hτ
  obtain ⟨-, M⟩ := memCtx_of C PB I fwd hrecP hrecB hf hk hc Ib
  rw [hτf, hP0] at M
  have G : GridPub AP pub tr tsd tp (p.sched.map instOf) I fwd := ⟨hH, OS, hrecP, h256, hP⟩
  have hgg := gbGrid_of G DX OC IO M hτ' hP0 hτf hfc hF hτc hNN
  refine ⟨f, m, fc, hf, hk, hc, hτf, Ib, hfc, hF, hτc, hNN, ?_⟩
  intro stF g
  obtain ⟨hrun, hbytes, hprev, hle, hgr, hfw⟩ := H
  refine ⟨hrun, hbytes, hprev, hle, hgr, hgg, fun h0 l hl h24 => ?_⟩
  have := hfw h0 l hl
  rw [Nat.mod_eq_of_lt h24, hgg l hl] at this
  exact this
end

end ZkFormal.NearV3.Sched

/-! ## `nearAirV3` -/

namespace ZkFormal.NearV3.Assembly

open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near

namespace LinkSchedCore

open ZkFormal.NearV3.Sched

theorem shaOwn2_v3 : ShaOwn2 nearAirV3 T_SHA_T T_SHA_R where
  lt1 := by decide
  tab1 := rfl
  lt2 := by decide
  tab2 := rfl
  dig := by
    have h : ∀ t, t < nearAirV3.tables.length → ¬(t = T_SHA_T ∨ t = T_SHA_R) →
        ∀ i ∈ nearAirV3.tables[t]!.interactions, i.bus = ZkFormal.Near.B_DIGEST → i.send = false := by
      decide +kernel
    exact fun t ht a b => h t ht (fun e => by rcases e with e | e <;> contradiction)
  pubDig := by decide +kernel

theorem memOwn_v3 : MemOwn nearAirV3 T_MEM :=
  ⟨by decide, rfl, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem cmpOwn_v3 : CmpOwn nearAirV3 T_CMP := ⟨by decide, rfl, by decide +kernel, by decide +kernel⟩

theorem shufOwn_v3 : ShufOwn nearAirV3 T_PROC T_SHUF T_CHACHA T_RNG := by
  constructor <;> first | rfl | decide +kernel

theorem schedOwn_v3 : SchedOwn nearAirV3 T_PROC T_MEM T_CMP T_SHUF T_CHACHA T_RNG := by
  constructor <;> first | exact memOwn_v3 | exact cmpOwn_v3 | exact shufOwn_v3 | rfl | decide +kernel

theorem scanOwn_v3 : ScanOwn nearAirV3 T_SSD T_PROC := by constructor <;> first | rfl | decide +kernel

theorem opOwn_v3 : OpOwn nearAirV3 T_PROC T_SSD T_CODEC where
  lt := by decide
  tab := rfl
  only := by
    have h : ∀ t, t < nearAirV3.tables.length → ¬(t = T_PROC ∨ t = T_SSD ∨ t = T_CODEC) →
        ∀ i ∈ nearAirV3.tables[t]!.interactions, i.bus = B_SOP → i.send = false := by decide +kernel
    exact fun t ht a b c => h t ht (fun e => by rcases e with e | e | e <;> contradiction)

theorem pubbOwn_v3 : PubbOwn nearAirV3 := by constructor <;> first | rfl | decide +kernel
theorem initOwn_v3 : InitOwn nearAirV3 T_CODEC T_SSD := by constructor <;> first | rfl | decide +kernel
theorem sdlOwn_v3 : SdlOwn nearAirV3 T_CODEC := by constructor <;> first | rfl | decide +kernel
theorem pubbRecv_v3 : PubbRecv nearAirV3 T_PROC T_CODEC := by constructor <;> first | rfl | decide +kernel
theorem sdlxOwn_v3 : SdlxOwn nearAirV3 T_SSD := by constructor <;> first | rfl | decide +kernel

/-! ### The kind registry `ShaKind` (no `BYTES` sender but the codec uses kind 11) -/

/-- A physical row send with nonzero multiplicity is counted by `tableBusCount`. -/
theorem row_send_pos {is : List Interaction} {tr : Trace Fp} {t r : Nat} {pub : List Fp}
    {i : Interaction} {b : Nat} (hr : r < tr.height t) (hi : i ∈ is) (hb : i.bus = b)
    (hs : i.send = true) (hm : i.multNat tr t r pub ≠ 0) :
    0 < tableBusCount is tr t pub b true (i.msgVal tr t r pub) := by
  rw [ZkFormal.Near.tableBusCount_eq]
  apply List.count_pos_iff.mpr
  refine List.mem_flatMap.mpr ⟨r, List.mem_range.mpr hr, ?_⟩
  unfold ZkFormal.Near.rowTraffic
  refine List.mem_flatMap.mpr ⟨i, hi, ?_⟩
  rw [if_pos ⟨hb, hs⟩]
  exact List.mem_replicate.mpr ⟨hm, rfl⟩

/-- A message counted in a record traffic's `BYTES` sends has the traffic's kinds. -/
theorem kind_of_tcnt {tf : Traffic} {ks : List Nat} (hK : ∀ x ∈ tf.sends B_BYTES, KindIn ks x)
    (h11 : 11 ∉ ks) {M : List Fp} (hc : 0 < tcnt tf true B_BYTES M) :
    ∀ a, M.head? = some a → a.toNat % 16 ≠ 11 := by
  simp only [tcnt, ite_true] at hc
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp (List.count_pos_iff.mp hc)
  intro a ha
  cases x with
  | nil => simp [Msg.toFp] at ha
  | cons b xs =>
    simp only [Msg.toFp, List.map_cons, List.head?_cons, Option.some.injEq] at ha
    subst ha
    obtain ⟨h1, h2⟩ := hK _ hx b rfl
    rw [Fp.toNat_ofNat, Nat.mod_eq_of_lt h1]
    exact fun e => h11 (e ▸ h2)

theorem nodeValKindIn {vs : List ZkFormal.NearV3.NodeS3} {es : List ZkFormal.NearV3.ValE}
    (hw : ZkFormal.NearV3.NodeWf3 vs) (hvw : ZkFormal.NearV3.ValWf es) {x : Msg}
    (hx : x ∈ ZkFormal.NearV3.nodeSends3 vs B_BYTES ++ ZkFormal.NearV3.valSends es B_BYTES) :
    KindIn [K_NPRE, K_NPOST, K_VPRE] x := by
  obtain ⟨K, n, hh, hK, hn⟩ := nodeVal_bytes_head hw hvw hx
  intro a ha
  rw [hh, Option.some.injEq] at ha
  subst ha
  have hK16 : K < 16 := by rcases hK with rfl | rfl | rfl <;> decide
  have hmod : msgId K n % 16 = K := by unfold msgId; omega
  refine ⟨by unfold msgId P; omega, ?_⟩
  rw [hmod]
  rcases hK with rfl | rfl | rfl <;> simp

/-- **`ShaKind` of `nearAirV3`**: only the codec sends `BYTES` messages of kind 11 (node/val
7/8/9, ups 12, rcpt 1–5, acct 10, srcp 13, mrk 6; no public `BYTES` send). -/
theorem shaKind_v3 {cb : NearSpec.Bytes} {h : NearSpecV3.Hint} {p : NearSpecV3.Prep} {oh : Nat}
    {tr : Trace Fp} {r : V3Records} (hp : NearSpecV3.prepD0 cb h = .ok p)
    (hsz : (ZkFormal.NearV3.Public.preparedBytes p oh).length < P)
    (hH : HoldsP nearAirV3 (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr)
    (T : V3RecordsTraffic (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr r)
    (W : V3RecordsWf (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r) :
    ShaKind nearAirV3 (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr T_CODEC where
  tabs := by
    intro t ht htc q hq i hi hb hs hm a ha
    have hc := row_send_pos (is := nearAirV3.tables[t]!.interactions) hq hi hb hs hm
    have key : ∀ t, t < nearAirV3.tables.length → t = T_CODEC ∨ t = T_NODE ∨ t = T_VAL ∨ t = T_UPS ∨
        t = T_RCPT ∨ t = T_ACCT ∨ t = T_SRCP ∨ t = T_MRK ∨
        (∀ i ∈ nearAirV3.tables[t]!.interactions, i.bus = B_BYTES → i.send = false) := by
      decide +kernel
    rcases key t ht with e | e | e | e | e | e | e | e | hno
    · exact absurd e htc
    · subst e
      rw [show nearAirV3.tables[T_NODE]!.interactions = isAt T_NODE from rfl,
        node_count T _ _ _ (by decide +kernel)] at hc
      exact kind_of_tcnt (fun x hx => nodeValKindIn W.nodes W.values (List.mem_append_left _ hx))
        (by decide) hc a ha
    · subst e
      rw [show nearAirV3.tables[T_VAL]!.interactions = isAt T_VAL from rfl,
        val_count T _ _ _ (by decide +kernel)] at hc
      exact kind_of_tcnt (fun x hx => nodeValKindIn W.nodes W.values (List.mem_append_right _ hx))
        (by decide) hc a ha
    · subst e
      rw [show nearAirV3.tables[T_UPS]!.interactions = isAt T_UPS from rfl,
        ups_count T _ _ _ (by decide +kernel)] at hc
      exact kind_of_tcnt (upsKindIn_of hp hsz hH T W) (by decide) hc a ha
    · subst e
      rw [show nearAirV3.tables[T_RCPT]!.interactions = ZkFormal.NearV3.RcptV3.interactions from rfl,
        tcnt_of_traffic T.lists] at hc
      exact kind_of_tcnt (fun x hx => rcptKindIn W.listsCount.1 W.listsCount.2 x hx) (by decide) hc a ha
    · subst e
      rw [show nearAirV3.tables[T_ACCT]!.interactions = ZkFormal.NearV3.AcctV3.interactions from rfl,
        tcnt_of_traffic T.accts] at hc
      exact kind_of_tcnt (fun x hx => acctKindIn hH T W x hx) (by decide) hc a ha
    · subst e
      rw [show nearAirV3.tables[T_SRCP]!.interactions = ZkFormal.NearV3.Rcpt.Candidates.DedupTable.interactions from rfl,
        tcnt_of_traffic T.srcp] at hc
      exact kind_of_tcnt (ddKindIn W.srcp) (by decide) hc a ha
    · subst e
      rw [show nearAirV3.tables[T_MRK]!.interactions =
          ZkFormal.NearV3.Candidates.MerkleEmpty.table.interactions from rfl,
        tcnt_of_traffic T.mrk] at hc
      exact kind_of_tcnt (mrkKindIn W (pubNat_pubOf_lt _)) (by decide) hc a ha
    · rw [hno i hi hb] at hs; cases hs
  pubs := by
    intro M hM
    exact absurd (pubCount_noside (sd := true) (by decide +kernel) _ M) hM

/-- **The scheduler core of `nearAirV3`** (`schedCore_sound2''` with every ownership condition,
the kind registry and the public records discharged): for every scheduler instance `τ` of the
prepared statement, `runCore` on the codec's previous state returns the codec's post bytes and the
spec's grants, with the canonical previous state, the grant bounds, the AIR's grants, `GbGrid`, and
the forwarding check of instance 0. -/
theorem schedCore_v3 {cb : NearSpec.Bytes} {h : NearSpecV3.Hint} {p : NearSpecV3.Prep} {oh : Nat}
    {tr : Trace Fp} {r : V3Records} (hp : NearSpecV3.prepD0 cb h = .ok p)
    (hsz : (ZkFormal.NearV3.Public.preparedBytes p oh).length < P)
    (hH : HoldsP nearAirV3 (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr)
    (T : V3RecordsTraffic (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr r)
    (W : V3RecordsWf (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r)
    {τ : Nat} (hτ : τ < p.sched.length) :
    let sp := p.sched[τ]
    let n := sp.ids.length
    ∃ f m fc, f < tr.height T_PROC ∧ cv tr T_PROC f Proc.kK = 1 ∧ cv tr T_PROC f Proc.kc = 0 ∧
      cv tr T_PROC f Proc.tau = τ ∧ Proc.Inst tr T_PROC f m ∧
      fc < tr.height T_CODEC ∧ cv tr T_CODEC fc Codec.kF = 1 ∧ cv tr T_CODEC fc Codec.tau = τ ∧
      cv tr T_CODEC fc Codec.NN = n * n ∧
      let stF := specSt n sp.allowed (reqsOf (instOf sp)) tr T_PROC f
        (lpState sp.ids sp.params sp.allowed (codecA0 tr T_CODEC τ) sp.seed) m
      let g := gridGrants n sp.allowed stF.senderBudget stF.receiverBudget
        (sordOf n sp.allowed stF.senderBudget) (rordOf n sp.allowed stF.receiverBudget)
      NearSpecV3.Scheduler.runCore sp (prevOf tr T_CODEC τ) = some
        ⟨(svOf tr T_CODEC τ).map UInt8.ofNat,
          (List.range (n * n)).map (fun l => ((sp.ids.getD (l / n) 0, sp.ids.getD (l % n) 0),
            stF.granted[l]! + (g[l]!).getD 0)),
          sp.params⟩ ∧
      (∀ x ∈ svOf tr T_CODEC τ, x < 256) ∧
      PrevCanon sp.ids (prevOf tr T_CODEC τ) (codecA0 tr T_CODEC τ) (h0Of tr T_CODEC τ) ∧
      (∀ l, l < n * n → stF.granted[l]! + (g[l]!).getD 0 ≤ 4500000) ∧
      (∀ l, l < n * n → cv tr T_CODEC (fc + 5 + 24 * l + 23) Codec.gfin = stF.granted[l]! ∧
        cv tr T_CODEC (fc + 5 + 24 * l + 23) Codec.gb < 2 ^ 23) ∧
      GbGrid tr T_CODEC fc n g ∧
      (τ = 0 → ∀ l, l < n * n → fwdDemand p.fwd l < 2 ^ 24 →
        fwdDemand p.fwd l ≤ stF.granted[l]! + (g[l]!).getD 0) := by
  have hlen : (ZkFormal.NearV3.Public.preparedBytes p oh).length < 256 ^ 4 := by unfold P at hsz; omega
  have hrec := ZkFormal.NearV3.Public.prepared_scheduler_index nearAirV3 oh rfl hp (prepD0_roots hp)
    (prepD0_source_roots hp) hlen
  exact schedCore_sound2'' hH schedOwn_v3 scanOwn_v3 opOwn_v3 codecOwn sparOwn pubbOwn_v3 initOwn_v3
    sdlOwn_v3 pubbRecv_v3 shaOwn2_v3 sdlxOwn_v3 (shaKind_v3 hp hsz hH T W) hp
    (ZkFormal.NearV3.Public.prepared_pubIdx nearAirV3 p oh rfl (prepD0_roots hp) (prepD0_source_roots hp) hlen)
    p.fwd hrec.2.1 hrec.1 hrec.2.2.1 hτ

end LinkSchedCore

end ZkFormal.NearV3.Assembly
