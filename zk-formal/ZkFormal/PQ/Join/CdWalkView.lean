import ZkFormal.NearV3.D3.CdBus
import ZkFormal.NearV3.Link.Walk3
import ZkFormal.PQ.Join.ContractDataView
import ZkFormal.PQ.Join.HostKeyNib
import ZkFormal.PQ.CdStorage.Link

/-!
# `ZkFormal.PQ.Join.CdWalkView` — the contract-data walk *view* and the `StateStmt` bridge

Lane `pq-d3-join`.  `PQ/Join/Statement.lean` declares `StateStmt` with opaque function fields
`walkPath` and `walkFinal`, and `PQ/CdStorage/Link.lean` relates the record lemmas to the
statement's conjuncts *given* those fields.  What was missing is a **producer**: a view of the
`cdWalkV3` table that says what its `FINAL`/`CDKEYNIB` traffic is, and a definition of the two
`StateStmt` fields from that view.

This module mirrors `NearV3.Extract.WalkView`'s `WalkV3ViewStmt` for the ContractData walk.

## The view

* `cdKeynibStream` — the `CDKEYNIB` stream of a `WalkR` list, explicitly as `(w, t, sym, last)`
  messages; `cdKeynibStream_eq_keynibRecvs` shows it is `walkV3`'s `KEYNIB` receiver
  (`cdWalkV3` is `walkV3` with that bus renamed, so there is nothing else to say).
* `cdWalkTraffic` — the contract-data walk's traffic: `walkV3`'s `EDGE`/`BMAP`/`FINAL` streams, the
  key stream on `CDKEYNIB`, and nothing on `KEYNIB`.
* `cdWalkViewStmt_holds` — from `TableLocal cdWalkV3` the table's traffic is exactly
  `cdWalkTraffic ws` for a `WalkWf3 ws` with at most `2^21` rows.  This is
  `WalkV3ViewStmt` (proved) transferred across the bus rename: `cdWalkV3_busCount` for every bus
  other than the two, plus a new count lemma at the *destination* bus (`renameOne_count_dst`).
* `cdWalkViewOfHoldsTraffic` — the same from `HoldsP` at the `cdWalkV3` table index.

## The headline: `WalkKeyIsContractData` is now a theorem for the `HOSTB` route

`PQ/CdStorage/Link.lean` lists `WalkKeyIsContractData wv account key` (`wv.key3 =
contractDataPath account key`, the E3 `HOSTB → CDKEYNIB` relay) as *stated, not proved*.  Here it
is **proved from a byte-level fact about the walk's `CDKEYNIB` rows**:

* `keyStream_eq_key3_append_end` — the walk's key-symbol stream is `key3 ++ [END]`;
* `walkKeyIsContractData_of_keyStream` — so a stream equal to the ContractData path followed by
  `END` forces `key3` to be exactly that path (`List.append_cancel_right`);
* `hostNibStream_cdPath_syms` — the `HOSTB` byte route (`hostNibStream`, `HostKeyNib`) produces
  exactly `contractDataPath account key ++ [SYM_END]`;
* `walkKeyIsContractData_of_hostNib` / `walkKeyIsContractData_of_wf_hostNib` — hence a walk whose
  `CDKEYNIB` rows are the `HOSTB` stream of `contractDataKey account key` has
  `WalkKeyIsContractData`.

The only residual is the *container-level* relay itself: `CdKeynibFromHostB` says the walk's
`CDKEYNIB` messages are the `HOSTB` byte stream's messages (same `t` positions, same symbols).
That is a statement about the join's wire; it is one level below the path claim that
`WalkKeyIsContractData` states, and it is not an AIR fact this module can see.

## The bridge

`CdWalkPath`/`CdWalkFinal` populate `StateStmt.walkPath`/`walkFinal` by looking a walk up by
`(wid, tau)` / `wid`, and `cd_state_half_walk_of_view` proves the first two conjuncts of
`StateHalfStorageWrite` for a `StateStmt` carrying that view.  `cdWalkPath_from_HostB` is the
combined version: the walk view's well-formedness plus the `HOSTB` key bytes ⇒
`walkPath wid tau = some path`, with `WalkKeyIsContractData` discharged, not assumed.
-/

namespace ZkFormal.PQ.Join

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.NearV3 ZkFormal.NearV3.D3
  ZkFormal.NearV3.Link3 ZkFormal.V2

set_option linter.unusedSimpArgs false

/-! ## The `CDKEYNIB` stream of a walk -/

/-- The `CDKEYNIB` rows of a list of walks: `(w, t, sym, last)`, one row per key symbol
(`t = 0 … L-2`), with `last = 1` on the final `END` row.  This is `D3.cdKeynibMsgs` flattened. -/
def cdKeynibStream (ws : List WalkR) : List Msg :=
  ws.flatMap cdKeynibMsgs

/-- The explicit `CDKEYNIB` stream is `walkV3`'s `KEYNIB` receiver (the bus the rename moved):
`cdWalkV3`'s key-nibble traffic is `keyStream` of its walks, `(w, t, sym, last)` row by row. -/
theorem cdKeynibStream_eq_keynibRecvs (ws : List WalkR) :
    cdKeynibStream ws = walkRecvs3 ws B_KEYNIB := by
  have h1 : ¬ (B_KEYNIB = B_EDGE) := by decide +kernel
  have h2 : ¬ (B_KEYNIB = B_BMAP) := by decide +kernel
  simp only [cdKeynibStream, walkRecvs3, h1, h2, ite_true, ite_false]
  rfl

/-- `cdWalkV3` receives the key stream on `CDKEYNIB` and nothing on `KEYNIB`; every other stream
is `walkV3`'s.  (`EDGE`, `BMAP`, `FINAL` are shared with `walkV3` verbatim.) -/
def cdWalkTraffic (ws : List WalkR) : Traffic where
  sends := walkSends3 ws
  recvs := fun b =>
    if b = B_CDKEYNIB then cdKeynibStream ws
    else if b = B_KEYNIB then [] else walkRecvs3 ws b

/-- The `FINAL` stream of the view is the walks' `(w, tau, fk, k)`. -/
theorem cdWalkTraffic_sends_final (ws : List WalkR) :
    (cdWalkTraffic ws).sends B_FINAL = ws.map fun wv => [wv.w, wv.tau, wv.fk, wv.k] := rfl

/-! ## The `cdWalkV3` view statement

`D3.CdBus.cdWalkView` / `cdWalkViewOfHolds` give `WalkWf3 ws` and the row bound, but no traffic.
The traffic is `WalkV3ViewStmt`'s, moved across the bus rename: `cdWalkV3_busCount`
(`PQ.Join.ContractDataView`) covers every bus but the two, and `renameOne_count_dst` below covers
the destination bus `CDKEYNIB` by transferring the source bus's (`KEYNIB`) count. -/

/-- **The rename's count at the destination bus.**  If no interaction already sits on `dst`, then
on `dst` the renamed table counts exactly what the original counted on `src`.  (For `cdWalkV3`
this is `CDKEYNIB`: `cdWalkV3` receives there what `walkV3` receives on `KEYNIB`.) -/
theorem renameOne_count_dst (is : List Interaction) (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (src dst : Nat) (hne : src ≠ dst) (hnd : ∀ i ∈ is, i.bus ≠ dst) (send : Bool) (m : List Fp)
    (acc : Nat) :
    (is.map (renameOne src dst)).foldr (fun i z =>
        (if i.bus = dst ∧ i.send = send ∧ i.msgVal tr t r pub = m then i.multNat tr t r pub
          else 0) + z) acc
      = is.foldr (fun i z =>
        (if i.bus = src ∧ i.send = send ∧ i.msgVal tr t r pub = m then i.multNat tr t r pub
          else 0) + z) acc := by
  induction is with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, List.foldr_cons]
    rw [ih (fun y hy => hnd y (List.mem_cons_of_mem _ hy))]
    congr 1
    rw [contrib_renamed src dst x hne (hnd x (List.mem_cons_self ..)) tr t r pub dst send m]
    simp

/-- The table-level form: `cdWalkV3`'s `CDKEYNIB` count is `walkV3`'s `KEYNIB` count. -/
theorem cdWalkV3_busCount_cdkeynib (tr : Trace Fp) (t : Nat) (pub : List Fp) (send : Bool)
    (m : List Fp) :
    tableBusCount cdWalkV3.interactions tr t pub B_CDKEYNIB send m
      = tableBusCount WalkV3.table.interactions tr t pub B_KEYNIB send m := by
  rw [ZkFormal.NearV3.D3.cdWalkV3_interactions]
  unfold tableBusCount
  congr 1
  funext r acc
  exact renameOne_count_dst WalkV3.table.interactions tr t r pub B_KEYNIB B_CDKEYNIB
    (by decide +kernel) ZkFormal.NearV3.D3.cdWalkV3_no_dst send m acc

/-- No interaction of `cdWalkV3` sits on `KEYNIB`. -/
theorem cdWalkV3_no_keynib_inter : ∀ i ∈ cdWalkV3.interactions, i.bus ≠ B_KEYNIB := by
  decide +kernel

/-- `cdWalkV3` never *sends* on `CDKEYNIB` (its one interaction there is the key receiver). -/
theorem cdWalkV3_no_cdkeynib_send :
    ∀ i ∈ cdWalkV3.interactions, i.bus = B_CDKEYNIB → i.send ≠ true := by
  decide +kernel

/-- A table with no interaction on bus `b` has count `0` there, on either side. -/
theorem tableBusCount_zero_of_no_bus {is : List Interaction} {tr : Trace Fp} {t : Nat}
    {pub : List Fp} {b : Nat} (h : ∀ i ∈ is, i.bus ≠ b) (send : Bool) (m : List Fp) :
    tableBusCount is tr t pub b send m = 0 := by
  have hrow : ∀ r acc, is.foldr (fun i acc' =>
      (if i.bus = b ∧ i.send = send ∧ i.msgVal tr t r pub = m then i.multNat tr t r pub
        else 0) + acc') acc = acc := by
    intro r acc
    induction is with
    | nil => rfl
    | cons x xs ih =>
      rw [List.foldr_cons, ih (fun y hy => h y (List.mem_cons_of_mem _ hy))]
      have hx := h x (List.mem_cons_self ..)
      simp [hx]
  unfold tableBusCount
  induction List.range (tr.height t) with
  | nil => rfl
  | cons r rs ih =>
    rw [List.foldr_cons, ih]
    exact hrow r 0

/-- A table that does not send on bus `b` has count `0` there. -/
theorem tableBusCount_zero_of_no_send {is : List Interaction} {tr : Trace Fp} {t : Nat}
    {pub : List Fp} {b : Nat} (h : ∀ i ∈ is, i.bus = b → i.send ≠ true) (m : List Fp) :
    tableBusCount is tr t pub b true m = 0 := by
  have hrow : ∀ r acc, is.foldr (fun i acc' =>
      (if i.bus = b ∧ i.send = true ∧ i.msgVal tr t r pub = m then i.multNat tr t r pub
        else 0) + acc') acc = acc := by
    intro r acc
    induction is with
    | nil => rfl
    | cons x xs ih =>
      rw [List.foldr_cons, ih (fun y hy => h y (List.mem_cons_of_mem _ hy))]
      by_cases hb : x.bus = b
      · have := h x (List.mem_cons_self ..) hb
        simp [hb, this]
      · simp [hb]
  unfold tableBusCount
  induction List.range (tr.height t) with
  | nil => rfl
  | cons r rs ih =>
    rw [List.foldr_cons, ih]
    exact hrow r 0

/-- **The contract-data walk view statement.**  From local legality of the `cdWalkV3` table, its
walks `ws` and its whole traffic. -/
def CdWalkViewStmt : Prop :=
  ∀ (tr : Trace Fp) (pub : List Fp) (t : Nat), TableLocal cdWalkV3 tr t pub →
    ∃ ws, WalkWf3 ws ∧ (ws.flatMap (·.steps)).length ≤ 2 ^ 21 ∧
      TableTraffic cdWalkV3.interactions tr t pub (cdWalkTraffic ws)

/-- **The view is proved**, by `WalkV3ViewStmt` plus the two bus transfers. -/
theorem cdWalkViewStmt_holds : CdWalkViewStmt := by
  intro tr pub t hloc
  obtain ⟨ws, hw, hrows, htr⟩ := ZkFormal.NearV3.walk3_view tr pub t (cdWalkLocal hloc)
  refine ⟨ws, hw, hrows, fun b m => ⟨?_, ?_⟩⟩
  · -- sends: `walkV3`'s on every bus but the two; `0` on both (neither table sends there)
    by_cases h1 : b = B_KEYNIB
    · subst h1
      rw [tableBusCount_zero_of_no_bus cdWalkV3_no_keynib_inter true m]
      have hE : ¬ (B_KEYNIB = B_EDGE) := by decide +kernel
      have hB : ¬ (B_KEYNIB = B_BMAP) := by decide +kernel
      have hF : ¬ (B_KEYNIB = B_FINAL) := by decide +kernel
      simp [cdWalkTraffic, walkSends3, hE, hB, hF]
    · by_cases h2 : b = B_CDKEYNIB
      · subst h2
        rw [tableBusCount_zero_of_no_send cdWalkV3_no_cdkeynib_send m]
        have hE : ¬ (B_CDKEYNIB = B_EDGE) := by decide +kernel
        have hB : ¬ (B_CDKEYNIB = B_BMAP) := by decide +kernel
        have hF : ¬ (B_CDKEYNIB = B_FINAL) := by decide +kernel
        simp [cdWalkTraffic, walkSends3, hE, hB, hF]
      · have hh : tableBusCount WalkV3.table.interactions tr t pub b true m
            = List.count m (List.map Msg.toFp (walkSends3 ws b)) := (htr b m).1
        rw [cdWalkV3_busCount tr t pub b h1 h2 true m, hh]
        rfl
  · -- receives: `CDKEYNIB` is the `KEYNIB` count (renamed); `KEYNIB` is empty; else `walkV3`'s
    by_cases h1 : b = B_CDKEYNIB
    · subst h1
      rw [show (cdWalkTraffic ws).recvs B_CDKEYNIB = cdKeynibStream ws from by
        simp [cdWalkTraffic]]
      have hh : tableBusCount WalkV3.table.interactions tr t pub B_KEYNIB false m
          = List.count m (List.map Msg.toFp (walkRecvs3 ws B_KEYNIB)) := (htr B_KEYNIB m).2
      rw [cdWalkV3_busCount_cdkeynib, hh, ← cdKeynibStream_eq_keynibRecvs]
    · by_cases h2 : b = B_KEYNIB
      · subst h2
        rw [show (cdWalkTraffic ws).recvs B_KEYNIB = [] from by simp [cdWalkTraffic, h1]]
        rw [tableBusCount_zero_of_no_bus cdWalkV3_no_keynib_inter false m]
        rfl
      · rw [show (cdWalkTraffic ws).recvs b = walkRecvs3 ws b from by
          simp [cdWalkTraffic, h1, h2]]
        have hh : tableBusCount WalkV3.table.interactions tr t pub b false m
            = List.count m (List.map Msg.toFp (walkRecvs3 ws b)) := (htr b m).2
        rw [cdWalkV3_busCount tr t pub b h2 h1 false m, hh]

/-- The view from `HoldsP`, at the AIR's `cdWalkV3` table index. -/
theorem cdWalkViewOfHoldsTraffic {AP : AirP} {pub : List Fp} {tr : Trace Fp}
    (hH : HoldsP AP pub tr) {t : Nat} (ht : t < AP.tables.length)
    (hT : AP.tables[t]! = cdWalkV3) :
    ∃ ws, WalkWf3 ws ∧ (ws.flatMap (·.steps)).length ≤ 2 ^ 21 ∧
      TableTraffic cdWalkV3.interactions tr t pub (cdWalkTraffic ws) := by
  have htab : AP.tables[t] = cdWalkV3 := by rw [← ZkFormal.Chacha.tables_get ht, hT]
  refine cdWalkViewStmt_holds tr pub t ?_
  exact { log_ge := (hH.logBound t ht).1
          log_le := by rw [← htab]; exact (hH.logBound t ht).2
          constr := by
            intro r hr e he
            rw [← htab] at he
            exact hH.constr t ht r hr e he
          bits := by
            intro r hr i hi b hb
            rw [← htab] at hi
            exact hH.bits t ht r hr i hi b hb }

/-! ## `WalkKeyIsContractData` from the `HOSTB` byte route -/

/-- The walk's key-symbol stream is `key3` followed by the `END` terminator. -/
theorem keyStream_eq_key3_append_end (wv : WalkR) (hL : 2 ≤ wv.steps.length)
    (hlast : (wv.step (wv.steps.length - 1)).sym = SYM_END) :
    keyStream wv = wv.key3 ++ [SYM_END] := by
  obtain ⟨m, hm⟩ : ∃ m, wv.steps.length = m + 2 := ⟨wv.steps.length - 2, by omega⟩
  have h1 : m + 2 - 1 = m + 1 := by omega
  have h2 : m + 2 - 2 = m := by omega
  have hk : (List.range m).map (fun t => (wv.step (t + 1)).sym) = wv.key3 := by
    unfold WalkR.key3
    rw [hm, h2]
  have hl : (wv.step (m + 1)).sym = SYM_END := by
    have := hlast
    rwa [hm, h1] at this
  unfold keyStream
  rw [hm, h1, show List.range (m + 1) = List.range m ++ [m] from List.range_succ]
  simp only [List.map_append, List.map_cons, List.map_nil, hk, hl]

/-- A `WalkWf3` walk's last row carries the `END` symbol (the table's last-row constraint). -/
theorem WalkWf3_last_sym_end {ws : List WalkR} (hw : WalkWf3 ws) {wv : WalkR}
    (hwv : wv ∈ ws) : (wv.step (wv.steps.length - 1)).sym = SYM_END := by
  have hL := hw.len wv hwv
  have hle : wv.steps.length - 1 < wv.steps.length := by omega
  have his : (wv.steps.length - 1 + 1 == wv.steps.length) = true := by
    rw [show wv.steps.length - 1 + 1 = wv.steps.length by omega]
    exact beq_self_eq_true _
  rw [ZkFormal.NearV3.Walk3.step_eq wv hle]
  exact (hw.rows wv hwv (wv.steps.length - 1) hle).lastEnd his

/-- `nibbles` is the byte-splitting of the bytes' natural values. -/
theorem nibbles_map_toNat (bs : NearSpec.Bytes) :
    (bs.map UInt8.toNat).flatMap byteNibs = NearSpec.nibbles bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp [NearSpec.nibbles, byteNibs, ih]

/-- **The ContractData path is what the `HOSTB` byte route sends.**  `hostNibStream` of the
contract-data key's bytes has exactly the path's symbols followed by `END`. -/
theorem hostNibStream_cdPath_syms (w : Nat) (account key : NearSpec.Bytes) :
    (hostNibStream w ((contractDataKey account key).map UInt8.toNat)).map (·.getD 2 0)
      = contractDataPath account key ++ [SYM_END] := by
  rw [hostNibStream_syms, nibbles_map_toNat]
  rfl

/-- **`WalkKeyIsContractData` from the key-symbol stream.**  If a walk's `CDKEYNIB` symbols are
the ContractData path followed by `END`, its `key3` is that path (the `END` cancels). -/
theorem walkKeyIsContractData_of_keyStream (wv : WalkR) (account key : NearSpec.Bytes)
    (hL : 2 ≤ wv.steps.length) (hlast : (wv.step (wv.steps.length - 1)).sym = SYM_END)
    (h : keyStream wv = contractDataPath account key ++ [SYM_END]) :
    ZkFormal.PQ.CdStorage.WalkKeyIsContractData wv account key := by
  unfold ZkFormal.PQ.CdStorage.WalkKeyIsContractData
  rw [keyStream_eq_key3_append_end wv hL hlast] at h
  exact List.append_cancel_right h

/-- **`WalkKeyIsContractData` from the `HOSTB` route.**  If a walk's `CDKEYNIB` rows are the
`HOSTB` byte stream of the contract-data key, its `key3` is `contractDataPath`.  This is E3's
path claim, now a theorem of the message stream. -/
theorem walkKeyIsContractData_of_hostNib (wv : WalkR) (account key : NearSpec.Bytes)
    (hL : 2 ≤ wv.steps.length) (hlast : (wv.step (wv.steps.length - 1)).sym = SYM_END)
    (h : cdKeynibMsgs wv = hostNibStream wv.w ((contractDataKey account key).map UInt8.toNat)) :
    ZkFormal.PQ.CdStorage.WalkKeyIsContractData wv account key := by
  apply walkKeyIsContractData_of_keyStream wv account key hL hlast
  have h' := congrArg (List.map (·.getD 2 0)) h
  rwa [cdKeynibMsgs_symbols, hostNibStream_cdPath_syms] at h'

/-- The `HOSTB` route for a walk of a well-formed walk view. -/
theorem walkKeyIsContractData_of_wf_hostNib {ws : List WalkR} (hw : WalkWf3 ws) {wv : WalkR}
    (hwv : wv ∈ ws) (account key : NearSpec.Bytes)
    (h : cdKeynibMsgs wv = hostNibStream wv.w ((contractDataKey account key).map UInt8.toNat)) :
    ZkFormal.PQ.CdStorage.WalkKeyIsContractData wv account key :=
  walkKeyIsContractData_of_hostNib wv account key (hw.len wv hwv)
    (WalkWf3_last_sym_end hw hwv) h

/-- **The residual of the relay, stated.**  The walk's `CDKEYNIB` rows are the `HOSTB` byte
stream's rows, position for position.  This is the join wire's obligation (E3); given it,
`WalkKeyIsContractData` is proved. -/
def CdKeynibFromHostB (wv : WalkR) (bytes : List Nat) : Prop :=
  cdKeynibMsgs wv = hostNibStream wv.w bytes

/-! ## The `StateStmt` fields from the view -/

/-- `StateStmt.walkPath`: the `key3` of the walk at `(wid, tau)`. -/
def CdWalkPath (ws : List WalkR) (wid tau : Nat) : Option (List Nat) :=
  (ws.find? fun wv => wv.w == wid && wv.tau == tau).map WalkR.key3

/-- `StateStmt.walkFinal`: the `FINAL` kind and target of the walk `wid`. -/
def CdWalkFinal (ws : List WalkR) (wid : Nat) : Option (Nat × Nat) :=
  (ws.find? fun wv => wv.w == wid).map fun wv => (wv.fk, wv.k)

/-- A `StateStmt` whose `walkPath`/`walkFinal` are the contract-data walk view's. -/
def CdWalkPopulates (s : StateStmt) (ws : List WalkR) : Prop :=
  s.walkPath = CdWalkPath ws ∧ s.walkFinal = CdWalkFinal ws

theorem CdWalkPath_eq_some (ws : List WalkR) (wid tau : Nat) (wv : WalkR)
    (h : ws.find? (fun x => x.w == wid && x.tau == tau) = some wv) :
    CdWalkPath ws wid tau = some wv.key3 := by
  simp [CdWalkPath, h]

theorem CdWalkFinal_eq_some (ws : List WalkR) (wid : Nat) (wv : WalkR)
    (h : ws.find? (fun x => x.w == wid) = some wv) :
    CdWalkFinal ws wid = some (wv.fk, wv.k) := by
  simp [CdWalkFinal, h]

/-- **Conjunct (1) of `StateHalfStorageWrite`** from the view and the key routing. -/
theorem cd_walkPath_of_cdView (s : StateStmt) (ws : List WalkR) (wid tau : Nat) (wv : WalkR)
    (account key : NearSpec.Bytes) (hpop : CdWalkPopulates s ws)
    (hfind : ws.find? (fun x => x.w == wid && x.tau == tau) = some wv)
    (hroute : ZkFormal.PQ.CdStorage.WalkKeyIsContractData wv account key) :
    s.walkPath wid tau = some (contractDataPath account key) := by
  rw [hpop.1]
  exact ZkFormal.PQ.CdStorage.cd_walkPath_of_view (CdWalkPath ws) wv wid tau account key
    (CdWalkPath_eq_some ws wid tau wv hfind) hroute

/-- **Conjunct (2), present case**: `FINAL` names the pre-state value record. -/
theorem cd_walkFinal_val_of_cdView (s : StateStmt) (ws : List WalkR) (wid : Nat) (wv : WalkR)
    (hpop : CdWalkPopulates s ws) (hfind : ws.find? (fun x => x.w == wid) = some wv)
    (h : wv.fk = FK_VAL) :
    s.walkFinal wid = some (0, wv.k) := by
  rw [hpop.2]
  exact ZkFormal.PQ.CdStorage.cd_walkFinal_val wv wid (CdWalkFinal ws)
    (CdWalkFinal_eq_some ws wid wv hfind) h

/-- **Conjunct (2), absent case**: an insertion. -/
theorem cd_walkFinal_abs_of_cdView (s : StateStmt) (ws : List WalkR) (wid : Nat) (wv : WalkR)
    (hpop : CdWalkPopulates s ws) (hfind : ws.find? (fun x => x.w == wid) = some wv)
    (h : wv.fk = FK_ABS) :
    s.walkFinal wid = some (1, 0) := by
  rw [hpop.2]
  exact ZkFormal.PQ.CdStorage.cd_walkFinal_abs wv wid (CdWalkFinal ws)
    (CdWalkFinal_eq_some ws wid wv hfind) h

/-- **The first two conjuncts of `StateHalfStorageWrite`, from the contract-data walk view.** -/
theorem cd_state_half_walk_of_view (s : StateStmt) (ws : List WalkR) (w : StorageWrite)
    (hpop : CdWalkPopulates s ws)
    (hpath : ∃ wid tau wv, ws.find? (fun x => x.w == wid && x.tau == tau) = some wv ∧
      ZkFormal.PQ.CdStorage.WalkKeyIsContractData wv (w.account.map UInt8.ofNat)
        (w.key.map UInt8.ofNat))
    (habs : w.preValue = none →
      ∃ wid wv, ws.find? (fun x => x.w == wid) = some wv ∧ wv.fk = FK_ABS)
    (hval : ∀ old, w.preValue = some old →
      ∃ wid wv, ws.find? (fun x => x.w == wid) = some wv ∧ wv.fk = FK_VAL) :
    (∃ wid tau, s.walkPath wid tau =
      some (contractDataPath (w.account.map UInt8.ofNat) (w.key.map UInt8.ofNat))) ∧
    (match w.preValue with
      | none => ∃ wid, s.walkFinal wid = some (1, 0)
      | some _ => ∃ wid vid, s.walkFinal wid = some (0, vid)) := by
  obtain ⟨wid, tau, wv, hf, hr⟩ := hpath
  refine ⟨⟨wid, tau, cd_walkPath_of_cdView s ws wid tau wv _ _ hpop hf hr⟩, ?_⟩
  cases hpv : w.preValue with
  | none =>
    obtain ⟨wid', wv', hf', hfk⟩ := habs hpv
    exact ⟨wid', cd_walkFinal_abs_of_cdView s ws wid' wv' hpop hf' hfk⟩
  | some old =>
    obtain ⟨wid', wv', hf', hfk⟩ := hval old hpv
    exact ⟨wid', wv'.k, cd_walkFinal_val_of_cdView s ws wid' wv' hpop hf' hfk⟩

/-- **The view and the `HOSTB` key bytes give the `walkPath`.**  No
`WalkKeyIsContractData` hypothesis: it comes from the byte stream. -/
theorem cdWalkPath_from_HostB (s : StateStmt) (ws : List WalkR) (wid tau : Nat)
    (wv : WalkR) (hw : WalkWf3 ws) (hwv : wv ∈ ws) (account key : NearSpec.Bytes)
    (hpop : CdWalkPopulates s ws)
    (hfind : ws.find? (fun x => x.w == wid && x.tau == tau) = some wv)
    (hbytes : CdKeynibFromHostB wv ((contractDataKey account key).map UInt8.toNat)) :
    s.walkPath wid tau = some (contractDataPath account key) :=
  cd_walkPath_of_cdView s ws wid tau wv account key hpop hfind
    (walkKeyIsContractData_of_wf_hostNib hw hwv account key hbytes)

end ZkFormal.PQ.Join
