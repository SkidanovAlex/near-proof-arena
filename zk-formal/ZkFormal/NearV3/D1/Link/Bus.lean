import ZkFormal.NearV3.D1.Extract.AirD1
import ZkFormal.NearV3.D1.Public.Split
import ZkFormal.NearV3.D1.Public.NewSegs
import ZkFormal.Near.Extract.BusCount

/-!
# `ZkFormal.NearV3.D1.Link.Bus` — bus-balance plumbing for the D1 link (L1)

Lane `v3-d1-phase2`, item L1.

* `sender_of_recv` (any `AirP`): a message received with positive multiplicity by some table is
  sent by some table or by the public segments (`HoldsP.balance`); `recv_of_send` dually.
* `nearAirV3D1`'s bus users: `MEM` is touched only by tables `16` (`rcptV3D1`), `17` (`acctV3`)
  and `25` (`txV3`); `SIG` only by `25` (`d1_mem_tables`, `d1_sig_tables`, kernel `decide` over
  the bus numbers of the 30 interaction lists, as D0a's `nearAir_mem_tables`).  No public
  segment is on `MEM`; the only public segment on `SIG` is the D1 `SIG` segment.
* `pub_sig_mem`: a public `SIG` message of the verifier's tape is `[o, valid_o]` for an op
  index `o < |ops|`.
-/

namespace ZkFormal.NearV3.D1.Link

open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near ZkFormal.NearV3.D1

variable {tr : Trace Fp} {pub : List Fp} {b : Nat} {m : List Fp}

theorem go_ge (s : Bool) : ∀ (l : List ZkFormal.Air.Table) (t i : Nat) (hi : i < l.length),
    tableBusCount l[i].interactions tr (t + i) pub b s m ≤ busCount.go tr pub b s m l t
  | [], _, _, hi => absurd hi (by simp)
  | T :: Ts, t, 0, _ => by
    show _ ≤ tableBusCount T.interactions tr t pub b s m + busCount.go tr pub b s m Ts (t + 1)
    simp only [List.getElem_cons_zero, Nat.add_zero]; omega
  | T :: Ts, t, i + 1, hi => by
    show _ ≤ tableBusCount T.interactions tr t pub b s m + busCount.go tr pub b s m Ts (t + 1)
    have := go_ge s Ts (t + 1) i (by simpa using hi)
    simp only [List.getElem_cons_succ]
    rw [show t + (i + 1) = t + 1 + i by omega]; omega

theorem go_pos (s : Bool) : ∀ (l : List ZkFormal.Air.Table) (t : Nat),
    0 < busCount.go tr pub b s m l t →
    ∃ i, ∃ hi : i < l.length, 0 < tableBusCount l[i].interactions tr (t + i) pub b s m
  | [], _, h => absurd h (by simp [busCount.go])
  | T :: Ts, t, h => by
    change 0 < tableBusCount T.interactions tr t pub b s m + busCount.go tr pub b s m Ts (t + 1) at h
    by_cases h0 : 0 < tableBusCount T.interactions tr t pub b s m
    · exact ⟨0, by simp, by simpa using h0⟩
    · obtain ⟨i, hi, hp⟩ := go_pos s Ts (t + 1) (by omega)
      exact ⟨i + 1, by simpa using hi, by
        simp only [List.getElem_cons_succ]; rw [show t + (i + 1) = t + 1 + i by omega]; exact hp⟩

theorem getElem?_of_lt {l : List ZkFormal.Air.Table} {i : Nat} (hi : i < l.length) :
    l[i]? = some l[i] := List.getElem?_eq_getElem hi

/-- **A positively received message has a sender** (a table or the public segments). -/
theorem sender_of_recv {AP : AirP} (hH : HoldsP AP pub tr) {t : Nat} {T : ZkFormal.Air.Table}
    (ht : AP.tables[t]? = some T) (hpos : 0 < tableBusCount T.interactions tr t pub b false m) :
    0 < pubCount AP pub b true m ∨
      ∃ t' T', AP.tables[t']? = some T' ∧ 0 < tableBusCount T'.interactions tr t' pub b true m := by
  have hb := hH.balance b m
  have hlt : t < AP.tables.length := by
    rcases Nat.lt_or_ge t AP.tables.length with hl | hl
    · exact hl
    · rw [List.getElem?_eq_none hl] at ht; cases ht
  have hT : AP.tables[t] = T := by
    rw [List.getElem?_eq_getElem hlt] at ht; exact Option.some.inj ht
  have hge := go_ge (tr := tr) (pub := pub) (b := b) (m := m) false AP.tables 0 t hlt
  rw [Nat.zero_add, hT] at hge
  change busCount.go tr pub b true m AP.tables 0 + _ = busCount.go tr pub b false m AP.tables 0 + _ at hb
  by_cases hp : 0 < pubCount AP pub b true m
  · exact Or.inl hp
  · right
    obtain ⟨i, hi, hpi⟩ := go_pos (tr := tr) (pub := pub) (b := b) (m := m) true AP.tables 0 (by omega)
    exact ⟨i, AP.tables[i], getElem?_of_lt hi, by simpa using hpi⟩

/-- Dually, a positively sent message has a receiver. -/
theorem recv_of_send {AP : AirP} (hH : HoldsP AP pub tr) {t : Nat} {T : ZkFormal.Air.Table}
    (ht : AP.tables[t]? = some T) (hpos : 0 < tableBusCount T.interactions tr t pub b true m) :
    0 < pubCount AP pub b false m ∨
      ∃ t' T', AP.tables[t']? = some T' ∧ 0 < tableBusCount T'.interactions tr t' pub b false m := by
  have hb := hH.balance b m
  have hlt : t < AP.tables.length := by
    rcases Nat.lt_or_ge t AP.tables.length with hl | hl
    · exact hl
    · rw [List.getElem?_eq_none hl] at ht; cases ht
  have hT : AP.tables[t] = T := by
    rw [List.getElem?_eq_getElem hlt] at ht; exact Option.some.inj ht
  have hge := go_ge (tr := tr) (pub := pub) (b := b) (m := m) true AP.tables 0 t hlt
  rw [Nat.zero_add, hT] at hge
  change busCount.go tr pub b true m AP.tables 0 + _ = busCount.go tr pub b false m AP.tables 0 + _ at hb
  by_cases hp : 0 < pubCount AP pub b false m
  · exact Or.inl hp
  · right
    obtain ⟨i, hi, hpi⟩ := go_pos (tr := tr) (pub := pub) (b := b) (m := m) false AP.tables 0 (by omega)
    exact ⟨i, AP.tables[i], getElem?_of_lt hi, by simpa using hpi⟩

theorem tableBusCount_nobus' {is : List Interaction} {t : Nat}
    (h : ∀ i ∈ is, i.bus ≠ b) (s : Bool) : tableBusCount is tr t pub b s m = 0 := by
  rw [tableBusCount_eq]
  have : (List.range (tr.height t)).flatMap (fun r => rowTraffic is tr t r pub b s) = [] :=
    List.flatMap_eq_nil_iff.2 fun r _ => by
      unfold rowTraffic
      exact List.flatMap_eq_nil_iff.2 fun i hi => by simp [h i hi]
  rw [this]; rfl

/-- A table of `nearAirV3D1` whose index is not in `S` has no interaction on bus `bus`, given
the closed check `onlyOn`. -/
def onlyOn (bus : Nat) (S : List Nat) : Bool :=
  (List.range 30).all fun t => S.contains t ||
    (nearTablesD1.getD t default).interactions.all fun i => i.bus != bus

theorem only_of {bus : Nat} {S : List Nat} (h : onlyOn bus S = true) {t : Nat} {T : ZkFormal.Air.Table}
    (ht : nearAirV3D1.tables[t]? = some T) (hS : t ∉ S) : ∀ i ∈ T.interactions, i.bus ≠ bus := by
  have hlt : t < 30 := by
    rcases Nat.lt_or_ge t 30 with hl | hl
    · exact hl
    · rw [List.getElem?_eq_none (by rw [tables_d1_length]; exact hl)] at ht; cases ht
  have h1 := List.all_eq_true.mp h t (List.mem_range.2 hlt)
  have hS' : S.contains t = false := by simpa using hS
  rw [hS', Bool.false_or] at h1
  have hT : nearTablesD1.getD t default = T := by
    rw [List.getD_eq_getElem?_getD]; change nearAirV3D1.tables[t]?.getD default = T; rw [ht]; rfl
  rw [hT] at h1
  intro i hi
  have := List.all_eq_true.mp h1 i hi
  simpa using this

theorem d1_mem_tables : onlyOn B_MEM [16, 17, 25] = true := by decide +kernel
theorem d1_sig_tables : onlyOn B_SIG [25] = true := by decide +kernel

/-! ## Public segments by bus -/

theorem pubCount_nobus {AP : AirP} (h : ∀ s ∈ AP.pubSegs, s.bus ≠ b) (sd : Bool) :
    pubCount AP pub b sd m = 0 := by
  unfold pubCount
  suffices ((pubMsgs AP pub).filter (fun x => decide (x = (b, sd, m)))) = [] by rw [this]; rfl
  apply List.filter_eq_nil_iff.mpr
  intro x hx
  have hn : x ≠ (b, sd, m) := by
    intro he
    subst x
    simp only [pubMsgs, List.mem_flatMap, List.mem_map] at hx
    obtain ⟨s, hseg, m', _, he⟩ := hx
    exact h s hseg (congrArg (fun x : Nat × Bool × List Fp => x.1) he)
  simp [hn]

theorem segsD1_no_mem : ∀ s ∈ nearAirV3D1.pubSegs, s.bus ≠ B_MEM := by
  have hall : Public.preparedSegmentsD1.all (fun s => decide (s.bus ≠ B_MEM)) = true := by decide +kernel
  intro s hs
  exact of_decide_eq_true (List.all_eq_true.mp hall s hs)

theorem segs_no_sig : ∀ s ∈ ZkFormal.NearV3.Public.preparedSegments, s.bus ≠ B_SIG := by
  have hall : ZkFormal.NearV3.Public.preparedSegments.all (fun s => decide (s.bus ≠ B_SIG)) = true := by
    decide +kernel
  intro s hs
  exact of_decide_eq_true (List.all_eq_true.mp hall s hs)

theorem segsV3_no_sig : ∀ s ∈ ZkFormal.NearV3.Assembly.nearAirV3.pubSegs, s.bus ≠ B_SIG := by
  rw [show ZkFormal.NearV3.Assembly.nearAirV3.pubSegs = ZkFormal.NearV3.Public.preparedSegments from rfl]
  exact segs_no_sig

theorem pubCountD1_mem (pub : List Fp) (sd : Bool) (m : List Fp) :
    pubCount nearAirV3D1 pub B_MEM sd m = 0 := pubCount_nobus segsD1_no_mem sd

theorem mem_tagged {s : PubSeg} {rows : ZkFormal.NearV3.Public.Payload} {x : Nat × Bool × List Fp}
    (hx : x ∈ Public.tagged s rows) :
    ∃ j < rows.length, x = (s.bus, s.send, ZkFormal.NearV3.Public.recordValues s j (rows.getD j [])) := by
  unfold Public.tagged at hx
  simp only [List.mem_map, List.mem_range] at hx
  obtain ⟨m', ⟨j, hj, rfl⟩, rfl⟩ := hx
  exact ⟨j, hj, rfl⟩

open ZkFormal.NearV3.D1.Public in
set_option maxHeartbeats 2000000 in
/-- **A public `SIG` message** of the verifier's tape is `[o, valid_o]` for an op `o < |ops|`. -/
theorem pub_sig_mem (p : PrepD1) (ov : Nat) (hr : ZkFormal.NearV3.Public.RootsSized p.base)
    (hs : ∀ s ∈ p.base.lists, s.root.length = 32) (hleaves : ∀ l ∈ p.leaves, l.length = 32)
    (hlen : (preparedBytesD1 p ov).length < 256 ^ 4) {sd : Bool} {m : List Fp}
    (hpos : 0 < pubCount nearAirV3D1 (ZkFormal.Udr.pubOf Fp (preparedBytesD1 p ov)) B_SIG sd m) :
    sd = true ∧ ∃ o < p.ops.length, m = [((o : Nat) : Fp), ZkFormal.NearV3.Public.byteF
      (UInt8.ofNat (p.ops.getD o default).valid)] := by
  rw [pubCountD1_split p ov hr hs hlen, pubCount_nobus segsV3_no_sig sd, Nat.zero_add] at hpos
  obtain ⟨x, hx⟩ := List.exists_mem_of_length_pos hpos
  rw [List.mem_filter, decide_eq_true_eq] at hx
  obtain ⟨hx, rfl⟩ := hx
  rw [newMsgs_eq p ov hr hlen hleaves] at hx
  simp only [List.mem_append] at hx
  rcases hx with (((((h | h) | h) | h) | h) | h) <;> obtain ⟨j, hj, he⟩ := mem_tagged h <;>
    simp only [Prod.mk.injEq] at he
  · exact absurd he.1 (by decide)
  · exact absurd he.1 (by decide)
  · have hj' : j < p.ops.length := by simpa [sigPayload] using hj
    refine ⟨he.2.1, j, hj', ?_⟩
    rw [he.2.2]
    simp [ZkFormal.NearV3.Public.recordValues, sigPlan, sigPayload, List.getD_eq_getElem?_getD,
      List.getElem?_map, List.getElem?_eq_getElem hj']
  · exact absurd he.1 (by decide)
  · exact absurd he.1 (by decide)
  · exact absurd he.1 (by decide)

end ZkFormal.NearV3.D1.Link
