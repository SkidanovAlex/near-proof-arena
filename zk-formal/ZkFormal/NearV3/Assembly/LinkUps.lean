import ZkFormal.NearV3.Assembly.LinkKeynib

/-!
# ZkFormal.NearV3.Assembly.LinkUps — the `upsV3_linkB_22` hypotheses from `HoldsP`

* `body_head` — every public `BYTES` receive (the refund body) has head `2` (`K_RF`);
* `othersU` — the `BYTES` senders other than ups, net of the public body receives;
  **`hbytesU_of`**: `shaU false BYTES m = cnt (ups sends ++ othersU) m` (the same `shaR` as
  `shaHyp_holds`); **`hothU_of`**: no `othersU` id is of kind `K_VUPS`.
-/

namespace ZkFormal.NearV3.Assembly

open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near

namespace LinkUps

open ZkFormal.NearV3

/-- The public `BYTES` receives are refund body records with head `2`. -/
theorem body_head {cb : NearSpec.Bytes} {h : NearSpecV3.Hint} {p : NearSpecV3.Prep} {oh : Nat}
    (hp : NearSpecV3.prepD0 cb h = .ok p)
    (hsz : (ZkFormal.NearV3.Public.preparedBytes p oh).length < P) {m : List Fp}
    (hm : 0 < pubCount nearAirV3 (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) B_BYTES false m) :
    m.head? = some (Fp.ofNat 2) := by
  have hlen : (ZkFormal.NearV3.Public.preparedBytes p oh).length < 256 ^ 4 := by unfold P at hsz; omega
  have hI := ZkFormal.NearV3.Public.prepared_receipt_index nearAirV3 p oh rfl (prepD0_roots hp)
    (prepD0_source_roots hp) hlen
  have hc := (ZkFormal.NearV3.Public.prepared_pubIdx nearAirV3 p oh rfl (prepD0_roots hp)
    (prepD0_source_roots hp) hlen).count B_BYTES false m
  rw [show B_BYTES = 0 from rfl, hI.2.2] at hc
  rw [show B_BYTES = 0 from rfl, hc] at hm
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp (List.count_pos_iff.mp hm)
  obtain ⟨j, -, rfl⟩ := List.mem_map.mp hy
  rfl

/-- The `BYTES` sends of the viewed tables other than node / val / ups, plus the codec. -/
def noUpsBytes (tr : Trace Fp) (pub : List Fp) (r : V3Records) : List (List Fp) :=
  (rcptSends3 pub r.lists B_BYTES ++ acctV3Sends r.accts B_BYTES ++ (srcpTraffic r.srcp).sends B_BYTES ++
    (mrkTrafficE pub r.mrkE r.mrk).sends B_BYTES).map Msg.toFp ++ codecBytes tr pub

/-- The `BYTES` senders other than ups, net of the public body. -/
def othersU (tr : Trace Fp) (pub : List Fp) (r : V3Records) : List Msg :=
  nodeSends3 r.nodes B_BYTES ++ valSends r.values B_BYTES ++
    (eraseAll (noUpsBytes tr pub r) (pubList pub B_BYTES false)).map fun x => x.map Fp.toNat

/-- Kinds of `noUpsBytes`: rcpt 1–5, acct 10, srcp 13, mrk 6, codec 11 — never `K_VUPS`. -/
theorem noUps_kinds {cb : NearSpec.Bytes} {h : NearSpecV3.Hint} {p : NearSpecV3.Prep} {oh : Nat}
    {tr : Trace Fp} {r : V3Records} (hp : NearSpecV3.prepD0 cb h = .ok p)
    (hsz : (ZkFormal.NearV3.Public.preparedBytes p oh).length < P)
    (hH : HoldsP nearAirV3 (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr)
    (T : V3RecordsTraffic (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr r)
    (W : V3RecordsWf (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r) :
    ∀ y ∈ noUpsBytes tr (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r, ∀ a,
      y.head? = some a → a.toNat % 16 ≠ K_VUPS := by
  have kin : ∀ {ks : List Nat} {x : Msg}, KindIn ks x → (∀ k ∈ ks, k ≠ K_VUPS) →
      ∀ a, x.toFp.head? = some a → a.toNat % 16 ≠ K_VUPS := by
    intro ks x hk hks a ha
    cases x with
    | nil => simp [Msg.toFp] at ha
    | cons b xs =>
      simp only [Msg.toFp, List.map_cons, List.head?_cons, Option.some.injEq] at ha
      subst ha
      obtain ⟨h1, h2⟩ := hk b rfl
      rw [Fp.toNat_ofNat, Nat.mod_eq_of_lt h1]
      exact hks _ h2
  intro y hy a ha
  simp only [noUpsBytes, List.mem_append, List.map_append] at hy
  rcases hy with (((hy | hy) | hy) | hy) | hy
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
    exact kin (rcptKindIn W.listsCount.1 W.listsCount.2 x hx) (by decide) a ha
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
    exact kin (acctKindIn hH T W x hx) (by decide) a ha
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
    exact kin (srcpKindIn W.srcp x hx) (by decide) a ha
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
    exact kin (mrkKindIn W (pubNat_pubOf_lt _) x hx) (by decide) a ha
  · rw [codecKindIn hp hsz hH y hy a ha]; decide

/-- **`hbytesU`** for the SHA union's `BYTES` receives. -/
theorem hbytesU_of {cb : NearSpec.Bytes} {h : NearSpecV3.Hint} {p : NearSpecV3.Prep} {oh : Nat}
    {tr : Trace Fp} {r : V3Records} (hp : NearSpecV3.prepD0 cb h = .ok p)
    (hsz : (ZkFormal.NearV3.Public.preparedBytes p oh).length < P)
    (hH : HoldsP nearAirV3 (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr)
    (T : V3RecordsTraffic (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr r)
    (W : V3RecordsWf (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r) (m : List Fp) :
    shaU tr (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) false B_BYTES m =
      cnt ((upsTraffic r.ups).sends B_BYTES ++
        othersU tr (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r) m := by
  have hb := bytes_balance hH T m
  have e1 : (otherBytes tr (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r).count m =
      (((upsTraffic r.ups).sends B_BYTES).map Msg.toFp).count m +
        (noUpsBytes tr (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r).count m := by
    simp only [otherBytes, otherRecBytes, noUpsBytes, List.map_append, List.count_append]; omega
  have e2 : cnt ((upsTraffic r.ups).sends B_BYTES ++
      othersU tr (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r) m =
      (((upsTraffic r.ups).sends B_BYTES).map Msg.toFp).count m +
        cnt (nodeSends3 r.nodes B_BYTES ++ valSends r.values B_BYTES) m +
        ((noUpsBytes tr (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r).count m -
          pubCount nearAirV3 (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) B_BYTES false m) := by
    unfold cnt othersU
    simp only [List.map_append, List.count_append, List.map_map]
    rw [show (Msg.toFp ∘ fun x : List Fp => x.map Fp.toNat) = id from funext toFp_map_toNat, List.map_id,
      count_eraseAll, count_pubList]
    omega
  rw [e2]
  rw [e1] at hb
  rcases Nat.eq_zero_or_pos (pubCount nearAirV3 (ZkFormal.Udr.pubOf Fp
      (ZkFormal.NearV3.Public.preparedBytes p oh)) B_BYTES false m) with h0 | h0
  · omega
  · have hnv := bodyOk_of hp hsz W m h0
    have hhd := body_head hp hsz h0
    have hu : (((upsTraffic r.ups).sends B_BYTES).map Msg.toFp).count m = 0 := by
      apply List.count_eq_zero.mpr
      intro hx0
      obtain ⟨x, hx, hxe⟩ := List.mem_map.mp hx0
      subst hxe
      cases x with
      | nil => simp [Msg.toFp] at hhd
      | cons b xs =>
        simp only [Msg.toFp, List.map_cons, List.head?_cons, Option.some.injEq] at hhd
        obtain ⟨h1, h2⟩ := upsKindIn_of hp hsz hH T W (b :: xs) hx b rfl
        rw [List.mem_singleton] at h2
        have := ZkFormal.Near.Link.ofNat_inj h1 (by unfold P; omega) hhd
        subst this
        revert h2; decide
    omega

/-- **`hothU`**: no `othersU` id is of kind `K_VUPS`. -/
theorem hothU_of {cb : NearSpec.Bytes} {h : NearSpecV3.Hint} {p : NearSpecV3.Prep} {oh : Nat}
    {tr : Trace Fp} {r : V3Records} (hp : NearSpecV3.prepD0 cb h = .ok p)
    (hsz : (ZkFormal.NearV3.Public.preparedBytes p oh).length < P)
    (hH : HoldsP nearAirV3 (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr)
    (T : V3RecordsTraffic (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr r)
    (W : V3RecordsWf (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r) :
    ∀ m ∈ othersU tr (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r, ∀ a,
      m.head? = some a → a < P ∧ a % 16 ≠ K_VUPS := by
  intro m hm a ha
  simp only [othersU, List.mem_append] at hm
  rcases hm with hm | hm
  · obtain ⟨K, n, hh, hK, hn⟩ := nodeVal_bytes_head W.nodes W.values (List.mem_append.mpr hm)
    rw [ha, Option.some.injEq] at hh; subst hh
    unfold msgId P
    rcases hK with rfl | rfl | rfl <;> simp only [K_NPRE, K_NPOST, K_VPRE, K_VUPS] <;> omega
  · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hm
    have hy' := (eraseAll_sublist _ _).subset hy
    cases hyh : y.head? with
    | none => simp [List.head?_map, hyh] at ha
    | some e =>
      simp only [List.head?_map, hyh, Option.map_some, Option.some.injEq] at ha
      subst ha
      exact ⟨Fp.toNat_lt e, noUps_kinds hp hsz hH T W y hy' e hyh⟩

end LinkUps

end ZkFormal.NearV3.Assembly
