import ZkFormal.NearV3.Assembly.LinkRidBytes
import ZkFormal.NearV3.Qv.Extract.WalkChain
import ZkFormal.NearV3.Qv.Extract.RepairedKeyTraffic

/-!
# ZkFormal.NearV3.Assembly.LinkKeynib — `KeynibOk` of the walks from `HoldsP`

The `KEYNIB` bus (users: walk receives; rcpt and the raw `qvV3` table send) balances, so every
walk key-symbol receive is a rcpt or qv send (`keynib_bal`).  The providers' symbols are nibbles
or `SYM_END`: rcpt's `keySyms`/`akSyms` are nibbles of byte strings (receiver / signer are bytes
by `RcptE.Wf`, the public key by `encBytes`); qv's physical sends are `repairedKeyTraffic`
(`repaired_key_physical`).  **`keynibOk_of`** : `KeynibOk r.walks prov` for
`prov = rcpt KEYNIB sends ++ qv KEYNIB sends (as naturals)` — the `hkey` hypothesis of
`walks_tau` / `upsV3_linkB`.
-/

namespace ZkFormal.NearV3.Assembly

open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near

namespace LinkKeynib

open ZkFormal.NearV3

/-- The physical `KEYNIB` sends of the raw `qvV3` table. -/
def qvKeys (tr : Trace Fp) (pub : List Fp) : List (List Fp) :=
  (List.range (tr.height T_QV)).flatMap fun q => rowTraffic (isAt T_QV) tr T_QV q pub B_KEYNIB true

/-- **`KEYNIB`**: walk receives = rcpt sends + qv sends. -/
theorem keynib_bal {pub : List Fp} {tr : Trace Fp} {r : V3Records} (hH : HoldsP nearAirV3 pub tr)
    (T : V3RecordsTraffic pub tr r) (m : List Fp) :
    ((walkRecvs3 r.walks B_KEYNIB).map Msg.toFp).count m =
      ((rcptSends3 pub r.lists B_KEYNIB).map Msg.toFp).count m + (qvKeys tr pub).count m := by
  have h := bal_users hH (b := B_KEYNIB) (U := [T_WALK, T_RCPT, T_QV]) (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) m
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero] at h
  rw [walk_count T, walk_count T, show isAt T_RCPT = RcptV3.interactions from rfl,
    tcnt_of_traffic T.lists, tcnt_of_traffic T.lists,
    tableBusCount_noside (s := false) (is := isAt T_QV) (by decide +kernel),
    tableBusCount_eq (isAt T_QV)] at h
  have w0 : walkSends3 r.walks B_KEYNIB = [] := by
    simp [walkSends3, B_KEYNIB, B_EDGE, B_BMAP, B_FINAL]
  have r0 : rcptRecvs3 r.lists B_KEYNIB = [] := by
    simp [rcptRecvs3, rRecvs, B_DIGEST, B_FINAL, B_MEM, B_KEYNIB, B_SREC, B_AKC, B_BND]
  simp only [tcnt, ite_true, Bool.false_eq_true, ite_false, walkTraffic3, rcptTraffic3, w0, r0,
    List.map_nil, List.count_nil, Nat.zero_add, Nat.add_zero] at h
  unfold qvKeys; omega

/-- The qv key symbols are nibbles or `SYM_END`. -/
theorem qvKeys_syms {pub : List Fp} {tr : Trace Fp} (hH : HoldsP nearAirV3 pub tr) :
    ∀ m ∈ qvKeys tr pub, (m.getD 2 0).toNat < 16 ∨ (m.getD 2 0).toNat = SYM_END := by
  have hQ : TableLocal Qv.Candidates.KeyTrafficRepair.table tr T_QV pub :=
    tableLocal_of_holdsP hH (t := T_QV) rfl
  obtain ⟨q⟩ := Qv.Extract.walk_chain_exists (Qv.Candidates.KeyTrafficRepair.local_to_base hQ)
  intro m hm
  rw [qvKeys, show isAt T_QV = Qv.Candidates.KeyTrafficRepair.interactions from rfl,
    Qv.Extract.repaired_key_physical hQ q] at hm
  obtain ⟨p, -, hm⟩ := List.mem_flatMap.mp hm
  obtain ⟨i, -, hm⟩ := List.mem_flatMap.mp hm
  have hb := UInt8.toNat_lt ((Qv.Extract.physicalWalkBytes tr T_QV p).getD i 0)
  have cast : ∀ v : Nat, v < 17 → ((v : Fp)).toNat = v := by
    intro v hv
    change (Fp.ofNat v).toNat = v
    rw [Fp.toNat_ofNat, Nat.mod_eq_of_lt (by unfold P; omega)]
  simp only [Qv.Extract.repairedKeyRow, List.mem_append] at hm
  rcases hm with hm | hm
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl
    · left; simp only [List.getD_cons_succ, List.getD_cons_zero]; rw [cast _ (by omega)]; omega
    · left; simp only [List.getD_cons_succ, List.getD_cons_zero]; rw [cast _ (by omega)]; omega
  · split at hm
    · simp only [List.mem_singleton] at hm
      subst hm
      right; simp only [List.getD_cons_succ, List.getD_cons_zero]; rw [cast _ (by decide)]
    · simp at hm

/-- The receipt view's `KEYNIB` sends over the flattened receipts. -/
theorem rcptSends3_keynib (pub : List Fp) (ls : RcptV3Vs) :
    rcptSends3 pub ls B_KEYNIB = ((flatR ls).zipIdx).flatMap fun p =>
      RcptE.keyMsgs p.2 p.1.keySyms ++ (if p.1.ee then RcptE.keyMsgs (W_AK + p.2) p.1.akSyms else []) := by
  simp only [rcptSends3, show B_KEYNIB ≠ B_BYTES by decide, show B_KEYNIB ≠ B_RCL by decide,
    ite_false, List.nil_append]
  have hs : ∀ (j : Nat) (p : Nat × Nat × RcptE), rSends pub (flatR ls) j p.1 p.2.1 p.2.2 B_KEYNIB =
      RcptE.keyMsgs p.1 p.2.2.keySyms ++
        (if p.2.2.ee then RcptE.keyMsgs (W_AK + p.1) p.2.2.akSyms else []) := by
    intro j p
    simp [rSends, B_KEYNIB, B_BYTES]
  simp only [hs]
  exact LinkRids.located_flat ls (fun r x => RcptE.keyMsgs r x.keySyms ++
    (if x.ee then RcptE.keyMsgs (W_AK + r) x.akSyms else []))

theorem keyMsgs_sym {w : Nat} {syms : List Nat} {m : Msg} (hm : m ∈ RcptE.keyMsgs w syms) :
    m.getD 2 0 ∈ syms := by
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hm
  simp only [List.getD_cons_succ, List.getD_cons_zero]
  have ht' := List.mem_range.mp ht
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht', Option.getD_some]
  exact List.getElem_mem ht'

theorem nibbles_ok (l : List Nat) (hl : ∀ c ∈ l, c < 256) :
    ∀ y ∈ l.flatMap (fun ch => [ch / 16, ch % 16]), y < 16 := by
  intro y hy
  obtain ⟨c, hc, hy⟩ := List.mem_flatMap.mp hy
  have := hl c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
  rcases hy with rfl | rfl <;> omega

/-- **`KeynibOk`** of the walks, providers = rcpt + qv `KEYNIB` sends. -/
theorem keynibOk_of {cb : NearSpec.Bytes} {h : NearSpecV3.Hint} {p : NearSpecV3.Prep} {oh : Nat}
    {tr : Trace Fp} {r : V3Records} (hp : NearSpecV3.prepD0 cb h = .ok p)
    (hsz : (ZkFormal.NearV3.Public.preparedBytes p oh).length < P)
    (hH : HoldsP nearAirV3 (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr)
    (T : V3RecordsTraffic (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr r)
    (W : V3RecordsWf (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r) :
    Link3.KeynibOk r.walks
      (rcptSends3 (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r.lists B_KEYNIB ++
        (qvKeys tr (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh))).map
          fun x => x.map Fp.toNat) := by
  have henc := LinkRidBytes.encBytes hp hsz hH T W
  obtain ⟨toks, -, -, hwf, -⟩ := W.lists.toks
  refine ⟨?_, ?_⟩
  · intro m hm
    have hc : 0 < ((walkRecvs3 r.walks B_KEYNIB).map Msg.toFp).count (Msg.toFp m) :=
      List.count_pos_iff.mpr (List.mem_map_of_mem hm)
    rw [keynib_bal hH T] at hc
    rw [List.map_append, List.map_map,
      show (Msg.toFp ∘ fun x : List Fp => x.map Fp.toNat) = id from funext toFp_map_toNat, List.map_id,
      List.mem_append]
    rcases Nat.eq_zero_or_pos (((rcptSends3 _ r.lists B_KEYNIB).map Msg.toFp).count (Msg.toFp m)) with h0 | h0
    · right; rw [h0, Nat.zero_add] at hc; exact List.count_pos_iff.mp hc
    · left; exact List.count_pos_iff.mp h0
  · have sym_ok : ∀ y, y < 16 ∨ y = SYM_END → y < P ∧ (y < 16 ∨ y = SYM_END) := by
      intro y hy; refine ⟨?_, hy⟩; rcases hy with hy | hy
      · unfold P; omega
      · rw [hy]; decide
    intro m hm
    rcases List.mem_append.mp hm with hm | hm
    · apply sym_ok
      rw [rcptSends3_keynib] at hm
      obtain ⟨⟨x, q⟩, hxq, hm⟩ := List.mem_flatMap.mp hm
      have hx : x ∈ flatR r.lists := (List.of_mem_zip (LinkRids.zipIdx_zero (flatR r.lists) ▸ hxq)).1
      obtain ⟨qq, hqq, hxe⟩ := List.getElem_of_mem hx
      have hW := hwf qq hqq
      rw [hxe] at hW
      rcases List.mem_append.mp hm with hm | hm
      · have hs := keyMsgs_sym hm
        simp only [RcptV.keySyms, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hs
        rcases hs with (hs | hs) | hs
        · left; rcases hs with hs | hs <;> rw [hs] <;> decide
        · left; exact nibbles_ok _ hW.ids.2.2.2.2.1 _ hs
        · right; exact hs
      · split at hm
        · have hs := keyMsgs_sym hm
          simp only [RcptE.akSyms, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hs
          rcases hs with hs | hs
          · left
            apply nibbles_ok _ _ _ hs
            intro c hc
            simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
            rcases hc with ((((hc | hc) | hc) | hc) | hc)
            · omega
            · exact hW.ids.2.2.2.2.2 c hc
            · omega
            · have := hW.lens.2.2.1; omega
            · exact henc x hx c (by simp [RcptV.enc, hc])
          · right; exact hs
        · simp at hm
    · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hm
      have hq := qvKeys_syms hH y hy
      have z0 : (0 : Nat) = Fp.toNat 0 := by
        have := Fp.toNat_ofNat 0
        rw [Nat.zero_mod] at this
        exact this.symm
      have e : (y.map Fp.toNat).getD 2 0 = (y.getD 2 0).toNat := by
        match y with
        | [] => exact z0
        | [_] => exact z0
        | [_, _] => exact z0
        | _ :: _ :: c :: _ => rfl
      rw [e]
      exact sym_ok _ hq

end LinkKeynib

end ZkFormal.NearV3.Assembly
