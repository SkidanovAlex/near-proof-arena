import ZkFormal.NearV3.Assembly.LinkPostRec
import ZkFormal.NearV3.Rcpt.Link.ValExact

/-!
# ZkFormal.NearV3.Assembly.LinkMainLink — `MainTrieLink` at `pre := Fpre r 0` from `HoldsP`

The receipt core's trie premise (`RcptLink.MainTrieLink`, lane v3-rcpt-sound) on this lane's
family `Tf r 0 (schedOut o).state` with `base := preV r` (`LinkTrieOk.Mdl`):

* `sched` — `LinkSched0.sched_pre` at `τ = 0`;
* `init` — `LinkTrieOk.init_of` with `LinkPostRec.hinit_holds`;
* `trie` (**`trieOk_holds`**) — `find_of` / `set_of` / `ak_of`; for a `VAL` access-key walk the
  value is the record of `akk`, which is no receipt slot (no acct slot, `RcptLink.akk_value`), so
  it keeps its pre bytes: 9 bytes, the last `1`.
-/

namespace ZkFormal.NearV3.Assembly

open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near

namespace LinkMainLink

open ZkFormal.NearV3 ZkFormal.NearV3.Link3 ZkFormal.NearV3.RcptLink LinkTrieOk LinkTrieFam

section
variable {cb : NearSpec.Bytes} {h : NearSpecV3.Hint} {p : NearSpecV3.Prep} {oh : Nat}
  {tr : Trace Fp} {r : V3Records}

/-- **`TrieOk`** of the receipt core on the main trie family. -/
theorem trieOk_holds (hp : NearSpecV3.prepD0 cb h = .ok p)
    (hsz : (ZkFormal.NearV3.Public.preparedBytes p oh).length < P)
    (hH : HoldsP nearAirV3 (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr)
    (T : V3RecordsTraffic (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr r)
    (W : V3RecordsWf (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r)
    (h0 : 0 < p.sched.length) (st : NearSpec.Bytes) :
    (Mdl r st).TrieOk := by
  have hinit := LinkPostRec.hinit_holds hp hsz hH T W st
  have H := LinkPostRec.recHyp_holds hp hsz hH T W
  refine ⟨fun i hi v hv => (find_of hp hsz hH T W h0 hinit hi hv).2,
    fun i hi v hv => (find_of hp hsz hH T W h0 hinit hi hv).1,
    fun i hi v hv b hb => set_of hp hsz hH T W h0 hinit hi hv hb, ?_⟩
  intro i hi hsys hsr
  have hi' : i < (flatR r.lists).length := by rwa [mdl_len] at hi
  obtain ⟨hee, hf⟩ := ak_of hp hsz hH T W h0 hinit hi' hsys hsr
    ((Mdl r st).valsAt_lenPres i)
  refine ⟨_, hf, ?_⟩
  by_cases hv : (flatR r.lists)[i].akf = FK_VAL
  · rw [if_pos hv]
    right
    refine ⟨_, rfl, ?_⟩
    obtain ⟨⟨e, he, -, hvid, hl9, h8⟩, hna⟩ :=
      akk_value hH T W (List.getElem_mem hi') hee (by simpa [FK_VAL] using hv)
    -- `akk` is no receipt slot
    have hw : (Mdl r st).written (flatR r.lists)[i].akk = false := by
      cases hw : (Mdl r st).written (flatR r.lists)[i].akk with
      | false => rfl
      | true =>
        exfalso
        simp only [RunModel.written, List.any_eq_true, List.mem_range, beq_iff_eq] at hw
        obtain ⟨j, hj, hjk⟩ := hw
        rw [mdl_len] at hj
        obtain ⟨a, ha, hak⟩ := LinkPostRec.acct_of_slot H j hj
        exact hna a ha (hak.trans hjk)
    have hva : (Mdl r st).valsAt i (flatR r.lists)[i].akk = toB e.bytes := by
      simp only [RunModel.valsAt, hw, Bool.false_eq_true, ↓reduceIte]
      obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem he
      show preV r _ = _
      rw [← hvid]; exact preV_at W ht
    rw [hva]
    refine ⟨by simp [toB, hl9], ?_⟩
    simp only [toB, List.getD_eq_getElem?_getD, List.getElem?_map] at h8 ⊢
    rw [List.getElem?_eq_getElem (by omega)] at h8 ⊢
    simp only [Option.getD_some, Option.map_some] at h8 ⊢
    rw [h8]; rfl
  · rw [if_neg hv]; left; rfl

/-- **`MainTrieLink`** at `pre := Fpre r 0` (any context whose scheduler input is instance `0`'s). -/
theorem mainTrieLink_holds (hp : NearSpecV3.prepD0 cb h = .ok p)
    (hsz : (ZkFormal.NearV3.Public.preparedBytes p oh).length < P)
    (hH : HoldsP nearAirV3 (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr)
    (T : V3RecordsTraffic (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr r)
    (W : V3RecordsWf (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r)
    (h0 : 0 < p.sched.length) {ctx : NearSpecV3.ApplyCtx}
    (hctx : NearSpecV3.schedPub ctx = some p.sched[0]) :
    ∃ o Q, NearSpecV3.Scheduler.runCore p.sched[0] (Sched.prevOf tr T_CODEC 0) = some o ∧
      MainTrieLink r.lists r.accts (preV r) (Tf r 0 (schedOut o).state) ctx (LinkImplicit.Fpre r 0) Q
        (schedOut o) := by
  obtain ⟨o, Q, ho, hQ, hs⟩ := LinkSched0.sched_pre hp hsz hH T W h0 (Nat.zero_le _) hctx
  exact ⟨o, Q, ho, hs,
    init_of hp hsz hH T W (LinkPostRec.hinit_holds hp hsz hH T W _) hQ,
    trieOk_holds hp hsz hH T W h0 _⟩

end

end LinkMainLink

end ZkFormal.NearV3.Assembly
