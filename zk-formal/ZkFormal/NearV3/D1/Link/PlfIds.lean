import ZkFormal.NearV3.D1.Link.MemBound
import ZkFormal.NearV3.D1.Extract.PlfProof

/-!
# `ZkFormal.NearV3.D1.Link.PlfIds` — the `DIGEST` messages of `plfV3` (L1)

Lane `v3-d1-phase2`, item L1.  In `nearAirV3D1` the SHA union is no longer the only sender on
`DIGEST`: `plfV3` sends `DIGEST (K_PLF + 16·pos, 68, leaf)` for the public outcome leaves
(`PLEAF`, positions `0 … M0 − 1`).  D0a's `digest_provided` ("every received digest is a SHA
output") holds in D1 for every message whose id is not a leaf id:

* `pub_pleaf_mem`: a public `PLEAF` message is `[j] ++ leaf_j` for `j < |leaves|`;
* **`plf_digest_small`**: a `DIGEST` message sent by `plfV3` has id `K_PLF + 16·j` with
  `j < |leaves| ≤ 2·NT0` (the `PLEAF` bus has the public segment as its only sender);
* `PlfSmall` / `plfSmall_of`: the same, as a predicate of the public input and the trace;
* `fp_kind_ne_plf`: an id `K + 16·n < P` of another kind `K < 16` is not a leaf id.
-/

namespace ZkFormal.NearV3.D1.Link

open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near ZkFormal.NearV3 ZkFormal.NearV3.D1
open ZkFormal.NearV3.D1.Public

theorem d1_pleaf_tables : onlyOn B_PLEAF [T_PLF] = true := by decide +kernel

theorem segs_no_pleaf : ∀ s ∈ ZkFormal.NearV3.Assembly.nearAirV3.pubSegs, s.bus ≠ B_PLEAF := by
  have hall : ZkFormal.NearV3.Public.preparedSegments.all (fun s => decide (s.bus ≠ B_PLEAF)) = true := by
    decide +kernel
  intro s hs
  exact of_decide_eq_true (List.all_eq_true.mp hall s hs)

set_option maxHeartbeats 2000000 in
/-- **A public `PLEAF` message** of the verifier's tape is `[j] ++ leaf_j` for `j < |leaves|`. -/
theorem pub_pleaf_mem (p : PrepD1) (ov : Nat) (hr : ZkFormal.NearV3.Public.RootsSized p.base)
    (hs : ∀ s ∈ p.base.lists, s.root.length = 32) (hleaves : ∀ l ∈ p.leaves, l.length = 32)
    (hlen : (preparedBytesD1 p ov).length < 256 ^ 4) {sd : Bool} {m : List Fp}
    (hpos : 0 < pubCount nearAirV3D1 (ZkFormal.Udr.pubOf Fp (preparedBytesD1 p ov)) B_PLEAF sd m) :
    sd = true ∧ ∃ j < p.leaves.length,
      m = ((j : Nat) : Fp) :: (p.leaves.getD j []).map ZkFormal.NearV3.Public.byteF := by
  rw [pubCountD1_split p ov hr hs hlen, pubCount_nobus segs_no_pleaf sd, Nat.zero_add] at hpos
  obtain ⟨x, hx⟩ := List.exists_mem_of_length_pos hpos
  rw [List.mem_filter, decide_eq_true_eq] at hx
  obtain ⟨hx, rfl⟩ := hx
  rw [newMsgs_eq p ov hr hlen hleaves] at hx
  simp only [List.mem_append] at hx
  rcases hx with (((((h | h) | h) | h) | h) | h) <;> obtain ⟨j, hj, he⟩ := mem_tagged h <;>
    simp only [Prod.mk.injEq] at he
  · exact absurd he.1 (by decide)
  · exact absurd he.1 (by decide)
  · exact absurd he.1 (by decide)
  · exact absurd he.1 (by decide)
  · have hj' : j < p.leaves.length := by simpa [leafPayload] using hj
    refine ⟨he.2.1, j, hj', ?_⟩
    rw [he.2.2]
    simp [ZkFormal.NearV3.Public.recordValues, leafPlan, leafPayload]
  · exact absurd he.1 (by decide)

/-- The leaf ids of `plfV3`'s `DIGEST` sends are small. -/
def PlfSmall (pub : List Fp) (tr : Trace Fp) : Prop :=
  ∀ m : List Fp, 0 < tableBusCount PlfV3.interactions tr T_PLF pub B_DIGEST true m →
    ∃ j < 8192, m.head? = some (Fp.ofNat (K_PLF + 16 * j))

/-- **`plfV3`'s `DIGEST` ids** are `K_PLF + 16·j`, `j < |leaves|`. -/
theorem plf_digest_small {cb : NearSpec.Bytes} {h : HintD1} {p : PrepD1} {ov : Nat} {tr : Trace Fp}
    (hp : prepD1 cb h = .ok p) (hlen : (preparedBytesD1 p ov).length < P)
    (hH : HoldsP nearAirV3D1 (ZkFormal.Udr.pubOf Fp (preparedBytesD1 p ov)) tr) {m : List Fp}
    (hpos : 0 < tableBusCount PlfV3.interactions tr T_PLF (ZkFormal.Udr.pubOf Fp (preparedBytesD1 p ov))
      B_DIGEST true m) :
    ∃ j < p.leaves.length, m.head? = some (Fp.ofNat (K_PLF + 16 * j)) := by
  have hP : P < 256 ^ 4 := by unfold P; omega
  obtain ⟨es, hw, hT⟩ := plf_view tr _ T_PLF (plfLocal hH)
  obtain ⟨v, hv, rfl⟩ := mem_of_count_pos hT hpos
  simp only [ite_true, plfTraffic, plfSends, show B_DIGEST ≠ B_MPOS by decide, ite_false,
    List.mem_map] at hv
  obtain ⟨e, he, rfl⟩ := hv
  -- the leaf's `PLEAF` receive is public
  have hr : e.pos :: e.d ∈ (plfTraffic es).recvs B_PLEAF := by
    simp only [plfTraffic, plfRecvs, ite_true]
    exact List.mem_map.mpr ⟨e, he, rfl⟩
  have hpos' := count_pos_of_mem hT hr
  rcases sender_of_recv hH getElem?_d1_plf hpos' with hpub | ⟨t', T', ht', hpos''⟩
  · obtain ⟨-, j, hj, hm⟩ := pub_pleaf_mem p ov (prepD1_roots hp) (prepD1_source_roots hp)
      (prepD1_leaves hp) (by omega) hpub
    simp only [Msg.toFp, List.map_cons, List.cons.injEq] at hm
    obtain ⟨h1, -⟩ := hm
    have hc := (hw.canon e he).1
    have hjl : j < P := by
      have := (prepD1_m0_t0 hp).1
      obtain ⟨w, -, rfl⟩ := prepD1_spec hp
      change j < w.loc.leaves.length at hj
      change w.loc.leaves.length ≤ _ at this
      unfold NearSpecV3.NT0 at this; unfold P; omega
    have : e.pos = j := by
      have := congrArg Fp.toNat h1
      rw [Fp.toNat_ofNat, natCast_eq, Fp.toNat_ofNat, Nat.mod_eq_of_lt hc, Nat.mod_eq_of_lt hjl] at this
      exact this
    subst this
    exact ⟨e.pos, hj, by simp [Msg.toFp, PlfE.mid]⟩
  · by_cases h28 : t' = T_PLF
    · subst h28
      rw [getElem?_d1_plf] at ht'
      cases ht'
      obtain ⟨v, hv, -⟩ := mem_of_count_pos hT hpos''
      simp [plfTraffic, plfSends, show B_PLEAF ≠ B_MPOS by decide,
        show B_PLEAF ≠ B_DIGEST by decide] at hv
    · rw [tableBusCount_nobus' (only_of d1_pleaf_tables ht' (by simpa using h28)) true] at hpos''
      omega

theorem plfSmall_of {cb : NearSpec.Bytes} {h : HintD1} {p : PrepD1} {ov : Nat} {tr : Trace Fp}
    (hp : prepD1 cb h = .ok p) (hlen : (preparedBytesD1 p ov).length < P)
    (hH : HoldsP nearAirV3D1 (ZkFormal.Udr.pubOf Fp (preparedBytesD1 p ov)) tr) :
    PlfSmall (ZkFormal.Udr.pubOf Fp (preparedBytesD1 p ov)) tr := by
  intro m hm
  obtain ⟨j, hj, he⟩ := plf_digest_small hp hlen hH hm
  have := (prepD1_m0_t0 hp).1
  obtain ⟨w, -, rfl⟩ := prepD1_spec hp
  change j < w.loc.leaves.length at hj
  change w.loc.leaves.length ≤ _ at this
  unfold NearSpecV3.NT0 at this
  exact ⟨j, by omega, he⟩

/-- An id `K + 16·n < P` of a kind `K < 16`, `K ≠ K_PLF`, is not a leaf id. -/
theorem fp_kind_ne_plf {K n j : Nat} (hK : K < 16) (hne : K ≠ K_PLF) (hn : K + 16 * n < P)
    (hj : j < 8192) : Fp.ofNat (K + 16 * n) ≠ Fp.ofNat (K_PLF + 16 * j) := by
  intro he
  have := congrArg Fp.toNat he
  have hj' : K_PLF + 16 * j < P := by unfold K_PLF P; omega
  rw [Fp.toNat_ofNat, Fp.toNat_ofNat, Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hj'] at this
  unfold K_PLF at this hne
  omega

end ZkFormal.NearV3.D1.Link
