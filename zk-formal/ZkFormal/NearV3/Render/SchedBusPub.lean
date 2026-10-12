import ZkFormal.NearV3.Render.CodecSpost
import ZkFormal.NearV3.Render.SchedBusSA0
import ZkFormal.NearV3.Public.SchedulerIndex
import ZkFormal.NearV3.Rcpt.Candidates.PreparedRootChain
import ZkFormal.NearV3.Sched.Link.SoundPrep

/-!
# The scheduler's public messages of an accepted witness, and the block list

* `sched_pub_counts`: on the certificate's public vector `A.pub`, the public `SPUBB`, `SPAR` and `SDL`
  messages are exactly the scheduler records `schedulerRecords A.p` (as field elements);
* `prior_pubs`: the `PriorCore` blocks of `A`'s trace carry exactly the prepared scheduler data,
  `bs.map (·.pub) = A.p.sched`; `prior_ids`: every block has the layout's shard ids.
-/
namespace ZkFormal.NearV3.Assembly
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near ZkFormal.NearV3.Render
open ZkFormal.NearV3.Assembly.CodecDigest NearSpec NearSpecV3

/-- Field image of byte records. -/
def recF (l : List (List Nat)) : List (List Fp) := l.map (·.map Fp.ofNat)

theorem sched_pub_counts {cb wb : Bytes} (A : AcceptedV3 cb wb) (m : List Fp) :
    pubCount nearAirV3 A.pub Sched.B_SPUBB true m = (recF (Public.schedulerRecords A.p).pubb).count m ∧
    pubCount nearAirV3 A.pub Sched.B_SPAR true m = (recF (Public.schedulerRecords A.p).par).count m ∧
    pubCount nearAirV3 A.pub Sched.B_SDL true m = (recF (Public.schedulerRecords A.p).dlSend).count m ∧
    pubCount nearAirV3 A.pub Sched.B_SDL false m = (recF (Public.schedulerRecords A.p).dlRecv).count m := by
  have hl4 : (Public.preparedBytes A.p 0).length < 256 ^ 4 := by
    have h1 := A.prepared_lt_P
    have : ZkFormal.Algebra.P < 256 ^ 4 := by decide
    omega
  let I := Public.prepared_pubIdx nearAirV3 A.p 0 rfl (prepD0_roots A.hp) (prepD0_source_roots A.hp) hl4
  obtain ⟨h1, h2, h3, h4⟩ := Public.prepared_scheduler_index nearAirV3 0 rfl A.hp (prepD0_roots A.hp)
    (prepD0_source_roots A.hp) hl4
  have c1 := I.count Sched.B_SPUBB true m
  have c2 := I.count Sched.B_SPAR true m
  have c3 := I.count Sched.B_SDL true m
  have c4 := I.count Sched.B_SDL false m
  change I.recs _ _ = _ at h1 h2 h3 h4
  rw [h1] at c1
  rw [h2] at c2
  rw [h3] at c3
  rw [h4] at c4
  exact ⟨c1, c2, c3, c4⟩

theorem sched_length {cb wb : Bytes} (A : AcceptedV3 cb wb) : A.p.sched.length = A.steps.length + 1 := by
  have hc : checkD0 cb wb = .ok () := by
    have h := A.h
    unfold checkD0a at h
    obtain ⟨u, hu, _⟩ := ReexecV3D0.bind_ok' h
    cases u; exact hu
  obtain ⟨_, _, hK⟩ := Rcpt.Candidates.NodePostUpdate.prepared_trace_root_endpoints A.hp A.hk A.hw hc A.hv
  rw [prepD0_sched_count A.hp, hK]

theorem prior_pubs {cb wb : Bytes} (A : AcceptedV3 cb wb) {B : Nat} {bs : List NativeBlock}
    (hc : PriorCore A.p B bs) (hlen : bs.length = A.steps.length + 1) : bs.map (·.pub) = A.p.sched := by
  apply List.ext_getElem?
  intro i
  rw [List.getElem?_map]
  cases hb : bs[i]? with
  | some b => exact ((hc.indexed i b hb).1.1).symm
  | none =>
    have : bs.length ≤ i := List.getElem?_eq_none_iff.mp hb
    simp only [Option.map_none]
    exact (List.getElem?_eq_none (by rw [sched_length A]; omega)).symm

/-- Instance `τ` of the rendered public data (as `Sched.render` reads it). -/
def instAt (Ps : List Sched.InstPub) (τ : Nat) : Sched.InstPub := Ps.getD τ ⟨[], ⟨0, 0, 0, 0, 0⟩, #[], [], [], []⟩

theorem prior_ids {cb wb : Bytes} (A : AcceptedV3 cb wb) {B : Nat} {bs : List NativeBlock}
    (hc : PriorCore A.p B bs) (hlen : bs.length = A.steps.length + 1) :
    ∀ b ∈ bs, b.pub.ids = (instAt (A.p.sched.map Sched.instOf) 0).ids := by
  obtain ⟨ids, hids⟩ := Sched.prepD0_ids A.hp
  have h0 : 0 < A.p.sched.length := by rw [sched_length A]; omega
  intro b hb
  have hm : b.pub ∈ A.p.sched := by rw [← prior_pubs A hc hlen]; exact List.mem_map_of_mem hb
  have h0' : 0 < (A.p.sched.map Sched.instOf).length := by simpa using h0
  rw [hids _ hm, instAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h0', Option.getD_some,
    List.getElem_map]
  exact (hids _ (List.getElem_mem h0)).symm

end ZkFormal.NearV3.Assembly
