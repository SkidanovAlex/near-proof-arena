import ZkFormal.NearV3.Render.SchedBusPub

/-!
# `SDL` (bus 56): the id-byte delay line balances

Instance `τ`'s codec receives the 16 id bytes of every record `k` as `(τ, k, o, b)` and forwards them to
`τ + 1`; the public statement sends instance 0's and receives instance `K + 1`'s.  All instances have
the layout's shard ids, so block `τ` receives `dlRecs τ ids` and sends `dlRecs (τ + 1) ids`, and the
bus telescopes.  **`RenderBundleV3.balancedAt_sdl`**.
-/
set_option linter.unusedSimpArgs false
namespace ZkFormal.NearV3.Render.Cdc
open ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen
open ZkFormal.Near ZkFormal.NearV3.Assembly ZkFormal.NearV3.Assembly.CodecDigest ZkFormal.NearV3.Candidates

theorem bpo_id (B : Blk) (kk o : Nat) (ho : o < 16) : B.bpo kk (o / 8) (o % 8) = idByte B.ids kk o := by
  unfold Blk.bpo
  rw [if_pos (by omega)]
  congr 1; omega

theorem dl_eq (B : Blk) (s : Nat) (hN : B.I.N = B.ids.length * B.ids.length) (hN4 : B.I.N ≤ 65536)
    (hk : ∀ kk, (B.recs kk).kk = kk) :
    ((List.range B.I.N).flatMap fun kk => (List.range 16).map fun o => [Fp.ofNat s, Fp.ofNat ((B.recs kk).kk % 256),
      Fp.ofNat ((B.recs kk).kk / 256), Fp.ofNat o, Fp.ofNat (B.bpo kk (o / 8) (o % 8))]) =
    recF (dlRecs s B.ids) := by
  unfold recF dlRecs
  rw [← hN, List.map_flatMap]
  apply flatMap_congr''
  intro kk hkk
  have hkk' := List.mem_range.mp hkk
  rw [List.map_map]
  apply List.map_congr_left
  intro o ho
  have ho' := List.mem_range.mp ho
  simp only [Function.comp_apply, hk, bpo_id B kk o ho', b2, List.cons_append, List.nil_append,
    List.map_cons, List.map_nil, List.singleton_append]
  rw [show kk / 256 % 256 = kk / 256 by omega]

theorem blkOf_sdl (b : NativeBlock) (tau : Nat) (hn : b.run.n ≤ 64)
    (hr : ActualRun.run (ProcPreparedSequence.input b.pub b.old) tau = .ok b.run) :
    (blkOf b).descs.flatMap sdlsT = recF (dlRecs (b.run.tau + 1) b.pub.ids) ∧
    (blkOf b).descs.flatMap sdlrT = recF (dlRecs b.run.tau b.pub.ids) := by
  obtain ⟨_, hnI, _⟩ := ProcActualRunProjection.run_fields _ tau b.run hr
  have hN : (blkOf b).I.N = (blkOf b).ids.length * (blkOf b).ids.length := by
    simp only [blkOf]; rw [hnI]
  have hN4 : (blkOf b).I.N ≤ 65536 := by
    simp only [blkOf]; have := Nat.mul_le_mul hn hn; omega
  rw [blk_sdls, blk_sdlr]
  exact ⟨dl_eq _ _ hN hN4 (fun _ => rfl), dl_eq _ _ hN hN4 (fun _ => rfl)⟩

theorem flatMap_tau {α : Type} (bs : List NativeBlock) (g : Nat → List α) (s : Nat)
    (ht : ∀ i b, bs[i]? = some b → b.run.tau = s + i) :
    bs.flatMap (fun b => g b.run.tau) = (List.range' s bs.length).flatMap g := by
  induction bs generalizing s with
  | nil => rfl
  | cons b bs ih =>
    have h0 : b.run.tau = s := by simpa using ht 0 b rfl
    rw [List.flatMap_cons, h0, ih (s + 1) (fun i x hx => by have := ht (i + 1) x (by simpa using hx); omega)]
    simp [List.range'_succ]

theorem telescope {α : Type} [BEq α] (g : Nat → List α) (m : α) :
    ∀ L, ((List.range' 1 L).flatMap g).count m + (g 0).count m =
      ((List.range' 0 L).flatMap g).count m + (g L).count m
  | 0 => by simp
  | L + 1 => by
    have ih := telescope g m L
    rw [List.range'_concat, List.range'_concat, List.flatMap_append, List.flatMap_append,
      List.count_append, List.count_append]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rw [show 1 + 1 * L = L + 1 by omega, show 0 + 1 * L = L by omega]
    omega

theorem range'_map_succ (s : Nat) : ∀ L, (List.range' s L).map (· + 1) = List.range' (s + 1) L
  | 0 => rfl
  | L + 1 => by
    simp only [List.range'_succ, List.map_cons, range'_map_succ (s + 1) L]

end ZkFormal.NearV3.Render.Cdc

namespace ZkFormal.NearV3.Assembly
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near ZkFormal.NearV3.Render
open ZkFormal.NearV3.Render.Cdc ZkFormal.NearV3.Sched ZkFormal.NearV3.Assembly.CodecDigest NearSpec

theorem covers_sdl_send : Covers Sched.B_SDL true (fun t => t == 11) = true := by decide +kernel
theorem covers_sdl_recv : Covers Sched.B_SDL false (fun t => t == 11) = true := by decide +kernel

namespace RenderBundleV3

/-- **`SDL` balance**: tables 11 (the codec render of the `PriorCore` blocks of `A`'s trace) and the
public id-byte endpoints. -/
theorem balancedAt_sdl {cb wb : Bytes} (A : AcceptedV3 cb wb) (R : RenderBundleV3 A.pub)
    {bs : List NativeBlock} (hc : PriorCore A.p NearSpecV3.B0 bs) (hlen : bs.length = A.steps.length + 1)
    (h11 : R.tf 11 = rowsTraffic Sched.Codec.table.interactions (codecCell (bs.map blkOf)) 22 11 A.pub) :
    R.BalancedAt Sched.B_SDL := by
  intro m
  rw [R.sum_tables true _ m _ covers_sdl_send, R.sum_tables false _ m _ covers_sdl_recv]
  have hf : (List.range 25).filter (fun t => t == 11) = [11] := by decide
  rw [hf]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
  rw [h11]
  have e1 := codec_sel A.pub _ (prior_cap hc) _ true sdlsT (rt_sdls · · 11 A.pub) m
  have e2 := codec_sel A.pub _ (prior_cap hc) _ false sdlrT (rt_sdlr · · 11 A.pub) m
  obtain ⟨-, -, p3, p4⟩ := sched_pub_counts A m
  rw [e1, e2, p3, p4]
  have hids := prior_ids A hc hlen
  obtain ⟨ids, hI⟩ : ∃ ids, (instAt (A.p.sched.map Sched.instOf) 0).ids = ids := ⟨_, rfl⟩
  rw [hI] at hids
  have hs : (bs.map blkOf).flatMap (fun B => B.descs.flatMap sdlsT) =
      bs.flatMap (fun b => recF (dlRecs (b.run.tau + 1) ids)) := by
    rw [List.flatMap_map]
    apply flatMap_congr''
    intro b hb
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hb
    rw [(blkOf_sdl b i (hc.valid b hb).2 (hc.indexed i b hi).1.2).1, hids b hb]
  have hr : (bs.map blkOf).flatMap (fun B => B.descs.flatMap sdlrT) =
      bs.flatMap (fun b => recF (dlRecs b.run.tau ids)) := by
    rw [List.flatMap_map]
    apply flatMap_congr''
    intro b hb
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hb
    rw [(blkOf_sdl b i (hc.valid b hb).2 (hc.indexed i b hi).1.2).2, hids b hb]
  rw [hs, hr, flatMap_tau bs (fun t => recF (dlRecs (t + 1) ids)) 0 (prior_tau hc),
    flatMap_tau bs (fun t => recF (dlRecs t ids)) 0 (prior_tau hc)]
  have hL : (A.p.sched.map Sched.instOf).length = bs.length := by
    rw [List.length_map, sched_length A, hlen]
  have hsend : (Public.schedulerRecords A.p).dlSend = dlRecs 0 ids := by rw [← hI]; rfl
  have hrecv : (Public.schedulerRecords A.p).dlRecv = dlRecs bs.length ids := by
    rw [← hI, ← hL]; rfl
  rw [hsend, hrecv]
  have ht := telescope (fun t => recF (dlRecs t ids)) m bs.length
  have hsh : (List.range' 0 bs.length).flatMap (fun t => recF (dlRecs (t + 1) ids)) =
      (List.range' 1 bs.length).flatMap (fun t => recF (dlRecs t ids)) := by
    rw [← range'_map_succ 0 bs.length, List.flatMap_map]
  rw [hsh]
  exact ht

end RenderBundleV3
end ZkFormal.NearV3.Assembly
