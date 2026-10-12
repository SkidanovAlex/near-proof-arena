import ZkFormal.NearV3.Render.CodecBus
import ZkFormal.NearV3.Render.CodecNatRes

/-!
# Codec traffic closed forms: `BYTES`, `DIGEST`, `S0F`, `SPLEN`

Per-row closed forms (`byT`, `dgT`, `s0T`, `slT`; `rt_*`), the table-level reduction to the descriptor
list (`codec_bus`), and the native identities:
* **`codec_bytes_native`**: the codec's `BYTES` sends over the `PriorCore` blocks are exactly
  `expectedBytes (schedulerSanityJobs 0 (bs.map NativeBlock.witness))` (as field messages);
* **`codec_digest_native`**: the `DIGEST` receives are `expectedDigests (schedulerSanityJobs 0 …)`;
* **`codec_s0f_native`**, **`codec_splen_native`**: one `[τ, pres, vid]` / `[τ, 37 + 24·n²]` per block.
-/
namespace ZkFormal.NearV3.Render.Cdc
open ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen
open ZkFormal.Near ZkFormal.NearV3.Assembly ZkFormal.NearV3.Assembly.CodecDigest NearSpec NearSpecV3
open ZkFormal.NearV3.Candidates
open ZkFormal.NearV3.Candidates.SchedSetAll ZkFormal.NearV3.Sched.Codec ZkFormal.Chacha.Table.E

def byT : Desc → List (List Fp)
  | .hash I _ hpre j => [[Fp.ofNat (11 + 16 * I.tv), Fp.ofNat j, Fp.ofNat (if I.pres then hpre.getD j 0 else 0)]]
  | .ash I ash j => [[Fp.ofNat (11 + 16 * I.tv), Fp.ofNat (32 + j), Fp.ofNat (ash.getD j 0)]]
  | _ => []

def dgT : Desc → List (List Fp)
  | .hash I dig _ j =>
    if j = 0 then [[Fp.ofNat (11 + 16 * I.tv), Fp.ofNat 64] ++ (List.range 32).map fun i => Fp.ofNat (dig.getD i 0)]
    else []
  | _ => []

def s0T : Desc → List (List Fp)
  | .hdr I p => if p = 0 then [[Fp.ofNat I.tv, Fp.ofNat (b2n I.pres), Fp.ofNat I.vid]] else []
  | _ => []

def slT : Desc → List (List Fp)
  | .hdr I p => if p = 0 then [[Fp.ofNat I.tv, Fp.ofNat (37 + 24 * I.N)]] else []
  | _ => []

theorem rt_bytes (d : Desc) (r t : Nat) (pub : List Fp) :
    rowTraffic Codec.table.interactions (dRow d r) t r pub ZkFormal.Near.B_BYTES true = byT d := by
  cases d <;> simp only [byT, bytes_hdr, bytes_rec, bytes_hash, bytes_ash]

theorem rt_digest (d : Desc) (r t : Nat) (pub : List Fp) :
    rowTraffic Codec.table.interactions (dRow d r) t r pub ZkFormal.Near.B_DIGEST false = dgT d := by
  cases d <;> simp only [dgT, digest_hdr, digest_rec, digest_hash, digest_ash]

theorem rt_s0f (d : Desc) (r t : Nat) (pub : List Fp) :
    rowTraffic Codec.table.interactions (dRow d r) t r pub B_S0F false = s0T d := by
  cases d <;> simp only [s0T, s0f_hdr, s0f_rec, s0f_hash, s0f_ash]

theorem rt_splen (d : Desc) (r t : Nat) (pub : List Fp) :
    rowTraffic Codec.table.interactions (dRow d r) t r pub B_SPLEN true = slT d := by
  cases d <;> simp only [slT, splen_hdr, splen_rec, splen_hash, splen_ash]

theorem map_range_getElem! {α : Type} [Inhabited α] (l : List α) :
    (List.range l.length).map (fun r => l[r]!) = l := by
  apply List.ext_getElem (by simp)
  intro n h1 h2
  simp only [List.getElem_map, List.getElem_range]
  exact getElem!_pos l n h2

theorem flat_descs (Bs : List Blk) (G : Desc → List (List Fp)) :
    (allDescs Bs).flatMap G = Bs.flatMap fun B => B.descs.flatMap G := by
  induction Bs with
  | nil => rfl
  | cons B Bs ih =>
    simp only [allDescs] at ih ⊢
    simp only [List.map_cons, List.flatten_cons, List.flatMap_append, List.flatMap_cons, ih]

/-- The table-level traffic on a bus whose row traffic is a function of the descriptor. -/
theorem codec_bus (Bs : List Blk) (hcap : (allDescs Bs).length ≤ 2 ^ 22) (t : Nat) (pub : List Fp)
    (b : Nat) (s : Bool) (G : Desc → List (List Fp))
    (hG : ∀ d r, rowTraffic Codec.table.interactions (dRow d r) t r pub b s = G d) :
    rowsTrafficFp Codec.table.interactions (codecCell Bs) 22 t pub b s = Bs.flatMap fun B => B.descs.flatMap G := by
  rw [rows_traffic Bs hcap]
  simp only [hG]
  have h := congrArg (List.flatMap G) (map_range_getElem! (allDescs Bs))
  rw [List.flatMap_map] at h
  rw [h]
  exact flat_descs Bs G

theorem records_nil (B : Blk) (m : Nat) (G : Desc → List (List Fp))
    (hG : ∀ I R f gg bpo bpr apv apostv bigv, G (.record I R f gg bpo bpr apv apostv bigv) = []) :
    (B.records m).flatMap G = [] := by
  apply List.flatMap_eq_nil_iff.mpr
  intro d hd
  simp only [Blk.records, List.mem_flatten, List.mem_map, List.mem_range] at hd
  obtain ⟨l, ⟨kk, _, rfl⟩, hl⟩ := hd
  simp only [Blk.recordDescs, Blk.fieldDescs, List.mem_append, List.mem_map, List.mem_range] at hl
  rcases hl with ((⟨gg, _, rfl⟩ | ⟨gg, _, rfl⟩) | ⟨gg, _, rfl⟩) <;> exact hG ..

theorem blk_bytes (B : Blk) : B.descs.flatMap byT =
    (List.range 32).map (fun j => [Fp.ofNat (11 + 16 * B.I.tv), Fp.ofNat j,
      Fp.ofNat (if B.I.pres then B.hpre.getD j 0 else 0)]) ++
    (List.range 32).map (fun j => [Fp.ofNat (11 + 16 * B.I.tv), Fp.ofNat (32 + j), Fp.ofNat (B.ash.getD j 0)]) := by
  simp only [Blk.descs, List.flatMap_append, records_nil B _ byT (fun _ _ _ _ _ _ _ _ _ => rfl), List.flatMap_map, byT]
  simp [List.range_succ]

theorem blk_digest (B : Blk) : B.descs.flatMap dgT =
    [[Fp.ofNat (11 + 16 * B.I.tv), Fp.ofNat 64] ++ (List.range 32).map fun i => Fp.ofNat (B.dig.getD i 0)] := by
  simp only [Blk.descs, List.flatMap_append, records_nil B _ dgT (fun _ _ _ _ _ _ _ _ _ => rfl), List.flatMap_map, dgT]
  simp [List.range_succ]

theorem blk_s0f (B : Blk) : B.descs.flatMap s0T = [[Fp.ofNat B.I.tv, Fp.ofNat (b2n B.I.pres), Fp.ofNat B.I.vid]] := by
  simp only [Blk.descs, List.flatMap_append, records_nil B _ s0T (fun _ _ _ _ _ _ _ _ _ => rfl), List.flatMap_map, s0T]
  simp [List.range_succ]

theorem blk_splen (B : Blk) : B.descs.flatMap slT = [[Fp.ofNat B.I.tv, Fp.ofNat (37 + 24 * B.I.N)]] := by
  simp only [Blk.descs, List.flatMap_append, records_nil B _ slT (fun _ _ _ _ _ _ _ _ _ => rfl), List.flatMap_map, slT]
  simp [List.range_succ]

/-! ## Native identities -/

theorem rt8 (l : List Nat) (h : ∀ x ∈ l, x < 256) : (l.map UInt8.ofNat).map UInt8.toNat = l := by
  rw [List.map_map]
  conv => rhs; rw [← List.map_id l]
  apply List.map_congr_left
  intro x hx
  exact UInt8.toNat_ofNat_of_lt' (h x hx)

theorem hpreOf_len (b : NativeBlock) (hb : b.Valid) :
    (hpreOf b).length = 32 ∧ ((ProcPreparedSequence.input b.pub b.old).ash.map (·.toNat)).length = 32 := by
  have ha : b.pub.allShardsHash.length = 32 := schedPub_hash_length hb.2.2.1
  have hsan := prepared_sanity_input (old := b.old) hb.2.1 hb.2.2.1 (by have := hb.2.2.2.1; split <;> simp_all)
  have hl := schedulerSanityJob_length 0 hb.1
  simp only [schedulerSanityJob, hsan, Option.getD_some, List.length_map, codecSanityInput,
    List.length_append] at hl
  refine ⟨?_, by simpa [ProcPreparedSequence.input] using ha⟩
  have ha' : (ProcPreparedSequence.input b.pub b.old).ash.length = 32 := ha
  unfold hpreOf
  split
  · rename_i hp
    simp only [hp, ite_true, List.length_map] at hl
    simp only [List.length_map]
    have := ha'
    simp only [ProcPreparedSequence.input] at hl this ⊢
    omega
  · simp

theorem sanity_bytes (b : NativeBlock) (hb : b.Valid) :
    ((schedulerWitnessSanity b.witness).getD []).map UInt8.toNat =
      hpreOf b ++ (ProcPreparedSequence.input b.pub b.old).ash.map (·.toNat) := by
  rw [prepared_sanity_input (old := b.old) hb.2.1 hb.2.2.1 (by have := hb.2.2.2.1; split <;> simp_all), Option.getD_some]
  have he : codecSanityInput (ProcPreparedSequence.input b.pub b.old) b.prior.isSome =
      (hpreOf b ++ (ProcPreparedSequence.input b.pub b.old).ash.map (·.toNat)).map UInt8.ofNat := by
    unfold codecSanityInput hpreOf; rfl
  rw [he]
  apply rt8
  intro x hx
  rcases List.mem_append.mp hx with h | h
  · unfold hpreOf at h
    split at h
    · exact toNat_lt_of_mem x h
    · simp only [List.mem_replicate] at h; omega
  · exact toNat_lt_of_mem x h

theorem blkOf_bytes (b : NativeBlock) (hb : b.Valid) :
    (blkOf b).descs.flatMap byT = (Sha.Gen.expectedBytes [schedulerSanityJob b.run.tau b.witness]).map Msg.toFp := by
  obtain ⟨h1, h2⟩ := hpreOf_len b hb
  rw [blk_bytes]
  simp only [Sha.Gen.expectedBytes, schedulerSanityJob, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    sanity_bytes b hb, List.length_append, h1, h2, List.range_add, List.map_append, List.map_map]
  congr 1
  · apply List.map_congr_left
    intro j hj
    have hj' := List.mem_range.mp hj
    simp only [Function.comp_apply, Msg.toFp, List.map_cons, List.map_nil, blkOf]
    rw [ZkFormal.Sha.Complete.getD_append_left' _ _ _ (by omega)]
    congr
    by_cases hp : b.prior.isSome = true
    · simp only [hp, ite_true]
    · simp only [hpreOf, hp, Bool.false_eq_true, ite_false]
      simp only [List.getD_eq_getElem?_getD, List.getElem?_replicate, hj', ite_true, Option.getD_some]
  · apply List.map_congr_left
    intro j hj
    simp only [Function.comp_apply, Msg.toFp, List.map_cons, List.map_nil, blkOf]
    rw [ZkFormal.Sha.Complete.getD_append_right' _ _ _ (by omega), h1, Nat.add_sub_cancel_left]

theorem blkOf_digest (b : NativeBlock) (hb : b.Valid) :
    (blkOf b).descs.flatMap dgT = (Sha.Gen.expectedDigests [schedulerSanityJob b.run.tau b.witness]).map Msg.toFp := by
  rw [blk_digest, prepared_sanity_job (old := b.old) hb.1 hb.2.1 hb.2.2.1 (by have := hb.2.2.2.1; split <;> simp_all)]
  simp only [digMsg, List.cons_append, List.nil_append, Msg.toFp, List.map_cons, List.map_nil, blkOf]
  congr 2
  have he : codecSanityInput (ProcPreparedSequence.input b.pub b.old) b.prior.isSome =
      (hpreOf b ++ (ProcPreparedSequence.input b.pub b.old).ash.map (·.toNat)).map UInt8.ofNat := by
    unfold codecSanityInput hpreOf; rfl
  rw [he]
  have hd : (sha256 ((hpreOf b ++ (ProcPreparedSequence.input b.pub b.old).ash.map (·.toNat)).map UInt8.ofNat)).length = 32 :=
    ZkFormal.NearV3.sha256_len _
  generalize sha256 ((hpreOf b ++ (ProcPreparedSequence.input b.pub b.old).ash.map (·.toNat)).map UInt8.ofNat) = D at hd ⊢
  have key : (List.range 32).map (fun i => Fp.ofNat ((D.map (fun x => x.toNat)).getD i 0)) =
      (D.map UInt8.toNat).map Fp.ofNat := by
    apply List.ext_getElem (by simp [hd])
    intro n h1 h2
    simp only [List.length_map, List.length_range] at h1
    simp [List.getD_eq_getElem?_getD, h1, hd]
  rw [key]

/-! ## Over the `PriorCore` block list -/

theorem expectedDigests_cons (x : Sha.Gen.Msg) (l : List Sha.Gen.Msg) :
    Sha.Gen.expectedDigests (x :: l) = Sha.Gen.expectedDigests [x] ++ Sha.Gen.expectedDigests l := by
  simp only [Sha.Gen.expectedDigests, List.filter_cons, List.filter_nil]
  split <;> simp

theorem jobs_bytes (bs : List NativeBlock) (s : Nat) (ht : ∀ i b, bs[i]? = some b → b.run.tau = s + i)
    (hv : ∀ b ∈ bs, b.Valid) :
    bs.flatMap (fun b => (blkOf b).descs.flatMap byT) =
      (Sha.Gen.expectedBytes (schedulerSanityJobs s (bs.map NativeBlock.witness))).map Msg.toFp := by
  induction bs generalizing s with
  | nil => rfl
  | cons b bs ih =>
    have h0 : b.run.tau = s := by simpa using ht 0 b rfl
    have ih' := ih (s + 1) (fun i x hx => by
      have := ht (i + 1) x (by simpa using hx); omega) (fun x hx => hv x (by simp [hx]))
    simp only [List.flatMap_cons, List.map_cons, schedulerSanityJobs]
    rw [ih', blkOf_bytes b (hv b (by simp)), h0]
    simp only [Sha.Gen.expectedBytes, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.map_append]

theorem jobs_digests (bs : List NativeBlock) (s : Nat) (ht : ∀ i b, bs[i]? = some b → b.run.tau = s + i)
    (hv : ∀ b ∈ bs, b.Valid) :
    bs.flatMap (fun b => (blkOf b).descs.flatMap dgT) =
      (Sha.Gen.expectedDigests (schedulerSanityJobs s (bs.map NativeBlock.witness))).map Msg.toFp := by
  induction bs generalizing s with
  | nil => rfl
  | cons b bs ih =>
    have h0 : b.run.tau = s := by simpa using ht 0 b rfl
    have ih' := ih (s + 1) (fun i x hx => by
      have := ht (i + 1) x (by simpa using hx); omega) (fun x hx => hv x (by simp [hx]))
    simp only [List.flatMap_cons, List.map_cons, schedulerSanityJobs]
    rw [ih', blkOf_digest b (hv b (by simp)), h0,
      expectedDigests_cons (schedulerSanityJob s b.witness) (schedulerSanityJobs (s + 1) _), List.map_append]

theorem prior_cap {p : Prep} {B : Nat} {bs : List NativeBlock} (hc : PriorCore p B bs) :
    (allDescs (bs.map blkOf)).length ≤ 2 ^ 22 := by
  have := blocks_length bs (fun b hb => (hc.valid b hb).2)
  have := hc.length
  omega

theorem prior_tau {p : Prep} {B : Nat} {bs : List NativeBlock} (hc : PriorCore p B bs) :
    ∀ i b, bs[i]? = some b → b.run.tau = 0 + i := fun i b hi => by
  rw [Nat.zero_add]; exact (hc.indexed i b hi).2.1

/-- **`BYTES`: the codec sends exactly the scheduler sanity jobs' bytes of the `PriorCore` blocks.** -/
theorem codec_bytes_native {p : Prep} {B : Nat} {bs : List NativeBlock} (hc : PriorCore p B bs)
    (t : Nat) (pub : List Fp) :
    rowsTrafficFp Codec.table.interactions (codecCell (bs.map blkOf)) 22 t pub ZkFormal.Near.B_BYTES true =
      (Sha.Gen.expectedBytes (schedulerSanityJobs 0 (bs.map NativeBlock.witness))).map Msg.toFp := by
  rw [codec_bus _ (prior_cap hc) t pub _ _ byT (rt_bytes · · t pub), List.flatMap_map]
  exact jobs_bytes bs 0 (prior_tau hc) (fun b hb => (hc.valid b hb).1)

/-- **`DIGEST`: the codec receives exactly the scheduler sanity jobs' digests.** -/
theorem codec_digest_native {p : Prep} {B : Nat} {bs : List NativeBlock} (hc : PriorCore p B bs)
    (t : Nat) (pub : List Fp) :
    rowsTrafficFp Codec.table.interactions (codecCell (bs.map blkOf)) 22 t pub ZkFormal.Near.B_DIGEST false =
      (Sha.Gen.expectedDigests (schedulerSanityJobs 0 (bs.map NativeBlock.witness))).map Msg.toFp := by
  rw [codec_bus _ (prior_cap hc) t pub _ _ dgT (rt_digest · · t pub), List.flatMap_map]
  exact jobs_digests bs 0 (prior_tau hc) (fun b hb => (hc.valid b hb).1)

theorem flat_single {α β : Type} (l : List α) (f : α → β) : l.flatMap (fun a => [f a]) = l.map f := by
  induction l <;> simp_all

/-- **`S0F`: one `[τ, pres, vid]` per block.** -/
theorem codec_s0f_native {p : Prep} {B : Nat} {bs : List NativeBlock} (hc : PriorCore p B bs)
    (t : Nat) (pub : List Fp) :
    rowsTrafficFp Codec.table.interactions (codecCell (bs.map blkOf)) 22 t pub B_S0F false =
      bs.map fun b => [Fp.ofNat b.run.tau, Fp.ofNat (b2n b.prior.isSome), Fp.ofNat b.vid] := by
  rw [codec_bus _ (prior_cap hc) t pub _ _ s0T (rt_s0f · · t pub), List.flatMap_map]
  simp only [blk_s0f]
  exact flat_single _ _

/-- **`SPLEN`: one `[τ, 37 + 24·n²]` per block.** -/
theorem codec_splen_native {p : Prep} {B : Nat} {bs : List NativeBlock} (hc : PriorCore p B bs)
    (t : Nat) (pub : List Fp) :
    rowsTrafficFp Codec.table.interactions (codecCell (bs.map blkOf)) 22 t pub B_SPLEN true =
      bs.map fun b => [Fp.ofNat b.run.tau, Fp.ofNat (37 + 24 * (b.run.n * b.run.n))] := by
  rw [codec_bus _ (prior_cap hc) t pub _ _ slT (rt_splen · · t pub), List.flatMap_map]
  simp only [blk_splen]
  exact flat_single _ _

theorem cnt_natMsgs (l : List (List Fp)) (m : List Fp) : ZkFormal.Near.cnt (natMsgs l) m = l.count m := by
  unfold ZkFormal.Near.cnt; rw [natMsgs_toFp]

/-- The codec premises of `rcpt_trie_side`, for the scheduler upsert witnesses of the `PriorCore` blocks. -/
theorem codec_sha_counts {p : Prep} {B : Nat} {bs : List NativeBlock} (hc : PriorCore p B bs) (pub : List Fp) :
    (∀ m, ZkFormal.Near.cnt ((rowsTraffic Codec.table.interactions (codecCell (bs.map blkOf)) 22 11 pub).sends
        ZkFormal.Near.B_BYTES) m =
      ZkFormal.Near.cnt (Sha.Gen.expectedBytes (schedulerSanityJobs 0 (bs.map NativeBlock.witness))) m) ∧
    (∀ m, ZkFormal.Near.cnt ((rowsTraffic Codec.table.interactions (codecCell (bs.map blkOf)) 22 11 pub).recvs
        ZkFormal.Near.B_DIGEST) m =
      ZkFormal.Near.cnt (Sha.Gen.expectedDigests (schedulerSanityJobs 0 (bs.map NativeBlock.witness))) m) := by
  refine ⟨fun m => ?_, fun m => ?_⟩
  · simp only [rowsTraffic]
    rw [cnt_natMsgs, codec_bytes_native hc]
    simp only [ZkFormal.Near.cnt]
  · simp only [rowsTraffic]
    rw [cnt_natMsgs, codec_digest_native hc]
    simp only [ZkFormal.Near.cnt]

/-- The sanity jobs only see `schedulerWitnessSanity`. -/
theorem jobs_congr (s : Nat) (us vs : List SchedulerUpsertWitness)
    (h : us.map schedulerWitnessSanity = vs.map schedulerWitnessSanity) :
    schedulerSanityJobs s us = schedulerSanityJobs s vs := by
  induction us generalizing s vs with
  | nil => cases vs with
    | nil => rfl
    | cons _ _ => simp at h
  | cons u us ih => cases vs with
    | nil => simp at h
    | cons v vs =>
      simp only [List.map_cons, List.cons.injEq] at h
      simp only [schedulerSanityJobs, schedulerSanityJob, h.1, ih (s + 1) vs h.2]

/-- **The codec premises of `rcpt_trie_side` for any `us` pinned to the `PriorCore` blocks** (same
sanity inputs per instance). -/
theorem codec_sha_counts_pinned {p : Prep} {B : Nat} {bs : List NativeBlock} (hc : PriorCore p B bs)
    (pub : List Fp) (us : List SchedulerUpsertWitness)
    (hpin : us.map schedulerWitnessSanity = (bs.map NativeBlock.witness).map schedulerWitnessSanity) :
    (∀ m, ZkFormal.Near.cnt ((rowsTraffic Codec.table.interactions (codecCell (bs.map blkOf)) 22 11 pub).sends
        ZkFormal.Near.B_BYTES) m = ZkFormal.Near.cnt (Sha.Gen.expectedBytes (schedulerSanityJobs 0 us)) m) ∧
    (∀ m, ZkFormal.Near.cnt ((rowsTraffic Codec.table.interactions (codecCell (bs.map blkOf)) 22 11 pub).recvs
        ZkFormal.Near.B_DIGEST) m = ZkFormal.Near.cnt (Sha.Gen.expectedDigests (schedulerSanityJobs 0 us)) m) := by
  rw [jobs_congr 0 us _ hpin]
  exact codec_sha_counts hc pub

end ZkFormal.NearV3.Render.Cdc
