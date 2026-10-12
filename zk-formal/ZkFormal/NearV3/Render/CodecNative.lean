import ZkFormal.NearV3.Render.CodecRender
import ZkFormal.NearV3.Assembly.SchedulerPriorCore
import ZkFormal.NearV3.Candidates.ProcActualAllowanceBound
import ZkFormal.NearV3.Candidates.ProcPriorCodecHeaderInitial
import ZkFormal.NearV3.Sched.Link.InitCodec

/-!
# The honest codec blocks of the native scheduler runs (table 11 from acceptance)

`blkOf b`: the frozen codec block of one native block (`NativeBlock`: the same native choice as the
proc/ssd/mem/cmp renders and `PriorCore`): instance constants from the run and its public input, the
canonical prior allowances `a0Canon`, per link the source map (`srcOf`), grants, the run's final link
values, the instance-0 forwarding demand, and the sanity-hash bytes.

`blkOf_ok`: `Blk.Ok (blkOf b)` from the run and its public input, up to the residual premises
`NatRes b` (value id `< P`; grants and final grant values `< 2^26`; the instance-0 forwarding demands
`< 2^24`).  `codec_accepted`: from `checkD0a B0` acceptance, the `PriorCore` block list `bs` gives,
under `∀ b ∈ bs, NatRes b`, a `TableRenderV3` for table 11 with trace `codecTrace (allDescs (bs.map blkOf))`.
-/
namespace ZkFormal.NearV3.Render.Cdc
open ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen ZkFormal.NearV3.Candidates
open ZkFormal.NearV3.Assembly ZkFormal.NearV3.Assembly.CodecDigest NearSpec NearSpecV3 NearSpecV3.Scheduler

/-- The forwarding demand of link `kk` (instance 0). -/
def demand (fwd : List (Nat × Nat)) (kk : Nat) : Nat := ((fwd.find? (·.1 == kk)).map (·.2)).getD 0

/-- The previous sanity hash bytes (zeros when absent). -/
def hpreOf (b : NativeBlock) : List Nat :=
  if b.prior.isSome then (ProcPreparedSequence.input b.pub b.old).prev.sanityHash.map (·.toNat)
  else List.replicate 32 0

/-- The frozen codec block of a native block. -/
def blkOf (b : NativeBlock) : Blk :=
  let I := ProcPreparedSequence.input b.pub b.old
  let R := b.run
  let N := R.n * R.n
  let a0 := a0Canon R.n I.prev
  { I := ⟨R.tau, R.n, N, b.prior.isSome, b.vid, I.p.base, I.p.maxShardBandwidth / R.n⟩
    ids := I.ids
    a0 := fun kk => a0[kk]!
    recs := fun kk =>
      { kk := kk, srcS := (srcOf I.ids kk).getD 0, hasC := (srcOf I.ids kk).isSome,
        useC := (List.range N).any fun l' => srcOf I.ids l' == some kk,
        al := I.allowed[kk]!,
        a0s := match srcOf I.ids kk with
          | some k' => if b.prior.isSome then a0[k']! else 0
          | none => 0,
        gb := b.grants[kk]!, afin := (R.segs.getD kk default).vfin,
        gfin := (R.segs.getD kk default).wfin,
        ft := if R.tau = 0 then demand b.forwarded kk else 0,
        iklv := inv (fsub kk (N - 1)) }
    dig := (NearSpec.sha256 ((hpreOf b ++ I.ash.map (·.toNat)).map UInt8.ofNat)).map (·.toNat)
    hpre := hpreOf b
    ash := I.ash.map (·.toNat) }

/-- Residual native premises of one block (not yet derived from the run). -/
structure NatRes (b : NativeBlock) : Prop where
  vid : b.vid < ZkFormal.Algebra.P
  gb : ∀ kk < b.run.n * b.run.n, b.grants[kk]! < 2 ^ 26
  gfin : ∀ kk < b.run.n * b.run.n, (b.run.segs.getD kk default).wfin < 2 ^ 26
  ft : b.run.tau = 0 → ∀ kk < b.run.n * b.run.n, demand b.forwarded kk < 2 ^ 24

/-- PV86: the base grant is at most the fair share, for every `1 ≤ n ≤ 64`. -/
theorem base_le_fair (n : Nat) (p : Params) (hp : Params.calculate Config.pv86 n = some p)
    (h1 : 1 ≤ n) (h64 : n ≤ 64) : p.base ≤ p.maxShardBandwidth / n := by
  rw [lp_calc hp]
  have key : ∀ m < 65, 1 ≤ m → Nat.min (305696 / Nat.max 1 (m - 1)) 100000 ≤ 4500000 / m := by
    decide
  exact key n (by omega) h1

theorem toNat_lt_of_mem {l : List UInt8} : ∀ x ∈ l.map (·.toNat), x < 256 := by
  intro x hx
  simp only [List.mem_map] at hx
  obtain ⟨y, _, rfl⟩ := hx
  exact y.toNat_lt

theorem blkOf_ok (b : NativeBlock) (hn : b.run.n ≤ 64) (tau : Nat) (htau : tau < 32)
    (hr : ActualRun.run (ProcPreparedSequence.input b.pub b.old) tau = .ok b.run)
    (hs : SchedPubOk b.pub) (hres : NatRes b) : (blkOf b).Ok := by
  obtain ⟨ht, hnI, _⟩ := ProcActualRunProjection.run_fields _ tau b.run hr
  have hids : (ProcPreparedSequence.input b.pub b.old).ids = b.pub.ids := rfl
  have hpar : Params.calculate Config.pv86 (ProcPreparedSequence.input b.pub b.old).ids.length =
      some (ProcPreparedSequence.input b.pub b.old).p := hs.params
  obtain ⟨hNN, hbase, hfair⟩ := ProcPriorCodecHeaderInitial.native_bounds _ b.run hpar hn
  have hn1 : 1 ≤ b.run.n := by rw [hnI, hids]; exact hs.n1
  have hbf := base_le_fair _ _ hpar (by rw [← hnI]; exact hn1) (by rw [← hnI]; exact hn)
  rw [← hnI] at hbf
  have hkI : ∀ kk, kk < b.run.n * b.run.n → kk < b.pub.ids.length * b.pub.ids.length := by
    intro kk hk; rw [hnI, hids] at hk; exact hk
  refine
    { inst := ⟨?_, hNN, by simp [blkOf], hbase, hfair⟩
      N1 := by simp only [blkOf]; exact Nat.mul_le_mul hn1 hn1
      kk := fun _ _ => rfl
      ikl := fun _ _ => rfl
      afin := fun kk hk => ProcActualAllowanceBound.successful_run b.pub hs b.old tau b.run hr kk (hkI kk hk)
      hasC := fun kk _ h => ?_
      ft := fun kk hk => ?_
      al := fun kk _ => ?_
      dig := toNat_lt_of_mem
      hpre := ?_
      ashB := toNat_lt_of_mem
      vid := hres.vid
      n := by simp only [blkOf]; omega
      src := fun kk _ => ?_
      gb := hres.gb
      gfin := hres.gfin }
  · simp only [blkOf]; rw [ht]; unfold ZkFormal.Algebra.P; omega
  · simp only [blkOf, Option.isSome_eq_false_iff, Option.isNone_iff_eq_none] at h ⊢
    simp [apRv, bigRv, h]
  · simp only [blkOf]
    split
    · exact hres.ft (by assumption) kk hk
    · decide
  · simp only [blkOf]
    have hle : b2n (ProcPreparedSequence.input b.pub b.old).allowed[kk]! * b.pub.params.base ≤
        b.pub.params.base := by
      cases (ProcPreparedSequence.input b.pub b.old).allowed[kk]! <;> simp [b2n]
    have hge : (ProcPreparedSequence.input b.pub b.old).p.maxShardBandwidth / b.run.n ≤
        a1v ⟨b.run.tau, b.run.n, b.run.n * b.run.n, b.prior.isSome, b.vid,
          (ProcPreparedSequence.input b.pub b.old).p.base,
          (ProcPreparedSequence.input b.pub b.old).p.maxShardBandwidth / b.run.n⟩
          ((blkOf b).recs kk) := by
      have hm : (ProcPreparedSequence.input b.pub b.old).p.maxShardBandwidth = 4500000 := by
        rw [lp_calc hpar]
      rw [a1v_def]
      dsimp only
      rw [hm]
      have hd := Nat.div_le_self 4500000 b.run.n
      have hMA : Codec.MA = 4500000 := rfl
      split
      · omega
      · split <;> omega
    exact Nat.le_trans hle (Nat.le_trans hbf hge)
  · intro x hx
    simp only [blkOf, hpreOf] at hx
    split at hx
    · exact toNat_lt_of_mem x hx
    · simp only [List.mem_replicate] at hx; omega
  · simp only [blkOf]
    cases hs' : srcOf (ProcPreparedSequence.input b.pub b.old).ids kk with
    | none => simp; unfold ZkFormal.Algebra.P; omega
    | some s =>
      have h1 := srcOf_lt hs'
      rw [hids] at h1
      have h64 : b.pub.ids.length ≤ 64 := hs.n64
      have := Nat.mul_le_mul h64 h64
      simp only [Option.getD_some]
      unfold ZkFormal.Algebra.P; omega

theorem blocks_length (bs : List NativeBlock) (hn : ∀ b ∈ bs, b.run.n ≤ 64) :
    (allDescs (bs.map blkOf)).length ≤ 98373 * bs.length := by
  induction bs with
  | nil => simp [allDescs]
  | cons b bs ih =>
    have h1 : (blkOf b).descs.length = 5 + 24 * (b.run.n * b.run.n) + 64 := (blkOf b).descs_length
    have hb := hn b (by simp)
    have hsq := Nat.mul_le_mul hb hb
    have h2 := ih (fun x hx => hn x (by simp [hx]))
    simp only [allDescs, List.map_cons, List.flatten_cons, List.length_append, List.length_cons] at h2 ⊢
    omega

end ZkFormal.NearV3.Render.Cdc

namespace ZkFormal.NearV3.Render
open ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Assembly ZkFormal.NearV3.Assembly.CodecDigest
open NearSpec NearSpecV3 Cdc

/-- **Table 11 from acceptance** (frozen codec over the `PriorCore` native blocks), under the residual
per-block premises `NatRes`. -/
theorem codec_accepted {cb wb : Bytes} {hint : Hint} {p : Prep} (hp : prepD0 cb hint = .ok p)
    {k : WalkD0} {w : StateWitness} (hk : walkD0 cb = .ok k) (hw : decodeW wb = .ok w)
    (h : checkD0a B0 cb wb = .ok ()) (pub : List Fp) :
    ∃ bs : List NativeBlock, PriorCore p B0 bs ∧ ((∀ b ∈ bs, NatRes b) →
      ∃ R : TableRenderV3 pub 11 (by decide), R.tr = codecTrace (allDescs (bs.map blkOf)) ∧
        R.tf = rowsTraffic Codec.table.interactions (codecCell (bs.map blkOf)) 22 11 pub) := by
  obtain ⟨bs, hc⟩ := accepted_prior_core hp hk hw h (by decide)
  refine ⟨bs, hc, fun hres => ?_⟩
  have hok : ∀ B ∈ bs.map blkOf, B.Ok := by
    intro B hB
    simp only [List.mem_map] at hB
    obtain ⟨b, hb, rfl⟩ := hB
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hb
    obtain ⟨⟨hsch, hrun⟩, _, _⟩ := hc.indexed i b hi
    have hil : i < bs.length := (List.getElem?_eq_some_iff.mp hi).1
    exact blkOf_ok b (hc.valid b hb).2 i (by have := hc.length; omega) hrun
      (prepD0_sched hp b.pub (List.mem_of_getElem? hsch)) (hres b hb)
  have hcap : (allDescs (bs.map blkOf)).length < 2 ^ 22 := by
    have := blocks_length bs (fun b hb => (hc.valid b hb).2)
    have := hc.length
    omega
  exact ⟨codecRenderV3 pub (bs.map blkOf) hok hcap, rfl, rfl⟩

end ZkFormal.NearV3.Render
