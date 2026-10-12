import ZkFormal.NearV3.Render.CodecSpost

/-!
# Codec `VBYTES` (bus 21) closed form: per row and per block

`bus_vbytes`: a codec row sends `VBYTES (vid, pos, bpre)` with multiplicity `vbg`.  Per row kind
(`vbytes_hdr/rec/hash/ash`): header, record and sanity-hash rows of a block with a present prior send
`[vid, pos, bpre]`, every other row nothing.  `vbT`: these per-row sends; **`blk_vbytes`**: a block's
`VBYTES` sends are `posMsgs vid 0 (stateBytes ids a0 hpre)` when its prior is present, `[]` otherwise
(the canonical prior bytes: header, the 24-byte records with the prior allowances, the prior sanity
hash), under `N = n²`, `N < 65536`, `|hpre| = 32`.
-/
set_option linter.unusedSimpArgs false

namespace ZkFormal.NearV3.Render.Cdc
open ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen
open ZkFormal.Near ZkFormal.NearV3.Candidates.SchedSetAll ZkFormal.NearV3.Sched.Codec

set_option maxRecDepth 65536 in
theorem bus_vbytes (d : Desc) (r t : Nat) (pub : List Fp) :
    rowTraffic Codec.table.interactions (dRow d r) t r pub ZkFormal.NearV3.B_VBYTES true =
      List.replicate (if cv d vbg = 1 then 1 else 0) [cv d vid, cv d pos, cv d bpre] := by
  simp only [rowTraffic, Codec.table, interactions, List.flatMap_cons, List.flatMap_nil,
    ZkFormal.NearV3.B_S0F, Sched.B_S0F, ZkFormal.NearV3.B_SPLEN, ZkFormal.NearV3.B_SPOST, ZkFormal.NearV3.B_VBYTES, Sched.B_SPOST, ZkFormal.Near.B_BYTES,
    ZkFormal.Near.B_DIGEST, Sched.B_SPLEN, Sched.B_SPAR, Sched.B_SDL, Sched.B_SPUBB, Sched.B_SOP,
    Sched.B_SFIN, Sched.B_SDG, Sched.B_SA0, Sched.B_SCMP]
  simp only [Nat.reduceEqDiff, Bool.false_eq_true, and_false, and_true, false_and, true_and,
    ite_false, ite_true, List.append_nil, List.nil_append]
  simp only [Interaction.multNat, mult1, Interaction.msgVal, List.map_cons, List.map_nil]
  rfl

theorem b2n_one (p : Bool) : ((Fp.ofNat (Gen.b2n p) : Fp) = 1) ↔ p = true := by
  cases p <;> simp [Gen.b2n] <;> decide

set_option maxRecDepth 65536 in
theorem vbytes_hdr (I : Inst) (p r t : Nat) (pub : List Fp) :
    rowTraffic Codec.table.interactions (dRow (.hdr I p) r) t r pub ZkFormal.NearV3.B_VBYTES true =
      if I.pres then [[Fp.ofNat I.vid, Fp.ofNat p, Fp.ofNat ((hdrBytes I).getD p 0)]] else [] := by
  rw [bus_vbytes]
  simp only [cv, Desc.asg]
  cdc_cell
  cases h : I.pres <;> simp [Gen.b2n, o1, z1]

set_option maxRecDepth 65536 in
theorem vbytes_rec (I : Inst) (R : Rec) (f gg bpo bpr apv apostv bigv r t : Nat) (pub : List Fp) :
    rowTraffic Codec.table.interactions (dRow (.record I R f gg bpo bpr apv apostv bigv) r) t r pub
        ZkFormal.NearV3.B_VBYTES true =
      if I.pres then [[Fp.ofNat I.vid, Fp.ofNat (5 + 24 * R.kk + 8 * f + gg), Fp.ofNat bpr]] else [] := by
  rw [bus_vbytes]
  simp only [cv, Desc.asg]
  cdc_cell
  cases h : I.pres <;> simp [Gen.b2n, o1, z1]

set_option maxRecDepth 65536 in
theorem vbytes_hash (I : Inst) (dig hpre : List Nat) (j r t : Nat) (pub : List Fp) :
    rowTraffic Codec.table.interactions (dRow (.hash I dig hpre j) r) t r pub ZkFormal.NearV3.B_VBYTES true =
      if I.pres then [[Fp.ofNat I.vid, Fp.ofNat (5 + 24 * I.N + j), Fp.ofNat (hpre.getD j 0)]] else [] := by
  rw [bus_vbytes]
  simp only [cv, Desc.asg]
  cdc_cell
  cases h : I.pres <;> simp [Gen.b2n, o1, z1]

set_option maxRecDepth 65536 in
theorem vbytes_ash (I : Inst) (ash : List Nat) (j r t : Nat) (pub : List Fp) :
    rowTraffic Codec.table.interactions (dRow (.ash I ash j) r) t r pub ZkFormal.NearV3.B_VBYTES true = [] := by
  rw [bus_vbytes]
  simp only [cv, Desc.asg]
  cdc_cell
  simp [z1]


/-- The per-row `VBYTES` sends. -/
def vbT : Desc → List (List Fp)
  | .hdr I p => if I.pres then [[Fp.ofNat I.vid, Fp.ofNat p, Fp.ofNat ((hdrBytes I).getD p 0)]] else []
  | .record I R f gg _ bpr _ _ _ =>
    if I.pres then [[Fp.ofNat I.vid, Fp.ofNat (5 + 24 * R.kk + 8 * f + gg), Fp.ofNat bpr]] else []
  | .hash I _ hpre j => if I.pres then [[Fp.ofNat I.vid, Fp.ofNat (5 + 24 * I.N + j), Fp.ofNat (hpre.getD j 0)]] else []
  | .ash .. => []

theorem rt_vbytes (d : Desc) (r t : Nat) (pub : List Fp) :
    rowTraffic Codec.table.interactions (dRow d r) t r pub ZkFormal.NearV3.B_VBYTES true = vbT d := by
  cases d <;> simp only [vbT, vbytes_hdr, vbytes_rec, vbytes_hash, vbytes_ash]

theorem vhdr_part (I : Inst) (hN : I.N < 65536) (hp : I.pres = true) :
    ((List.range 5).map (Desc.hdr I)).flatMap vbT = posMsgs I.vid 0 ([0] ++ bytesLE I.N 4) := by
  have h1 : I.N / 256 ^ 2 = 0 := Nat.div_eq_of_lt (by simpa using hN)
  have h2 : I.N / 256 ^ 3 = 0 := Nat.div_eq_of_lt (by have : (256:Nat) ^ 3 = 16777216 := rfl; omega)
  simp [posMsgs, vbT, hp, hdrBytes, bytesLE, List.range_succ, h1, h2]

theorem vrec_part (B : Blk) (kk : Nat) (hk : (B.recs kk).kk = kk) (hp : B.I.pres = true) :
    (B.recordDescs kk).flatMap vbT = posMsgs B.I.vid (5 + 24 * kk)
      (bytesLE (B.ids.getD (kk / B.ids.length) 0) 8 ++ bytesLE (B.ids.getD (kk % B.ids.length) 0) 8 ++
        bytesLE (B.a0 kk) 8) := by
  simp only [Blk.recordDescs, Blk.fieldDescs, Blk.recD, List.flatMap_append, List.flatMap_map, vbT, hk, hp,
    posMsgs, bytesLE, List.length_append, List.length_map, List.length_range, List.range_succ, List.range_zero,
    List.nil_append, List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil, List.cons_append,
    List.append_nil, ite_true]
  have r24 : List.range 24 = [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := rfl
  simp [Blk.bpr, Blk.bpo, hp, idByte, List.getD_eq_getElem?_getD, Nat.add_assoc, r24]

theorem vhash_part (I : Inst) (dig hpre : List Nat) (hd : hpre.length = 32) (hp : I.pres = true) :
    ((List.range 32).map (Desc.hash I dig hpre)).flatMap vbT = posMsgs I.vid (5 + 24 * I.N) hpre := by
  simp only [List.flatMap_map, vbT, posMsgs, hd, hp, ite_true]
  induction (List.range 32) <;> simp_all

theorem blk_vbytes (B : Blk) (hOk : B.Ok) (hN : B.I.N = B.ids.length * B.ids.length)
    (hd : B.hpre.length = 32) :
    B.descs.flatMap vbT = if B.I.pres then posMsgs B.I.vid 0 (stateBytes B.ids B.a0 B.hpre) else [] := by
  cases hp : B.I.pres with
  | false =>
    apply List.flatMap_eq_nil_iff.mpr
    intro d hd'
    unfold Blk.descs at hd'
    simp only [List.mem_append, List.mem_map, Blk.records, List.mem_flatten] at hd'
    rcases hd' with ((⟨p, -, rfl⟩ | ⟨L, ⟨kk, -, rfl⟩, hL⟩) | ⟨j, -, rfl⟩) | ⟨j, -, rfl⟩
    · simp [vbT, hp]
    · simp only [Blk.recordDescs, Blk.fieldDescs, List.mem_append, List.mem_map] at hL
      rcases hL with (⟨gg, -, rfl⟩ | ⟨gg, -, rfl⟩) | ⟨gg, -, rfl⟩ <;> simp [Blk.recD, vbT, hp]
    · simp [vbT, hp]
    · simp [vbT]
  | true =>
    have hN6 : B.I.N < 65536 := hOk.inst.2.1
    have hF : ∀ k, (bytesLE (B.ids.getD (k / B.ids.length) 0) 8 ++ bytesLE (B.ids.getD (k % B.ids.length) 0) 8 ++
        bytesLE (B.a0 k) 8).length = 24 := fun k => by simp [bytesLE]
    have hX : ((List.range (B.ids.length * B.ids.length)).flatMap fun k =>
        bytesLE (B.ids.getD (k / B.ids.length) 0) 8 ++ bytesLE (B.ids.getD (k % B.ids.length) 0) 8 ++
          bytesLE (B.a0 k) 8).length = 24 * (B.ids.length * B.ids.length) := by
      rw [List.length_flatMap]
      have : ∀ L : List Nat, (L.map fun k => (bytesLE (B.ids.getD (k / B.ids.length) 0) 8 ++
          bytesLE (B.ids.getD (k % B.ids.length) 0) 8 ++ bytesLE (B.a0 k) 8).length).sum = 24 * L.length := by
        intro L; induction L with
        | nil => rfl
        | cons x L ih => rw [List.map_cons, List.sum_cons, ih, hF, List.length_cons]; omega
      exact (this _).trans (by rw [List.length_range])
    simp only [ite_true]
    unfold Blk.descs stateBytes
    simp only [List.flatMap_append]
    have hash0 : ((List.range 32).map (Desc.ash B.I B.ash)).flatMap vbT = [] := by
      simp [vbT]
    rw [hash0, List.append_nil, vhdr_part B.I hN6 hp, vhash_part B.I B.dig B.hpre hd hp, Blk.records,
      flatten_flatMap]
    conv => rhs; rw [posMsgs_append, posMsgs_append, posMsgs_flat _ _ 24 _ hF]
    have hb4 : (bytesLE (B.ids.length * B.ids.length) 4).length = 4 := by simp [bytesLE]
    simp only [List.length_append, hX, hb4, List.length_cons, List.length_nil]
    rw [← hN]
    congr 1
    · congr 1
      apply flatMap_congr_rt
      intro kk hkk
      have hk := List.mem_range.mp hkk
      rw [vrec_part B kk (hOk.kk kk hk) hp]
    · congr 1
      omega

end ZkFormal.NearV3.Render.Cdc
