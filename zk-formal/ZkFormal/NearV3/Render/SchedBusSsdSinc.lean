import ZkFormal.NearV3.Render.SchedBusSsdOps
import ZkFormal.NearV3.Sched.View.ScanSpec

/-!
# Scan rows (table 12): the `SINC` sends of a converted request

Row `ρ` of request `c` sends slot 0 (bit `2ρ`) and slot 1 (bit `2ρ + 1`) when the bit is set and the
increase with that index is processed (`R.used`).  With the scan state `stAt` (`View/ScanSpec`) the
message is `(τ, 64·cid + j, incs[j], |incs| − j − 1, s, r, link)` for the bit's index `j`; over the
request this is every processed index exactly once (`req_sinc_block`).
-/
set_option linter.unusedSimpArgs false
set_option autoImplicit false
namespace ZkFormal.NearV3.Render.SsdBus
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen
open ZkFormal.NearV3.Candidates ZkFormal.NearV3.Render.Ssd NearSpecV3.Scheduler

theorem fp_sub (a b : Nat) (h : b ≤ a) : Fp.ofNat a + -Fp.ofNat b = Fp.ofNat (a - b) := by
  have e : Fp.ofNat a = Fp.ofNat (a - b) + Fp.ofNat b := by rw [ofNat_add']; congr 1; omega
  rw [e]; grind

theorem b2n_fp (x : Bool) : (Fp.ofNat (b2n x) = 1) ↔ x = true := by
  cases x <;> simp [b2n] <;> decide

theorem app_congr {α : Type} {a b c d : List α} (h1 : a = c) (h2 : b = d) : a ++ b = c ++ d := by rw [h1, h2]

open ProcScanRequestFactor in
set_option maxRecDepth 16384 in
theorem req_sinc (R : Run) (c : CReq) (rho jj cv : Nat) :
    sincM (fx (row R c rho jj cv)) =
      (if (getBit c.bm (2 * rho) && (R.used.getD c.cid #[]).getD jj false) = true then
        [[Fp.ofNat R.tau, Fp.ofNat (64 * c.cid + jj), Fp.ofNat (R.base + R.D * (2 * rho + 1) / 40) + -Fp.ofNat cv,
          Fp.ofNat c.bits.length + -Fp.ofNat jj + -Fp.ofNat 1, Fp.ofNat c.s, Fp.ofNat c.r, Fp.ofNat c.link]] else []) ++
      (if (getBit c.bm (2 * rho + 1) && (R.used.getD c.cid #[]).getD (jj + b2n (getBit c.bm (2 * rho))) false) = true then
        [[Fp.ofNat R.tau, Fp.ofNat (64 * c.cid + jj + b2n (getBit c.bm (2 * rho))),
          Fp.ofNat (R.base + R.D * (2 * rho + 2) / 40) +
            -Fp.ofNat (if b2n (getBit c.bm (2 * rho)) = 1 then R.base + R.D * (2 * rho + 1) / 40 else cv),
          Fp.ofNat c.bits.length + -Fp.ofNat jj + -Fp.ofNat (b2n (getBit c.bm (2 * rho))) + -Fp.ofNat 1,
          Fp.ofNat c.s, Fp.ofNat c.r, Fp.ofNat c.link]] else []) := by
  obtain ⟨-, -, -, htau, -, hbase, hdd, hcid⟩ := ProcScanRequestCells.controls R c rho jj cv
  obtain ⟨hs, hr, hlink, -, hm, -, -⟩ := ProcScanRequestCells.payload R c rho jj cv
  obtain ⟨hj, hcur, hcm, hb0, -, -, -, -⟩ := ProcScanRequestCells.progress R c rho jj cv
  obtain ⟨hQ0, hQ1, -, -⟩ := ProcScanRequestCells.quotients R c rho jj cv
  obtain ⟨hu0, hu1⟩ := ProcScanRequestQuietCells.uses R c rho jj cv
  rw [ProcScanRequestArithmetic.position] at hcm hb0 hQ0 hQ1 hu0 hu1
  have e1 := fx_of htau
  have e2 := fx_of hbase
  have e3 := fx_of hcid
  have e4 := fx_of hs
  have e5 := fx_of hr
  have e6 := fx_of hlink
  have e7 := fx_of hm
  have e8 := fx_of hj
  have e9 := fx_of hcur
  have e10 := fx_of hcm
  have e11 := fx_of hb0
  have e12 := fx_of hQ0
  have e13 := fx_of hQ1
  have e14 := fx_of hu0
  have e15 := fx_of hu1
  generalize fx (row R c rho jj cv) = x at *
  simp only [sincM, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, natCast_fp, ofNat_mul',
    ofNat_add']
  refine app_congr ?_ ?_
  · by_cases h : (getBit c.bm (2 * rho) && (R.used.getD c.cid #[]).getD jj false) = true
    · have h' : (b2n (getBit c.bm (2 * rho)) == 1 && (R.used.getD c.cid #[]).getD jj false) = true := by
        simp only [Bool.and_eq_true] at h ⊢; cases hb : getBit c.bm (2 * rho) <;> simp_all [b2n]
      rw [if_pos ((b2n_fp _).mpr h'), if_pos h]
      simp [ofNat_add']
    · have h' : ¬ (b2n (getBit c.bm (2 * rho)) == 1 && (R.used.getD c.cid #[]).getD jj false) = true := by
        simp only [Bool.and_eq_true] at h ⊢; cases hb : getBit c.bm (2 * rho) <;> simp_all [b2n]
      rw [if_neg (fun e => h' ((b2n_fp _).mp e)), if_neg h]; rfl
  · by_cases h : (getBit c.bm (2 * rho + 1) && (R.used.getD c.cid #[]).getD (jj + b2n (getBit c.bm (2 * rho))) false) = true
    · have h' : (b2n (getBit c.bm (2 * rho + 1)) == 1 &&
          (R.used.getD c.cid #[]).getD (jj + b2n (getBit c.bm (2 * rho))) false) = true := by
        simp only [Bool.and_eq_true] at h ⊢; cases hb : getBit c.bm (2 * rho + 1) <;> simp_all [b2n]
      rw [if_pos ((b2n_fp _).mpr h'), if_pos h]
      simp [ofNat_add']
    · have h' : ¬ (b2n (getBit c.bm (2 * rho + 1)) == 1 &&
          (R.used.getD c.cid #[]).getD (jj + b2n (getBit c.bm (2 * rho))) false) = true := by
        simp only [Bool.and_eq_true] at h ⊢; cases hb : getBit c.bm (2 * rho + 1) <;> simp_all [b2n]
      rw [if_neg (fun e => h' ((b2n_fp _).mp e)), if_neg h]; rfl

open ZkFormal.NearV3.Sched.ScanSpec

/-- The `SINC` message of increase `j` of request `c`. -/
def incMsgN (R : Run) (c : CReq) (j : Nat) : List Nat :=
  [R.tau, 64 * c.cid + j, c.incs.getD j 0, c.incs.length - j - 1, c.s, c.r, c.link]

theorem cur_state (R : Run) (c : CReq) (p : Params) (hb : R.base = p.base) (hD : R.D = p.maxSingleGrant - p.base) :
    ∀ rho, rho ≤ 20 → (ProcScanRequestState.state R c rho).2.2 = (stAt (requestValues p) c.bm p.base (2 * rho)).1
  | 0, _ => by simp [ProcScanRequestState.zero, stAt, hb]
  | rho + 1, h => by
    rw [ProcScanRequestState.succ]
    show ProcScanRequestFactor.nextCur R c rho (ProcScanRequestState.state R c rho).2.2 = _
    rw [cur_state R c p hb hD rho (by omega), show 2 * (rho + 1) = 2 * rho + 1 + 1 by omega, stAt_succ, stAt_succ]
    unfold ProcScanRequestFactor.nextCur
    rw [ProcScanRequestArithmetic.position, ScanSpec.requestValues_getD p (by omega : 2 * rho + 1 < 40), ScanSpec.requestValues_getD p (by omega : 2 * rho < 40), hb, hD]
    cases h1 : getBit c.bm (2 * rho + 1) <;> cases h0 : getBit c.bm (2 * rho) <;> simp [b2n]

theorem flat_bits {β : Type} (g : Nat → Bool) (F : Nat → List β) :
    ∀ c, (List.range c).flatMap (fun k => if g k then F ((List.range k).filter g).length else []) =
      (List.range ((List.range c).filter g).length).flatMap F
  | 0 => rfl
  | c + 1 => by
    rw [filter_range_succ g c, List.range_succ, List.flatMap_append, flat_bits g F c]
    cases h : g c
    · simp [h]
    · simp [h, List.range_succ]

theorem neg_neg_add (x : Fp) (a b : Nat) : x + -Fp.ofNat a + -Fp.ofNat b = x + -Fp.ofNat (a + b) := by
  rw [← ofNat_add']; grind

/-- Index of bit position `k` among the set bits. -/
def idx (bm : List UInt8) (k : Nat) : Nat := ((List.range k).filter (getBit bm)).length

theorem idx_stAt (p : Params) (bm : List UInt8) (k : Nat) : idx bm k = (stAt (requestValues p) bm p.base k).2 :=
  (stAt_spec _ bm _ k).2

theorem len_incs (p : Params) (bm : List UInt8) : (incsOf p bm).length = idx bm 40 := by
  rw [incsOf_length_stAt, idx_stAt p]

/-- The slot message of set bit `k`. -/
theorem slot_msg (R : Run) (c : CReq) (p : Params) (hincs : c.incs = incsOf p c.bm) (hbits : c.bits = setBits c.bm)
    (k : Nat) (hk : k < 40) (hbit : getBit c.bm k = true) :
    [Fp.ofNat R.tau, Fp.ofNat (64 * c.cid + idx c.bm k),
      Fp.ofNat (p.base + (p.maxSingleGrant - p.base) * (k + 1) / 40) + -Fp.ofNat (stAt (requestValues p) c.bm p.base k).1,
      Fp.ofNat c.bits.length + -Fp.ofNat (idx c.bm k) + -Fp.ofNat 1, Fp.ofNat c.s, Fp.ofNat c.r, Fp.ofNat c.link] =
    F (incMsgN R c (idx c.bm k)) := by
  have hlt : idx c.bm k < idx c.bm 40 := by
    rw [idx_stAt p, idx_stAt p]; exact stAt_snd_lt _ _ _ hk hbit
  have hbl : c.bits.length = c.incs.length := by
    rw [hbits, hincs, len_incs, idx]; rfl
  have hle := stAt_fst_le p c.bm k k (Nat.le_refl _) hk
  rw [ScanSpec.requestValues_getD p hk] at hle
  have hg := incsOf_getD p c.bm hk hbit
  rw [ScanSpec.requestValues_getD p hk] at hg
  rw [fp_sub _ _ hle, neg_neg_add, fp_sub _ _ (by rw [hbl, hincs, len_incs]; omega)]
  simp only [F, incMsgN, List.map_cons, List.map_nil, hincs, idx_stAt p, hg]
  rw [← idx_stAt p, hbl, hincs, Nat.sub_sub]

theorem flat_pairs {β : Type} (f : Nat → List β) :
    ∀ n, (List.range n).flatMap (fun r => f (2 * r) ++ f (2 * r + 1)) = (List.range (2 * n)).flatMap f
  | 0 => rfl
  | n + 1 => by
    rw [List.range_succ, List.flatMap_append, flat_pairs f n, show 2 * (n + 1) = 2 * n + 1 + 1 by omega,
      List.range_succ, List.range_succ]
    simp [List.flatMap_append]

theorem idx_succ (bm : List UInt8) (k : Nat) : idx bm (k + 1) = idx bm k + b2n (getBit bm k) := by
  unfold idx; rw [filter_range_succ]; cases getBit bm k <;> simp [b2n]

/-- **The `SINC` sends of one converted request**: every processed increase, once. -/
theorem req_sinc_block (R : Run) (c : CReq) (p : Params) (hb : R.base = p.base)
    (hD : R.D = p.maxSingleGrant - p.base) (hincs : c.incs = incsOf p c.bm) (hbits : c.bits = setBits c.bm) :
    ((List.range 20).map (Desc.req R c)).flatMap (fun d => sincM (fx d.row)) =
      ((List.range c.incs.length).filter (fun j => (R.used.getD c.cid #[]).getD j false)).map
        (fun j => F (incMsgN R c j)) := by
  let slot : Nat → List (List Fp) := fun k => if getBit c.bm k then
    (if (R.used.getD c.cid #[]).getD (idx c.bm k) false then [F (incMsgN R c (idx c.bm k))] else []) else []
  have hrow : ∀ rho ∈ List.range 20, sincM (fx (Desc.req R c rho).row) = slot (2 * rho) ++ slot (2 * rho + 1) := by
    intro rho hr
    have hr' := List.mem_range.mp hr
    rw [req_row_eq _ _ _ hr', req_sinc, cur_state R c p hb hD rho (by omega)]
    have hj : ProcScanRequestCount.before c.bm rho = idx c.bm (2 * rho) := rfl
    rw [hj, hb, hD]
    refine app_congr ?_ ?_
    · simp only [slot]
      cases h0 : getBit c.bm (2 * rho)
      · simp
      · cases hu : (R.used.getD c.cid #[]).getD (idx c.bm (2 * rho)) false
        · simp
        · simp only [Bool.and_self, if_true]
          rw [← slot_msg R c p hincs hbits (2 * rho) (by omega) h0]
    · simp only [slot]
      have hi1 := idx_succ c.bm (2 * rho)
      cases h1 : getBit c.bm (2 * rho + 1)
      · simp
      · rw [← hi1]
        cases hu : (R.used.getD c.cid #[]).getD (idx c.bm (2 * rho + 1)) false
        · simp
        · simp only [Bool.and_self, if_true, Bool.true_and]
          rw [← slot_msg R c p hincs hbits (2 * rho + 1) (by omega) h1, stAt_succ]
          rw [hi1, ← neg_neg_add]
          cases h0 : getBit c.bm (2 * rho) <;> simp [b2n, ScanSpec.requestValues_getD p (show 2 * rho < 40 by omega)]
          refine ⟨by rw [Nat.add_assoc], ?_⟩
          rw [show 2 * rho + 1 + 1 = 2 * rho + 2 by omega, ← List.getD_eq_getElem?_getD,
            ScanSpec.requestValues_getD p (by omega)]
  rw [List.flatMap_map, flatMap_congr_rt hrow, flat_pairs slot 20]
  have hl : c.incs.length = idx c.bm 40 := by rw [hincs, len_incs]
  have := flat_bits (getBit c.bm) (fun j => if (R.used.getD c.cid #[]).getD j false then [F (incMsgN R c j)] else []) 40
  rw [hl, ← Cdc.flatMap_ite_single]
  exact this

end ZkFormal.NearV3.Render.SsdBus
