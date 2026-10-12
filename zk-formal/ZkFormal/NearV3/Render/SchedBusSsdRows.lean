import ZkFormal.NearV3.Render.SchedBusSsdDist

/-!
# Scan/distribute rows: per-descriptor messages on `SPAR`, `SPUSH`, `SOP`, `SFIN`
-/
set_option linter.unusedSimpArgs false
namespace ZkFormal.NearV3.Render.SsdBus
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen
open ZkFormal.NearV3.Candidates ZkFormal.NearV3.Render.Ssd SchedSetAll

/-- Cells of a row array, as field elements. -/
def fx (row : Array Nat) : Nat → Fp := fun c => Fp.ofNat row[c]!

theorem natCast_fp (n : Nat) : ((n : Nat) : Fp) = Fp.ofNat n := rfl
theorem fp_add0 (x : Fp) : x + 0 = x := by grind
theorem fp_0add (x : Fp) : 0 + x = x := by grind
theorem fp_mul0 (x : Fp) : x * 0 = 0 := by grind
theorem fp_0mul (x : Fp) : 0 * x = 0 := by grind
theorem fp_mul1 (x : Fp) : x * 1 = x := by grind
theorem fp_ofNat0 : (Fp.ofNat 0 : Fp) = 0 := rfl
theorem fp_ofNat1 : (Fp.ofNat 1 : Fp) = 1 := rfl
theorem fp_01 : ((0 : Fp) = 1) = False := by simp only [eq_iff_iff, iff_false]; decide
theorem fp_neg0 : (-(0 : Fp)) = 0 := by grind
theorem fp_add1 (a : Nat) : Fp.ofNat a + 1 = Fp.ofNat (a + 1) := by rw [← fp_ofNat1, ofNat_add']
theorem fp_1add (a : Nat) : 1 + Fp.ofNat a = Fp.ofNat (1 + a) := by rw [← fp_ofNat1, ofNat_add']

macro "ssd_eval" : tactic => `(tactic| (
  simp [lookup, Dist.act, Dist.kSh, Dist.kGH, Dist.kC, Dist.tau, Dist.nn, Dist.kP, Dist.kS, Dist.side, Dist.shd, Dist.lnk, Dist.by0, Dist.by1, Dist.by2, Dist.llo, Dist.lhi, Dist.alc, Dist.fw, Dist.a, Dist.b, Dist.s, Dist.r, Dist.N1, Dist.adr, Dist.L1, Dist.bv, Dist.N2, Dist.L2, Dist.q1, Dist.r1, Dist.bt1, Dist.q2, Dist.r2, Dist.bt2, Dist.icnt, Dist.ig2, Dist.zc, Dist.e2, Dist.kp, Dist.gb, Dist.da, Dist.db, Dist.al, Dist.ig1, Dist.e1, Dist.cx, Dist.cy, Dist.cb, Dist.cg, Dist.dlsg, Dist.dlrg, Dist.sL, Dist.eI, Scan.act, Scan.kP, Scan.kS, Scan.kSh, Scan.kGH, Scan.kC, Scan.tau, Scan.nn, Scan.q, Scan.clo, Scan.chi, Scan.s, Scan.r, Scan.base, Scan.cid, Scan.key, Scan.dd, Scan.link, Scan.bvz, Scan.y, Scan.iy, Scan.Q0, Scan.Q1, Scan.b0, Scan.b1, Scan.u0, Scan.u1, Scan.e4, Scan.zk0, Scan.cur, Scan.cm, Scan.ikey, Scan.j, Scan.m, Scan.fQ, Scan.re, Scan.us0, Scan.us1, List.range_succ, natCast_fp, ofNat_add', ofNat_mul', fp_add0, fp_0add,
    fp_mul0, fp_0mul, fp_mul1, fp_ofNat0, fp_ofNat1, fp_01, fp_neg0, fp_add1, fp_1add, b2n]))

set_option maxRecDepth 8192 in
theorem param_spar (R : Run) : sparM (fx (Scan.paramRow R)) =
    [([R.tau, 1, Scan.byteOf R.base 0, Scan.byteOf R.base 1, Scan.byteOf R.base 2, Scan.byteOf R.D 0,
      Scan.byteOf R.D 1, Scan.byteOf R.D 2, R.n, 0, 0] : List Nat).map Fp.ofNat] := by
  simp only [sparM, fx, ProcScanParamPhysical.row_all, ProcScanParamLocal.assignments]
  ssd_eval

set_option maxRecDepth 8192 in
theorem param_spush (R : Run) : spushM (fx (Scan.paramRow R)) = [] := by
  simp only [spushM, fx, ProcScanParamPhysical.row_all, ProcScanParamLocal.assignments]
  ssd_eval

set_option maxRecDepth 8192 in
theorem param_sop (R : Run) : sopM (fx (Scan.paramRow R)) = [] := by
  simp only [sopM, fx, ProcScanParamPhysical.row_all, ProcScanParamLocal.assignments]
  ssd_eval

set_option maxRecDepth 8192 in
theorem param_sfin (R : Run) : sfinM (fx (Scan.paramRow R)) = [] := by
  simp only [sfinM, fx, ProcScanParamPhysical.row_all, ProcScanParamLocal.assignments]
  ssd_eval

set_option maxRecDepth 8192 in
theorem header_spar (tv n i sv count left : Nat) : sparM (fx (ProcDistHeader.row tv n i sv count left)) = [] := by
  simp only [sparM, fx, ProcDistHeaderPhysical.row_all, ProcDistHeader.assignments]
  ssd_eval

set_option maxRecDepth 8192 in
theorem header_spush (tv n i sv count left : Nat) : spushM (fx (ProcDistHeader.row tv n i sv count left)) = [] := by
  simp only [spushM, fx, ProcDistHeaderPhysical.row_all, ProcDistHeader.assignments]
  ssd_eval

set_option maxRecDepth 8192 in
theorem header_sop (tv n i sv count left : Nat) : sopM (fx (ProcDistHeader.row tv n i sv count left)) = [] := by
  simp only [sopM, fx, ProcDistHeaderPhysical.row_all, ProcDistHeader.assignments]
  ssd_eval

set_option maxRecDepth 8192 in
theorem header_sfin (tv n i sv count left : Nat) : sfinM (fx (ProcDistHeader.row tv n i sv count left)) = [] := by
  simp only [sfinM, fx, ProcDistHeaderPhysical.row_all, ProcDistHeader.assignments]
  ssd_eval

theorem shard_fx (tv n sd i x count left budget kp col : Nat) (hc : col < 119) (hbt : col < 35 ∨ 41 ≤ col)
    (hqb : col < 80 ∨ 103 ≤ col) (hrb : col < 109 ∨ 115 ≤ col) :
    fx (ProcDistShardRow.row tv n sd i x count left budget kp) col =
      Fp.ofNat (lookup (ProcDistShardRow.core tv n sd i x count left budget kp) col 0) := by
  unfold fx; rw [ProcDistShardCells.core_cell _ _ _ _ _ _ _ _ _ _ hc hbt hqb hrb]

theorem cell_fx (ids : List Nat) (tv n i j sv rr n1 l1 n2 l2 : Nat) (al : Bool) (col : Nat)
    (hc : col < 119) (hbt1 : col < 27 ∨ 33 ≤ col) (hbt2 : col < 35 ∨ 41 ≤ col) (hh : col < 57 ∨ 115 ≤ col) :
    fx (ProcDistCellRow.row ids tv n i j sv rr n1 l1 n2 l2 al) col =
      Fp.ofNat (lookup (ProcDistCellRow.core ids tv n i j sv rr n1 l1 n2 l2 al) col 0) := by
  unfold fx; rw [ProcDistCellCells.core_cell _ _ _ _ _ _ _ _ _ _ _ _ _ hc hbt1 hbt2 hh]

set_option maxRecDepth 8192 in
theorem shard_spar (tv n sd i x count left budget kp : Nat) :
    sparM (fx (ProcDistShardRow.row tv n sd i x count left budget kp)) =
      [([tv, 3, sd, x, count, budget % 256, budget / 256 % 256, budget / 65536 % 256, n, 0, 0] : List Nat).map Fp.ofNat] := by
  simp only [sparM]
  simp (disch := decide) only [List.range_succ, List.range_zero, List.map_cons, List.map_nil, List.map_append,
    List.nil_append, List.cons_append, Dist.fw, shard_fx, ProcDistShardRow.core]
  ssd_eval

set_option maxRecDepth 8192 in
theorem shard_spush (tv n sd i x count left budget kp : Nat) : spushM (fx (ProcDistShardRow.row tv n sd i x count left budget kp)) = [] := by
  simp only [spushM]
  simp (disch := decide) only [List.range_succ, List.range_zero, List.map_cons, List.map_nil, List.map_append,
    List.nil_append, List.cons_append, Dist.fw, shard_fx, ProcDistShardRow.core]
  ssd_eval

set_option maxRecDepth 8192 in
theorem shard_sop (tv n sd i x count left budget kp : Nat) :
    sopM (fx (ProcDistShardRow.row tv n sd i x count left budget kp)) = [([16384 * tv + (4096 * (sd + 1) + x), 0, 0, 0, budget, 0, 0, 0] : List Nat).map Fp.ofNat] := by
  simp only [sopM]
  simp (disch := decide) only [List.range_succ, List.range_zero, List.map_cons, List.map_nil, List.map_append,
    List.nil_append, List.cons_append, Dist.fw, shard_fx, ProcDistShardRow.core]
  ssd_eval

set_option maxRecDepth 8192 in
theorem shard_sfin (tv n sd i x count left budget kp : Nat) :
    sfinM (fx (ProcDistShardRow.row tv n sd i x count left budget kp)) = [([16384 * tv + (4096 * (sd + 1) + x), left, 0] : List Nat).map Fp.ofNat] := by
  simp only [sfinM]
  simp (disch := decide) only [List.range_succ, List.range_zero, List.map_cons, List.map_nil, List.map_append,
    List.nil_append, List.cons_append, Dist.fw, shard_fx, ProcDistShardRow.core]
  ssd_eval

set_option maxRecDepth 8192 in
theorem cell_spar (ids : List Nat) (tv n i j sv rr n1 l1 n2 l2 : Nat) (al : Bool) :
    sparM (fx (ProcDistCellRow.row ids tv n i j sv rr n1 l1 n2 l2 al)) =
      [([tv, 4, (srcFields ids (sv * n + rr))[0]!, (srcFields ids (sv * n + rr))[1]!, (srcFields ids (sv * n + rr))[2]!,
        (srcFields ids (sv * n + rr))[3]!, 0, 0, (sv * n + rr) % 256, (sv * n + rr) / 256, b2n al] : List Nat).map Fp.ofNat] := by
  simp only [sparM]
  simp (disch := decide) only [List.range_succ, List.range_zero, List.map_cons, List.map_nil, List.map_append,
    List.nil_append, List.cons_append, Dist.fw, cell_fx, ProcDistCellRow.core]
  ssd_eval

set_option maxRecDepth 8192 in
theorem cell_spush (ids : List Nat) (tv n i j sv rr n1 l1 n2 l2 : Nat) (al : Bool) : spushM (fx (ProcDistCellRow.row ids tv n i j sv rr n1 l1 n2 l2 al)) = [] := by
  simp only [spushM]
  simp (disch := decide) only [List.range_succ, List.range_zero, List.map_cons, List.map_nil, List.map_append,
    List.nil_append, List.cons_append, Dist.fw, cell_fx, ProcDistCellRow.core]
  ssd_eval

set_option maxRecDepth 8192 in
theorem cell_sop (ids : List Nat) (tv n i j sv rr n1 l1 n2 l2 : Nat) (al : Bool) : sopM (fx (ProcDistCellRow.row ids tv n i j sv rr n1 l1 n2 l2 al)) = [] := by
  simp only [sopM]
  simp (disch := decide) only [List.range_succ, List.range_zero, List.map_cons, List.map_nil, List.map_append,
    List.nil_append, List.cons_append, Dist.fw, cell_fx, ProcDistCellRow.core]
  ssd_eval

set_option maxRecDepth 8192 in
theorem cell_sfin (ids : List Nat) (tv n i j sv rr n1 l1 n2 l2 : Nat) (al : Bool) : sfinM (fx (ProcDistCellRow.row ids tv n i j sv rr n1 l1 n2 l2 al)) = [] := by
  simp only [sfinM]
  simp (disch := decide) only [List.range_succ, List.range_zero, List.map_cons, List.map_nil, List.map_append,
    List.nil_append, List.cons_append, Dist.fw, cell_fx, ProcDistCellRow.core]
  ssd_eval

theorem fx_of {row : Array Nat} {col v : Nat} (h : row[col]! = v) : fx row col = Fp.ofNat v := by
  unfold fx; rw [h]

open ProcScanRequestFactor in
set_option maxRecDepth 32768 in
set_option maxHeartbeats 1200000 in
theorem req_bv (R : Run) (c : CReq) (rho jj cv : Nat) : (row R c rho jj cv)[Dist.bv]! = 0 := by
  simp only [row,List.forIn_pure_yield_eq_foldl,Id.run,pure_bind]
  simp only [List.range_succ,List.range_zero,List.foldl_cons,List.foldl_nil,List.foldl_append]
  simp [pure,Array.getElem!_set!_ne,Array.getElem!_set!_self,zrow,Array.size_set!,Array.size_replicate,Scan.act,Scan.kP,Scan.kS,Scan.kSh,Scan.kGH,Scan.kC,Scan.tau,Scan.nn,Scan.q,Scan.clo,Scan.chi,Scan.s,Scan.r,Scan.base,Scan.cid,Scan.key,Scan.dd,Scan.link,Scan.bvz,Scan.y,Scan.iy,Scan.Q0,Scan.Q1,Scan.b0,Scan.b1,Scan.u0,Scan.u1,Scan.e4,Scan.zk0,Scan.cur,Scan.cm,Scan.ikey,Scan.j,Scan.m,Scan.rb0,Scan.rb1,Scan.qb0,Scan.qb1,Scan.fQ,Scan.re,Scan.us0,Scan.us1,Scan.width,Dist.act,Dist.kSh,Dist.kGH,Dist.kC,Dist.tau,Dist.nn,Dist.kP,Dist.kS,Dist.side,Dist.shd,Dist.lnk,Dist.by0,Dist.by1,Dist.by2,Dist.llo,Dist.lhi,Dist.alc,Dist.fw,Dist.a,Dist.b,Dist.s,Dist.r,Dist.N1,Dist.adr,Dist.L1,Dist.bv,Dist.N2,Dist.L2,Dist.q1,Dist.r1,Dist.bt1,Dist.q2,Dist.r2,Dist.bt2,Dist.icnt,Dist.ig2,Dist.zc,Dist.e2,Dist.kp,Dist.gb,Dist.da,Dist.db,Dist.al,Dist.ig1,Dist.e1,Dist.cx,Dist.cy,Dist.cb,Dist.cg,Dist.dlsg,Dist.dlrg,Dist.sL,Dist.eI,Dist.qb1,Dist.qb2,Dist.rb1,Dist.rb2,Dist.width]
  all_goals rfl

open ProcScanRequestFactor in
theorem req_spar (R : Run) (c : CReq) (rho jj cv : Nat) :
    sparM (fx (row R c rho jj cv)) = if rho = 0 then
      [([R.tau, 2, (c.bm.map (·.toNat)).getD 0 0, (c.bm.map (·.toNat)).getD 1 0, (c.bm.map (·.toNat)).getD 2 0,
        (c.bm.map (·.toNat)).getD 3 0, (c.bm.map (·.toNat)).getD 4 0, c.cid % 256, c.cid / 256, c.s, c.r] :
        List Nat).map Fp.ofNat] else [] := by
  obtain ⟨-, hkS, hfQ, htau, -, -, -, -⟩ := ProcScanRequestCells.controls R c rho jj cv
  obtain ⟨hs, hr, -, -, -, hclo, hchi⟩ := ProcScanRequestCells.payload R c rho jj cv
  obtain ⟨hkP, hkSh, -, hkC, -⟩ := ProcScanRequestQuietCells.zeros R c rho jj cv
  have hq0 := ProcScanRequestByteCells.first_byte R c rho jj cv
  have hq1 := ProcScanRequestByteCells.following_bytes R c rho jj cv 1 ⟨by omega, by omega⟩
  have hq2 := ProcScanRequestByteCells.following_bytes R c rho jj cv 2 ⟨by omega, by omega⟩
  have hq3 := ProcScanRequestByteCells.following_bytes R c rho jj cv 3 ⟨by omega, by omega⟩
  have hq4 := ProcScanRequestByteCells.following_bytes R c rho jj cv 4 ⟨by omega, by omega⟩
  simp only [sparM, List.range_succ, List.range_zero, List.map_cons, List.map_nil, List.map_append,
    List.nil_append, List.cons_append]
  simp only [Scan.kP, Scan.kS, Scan.fQ, Scan.tau, Scan.s, Scan.r, Scan.clo, Scan.chi, Scan.q] at *
  simp only [fx_of hkS, fx_of hfQ, fx_of htau, fx_of hs, fx_of hr, fx_of hclo,
    fx_of hchi, fx_of hkP, fx_of hkSh, fx_of hkC, fx_of hq0, fx_of hq1, fx_of hq2, fx_of hq3, fx_of hq4]
  by_cases h0 : rho = 0
  · subst h0; ssd_eval
  · simp [h0, b2n]
    ssd_eval

open ProcScanRequestFactor in
theorem req_spush (R : Run) (c : CReq) (rho jj cv : Nat) :
    spushM (fx (row R c rho jj cv)) = if rho / 4 = 4 ∧ rho % 4 = 3 then
      [([R.tau, c.key, b2n (c.key == 0), c.cid, 64 * c.cid] : List Nat).map Fp.ofNat] else [] := by
  obtain ⟨-, -, -, htau, -, -, -, hcid⟩ := ProcScanRequestCells.controls R c rho jj cv
  obtain ⟨-, -, -, hkey, -, -, -⟩ := ProcScanRequestCells.payload R c rho jj cv
  obtain ⟨-, hre, -, -, hzk⟩ := ProcScanRequestCells.flags R c rho jj cv
  simp only [spushM]
  simp only [Scan.re, Scan.tau, Scan.key, Scan.zk0, Scan.cid] at *
  simp only [fx_of hre, fx_of htau, fx_of hkey, fx_of hzk, fx_of hcid]
  by_cases h0 : rho / 4 = 4 ∧ rho % 4 = 3
  · simp only [h0, beq_self_eq_true, Bool.and_self, if_true]; ssd_eval
  · rw [if_neg h0]
    have : (rho / 4 == 4 && rho % 4 == 3) = false := by
      simp only [Bool.and_eq_false_iff, beq_eq_false_iff_ne]; omega
    simp only [this]; ssd_eval

open ProcScanRequestFactor in
theorem req_sop (R : Run) (c : CReq) (rho jj cv : Nat) :
    sopM (fx (row R c rho jj cv)) = if rho / 4 = 4 ∧ rho % 4 = 3 then
      [([16384 * R.tau + c.link, c.cid + 1, 1, c.key, c.key, 0, 0, 0] : List Nat).map Fp.ofNat] else [] := by
  obtain ⟨-, hkS, -, htau, -, -, -, hcid⟩ := ProcScanRequestCells.controls R c rho jj cv
  obtain ⟨-, -, hlink, hkey, -, -, -⟩ := ProcScanRequestCells.payload R c rho jj cv
  obtain ⟨-, hre, -, -, -⟩ := ProcScanRequestCells.flags R c rho jj cv
  obtain ⟨-, hkSh, -, -, -⟩ := ProcScanRequestQuietCells.zeros R c rho jj cv
  have hbv := req_bv R c rho jj cv
  simp only [sopM]
  simp only [Scan.re, Scan.tau, Scan.key, Scan.cid, Scan.kS, Scan.link, Scan.bvz] at *
  simp only [fx_of hre, fx_of htau, fx_of hkey, fx_of hcid, fx_of hkS, fx_of hlink, fx_of hkSh, fx_of hbv]
  by_cases h0 : rho / 4 = 4 ∧ rho % 4 = 3
  · simp only [h0, beq_self_eq_true, Bool.and_self, if_true]; ssd_eval
  · rw [if_neg h0]
    have : (rho / 4 == 4 && rho % 4 == 3) = false := by
      simp only [Bool.and_eq_false_iff, beq_eq_false_iff_ne]; omega
    simp only [this]; ssd_eval

open ProcScanRequestFactor in
theorem req_sfin (R : Run) (c : CReq) (rho jj cv : Nat) : sfinM (fx (row R c rho jj cv)) = [] := by
  obtain ⟨-, hkSh, -, -, -⟩ := ProcScanRequestQuietCells.zeros R c rho jj cv
  simp only [sfinM, fx_of hkSh]
  ssd_eval

end ZkFormal.NearV3.Render.SsdBus
