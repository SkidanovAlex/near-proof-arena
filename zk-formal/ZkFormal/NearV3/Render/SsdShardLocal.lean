import ZkFormal.NearV3.Candidates.ProcDistShardOutput
import ZkFormal.NearV3.Candidates.ProcDistShardGrid
import ZkFormal.NearV3.Candidates.ProcDistShardBools
import ZkFormal.NearV3.Candidates.ProcDistShardRange
import ZkFormal.NearV3.Candidates.ProcDistScanQuiet
import ZkFormal.NearV3.Candidates.ProcDistIndexTest

/-!
# Local legality of an honest distribute shard row of `ssdV3` (`ScanDist.table`, table 12)

`ProcDistShardRow.row tv n sd i x count left budget kp` (the row the distribute generator emits
for position `i` of side `sd`) satisfies every constraint of the frozen `ScanDist.constraints`
(239 + 12 scan) on a physical trace, given the next-row facts `Next`: within a side the next row is
shard row `i + 1` with `kp = key + 1`; after the last sender row the first receiver row
(`side = 1, a = 0, kp = 0`); after the last receiver row the first grid header (`a = 0`,
`kp = 0`); instance constants carried.  The first-row selector is allowed only for sender row 0
with `kp = 0` (`hfirst`).

The pieces for the shard-only constraints already proved (`ProcDistShard{Average,Output,Grid,
Range}`, the booleanity `ProcDistShardBools`, the scan quietness `ProcDistScanQuiet`) are combined
with the kind frame, the `e1` index test and the transition constraints proved here.
-/
namespace ZkFormal.NearV3.Render.SsdShard
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen
open ZkFormal.NearV3.Candidates ZkFormal.NearV3.Candidates.ProcDistShardRow
attribute [local irreducible] ProcDistShardRow.row
set_option maxRecDepth 32768

/-- The sort key of a shard row. -/
def key (count left x : Nat) : Nat := average count left * 64 + x

/-- Next-row facts of shard row `(sd, i)`. -/
def Next (tv n sd i x count left : Nat) (tr : Trace Fp) (t r : Nat) : Prop :=
  tr.cell t ((r+1) % tr.height t) Dist.tau = Fp.ofNat tv ∧
  tr.cell t ((r+1) % tr.height t) Dist.nn = Fp.ofNat n ∧
  (i+1 < n →
    tr.cell t ((r+1) % tr.height t) Dist.kSh = 1 ∧
    tr.cell t ((r+1) % tr.height t) Dist.side = Fp.ofNat sd ∧
    tr.cell t ((r+1) % tr.height t) Dist.a = Fp.ofNat (i+1) ∧
    tr.cell t ((r+1) % tr.height t) Dist.kp = Fp.ofNat (key count left x + 1)) ∧
  (i+1 = n →
    tr.cell t ((r+1) % tr.height t) Dist.kp = 0 ∧
    tr.cell t ((r+1) % tr.height t) Dist.a = 0 ∧
    (sd = 0 → tr.cell t ((r+1) % tr.height t) Dist.kSh = 1 ∧
      tr.cell t ((r+1) % tr.height t) Dist.side = 1) ∧
    (sd = 1 → tr.cell t ((r+1) % tr.height t) Dist.kGH = 1))

theorem key_lt (count left x : Nat) (hc : count ≤ 64) (hl : left ≤ 4500000) (hx : x < 64) :
    key count left x + 1 < 2013265921 := by
  unfold key average
  split
  · omega
  · have h := Nat.div_le_self left count; omega

/-- The kind frame (`cCommon` and the side / first-row / scan-successor constraints). -/
theorem kind_frame (Z : ZEnv) (ha : Z.cur Dist.act = 1) (hp : Z.cur Dist.kP = 0)
    (hs : Z.cur Dist.kS = 0) (hsh : Z.cur Dist.kSh = 1) (hg : Z.cur Dist.kGH = 0)
    (hc : Z.cur Dist.kC = 0) (hside : Z.cur Dist.side ≤ 1) (hl : Z.last = 0)
    (hf : Z.first = 0 ∨ (Z.cur Dist.side = 0 ∧ Z.cur Dist.a = 0 ∧ Z.cur Dist.kp = 0)) :
    ∀ e ∈ (Dist.cKind.drop (Dist.boolCols.map ZkFormal.Chacha.Table.boolC).length).take 13,
      zev Z e = 0 := by
  have hsd : Z.cur Dist.side = 0 ∨ Z.cur Dist.side = 1 := by omega
  simp only [Dist.cKind, List.append_assoc, List.drop_left, Dist.cCommon, List.cons_append,
    List.nil_append, List.take_succ_cons, List.take_zero, List.forall_mem_cons, List.forall_mem_nil]
  rcases hf with hf | ⟨h1, h2, h3⟩
  · rcases hsd with hsd | hsd <;>
    simp [Dist.mul3, Dist.notE, zev, ZkFormal.Chacha.Table.E.c, ZkFormal.Chacha.Table.E.n,
      ZkFormal.Chacha.Table.E.k, ZkFormal.Chacha.Table.E.sub, ZkFormal.Chacha.Table.boolC,
      ha, hp, hs, hsh, hg, hc, hf, hl, hsd]
  · simp [Dist.mul3, Dist.notE, zev, ZkFormal.Chacha.Table.E.c, ZkFormal.Chacha.Table.E.n,
      ZkFormal.Chacha.Table.E.k, ZkFormal.Chacha.Table.E.sub, ZkFormal.Chacha.Table.boolC,
      ha, hp, hs, hsh, hg, hc, hl, h1, h2, h3]

/-- The shard transition constraints: `kp` successor and the row/side/grid successors. -/
theorem trans_frame (Z : ZEnv) (tv n sd i keyV : Nat) (hsd : sd = 0 ∨ sd = 1) (hii : i < n)
    (hsh : Z.cur Dist.kSh = 1) (he1 : Z.cur Dist.e1 = if i+1 = n then 1 else 0)
    (hcx : Z.cur Dist.cx = keyV) (hside : Z.cur Dist.side = sd) (ha : Z.cur Dist.a = i)
    (htv : Z.cur Dist.tau = tv) (hnn : Z.cur Dist.nn = n)
    (ntv : Z.nxt Dist.tau = tv) (nnn : Z.nxt Dist.nn = n)
    (hin : i+1 < n → Z.nxt Dist.kSh = 1 ∧ Z.nxt Dist.side = sd ∧ Z.nxt Dist.a = i+1 ∧
      Z.nxt Dist.kp = keyV + 1)
    (hend : i+1 = n → Z.nxt Dist.kp = 0 ∧ Z.nxt Dist.a = 0 ∧
      (sd = 0 → Z.nxt Dist.kSh = 1 ∧ Z.nxt Dist.side = 1) ∧ (sd = 1 → Z.nxt Dist.kGH = 1)) :
    (∀ e ∈ (Dist.cShard.drop 8).take 2, zev Z e = 0) ∧ (∀ e ∈ Dist.cShard.drop 21, zev Z e = 0) := by
  simp only [Dist.cShard, Dist.instCols, List.cons_append, List.nil_append, List.drop_succ_cons,
    List.drop_zero, List.take_succ_cons, List.take_zero, List.forall_mem_cons, List.forall_mem_nil,
    List.map_cons, List.map_nil]
  by_cases hi : i+1 < n
  · obtain ⟨n1, n2, n3, n4⟩ := hin hi
    have hne : ¬ (i+1 = n) := by omega
    rw [if_neg hne] at he1
    simp [Dist.mul3, Dist.notE, zev, ZkFormal.Chacha.Table.E.c, ZkFormal.Chacha.Table.E.n,
      ZkFormal.Chacha.Table.E.k, ZkFormal.Chacha.Table.E.sub, hsh, he1, hcx, hside, ha, htv, hnn,
      ntv, nnn, n1, n2, n3, n4] <;> omega
  · have heq : i+1 = n := by omega
    obtain ⟨n1, n2, n3, n4⟩ := hend heq
    rw [if_pos heq] at he1
    rcases hsd with rfl | rfl
    · obtain ⟨m1, m2⟩ := n3 rfl
      simp [Dist.mul3, Dist.notE, zev, ZkFormal.Chacha.Table.E.c, ZkFormal.Chacha.Table.E.n,
        ZkFormal.Chacha.Table.E.k, ZkFormal.Chacha.Table.E.sub, hsh, he1, hcx, hside, ha, htv, hnn,
        ntv, nnn, n1, n2, m1, m2] <;> omega
    · have m1 := n4 rfl
      simp [Dist.mul3, Dist.notE, zev, ZkFormal.Chacha.Table.E.c, ZkFormal.Chacha.Table.E.n,
        ZkFormal.Chacha.Table.E.k, ZkFormal.Chacha.Table.E.sub, hsh, he1, hcx, hside, ha, htv, hnn,
        ntv, nnn, n1, n2, m1] <;> omega

theorem split_at {α : Type} (l : List α) (k : Nat) (P : α → Prop)
    (h1 : ∀ e ∈ l.take k, P e) (h2 : ∀ e ∈ l.drop k, P e) : ∀ e ∈ l, P e := by
  rw [← List.take_append_drop k l]
  intro e he
  rcases List.mem_append.mp he with h | h
  · exact h1 e h
  · exact h2 e h

theorem scan_cols (tv n sd i x count left budget kpV : Nat) :
    (row tv n sd i x count left budget kpV)[Scan.fQ]! = 0 ∧
    (row tv n sd i x count left budget kpV)[Scan.re]! = 0 ∧
    (row tv n sd i x count left budget kpV)[Scan.us0]! = 0 ∧
    (row tv n sd i x count left budget kpV)[Scan.us1]! = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals
    rw [ProcDistShardCells.core_cell _ _ _ _ _ _ _ _ _ _ (by decide) (by decide) (by decide) (by decide)]
    apply SchedSetAll.lookup_miss
    simp only [core, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    decide

theorem tau_cell (tv n sd i x count left budget kpV : Nat) :
    (row tv n sd i x count left budget kpV)[Dist.tau]! = tv := by
  rw [ProcDistShardCells.core_cell _ _ _ _ _ _ _ _ _ Dist.tau (by decide) (by decide) (by decide)
    (by decide)]
  rfl

/-- **Local legality of an honest shard row.** -/
theorem physical (tv n sd i x count left budget kpV : Nat) (hsd : sd = 0 ∨ sd = 1)
    (hbudget : budget < 256 ^ 3) (hc : count ≤ 64) (hl : left ≤ 4500000) (hx : x < 64)
    (hi : i < n) (hn : n ≤ 64) (htv : tv < P) (hkp : kpV < P)
    (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (hrow : ∀ col, tr.cell t r col = Fp.ofNat (row tv n sd i x count left budget kpV)[col]!)
    (hfirst : r = 0 → sd = 0 ∧ i = 0 ∧ kpV = 0) (hlast : r+1 < tr.height t)
    (hnext : Next tv n sd i x count left tr t r) :
    ∀ e ∈ ScanDist.constraints, e.eval tr t r pub = 0 := by
  rcases ProcDistShardControlCells.fields tv n sd i x count left budget kpV with
    ⟨hact, hkP, hkS, hkSh, hkGH, hkC, _, _, _, _, _, he1⟩
  rcases ProcDistShardOutputCells.fields tv n sd i x count left budget kpV with
    ⟨hcx, _, _, hkpc, hside, hac, _, _, _, _, _, _, _, _, hnnc, _, _, _, _, _, hbc, _⟩
  have hsc := scan_cols tv n sd i x count left budget kpV
  have hig := ProcDistShardInverseCell.cell tv n sd i x count left budget kpV
  have hP : ∀ v, v < 2013265921 → (Fp.ofNat v).toNat = v := fun v hv => by
    rw [Fp.toNat_ofNat, Nat.mod_eq_of_lt (by unfold P; omega)]
  have hsdP : sd < 2013265921 := by omega
  have hiP : i < 2013265921 := by omega
  have hnP : n < 2013265921 := by omega
  have htvP : tv < 2013265921 := by unfold P at htv; omega
  have hkpP : kpV < 2013265921 := by unfold P at hkp; omega
  have hkey := key_lt count left x hc hl hx
  have zcur (col v : Nat) (hv : v < 2013265921)
      (h : (row tv n sd i x count left budget kpV)[col]! = v) : (tenv tr t r pub).cur col = v := by
    change (tr.cell t r col).toNat = v
    rw [hrow, h, hP v hv]
  have znxt (col v : Nat) (hv : v < 2013265921)
      (h : tr.cell t ((r+1) % tr.height t) col = Fp.ofNat v) : (tenv tr t r pub).nxt col = v := by
    change (tr.cell t ((r+1) % tr.height t) col).toNat = v
    rw [h, hP v hv]
  have fcell (col v : Nat) (h : (row tv n sd i x count left budget kpV)[col]! = v) :
      tr.cell t r col = Fp.ofNat v := by rw [hrow, h]
  have fz (col : Nat) (h : (row tv n sd i x count left budget kpV)[col]! = 0) :
      tr.cell t r col = 0 := by rw [hrow, h]; rfl
  obtain ⟨ntv, nnn, nin, nend⟩ := hnext
  -- the kind frame
  have hkind := kind_frame (tenv tr t r pub) (zcur _ 1 (by decide) hact) (zcur _ 0 (by decide) hkP)
    (zcur _ 0 (by decide) hkS) (zcur _ 1 (by decide) hkSh) (zcur _ 0 (by decide) hkGH)
    (zcur _ 0 (by decide) hkC) (by rw [zcur _ sd hsdP hside]; omega)
    (by simp [tenv, show r+1 ≠ tr.height t by omega])
    (by
      by_cases h0 : r = 0
      · obtain ⟨h1, h2, h3⟩ := hfirst h0
        right
        refine ⟨?_, ?_, ?_⟩
        · rw [zcur _ sd hsdP hside, h1]
        · rw [zcur _ i hiP hac, h2]
        · rw [zcur _ kpV hkpP hkpc, h3]
      · left; simp [tenv, h0])
  -- the shard transitions
  have htr := trans_frame (tenv tr t r pub) tv n sd i (key count left x) hsd hi
    (zcur _ 1 (by decide) hkSh)
    (zcur _ _ (by split <;> decide) he1)
    (zcur _ _ (by omega) (by rw [hcx]; rfl))
    (zcur _ sd hsdP hside) (zcur _ i hiP hac)
    (zcur _ tv htvP (tau_cell tv n sd i x count left budget kpV)) (zcur _ n hnP hnnc)
    (znxt _ tv htvP ntv) (znxt _ n hnP nnn)
    (fun h => by
      obtain ⟨m1, m2, m3, m4⟩ := nin h
      exact ⟨znxt _ 1 (by decide) m1, znxt _ sd hsdP m2, znxt _ (i+1) (by omega) m3,
        znxt _ _ hkey m4⟩)
    (fun h => by
      obtain ⟨m1, m2, m3, m4⟩ := nend h
      refine ⟨znxt _ 0 (by decide) m1, znxt _ 0 (by decide) m2, fun hs => ?_, fun hs => ?_⟩
      · obtain ⟨k1, k2⟩ := m3 hs
        exact ⟨znxt _ 1 (by decide) k1, znxt _ 1 (by decide) k2⟩
      · exact znxt _ 1 (by decide) (m4 hs))
  -- the `e1` index test
  have hktest : ∀ e ∈ (Dist.cKind.drop (Dist.boolCols.map ZkFormal.Chacha.Table.boolC).length).drop 13,
      e.eval tr t r pub = 0 := by
    have hs : tr.cell t r Dist.kSh = 1 := by rw [fcell _ _ hkSh]; rfl
    have hcc : tr.cell t r Dist.kC = 0 := fz _ hkC
    have ha : tr.cell t r Dist.a = Fp.ofNat i := fcell _ _ hac
    have hb : tr.cell t r Dist.b = 0 := fz _ hbc
    have hnn : tr.cell t r Dist.nn = Fp.ofNat n := fcell _ _ hnnc
    have he1' : tr.cell t r Dist.e1 = (if i+1 = n then 1 else 0) := by
      rw [fcell _ _ he1]; split <;> rfl
    have hg1 : tr.cell t r Dist.ig1 = Fp.ofNat (finv (fsub i (n-1))) := fcell _ _ hig
    have hInv := ProcDistIndexTest.inverse i n hi hn
    have hZero := ProcDistIndexTest.annihilate i n hi
    simp only [Dist.cKind, List.append_assoc, List.drop_left, Dist.cCommon, List.cons_append,
      List.nil_append, List.drop_succ_cons, List.drop_zero, List.forall_mem_cons]
    refine ⟨?_, ?_, ?_, ?_, by simp⟩
    · change (tr.cell t r Dist.kSh+tr.cell t r Dist.kC)*
        (tr.cell t r Dist.e1 + -(1 + -(((tr.cell t r Dist.kSh*tr.cell t r Dist.a+tr.cell t r Dist.kC*tr.cell t r Dist.b)+-(tr.cell t r Dist.nn + -(1:Fp)))*tr.cell t r Dist.ig1)))=0
      rw [hs, hcc, he1', ha, hb, hnn, hg1]; grind only
    · change (tr.cell t r Dist.kSh+tr.cell t r Dist.kC)*
        (((tr.cell t r Dist.kSh*tr.cell t r Dist.a+tr.cell t r Dist.kC*tr.cell t r Dist.b)+-(tr.cell t r Dist.nn + -(1:Fp)))*tr.cell t r Dist.e1)=0
      rw [hs, hcc, he1', ha, hb, hnn]; grind only
    · change tr.cell t r Dist.kC*
        (tr.cell t r Dist.e2 + -(1 + -((tr.cell t r Dist.a + -(tr.cell t r Dist.nn + -(1:Fp)))*tr.cell t r Dist.ig2)))=0
      rw [hcc]; grind only
    · change tr.cell t r Dist.kC*((tr.cell t r Dist.a + -(tr.cell t r Dist.nn + -(1:Fp)))*tr.cell t r Dist.e2)=0
      rw [hcc]; grind only
  have hsplit : Dist.cKind = Dist.boolCols.map ZkFormal.Chacha.Table.boolC ++
      ((Dist.cKind.drop (Dist.boolCols.map ZkFormal.Chacha.Table.boolC).length).take 13 ++
       (Dist.cKind.drop (Dist.boolCols.map ZkFormal.Chacha.Table.boolC).length).drop 13) := by
    rw [List.take_append_drop]
    simp only [Dist.cKind, List.append_assoc, List.drop_left]
  have hKind : ∀ e ∈ Dist.cKind, e.eval tr t r pub = 0 := by
    rw [hsplit]
    simp only [List.forall_mem_append]
    refine ⟨?_, fun e he => eval_zero_of (hkind e he), hktest⟩
    intro e he
    obtain ⟨col, hcol, rfl⟩ := List.mem_map.mp he
    apply eval_zero_of
    apply Complete.zev_boolC
    change (tr.cell t r col).toNat ≤ 1
    rw [hrow, Fp.toNat_ofNat]
    exact Nat.le_trans (Nat.mod_le _ _)
      (ProcDistShardBools.columns tv n sd i x count left budget kpV col hcol)
  have hShard : ∀ e ∈ Dist.cShard, e.eval tr t r pub = 0 := by
    have hav := ProcDistShardAverage.physical tv n sd i x count left budget kpV hc tr t r pub hrow
    have hout := ProcDistShardOutput.physical tv n sd i x count left budget kpV hsd hbudget tr t r pub hrow
    apply split_at _ 5 _ hav
    apply split_at _ 3 _ hout.1
    rw [List.drop_drop]
    apply split_at _ 2 _ (fun e he => eval_zero_of (htr.1 e he))
    rw [List.drop_drop]
    apply split_at _ 11 _ hout.2
    rw [List.drop_drop]
    exact fun e he => eval_zero_of (htr.2 e he)
  have hGrid := ProcDistShardGrid.physical tv n sd i x count left budget kpV tr t r pub hrow
  have hRange := ProcDistShardRange.physical tv n sd i x count left budget kpV hc hl tr t r pub hrow
  have hOwn := ProcDistScanQuiet.physical tr t r pub (fz _ hkP) (fz _ hkS)
    (fz _ hsc.1) (fz _ hsc.2.1) (fz _ hsc.2.2.1) (fz _ hsc.2.2.2)
  simp only [ScanDist.constraints, Dist.constraints, List.forall_mem_append]
  exact ⟨⟨⟨⟨hKind, hShard⟩, hGrid⟩, hRange⟩, hOwn⟩

end ZkFormal.NearV3.Render.SsdShard
