import ZkFormal.NearV3.Rcpt.Extract.SizeProof
import ZkFormal.Near.Render.Proof.Base

/-!
# ZkFormal.NearV3.Rcpt.Render.SizeRender — completeness of the `sizeV3` table

Honest rows (`sizeRows pub v`, 4 rows): rows `q = 0, 1, 2` receive `SIZE (q, x_q)` with running
sums `tot`, `base`, the flags `lb = [q = 1]`, `la = [q = 2]` and the 24-bit slacks
`3,000,000 − (x_0 + x_1)` (row 1) and `8,388,608 − OVH − Σ x` (row 2); row 3 is padding with
`t = 3`.  Given the bounds (`SizeOk`):
* `size_render_local`: `TableLocal SizeV3.table`;
* `size_render_traffic`: traffic `sizeTraffic v`.
-/

namespace ZkFormal.NearV3.Render

open ZkFormal.Near ZkFormal.Near.Render ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl

/-- The bounds the honest table needs (as naturals). -/
structure SizeOk (pub : List Fp) (v : SizeV) : Prop where
  base : v.x0 + v.x1 ≤ 3000000
  tot : ovhNat pub + v.x0 + v.x1 + v.x2 ≤ 8388608

namespace SizeGen

def xAt (v : SizeV) : Nat → Nat
  | 0 => v.x0
  | 1 => v.x1
  | 2 => v.x2
  | _ => 0

def totAt (v : SizeV) : Nat → Nat
  | 0 => v.x0
  | 1 => v.x0 + v.x1
  | 2 => v.x0 + v.x1 + v.x2
  | _ => 0

def baseAt (v : SizeV) : Nat → Nat
  | 0 => v.x0
  | 1 => v.x0 + v.x1
  | 2 => v.x0 + v.x1
  | _ => 0

/-- The slack of row `q` (24 bits). -/
def bv (pub : List Fp) (v : SizeV) : Nat → Nat
  | 1 => 3000000 - (v.x0 + v.x1)
  | 2 => 8388608 - ovhNat pub - (v.x0 + v.x1 + v.x2)
  | _ => 0

def cell (pub : List Fp) (v : SizeV) (q : Nat) : Nat → Nat
  | 0 => if q < 3 then 1 else 0
  | 1 => q
  | 2 => xAt v q
  | 3 => totAt v q
  | 4 => baseAt v q
  | 5 => if q = 1 then 1 else 0
  | 6 => if q = 2 then 1 else 0
  | e + 7 => if e < 24 then (bv pub v q / 2 ^ e) % 2 else 0

end SizeGen

/-- The honest `sizeV3` rows. -/
def sizeRows (pub : List Fp) (v : SizeV) : Array Row := mkTab 4 SizeV3.width (SizeGen.cell pub v)

namespace SizeRender

theorem ofNat0 : Fp.ofNat 0 = 0 := rfl
theorem ofNat1 : Fp.ofNat 1 = 1 := rfl
theorem ofNat2 : Fp.ofNat 2 = 2 := rfl
theorem ofNat3 : Fp.ofNat 3 = 3 := rfl
theorem ofNatAdd (a b : Nat) : Fp.ofNat (a + b) = Fp.ofNat a + Fp.ofNat b := (ofNat_add' a b).symm

theorem bitsVal_bits (v : Nat) : ∀ n, bitsVal (fun e => (v / 2 ^ e) % 2) 0 n = v % 2 ^ n
  | 0 => by simp [bitsVal, Nat.mod_one]
  | n + 1 => by
    rw [bitsVal, bitsVal_bits v n, Nat.mod_pow_succ, Nat.zero_add]

theorem bitsVal_congr (f g : Nat → Nat) : ∀ n, (∀ e, e < n → f e = g e) → bitsVal f 0 n = bitsVal g 0 n
  | 0, _ => rfl
  | n + 1, h => by
    simp only [bitsVal, Nat.zero_add]
    rw [bitsVal_congr f g n (fun e he => h e (by omega)), h n (by omega)]

/-- Rows from `3` on are padding: only the (unconstrained) row counter `t` is nonzero. -/
theorem cell_pad (pub : List Fp) (v : SizeV) {q : Nat} (hq : 3 ≤ q) (y : Nat) :
    SizeGen.cell pub v q y = if y = 1 then q else 0 := by
  have hx : SizeGen.xAt v q = 0 := by
    unfold SizeGen.xAt; split <;> first | rfl | omega
  have ht : SizeGen.totAt v q = 0 := by
    unfold SizeGen.totAt; split <;> first | rfl | omega
  have hb : SizeGen.baseAt v q = 0 := by
    unfold SizeGen.baseAt; split <;> first | rfl | omega
  have hv : SizeGen.bv pub v q = 0 := by
    unfold SizeGen.bv; split <;> first | rfl | omega
  match y with
  | 0 => simp [SizeGen.cell]; omega
  | 1 => simp [SizeGen.cell]
  | 2 => simp [SizeGen.cell, hx]
  | 3 => simp [SizeGen.cell, ht]
  | 4 => simp [SizeGen.cell, hb]
  | 5 => simp [SizeGen.cell]; omega
  | 6 => simp [SizeGen.cell]; omega
  | e + 7 => simp [SizeGen.cell, hv]

section rows
variable {pub : List Fp} {v : SizeV} (ok : SizeOk pub v) {tr : Trace Fp} {tt : Nat}
  (hH : 4 ≤ tr.height tt)
  (hc : ∀ q x, q < tr.height tt → x < SizeV3.width → tr.cell tt q x = Fp.ofNat (SizeGen.cell pub v q x))
include ok hH hc

theorem bitCell {q : Nat} (hq : q < tr.height tt) {e : Nat} (he : e < 24) :
    tr.cell tt q (SizeV3.bt e) = Fp.ofNat ((SizeGen.bv pub v q / 2 ^ e) % 2) := by
  rw [show SizeV3.bt e = e + 7 by unfold SizeV3.bt; omega, hc q (e + 7) (by omega) (by unfold SizeV3.width; omega)]
  simp [SizeGen.cell, he]

theorem boolCols {q : Nat} (hq : q < tr.height tt) {y : Nat}
    (hy : y ∈ [SizeV3.act, SizeV3.lb, SizeV3.la] ++ (List.range 24).map SizeV3.bt) :
    tr.cell tt q y = 0 ∨ tr.cell tt q y = 1 := by
  rcases List.mem_append.1 hy with hy | hy
  · simp only [SizeV3.act, SizeV3.lb, SizeV3.la, List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl <;> rw [hc q _ (by omega) (by decide)] <;> simp only [SizeGen.cell] <;>
      split <;> simp [ofNat0, ofNat1]
  · obtain ⟨e, he, rfl⟩ := List.mem_map.1 hy
    rw [bitCell ok hH hc hq (List.mem_range.1 he)]
    rcases Nat.mod_two_eq_zero_or_one (SizeGen.bv pub v q / 2 ^ e) with h | h <;> rw [h] <;> simp [ofNat0, ofNat1]

theorem bv_lt (q : Nat) : SizeGen.bv pub v q < 2 ^ 24 := by
  unfold SizeGen.bv; split <;> omega

theorem bitsAt {q : Nat} (hq : q < tr.height tt) :
    SizeV3.bitsE.eval tr tt q pub = Fp.ofNat (SizeGen.bv pub v q) := by
  rw [show SizeV3.bitsE = bits (fun e => c (SizeV3.bt e)) 0 24 from rfl,
    eval_bits tr tt q pub SizeV3.bt 0 24 (fun e he => boolCols ok hH hc hq (by
      rw [Nat.zero_add]; exact List.mem_append_right _ (List.mem_map_of_mem (List.mem_range.2 he)))),
    bitsVal_congr _ (fun e => (SizeGen.bv pub v q / 2 ^ e) % 2) 24 (fun e he => by
      simp only [cv, bitCell ok hH hc hq he, Fp.toNat_ofNat]
      exact Nat.mod_eq_of_lt (by
        have h2 := Nat.mod_lt (SizeGen.bv pub v q / 2 ^ e) (show 2 > 0 by decide); unfold ZkFormal.Algebra.P; omega)),
    bitsVal_bits, Nat.mod_eq_of_lt (bv_lt ok hH hc q)]
  rfl

end rows
end SizeRender

open SizeRender in
/-- **The honest `sizeV3` table is locally legal** at any height `≥ 4` (rows `≥ 3` padding). -/
theorem size_render_local_at (pub : List Fp) (v : SizeV) (ok : SizeOk pub v) (tr : Trace Fp) (t : Nat)
    (cap : Nat) (hlog : 2 ≤ tr.log t ∧ tr.log t ≤ cap)
    (hcell : ∀ r x, r < tr.height t → x < SizeV3.width → tr.cell t r x = Fp.ofNat (SizeGen.cell pub v r x)) :
    TableLocal { SizeV3.table with maxLog := cap } tr t pub := by
  have hH : 4 ≤ tr.height t := by
    unfold Trace.height; exact Nat.le_trans (by decide) (Nat.pow_le_pow_right (by decide) hlog.1)
  have hb1 : 3000000 - (v.x0 + v.x1) < 2 ^ 24 := by omega
  have hb2 : 8388608 - ovhNat pub - (v.x0 + v.x1 + v.x2) < 2 ^ 24 := by omega
  have e1 : (3000000 - (v.x0 + v.x1)) + v.x0 + v.x1 = 3000000 := by have := ok.base; omega
  have e2 : (8388608 - ovhNat pub - (v.x0 + v.x1 + v.x2)) + ovhNat pub + v.x0 + v.x1 + v.x2 = 8388608 := by
    have := ok.tot; omega
  have f1 := congrArg Fp.ofNat e1
  have f2 := congrArg Fp.ofNat e2
  simp only [ofNatAdd] at f1 f2
  refine ⟨by omega, hlog.2, ?_, ?_⟩
  · intro r hr e he
    change e ∈ SizeV3.constraints at he
    unfold SizeV3.constraints at he
    rcases List.mem_append.1 he with he' | he'
    · obtain ⟨y, hy, rfl⟩ := List.mem_map.1 he'
      simp only [eval_bool, eval_c]
      rcases boolCols ok hH hcell hr hy with h | h <;> rw [h] <;> grind
    · clear he
      have cellv : ∀ q x, q < tr.height t → x < 31 → tr.cell t q x = Fp.ofNat (SizeGen.cell pub v q x) :=
        fun q x hq hx => hcell q x hq hx
      have hbits := bitsAt ok hH hcell hr
      by_cases h3 : r < 3
      · have m1 : 1 % tr.height t = 1 := Nat.mod_eq_of_lt (by omega)
        have m2 : 2 % tr.height t = 2 := Nat.mod_eq_of_lt (by omega)
        have m3 : 3 % tr.height t = 3 := Nat.mod_eq_of_lt (by omega)
        have n1 : ¬ 1 = tr.height t := by omega
        have n2 : ¬ 2 = tr.height t := by omega
        have n3 : ¬ 3 = tr.height t := by omega
        have c0 := fun x (hx : x < 31) => cellv 0 x (by omega) hx
        have c1 := fun x (hx : x < 31) => cellv 1 x (by omega) hx
        have c2 := fun x (hx : x < 31) => cellv 2 x (by omega) hx
        have c3 := fun x (hx : x < 31) => cellv 3 x (by omega) hx
        have hrow : r = 0 ∨ r = 1 ∨ r = 2 := by omega
        simp only [List.mem_cons, List.not_mem_nil, or_false] at he'
        rcases he' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
          rfl | rfl | rfl
        all_goals
          simp only [eval_mul, eval_mul3, eval_sub, eval_add, eval_c, eval_n, eval_k, eval_not, eval_isFirst,
            eval_isLast, eval_isTransition, SizeV3.NT, SizeProof.eval_ovh, hbits]
          rcases hrow with rfl | rfl | rfl <;>
          simp only [Nat.reduceAdd, m1, m2, m3, n1, n2, n3, c0, c1, c2, c3, SizeV3.act, SizeV3.t, SizeV3.x,
            SizeV3.tot, SizeV3.base, SizeV3.lb, SizeV3.la,
            SizeGen.cell, SizeGen.xAt, SizeGen.totAt, SizeGen.baseAt, SizeGen.bv, ofNat0, ofNat1, ofNat2, ofNat3,
            natCast_eq, ofNatAdd, Nat.reduceLT, Nat.reduceMod, Nat.reduceSub, reduceIte, Nat.reduceEqDiff,
            Nat.add_eq, Nat.zero_add, if_false, if_true] <;> grind
      · -- a padding row: every constrained cell is zero; next-row reads are padding or masked
        have cP : ∀ q y, 3 ≤ q → q < tr.height t → y < 31 → y ≠ 1 → tr.cell t q y = 0 := by
          intro q y hq hqH hy h1
          rw [cellv q y hqH hy, cell_pad pub v hq, if_neg h1]; rfl
        have r0 : r ≠ 0 := by omega
        have cr := fun y (hy : y < 31) (h1 : y ≠ 1) => cP r y (by omega) hr hy h1
        simp only [List.mem_cons, List.not_mem_nil, or_false] at he'
        by_cases hl : r + 1 < tr.height t
        · have cn := fun y (hy : y < 31) (h1 : y ≠ 1) => cP (r + 1) y (by omega) hl hy h1
          have mn : (r + 1) % tr.height t = r + 1 := Nat.mod_eq_of_lt hl
          have nl : ¬ r + 1 = tr.height t := by omega
          rcases he' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
            rfl | rfl | rfl
          all_goals
            simp only [eval_mul, eval_mul3, eval_sub, eval_add, eval_c, eval_n, eval_k, eval_not, eval_isFirst,
              eval_isLast, eval_isTransition, mn, nl, r0, if_false, SizeV3.act, SizeV3.lb, SizeV3.la, SizeV3.x,
              SizeV3.tot, SizeV3.base,
              cr 0 (by decide) (by decide), cr 2 (by decide) (by decide), cr 3 (by decide) (by decide),
              cr 4 (by decide) (by decide), cr 5 (by decide) (by decide), cr 6 (by decide) (by decide),
              cn 0 (by decide) (by decide), cn 2 (by decide) (by decide), cn 3 (by decide) (by decide),
              cn 4 (by decide) (by decide), cn 5 (by decide) (by decide), cn 6 (by decide) (by decide)]
            <;> grind
        · have nl : r + 1 = tr.height t := by omega
          rcases he' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
            rfl | rfl | rfl
          all_goals
            simp only [eval_mul, eval_mul3, eval_sub, eval_add, eval_c, eval_n, eval_k, eval_not, eval_isFirst,
              eval_isLast, eval_isTransition, nl, r0, if_false, if_true, SizeV3.act, SizeV3.lb, SizeV3.la,
              SizeV3.x, SizeV3.tot, SizeV3.base,
              cr 0 (by decide) (by decide), cr 2 (by decide) (by decide), cr 3 (by decide) (by decide),
              cr 4 (by decide) (by decide), cr 5 (by decide) (by decide), cr 6 (by decide) (by decide)]
            <;> grind
  · intro r hr it hi bb hb
    change it ∈ SizeV3.interactions at hi
    simp only [SizeV3.interactions, Dsl.recv, List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    subst hb
    simp only [eval_c]
    exact boolCols ok hH hcell hr (by simp)

open SizeRender in
/-- **The honest `sizeV3` table has the traffic of `v`** at any height `≥ 4`. -/
theorem size_render_traffic_at (pub : List Fp) (v : SizeV) (tr : Trace Fp) (t : Nat)
    (hH : 4 ≤ tr.height t)
    (hcell : ∀ r x, r < tr.height t → x < SizeV3.width → tr.cell t r x = Fp.ofNat (SizeGen.cell pub v r x)) :
    TableTraffic SizeV3.interactions tr t pub (sizeTraffic v) := by
  have hsplit : List.range (tr.height t) = List.range 4 ++ (List.range (tr.height t - 4)).map (4 + ·) := by
    rw [← List.range_add, Nat.add_sub_cancel' hH]
  have hrest : ∀ b sd, ((List.range (tr.height t - 4)).map (4 + ·)).flatMap
      (fun r => rowTraffic SizeV3.interactions tr t r pub b sd) = [] := by
    intro b sd
    refine List.flatMap_eq_nil_iff.2 fun q hq => ?_
    obtain ⟨q', hq', rfl⟩ := List.mem_map.1 hq
    have := List.mem_range.1 hq'
    rw [SizeProof.rowT, hcell _ _ (by omega) (show SizeV3.act < SizeV3.width by decide),
      cell_pad pub v (by omega)]
    simp [SizeV3.act, ofNat0]
  apply traffic_of
  all_goals
    intro b
    refine List.Perm.of_eq ?_
    rw [hsplit, List.flatMap_append, hrest, List.append_nil]
    simp only [SizeProof.rowT, show List.range 4 = [0, 1, 2, 3] from rfl, List.flatMap_cons, List.flatMap_nil]
    simp only [hcell _ _ (show (0 : Nat) < tr.height t by omega) (show SizeV3.act < SizeV3.width by decide),
      hcell _ _ (show (1 : Nat) < tr.height t by omega) (show SizeV3.act < SizeV3.width by decide),
      hcell _ _ (show (2 : Nat) < tr.height t by omega) (show SizeV3.act < SizeV3.width by decide),
      hcell _ _ (show (3 : Nat) < tr.height t by omega) (show SizeV3.act < SizeV3.width by decide),
      hcell _ _ (show (0 : Nat) < tr.height t by omega) (show SizeV3.t < SizeV3.width by decide),
      hcell _ _ (show (1 : Nat) < tr.height t by omega) (show SizeV3.t < SizeV3.width by decide),
      hcell _ _ (show (2 : Nat) < tr.height t by omega) (show SizeV3.t < SizeV3.width by decide),
      hcell _ _ (show (0 : Nat) < tr.height t by omega) (show SizeV3.x < SizeV3.width by decide),
      hcell _ _ (show (1 : Nat) < tr.height t by omega) (show SizeV3.x < SizeV3.width by decide),
      hcell _ _ (show (2 : Nat) < tr.height t by omega) (show SizeV3.x < SizeV3.width by decide)]
    simp [SizeGen.cell, SizeGen.xAt, SizeV3.act, SizeV3.t, SizeV3.x, sizeTraffic, Msg.toFp, ofNat0, ofNat1]
  all_goals by_cases hb : b = B_SIZE <;> simp [hb] <;> exact ⟨rfl, rfl, rfl⟩

open SizeRender in
/-- **The honest `sizeV3` table is locally legal.** -/
theorem size_render_local (pub : List Fp) (v : SizeV) (ok : SizeOk pub v) (tr : Trace Fp) (t : Nat)
    (hlog : tr.log t = 2)
    (hcell : ∀ r x, r < tr.height t → x < SizeV3.width → tr.cell t r x = Fp.ofNat (SizeGen.cell pub v r x)) :
    TableLocal SizeV3.table tr t pub :=
  size_render_local_at pub v ok tr t SizeV3.maxLog ⟨by omega, by rw [hlog]; decide⟩ hcell

/-- **The honest `sizeV3` table has the traffic of `v`.** -/
theorem size_render_traffic (pub : List Fp) (v : SizeV) (tr : Trace Fp) (t : Nat)
    (hlog : tr.log t = 2)
    (hcell : ∀ r x, r < tr.height t → x < SizeV3.width → tr.cell t r x = Fp.ofNat (SizeGen.cell pub v r x)) :
    TableTraffic SizeV3.interactions tr t pub (sizeTraffic v) :=
  size_render_traffic_at pub v tr t (by simp [Trace.height, hlog]) hcell

end ZkFormal.NearV3.Render
