import ZkFormal.Near.Extract.Segments
import ZkFormal.Near.Extract.BusCount
import ZkFormal.Near.Extract.Eval
import ZkFormal.NearV3.D1.Tables.RelayDefs

/-!
# `ZkFormal.NearV3.D1.Extract.KibProof` — the `kibV3` view (`KibViewStmt`, `kib_view`)

Lane `v3-d1-phase2` (docs/zk-formal/V3-D1-PHASE2.md, milestone V1).  One `KibE` per active row
(in row order): the public key-nibble record `(w₀, w₁, w₂, t, sym, last)`.  Traffic: receives
`PKEY (w₀, w₁, w₂, t, sym, last)`, sends `KEYNIB (w₀ + 2⁸·w₁ + 2¹⁶·w₂, t, sym, last)` (the walk
id as a natural; `walkV3` and the public segment fix the byte ranges at link time).
-/

namespace ZkFormal.NearV3.D1

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near

structure KibE where
  w0 : Nat
  w1 : Nat
  w2 : Nat
  t : Nat
  sym : Nat
  last : Nat
  deriving Repr, Inhabited

/-- The walk id the row sends. -/
def KibE.wid (e : KibE) : Nat := e.w0 + 256 * e.w1 + 65536 * e.w2

structure KibWf (es : List KibE) : Prop where
  canon : ∀ e ∈ es, e.w0 < P ∧ e.w1 < P ∧ e.w2 < P ∧ e.t < P ∧ e.sym < P ∧ e.last < P
  rows : es.length ≤ 2 ^ KibV3.maxLog

def kibSends (es : List KibE) (b : Nat) : List Msg :=
  if b = B_KEYNIB then es.map fun e => [e.wid, e.t, e.sym, e.last] else []

def kibRecvs (es : List KibE) (b : Nat) : List Msg :=
  if b = B_PKEY then es.map fun e => [e.w0, e.w1, e.w2, e.t, e.sym, e.last] else []

def kibTraffic (es : List KibE) : Traffic := ⟨kibSends es, kibRecvs es⟩

/-- **The `kibV3` view statement.** -/
def KibViewStmt : Prop :=
  ∀ (tr : Trace Fp) (pub : List Fp) (t : Nat), TableLocal KibV3.table tr t pub →
    ∃ es, KibWf es ∧ TableTraffic KibV3.interactions tr t pub (kibTraffic es)

end ZkFormal.NearV3.D1

namespace ZkFormal.NearV3.D1.KibProof

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.D1
  ZkFormal.NearV3.D1.KibV3

variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}

def rowOf (tr : Trace Fp) (tt q : Nat) : KibE :=
  ⟨cv tr tt q w0, cv tr tt q w1, cv tr tt q w2, cv tr tt q t, cv tr tt q sym, cv tr tt q last⟩

def isA (tr : Trace Fp) (tt q : Nat) : Bool := decide (tr.cell tt q act = 1)

theorem wid_toFp (q : Nat) :
    Fp.ofNat (rowOf tr tt q).wid =
      tr.cell tt q w0 + ((256 : Nat) * tr.cell tt q w1 + ((65536 : Nat) * tr.cell tt q w2 + 0)) := by
  simp only [KibE.wid, rowOf, cv]
  rw [← ofNat_add', ← ofNat_add', ← ofNat_mul', ← ofNat_mul', Fp.ofNat_toNat, Fp.ofNat_toNat,
    Fp.ofNat_toNat, ← natCast_eq, ← natCast_eq]
  grind

theorem rowT (q bb : Nat) (sd : Bool) :
    rowTraffic KibV3.interactions tr tt q pub bb sd =
      if isA tr tt q then
        (if sd then kibSends [rowOf tr tt q] bb else kibRecvs [rowOf tr tt q] bb).map Msg.toFp
      else [] := by
  unfold rowTraffic KibV3.interactions
  simp only [List.flatMap_cons, List.flatMap_nil, Dsl.send, Dsl.recv, Interaction.multNat,
    Interaction.multNat.go, Interaction.msgVal, List.map_cons, List.map_nil, List.append_nil]
  by_cases ha : tr.cell tt q act = 1
  · have hw := wid_toFp (tr := tr) (tt := tt) q
    simp only [eval_c, ha, ite_true, isA, decide_true]
    cases sd <;> by_cases h1 : bb = B_PKEY <;> by_cases h2 : bb = B_KEYNIB <;>
      simp_all [kibSends, kibRecvs, Msg.toFp, B_PKEY, B_KEYNIB, KibV3.wE, rowOf, cv,
        Fp.ofNat_toNat]
    all_goals first | rfl | exact fun h => h1 h.symm | exact fun h => h2 h.symm
  · simp [eval_c, ha, isA]

theorem kibSends_flat (es : List KibE) (b : Nat) :
    kibSends es b = es.flatMap fun e => kibSends [e] b := by
  unfold kibSends; split <;> simp [map_eq_flatMap]

theorem kibRecvs_flat (es : List KibE) (b : Nat) :
    kibRecvs es b = es.flatMap fun e => kibRecvs [e] b := by
  unfold kibRecvs; split <;> simp [map_eq_flatMap]

theorem flatMap_if {α β : Type} (p : α → Bool) (f : α → List β) :
    ∀ l : List α, (l.flatMap fun q => if p q then f q else []) = (l.filter p).flatMap f
  | [] => rfl
  | a :: l => by
    by_cases h : p a = true
    · simp [h, flatMap_if p f l]
    · simp [h, flatMap_if p f l]

end ZkFormal.NearV3.D1.KibProof

namespace ZkFormal.NearV3.D1

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near KibProof

/-- **The `kibV3` view.** -/
theorem kib_view : KibViewStmt := by
  intro tr pub tt hL
  let rows := (List.range (tr.height tt)).filter (isA tr tt)
  have hall : ∀ b sd, (List.range (tr.height tt)).flatMap
      (fun q => rowTraffic KibV3.interactions tr tt q pub b sd) =
      (if sd then kibSends (rows.map (rowOf tr tt)) b
       else kibRecvs (rows.map (rowOf tr tt)) b).map Msg.toFp := by
    intro b sd
    simp only [rowT]
    rw [flatMap_if]
    cases sd
    · simp only [Bool.false_eq_true, ite_false]
      rw [kibRecvs_flat, List.map_flatMap, List.flatMap_map]
    · simp only [ite_true]
      rw [kibSends_flat, List.map_flatMap, List.flatMap_map]
  refine ⟨rows.map (rowOf tr tt), ⟨?_, ?_⟩, fun b m => ⟨?_, ?_⟩⟩
  · intro e he
    obtain ⟨q, -, rfl⟩ := List.mem_map.1 he
    exact ⟨cv_lt _ _ _ _, cv_lt _ _ _ _, cv_lt _ _ _ _, cv_lt _ _ _ _, cv_lt _ _ _ _, cv_lt _ _ _ _⟩
  · rw [List.length_map]
    refine Nat.le_trans (List.length_filter_le _ _) ?_
    rw [List.length_range]
    unfold Trace.height
    exact Nat.pow_le_pow_right (by omega) hL.log_le
  · simp only [kibTraffic]; rw [tableBusCount_eq, hall]; rfl
  · simp only [kibTraffic]; rw [tableBusCount_eq, hall]; rfl

end ZkFormal.NearV3.D1
