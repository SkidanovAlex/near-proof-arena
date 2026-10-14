import ZkFormal.NearV3.D1.Extract.Akm.Decode
import ZkFormal.NearV3.D1.Extract.AkmView

/-!
# `ZkFormal.NearV3.D1.Extract.Akm.Traffic` — the bus traffic of an `akmV3` row and segment
-/

namespace ZkFormal.NearV3.D1.AkmProof

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.D1
  ZkFormal.NearV3.D1.AkmV3

variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}

theorem multNat1 (x : Nat) (q : Nat) :
    Interaction.multNat.go tr tt q pub [c x] 0 = if tr.cell tt q x = 1 then 1 else 0 := by
  simp only [Interaction.multNat.go, eval_c]
  by_cases h : tr.cell tt q x = 1 <;> simp [h]

/-- The traffic of row `q`, interaction by interaction. -/
theorem rowT (q bb : Nat) (sd : Bool) :
    rowTraffic AkmV3.interactions tr tt q pub bb sd =
      (if bb = B_VBYTES ∧ sd = true ∧ tr.cell tt q act = 1 then
        [[tr.cell tt q vid, tr.cell tt q pos, bE.eval tr tt q pub]] else []) ++
      (if bb = B_AKMEM ∧ sd = true ∧ tr.cell tt q sN = 1 then
        [[tr.cell tt q vid, ((0 : Nat) : Fp), tr.cell tt q ix, bE.eval tr tt q pub, tr.cell tt q (t 1)]] else []) ++
      (if bb = B_AKMEM ∧ sd = false ∧ tr.cell tt q sN = 1 then
        [[tr.cell tt q vid, tr.cell tt q tlast, tr.cell tt q ix, tr.cell tt q pb, tr.cell tt q (t 1)]] else []) ++
      (if bb = B_VSLOT ∧ sd = true ∧ tr.cell tt q aF = 1 then [[tr.cell tt q vid]] else []) ++
      (if bb = B_BYTES ∧ sd = true ∧ tr.cell tt q nF = 1 then
        [[((K_VPOST : Nat) : Fp) + ((16 : Nat) : Fp) * tr.cell tt q vid, tr.cell tt q pos, tr.cell tt q pb]] else []) ++
      (if bb = B_BYTES ∧ sd = true ∧ tr.cell tt q tF = 1 then
        [[((K_VPOST : Nat) : Fp) + ((16 : Nat) : Fp) * tr.cell tt q vid, tr.cell tt q pos, bE.eval tr tt q pub]]
        else []) ++
      (if bb = B_AKC ∧ sd = true ∧ tr.cell tt q aF = 1 then [[tr.cell tt q vid, ((0 : Nat) : Fp)]] else []) ++
      (if bb = B_AKC ∧ sd = false ∧ tr.cell tt q aF = 1 then [[tr.cell tt q vid, tr.cell tt q U]] else []) := by
  simp only [rowTraffic, AkmV3.interactions, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    Dsl.recv, Dsl.send, Interaction.multNat, multNat1, Interaction.msgVal, List.map_cons,
    List.map_nil, eval_c, eval_k, eval_mid, vpost, List.append_assoc]
  have ap : ∀ {a b c d : List (List Fp)}, a = b → c = d → a ++ c = b ++ d := by
    intro a b c d h1 h2; rw [h1, h2]
  refine ap ?_ (ap ?_ (ap ?_ (ap ?_ (ap ?_ (ap ?_ (ap ?_ ?_)))))) <;>
    (split <;> split <;> simp_all [eq_comm]) <;> first | rfl | grind

/-- The entry of the segment `s … s+ℓ−1`. -/
def akmOf (tr : Trace Fp) (tt s ℓ : Nat) : AkmE :=
  { vid := cv tr tt s vid, fa := cv tr tt s (t 1), tlast := cv tr tt s tlast, U := cv tr tt s U,
    bytes := (List.range ℓ).map fun j => bvA tr tt (s + j),
    pb := (List.range 8).map fun j => cv tr tt (s + j) pb }

/-- The messages of offset `j` of segment `e` (as naturals). -/
def rowMsgsA (e : AkmE) (j bb : Nat) (sd : Bool) : List Msg :=
  if sd then
    (if bb = B_VBYTES then [[e.vid, j, e.bytes.getD j 0]] else []) ++
    (if bb = B_AKMEM ∧ j < 8 then [[e.vid, 0, j, e.bytes.getD j 0, e.fa]] else []) ++
    (if bb = B_VSLOT ∧ j = 0 ∧ e.fa = 1 then [[e.vid]] else []) ++
    (if bb = B_BYTES ∧ j < 8 ∧ e.fa = 1 then [[e.vpost, j, e.pb.getD j 0]] else []) ++
    (if bb = B_BYTES ∧ j = 8 ∧ e.fa = 1 then [[e.vpost, 8, e.bytes.getD 8 0]] else []) ++
    (if bb = B_AKC ∧ j = 0 ∧ e.fa = 1 then [[e.vid, 0]] else [])
  else
    (if bb = B_AKMEM ∧ j < 8 then [[e.vid, e.tlast, j, e.pb.getD j 0, e.fa]] else []) ++
    (if bb = B_AKC ∧ j = 0 ∧ e.fa = 1 then [[e.vid, e.U]] else [])

theorem range_split8 (L : Nat) (h : 8 ≤ L) : List.range L = List.range 8 ++ List.range' 8 (L - 8) := by
  rw [List.range_eq_range', List.range_eq_range', show L = 8 + (L - 8) by omega, ← List.range'_append]; simp

theorem fm_lt8 {α : Type} (L : Nat) (h : 8 ≤ L) (m : Nat → α) :
    ((List.range L).flatMap fun j => if j < 8 then [m j] else []) = (List.range 8).map m := by
  rw [range_split8 L h, List.flatMap_append, flatMap_range'_nil _ 8 (L - 8) (fun j _ => by simp),
    List.append_nil, map_eq_flatMap]
  exact flatMap_congr' (fun j hj => by simp [List.mem_range.1 hj])

theorem fm_eq0 {α : Type} (L : Nat) (h : 1 ≤ L) (x : α) :
    ((List.range L).flatMap fun j => if j = 0 then [x] else []) = [x] := by
  rw [List.range_eq_range', show L = 1 + (L - 1) by omega, ← List.range'_append, List.flatMap_append]
  simp only [List.range'_one, List.flatMap_cons, List.flatMap_nil, if_pos rfl, List.append_nil]
  rw [flatMap_range'_nil _ (0 + 1) (L - 1) (fun j _ => by simp)]; rfl

/-- The segment's traffic is the offsets' messages. -/
theorem rowMsgsA_sum (e : AkmE) (h9 : 9 ≤ e.bytes.length) (hfa : e.fa = 1 → e.bytes.length = 9)
    (bb : Nat) (sd : Bool) :
    (List.range e.bytes.length).flatMap (fun j => rowMsgsA e j bb sd) =
      (if sd then akmSends [e] bb else akmRecvs [e] bb) := by
  have hne : ∀ a b : Nat, a ≠ b → (a = b) = False := fun a b h => by simp [h]
  cases sd
  · by_cases h1 : bb = B_AKMEM
    · subst h1
      rw [flatMap_congr' (G := fun j => if j < 8 then [[e.vid, e.tlast, j, e.pb.getD j 0, e.fa]] else [])
        (fun j _ => by simp [rowMsgsA, B_AKMEM, B_AKC]), fm_lt8 _ (by omega)]
      simp [akmRecvs]
    by_cases h2 : bb = B_AKC
    · subst h2
      by_cases hf : e.fa = 1
      · rw [flatMap_congr' (G := fun j => if j = 0 then [[e.vid, e.U]] else [])
          (fun j _ => by by_cases h : j = 0 <;> simp [h, hf, rowMsgsA, B_AKMEM, B_AKC]), fm_eq0 _ (by omega)]
        simp [akmRecvs, hf, B_AKMEM, B_AKC]
      · rw [flatMap_congr' (G := fun _ => []) (fun j _ => by simp [hf, rowMsgsA, B_AKMEM, B_AKC]), flatMap_nil_fun]
        simp [akmRecvs, hf, B_AKMEM, B_AKC]
    rw [flatMap_congr' (G := fun _ => []) (fun j _ => by simp [rowMsgsA, h1, h2]), flatMap_nil_fun]
    simp [akmRecvs, h1, h2]
  · by_cases h1 : bb = B_VBYTES
    · subst h1
      rw [flatMap_congr' (G := fun j => [[e.vid, j, e.bytes.getD j 0]])
        (fun j _ => by simp [rowMsgsA, B_VBYTES, B_AKMEM, B_VSLOT, B_BYTES, B_AKC])]
      simp [akmSends, map_eq_flatMap]
    by_cases h2 : bb = B_AKMEM
    · subst h2
      rw [flatMap_congr' (G := fun j => if j < 8 then [[e.vid, 0, j, e.bytes.getD j 0, e.fa]] else [])
        (fun j _ => by simp [rowMsgsA, B_VBYTES, B_AKMEM, B_VSLOT, B_BYTES, B_AKC]), fm_lt8 _ (by omega)]
      simp [akmSends, B_VBYTES, B_AKMEM]
    by_cases hf : e.fa = 1
    · have hl := hfa hf
      by_cases h3 : bb = B_VSLOT
      · subst h3
        rw [flatMap_congr' (G := fun j => if j = 0 then [[e.vid]] else [])
          (fun j _ => by by_cases h : j = 0 <;> simp [h, hf, rowMsgsA, B_VBYTES, B_AKMEM, B_VSLOT, B_BYTES, B_AKC]),
          fm_eq0 _ (by omega)]
        simp [akmSends, hf, B_VBYTES, B_AKMEM, B_VSLOT]
      by_cases h4 : bb = B_BYTES
      · subst h4
        rw [hl, show List.range 9 = List.range 8 ++ [8] by decide, List.flatMap_append,
          flatMap_congr' (G := fun j => [[e.vpost, j, e.pb.getD j 0]])
            (fun j hj => by have := List.mem_range.1 hj; simp [this, hf, rowMsgsA, B_VBYTES, B_AKMEM, B_VSLOT,
              B_BYTES, B_AKC, show j ≠ 8 by omega])]
        simp [akmSends, hf, rowMsgsA, B_VBYTES, B_AKMEM, B_VSLOT, B_BYTES, B_AKC, map_eq_flatMap]
      by_cases h5 : bb = B_AKC
      · subst h5
        rw [flatMap_congr' (G := fun j => if j = 0 then [[e.vid, 0]] else [])
          (fun j _ => by by_cases h : j = 0 <;> simp [h, hf, rowMsgsA, B_VBYTES, B_AKMEM, B_VSLOT, B_BYTES, B_AKC]),
          fm_eq0 _ (by omega)]
        simp [akmSends, hf, B_VBYTES, B_AKMEM, B_VSLOT, B_BYTES, B_AKC]
      rw [flatMap_congr' (G := fun _ => []) (fun j _ => by simp [rowMsgsA, h1, h2, h3, h4, h5]), flatMap_nil_fun]
      simp [akmSends, h1, h2, h3, h4, h5]
    · rw [flatMap_congr' (G := fun _ => []) (fun j _ => by simp [rowMsgsA, h1, h2, hf]), flatMap_nil_fun]
      simp [akmSends, h1, h2, hf]

end ZkFormal.NearV3.D1.AkmProof
