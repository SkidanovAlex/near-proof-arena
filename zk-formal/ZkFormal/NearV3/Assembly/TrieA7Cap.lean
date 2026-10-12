import ZkFormal.NearV3.Assembly.TrieA7Ups
import ZkFormal.NearV3.Assembly.TrieUpsOrigin
import ZkFormal.NearV3.Assembly.TrieA7Post

/-!
# ZkFormal.NearV3.Assembly.TrieA7Cap — the ups row cap from A7

* `recsI_length`, **`R_eq`**: `R insts = 4·|insts| + upsA7Total insts`;
* `inst_total`: an instance with its scheduler SHA family has `L + Σ_k |Q_k| = |u.value| + outputByteCharge u.run`;
* **`upsA7Total_le_of_upsSha`**: `UpsSha insts → upsA7Total insts ≤ 2,000,000` (from the A7 (b) ups bound
  `TrieA7Post.ups_post_bound` carried by `UpsSha`), and that bound holds for the ranked instances too
  (`upsA7Total` only depends on `v`/parts, `prefix_map_eq`);
* **`rowCap_of_upsSha`**: `UpsSha insts → R insts + 1 ≤ 2^22` — the premise of `trie_all_of`'s ups render
  (`UpsRenderOk`), `UpbBal`.
-/

namespace ZkFormal.NearV3.Assembly.TrieA7Cap

open NearSpec NearSpecV3 ZkFormal.Near ZkFormal.NearV3 ZkFormal.NearV3.Assembly Render Render.UpsGen

theorem recsI_length (I : UpsInst) :
    (recsI I).length = 4 + (L I + ((List.range (nQ I)).map fun k => (part I k).q.length).sum) := by
  simp [recsI, List.length_flatMap]

private theorem sum_map_add {α : Type} (l : List α) (f g : α → Nat) :
    (l.map (fun x => f x + g x)).sum = (l.map f).sum + (l.map g).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.map_cons, List.sum_cons, ih]; omega

theorem R_eq (insts : List UpsInst) : UpsGen.R insts = 4 * insts.length + TrieA7.upsA7Total insts := by
  unfold UpsGen.R recs
  rw [List.length_flatMap]
  simp only [List.length_map, recsI_length]
  rw [ZkFormal.NearV3.Render.ValGen.map_getD default
    (fun I => 4 + (L I + ((List.range (nQ I)).map fun k => (part I k).q.length).sum)) insts]
  rw [sum_map_add]
  have h4 : (insts.map (fun _ => 4)).sum = 4 * insts.length := by
    induction insts with
    | nil => rfl
    | cons a l ih => simp only [List.map_cons, List.sum_cons, ih, List.length_cons]; omega
  rw [h4]
  rfl

theorem inst_total (u : SchedulerUpsertWitness) (I : UpsInst) (hf : NativeShaFamily u I)
    (hv : I.v = u.value.map UInt8.toNat) :
    L I + ((List.range (nQ I)).map fun k => (part I k).q.length).sum = u.value.length + outputByteCharge u.run := by
  obtain ⟨hn, hk⟩ := hf
  have hL : L I = u.value.length := by simp [L, hv]
  have hq : (List.range (nQ I)).map (fun k => (part I k).q.length) =
      u.run.parts.map (fun p => (ZkFormal.NearV3.nodeEnc p.output).length) := by
    apply List.ext_getElem (by simp [hn])
    intro k h1 h2
    simp only [List.getElem_map, List.getElem_range]
    have hk' : k < nQ I := by simpa using h1
    obtain ⟨M, hM, -, hb⟩ := hk k hk'
    have hp : k < u.run.parts.length := by omega
    rw [upsertShaJobs_part, List.getElem?_eq_getElem hp] at hM
    simp only [Option.map_some, Option.some.injEq] at hM
    rw [← hb, ← hM]
    simp [upsertShaJob]
  rw [hL, hq]
  rfl

/-- `upsA7Total` of the `UpsSha` instances is at most `B0 = 2,000,000`. -/
theorem upsA7Total_le_of_upsSha {insts : List UpsInst} (h : TrieUpsOrigin.UpsSha insts) :
    TrieA7.upsA7Total insts ≤ 2000000 ∧ insts.length ≤ 32 := by
  obtain ⟨us, hl, h32, -, -, -, hpost, hI⟩ := h
  refine ⟨?_, by omega⟩
  have e : insts.map (fun I => L I + ((List.range (nQ I)).map fun k => (part I k).q.length).sum) =
      us.map (fun u => u.value.length + outputByteCharge u.run) := by
    apply List.ext_getElem (by simp [hl])
    intro i h1 h2
    simp only [List.getElem_map]
    have hi1 : i < insts.length := by simpa using h1
    have hi2 : i < us.length := by simpa using h2
    have hu : us[i]? = some us[i] := List.getElem?_eq_getElem hi2
    have hI' : insts[i]? = some insts[i] := List.getElem?_eq_getElem hi1
    obtain ⟨hf, hv, -⟩ := hI i us[i] insts[i] hu hI'
    exact inst_total us[i] insts[i] hf hv
  unfold TrieA7.upsA7Total
  rw [e]
  exact hpost

/-- **The ups row cap**: `UpsSha insts → R insts + 1 ≤ 2^22` (`R ≤ 4·32 + 2,000,000`). -/
theorem rowCap_of_upsSha {insts : List UpsInst} (h : TrieUpsOrigin.UpsSha insts) : UpsGen.R insts + 1 ≤ 2 ^ 22 := by
  obtain ⟨h1, h2⟩ := upsA7Total_le_of_upsSha h
  rw [R_eq]
  have : (2 : Nat) ^ 22 = 4194304 := by decide
  omega

end ZkFormal.NearV3.Assembly.TrieA7Cap
