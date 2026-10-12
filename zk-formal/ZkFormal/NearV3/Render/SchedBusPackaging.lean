import ZkFormal.NearV3.Render.SchedBusSPUBB

/-!
# Packaging step: `RenderBundleV3.Balanced` from the balances of the 51 used buses

`usedBuses`: every bus some `nearAirV3` table interaction or public segment uses (kernel-checked:
`table_buses`, `pub_buses`).  On any other bus both sides of every bundle are empty
(`balancedAt_unused`), so **`balanced_of_used`**: a bundle is balanced as soon as it balances the used
buses.  Where each used bus comes from (state 2026-10-12; numbers from `#eval`):

* receipt side, `rcpt_trie_sched` (`BusBalanced`, the same proposition: `balancedAt_of_bus`):
  SREC 16, RCL 26, AKC 27, RIDS 8, MEM 7, QVC 63, QSH 29, SRC 14, BNDP 28, BND 15;
* trie side, `rcpt_trie_sched`: PARENT 2, VPARENT 22, ENT 20, DIGS 17, DUP 19, EDGE 4, BMAP 11, MIDROOT 24,
  ROOT 10, UPB 25, MEMD 23, RPL 70, RPLV 71; shared SIZE 18, VSLOT 3, KEYNIB 5, FINAL 6, BYTES 0,
  DIGEST 1; codec ↔ ups S0F 59, SPOST 60, SPLEN 61;
* scheduler (`sched_side`): SCMP 40, SOP 41, SFIN 42, SINC 43, SPUSH 44, SPUBB 51, SPAR 52, SDL 56,
  SDLX 57, SDG 58, SA0 62;
* sibling lanes: MPOS 9, VBYTES 21 (lane v3-render-vbytes); 45–50 (lane v3-render-chacha).
-/
set_option autoImplicit false
namespace ZkFormal.NearV3.Assembly
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near ZkFormal.NearV3.Render

/-- Every bus a `nearAirV3` table or public segment uses. -/
def usedBuses : List Nat :=
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 40, 41,
   42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 56, 57, 58, 59, 60, 61, 62, 63, 70, 71]

theorem table_buses : ((List.range 25).all fun t =>
    (nearTablesFull.getD t default).interactions.all fun i => usedBuses.contains i.bus) = true := by
  decide +kernel

theorem pub_buses : (nearAirV3.pubSegs.all fun g => usedBuses.contains g.bus) = true := by
  decide +kernel

theorem covers_unused (b : Nat) (hb : b ∉ usedBuses) (s : Bool) : Covers b s (fun _ => false) = true := by
  unfold Covers
  apply List.all_eq_true.mpr
  intro t ht
  have h1 := List.all_eq_true.mp table_buses t ht
  simp only [Bool.false_or]
  apply List.all_eq_true.mpr
  intro i hi
  have h2 := List.all_eq_true.mp h1 i hi
  have hne : i.bus ≠ b := by
    intro e; rw [e] at h2; exact hb (List.contains_iff_mem.mp h2)
  simp [hne]

theorem pub_unused (b : Nat) (hb : b ∉ usedBuses) (s : Bool) (pub m : List Fp) :
    pubCount nearAirV3 pub b s m = 0 := by
  apply ZkFormal.Chacha.pubCount_zero
  intro seg hseg hbus _
  have := List.all_eq_true.mp pub_buses seg hseg
  rw [hbus] at this
  exact hb (List.contains_iff_mem.mp this)

namespace RenderBundleV3

theorem balancedAt_unused {pub : List Fp} (R : RenderBundleV3 pub) (b : Nat) (hb : b ∉ usedBuses) :
    R.BalancedAt b := by
  intro m
  rw [R.sum_tables true _ m _ (covers_unused b hb true), R.sum_tables false _ m _ (covers_unused b hb false),
    pub_unused b hb true, pub_unused b hb false]
  have hf : (List.range 25).filter (fun _ => false) = [] := by decide
  rw [hf]
  simp

theorem balancedAt_of_bus {pub : List Fp} (R : RenderBundleV3 pub) (b : Nat) (h : RcptBal.BusBalanced R b) :
    R.BalancedAt b := h

/-- **A bundle that balances every used bus is balanced.** -/
theorem balanced_of_used {pub : List Fp} (R : RenderBundleV3 pub) (h : ∀ b ∈ usedBuses, R.BalancedAt b) :
    R.Balanced :=
  (R.balanced_iff).mpr fun b => if hb : b ∈ usedBuses then h b hb else R.balancedAt_unused b hb

end RenderBundleV3
end ZkFormal.NearV3.Assembly
