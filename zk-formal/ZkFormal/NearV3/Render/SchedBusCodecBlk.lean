import ZkFormal.NearV3.Render.SchedBusCodec

/-!
# Codec (table 11) scheduler-bus traffic per descriptor and per block

`*T d`: the row traffic of descriptor `d` on one bus/side (`rt_*`), and the block-level closed forms
`blk_*` (`B.descs.flatMap *T`) for `SA0`, `SDL`, `SPUBB`, `SPAR`, `SOP`, `SFIN`, `SDG`.
-/
set_option linter.unusedSimpArgs false
namespace ZkFormal.NearV3.Render.Cdc
open ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen
open ZkFormal.Near
open ZkFormal.NearV3.Candidates.SchedSetAll ZkFormal.NearV3.Sched.Codec

def sa0sT : Desc → List (List Fp)
  | .record I R f gg _ bpr apv _ bigv => if f = 2 ∧ gg = 7 ∧ R.useC = true then
      [[Fp.ofNat I.tv, Fp.ofNat R.kk, Fp.ofNat apv, Fp.ofNat (if bigv = 1 ∨ bpr ≠ 0 then 1 else 0)]] else []
  | _ => []

def sa0rT : Desc → List (List Fp)
  | .record I R f gg _ _ _ _ _ => if f = 2 ∧ gg = 2 ∧ R.hasC = true then
      [[Fp.ofNat I.tv, Fp.ofNat R.srcS, Fp.ofNat (apRv R), Fp.ofNat (bigRv R)]] else []
  | _ => []

def sdlsT : Desc → List (List Fp)
  | .record I R f gg bpo _ _ _ _ => if f < 2 then
      [[Fp.ofNat (I.tv + 1), Fp.ofNat (R.kk % 256), Fp.ofNat (R.kk / 256), Fp.ofNat (8 * f + gg), Fp.ofNat bpo]] else []
  | _ => []

def sdlrT : Desc → List (List Fp)
  | .record I R f gg bpo _ _ _ _ => if f < 2 then
      [[Fp.ofNat I.tv, Fp.ofNat (R.kk % 256), Fp.ofNat (R.kk / 256), Fp.ofNat (8 * f + gg), Fp.ofNat bpo]] else []
  | _ => []

def spubbT : Desc → List (List Fp)
  | .record I R f gg _ _ _ _ _ => if f = 2 ∧ gg = 7 ∧ I.tv = 0 then
      [[0, Fp.ofNat 4, Fp.ofNat (R.kk % 256), Fp.ofNat (R.kk / 256), Fp.ofNat (R.ft % 256),
        Fp.ofNat (R.ft / 256 % 256), Fp.ofNat (R.ft / 65536 % 256)]] else []
  | .ash I ash j => [[Fp.ofNat I.tv, Fp.ofNat 2, Fp.ofNat j, Fp.ofNat (ash.getD j 0), 0, 0, 0]]
  | _ => []

def sparT : Desc → List (List Fp)
  | .hdr I p => if p = 0 then
      [[Fp.ofNat I.tv, 0, Fp.ofNat I.n, Fp.ofNat (I.N % 256), Fp.ofNat (I.N / 256 % 256),
        Fp.ofNat (I.base % 256), Fp.ofNat (I.base / 256 % 256), Fp.ofNat (I.base / 65536 % 256),
        Fp.ofNat (I.fair % 256), Fp.ofNat (I.fair / 256 % 256), Fp.ofNat (I.fair / 65536 % 256)]] else []
  | _ => []

def sopT : Desc → List (List Fp)
  | .record I R f gg _ _ _ _ _ => if f = 2 ∧ gg = 7 then
      [[Fp.ofNat (16384 * I.tv + R.kk), 0, 0, Fp.ofNat (b2n R.al), Fp.ofNat (a1v I R - b2n R.al * I.base),
        Fp.ofNat (b2n R.al * I.base), 0, 1]] else []
  | _ => []

def sfinT : Desc → List (List Fp)
  | .record I R f gg _ _ _ _ _ => if f = 2 ∧ gg = 7 then
      [[Fp.ofNat (16384 * I.tv + R.kk), Fp.ofNat R.afin, Fp.ofNat R.gfin]] else []
  | _ => []

def sdgT : Desc → List (List Fp)
  | .record I R f gg _ _ _ _ _ => if f = 0 ∧ gg = 0 then
      [[Fp.ofNat I.tv, Fp.ofNat R.kk, Fp.ofNat (b2n R.al), Fp.ofNat R.gb, Fp.ofNat R.srcS,
        Fp.ofNat (b2n R.hasC), Fp.ofNat (b2n R.useC)]] else []
  | _ => []

theorem rt_sa0s (d : Desc) (r t : Nat) (pub : List Fp) :
    rowTraffic Codec.table.interactions (dRow d r) t r pub B_SA0 true = sa0sT d := by
  cases d <;> simp only [sa0sT, sa0_send_hdr, sa0_send_rec, sa0_send_hash, sa0_send_ash]

theorem rt_sa0r (d : Desc) (r t : Nat) (pub : List Fp) :
    rowTraffic Codec.table.interactions (dRow d r) t r pub B_SA0 false = sa0rT d := by
  cases d <;> simp only [sa0rT, sa0_recv_hdr, sa0_recv_rec, sa0_recv_hash, sa0_recv_ash]

theorem rt_sdls (d : Desc) (r t : Nat) (pub : List Fp) :
    rowTraffic Codec.table.interactions (dRow d r) t r pub B_SDL true = sdlsT d := by
  cases d <;> simp only [sdlsT, sdl_send_hdr, sdl_send_rec, sdl_send_hash, sdl_send_ash]

theorem rt_sdlr (d : Desc) (r t : Nat) (pub : List Fp) :
    rowTraffic Codec.table.interactions (dRow d r) t r pub B_SDL false = sdlrT d := by
  cases d <;> simp only [sdlrT, sdl_recv_hdr, sdl_recv_rec, sdl_recv_hash, sdl_recv_ash]

theorem rt_spubb (d : Desc) (r t : Nat) (pub : List Fp) :
    rowTraffic Codec.table.interactions (dRow d r) t r pub B_SPUBB false = spubbT d := by
  cases d <;> simp only [spubbT, spubb_hdr, spubb_rec, spubb_hash, spubb_ash]

theorem rt_spar (d : Desc) (r t : Nat) (pub : List Fp) :
    rowTraffic Codec.table.interactions (dRow d r) t r pub B_SPAR false = sparT d := by
  cases d <;> simp only [sparT, spar_hdr, spar_rec, spar_hash, spar_ash]

theorem rt_sop (d : Desc) (r t : Nat) (pub : List Fp) :
    rowTraffic Codec.table.interactions (dRow d r) t r pub B_SOP true = sopT d := by
  cases d <;> simp only [sopT, sop_hdr, sop_rec, sop_hash, sop_ash]

theorem rt_sfin (d : Desc) (r t : Nat) (pub : List Fp) :
    rowTraffic Codec.table.interactions (dRow d r) t r pub B_SFIN false = sfinT d := by
  cases d <;> simp only [sfinT, sfin_hdr, sfin_rec, sfin_hash, sfin_ash]

theorem rt_sdg (d : Desc) (r t : Nat) (pub : List Fp) :
    rowTraffic Codec.table.interactions (dRow d r) t r pub B_SDG false = sdgT d := by
  cases d <;> simp only [sdgT, sdg_hdr, sdg_rec, sdg_hash, sdg_ash]

/-! ## Block level -/

theorem flatten_flatMap' {α β : Type} (l : List (List α)) (G : α → List β) :
    l.flatten.flatMap G = l.flatMap (fun x => x.flatMap G) := by
  induction l with
  | nil => rfl
  | cons x l ih => simp only [List.flatten_cons, List.flatMap_append, List.flatMap_cons, ih]

theorem flatMap_congr'' {α β : Type} {l : List α} {f g : α → List β} (h : ∀ x ∈ l, f x = g x) :
    l.flatMap f = l.flatMap g := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    simp only [List.flatMap_cons]
    rw [h x (by simp), ih (fun y hy => h y (by simp [hy]))]

theorem descs_flat (B : Blk) (G : Desc → List (List Fp)) :
    B.descs.flatMap G = ((List.range 5).map (Desc.hdr B.I)).flatMap G ++
      (List.range B.I.N).flatMap (fun kk => (List.range 3).flatMap fun f =>
        (List.range 8).flatMap fun gg => G (B.recD kk f gg)) ++
      ((List.range 32).map (Desc.hash B.I B.dig B.hpre)).flatMap G ++
      ((List.range 32).map (Desc.ash B.I B.ash)).flatMap G := by
  simp only [Blk.descs, List.flatMap_append, Blk.records, flatten_flatMap', List.flatMap_map]
  congr 3
  apply flatMap_congr''
  intro kk _
  simp [Blk.recordDescs, Blk.fieldDescs, List.range_succ, List.flatMap_append]

theorem descs_rec (B : Blk) (G : Desc → List (List Fp)) (h1 : ∀ p, G (.hdr B.I p) = [])
    (h2 : ∀ j, G (.hash B.I B.dig B.hpre j) = []) (h3 : ∀ j, G (.ash B.I B.ash j) = []) :
    B.descs.flatMap G = (List.range B.I.N).flatMap (fun kk => (List.range 3).flatMap fun f =>
        (List.range 8).flatMap fun gg => G (B.recD kk f gg)) := by
  rw [descs_flat]
  simp [List.flatMap_map, h1, h2, h3]

theorem blk_sa0s (B : Blk) : B.descs.flatMap sa0sT = (List.range B.I.N).flatMap fun kk =>
    if (B.recs kk).useC = true then
      [[Fp.ofNat B.I.tv, Fp.ofNat (B.recs kk).kk, Fp.ofNat (B.apS kk 7),
        Fp.ofNat (if B.bigS kk 7 = 1 ∨ B.bpr kk 2 7 ≠ 0 then 1 else 0)]] else [] := by
  rw [descs_rec B _ (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)]
  apply flatMap_congr''
  intro kk _
  simp [List.range_succ, Blk.recD, sa0sT]

theorem blk_sa0r (B : Blk) : B.descs.flatMap sa0rT = (List.range B.I.N).flatMap fun kk =>
    if (B.recs kk).hasC = true then
      [[Fp.ofNat B.I.tv, Fp.ofNat (B.recs kk).srcS, Fp.ofNat (apRv (B.recs kk)), Fp.ofNat (bigRv (B.recs kk))]]
    else [] := by
  rw [descs_rec B _ (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)]
  apply flatMap_congr''
  intro kk _
  simp [List.range_succ, Blk.recD, sa0rT]

theorem blk_sdls (B : Blk) : B.descs.flatMap sdlsT = (List.range B.I.N).flatMap fun kk =>
    (List.range 16).map fun o => [Fp.ofNat (B.I.tv + 1), Fp.ofNat ((B.recs kk).kk % 256),
      Fp.ofNat ((B.recs kk).kk / 256), Fp.ofNat o, Fp.ofNat (B.bpo kk (o / 8) (o % 8))] := by
  rw [descs_rec B _ (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)]
  apply flatMap_congr''
  intro kk _
  simp [List.range_succ, Blk.recD, sdlsT]

theorem blk_sdlr (B : Blk) : B.descs.flatMap sdlrT = (List.range B.I.N).flatMap fun kk =>
    (List.range 16).map fun o => [Fp.ofNat B.I.tv, Fp.ofNat ((B.recs kk).kk % 256),
      Fp.ofNat ((B.recs kk).kk / 256), Fp.ofNat o, Fp.ofNat (B.bpo kk (o / 8) (o % 8))] := by
  rw [descs_rec B _ (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)]
  apply flatMap_congr''
  intro kk _
  simp [List.range_succ, Blk.recD, sdlrT]

theorem blk_spubb (B : Blk) : B.descs.flatMap spubbT =
    (if B.I.tv = 0 then (List.range B.I.N).map fun kk =>
      [0, Fp.ofNat 4, Fp.ofNat ((B.recs kk).kk % 256), Fp.ofNat ((B.recs kk).kk / 256),
        Fp.ofNat ((B.recs kk).ft % 256), Fp.ofNat ((B.recs kk).ft / 256 % 256),
        Fp.ofNat ((B.recs kk).ft / 65536 % 256)] else []) ++
    (List.range 32).map fun j => [Fp.ofNat B.I.tv, Fp.ofNat 2, Fp.ofNat j, Fp.ofNat (B.ash.getD j 0), 0, 0, 0] := by
  rw [descs_flat]
  have hr : (List.range B.I.N).flatMap (fun kk => (List.range 3).flatMap fun f =>
        (List.range 8).flatMap fun gg => spubbT (B.recD kk f gg)) =
      (List.range B.I.N).flatMap fun kk => if B.I.tv = 0 then
      [[0, Fp.ofNat 4, Fp.ofNat ((B.recs kk).kk % 256), Fp.ofNat ((B.recs kk).kk / 256),
        Fp.ofNat ((B.recs kk).ft % 256), Fp.ofNat ((B.recs kk).ft / 256 % 256),
        Fp.ofNat ((B.recs kk).ft / 65536 % 256)]] else [] := by
    apply flatMap_congr''
    intro kk _
    by_cases ht : B.I.tv = 0 <;> simp [List.range_succ, Blk.recD, spubbT, ht]
  rw [hr]
  by_cases ht : B.I.tv = 0
  · simp [ht, List.flatMap_map, spubbT, List.range_succ, ← flat_single]
  · simp [ht, List.flatMap_map, spubbT, List.range_succ]

theorem blk_spar (B : Blk) : B.descs.flatMap sparT =
    [[Fp.ofNat B.I.tv, 0, Fp.ofNat B.I.n, Fp.ofNat (B.I.N % 256), Fp.ofNat (B.I.N / 256 % 256),
        Fp.ofNat (B.I.base % 256), Fp.ofNat (B.I.base / 256 % 256), Fp.ofNat (B.I.base / 65536 % 256),
        Fp.ofNat (B.I.fair % 256), Fp.ofNat (B.I.fair / 256 % 256), Fp.ofNat (B.I.fair / 65536 % 256)]] := by
  rw [descs_flat]
  simp [List.flatMap_map, sparT, List.range_succ, Blk.recD]

theorem blk_sop (B : Blk) : B.descs.flatMap sopT = (List.range B.I.N).map fun kk =>
    [Fp.ofNat (16384 * B.I.tv + (B.recs kk).kk), 0, 0, Fp.ofNat (b2n (B.recs kk).al),
      Fp.ofNat (a1v B.I (B.recs kk) - b2n (B.recs kk).al * B.I.base),
      Fp.ofNat (b2n (B.recs kk).al * B.I.base), 0, 1] := by
  rw [descs_rec B _ (fun _ => rfl) (fun _ => rfl) (fun _ => rfl), ← flat_single]
  apply flatMap_congr''
  intro kk _
  simp [List.range_succ, Blk.recD, sopT]

theorem blk_sfin (B : Blk) : B.descs.flatMap sfinT = (List.range B.I.N).map fun kk =>
    [Fp.ofNat (16384 * B.I.tv + (B.recs kk).kk), Fp.ofNat (B.recs kk).afin, Fp.ofNat (B.recs kk).gfin] := by
  rw [descs_rec B _ (fun _ => rfl) (fun _ => rfl) (fun _ => rfl), ← flat_single]
  apply flatMap_congr''
  intro kk _
  simp [List.range_succ, Blk.recD, sfinT]

theorem blk_sdg (B : Blk) : B.descs.flatMap sdgT = (List.range B.I.N).map fun kk =>
    [Fp.ofNat B.I.tv, Fp.ofNat (B.recs kk).kk, Fp.ofNat (b2n (B.recs kk).al), Fp.ofNat (B.recs kk).gb,
      Fp.ofNat (B.recs kk).srcS, Fp.ofNat (b2n (B.recs kk).hasC), Fp.ofNat (b2n (B.recs kk).useC)] := by
  rw [descs_rec B _ (fun _ => rfl) (fun _ => rfl) (fun _ => rfl), ← flat_single]
  apply flatMap_congr''
  intro kk _
  simp [List.range_succ, Blk.recD, sdgT]

end ZkFormal.NearV3.Render.Cdc
