import ZkFormal.NearV3.Render.CodecSanity

/-!
# Codec (table 11) traffic on the scheduler buses `SA0`, `SDL`, `SPUBB`, `SPAR`, `SOP`, `SFIN`, `SDG`

Generic per-row traffic of a descriptor row (`bus_*`, via `cv d col`) and per-kind closed forms.
-/
set_option linter.unusedSimpArgs false
namespace ZkFormal.NearV3.Render.Cdc
open ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen
open ZkFormal.Near
open ZkFormal.NearV3.Candidates.SchedSetAll ZkFormal.NearV3.Sched.Codec ZkFormal.Chacha.Table.E

set_option maxRecDepth 65536 in
theorem bus_sa0_send (d : Desc) (r t : Nat) (pub : List Fp) :
    rowTraffic Codec.table.interactions (dRow d r) t r pub B_SA0 true =
      List.replicate (if cv d u0g = 1 then 1 else 0) [cv d tau, cv d kidx, cv d ap, cv d bF] := by
  simp only [rowTraffic, Codec.table, interactions, List.flatMap_cons, List.flatMap_nil,
    ZkFormal.NearV3.B_S0F, Sched.B_S0F, ZkFormal.NearV3.B_SPLEN, ZkFormal.NearV3.B_SPOST, ZkFormal.NearV3.B_VBYTES, Sched.B_SPOST, ZkFormal.Near.B_BYTES,
    ZkFormal.Near.B_DIGEST, Sched.B_SPLEN, Sched.B_SPAR, Sched.B_SDL, Sched.B_SPUBB, Sched.B_SOP,
    Sched.B_SFIN, Sched.B_SDG, Sched.B_SA0, Sched.B_SCMP]
  simp only [Nat.reduceEqDiff, Bool.false_eq_true, and_false, and_true, false_and, true_and,
    ite_false, ite_true, List.append_nil, List.nil_append, decide_true, decide_false, Bool.true_eq_false]
  simp only [Interaction.multNat, mult1, Interaction.msgVal, List.map_cons, List.map_nil]
  rfl

set_option maxRecDepth 65536 in
theorem bus_sa0_recv (d : Desc) (r t : Nat) (pub : List Fp) :
    rowTraffic Codec.table.interactions (dRow d r) t r pub B_SA0 false =
      List.replicate (if cv d a0g = 1 then 1 else 0) [cv d tau, cv d srcC, cv d apR, cv d bigR] := by
  simp only [rowTraffic, Codec.table, interactions, List.flatMap_cons, List.flatMap_nil,
    ZkFormal.NearV3.B_S0F, Sched.B_S0F, ZkFormal.NearV3.B_SPLEN, ZkFormal.NearV3.B_SPOST, ZkFormal.NearV3.B_VBYTES, Sched.B_SPOST, ZkFormal.Near.B_BYTES,
    ZkFormal.Near.B_DIGEST, Sched.B_SPLEN, Sched.B_SPAR, Sched.B_SDL, Sched.B_SPUBB, Sched.B_SOP,
    Sched.B_SFIN, Sched.B_SDG, Sched.B_SA0, Sched.B_SCMP]
  simp only [Nat.reduceEqDiff, Bool.false_eq_true, and_false, and_true, false_and, true_and,
    ite_false, ite_true, List.append_nil, List.nil_append, decide_true, decide_false, Bool.true_eq_false]
  simp only [Interaction.multNat, mult1, Interaction.msgVal, List.map_cons, List.map_nil]
  rfl

set_option maxRecDepth 65536 in
theorem sa0s_hdr (I : Inst) (p r t : Nat) (pub : List Fp) :
    rowTraffic Codec.table.interactions (dRow (.hdr I p) r) t r pub B_SA0 true = [] := by
  rw [bus_sa0_send]; cdc_bus

set_option maxRecDepth 65536 in
theorem sa0r_hdr (I : Inst) (p r t : Nat) (pub : List Fp) :
    rowTraffic Codec.table.interactions (dRow (.hdr I p) r) t r pub B_SA0 false = [] := by
  rw [bus_sa0_recv]; cdc_bus

set_option maxRecDepth 65536 in
theorem sa0s_hash (I : Inst) (dig hpre : List Nat) (j r t : Nat) (pub : List Fp) :
    rowTraffic Codec.table.interactions (dRow (.hash I dig hpre j) r) t r pub B_SA0 true = [] := by
  rw [bus_sa0_send]; cdc_bus

set_option maxRecDepth 65536 in
theorem sa0r_hash (I : Inst) (dig hpre : List Nat) (j r t : Nat) (pub : List Fp) :
    rowTraffic Codec.table.interactions (dRow (.hash I dig hpre j) r) t r pub B_SA0 false = [] := by
  rw [bus_sa0_recv]; cdc_bus

set_option maxRecDepth 65536 in
theorem sa0s_ash (I : Inst) (ash : List Nat) (j r t : Nat) (pub : List Fp) :
    rowTraffic Codec.table.interactions (dRow (.ash I ash j) r) t r pub B_SA0 true = [] := by
  rw [bus_sa0_send]; cdc_bus

set_option maxRecDepth 65536 in
theorem sa0r_ash (I : Inst) (ash : List Nat) (j r t : Nat) (pub : List Fp) :
    rowTraffic Codec.table.interactions (dRow (.ash I ash j) r) t r pub B_SA0 false = [] := by
  rw [bus_sa0_recv]; cdc_bus

set_option maxRecDepth 65536 in
theorem bus_sdl_send (d : Desc) (r t : Nat) (pub : List Fp) :
    rowTraffic Codec.table.interactions (dRow d r) t r pub B_SDL true =
      List.replicate (if cv d fS + cv d fR = 1 then 1 else 0) [cv d tau + 1, cv d klo, cv d khi, Fp.ofNat 8 * cv d fR + cv d g, cv d bpost] := by
  simp only [rowTraffic, Codec.table, interactions, List.flatMap_cons, List.flatMap_nil,
    ZkFormal.NearV3.B_S0F, Sched.B_S0F, ZkFormal.NearV3.B_SPLEN, ZkFormal.NearV3.B_SPOST, ZkFormal.NearV3.B_VBYTES, Sched.B_SPOST, ZkFormal.Near.B_BYTES,
    ZkFormal.Near.B_DIGEST, Sched.B_SPLEN, Sched.B_SPAR, Sched.B_SDL, Sched.B_SPUBB, Sched.B_SOP,
    Sched.B_SFIN, Sched.B_SDG, Sched.B_SA0, Sched.B_SCMP]
  simp only [Nat.reduceEqDiff, Bool.false_eq_true, and_false, and_true, false_and, true_and,
    ite_false, ite_true, List.append_nil, List.nil_append, decide_true, decide_false, Bool.true_eq_false]
  simp only [Interaction.multNat, mult1, Interaction.msgVal, List.map_cons, List.map_nil]
  simp only [oE, Expr.eval, Expr.evalWith]
  rfl

set_option maxRecDepth 65536 in
theorem bus_sdl_recv (d : Desc) (r t : Nat) (pub : List Fp) :
    rowTraffic Codec.table.interactions (dRow d r) t r pub B_SDL false =
      List.replicate (if cv d fS + cv d fR = 1 then 1 else 0) [cv d tau, cv d klo, cv d khi, Fp.ofNat 8 * cv d fR + cv d g, cv d bpost] := by
  simp only [rowTraffic, Codec.table, interactions, List.flatMap_cons, List.flatMap_nil,
    ZkFormal.NearV3.B_S0F, Sched.B_S0F, ZkFormal.NearV3.B_SPLEN, ZkFormal.NearV3.B_SPOST, ZkFormal.NearV3.B_VBYTES, Sched.B_SPOST, ZkFormal.Near.B_BYTES,
    ZkFormal.Near.B_DIGEST, Sched.B_SPLEN, Sched.B_SPAR, Sched.B_SDL, Sched.B_SPUBB, Sched.B_SOP,
    Sched.B_SFIN, Sched.B_SDG, Sched.B_SA0, Sched.B_SCMP]
  simp only [Nat.reduceEqDiff, Bool.false_eq_true, and_false, and_true, false_and, true_and,
    ite_false, ite_true, List.append_nil, List.nil_append, decide_true, decide_false, Bool.true_eq_false]
  simp only [Interaction.multNat, mult1, Interaction.msgVal, List.map_cons, List.map_nil]
  simp only [oE, Expr.eval, Expr.evalWith]
  rfl

set_option maxRecDepth 65536 in
theorem bus_spubb (d : Desc) (r t : Nat) (pub : List Fp) :
    rowTraffic Codec.table.interactions (dRow d r) t r pub B_SPUBB false =
      List.replicate (if cv d kA + cv d fwg = 1 then 1 else 0) [cv d tau, Fp.ofNat 2 * cv d kA + Fp.ofNat 4 * cv d fwg, cv d pm0, cv d pm1, cv d (fb 0), cv d (fb 1), cv d (fb 2)] := by
  simp only [rowTraffic, Codec.table, interactions, List.flatMap_cons, List.flatMap_nil,
    ZkFormal.NearV3.B_S0F, Sched.B_S0F, ZkFormal.NearV3.B_SPLEN, ZkFormal.NearV3.B_SPOST, ZkFormal.NearV3.B_VBYTES, Sched.B_SPOST, ZkFormal.Near.B_BYTES,
    ZkFormal.Near.B_DIGEST, Sched.B_SPLEN, Sched.B_SPAR, Sched.B_SDL, Sched.B_SPUBB, Sched.B_SOP,
    Sched.B_SFIN, Sched.B_SDG, Sched.B_SA0, Sched.B_SCMP]
  simp only [Nat.reduceEqDiff, Bool.false_eq_true, and_false, and_true, false_and, true_and,
    ite_false, ite_true, List.append_nil, List.nil_append, decide_true, decide_false, Bool.true_eq_false]
  simp only [Interaction.multNat, mult1, Interaction.msgVal, List.map_cons, List.map_nil]
  rfl

set_option maxRecDepth 65536 in
theorem bus_spar (d : Desc) (r t : Nat) (pub : List Fp) :
    rowTraffic Codec.table.interactions (dRow d r) t r pub B_SPAR false =
      List.replicate (if cv d kF = 1 then 1 else 0) [cv d tau, 0, cv d nn, cv d (reg 1), cv d (reg 2), cv d (reg 5), cv d (reg 6), cv d (reg 7), cv d (reg 8), cv d (reg 9), cv d (reg 10)] := by
  simp only [rowTraffic, Codec.table, interactions, List.flatMap_cons, List.flatMap_nil,
    ZkFormal.NearV3.B_S0F, Sched.B_S0F, ZkFormal.NearV3.B_SPLEN, ZkFormal.NearV3.B_SPOST, ZkFormal.NearV3.B_VBYTES, Sched.B_SPOST, ZkFormal.Near.B_BYTES,
    ZkFormal.Near.B_DIGEST, Sched.B_SPLEN, Sched.B_SPAR, Sched.B_SDL, Sched.B_SPUBB, Sched.B_SOP,
    Sched.B_SFIN, Sched.B_SDG, Sched.B_SA0, Sched.B_SCMP]
  simp only [Nat.reduceEqDiff, Bool.false_eq_true, and_false, and_true, false_and, true_and,
    ite_false, ite_true, List.append_nil, List.nil_append, decide_true, decide_false, Bool.true_eq_false]
  simp only [Interaction.multNat, mult1, Interaction.msgVal, List.map_cons, List.map_nil]
  rfl

set_option maxRecDepth 65536 in
theorem bus_sop (d : Desc) (r t : Nat) (pub : List Fp) :
    rowTraffic Codec.table.interactions (dRow d r) t r pub B_SOP true =
      List.replicate (if cv d rend = 1 then 1 else 0) [Fp.ofNat 16384 * cv d tau + cv d kidx, 0, 0, cv d al, cv d a2, cv d g2, 0, 1] := by
  simp only [rowTraffic, Codec.table, interactions, List.flatMap_cons, List.flatMap_nil,
    ZkFormal.NearV3.B_S0F, Sched.B_S0F, ZkFormal.NearV3.B_SPLEN, ZkFormal.NearV3.B_SPOST, ZkFormal.NearV3.B_VBYTES, Sched.B_SPOST, ZkFormal.Near.B_BYTES,
    ZkFormal.Near.B_DIGEST, Sched.B_SPLEN, Sched.B_SPAR, Sched.B_SDL, Sched.B_SPUBB, Sched.B_SOP,
    Sched.B_SFIN, Sched.B_SDG, Sched.B_SA0, Sched.B_SCMP]
  simp only [Nat.reduceEqDiff, Bool.false_eq_true, and_false, and_true, false_and, true_and,
    ite_false, ite_true, List.append_nil, List.nil_append, decide_true, decide_false, Bool.true_eq_false]
  simp only [Interaction.multNat, mult1, Interaction.msgVal, List.map_cons, List.map_nil]
  rfl

set_option maxRecDepth 65536 in
theorem bus_sfin (d : Desc) (r t : Nat) (pub : List Fp) :
    rowTraffic Codec.table.interactions (dRow d r) t r pub B_SFIN false =
      List.replicate (if cv d rend = 1 then 1 else 0) [Fp.ofNat 16384 * cv d tau + cv d kidx, cv d afin, cv d gfin] := by
  simp only [rowTraffic, Codec.table, interactions, List.flatMap_cons, List.flatMap_nil,
    ZkFormal.NearV3.B_S0F, Sched.B_S0F, ZkFormal.NearV3.B_SPLEN, ZkFormal.NearV3.B_SPOST, ZkFormal.NearV3.B_VBYTES, Sched.B_SPOST, ZkFormal.Near.B_BYTES,
    ZkFormal.Near.B_DIGEST, Sched.B_SPLEN, Sched.B_SPAR, Sched.B_SDL, Sched.B_SPUBB, Sched.B_SOP,
    Sched.B_SFIN, Sched.B_SDG, Sched.B_SA0, Sched.B_SCMP]
  simp only [Nat.reduceEqDiff, Bool.false_eq_true, and_false, and_true, false_and, true_and,
    ite_false, ite_true, List.append_nil, List.nil_append, decide_true, decide_false, Bool.true_eq_false]
  simp only [Interaction.multNat, mult1, Interaction.msgVal, List.map_cons, List.map_nil]
  rfl

set_option maxRecDepth 65536 in
theorem bus_sdg (d : Desc) (r t : Nat) (pub : List Fp) :
    rowTraffic Codec.table.interactions (dRow d r) t r pub B_SDG false =
      List.replicate (if cv d rs = 1 then 1 else 0) [cv d tau, cv d kidx, cv d al, cv d gb, cv d srcC, cv d hasC, cv d useC] := by
  simp only [rowTraffic, Codec.table, interactions, List.flatMap_cons, List.flatMap_nil,
    ZkFormal.NearV3.B_S0F, Sched.B_S0F, ZkFormal.NearV3.B_SPLEN, ZkFormal.NearV3.B_SPOST, ZkFormal.NearV3.B_VBYTES, Sched.B_SPOST, ZkFormal.Near.B_BYTES,
    ZkFormal.Near.B_DIGEST, Sched.B_SPLEN, Sched.B_SPAR, Sched.B_SDL, Sched.B_SPUBB, Sched.B_SOP,
    Sched.B_SFIN, Sched.B_SDG, Sched.B_SA0, Sched.B_SCMP]
  simp only [Nat.reduceEqDiff, Bool.false_eq_true, and_false, and_true, false_and, true_and,
    ite_false, ite_true, List.append_nil, List.nil_append, decide_true, decide_false, Bool.true_eq_false]
  simp only [Interaction.multNat, mult1, Interaction.msgVal, List.map_cons, List.map_nil]
  rfl

set_option maxRecDepth 65536 in
theorem sa0_send_hdr (I : Inst) (p r t : Nat) (pub : List Fp) :
    rowTraffic Codec.table.interactions (dRow (.hdr I p) r) t r pub B_SA0 true = [] := by
  rw [bus_sa0_send]; cdc_bus

set_option maxRecDepth 65536 in
theorem sa0_send_hash (I : Inst) (dig hpre : List Nat) (j r t : Nat) (pub : List Fp) :
    rowTraffic Codec.table.interactions (dRow (.hash I dig hpre j) r) t r pub B_SA0 true = [] := by
  rw [bus_sa0_send]; cdc_bus

set_option maxRecDepth 65536 in
theorem sa0_send_ash (I : Inst) (ash : List Nat) (j r t : Nat) (pub : List Fp) :
    rowTraffic Codec.table.interactions (dRow (.ash I ash j) r) t r pub B_SA0 true = [] := by
  rw [bus_sa0_send]; cdc_bus

set_option maxRecDepth 65536 in
theorem sa0_recv_hdr (I : Inst) (p r t : Nat) (pub : List Fp) :
    rowTraffic Codec.table.interactions (dRow (.hdr I p) r) t r pub B_SA0 false = [] := by
  rw [bus_sa0_recv]; cdc_bus

set_option maxRecDepth 65536 in
theorem sa0_recv_hash (I : Inst) (dig hpre : List Nat) (j r t : Nat) (pub : List Fp) :
    rowTraffic Codec.table.interactions (dRow (.hash I dig hpre j) r) t r pub B_SA0 false = [] := by
  rw [bus_sa0_recv]; cdc_bus

set_option maxRecDepth 65536 in
theorem sa0_recv_ash (I : Inst) (ash : List Nat) (j r t : Nat) (pub : List Fp) :
    rowTraffic Codec.table.interactions (dRow (.ash I ash j) r) t r pub B_SA0 false = [] := by
  rw [bus_sa0_recv]; cdc_bus

set_option maxRecDepth 65536 in
theorem sdl_send_hdr (I : Inst) (p r t : Nat) (pub : List Fp) :
    rowTraffic Codec.table.interactions (dRow (.hdr I p) r) t r pub B_SDL true = [] := by
  rw [bus_sdl_send]; cdc_bus

set_option maxRecDepth 65536 in
theorem sdl_send_hash (I : Inst) (dig hpre : List Nat) (j r t : Nat) (pub : List Fp) :
    rowTraffic Codec.table.interactions (dRow (.hash I dig hpre j) r) t r pub B_SDL true = [] := by
  rw [bus_sdl_send]; cdc_bus

set_option maxRecDepth 65536 in
theorem sdl_send_ash (I : Inst) (ash : List Nat) (j r t : Nat) (pub : List Fp) :
    rowTraffic Codec.table.interactions (dRow (.ash I ash j) r) t r pub B_SDL true = [] := by
  rw [bus_sdl_send]; cdc_bus

set_option maxRecDepth 65536 in
theorem sdl_recv_hdr (I : Inst) (p r t : Nat) (pub : List Fp) :
    rowTraffic Codec.table.interactions (dRow (.hdr I p) r) t r pub B_SDL false = [] := by
  rw [bus_sdl_recv]; cdc_bus

set_option maxRecDepth 65536 in
theorem sdl_recv_hash (I : Inst) (dig hpre : List Nat) (j r t : Nat) (pub : List Fp) :
    rowTraffic Codec.table.interactions (dRow (.hash I dig hpre j) r) t r pub B_SDL false = [] := by
  rw [bus_sdl_recv]; cdc_bus

set_option maxRecDepth 65536 in
theorem sdl_recv_ash (I : Inst) (ash : List Nat) (j r t : Nat) (pub : List Fp) :
    rowTraffic Codec.table.interactions (dRow (.ash I ash j) r) t r pub B_SDL false = [] := by
  rw [bus_sdl_recv]; cdc_bus

set_option maxRecDepth 65536 in
theorem spubb_hdr (I : Inst) (p r t : Nat) (pub : List Fp) :
    rowTraffic Codec.table.interactions (dRow (.hdr I p) r) t r pub B_SPUBB false = [] := by
  rw [bus_spubb]; cdc_bus

set_option maxRecDepth 65536 in
theorem spubb_hash (I : Inst) (dig hpre : List Nat) (j r t : Nat) (pub : List Fp) :
    rowTraffic Codec.table.interactions (dRow (.hash I dig hpre j) r) t r pub B_SPUBB false = [] := by
  rw [bus_spubb]; cdc_bus

set_option maxRecDepth 65536 in
theorem spar_hash (I : Inst) (dig hpre : List Nat) (j r t : Nat) (pub : List Fp) :
    rowTraffic Codec.table.interactions (dRow (.hash I dig hpre j) r) t r pub B_SPAR false = [] := by
  rw [bus_spar]; cdc_bus

set_option maxRecDepth 65536 in
theorem spar_ash (I : Inst) (ash : List Nat) (j r t : Nat) (pub : List Fp) :
    rowTraffic Codec.table.interactions (dRow (.ash I ash j) r) t r pub B_SPAR false = [] := by
  rw [bus_spar]; cdc_bus

set_option maxRecDepth 65536 in
theorem sop_hdr (I : Inst) (p r t : Nat) (pub : List Fp) :
    rowTraffic Codec.table.interactions (dRow (.hdr I p) r) t r pub B_SOP true = [] := by
  rw [bus_sop]; cdc_bus

set_option maxRecDepth 65536 in
theorem sop_hash (I : Inst) (dig hpre : List Nat) (j r t : Nat) (pub : List Fp) :
    rowTraffic Codec.table.interactions (dRow (.hash I dig hpre j) r) t r pub B_SOP true = [] := by
  rw [bus_sop]; cdc_bus

set_option maxRecDepth 65536 in
theorem sop_ash (I : Inst) (ash : List Nat) (j r t : Nat) (pub : List Fp) :
    rowTraffic Codec.table.interactions (dRow (.ash I ash j) r) t r pub B_SOP true = [] := by
  rw [bus_sop]; cdc_bus

set_option maxRecDepth 65536 in
theorem sfin_hdr (I : Inst) (p r t : Nat) (pub : List Fp) :
    rowTraffic Codec.table.interactions (dRow (.hdr I p) r) t r pub B_SFIN false = [] := by
  rw [bus_sfin]; cdc_bus

set_option maxRecDepth 65536 in
theorem sfin_hash (I : Inst) (dig hpre : List Nat) (j r t : Nat) (pub : List Fp) :
    rowTraffic Codec.table.interactions (dRow (.hash I dig hpre j) r) t r pub B_SFIN false = [] := by
  rw [bus_sfin]; cdc_bus

set_option maxRecDepth 65536 in
theorem sfin_ash (I : Inst) (ash : List Nat) (j r t : Nat) (pub : List Fp) :
    rowTraffic Codec.table.interactions (dRow (.ash I ash j) r) t r pub B_SFIN false = [] := by
  rw [bus_sfin]; cdc_bus

set_option maxRecDepth 65536 in
theorem sdg_hdr (I : Inst) (p r t : Nat) (pub : List Fp) :
    rowTraffic Codec.table.interactions (dRow (.hdr I p) r) t r pub B_SDG false = [] := by
  rw [bus_sdg]; cdc_bus

set_option maxRecDepth 65536 in
theorem sdg_hash (I : Inst) (dig hpre : List Nat) (j r t : Nat) (pub : List Fp) :
    rowTraffic Codec.table.interactions (dRow (.hash I dig hpre j) r) t r pub B_SDG false = [] := by
  rw [bus_sdg]; cdc_bus

set_option maxRecDepth 65536 in
theorem sdg_ash (I : Inst) (ash : List Nat) (j r t : Nat) (pub : List Fp) :
    rowTraffic Codec.table.interactions (dRow (.ash I ash j) r) t r pub B_SDG false = [] := by
  rw [bus_sdg]; cdc_bus

set_option maxRecDepth 65536 in
theorem sa0_send_rec (I : Inst) (R : Rec) (f gg bpo bpr apv apostv bigv r t : Nat) (pub : List Fp) :
    rowTraffic Codec.table.interactions (dRow (.record I R f gg bpo bpr apv apostv bigv) r) t r pub B_SA0 true =
      if f = 2 ∧ gg = 7 ∧ R.useC = true then
        [[Fp.ofNat I.tv, Fp.ofNat R.kk, Fp.ofNat apv, Fp.ofNat (if bigv = 1 ∨ bpr ≠ 0 then 1 else 0)]]
      else [] := by
  rw [bus_sa0_send]
  by_cases h : f = 2 ∧ gg = 7
  · obtain ⟨rfl, rfl⟩ := h
    cases hu : R.useC <;> cdc_bus <;> simp [hu, b2n, o1, z1]
  · cdc_bus
    simp [h, z1] <;> intro h1 h2 <;> exact absurd ⟨h1, h2⟩ h

set_option maxRecDepth 65536 in
theorem sa0_recv_rec (I : Inst) (R : Rec) (f gg bpo bpr apv apostv bigv r t : Nat) (pub : List Fp) :
    rowTraffic Codec.table.interactions (dRow (.record I R f gg bpo bpr apv apostv bigv) r) t r pub B_SA0 false =
      if f = 2 ∧ gg = 2 ∧ R.hasC = true then
        [[Fp.ofNat I.tv, Fp.ofNat R.srcS, Fp.ofNat (apRv R), Fp.ofNat (bigRv R)]]
      else [] := by
  rw [bus_sa0_recv]
  by_cases h : f = 2 ∧ gg = 2
  · obtain ⟨rfl, rfl⟩ := h
    cases hu : R.hasC <;> cdc_bus <;> simp [hu, b2n, o1, z1]
  · cdc_bus
    simp [h, z1] <;> intro h1 h2 <;> exact absurd ⟨h1, h2⟩ h

theorem ofNat_succ1 (v : Nat) : Fp.ofNat v + 1 = Fp.ofNat (v + 1) := by
  rw [← ZkFormal.Near.ofNat_add']; rfl

set_option maxRecDepth 65536 in
theorem sdl_send_rec (I : Inst) (R : Rec) (f gg bpo bpr apv apostv bigv r t : Nat) (pub : List Fp) :
    rowTraffic Codec.table.interactions (dRow (.record I R f gg bpo bpr apv apostv bigv) r) t r pub B_SDL true =
      if f < 2 then
        [[Fp.ofNat (I.tv + 1), Fp.ofNat (R.kk % 256), Fp.ofNat (R.kk / 256), Fp.ofNat (8 * f + gg), Fp.ofNat bpo]]
      else [] := by
  rw [bus_sdl_send]
  rcases (show f = 0 ∨ f = 1 ∨ 2 ≤ f by omega) with rfl | rfl | h
  · cdc_bus; simp [ofNat_succ1]
  · cdc_bus; simp [ofNat_succ1, o1]
    rw [show (1:Fp) = Fp.ofNat 1 from rfl, ofNat_mul', ofNat_add']
  · cdc_bus
    simp [show f ≠ 0 by omega, show f ≠ 1 by omega, show ¬ f < 2 by omega, z1]

set_option maxRecDepth 65536 in
theorem sdl_recv_rec (I : Inst) (R : Rec) (f gg bpo bpr apv apostv bigv r t : Nat) (pub : List Fp) :
    rowTraffic Codec.table.interactions (dRow (.record I R f gg bpo bpr apv apostv bigv) r) t r pub B_SDL false =
      if f < 2 then
        [[Fp.ofNat I.tv, Fp.ofNat (R.kk % 256), Fp.ofNat (R.kk / 256), Fp.ofNat (8 * f + gg), Fp.ofNat bpo]]
      else [] := by
  rw [bus_sdl_recv]
  rcases (show f = 0 ∨ f = 1 ∨ 2 ≤ f by omega) with rfl | rfl | h
  · cdc_bus; simp
  · cdc_bus; simp [o1]
    rw [show (1:Fp) = Fp.ofNat 1 from rfl, ofNat_mul', ofNat_add']
  · cdc_bus
    simp [show f ≠ 0 by omega, show f ≠ 1 by omega, show ¬ f < 2 by omega, z1]

set_option maxRecDepth 65536 in
theorem spubb_ash (I : Inst) (ash : List Nat) (j r t : Nat) (pub : List Fp) :
    rowTraffic Codec.table.interactions (dRow (.ash I ash j) r) t r pub B_SPUBB false =
      [[Fp.ofNat I.tv, Fp.ofNat 2, Fp.ofNat j, Fp.ofNat (ash.getD j 0), 0, 0, 0]] := by
  rw [bus_spubb]; cdc_bus
  rw [show (Fp.ofNat 2 : Fp) * 1 + Fp.ofNat (4 * 0) = Fp.ofNat 2 by decide]; rfl

set_option maxRecDepth 65536 in
theorem spubb_rec (I : Inst) (R : Rec) (f gg bpo bpr apv apostv bigv r t : Nat) (pub : List Fp) :
    rowTraffic Codec.table.interactions (dRow (.record I R f gg bpo bpr apv apostv bigv) r) t r pub B_SPUBB false =
      if f = 2 ∧ gg = 7 ∧ I.tv = 0 then
        [[0, Fp.ofNat 4, Fp.ofNat (R.kk % 256), Fp.ofNat (R.kk / 256), Fp.ofNat (R.ft % 256),
          Fp.ofNat (R.ft / 256 % 256), Fp.ofNat (R.ft / 65536 % 256)]]
      else [] := by
  rw [bus_spubb]
  by_cases h : f = 2 ∧ gg = 7
  · obtain ⟨rfl, rfl⟩ := h
    by_cases ht : I.tv = 0
    · cdc_bus
      simp [zt0, ht, o1]; rfl
    · cdc_bus
      simp [zt0, ht, z1]
  · cdc_bus
    simp [h, z1] <;> intro h1 h2 <;> exact absurd ⟨h1, h2⟩ h

set_option maxRecDepth 65536 in
theorem spar_hdr (I : Inst) (p r t : Nat) (pub : List Fp) :
    rowTraffic Codec.table.interactions (dRow (.hdr I p) r) t r pub B_SPAR false =
      if p = 0 then
        [[Fp.ofNat I.tv, 0, Fp.ofNat I.n, Fp.ofNat (I.N % 256), Fp.ofNat (I.N / 256 % 256),
          Fp.ofNat (I.base % 256), Fp.ofNat (I.base / 256 % 256), Fp.ofNat (I.base / 65536 % 256),
          Fp.ofNat (I.fair % 256), Fp.ofNat (I.fair / 256 % 256), Fp.ofNat (I.fair / 65536 % 256)]]
      else [] := by
  rw [bus_spar]
  by_cases hp : p = 0
  · subst hp; cdc_bus
    simp [params, hdrBytes, bytesLE, List.range_succ]
  · cdc_bus; simp [hp, z1]

set_option maxRecDepth 65536 in
theorem spar_rec (I : Inst) (R : Rec) (f gg bpo bpr apv apostv bigv r t : Nat) (pub : List Fp) :
    rowTraffic Codec.table.interactions (dRow (.record I R f gg bpo bpr apv apostv bigv) r) t r pub B_SPAR false = [] := by
  rw [bus_spar]; cdc_bus

set_option maxRecDepth 65536 in
theorem sop_rec (I : Inst) (R : Rec) (f gg bpo bpr apv apostv bigv r t : Nat) (pub : List Fp) :
    rowTraffic Codec.table.interactions (dRow (.record I R f gg bpo bpr apv apostv bigv) r) t r pub B_SOP true =
      if f = 2 ∧ gg = 7 then
        [[Fp.ofNat (16384 * I.tv + R.kk), 0, 0, Fp.ofNat (b2n R.al), Fp.ofNat (a1v I R - b2n R.al * I.base),
          Fp.ofNat (b2n R.al * I.base), 0, 1]]
      else [] := by
  rw [bus_sop]
  by_cases h : f = 2 ∧ gg = 7
  · obtain ⟨rfl, rfl⟩ := h
    cdc_bus
  · cdc_bus
    simp [h, z1]

set_option maxRecDepth 65536 in
theorem sfin_rec (I : Inst) (R : Rec) (f gg bpo bpr apv apostv bigv r t : Nat) (pub : List Fp) :
    rowTraffic Codec.table.interactions (dRow (.record I R f gg bpo bpr apv apostv bigv) r) t r pub B_SFIN false =
      if f = 2 ∧ gg = 7 then [[Fp.ofNat (16384 * I.tv + R.kk), Fp.ofNat R.afin, Fp.ofNat R.gfin]] else [] := by
  rw [bus_sfin]
  by_cases h : f = 2 ∧ gg = 7
  · obtain ⟨rfl, rfl⟩ := h
    cdc_bus
  · cdc_bus
    simp [h, z1]

set_option maxRecDepth 65536 in
theorem sdg_rec (I : Inst) (R : Rec) (f gg bpo bpr apv apostv bigv r t : Nat) (pub : List Fp) :
    rowTraffic Codec.table.interactions (dRow (.record I R f gg bpo bpr apv apostv bigv) r) t r pub B_SDG false =
      if f = 0 ∧ gg = 0 then
        [[Fp.ofNat I.tv, Fp.ofNat R.kk, Fp.ofNat (b2n R.al), Fp.ofNat R.gb, Fp.ofNat R.srcS,
          Fp.ofNat (b2n R.hasC), Fp.ofNat (b2n R.useC)]]
      else [] := by
  rw [bus_sdg]
  by_cases h : f = 0 ∧ gg = 0
  · obtain ⟨rfl, rfl⟩ := h
    cdc_bus
  · cdc_bus
    simp [h, z1]

end ZkFormal.NearV3.Render.Cdc
