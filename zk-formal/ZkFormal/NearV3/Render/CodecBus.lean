import ZkFormal.NearV3.Render.CodecTraffic
import ZkFormal.NearV3.Render.CodecRowMod

namespace ZkFormal.NearV3.Render.Cdc
open ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen
open ZkFormal.Near
open ZkFormal.NearV3.Candidates.SchedSetAll ZkFormal.NearV3.Sched.Codec ZkFormal.Chacha.Table.E

/-- One-term multiplicity. -/
theorem mult1 (e : Expr) (tr : Trace Fp) (t r : Nat) (pub : List Fp) :
    Interaction.multNat.go tr t r pub [e] 0 = if e.eval tr t r pub = 1 then 1 else 0 := by
  simp [Interaction.multNat.go]

def cv (d : Desc) (col : Nat) : Fp := Fp.ofNat (lookup d.asg col 0)

set_option maxRecDepth 65536 in
theorem bus_bytes (d : Desc) (r t : Nat) (pub : List Fp) :
    rowTraffic Codec.table.interactions (dRow d r) t r pub ZkFormal.Near.B_BYTES true =
      List.replicate (if cv d kZ + cv d kA = 1 then 1 else 0)
        [Fp.ofNat K_SCH + Fp.ofNat 16 * cv d tau, cv d sj, cv d bsha] := by
  simp only [rowTraffic, Codec.table, interactions, List.flatMap_cons, List.flatMap_nil,
    ZkFormal.NearV3.B_S0F, Sched.B_S0F, ZkFormal.NearV3.B_SPLEN, ZkFormal.NearV3.B_SPOST, ZkFormal.NearV3.B_VBYTES, Sched.B_SPOST, ZkFormal.Near.B_BYTES,
    ZkFormal.Near.B_DIGEST, Sched.B_SPLEN, Sched.B_SPAR, Sched.B_SDL, Sched.B_SPUBB, Sched.B_SOP,
    Sched.B_SFIN, Sched.B_SDG, Sched.B_SA0, Sched.B_SCMP]
  simp only [Nat.reduceEqDiff, Bool.false_eq_true, and_false, and_true, false_and, true_and,
    ite_false, ite_true, List.append_nil, List.nil_append, decide_true, decide_false]
  simp only [Interaction.multNat, mult1, Interaction.msgVal, List.map_cons, List.map_nil, shaId]
  rfl

set_option maxRecDepth 65536 in
theorem bus_digest (d : Desc) (r t : Nat) (pub : List Fp) :
    rowTraffic Codec.table.interactions (dRow d r) t r pub ZkFormal.Near.B_DIGEST false =
      List.replicate (if cv d dgg = 1 then 1 else 0)
        ([Fp.ofNat K_SCH + Fp.ofNat 16 * cv d tau, Fp.ofNat 64] ++ (List.range 32).map fun i => cv d (reg i)) := by
  simp only [rowTraffic, Codec.table, interactions, List.flatMap_cons, List.flatMap_nil,
    ZkFormal.NearV3.B_S0F, Sched.B_S0F, ZkFormal.NearV3.B_SPLEN, ZkFormal.NearV3.B_SPOST, ZkFormal.NearV3.B_VBYTES, Sched.B_SPOST, ZkFormal.Near.B_BYTES,
    ZkFormal.Near.B_DIGEST, Sched.B_SPLEN, Sched.B_SPAR, Sched.B_SDL, Sched.B_SPUBB, Sched.B_SOP,
    Sched.B_SFIN, Sched.B_SDG, Sched.B_SA0, Sched.B_SCMP]
  simp only [Nat.reduceEqDiff, Bool.false_eq_true, and_false, and_true, false_and, true_and,
    ite_false, ite_true, List.append_nil, List.nil_append]
  simp only [Interaction.multNat, mult1, Interaction.msgVal, List.map_cons, List.map_nil, shaId,
    List.map_append, List.map_map]
  rfl

set_option maxRecDepth 65536 in
theorem bus_s0f (d : Desc) (r t : Nat) (pub : List Fp) :
    rowTraffic Codec.table.interactions (dRow d r) t r pub B_S0F false =
      List.replicate (if cv d kF = 1 then 1 else 0) [cv d tau, cv d pres, cv d vid] := by
  simp only [rowTraffic, Codec.table, interactions, List.flatMap_cons, List.flatMap_nil,
    ZkFormal.NearV3.B_S0F, Sched.B_S0F, ZkFormal.NearV3.B_SPLEN, ZkFormal.NearV3.B_SPOST, ZkFormal.NearV3.B_VBYTES, Sched.B_SPOST, ZkFormal.Near.B_BYTES,
    ZkFormal.Near.B_DIGEST, Sched.B_SPLEN, Sched.B_SPAR, Sched.B_SDL, Sched.B_SPUBB, Sched.B_SOP,
    Sched.B_SFIN, Sched.B_SDG, Sched.B_SA0, Sched.B_SCMP]
  simp only [Nat.reduceEqDiff, Bool.false_eq_true, and_false, and_true, false_and, true_and,
    ite_false, ite_true, List.append_nil, List.nil_append]
  simp only [Interaction.multNat, mult1, Interaction.msgVal, List.map_cons, List.map_nil]
  rfl

set_option maxRecDepth 65536 in
theorem bus_splen (d : Desc) (r t : Nat) (pub : List Fp) :
    rowTraffic Codec.table.interactions (dRow d r) t r pub B_SPLEN true =
      List.replicate (if cv d kF = 1 then 1 else 0) [cv d tau, Fp.ofNat 37 + Fp.ofNat 24 * cv d NN] := by
  simp only [rowTraffic, Codec.table, interactions, List.flatMap_cons, List.flatMap_nil,
    ZkFormal.NearV3.B_S0F, Sched.B_S0F, ZkFormal.NearV3.B_SPLEN, ZkFormal.NearV3.B_SPOST, ZkFormal.NearV3.B_VBYTES, Sched.B_SPOST, ZkFormal.Near.B_BYTES,
    ZkFormal.Near.B_DIGEST, Sched.B_SPLEN, Sched.B_SPAR, Sched.B_SDL, Sched.B_SPUBB, Sched.B_SOP,
    Sched.B_SFIN, Sched.B_SDG, Sched.B_SA0, Sched.B_SCMP]
  simp only [Nat.reduceEqDiff, Bool.false_eq_true, and_false, and_true, false_and, true_and,
    ite_false, ite_true, List.append_nil, List.nil_append]
  simp only [Interaction.multNat, mult1, Interaction.msgVal, List.map_cons, List.map_nil]
  rfl

set_option maxRecDepth 65536 in
theorem bus_spost (d : Desc) (r t : Nat) (pub : List Fp) :
    rowTraffic Codec.table.interactions (dRow d r) t r pub B_SPOST true =
      List.replicate (if cv d kH + (cv d kR + cv d kZ) = 1 then 1 else 0) [cv d tau, cv d pos, cv d bpost] := by
  simp only [rowTraffic, Codec.table, interactions, List.flatMap_cons, List.flatMap_nil,
    ZkFormal.NearV3.B_S0F, Sched.B_S0F, ZkFormal.NearV3.B_SPLEN, ZkFormal.NearV3.B_SPOST, ZkFormal.NearV3.B_VBYTES, Sched.B_SPOST, ZkFormal.Near.B_BYTES,
    ZkFormal.Near.B_DIGEST, Sched.B_SPLEN, Sched.B_SPAR, Sched.B_SDL, Sched.B_SPUBB, Sched.B_SOP,
    Sched.B_SFIN, Sched.B_SDG, Sched.B_SA0, Sched.B_SCMP]
  simp only [Nat.reduceEqDiff, Bool.false_eq_true, and_false, and_true, false_and, true_and,
    ite_false, ite_true, List.append_nil, List.nil_append]
  simp only [Interaction.multNat, mult1, Interaction.msgVal, List.map_cons, List.map_nil, encG]
  rfl

/-! ## Per-kind values -/

theorem f01 : (Fp.ofNat 0 : Fp) + Fp.ofNat 0 = 0 := by decide
theorem z1 : ¬ ((Fp.ofNat 0 : Fp) = 1) := by decide
theorem o1 : (Fp.ofNat 1 : Fp) = 1 := rfl
theorem f10 : (Fp.ofNat 1 : Fp) + Fp.ofNat 0 = 1 := by decide
theorem f01' : (Fp.ofNat 0 : Fp) + Fp.ofNat 1 = 1 := by decide
theorem f00 : (Fp.ofNat 0 : Fp) + (Fp.ofNat 0 + Fp.ofNat 0) = 0 := by decide
theorem z0 : (0 : Fp) ≠ 1 := by decide
theorem a10 : (1 : Fp) + Fp.ofNat 0 = 1 := by decide
theorem a01 : Fp.ofNat 0 + (1 : Fp) = 1 := by decide
theorem a100 : (1 : Fp) + (Fp.ofNat 0 + Fp.ofNat 0) = 1 := by decide
theorem a010 : Fp.ofNat 0 + ((1 : Fp) + Fp.ofNat 0) = 1 := by decide
theorem a001 : Fp.ofNat 0 + (Fp.ofNat 0 + (1 : Fp)) = 1 := by decide

macro "cdc_bus" : tactic => `(tactic| (
  simp only [cv, Desc.asg]
  cdc_cell
  try simp only [f01, f10, f01', f00, z1, o1, z0, ite_true, ite_false, List.replicate_zero,
    List.replicate_one, ofNat_add', ofNat_mul', K_SCH]
  try simp only [Nat.add_zero, z1, a10, a01, a100, a010, a001, f00, ite_true, ite_false,
    List.replicate_zero, List.replicate_one]))

set_option maxRecDepth 65536 in
theorem bytes_hdr (I : Inst) (p r t : Nat) (pub : List Fp) :
    rowTraffic Codec.table.interactions (dRow (.hdr I p) r) t r pub ZkFormal.Near.B_BYTES true = [] := by
  rw [bus_bytes]; cdc_bus

set_option maxRecDepth 65536 in
theorem bytes_rec (I : Inst) (R : Rec) (f gg bpo bpr apv apostv bigv r t : Nat) (pub : List Fp) :
    rowTraffic Codec.table.interactions (dRow (.record I R f gg bpo bpr apv apostv bigv) r) t r pub
      ZkFormal.Near.B_BYTES true = [] := by
  rw [bus_bytes]; cdc_bus

set_option maxRecDepth 65536 in
theorem bytes_hash (I : Inst) (dig hpre : List Nat) (j r t : Nat) (pub : List Fp) :
    rowTraffic Codec.table.interactions (dRow (.hash I dig hpre j) r) t r pub ZkFormal.Near.B_BYTES true =
      [[Fp.ofNat (11 + 16 * I.tv), Fp.ofNat j, Fp.ofNat (if I.pres then hpre.getD j 0 else 0)]] := by
  rw [bus_bytes]; cdc_bus

set_option maxRecDepth 65536 in
theorem bytes_ash (I : Inst) (ash : List Nat) (j r t : Nat) (pub : List Fp) :
    rowTraffic Codec.table.interactions (dRow (.ash I ash j) r) t r pub ZkFormal.Near.B_BYTES true =
      [[Fp.ofNat (11 + 16 * I.tv), Fp.ofNat (32 + j), Fp.ofNat (ash.getD j 0)]] := by
  rw [bus_bytes]; cdc_bus

set_option maxRecDepth 65536 in
theorem digest_hdr (I : Inst) (p r t : Nat) (pub : List Fp) :
    rowTraffic Codec.table.interactions (dRow (.hdr I p) r) t r pub ZkFormal.Near.B_DIGEST false =
      [] := by
  rw [bus_digest]; cdc_bus

set_option maxRecDepth 65536 in
theorem digest_rec (I : Inst) (R : Rec) (f gg bpo bpr apv apostv bigv r t : Nat) (pub : List Fp) :
    rowTraffic Codec.table.interactions (dRow (.record I R f gg bpo bpr apv apostv bigv) r) t r pub ZkFormal.Near.B_DIGEST false =
      [] := by
  rw [bus_digest]; cdc_bus

set_option maxRecDepth 65536 in
theorem digest_ash (I : Inst) (ash : List Nat) (j r t : Nat) (pub : List Fp) :
    rowTraffic Codec.table.interactions (dRow (.ash I ash j) r) t r pub ZkFormal.Near.B_DIGEST false =
      [] := by
  rw [bus_digest]; cdc_bus

set_option maxRecDepth 65536 in
theorem digest_hash (I : Inst) (dig hpre : List Nat) (j r t : Nat) (pub : List Fp) :
    rowTraffic Codec.table.interactions (dRow (.hash I dig hpre j) r) t r pub ZkFormal.Near.B_DIGEST false =
      if j = 0 then [[Fp.ofNat (11 + 16 * I.tv), Fp.ofNat 64] ++ (List.range 32).map fun i => Fp.ofNat (dig.getD i 0)] else [] := by
  rw [bus_digest]; cdc_bus
  by_cases hj : j = 0
  · subst hj; simp [o1]
  · simp [hj, z1]

set_option maxRecDepth 65536 in
theorem s0f_rec (I : Inst) (R : Rec) (f gg bpo bpr apv apostv bigv r t : Nat) (pub : List Fp) :
    rowTraffic Codec.table.interactions (dRow (.record I R f gg bpo bpr apv apostv bigv) r) t r pub B_S0F false =
      [] := by
  rw [bus_s0f]; cdc_bus

set_option maxRecDepth 65536 in
theorem s0f_hash (I : Inst) (dig hpre : List Nat) (j r t : Nat) (pub : List Fp) :
    rowTraffic Codec.table.interactions (dRow (.hash I dig hpre j) r) t r pub B_S0F false =
      [] := by
  rw [bus_s0f]; cdc_bus

set_option maxRecDepth 65536 in
theorem s0f_ash (I : Inst) (ash : List Nat) (j r t : Nat) (pub : List Fp) :
    rowTraffic Codec.table.interactions (dRow (.ash I ash j) r) t r pub B_S0F false =
      [] := by
  rw [bus_s0f]; cdc_bus

set_option maxRecDepth 65536 in
theorem s0f_hdr (I : Inst) (p r t : Nat) (pub : List Fp) :
    rowTraffic Codec.table.interactions (dRow (.hdr I p) r) t r pub B_S0F false =
      if p = 0 then [[Fp.ofNat I.tv, Fp.ofNat (b2n I.pres), Fp.ofNat I.vid]] else [] := by
  rw [bus_s0f]; cdc_bus
  by_cases hp : p = 0 <;> simp [hp, o1, z1]

set_option maxRecDepth 65536 in
theorem splen_rec (I : Inst) (R : Rec) (f gg bpo bpr apv apostv bigv r t : Nat) (pub : List Fp) :
    rowTraffic Codec.table.interactions (dRow (.record I R f gg bpo bpr apv apostv bigv) r) t r pub B_SPLEN true =
      [] := by
  rw [bus_splen]; cdc_bus

set_option maxRecDepth 65536 in
theorem splen_hash (I : Inst) (dig hpre : List Nat) (j r t : Nat) (pub : List Fp) :
    rowTraffic Codec.table.interactions (dRow (.hash I dig hpre j) r) t r pub B_SPLEN true =
      [] := by
  rw [bus_splen]; cdc_bus

set_option maxRecDepth 65536 in
theorem splen_ash (I : Inst) (ash : List Nat) (j r t : Nat) (pub : List Fp) :
    rowTraffic Codec.table.interactions (dRow (.ash I ash j) r) t r pub B_SPLEN true =
      [] := by
  rw [bus_splen]; cdc_bus

set_option maxRecDepth 65536 in
theorem splen_hdr (I : Inst) (p r t : Nat) (pub : List Fp) :
    rowTraffic Codec.table.interactions (dRow (.hdr I p) r) t r pub B_SPLEN true =
      if p = 0 then [[Fp.ofNat I.tv, Fp.ofNat (37 + 24 * I.N)]] else [] := by
  rw [bus_splen]; cdc_bus
  by_cases hp : p = 0 <;> simp [hp, o1, z1]

set_option maxRecDepth 65536 in
theorem spost_ash (I : Inst) (ash : List Nat) (j r t : Nat) (pub : List Fp) :
    rowTraffic Codec.table.interactions (dRow (.ash I ash j) r) t r pub B_SPOST true =
      [] := by
  rw [bus_spost]; cdc_bus

set_option maxRecDepth 65536 in
theorem spost_hdr (I : Inst) (p r t : Nat) (pub : List Fp) :
    rowTraffic Codec.table.interactions (dRow (.hdr I p) r) t r pub B_SPOST true =
      [[Fp.ofNat I.tv, Fp.ofNat p, Fp.ofNat ((hdrBytes I).getD p 0)]] := by
  rw [bus_spost]; cdc_bus

set_option maxRecDepth 65536 in
theorem spost_rec (I : Inst) (R : Rec) (f gg bpo bpr apv apostv bigv r t : Nat) (pub : List Fp) :
    rowTraffic Codec.table.interactions (dRow (.record I R f gg bpo bpr apv apostv bigv) r) t r pub B_SPOST true =
      [[Fp.ofNat I.tv, Fp.ofNat (5 + 24 * R.kk + 8 * f + gg), Fp.ofNat bpo]] := by
  rw [bus_spost]; cdc_bus

set_option maxRecDepth 65536 in
theorem spost_hash (I : Inst) (dig hpre : List Nat) (j r t : Nat) (pub : List Fp) :
    rowTraffic Codec.table.interactions (dRow (.hash I dig hpre j) r) t r pub B_SPOST true =
      [[Fp.ofNat I.tv, Fp.ofNat (5 + 24 * I.N + j), Fp.ofNat (dig.getD j 0)]] := by
  rw [bus_spost]; cdc_bus

end ZkFormal.NearV3.Render.Cdc
