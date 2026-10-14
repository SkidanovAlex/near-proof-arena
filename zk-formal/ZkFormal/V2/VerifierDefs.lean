import ArenaCore.Bytes
import ZkFormal.Air.Basic
import ZkFormal.Algebra.Fp
import ZkFormal.GameDefs
import ZkFormal.Stark.BcsDefs
import ZkFormal.Stark.Field
import ZkFormal.Stark.Iop
import ZkFormal.Stark.Params
import ZkFormal.Stark.ProtocolDefs
import ZkFormal.Stark.VerifierDefs
import ZkFormal.V2.Air

/-!
# `ZkFormal.V2.VerifierDefs`

The definitions of `ZkFormal.V2.Verifier` that the deployed verifier model
(`NpUdrStarkV2.Model.verifier`) uses, moved verbatim (same names, statements and bodies).
`ZkFormal.V2.Verifier` imports this module, so its importers see the same names. Definitions only:
the model's import closure must not contain proof modules (judge native-lean build,
lane v3-model-split, docs/logs/v3-model-split-2026-10.md).
-/

namespace ZkFormal.V2

open ArenaCore Lean.Grind ZkFormal.Air ZkFormal.Stark

/-- BabyBear elements read as naturals: the canonical representative. -/
instance : PubVal ZkFormal.Algebra.Fp := ⟨ZkFormal.Algebra.Fp.toNat⟩

section

variable {F K : Type} [Field F] [Field K] [StarkField F K] [DecidableEq F] [DecidableEq K] [PubVal F]

attribute [local instance] Semiring.natCast

/-- Fingerprint of a public message: `fp_α(m ‖ (bus+1))`, v1's convention. -/
def pubFp (α : K) (b : Nat) (m : List F) : K :=
  combine α (m.map StarkField.embed ++ [((b + 1 : Nat) : K)])

/-- `Π_pub(s)`: the product of `γ − fp` over the public messages of side `s`. -/
def pubProd (AP : AirP) (pub : List F) (α γ : K) (s : Bool) : K :=
  ((pubMsgs AP pub).filter fun x => x.2.1 == s).foldl
    (fun acc x => acc * (γ - pubFp α x.1 x.2.2)) 1

/-- The global ALI and bus checks of v2 (v1's `globalChecks` with the public products). -/
def globalChecksP (AP : AirP) (prm : Params) (pub : List F) (lay : List TLayout)
    (ood : List (TOod K)) (finals : List K) (αfp γ αc z : K) : Bool :=
  let perTable := (AP.tables.zip (lay.zip ood))
  let r := perTable.foldl (fun (acc : Bool × List K) (T, L, o) =>
    let fins := acc.2.take (L.sendG + L.recvG)
    let env := oodEnv pub L.log z o.mainZ o.mainG
    let cs := (T.allConstraints.map (·.evalWith env)) ++
      auxConstraints T prm.auxGroup env αfp γ o.auxZ o.auxG fins
    let zT := z ^ (2 ^ L.log)
    let qz := combine zT o.quotZ
    (acc.1 && decide (combine αc cs = (zT - 1) * qz), acc.2.drop (L.sendG + L.recvG)))
    (true, finals)
  let fins := (lay.foldl (fun (acc : List (List K) × List K) L =>
      (acc.1 ++ [acc.2.take (L.sendG + L.recvG)], acc.2.drop (L.sendG + L.recvG))) ([], finals)).1
  let sends : List K := (fins.zip lay).map fun (f, L) => (f.take L.sendG).foldl (· * ·) 1
  let recvs : List K := (fins.zip lay).map fun (f, L) => (f.drop L.sendG).foldl (· * ·) 1
  r.1 && decide (sends.foldl (fun a b => a * b) (1 : K) * pubProd AP pub αfp γ true =
    recvs.foldl (fun a b => a * b) (1 : K) * pubProd AP pub αfp γ false)

/-- Build the v2 context from an erased complete transcript (v1's `prep`, new `globalOk`). -/
def prepP (AP : AirP) (prm : Params) (τ : PT K Unit) : Ctx K :=
  match τ.header? with
  | none => .bad
  | some hdr =>
    let A := AP.toAir
    let lay := layout A prm hdr
    let pub : List F := τ.cb.map fun b => ofNatF b.toNat
    match τ.chals, τ.elems with
    | αfp :: γ :: αc :: z :: rest, [finals, ood, fp] =>
      let L := batchRounds lay
      let rs := rest.take L
      let fri := rest.drop L
      let kinds := friChalKinds A prm hdr
      let betas := ((kinds.zip fri).filter (! ·.1.1)).map (·.2)
      let gammas := ((kinds.zip fri).filter (·.1.1)).map fun (k, c) => (k.2, c)
      let (oods, _) := splitOod lay ood
      let eqs := eqTable rs
      let deep := ((lay.zip oods).foldl (fun (acc : List (TDeep K) × List (Nat × Nat)) (Lt, o) =>
        let off := (acc.2.lookup Lt.lde).getD 0
        let e := eqs.drop off
        let eMz := e.take Lt.width; let e := e.drop Lt.width
        let eMg := e.take Lt.width; let e := e.drop Lt.width
        let eAz := e.take Lt.aux; let e := e.drop Lt.aux
        let eAg := e.take Lt.aux; let e := e.drop Lt.aux
        let eQ := e.take Lt.quot
        let dot (a b : List K) : K := (a.zip b).foldl (fun s (u, v) => s + u * v) 0
        let td : TDeep K := ⟨eMz, eMg, eAz, eAg, eQ,
          dot eMz o.mainZ + dot eAz o.auxZ + dot eQ o.quotZ, dot eMg o.mainG + dot eAg o.auxG⟩
        let cnt := 2 * Lt.width + 2 * Lt.aux + Lt.quot
        (acc.1 ++ [td], (Lt.lde, off + cnt) :: acc.2.filter (·.1 != Lt.lde))) ([], [])).1
      let okLens := decide (rest.length = L + kinds.length) && decide (fp.length = 2) &&
        decide (finals.length = (lay.map fun L => L.sendG + L.recvG).sum) &&
        decide (ood.length = (lay.map fun L => 2 * L.width + 2 * L.aux + L.quot).sum)
      { ok := okLens, hdr, lay, n0 := queryLog A prm hdr, ℓ := finalLayer A prm hdr, z
        ood := oods, deep, commits := friCommits A prm hdr, betas, gammas, finalPoly := fp
        globalOk := okLens && pubFit AP pub &&
          globalChecksP (F := F) AP prm pub lay oods finals αfp γ αc z }
    | _, _ => .bad

/-- The v2 `globalOk` as a function of the transcript (`false` on malformed ones). -/
def globalOkP (AP : AirP) (prm : Params) (τ : PT K Unit) : Bool :=
  match τ.header? with
  | none => false
  | some hdr =>
    let pub : List F := τ.cb.map fun b => ofNatF b.toNat
    let lay := layout AP.toAir prm hdr
    match τ.chals, τ.elems with
    | αfp :: γ :: αc :: z :: rest, [finals, ood, fp] =>
      let okLens := decide (rest.length = batchRounds lay + (friChalKinds AP.toAir prm hdr).length) &&
        decide (fp.length = 2) &&
        decide (finals.length = (lay.map fun L => L.sendG + L.recvG).sum) &&
        decide (ood.length = (lay.map fun L => 2 * L.width + 2 * L.aux + L.quot).sum)
      okLens && pubFit AP pub &&
        globalChecksP (F := F) AP prm pub lay (splitOod lay ood).1 finals αfp γ αc z
    | _, _ => false

end

/-- **The IOP verifier of `np-udr-stark-v2`**: v1's, with v2's clear-text checks. -/
def Iop.verifierP (F K : Type) [Field F] [Field K] [StarkField F K] [DecidableEq F] [DecidableEq K]
    [PubVal F] (AP : AirP) (prm : Params) : IopSpec F K :=
  { Iop.verifier F K AP.toAir prm with
    prep := prepP (F := F) AP prm
    global := fun c => c.globalOk }

/-- **The deployed verifier model of `np-udr-stark-v2`**: the BCS compilation of `Iop.verifierP`. -/
def verifierP (F K : Type) [Field F] [Field K] [StarkField F K] [DecidableEq F] [DecidableEq K]
    [PubVal F] (AP : AirP) (prm : Params) : ZkFormal.TreeVerifier :=
  ⟨fun pub cb pb => Bcs.compile (F := F) (Iop.verifierP F K AP prm) pub cb pb⟩

section

end

section

end

end ZkFormal.V2
