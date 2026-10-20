import NearCompression.FrameWire

/-! Complete gas record encoding. Every counter is retained, including profiling.
128-bit bounds are explicit codec obligations and are not runtime assumptions. -/
namespace NearCompression
open NearSpec NearSpecV3 NearSpecV3.Wasm

def gasWireWf (g : Gas) : Prop :=
  g.burnt < 340282366920938463463374607431768211456 ∧
  g.promises < 340282366920938463463374607431768211456 ∧
  g.prepaid < 340282366920938463463374607431768211456 ∧
  g.limit < 340282366920938463463374607431768211456 ∧
  g.g < 340282366920938463463374607431768211456 ∧
  g.host < 340282366920938463463374607431768211456 ∧
  g.action < 340282366920938463463374607431768211456 ∧
  g.sendCompute < 340282366920938463463374607431768211456 ∧
  g.special.toList.length < 4294967296 ∧
  ∀ n ∈ g.special.toList, n < 340282366920938463463374607431768211456

def encodeGasWire (g : Gas) : Bytes :=
  u128 g.burnt ++ u128 g.promises ++ u128 g.prepaid ++ u128 g.limit ++ u128 g.g ++ u128 g.host ++ u128 g.action ++ u128 g.sendCompute ++
    encList u128 g.special.toList

def parseGasWire : NearSpecV3.P Gas := fun bs => do
  let (burnt, bs) ← pU128 "gas burnt" bs
  let (promises, bs) ← pU128 "gas promises" bs
  let (prepaid, bs) ← pU128 "gas prepaid" bs
  let (limit, bs) ← pU128 "gas limit" bs
  let (g, bs) ← pU128 "gas g" bs
  let (host, bs) ← pU128 "gas host" bs
  let (action, bs) ← pU128 "gas action" bs
  let (sendCompute, bs) ← pU128 "gas sendCompute" bs
  let (special, bs) ← pVec "special gas" (pU128 "special counter") bs
  pure ({ burnt, promises, prepaid, limit, g, host, action, sendCompute, special := special.toArray }, bs)

theorem gas_wire_roundtrip (g : Gas) (wf : gasWireWf g) (rest : Bytes) :
    parseGasWire (encodeGasWire g ++ rest) = .ok (g, rest) := by
  obtain ⟨hburnt, hpromises, hprepaid, hlimit, hg, hhost, haction, hsendCompute, hlen, hspecial⟩ := wf
  simp only [parseGasWire, encodeGasWire, List.append_assoc]
  rw [pU128_ok _ _ _ hburnt]
  simp only [bind, Except.bind]
  rw [pU128_ok _ _ _ hpromises]
  simp only [bind, Except.bind]
  rw [pU128_ok _ _ _ hprepaid]
  simp only [bind, Except.bind]
  rw [pU128_ok _ _ _ hlimit]
  simp only [bind, Except.bind]
  rw [pU128_ok _ _ _ hg]
  simp only [bind, Except.bind]
  rw [pU128_ok _ _ _ hhost]
  simp only [bind, Except.bind]
  rw [pU128_ok _ _ _ haction]
  simp only [bind, Except.bind]
  rw [pU128_ok _ _ _ hsendCompute]
  simp only [bind, Except.bind]
  rw [pVec_ok _ _ _ _ _ hlen (fun n hn tail => pU128_ok _ n tail (hspecial n hn))]
  simp [bind, Except.bind, pure, Except.pure]

theorem gas_wire_injective (a b : Gas) (ha : gasWireWf a) (hb : gasWireWf b)
    (same : encodeGasWire a = encodeGasWire b) : a = b := by
  have h := congrArg (fun bs => parseGasWire (bs ++ [])) same
  rw [gas_wire_roundtrip a ha [], gas_wire_roundtrip b hb []] at h
  exact congrArg Prod.fst (Except.ok.inj h)

end NearCompression
