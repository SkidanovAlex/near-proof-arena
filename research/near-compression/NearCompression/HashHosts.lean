import NearCompression.Instruction

/-! Actual hash-host execution preserves logical map representation. The hash
functions are the existing deterministic functions; this makes no collision,
random-oracle or quantum-security assumption or claim about them. -/
namespace NearCompression
open NearSpecV3.Wasm

def hashCallCode (base byte : Cost) (units : Nat → Nat)
    (hash : ByteArray → ByteArray) : HM Unit := do
  let a ← popArgs 3
  payBaseH base
  let v ← memOrRegH a[1] a[0]
  payPerH byte (units v.size)
  regSetH a[2] (hash v)

theorem host_sim_hash_call_code (base byte : Cost) (units : Nat → Nat)
    (hash : ByteArray → ByteArray) :
    HostSim (hashCallCode base byte units hash) (hashCallCode base byte units hash) := by
  unfold hashCallCode
  with_reducible apply host_sim_bind
  · exact host_sim_pop_args 3
  intro args
  with_reducible apply host_sim_bind
  · unfold payBaseH
    exact host_sim_with_gas _
  intro _
  with_reducible apply host_sim_bind
  · with_reducible exact host_sim_mem_or_reg args[1] args[0]
  intro value
  with_reducible apply host_sim_bind
  · unfold payPerH
    exact host_sim_with_gas _
  intro _
  with_reducible exact host_sim_reg_set args[2] (hash value) true

theorem actual_sha256_code : hostCall "sha256" =
    some (hashCallCode C.sha256Base C.sha256Byte id Crypto.sha256) := by rfl

theorem actual_keccak256_code : hostCall "keccak256" =
    some (hashCallCode C.keccak256Base C.keccak256Byte id Crypto.keccak256) := by rfl

theorem actual_keccak512_code : hostCall "keccak512" =
    some (hashCallCode C.keccak512Base C.keccak512Byte id Crypto.keccak512) := by rfl

theorem actual_ripemd160_code : hostCall "ripemd160" =
    some (hashCallCode C.ripemd160Base C.ripemd160Block
      (fun n => (n + 8) / 64 + 1) Crypto.ripemd160) := by rfl

theorem actual_hash_call_sim (name : String)
    (hn : name ∈ ["sha256", "keccak256", "keccak512", "ripemd160"])
    (call : HM Unit) (hc : hostCall name = some call) : HostSim call call := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with hn | hn | hn | hn
  · subst name
    rw [actual_sha256_code] at hc
    cases Option.some.inj hc
    with_reducible exact host_sim_hash_call_code C.sha256Base C.sha256Byte id Crypto.sha256
  · subst name
    rw [actual_keccak256_code] at hc
    cases Option.some.inj hc
    with_reducible exact host_sim_hash_call_code C.keccak256Base C.keccak256Byte id Crypto.keccak256
  · subst name
    rw [actual_keccak512_code] at hc
    cases Option.some.inj hc
    with_reducible exact host_sim_hash_call_code C.keccak512Base C.keccak512Byte id Crypto.keccak512
  · subst name
    rw [actual_ripemd160_code] at hc
    cases Option.some.inj hc
    with_reducible exact host_sim_hash_call_code C.ripemd160Base C.ripemd160Block (fun n => (n + 8) / 64 + 1) Crypto.ripemd160

theorem hash_call_host_equiv (s t : St) (h : StateEquivalent s t) (name : String)
    (hn : name ∈ ["sha256", "keccak256", "keccak512", "ripemd160"]) :
    ResultEquivalent (callHost s name) (callHost t name) :=
  call_host_equiv s t h name (actual_hash_call_sim name hn)

end NearCompression
