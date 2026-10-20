import NearCompression.PromiseObservationPersistence

/-! Context and register host persistence, including charged memory/register errors. -/
namespace NearCompression
open NearSpecV3.Wasm

theorem context_register_body_keeps_real (kind : ContextRegisterHost) (reg : Nat) :
    HostKeepsReal (do regSetH reg (contextRegisterValue kind (← get).ctx) (contextRegisterCharge kind)) := by
  apply host_real_get_bind
  intro s hs
  have hr := host_real_reg_set reg (contextRegisterValue kind s.ctx) (contextRegisterCharge kind)
  exact hr s hs

theorem context_register_code_keeps_real (kind : ContextRegisterHost) (base : Cost) :
    HostKeepsReal (contextRegisterCode kind base) := by
  unfold contextRegisterCode
  with_reducible apply host_real_bind
  · exact host_real_pop_args 1
  intro args
  with_reducible apply host_real_bind
  · unfold payBaseH
    exact host_real_with_gas _
  intro _
  with_reducible exact context_register_body_keeps_real kind args[0]

theorem actual_context_register_keeps_real (kind : ContextRegisterHost) (call : HM Unit)
    (hc : hostCall (contextRegisterName kind) = some call) : HostKeepsReal call := by
  rw [actual_context_register_code] at hc
  cases Option.some.inj hc
  with_reducible exact context_register_code_keeps_real kind C.base

theorem context_nat_code_keeps_real (kind : ContextNatHost) (base : Cost) :
    HostKeepsReal (contextNatCode kind base) := by
  unfold contextNatCode
  with_reducible apply host_real_bind
  · unfold payBaseH
    exact host_real_with_gas _
  intro _
  with_reducible apply host_real_get_bind
  intro s hs
  exact host_real_push_ret _ true s hs

theorem actual_context_nat_keeps_real (kind : ContextNatHost) (call : HM Unit)
    (hc : hostCall (contextNatName kind) = some call) : HostKeepsReal call := by
  rw [actual_context_nat_code] at hc
  cases Option.some.inj hc
  with_reducible exact context_nat_code_keeps_real kind C.base

theorem actual_context_host_keeps_real (name : String) (hn : name ∈ contextRegisterNames ++ contextNatNames)
    (call : HM Unit) (hc : hostCall name = some call) : HostKeepsReal call := by
  simp only [List.mem_append, contextRegisterNames, contextNatNames, List.mem_map] at hn
  rcases hn with ⟨kind, _, rfl⟩ | ⟨kind, _, rfl⟩
  · exact actual_context_register_keeps_real kind call hc
  · exact actual_context_nat_keeps_real kind call hc

theorem read_register_code_keeps_real (base : Cost) : HostKeepsReal (readRegisterCode base) := by
  unfold readRegisterCode
  with_reducible apply host_real_bind
  · exact host_real_pop_args 2
  intro a
  with_reducible apply host_real_bind
  · unfold payBaseH
    exact host_real_with_gas _
  intro _
  with_reducible apply host_real_bind
  · with_reducible exact host_real_reg_get a[0]
  intro bytes
  with_reducible exact host_real_write_mem a[1] bytes

theorem write_register_code_keeps_real (base readBase readByte writeBase writeByte : Cost) :
    HostKeepsReal (writeRegisterCode base readBase readByte writeBase writeByte) := by
  unfold writeRegisterCode
  with_reducible apply host_real_bind
  · exact host_real_pop_args 3
  intro a
  with_reducible apply host_real_bind
  · unfold payBaseH
    exact host_real_with_gas _
  intro _
  with_reducible apply host_real_bind
  · exact host_real_charged_read readBase readByte a[2] a[1]
  intro bytes
  exact host_real_charged_register writeBase writeByte a[0] bytes true

theorem register_len_code_keeps_real (base : Cost) : HostKeepsReal (registerLenCode base) := by
  unfold registerLenCode
  with_reducible apply host_real_bind
  · exact host_real_pop_args 1
  intro a
  with_reducible apply host_real_bind
  · unfold payBaseH
    exact host_real_with_gas _
  intro _
  apply host_real_get_bind
  intro s hs
  exact host_real_push_ret _ true s hs

theorem actual_register_host_keeps_real (name : String)
    (hn : name ∈ ["read_register", "write_register", "register_len"])
    (call : HM Unit) (hc : hostCall name = some call) : HostKeepsReal call := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with hn | hn | hn
  · subst name
    rw [actual_read_register_code] at hc
    cases Option.some.inj hc
    with_reducible exact read_register_code_keeps_real C.base
  · subst name
    rw [actual_write_register_code] at hc
    cases Option.some.inj hc
    with_reducible exact write_register_code_keeps_real C.base C.readMemoryBase C.readMemoryByte C.writeRegisterBase C.writeRegisterByte
  · subst name
    rw [actual_register_len_code] at hc
    cases Option.some.inj hc
    with_reducible exact register_len_code_keeps_real C.base

theorem host_real_hash_call_code (base byte : Cost) (units : Nat → Nat)
    (hash : ByteArray → ByteArray) :
    HostKeepsReal (hashCallCode base byte units hash) := by
  unfold hashCallCode
  with_reducible apply host_real_bind
  · exact host_real_pop_args 3
  intro args
  with_reducible apply host_real_bind
  · unfold payBaseH
    exact host_real_with_gas _
  intro _
  with_reducible apply host_real_bind
  · with_reducible exact host_real_mem_or_reg args[1] args[0]
  intro value
  with_reducible apply host_real_bind
  · unfold payPerH
    exact host_real_with_gas _
  intro _
  with_reducible exact host_real_reg_set args[2] (hash value) true

theorem actual_hash_call_keeps_real (name : String)
    (hn : name ∈ ["sha256", "keccak256", "keccak512", "ripemd160"])
    (call : HM Unit) (hc : hostCall name = some call) : HostKeepsReal call := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with hn | hn | hn | hn
  · subst name
    rw [actual_sha256_code] at hc
    cases Option.some.inj hc
    with_reducible exact host_real_hash_call_code C.sha256Base C.sha256Byte id Crypto.sha256
  · subst name
    rw [actual_keccak256_code] at hc
    cases Option.some.inj hc
    with_reducible exact host_real_hash_call_code C.keccak256Base C.keccak256Byte id Crypto.keccak256
  · subst name
    rw [actual_keccak512_code] at hc
    cases Option.some.inj hc
    with_reducible exact host_real_hash_call_code C.keccak512Base C.keccak512Byte id Crypto.keccak512
  · subst name
    rw [actual_ripemd160_code] at hc
    cases Option.some.inj hc
    with_reducible exact host_real_hash_call_code C.ripemd160Base C.ripemd160Block (fun n => (n + 8) / 64 + 1) Crypto.ripemd160

end NearCompression
