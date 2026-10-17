# Retained version3 batching intermediate

Actual Wasm child proof with SHA384/Ext12, batched field observations and the
original two-block Merkle-node framing. Proof740881bytes. All archived replay,
public mutation, independent Lean execution and transcript oracle checks passed.
Actual verifier hash workload34769compression blocks. QROM security uncertified.

This intermediate's source, Cargo files and proof are retained here. Current
prepare_native_sha384.py emits version4; to replay this version, use this folder's
main.rs, native_sha384_config.rs and literal.rs in the standalone crate, its
Cargo.lock, and NEARPROOF_REPLAY=1 with NEARPROOF_LITERAL_OUT pointing here.
Do not replay this proof with a differently versioned transcript.
