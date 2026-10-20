//! Research adapter: compile the existing reference verifier without the prover.
//! Source modules are reused verbatim. This is not the certified Lean verifier.
#[path = "../../../../../examples/np-udr-stark-fast2/source/src/air.rs"]
pub mod air;
#[path = "../../../../../examples/np-udr-stark-fast2/source/src/aux.rs"]
pub mod aux;
#[path = "../../../../../examples/np-udr-stark-fast2/source/src/field.rs"]
pub mod field;
#[path = "../../../../../examples/np-udr-stark-fast2/source/src/hash.rs"]
pub mod hash;
#[path = "../../../../../examples/np-udr-stark-fast2/source/src/mmcs.rs"]
pub mod mmcs;
#[path = "../../../../../examples/np-udr-stark-fast2/source/src/protocol.rs"]
pub mod protocol;
#[path = "../../../../../examples/np-udr-stark-fast2/source/src/transcript.rs"]
pub mod transcript;
#[path = "../../../../../examples/np-udr-stark-fast2/source/src/verifier.rs"]
pub mod verifier;

pub const JOURNAL_DOMAIN: &[u8] = b"nearproof-compression-v1\0";

/// Bind exact AIR, public tape and claim bytes, each with a fixed-size digest.
/// The verifier image ID separately binds the implementation and protocol.
pub fn journal(air: &[u8], public: &[u8], claim: &[u8]) -> Vec<u8> {
    use sha2::{Digest, Sha256};
    let mut out = JOURNAL_DOMAIN.to_vec();
    for bytes in [air, public, claim] {
        out.extend_from_slice(&Sha256::digest(bytes));
    }
    out
}

