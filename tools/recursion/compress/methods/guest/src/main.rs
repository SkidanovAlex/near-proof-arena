use compression_verifier::{air::Air, journal, verifier::verify};
use risc0_zkvm::guest::env;

fn main() {
    let air_bytes = env::read_frame();
    let public = env::read_frame();
    let claim = env::read_frame();
    let proof = env::read_frame();
    assert!(air_bytes.len() <= 16 * 1024 * 1024);
    assert!(public.len() <= 16 * 1024 * 1024);
    assert!(claim.len() <= 16 * 1024 * 1024);
    assert!(proof.len() <= compression_verifier::protocol::MAX_PROOF_BYTES);
    let air = Air::from_json(std::str::from_utf8(&air_bytes).unwrap()).unwrap();
    verify(&air, &public, &claim, &proof).expect("inner proof rejected");
    env::commit_slice(&journal(&air_bytes, &public, &claim));
}

