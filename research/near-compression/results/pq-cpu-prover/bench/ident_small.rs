//! lane/pq-cpu-prover: small byte-identity fixtures for the Ext12 CPU prover. Proves
//! MixtureFixture::standard (Fib, interactions, cached, preprocessed, self-interaction AIRs) and a
//! FibFixture at several heights with the SHA-384/Ext12 engine at PARENT_* lever settings, and
//! prints one SHA-256 per proof. Compare across binaries and NEARPROOF_CPU_FAST=0/1.
use openvm_recursion_circuit::sha384::config::*;
use openvm_stark_backend::{
    interaction::LogUpSecurityParameters,
    test_utils::{FibFixture, MixtureFixture, TestFixture},
    StarkEngine, SystemParams, WhirConfig, WhirLevers, WhirParams, WhirProximityStrategy,
};

fn env_usize(name: &str, d: usize) -> usize {
    std::env::var(name).map(|s| s.parse().unwrap()).unwrap_or(d)
}

fn with_levers(mut p: SystemParams, levers: WhirLevers, x15: usize, bits: usize) -> SystemParams {
    let w = &p.whir;
    let h = p.l_skip + p.n_stack;
    let lf = if levers.k_first != 0 {
        let lf0 = p.log_final_poly_len();
        lf0 + (h - levers.k_first - lf0) % w.k
    } else {
        p.log_final_poly_len()
    };
    let wp = WhirParams {
        k: w.k,
        log_final_poly_len: lf,
        proximity: w.proximity,
        query_phase_pow_bits: w.query_phase_pow_bits,
        folding_pow_bits: w.folding_pow_bits,
        mu_pow_bits: w.mu_pow_bits,
    };
    p.whir = WhirConfig::new_full(p.log_blowup, p.l_skip + p.n_stack, wp, bits, levers, x15);
    p
}

fn env_levers(prefix: &str, p: SystemParams, bits: usize) -> SystemParams {
    let e = |n: &str, d: usize| env_usize(&format!("{prefix}_{n}"), d);
    let levers = WhirLevers {
        k_first: e("K1", 0),
        multiproof: e("MULTIPROOF", 0) == 1,
        keep_domain: e("KEEP_DOMAIN", 0) == 1,
        gruen_gkr: e("GRUEN_GKR", 0) == 1,
        gkr_derive_claims: e("GKR_DERIVE", 0) == 1,
        next_mask: e("NEXT_MASK", 0) == 1,
        gruen_zerocheck: e("GRUEN_ZC", 0) == 1,
        wide_query_pow: e("WIDE_POW", 0) == 1,
        tight_heights: e("TIGHT", 0) == 1,
        whir_y: e("WHIR_Y", 0) == 1,
    };
    let x15 = e("X15", 1);
    if levers.is_default() && x15 == 1 {
        return p;
    }
    with_levers(p, levers, x15, bits)
}

fn params_from_env(prefix: &str, d: [usize; 4]) -> SystemParams {
    let e = |n: &str, dflt: usize| env_usize(&format!("{prefix}_{n}"), dflt);
    let l_skip = e("L_SKIP", 2);
    let n_stack = e("N_STACK", d[0]);
    let k = e("K", 3);
    let bits = e("BITS", d[2]);
    let list_m = e("LIST_M", d[3]);
    let proximity = if list_m > 0 { WhirProximityStrategy::ListDecoding { m: list_m } } else { WhirProximityStrategy::UniqueDecoding };
    let logup = LogUpSecurityParameters { max_interaction_count: 1 << e("INTERACTION_LOG", 28), log_max_message_length: 7, pow_bits: e("LOGUP_POW", 0) };
    let log_final = e("LOG_FINAL", (l_skip + n_stack) % k);
    let p = SystemParams::new(e("LOG_BLOWUP", d[1]), l_skip, n_stack, e("W_STACK", 1 << 12), log_final, e("FOLD_POW", 0), e("MU_POW", 0), proximity, bits, logup, 4, e("QUERY_POW", 0), k);
    env_levers(prefix, p, bits)
}

fn sha(p: &openvm_stark_backend::proof::Proof<Sha384Config>) -> String {
    use openvm_stark_backend::codec::Encode;
    use sha2::{Digest, Sha256};
    let mut bytes = Vec::new();
    p.encode(&mut bytes).unwrap();
    Sha256::digest(&bytes).iter().map(|b| format!("{b:02x}")).collect()
}

fn main() {
    let logs: Vec<usize> = std::env::var("IDENT_LOGS").unwrap_or("8,11,14".into()).split(',').map(|x| x.parse().unwrap()).collect();
    for &lh in &logs {
        let mut pp = params_from_env("PARENT", [lh.max(6) - 2, 1, 100, 3]);
        pp.max_constraint_degree = 4;
        let engine = Sha384CpuEngine::new(pp);
        let t = std::time::Instant::now();
        let (_, p) = MixtureFixture::standard(lh, engine.config().clone()).keygen_and_prove(&engine);
        println!("IDENT mixture log_h={lh} sha256={} secs={:.2}", sha(&p), t.elapsed().as_secs_f64());
        let t = std::time::Instant::now();
        let (_, p) = FibFixture::new(0, 1, 1 << lh).keygen_and_prove(&engine);
        println!("IDENT fib log_h={lh} sha256={} secs={:.2}", sha(&p), t.elapsed().as_secs_f64());
    }
}
