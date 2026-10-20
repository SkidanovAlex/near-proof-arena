//! One NV layer at fixed (padded) trace heights, with per-phase timing (tracing-forest).
//! lane/pq-prover-latency.  The child is the Fib fixture; with `NV_FIXED` the NV traces are padded
//! to the given heights, so the prover's work is that of a layer of that shape (the program only
//! fills part of NvAir; the zerocheck / GKR / commit / WHIR work is a function of the heights).
//! Env: PARENT_* (as nv_chain: N_STACK, LOG_BLOWUP, K, BITS, LIST_M, QUERY_POW, K1, X15, MULTIPROOF,
//! KEEP_DOMAIN, GRUEN_GKR, GKR_DERIVE, GRUEN_ZC, NEXT_MASK, WHIR_Y, TIGHT, WIDE_POW), NV_LOG_ROWS,
//! NV_FIXED (comma list: NvAir, Sha512Air, TableAir, ByteAir heights), NV_TRACE=1 for the span tree.
use openvm_recursion_circuit::{nv::circuit::{prove_level, NvCircuit}, sha384::config::*};
use openvm_stark_backend::{
    interaction::LogUpSecurityParameters,
    test_utils::{test_system_params_small, FibFixture, TestFixture},
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

fn main() {
    if env_usize("NV_TRACE", 1) == 1 {
        openvm_stark_sdk::utils::setup_tracing();
    }
    let log_rows = env_usize("NV_LOG_ROWS", 18);
    let mut cp = test_system_params_small(2, 8, 3);
    cp.max_constraint_degree = 4;
    let cp = env_levers("CHILD", cp, 5);
    let child_engine = Sha384CpuEngine::new(cp);
    let (vk0, p0) = FibFixture::new(0, 1, 1 << 5).keygen_and_prove(&child_engine);
    let mut pp = params_from_env("PARENT", [16, 3, 20, 3]);
    pp.max_constraint_degree = NvCircuit::new(3, 16, 1).layout().degree().max(6);
    println!(
        "NVL_PARAMS l_skip={} n_stack={} k={} log_blowup={} queries={:?} pow(mu,fold,query,logup)=({},{},{},{})",
        pp.l_skip, pp.n_stack, pp.k_whir(), pp.log_blowup,
        pp.whir.rounds.iter().map(|r| r.num_queries).collect::<Vec<_>>(),
        pp.whir.mu_pow_bits, pp.whir.folding_pow_bits, pp.whir.query_phase_pow_bits, pp.logup.pow_bits
    );
    let engine = Sha384CpuEngine::new(pp);
    let k = engine.params().k_whir();
    let mut circ = NvCircuit::new(k, log_rows, 1);
    if let Ok(s) = std::env::var("NV_FIXED") {
        circ.heights = Some(s.split(',').map(|x| x.trim().parse().unwrap()).collect());
    }
    let _ = std::fs::write("/proc/self/clear_refs", "5");
    let t = std::time::Instant::now();
    let (vk1, p1, b, shapes) = prove_level(&circ, &engine, &vk0, &p0);
    let secs = t.elapsed().as_secs_f64();
    let hwm = std::fs::read_to_string("/proc/self/status").ok()
        .and_then(|s| s.lines().find(|l| l.starts_with("VmHWM")).map(|l| l.split_whitespace().nth(1).unwrap().parse::<f64>().unwrap()))
        .unwrap_or(0.0) / 1048576.0;
    let mut cells = 0usize;
    for (i, a) in vk1.inner.per_air.iter().enumerate() {
        cells += shapes[i].0 * shapes[i].1;
        println!("NVL_AIR {i} h={} w={} int/row={} deg={}", shapes[i].0, shapes[i].1, a.symbolic_constraints.interactions.len(), a.max_constraint_degree);
    }
    use openvm_stark_backend::codec::Encode;
    let mut bytes = Vec::new();
    p1.encode(&mut bytes).unwrap();
    println!(
        "NVL_SUMMARY wall_s={secs:.1} (keygen+tracegen+prove+verify) peak_rss_gb={hwm:.2} cells={cells} (2^{:.2}) program_rows={} proof_bytes={}",
        (cells as f64).log2(), b.instrs.len(), bytes.len()
    );
}
