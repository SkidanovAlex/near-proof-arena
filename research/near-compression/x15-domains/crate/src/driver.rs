// Driver body, included inside `mod config` (next to the SHA-384 config's private types).
// ---------- a wide AIR: W columns, next[j] = local[j] + local[j+1 mod W] (degree 1) ----------
#[derive(Clone, Copy)]
struct WideAir { w: usize }
impl<F> PartitionedBaseAir<F> for WideAir {}
impl<F> BaseAir<F> for WideAir { fn width(&self) -> usize { self.w } }
impl<F> BaseAirWithPublicValues<F> for WideAir {}
impl<AB: AirBuilder> Air<AB> for WideAir {
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let (local, next) = (main.row_slice(0).unwrap(), main.row_slice(1).unwrap());
        let (local, next) = (local.to_vec(), next.to_vec());
        let mut t = builder.when_transition();
        for j in 0..self.w {
            t.assert_eq(local[j].clone() + local[(j + 1) % self.w].clone(), next[j].clone());
        }
    }
}
struct WideFixture { w: usize, log_h: usize }
impl TestFixture<Sc> for WideFixture {
    fn airs(&self) -> Vec<AirRef<Sc>> { vec![Arc::new(WideAir { w: self.w })] }
    fn generate_proving_ctx(&self) -> ProvingContext<CpuColMajorBackend<Sc>> {
        let (w, h) = (self.w, 1usize << self.log_h);
        let mut rows = vec![Fb::ZERO; w * h];
        for j in 0..w { rows[j] = Fb::from_u64(j as u64 + 1); }
        for r in 1..h { for j in 0..w { rows[r * w + j] = rows[(r - 1) * w + j] + rows[(r - 1) * w + (j + 1) % w]; } }
        let m = p3_matrix::dense::RowMajorMatrix::new(rows, w);
        ProvingContext::new(vec![(0, AirProvingContext::simple_no_pis(ColMajorMatrix::from_row_major(&m)))])
    }
}

fn params(odd: usize, log_blowup: usize, l_skip: usize, n_stack: usize, k: usize, bits: usize) -> SystemParams {
    let mut p = test_system_params_small(l_skip, n_stack, k);
    p.max_constraint_degree = 3; p.logup.pow_bits = 0; p.log_blowup = log_blowup;
    p.logup.max_interaction_count = 1 << 20;
    let wp = openvm_stark_backend::WhirParams { k, log_final_poly_len: p.log_final_poly_len(),
        proximity: openvm_stark_backend::WhirProximityStrategy::ListDecoding { m: 3 },
        query_phase_pow_bits: 0, folding_pow_bits: 0, mu_pow_bits: 0 };
    #[cfg(feature = "x15")]
    { p.whir = openvm_stark_backend::WhirConfig::new_with_odd_domain(log_blowup, l_skip + n_stack, wp, bits, odd); }
    #[cfg(not(feature = "x15"))]
    { assert_eq!(odd, 1); p.whir = openvm_stark_backend::WhirConfig::new(log_blowup, l_skip + n_stack, wp, bits); }
    p
}

fn encode(proof: &openvm_stark_backend::proof::Proof<Sc>) -> Vec<u8> {
    use openvm_stark_backend::codec::Encode;
    let mut b = Vec::new(); proof.encode(&mut b).unwrap(); b
}
fn sha256_hex(b: &[u8]) -> String { use sha2::{Sha256, Digest}; Sha256::digest(b).iter().map(|x| format!("{x:02x}")).collect() }
fn hwm_kb() -> u64 {
    std::fs::read_to_string("/proc/self/status").unwrap().lines().find(|l| l.starts_with("VmHWM"))
        .and_then(|l| l.split_whitespace().nth(1)).unwrap().parse().unwrap()
}

/// Proves `fx` with `p`, verifies, returns (proof, vk, engine).
fn prove<FX: TestFixture<Sc>>(fx: &FX, p: SystemParams) -> (openvm_stark_backend::proof::Proof<Sc>, openvm_stark_backend::keygen::types::MultiStarkVerifyingKey<Sc>, Eng) {
    let engine = Eng::new(p);
    let (pk, vk) = fx.keygen(&engine);
    let proof = fx.prove(&engine, &pk);
    engine.verify(&vk, &proof).expect("honest proof must verify");
    (proof, vk, engine)
}

fn ident() {
    // Fixed fixtures, odd = 1: proofs must be byte-identical between base and patched backends.
    let mut out = Vec::new();
    let p = || params(1, 2, 2, 8, 3, 100);
    out.push(("fib", sha256_hex(&encode(&prove(&FibFixture::new(0, 1, 1 << 9), p()).0))));
    out.push(("interactions", sha256_hex(&encode(&prove(&InteractionsFixture11, p()).0))));
    out.push(("preprocessed", sha256_hex(&encode(&prove(&PreprocessedFibFixture::new(7, 3, (0..256).map(|i| i % 2 == 0).collect()), p()).0))));
    let e = Eng::new(p());
    out.push(("cached", sha256_hex(&encode(&prove(&CachedFixture11::new(e.config().clone()), p()).0))));
    out.push(("mixture", sha256_hex(&encode(&prove(&MixtureFixture::standard(8, e.config().clone()), p()).0))));
    out.push(("wide", sha256_hex(&encode(&prove(&WideFixture { w: 40, log_h: 10 }, params(1, 3, 2, 10, 4, 268)).0))));
    for (n, h) in out { println!("IDENT {n} {h}"); }
}

#[cfg(feature = "x15")]
fn selftest() {
    use openvm_stark_backend::soundness::SoundnessCalculator;
    let mut pass = 0;
    for &(odd, lb, k) in &[(15usize, 1usize, 3usize), (15, 2, 3), (3, 2, 2), (5, 1, 4), (15, 3, 4)] {
        let p = || params(odd, lb, 2, 8, k, 100);
        let (proof, vk, engine) = prove(&FibFixture::new(0, 1, 1 << 9), p());
        let qs: Vec<_> = p().whir.rounds.iter().map(|r| r.num_queries).collect();
        let bits = SoundnessCalculator::calculate_from_vk(&vk);
        println!("SELFTEST fib odd={odd} log_blowup={lb} k={k} queries={qs:?} bytes={} calc_total={:.1} whir={:.1} query={:.1}",
            encode(&proof).len(), bits.total_bits, bits.whir_bits, bits.whir_details.query_bits);
        // Depth check: initial-round path = n + log_blowup - k + ceil(log2 odd).
        let d0 = proof.whir_proof.initial_round_merkle_proofs[0][0].len();
        assert_eq!(d0, 2 + 8 + lb - k + openvm_stark_backend::odd_domain::ceil_log2(odd));
        // ---- negative tests ----
        let mut cases: Vec<(&str, openvm_stark_backend::proof::Proof<Sc>)> = Vec::new();
        let mut b = proof.clone(); b.whir_proof.initial_round_opened_rows[0][0][0][0] += Fb::ONE; cases.push(("initial opened row value", b));
        let mut b = proof.clone(); let last = b.whir_proof.initial_round_opened_rows[0].len() - 1;
        let lr = b.whir_proof.initial_round_opened_rows[0][last].len() - 1; b.whir_proof.initial_round_opened_rows[0][last][lr][0] += Fb::ONE; cases.push(("initial opened row (last query, last coset row)", b));
        let mut b = proof.clone(); b.whir_proof.initial_round_merkle_proofs[0][0][0][0] ^= 1; cases.push(("initial merkle sibling (leaf level)", b));
        let mut b = proof.clone(); let top = b.whir_proof.initial_round_merkle_proofs[0][0].len() - 1; b.whir_proof.initial_round_merkle_proofs[0][0][top][0] ^= 1; cases.push(("initial merkle sibling (top / padding level)", b));
        if !proof.whir_proof.codeword_opened_values.is_empty() {
            let mut b = proof.clone(); b.whir_proof.codeword_opened_values[0][0][1] += <Sc as openvm_stark_backend::StarkProtocolConfig>::EF::ONE; cases.push(("round-1 codeword opened value", b));
            let mut b = proof.clone(); b.whir_proof.codeword_merkle_proofs[0][0][0][0] ^= 1; cases.push(("round-1 merkle sibling", b));
            let mut b = proof.clone(); b.whir_proof.codeword_commits[0][0] ^= 1; cases.push(("round-1 commitment", b));
            let mut b = proof.clone(); b.whir_proof.ood_values[0] += <Sc as openvm_stark_backend::StarkProtocolConfig>::EF::ONE; cases.push(("OOD value", b));
        }
        let mut b = proof.clone(); b.whir_proof.final_poly[0] += <Sc as openvm_stark_backend::StarkProtocolConfig>::EF::ONE; cases.push(("final polynomial", b));
        let mut b = proof.clone(); b.common_main_commit[0] ^= 1; cases.push(("main commitment", b));
        for (name, bad) in cases {
            assert!(engine.verify(&vk, &bad).is_err(), "tampered {name} accepted (odd={odd})");
            pass += 1;
        }
        // The x15 proof must not verify under the power-of-two verifier (domain bound in transcript + shape).
        let e1 = Eng::new(params(1, lb, 2, 8, k, 100));
        let (_pk1, vk1) = FibFixture::new(0, 1, 1 << 9).keygen(&e1);
        assert!(e1.verify(&vk1, &proof).is_err()); pass += 1;
    }
    // Other fixtures (multiple commitments: cached + preprocessed + interactions).
    for (name, run) in [
        ("interactions", Box::new(|p| { prove(&InteractionsFixture11, p); }) as Box<dyn Fn(SystemParams)>),
        ("preprocessed", Box::new(|p| { prove(&PreprocessedFibFixture::new(7, 3, (0..256).map(|i| i % 2 == 0).collect()), p); })),
        ("cached", Box::new(|p: SystemParams| { let e = Eng::new(p.clone()); prove(&CachedFixture11::new(e.config().clone()), p); })),
        ("mixture", Box::new(|p: SystemParams| { let e = Eng::new(p.clone()); prove(&MixtureFixture::standard(8, e.config().clone()), p); })),
        ("wide", Box::new(|p| { let _ = p; prove(&WideFixture { w: 40, log_h: 10 }, params(15, 3, 2, 10, 4, 268)); })),
    ] {
        run(params(15, 2, 2, 8, 3, 100));
        println!("SELFTEST {name} odd=15 honest proof verifies");
    }
    println!("SELFTEST_PASS negative_cases_rejected={pass}");
}

/// WHIR-level adversarial tests on the x15 domain: the prover commits *well-formed* Merkle trees
/// (every authentication path is valid) over words that are not the RS encoding on the declared
/// 15 * 2^L domain. The verifier must reject via the fold/sumcheck consistency checks, which only
/// works if prover layout, verifier query points and transcript sampling agree.
#[cfg(feature = "x15")]
fn adversarial() {
    use openvm_stark_backend::{prover::{stacked_pcs::{stacked_matrix, rs_code_matrix_odd, MerkleTree}, poly::Ple,
        whir::prove_whir_opening, MatrixDimensions}, verifier::whir::verify_whir, StarkProtocolConfig, FiatShamirTranscript, poly_common::Squarable};
    type EF = <Sc as StarkProtocolConfig>::EF;
    let (odd, lb, l_skip, n_stack, k) = (15usize, 2usize, 2usize, 6usize, 2usize);
    let p = params(odd, lb, l_skip, n_stack, k, 100);
    let engine = Eng::new(p.clone());
    let cfg = engine.config().clone();
    let h = 1usize << (l_skip + n_stack);
    let w = 5usize;
    let mut seed = 0x9e3779b97f4a7c15u64;
    let mut rnd = || { seed ^= seed << 13; seed ^= seed >> 7; seed ^= seed << 17; seed };
    let mat = ColMajorMatrix::new((0..h * w).map(|_| Fb::from_u64(rnd() % 2013265921)).collect(), w);
    let (q, _layout) = stacked_matrix(l_skip, n_stack, &[&mat]).unwrap();
    let z_prism: Vec<EF> = (0..n_stack + 1).map(|_| EF::from_u64(rnd())).collect();
    let z_cube: Vec<EF> = z_prism[0].exp_powers_of_2().take(l_skip).chain(z_prism[1..].iter().copied()).collect();
    let openings: Vec<EF> = q.columns().map(|c| Ple::from_evaluations(l_skip, c).eval_at_point(l_skip, z_prism[0], &z_prism[1..])).collect();
    let honest_rs = rs_code_matrix_odd(l_skip, lb, odd, &q).unwrap();
    let block = honest_rs.height() / odd;
    let run = |name: &str, rs: ColMajorMatrix<Fb>, expect_ok: bool| {
        let tree = MerkleTree::new_with_cosets(cfg.hasher(), rs, 1 << k, odd).unwrap();
        let commit = tree.root().unwrap();
        let mut tp = engine.initial_transcript();
        tp.observe_commit(commit);
        let proof = prove_whir_opening::<Sc, _>(&mut tp, cfg.hasher(), l_skip, lb, &p.whir, &[(&q, &tree)], &z_cube).unwrap();
        let mut tv = engine.initial_transcript();
        tv.observe_commit(commit);
        let r = verify_whir::<Sc, _>(&mut tv, &cfg, &proof, &[openings.clone()], &[commit], &z_cube);
        println!("ADVERSARIAL {name}: verify={}", if r.is_ok() { "ACCEPT".to_string() } else { format!("REJECT ({:?})", r.as_ref().unwrap_err()) });
        assert_eq!(r.is_ok(), expect_ok, "{name}");
    };
    let remap = |f: &dyn Fn(usize) -> usize| {
        let hh = honest_rs.height();
        let vals: Vec<Fb> = (0..w).flat_map(|c| (0..hh).map(move |r| (c, r))).map(|(c, r)| honest_rs.values[c * hh + f(r)]).collect();
        ColMajorMatrix::new_any_height(vals, w)
    };
    run("honest x15 codeword", remap(&|r| r), true);
    // (a) cosets 1 and 2 swapped: a valid tree over a permuted (non-RS-on-D) word.
    run("cosets 1<->2 swapped", remap(&|r| { let (a, u) = (r / block, r % block); let a2 = match a { 1 => 2, 2 => 1, x => x }; a2 * block + u }), false);
    // (b) all 15 cosets replaced by coset 0 (the power-of-two codeword repeated): looks like an
    //     RS codeword on H, not on D.
    run("power-of-two codeword repeated 15x", remap(&|r| r % block), false);
    // (c) points inside each coset reversed (u -> -u mod 2^L): evaluation on the inverse domain.
    run("each coset bit-mirrored (u -> 2^L - u)", remap(&|r| { let (a, u) = (r / block, r % block); a * block + ((block - u) % block) }), false);
    println!("ADVERSARIAL_PASS");
}

/// Commit-phase micro-benchmark: RS encoding and Merkle tree, separately, best of `reps`.
fn commit_bench(args: &[String]) {
    use openvm_stark_backend::prover::{stacked_pcs::{rs_code_matrix, MerkleTree}, MatrixDimensions};
    let a: Vec<usize> = args.iter().map(|s| s.parse().unwrap()).collect();
    let (odd, lb, log_h, w, k, reps) = (a[0], a[1], a[2], a[3], a[4], a[5]);
    let engine = Eng::new(params(1, lb, 2, log_h - 2, k, 100));
    let h = 1usize << log_h;
    let mat = ColMajorMatrix::new((0..h * w).map(|i| Fb::from_u64((i as u64).wrapping_mul(0x9e3779b97f4a7c15) % 2013265921)).collect(), w);
    let (mut best_rs, mut best_tree) = (f64::MAX, f64::MAX);
    let mut height = 0;
    for _ in 0..reps {
        let t = std::time::Instant::now();
        #[cfg(feature = "x15")]
        let rs = if odd == 1 { rs_code_matrix(2, lb, &mat).unwrap() } else { openvm_stark_backend::prover::stacked_pcs::rs_code_matrix_odd(2, lb, odd, &mat).unwrap() };
        #[cfg(not(feature = "x15"))]
        let rs = { assert_eq!(odd, 1); rs_code_matrix(2, lb, &mat).unwrap() };
        best_rs = best_rs.min(t.elapsed().as_secs_f64());
        height = rs.height();
        let t = std::time::Instant::now();
        #[cfg(feature = "x15")]
        let tree = MerkleTree::new_with_cosets(engine.config().hasher(), rs, 1 << k, odd).unwrap();
        #[cfg(not(feature = "x15"))]
        let tree = MerkleTree::new(engine.config().hasher(), rs, 1 << k).unwrap();
        best_tree = best_tree.min(t.elapsed().as_secs_f64());
        std::hint::black_box(tree.root().unwrap());
    }
    println!("COMMIT odd={odd} log_blowup={lb} log_h={log_h} w={w} k={k} domain={height} rs_s={best_rs:.3} merkle_s={best_tree:.3} rs_ns_per_point_col={:.2} vm_hwm_mb={}",
        best_rs * 1e9 / (height as f64 * w as f64), hwm_kb() / 1024);
}

fn bench(args: &[String]) {
    let a: Vec<usize> = args.iter().map(|s| s.parse().unwrap()).collect();
    let (odd, lb, log_h, w, k, bits) = (a[0], a[1], a[2], a[3], a[4], a[5]);
    let p = params(odd, lb, 2, log_h - 2, k, bits);
    let qs: Vec<_> = p.whir.rounds.iter().map(|r| r.num_queries).collect();
    let fx = WideFixture { w, log_h };
    let engine = Eng::new(p);
    let (pk, vk) = fx.keygen(&engine);
    let t = std::time::Instant::now();
    let proof = fx.prove(&engine, &pk);
    let prove_s = t.elapsed().as_secs_f64();
    let t = std::time::Instant::now();
    engine.verify(&vk, &proof).unwrap();
    let verify_s = t.elapsed().as_secs_f64();
    let bytes = encode(&proof).len();
    let whir = { use openvm_stark_backend::codec::Encode; let mut b = Vec::new(); proof.whir_proof.encode(&mut b).unwrap(); b.len() };
    println!("BENCH odd={odd} log_blowup={lb} log_h={log_h} w={w} k={k} bits={bits} queries={qs:?} prove_s={prove_s:.3} verify_s={verify_s:.4} proof_bytes={bytes} whir_bytes={whir} vm_hwm_mb={}",
        hwm_kb() / 1024);
}

pub(super) fn run() {
    let args: Vec<String> = std::env::args().collect();
    match args.get(1).map(|s| s.as_str()) {
        Some("ident") => ident(),
        #[cfg(feature = "x15")]
        Some("selftest") => selftest(),
        #[cfg(feature = "x15")]
        Some("adversarial") => adversarial(),
        Some("bench") => bench(&args[2..]),
        Some("commit") => commit_bench(&args[2..]),
        _ => panic!("usage: ident | selftest | bench odd log_blowup log_h w k bits"),
    }
}
