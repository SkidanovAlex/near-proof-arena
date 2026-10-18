//! Direct-Wasm base-layer prover slice (lane/pq-wasm-base): AIR set `wasm-base-v1`, family F1, on
//! the unified SWIRL backend (BabyBear, Ext12, SHA-384, T*, 42-byte digests, stacked WHIR).
//!
//! Usage (run `setup.sh` first; the hash levers are fixed by this binary):
//!   nearproof-wasm-base check <air.json> <prep.json>            trace + constraint/bus pre-check
//!   nearproof-wasm-base prove <air.json> <prep.json> [small|pinned]   keygen, debug, prove, verify, sizes
//!   nearproof-wasm-base tamper <air.json> <prep.json>           mutation tests (debug checker + verifier)
//!   nearproof-wasm-base difftest <air.json> <points.txt> <rust.jsonl> [n]   random points for the
//!       Lean/Rust differential test (Rust side: the verifying key's symbolic DAG)
#[allow(dead_code, clippy::all)]
mod config;
mod air;
mod tracegen;

use air::{AirSpec, JsonAir};
use config::{F, Sha384Config, Sha384RefEngine};
use openvm_stark_backend::{
    AirRef, StarkEngine, SystemParams, WhirConfig, WhirLevers, WhirParams, WhirProximityStrategy,
    air_builders::symbolic::{SymbolicExpressionNode, symbolic_variable::Entry},
    codec::Encode,
    interaction::LogUpSecurityParameters,
    keygen::types::MultiStarkVerifyingKey,
    prover::{AirProvingContext, ColMajorMatrix, CpuColMajorBackend, DeviceDataTransporter, ProvingContext},
};
use p3_field::{PrimeCharacteristicRing, PrimeField32};
use p3_matrix::dense::RowMajorMatrix;
use std::sync::Arc;
use std::time::Instant;
use tracegen::{Gen, Prep};

fn set_levers() {
    // The pinned base shape: 42-byte digests, coset leaves, T* (read once by `sha_levers`).
    unsafe {
        std::env::set_var("NEARPROOF_DIGEST_BYTES", "42");
        std::env::set_var("NEARPROOF_COSET_LEAF", "1");
        std::env::set_var("NEARPROOF_TSTAR", "1");
    }
    let l = config::sha_levers();
    assert!(l.digest_bytes == 42 && l.coset_leaf && l.tstar);
}

/// seg-v1 pinned shape (DESIGN-BASE §3): c = 1, b = 1, m = 16, k1 = 1, k = 4, final 2^7, keep-domain,
/// WHIR-Y, multiproof, z = 24, target 268; `n_stack ∈ {10, 14, 18, 22}` (22 = pinned 2^24).
pub fn seg_v1_params(n_stack: usize, w_stack: usize, max_degree: usize) -> SystemParams {
    let (l_skip, log_blowup, k, k1, lf) = (2, 1, 4, 1, 7);
    let log_h = l_skip + n_stack;
    assert_eq!((log_h - k1 - lf) % k, 0, "n_stack must be 10, 14, 18 or 22");
    let levers = WhirLevers { k_first: k1, multiproof: true, keep_domain: true, whir_y: true, ..Default::default() };
    let whir = WhirConfig::new_full(
        log_blowup,
        log_h,
        WhirParams {
            k,
            log_final_poly_len: lf,
            query_phase_pow_bits: 24,
            proximity: WhirProximityStrategy::ListDecoding { m: 16 },
            folding_pow_bits: 0,
            mu_pow_bits: 0,
        },
        268,
        levers,
        1,
    );
    SystemParams {
        l_skip,
        n_stack,
        w_stack,
        log_blowup,
        whir,
        logup: LogUpSecurityParameters { max_interaction_count: 1 << 28, log_max_message_length: 4, pow_bits: 0 },
        max_constraint_degree: max_degree,
    }
}

fn load(air_path: &str) -> AirSpec {
    AirSpec::parse(&std::fs::read_to_string(air_path).unwrap())
}

fn airs(spec: &AirSpec) -> Vec<AirRef<Sha384Config>> {
    spec.tables
        .iter()
        .map(|t| {
            let np = if JsonAir::reads_pub(t) { spec.num_pub } else { 0 };
            Arc::new(JsonAir { spec: t.clone(), num_pub: np }) as AirRef<Sha384Config>
        })
        .collect()
}

fn ctx(spec: &AirSpec, g: &Gen) -> ProvingContext<CpuColMajorBackend<Sha384Config>> {
    ProvingContext::new(
        g.mats
            .iter()
            .enumerate()
            .map(|(i, m)| {
                let pv = if JsonAir::reads_pub(&spec.tables[i]) { g.pubs.clone() } else { vec![] };
                (i, AirProvingContext::simple(ColMajorMatrix::from_row_major(m), pv))
            })
            .collect(),
    )
}

fn cells(g: &Gen) -> usize {
    g.mats.iter().map(|m| m.values.len()).sum()
}

fn compare_with_spec(prep: &Prep, g: &Gen) {
    assert_eq!(prep.status, "fin", "spec run did not finish normally");
    assert_eq!(g.steps, prep.steps, "step count vs spec");
    let spent = prep.g0 - prep.g_final;
    assert_eq!(spent, prep.regular * g.s_units as u128, "gas vs spec");
    match (g.result, prep.stack.last()) {
        (Some((tag, val)), Some((stag, slimbs))) => {
            assert_eq!(tag, *stag);
            assert_eq!(tracegen::limbs(val), *slimbs, "result vs spec");
        }
        (None, None) => {}
        _ => panic!("result arity vs spec"),
    }
}

fn generate(spec: &AirSpec, prep_path: &str) -> (Prep, Gen) {
    let prep = Prep::parse(&std::fs::read_to_string(prep_path).unwrap());
    let g = tracegen::generate(spec, &prep);
    compare_with_spec(&prep, &g);
    (prep, g)
}

fn report_shape(spec: &AirSpec, g: &Gen) {
    let mut active_cells = 0;
    for (i, t) in spec.tables.iter().enumerate() {
        let w = t.cols.len();
        let h = g.mats[i].values.len() / w;
        let rows = g.rows_per_table[i].1;
        active_cells += rows * w;
        println!(
            "TABLE {:<9} width {:>3} rows {:>6} height {:>6} cells {:>9} constraints {:>3} interactions {:>3} degree {}",
            t.name, w, rows, h, h * w, t.constraints.len(), t.inters.len(), t.degree
        );
    }
    println!("STEPS {} S_UNITS {} CELLS_TOTAL {} CELLS_ACTIVE {}", g.steps, g.s_units, cells(g), active_cells);
}

fn cmd_check(air_path: &str, prep_path: &str) {
    let spec = load(air_path);
    let (_prep, g) = generate(&spec, prep_path);
    tracegen::check_constraints(&spec, &g).expect("constraints");
    tracegen::check_buses(&spec, &g).expect("buses");
    report_shape(&spec, &g);
    println!("CHECK OK result {:?}", g.result);
}

fn choose_shape(g: &Gen, which: &str, degree: usize) -> SystemParams {
    let total = cells(g);
    let maxh = g.mats.iter().map(|m| m.values.len() / m.width).max().unwrap();
    let n_stack = match which {
        "pinned" => 22,
        _ => [14, 18, 22]
            .into_iter()
            .find(|&n| (1usize << (n + 2)) >= maxh && total.div_ceil(1 << (n + 2)) + 4 <= 24)
            .unwrap_or(22),
    };
    let w_stack = total.div_ceil(1 << (n_stack + 2)) + 4;
    seg_v1_params(n_stack, w_stack.max(8), degree)
}

fn census(proof: &openvm_stark_backend::proof::Proof<Sha384Config>) -> String {
    fn size<T: Encode>(x: &T) -> usize {
        let mut b = Vec::new();
        x.encode(&mut b).unwrap();
        b.len()
    }
    let lv = proof.whir_proof.levers;
    let (mut gk, mut rl) = (Vec::new(), Vec::new());
    proof.gkr_proof.encode_levers(&lv, &mut gk).unwrap();
    proof.batch_constraint_proof.encode_levers(&mut rl).unwrap();
    format!(
        "total={} gkr={} relations={} stacking={} whir={}",
        size(proof),
        gk.len(),
        rl.len(),
        size(&proof.stacking_proof),
        size(&proof.whir_proof)
    )
}

fn peak_rss_kib() -> u64 {
    std::fs::read_to_string("/proc/self/status")
        .ok()
        .and_then(|s| s.lines().find(|l| l.starts_with("VmHWM:")).map(|l| l.split_whitespace().nth(1).unwrap().parse().unwrap()))
        .unwrap_or(0)
}

fn cmd_prove(air_path: &str, prep_path: &str, which: &str) {
    set_levers();
    let spec = load(air_path);
    let t0 = Instant::now();
    let (_prep, g) = generate(&spec, prep_path);
    let t_gen = t0.elapsed().as_secs_f64();
    tracegen::check_constraints(&spec, &g).expect("constraints");
    tracegen::check_buses(&spec, &g).expect("buses");
    report_shape(&spec, &g);
    let degree = spec.tables.iter().map(|t| t.degree).max().unwrap();
    let params = choose_shape(&g, which, degree.max(2));
    println!(
        "PARAMS n_stack {} log_h {} w_stack {} degree {} queries {:?} pow {}",
        params.n_stack,
        params.l_skip + params.n_stack,
        params.w_stack,
        params.max_constraint_degree,
        params.whir.rounds.iter().map(|r| r.num_queries).collect::<Vec<_>>(),
        params.whir.query_phase_pow_bits
    );
    let eng = Sha384RefEngine::new(params);
    let airs = airs(&spec);
    let t1 = Instant::now();
    let (pk, vk) = eng.keygen(&airs);
    let t_keygen = t1.elapsed().as_secs_f64();
    for (i, a) in vk.inner.per_air.iter().enumerate() {
        println!(
            "VK {:<9} degree {} constraints {} interactions {} dag_nodes {}",
            spec.tables[i].name,
            a.max_constraint_degree,
            a.symbolic_constraints.constraints.constraint_idx.len(),
            a.symbolic_constraints.interactions.len(),
            a.symbolic_constraints.constraints.nodes.len()
        );
    }
    if std::env::var("WASMBASE_DEBUG").is_ok() {
        eng.debug(&airs, &ctx(&spec, &g));
        println!("DEBUG OK");
    }
    let b = openvm_stark_backend::soundness::SoundnessCalculator::calculate_from_vk(&vk);
    println!(
        "SOUNDNESS total={:.1} logup={:.1} proximity={:.1} query={:.1}",
        b.total_bits, b.logup_bits, b.whir_details.proximity_gaps_bits, b.whir_details.query_bits
    );
    let d_pk = eng.device().transport_pk_to_device(&pk);
    let t2 = Instant::now();
    let proof = eng.prove(&d_pk, ctx(&spec, &g)).expect("prove");
    let t_prove = t2.elapsed().as_secs_f64();
    let t3 = Instant::now();
    eng.verify(&vk, &proof).expect("verify");
    let t_verify = t3.elapsed().as_secs_f64();
    println!("PROOF {}", census(&proof));
    println!(
        "TIME tracegen {t_gen:.3}s keygen {t_keygen:.3}s prove {t_prove:.3}s verify {t_verify:.4}s threads {} peak_rss_kib {}",
        std::env::var("RAYON_NUM_THREADS").unwrap_or_default(),
        peak_rss_kib()
    );
    if let Ok(path) = std::env::var("WASMBASE_PROOF_OUT") {
        let mut bytes = Vec::new();
        proof.encode(&mut bytes).unwrap();
        std::fs::write(path, bytes).unwrap();
    }
    println!("PROVE OK steps {} result {:?}", g.steps, g.result);
}

/// Mutation tests: each tamper must be rejected by the native verifier (and is reported against
/// the interpreter pre-checks for diagnosis).
fn cmd_tamper(air_path: &str, prep_path: &str) {
    set_levers();
    let spec = load(air_path);
    let (prep, g) = generate(&spec, prep_path);
    let degree = spec.tables.iter().map(|t| t.degree).max().unwrap();
    let params = choose_shape(&g, "small", degree);
    let eng = Sha384RefEngine::new(params);
    let airs = airs(&spec);
    let (pk, vk) = eng.keygen(&airs);
    let d_pk = eng.device().transport_pk_to_device(&pk);
    let honest = eng.prove(&d_pk, ctx(&spec, &g)).expect("prove honest");
    eng.verify(&vk, &honest).expect("honest verifies");
    println!("TAMPER honest proof verifies");
    let tb = |n: &str| spec.index(n);
    let col = |t: usize, c: &str| spec.tables[t].col(c);
    type Mut = Box<dyn Fn(&mut Gen)>;
    let cell = |t: usize, r: usize, c: usize, f: Box<dyn Fn(F) -> F>| -> Mut {
        Box::new(move |g: &mut Gen| {
            let w = g.mats[t].width;
            let v = &mut g.mats[t].values[r * w + c];
            *v = f(*v);
        })
    };
    let plus1: fn() -> Box<dyn Fn(F) -> F> = || Box::new(|v| v + F::ONE);
    let mut cases: Vec<(String, Mut)> = vec![];
    for (name, c) in [("ADD", "r0"), ("ADD", "c0"), ("MUL", "rb0"), ("MUL", "cy0"), ("BIT", "rb0"), ("SHIFT", "P0"),
        ("SHIFT", "kb0"), ("CMP", "d0"), ("CMP", "br0"), ("CMP", "inv"), ("CONST", "imm0"), ("LOCAL", "L0"),
        ("CTRL", "tgt"), ("CTRL", "inv"), ("STACK", "inv"), ("ADD", "ta"), ("ADD", "h"), ("ADD", "fee"), ("CMP", "S")] {
        let t = tb(name);
        if g.rows_per_table[t].1 == 0 {
            continue;
        }
        cases.push((format!("{name}.{c}+1"), cell(t, 0, col(t, c), plus1())));
    }
    let tb_b = tb("BOUNDARY");
    cases.push(("BOUNDARY.m0+1".into(), cell(tb_b, 0, col(tb_b, "m0"), plus1())));
    cases.push(("RANGE16.v[5]+1".into(), cell(tb("RANGE16"), 5, 0, plus1())));
    cases.push(("BYTE.x0[1] flip".into(), cell(tb("BYTE"), 1, 0, Box::new(|v| F::ONE - v))));
    cases.push(("pub.N+1".into(), Box::new(|g: &mut Gen| g.pubs[0] += F::ONE)));
    cases.push(("pub.S+1".into(), Box::new(|g: &mut Gen| g.pubs[1] += F::ONE)));
    cases.push(("pub.result+1".into(), Box::new(|g: &mut Gen| g.pubs[4] += F::ONE)));
    let rec_op = 8 + prep.local_tags.len() + 1;
    cases.push(("pub.record0.op+1".into(), Box::new(move |g: &mut Gen| g.pubs[rec_op] += F::ONE)));
    let rec_h = 8 + prep.local_tags.len() + 2;
    cases.push(("pub.record0.h+1".into(), Box::new(move |g: &mut Gen| g.pubs[rec_h] += F::ONE)));
    // swap two ADD rows' timestamps (reorders execution)
    let ta = tb("ADD");
    if g.rows_per_table[ta].1 >= 2 {
        let c = col(ta, "ts");
        cases.push(("ADD swap ts rows 0,1".into(), Box::new(move |g: &mut Gen| {
            let w = g.mats[ta].width;
            g.mats[ta].values.swap(c, w + c);
        })));
    }
    let mut rejected = 0;
    let total = cases.len();
    for (name, m) in cases {
        let mut gt = Gen { mats: g.mats.clone(), pubs: g.pubs.clone(), rows_per_table: g.rows_per_table.clone(), result: g.result, steps: g.steps, s_units: g.s_units };
        m(&mut gt);
        let pre = match (tracegen::check_constraints(&spec, &gt), tracegen::check_buses(&spec, &gt)) {
            (Err(e), _) => format!("constraint: {e}"),
            (_, Err(e)) => format!("bus: {}", &e[..e.len().min(80)]),
            _ => "PRECHECK PASSES".into(),
        };
        let verdict = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            match eng.prove(&d_pk, ctx(&spec, &gt)) {
                Ok(p) => eng.verify(&vk, &p).is_err(),
                Err(_) => true,
            }
        }));
        let ok = matches!(verdict, Ok(true) | Err(_));
        if ok {
            rejected += 1;
        }
        println!("TAMPER {name:<28} {} ({pre})", if ok { "REJECTED" } else { "ACCEPTED!" });
    }
    println!("TAMPER summary {rejected}/{total} rejected");
    assert_eq!(rejected, total);
}

fn dag_eval(vk: &MultiStarkVerifyingKey<Sha384Config>, ai: usize, cur: &[F], nxt: &[F], pubs: &[F], sel: [F; 3]) -> (Vec<F>, Vec<(u16, F, Vec<F>)>) {
    let dag = &vk.inner.per_air[ai].symbolic_constraints;
    let mut val: Vec<F> = Vec::with_capacity(dag.constraints.nodes.len());
    for n in &dag.constraints.nodes {
        let v = match n {
            SymbolicExpressionNode::Variable(var) => match var.entry {
                Entry::Main { offset: 0, .. } => cur[var.index],
                Entry::Main { offset: 1, .. } => nxt[var.index],
                Entry::Public => pubs[var.index],
                e => panic!("unexpected entry {e:?}"),
            },
            SymbolicExpressionNode::IsFirstRow => sel[0],
            SymbolicExpressionNode::IsLastRow => sel[1],
            SymbolicExpressionNode::IsTransition => sel[2],
            SymbolicExpressionNode::Constant(c) => *c,
            SymbolicExpressionNode::Add { left_idx, right_idx, .. } => val[*left_idx] + val[*right_idx],
            SymbolicExpressionNode::Sub { left_idx, right_idx, .. } => val[*left_idx] - val[*right_idx],
            SymbolicExpressionNode::Neg { idx, .. } => -val[*idx],
            SymbolicExpressionNode::Mul { left_idx, right_idx, .. } => val[*left_idx] * val[*right_idx],
        };
        val.push(v);
    }
    let cons = dag.constraints.constraint_idx.iter().map(|&i| val[i]).collect();
    let ints = dag.interactions.iter().map(|it| (it.bus_index, val[it.count], it.message.iter().map(|&i| val[i]).collect())).collect();
    (cons, ints)
}

fn cmd_difftest(air_path: &str, points_out: &str, rust_out: &str, n: usize) {
    set_levers();
    let spec = load(air_path);
    let eng = Sha384RefEngine::new(seg_v1_params(14, 32, 8));
    let (_pk, vk) = eng.keygen(&airs(&spec));
    let mut rng: u64 = 0x2026_1018_dead_beef;
    let mut next = || {
        rng ^= rng << 13;
        rng ^= rng >> 7;
        rng ^= rng << 17;
        F::from_u32((rng % 2013265921) as u32)
    };
    let mut pts = String::new();
    let mut out = String::new();
    for (ti, t) in spec.tables.iter().enumerate() {
        let w = t.cols.len();
        for _ in 0..n {
            let sel = [next(), next(), next()];
            let cur: Vec<F> = (0..w).map(|_| next()).collect();
            let nxt: Vec<F> = (0..w).map(|_| next()).collect();
            let np = if JsonAir::reads_pub(t) { spec.num_pub } else { 0 };
            let pubs: Vec<F> = (0..np).map(|_| next()).collect();
            let j = |v: &[F]| v.iter().map(|x| x.as_canonical_u32().to_string()).collect::<Vec<_>>().join(" ");
            pts.push_str(&format!("{} {} | {} | {} | {}\n", ti, j(&sel), j(&cur), j(&nxt), j(&pubs)));
            let (cons, ints) = dag_eval(&vk, ti, &cur, &nxt, &pubs, sel);
            let cj: Vec<String> = cons.iter().map(|x| x.as_canonical_u32().to_string()).collect();
            let ij: Vec<String> = ints
                .iter()
                .map(|(b, c, m)| format!("[{},{},[{}]]", b, c.as_canonical_u32(), m.iter().map(|x| x.as_canonical_u32().to_string()).collect::<Vec<_>>().join(",")))
                .collect();
            out.push_str(&format!("{{\"t\":{ti},\"constraints\":[{}],\"inters\":[{}]}}\n", cj.join(","), ij.join(",")));
        }
    }
    std::fs::write(points_out, pts).unwrap();
    std::fs::write(rust_out, out).unwrap();
    println!("DIFFTEST points written: {} tables x {n}", spec.tables.len());
}

fn main() {
    let a: Vec<String> = std::env::args().collect();
    match a.get(1).map(|s| s.as_str()) {
        Some("check") => cmd_check(&a[2], &a[3]),
        Some("prove") => cmd_prove(&a[2], &a[3], a.get(4).map(|s| s.as_str()).unwrap_or("small")),
        Some("tamper") => cmd_tamper(&a[2], &a[3]),
        Some("difftest") => cmd_difftest(&a[2], &a[3], &a[4], a.get(5).map(|s| s.parse().unwrap()).unwrap_or(16)),
        _ => eprintln!("usage: see source header"),
    }
    let _: Option<RowMajorMatrix<F>> = None;
}
