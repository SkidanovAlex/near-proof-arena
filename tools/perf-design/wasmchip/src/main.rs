//! Spike #1 (V3-PERF-DESIGN §9): register-form WASM chips on the np-udr-stark-v2 prover.
//!
//! ```text
//! wasmchip run <measured|loadchain|mem> <iters> [--prove] [--tamper]
//! wasmchip bench-hash [mib]
//! wasmchip bench-commit <log_n> <width> <log_blowup>
//! ```
//! All timings are on whatever CPUs the process is pinned to (run under
//! `nice -n 19 taskset -c 9,25`, RAYON_NUM_THREADS=2): contended, indicative only.
mod chips;
mod ext;
mod sha512;
mod sha512k;
mod v1;
mod wasm;

use std::time::Instant;

use npudr::aux::{AuxLayout, table_degree};
use npudr::field::{F, omega, shift};
use p3_field::PrimeCharacteristicRing;
use p3_matrix::Matrix;
use rayon::prelude::*;

fn main() {
    let a: Vec<String> = std::env::args().collect();
    match a.get(1).map(|s| s.as_str()) {
        Some("run") => run(&a[2], a[3].parse().unwrap(), a.iter().any(|s| s == "--prove"), a.iter().any(|s| s == "--tamper")),
        Some("bench-ext") => ext::bench_ext(),
        Some("sha") => sha(&a[2], a[3].parse().unwrap(), a.iter().any(|s| s == "--prove")),
        Some("run1") => run1(&a[2], a[3].parse().unwrap(), a.iter().any(|s| s == "--prove"), a.iter().any(|s| s == "--forge")),
        Some("bench-hash") => bench_hash(a.get(2).map(|s| s.parse().unwrap()).unwrap_or(256)),
        Some("bench-commit") => bench_commit(a[2].parse().unwrap(), a[3].parse().unwrap(), a[4].parse().unwrap()),
        _ => eprintln!("usage: see src/main.rs"),
    }
}

fn prog(name: &str, iters: u64) -> wasm::Prog {
    match name {
        "measured" => wasm::measured_loop(iters),
        "loadchain" => wasm::load_chain(iters, 16),
        "mem" => wasm::mem_loop(iters),
        _ => panic!("unknown program {name}"),
    }
}

fn run(name: &str, iters: u64, prove: bool, tamper: bool) {
    let p = prog(name, iters);
    let t0 = Instant::now();
    let (ops, loc, mem) = wasm::interpret(&p);
    let t_interp = t0.elapsed().as_secs_f64();
    let rp = wasm::translate(&p);
    let t1 = Instant::now();
    let run = wasm::execute(&rp, &p);
    let t_exec = t1.elapsed().as_secs_f64();
    // differential check: register machine == reference interpreter
    for (i, v) in loc.iter().enumerate() {
        let got = run.mem.cur.get(&(0, i as u32)).map(|x| wasm::unlimbs(&x.0)).unwrap_or(p.locals0[i]);
        assert_eq!(got, *v, "local {i} differs");
    }
    for (w, v) in &mem {
        let got = run.mem.cur.get(&(1, *w)).map(|x| wasm::unlimbs(&x.0) as u32).unwrap_or(*p.mem0.get(w).unwrap_or(&0));
        assert_eq!(got, *v, "memory word {w} differs");
    }
    let fee: u64 = run.final_state.2 as u64;
    assert_eq!(fee, ops, "gas units (block-level fees) must equal executed WASM ops");
    println!("program: {} | iterations {iters}", p.name);
    println!(
        "  WASM ops executed {ops} | register-form rows {} | ops/row {:.2} | static rows {} | gas units {fee} (= ops: OK) | locals+memory match reference: OK",
        run.steps.len(),
        ops as f64 / run.steps.len() as f64,
        rp.rows.len()
    );
    println!("  reference interpreter {:.3} s, register machine (recording accesses) {:.3} s", t_interp, t_exec);
    let t2 = Instant::now();
    let b = chips::build(&rp, &run);
    println!("  trace build {:.3} s", t2.elapsed().as_secs_f64());
    // self-check: constraints + buses
    let t3 = Instant::now();
    let mut bad = 0;
    for (t, tr) in b.air.tables.iter().zip(&b.traces) {
        let f = npudr::check::failing_constraints(t, tr, &[], 5);
        if !f.is_empty() {
            println!("  FAIL constraints in {}: {:?}", t.name, f);
            bad += f.len();
        }
    }
    let imb = npudr::check::bus_imbalance(&b.air, &b.traces, &[]);
    for i in imb.iter().take(5) {
        println!("  FAIL bus imbalance {:?}", i);
    }
    println!(
        "  honest trace: {} failing constraints, {} unbalanced bus messages ({:.2} s)",
        bad,
        imb.len(),
        t3.elapsed().as_secs_f64()
    );
    report(&b, ops);
    if prove {
        prove_verify(&b, "honest");
    }
    if tamper {
        tamper_tests(&b);
    }
}

/// Committed-cell accounting, per active row, under several backends (E = extension degree).
fn report(b: &chips::Built, ops: u64) {
    println!("\n  table        kind   active   padded   w   I  aux(GP) deg | W_eq(prover, padded) | per active row: GP/E=10  logUp-k2/E=10  GKR/E=10  multilin");
    let mut tot = [0f64; 7]; // main, fractions, weq_prover, gp10, logup10, gkr10, ml
    let mut fixed = [0f64; 7];
    for (i, t) in b.air.tables.iter().enumerate() {
        let w = t.width as f64;
        let ni = t.interactions.len() as f64;
        let aux = AuxLayout::new(t, 1).width() as f64;
        let d = table_degree(t, 1);
        let q = (d - 1) as f64;
        let h = b.traces[i].height() as f64;
        let act = b.active[i] as f64;
        let weq = (w + 8.0 * aux + 8.0 * q) * h;
        let e = 10.0;
        let gp = w + e * aux + e * q;
        let lu = w + e * ((ni / 2.0).ceil() + 1.0) + e * 2.0;
        let gkr = w + e * 2.0;
        let ml = w;
        println!(
            "  {:12} {:5} {:8} {:8} {:3} {:3} {:4} {:3} | {:20.0} | {:8.0} {:13.0} {:9.0} {:8.0}",
            t.name, b.kind[i], b.active[i], h as usize, t.width, t.interactions.len(), aux as usize, d, weq, gp, lu, gkr, ml
        );
        let v = [w * act, ni * act, weq, gp * act, lu * act, gkr * act, ml * act];
        let tgt = if b.kind[i] == "fixed" { &mut fixed } else { &mut tot };
        for j in 0..7 {
            tgt[j] += v[j];
        }
    }
    let o = ops as f64;
    println!("\n  per WASM op (chips + memory boundary, active rows; fixed lookup/code/io tables excluded):");
    println!(
        "    main cells {:.1} | bus fractions {:.1} | committed cells: GP(E=10) {:.1}, logUp-k2(E=10) {:.1}, GKR-logUp(E=10) {:.1}, multilinear {:.1} | prover-actual W_eq (E=8, GP, padded) {:.1}",
        tot[0] / o, tot[1] / o, tot[3] / o, tot[4] / o, tot[5] / o, tot[6] / o, tot[2] / o
    );
    println!(
        "  fixed tables (range16/pair/code/io; amortised over a segment): main {:.2} M cells, prover W_eq {:.2} M",
        fixed[0] / 1e6,
        fixed[2] / 1e6
    );
}

fn prove_verify(b: &chips::Built, label: &str) -> bool {
    let opts = npudr::prover::ProveOptions { verbose: false };
    let t0 = Instant::now();
    let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        npudr::prover::prove_bytes(&b.air, b.traces.clone(), &[], &[], &opts)
    }));
    let dt = t0.elapsed().as_secs_f64();
    let bytes = match r {
        Ok(Ok(v)) => v,
        Ok(Err(e)) => {
            println!("  [{label}] prover returned error after {dt:.1} s: {e}");
            return false;
        }
        Err(_) => {
            println!("  [{label}] prover panicked after {dt:.1} s");
            return false;
        }
    };
    let weq: f64 = b
        .air
        .tables
        .iter()
        .zip(&b.traces)
        .map(|(t, tr)| {
            (t.width + 8 * AuxLayout::new(t, 1).width() + 8 * (table_degree(t, 1) - 1)) as f64 * tr.height() as f64
        })
        .sum();
    let main: f64 = b.traces.iter().map(|t| (t.width() * t.height()) as f64).sum();
    let t1 = Instant::now();
    let v = npudr::verifier::verify(&b.air, &[], &[], &bytes);
    println!(
        "  [{label}] np-udr-stark-v2 params (BabyBear, Fp8, blowup 16, 216 queries, SHA-256 WH): prove {dt:.1} s | proof {} KB | committed W_eq {:.1} M ({:.2} M W_eq/s), main {:.1} M | Rust verify: {} ({:.2} s)",
        bytes.len() / 1024,
        weq / 1e6,
        weq / dt / 1e6,
        main / 1e6,
        if v.is_ok() { "ACCEPT".to_string() } else { format!("REJECT ({})", v.clone().unwrap_err()) },
        t1.elapsed().as_secs_f64()
    );
    v.is_ok()
}

fn tamper_tests(b: &chips::Built) {
    // T3: verifier-side: an honest proof with one byte flipped at several offsets must be rejected
    {
        let opts = npudr::prover::ProveOptions { verbose: false };
        let bytes = npudr::prover::prove_bytes(&b.air, b.traces.clone(), &[], &[], &opts).expect("honest proof");
        let mut rej = 0;
        let offs: Vec<usize> = (1..=16).map(|k| k * bytes.len() / 17).collect();
        for &o in &offs {
            let mut t = bytes.clone();
            t[o] ^= 0x01;
            if npudr::verifier::verify(&b.air, &[], &[], &t).is_err() {
                rej += 1;
            }
        }
        println!("\n  T3 (proof bytes, 1 bit flipped at {} spread offsets): rejected {rej}/{}", offs.len(), offs.len());
    }
    let alu = b.air.tables.iter().position(|t| t.name == "alu_ri" || t.name == "ld").expect("alu_ri or ld table");
    let names = &b.air.tables[alu].name;
    println!("\n  tamper tests on table {names}:");
    // T1: break an arithmetic/limb relation (constraint violation)
    {
        let mut tr = b.traces.clone();
        let w = tr[alu].width();
        let c = if names == "alu_ri" { 15 } else { 15 }; // a column inside the value block
        tr[alu].values[c] += F::ONE;
        let _ = w;
        let f = npudr::check::failing_constraints(&b.air.tables[alu], &tr[alu], &[], 3);
        let imb = npudr::check::bus_imbalance(&b.air, &tr, &[]).len();
        println!("    T1 (+1 on column {c} of row 0): failing constraints {:?}, unbalanced messages {imb}", f);
        let bb = chips::Built { air: b.air.clone(), traces: tr, active: b.active.clone(), kind: b.kind.clone() };
        let ok = prove_verify(&bb, "T1 tampered");
        println!("    T1 => {}", if ok { "UNSOUND: accepted" } else { "rejected (expected)" });
    }
    // T2: consistent local arithmetic but wrong memory value (bus-only violation):
    // alu_ri row 0 (an add or sub): bump the operand A limb 3 and the matching result limb.
    if names == "alu_ri" {
        let mut tr = b.traces.clone();
        let t = &b.air.tables[alu];
        let _ = t;
        // column layout of alu_ri: act pc ts fp u fee nxt sub aoff doff A0..3 I0..3 C0..3 ...
        let (a3, c3) = (10 + 3, 18 + 3);
        let sub = tr[alu].values[7];
        let (ca, cc) = (tr[alu].values[a3], tr[alu].values[c3]);
        // keep A3 + I3 + k2 = C3 + 2^16 k3 (add) or C3 + I3 + k2 = A3 + 2^16 k3 (sub): shift both by the same delta
        let delta = F::ONE;
        tr[alu].values[a3] = ca + delta;
        tr[alu].values[c3] = cc + delta;
        let _ = sub;
        let f = npudr::check::failing_constraints(&b.air.tables[alu], &tr[alu], &[], 3);
        let imb = npudr::check::bus_imbalance(&b.air, &tr, &[]).len();
        println!("    T2 (operand read != memory, arithmetic kept consistent): failing constraints {:?}, unbalanced messages {imb}", f);
        let bb = chips::Built { air: b.air.clone(), traces: tr, active: b.active.clone(), kind: b.kind.clone() };
        let ok = prove_verify(&bb, "T2 tampered");
        println!("    T2 => {}", if ok { "UNSOUND: accepted" } else { "rejected (expected)" });
    }
}

// ---------------------------------------------------------------------------------------
// micro-benchmarks
// ---------------------------------------------------------------------------------------

fn bench_hash(mib: usize) {
    use sha2::digest::generic_array::GenericArray;
    let nthreads = rayon::current_num_threads();
    let n512 = mib * (1 << 20) / 128;
    let n256 = mib * (1 << 20) / 64;
    let data: Vec<u8> = (0..mib * (1 << 20)).map(|i| (i * 2654435761usize >> 13) as u8).collect();
    // SHA-512 compression (= SHA-384 compression): single thread
    let blocks512: Vec<GenericArray<u8, sha2::digest::consts::U128>> =
        data.chunks(128).map(|c| GenericArray::clone_from_slice(c)).collect();
    let blocks256: Vec<GenericArray<u8, sha2::digest::consts::U64>> =
        data.chunks(64).map(|c| GenericArray::clone_from_slice(c)).collect();
    let mut st = [0x6a09e667f3bcc908u64, 0xbb67ae8584caa73b, 0x3c6ef372fe94f82b, 0xa54ff53a5f1d36f1, 0x510e527fade682d1, 0x9b05688c2b3e6c1f, 0x1f83d9abfb41bd6b, 0x5be0cd19137e2179];
    let t0 = Instant::now();
    sha2::compress512(&mut st, &blocks512);
    let d512 = t0.elapsed().as_secs_f64();
    let mut st2 = [0x6a09e667u32, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19];
    let t1 = Instant::now();
    sha2::compress256(&mut st2, &blocks256);
    let d256 = t1.elapsed().as_secs_f64();
    // parallel (independent streams)
    let t2 = Instant::now();
    blocks512.par_chunks(4096).for_each(|c| {
        let mut s = st;
        sha2::compress512(&mut s, c);
        std::hint::black_box(s);
    });
    let p512 = t2.elapsed().as_secs_f64();
    println!(
        "bench-hash ({mib} MiB; {nthreads} rayon threads): SHA-512/384 compression 1 thread {:.2} M/s ({:.0} MB/s), {nthreads} threads {:.2} M/s | SHA-256 compression (SHA-NI if available) 1 thread {:.2} M/s ({:.0} MB/s) [{:x}{:x}]",
        n512 as f64 / d512 / 1e6,
        (mib as f64 * 1.048576) / d512,
        n512 as f64 / p512 / 1e6,
        n256 as f64 / d256 / 1e6,
        (mib as f64 * 1.048576) / d256,
        st[0] & 0xff,
        st2[0] & 0xff
    );
}

/// Rate-1/2^lb LDE (iDFT + coset DFTs, cache-blocked `npudr::lde::CosetDft`) and a SHA-384
/// Merkle commitment of the LDE rows (one leaf per LDE row; binary tree, 48-byte nodes).
fn bench_commit(log_n: usize, w: usize, lb: usize) {
    use sha2::{Digest, Sha384};
    let n = 1usize << log_n;
    let tr: Vec<F> = (0..n * w)
        .into_par_iter()
        .map(|i| F::from_u64((i as u64).wrapping_mul(0x9e37_79b9_7f4a_7c15) >> 34))
        .collect();
    let cd = npudr::lde::CosetDft::new(log_n);
    let t0 = Instant::now();
    let mut coef = vec![F::ZERO; n * w];
    cd.idft(&tr, w, &mut coef);
    let t_idft = t0.elapsed().as_secs_f64();
    let nb = 1usize << lb;
    let mut lde = vec![F::ZERO; n * w * nb];
    let t1 = Instant::now();
    for (bi, blk) in lde.chunks_mut(n * w).enumerate() {
        let c = shift() * omega(log_n + lb).exp_u64(bi as u64);
        cd.eval(&coef, w, c, blk);
    }
    let t_lde = t1.elapsed().as_secs_f64();
    let t2 = Instant::now();
    let leaves: Vec<[u8; 48]> = lde
        .par_chunks(w)
        .map(|row| {
            let mut h = Sha384::new();
            h.update([0x01u8]);
            for v in row {
                use p3_field::PrimeField32;
                h.update(v.as_canonical_u32().to_le_bytes());
            }
            h.finalize().into()
        })
        .collect();
    let t_leaf = t2.elapsed().as_secs_f64();
    let t3 = Instant::now();
    let mut lvl = leaves;
    while lvl.len() > 1 {
        lvl = lvl
            .par_chunks(2)
            .map(|p| {
                let mut h = Sha384::new();
                h.update([0x02u8]);
                h.update(p[0]);
                h.update(p[1]);
                h.finalize().into()
            })
            .collect();
    }
    let t_node = t3.elapsed().as_secs_f64();
    let cells = (n * w) as f64;
    let tot = t_idft + t_lde + t_leaf + t_node;
    println!(
        "bench-commit 2^{log_n} x {w}, blowup 2^{lb} ({} threads): iDFT {:.3} s, coset DFTs {:.3} s, SHA-384 leaves {:.3} s, nodes {:.3} s | total {:.3} s = {:.1} ns/trace cell ({:.2} M trace cells/s); hashing share {:.0} % [{:02x}]",
        rayon::current_num_threads(),
        t_idft,
        t_lde,
        t_leaf,
        t_node,
        tot,
        tot / cells * 1e9,
        cells / tot / 1e6,
        100.0 * (t_leaf + t_node) / tot,
        lvl[0][0]
    );
}

// =========================================================================================
// v1 (spike #4): typed operand forms, channels, single-lookup timestamps, public binding,
// forged-proof tests
// =========================================================================================

fn prog1(name: &str, iters: u64) -> v1::Prog {
    match name {
        "measured" => v1::measured(iters),
        "loadchain" => v1::loadchain(iters, 16),
        "divchain" => v1::divchain(iters),
        "callchain" => v1::callchain(iters),
        "memmix" => v1::memmix(iters),
        "bulk" => v1::bulk(iters, 256),
        _ => panic!("unknown program {name}"),
    }
}

fn imbalance1(b: &v1::Built, traces: &[p3_matrix::dense::RowMajorMatrix<F>]) -> usize {
    let pubs = npudr::verifier::public_inputs(&b.air, &b.cb);
    let trs: Vec<(usize, &p3_matrix::dense::RowMajorMatrix<F>)> = traces.iter().enumerate().collect();
    (0..b.air.num_buses)
        .map(|bus| npudr::check::bus_imbalance_with_pub(&b.air, &trs, &pubs, &b.cb, bus).map(|v| v.len()).unwrap_or(usize::MAX / 64))
        .sum()
}

fn prove1(b: &v1::Built, traces: Vec<p3_matrix::dense::RowMajorMatrix<F>>, label: &str) -> Option<Vec<u8>> {
    let opts = npudr::prover::ProveOptions { verbose: false };
    let t0 = Instant::now();
    let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| npudr::prover::prove_bytes(&b.air, traces, &[], &b.cb, &opts)));
    let dt = t0.elapsed().as_secs_f64();
    match r {
        Ok(Ok(v)) => {
            let weq: f64 = b.air.tables.iter().zip(&b.traces).map(|(t, tr)| (t.width + 8 * AuxLayout::new(t, 1).width() + 8 * (table_degree(t, 1) - 1)) as f64 * tr.height() as f64).sum();
            let main: f64 = b.traces.iter().map(|t| (t.width() * t.height()) as f64).sum();
            println!("  [{label}] prover emitted a proof ({} KB) in {dt:.1} s | committed W_eq {:.1} M (Fp8, blowup 16, grand products) = {:.2} M W_eq/s; main {:.1} M cells", v.len() / 1024, weq / 1e6, weq / dt / 1e6, main / 1e6);
            Some(v)
        }
        Ok(Err(e)) => {
            println!("  [{label}] prover refused after {dt:.1} s: {e}");
            None
        }
        Err(_) => {
            println!("  [{label}] prover panicked after {dt:.1} s");
            None
        }
    }
}

fn verify1(b: &v1::Built, cb: &[u8], bytes: &[u8]) -> Result<(), String> {
    npudr::verifier::verify(&b.air, &[], cb, bytes)
}

fn col(b: &v1::Built, t: usize, n: &str) -> usize {
    b.names[t].iter().position(|x| x == n).unwrap_or_else(|| panic!("no column {n} in {}", b.air.tables[t].name))
}

fn set_env(k: &str, v: &str) {
    // SAFETY: single-threaded at this point (rayon pools idle between proofs)
    unsafe { std::env::set_var(k, v) }
}
fn clear_env() {
    unsafe {
        std::env::remove_var("NPUDR_FORGE");
        std::env::remove_var("NPUDR_FORGE_BUS");
    }
}

fn run1(name: &str, iters: u64, prove: bool, forge: bool) {
    let p = prog1(name, iters);
    let t0 = Instant::now();
    let rf = v1::interpret(&p);
    let t_int = t0.elapsed().as_secs_f64();
    let rp = v1::translate(&p);
    let t1 = Instant::now();
    let run = v1::execute(&rp, &p);
    let t_exec = t1.elapsed().as_secs_f64();
    // differential: entry-frame locals and memory vs the reference interpreter; gas
    for (i, v) in rf.locals0.iter().enumerate() {
        let got = run.mem.get(&(v1::SP_LOCAL, i as u32)).map(|x| v1::unl(&x.0)).unwrap_or(*p.args.get(i).unwrap_or(&0));
        assert_eq!(got, *v, "local {i} differs");
    }
    let mut mem = p.mem0.clone();
    mem.resize(v1::MEMB, 0);
    for ((sp, w), (l, _)) in &run.mem {
        if *sp == v1::SP_MEM && ((*w as usize) + 1) * 4 <= v1::MEMB {
            let v = (v1::unl(l) as u32).to_le_bytes();
            mem[4 * *w as usize..4 * *w as usize + 4].copy_from_slice(&v);
        }
    }
    assert!(mem == rf.mem, "memory differs from the reference");
    assert_eq!(run.final_state.3 as u64, rf.gas, "gas differs");
    println!("program: {} | iterations {iters}", p.name);
    println!(
        "  WASM ops {} (gas units {}) | rows {} | ops/row {:.2} | static rows {} | locals, memory, gas == reference: OK | channel discipline: OK",
        rf.ops,
        rf.gas,
        run.steps.len(),
        rf.ops as f64 / run.steps.len() as f64,
        rp.rows.len()
    );
    println!("  reference interpreter {t_int:.3} s, register machine {t_exec:.3} s ({:.1} M rows/s, {:.1} M ops/s)", run.steps.len() as f64 / t_exec / 1e6, rf.ops as f64 / t_exec / 1e6);
    let t2 = Instant::now();
    let b = v1::build(&rp, &run);
    println!("  trace build {:.3} s", t2.elapsed().as_secs_f64());
    let mut bad = 0;
    for (t, tr) in b.air.tables.iter().zip(&b.traces) {
        let f = npudr::check::failing_constraints(t, tr, &npudr::verifier::public_inputs(&b.air, &b.cb), 3);
        if !f.is_empty() {
            println!("  FAIL constraints in {}: {:?}", t.name, f);
            bad += f.len();
        }
    }
    let imb = imbalance1(&b, &b.traces);
    println!("  honest trace: {bad} failing constraints, {imb} unbalanced bus messages (public segments included)");
    report1(&b, rf.ops, rf.gas);
    if !prove {
        return;
    }
    clear_env();
    let Some(bytes) = prove1(&b, b.traces.clone(), "honest") else { return };
    println!("  [honest] verify: {:?}", verify1(&b, &b.cb, &bytes).map(|_| "ACCEPT"));
    // public binding: the same proof against a modified claim must be rejected
    let n_code = u32::from_le_bytes(b.cb[0..4].try_into().unwrap()) as usize;
    let off_code = u32::from_le_bytes(b.cb[4..8].try_into().unwrap()) as usize;
    let off_mem = u32::from_le_bytes(b.cb[12..16].try_into().unwrap()) as usize;
    let off_io = u32::from_le_bytes(b.cb[20..24].try_into().unwrap()) as usize;
    let mut cases: Vec<(&str, Vec<u8>)> = vec![];
    let mut c = b.cb.clone();
    c[off_code + (n_code / 2) * v1::CODE_REC + 6] ^= 1; // an immediate byte of a mid code row
    cases.push(("code byte", c));
    if off_io > off_mem {
        let mut c = b.cb.clone();
        c[off_mem + 5] ^= 1; // first initial memory word's value
        cases.push(("initial memory word", c));
    }
    let mut c = b.cb.clone();
    c[off_io + 28 + 12] ^= 1; // final u (gas)
    cases.push(("final gas", c));
    for (what, c) in cases {
        let r = verify1(&b, &c, &bytes);
        println!("  B (claim: {what} flipped, honest proof): {}", if r.is_err() { format!("rejected ({})", r.unwrap_err()) } else { "ACCEPTED: UNSOUND".into() });
    }
    if !forge {
        return;
    }
    // forged proofs: dishonest traces committed by the forging prover
    let alu = b.air.tables.iter().position(|t| t.name.starts_with("alu_ri")).expect("an alu_ri table");
    let w = b.traces[alu].width();
    let mut t_constraint = b.traces.clone();
    t_constraint[alu].values[col(&b, alu, "C0")] += F::ONE; // result limb +1 (row 0)
    let mut t_bus = b.traces.clone();
    // a consistent-arithmetic lie about the value read (bus-only violation): +1 on A0 and C0 of row 0
    let (ca, cc) = (col(&b, alu, "A0"), col(&b, alu, "C0"));
    if b.names[alu].iter().any(|n| n == "a_t") || true {
        t_bus[alu].values[ca] += F::ONE;
        t_bus[alu].values[cc] += F::ONE;
    }
    let _ = w;
    let tests: Vec<(&str, Vec<p3_matrix::dense::RowMajorMatrix<F>>, &str, &str)> = vec![
        ("F1 constraint violation, naive forger", t_constraint.clone(), "1", "0"),
        ("F2 constraint violation, OOD-consistent forger", t_constraint, "2", "0"),
        ("F3 bus violation, naive forger", t_bus.clone(), "1", "0"),
        ("F4 bus violation, finals balanced + OOD-consistent forger", t_bus, "2", "1"),
    ];
    // F5: an honest trace proved against a claim with a different final gas (forger balances the
    // bus products and patches the OOD quotient values)
    {
        let mut c = b.cb.clone();
        let off_io = u32::from_le_bytes(c[20..24].try_into().unwrap()) as usize;
        c[off_io + 28 + 12] ^= 1;
        let bb = v1::Built { air: b.air.clone(), traces: vec![], active: vec![], kind: vec![], names: vec![], cb: c };
        set_env("NPUDR_FORGE", "2");
        set_env("NPUDR_FORGE_BUS", "1");
        let pr = prove1(&bb, b.traces.clone(), "F5 claim mismatch (final gas)");
        clear_env();
        if let Some(bytes) = pr {
            let r = verify1(&bb, &bb.cb, &bytes);
            println!("  F5 claim mismatch (honest trace, final gas flipped in the claim), forger -> verifier {}", if r.is_err() { format!("REJECTS ({})", r.unwrap_err()) } else { "ACCEPTS: UNSOUND".into() });
        }
    }
    for (what, tr, m, bus) in tests {
        let nf: usize = npudr::check::failing_constraints(&b.air.tables[alu], &tr[alu], &[], 3).len();
        let ni = imbalance1(&b, &tr);
        set_env("NPUDR_FORGE", m);
        set_env("NPUDR_FORGE_BUS", bus);
        let pr = prove1(&b, tr, what);
        clear_env();
        match pr {
            Some(bytes) => {
                let r = verify1(&b, &b.cb, &bytes);
                println!(
                    "  {what}: trace has {nf} failing constraint(s), {ni} unbalanced message(s) -> verifier {}",
                    if r.is_err() { format!("REJECTS ({})", r.unwrap_err()) } else { "ACCEPTS: UNSOUND".into() }
                );
            }
            None => println!("  {what}: forger produced no proof"),
        }
    }
}

fn report1(b: &v1::Built, ops: u64, gas: u64) {
    println!("\n  table                  kind   active   padded   w   I | per active row: committed U-logUp(E=10)  GKR  ML");
    let (mut main, mut fr, mut lu, mut gkr) = (0f64, 0f64, 0f64, 0f64);
    let mut fixed = 0f64;
    for (i, t) in b.air.tables.iter().enumerate() {
        let w = t.width as f64;
        let ni = t.interactions.len() as f64;
        let act = b.active[i] as f64;
        let e = 10.0;
        let l = w + e * ((ni / 2.0).ceil() + 1.0) + e * 2.0;
        let g = w + e * 2.0;
        println!("  {:22} {:5} {:8} {:8} {:3} {:3} | {:28.0} {:4.0} {:3.0}", t.name, b.kind[i], b.active[i], b.traces[i].height(), t.width, t.interactions.len(), l, g, w);
        if b.kind[i] == "fixed" {
            fixed += w * b.traces[i].height() as f64;
        } else {
            main += w * act;
            fr += ni * act;
            lu += l * act;
            gkr += g * act;
        }
    }
    let o = ops as f64;
    println!(
        "\n  per WASM op (chips + memory boundary; fixed tables excluded): main {:.1} | fractions {:.1} | committed U-logUp {:.1}, U-GKR {:.1}, ML {:.1} | per gas unit: main {:.2}, fractions {:.2}",
        main / o, fr / o, lu / o, gkr / o, main / o, main / gas as f64, fr / gas as f64
    );
    println!("  fixed tables (code/io/minit/range16/rangeT/pair8): {:.2} M main cells", fixed / 1e6);
}

fn sha(which: &str, nblk: usize, prove: bool) {
    let sp = if which == "256" { sha512::SHA256 } else { sha512::SHA384 };
    let t0 = Instant::now();
    let b = sha512::build(sp, nblk, 0x1234_5678_9abc_def1);
    println!("{} compression AIR: {nblk} compressions, reference == sha2 crate: OK | build {:.2} s", sp.name, t0.elapsed().as_secs_f64());
    let mut bad = 0;
    for (t, tr) in b.air.tables.iter().zip(&b.traces) {
        let f = npudr::check::failing_constraints(t, tr, &[], 3);
        if !f.is_empty() {
            println!("  FAIL constraints in {}: {:?}", t.name, f);
            bad += f.len();
        }
    }
    let imb = npudr::check::bus_imbalance(&b.air, &b.traces, &[]).len();
    println!("  honest trace: {bad} failing constraints, {imb} unbalanced bus messages");
    let (mut cells, mut fr, mut lu) = (0f64, 0f64, 0f64);
    let e = 10.0;
    for (i, t) in b.air.tables.iter().enumerate() {
        let rows_per = b.rows_per[i] as f64;
        let deg = npudr::aux::table_degree(t, 1);
        let pre = if i < 2 { b.preprocessed[i] } else { 0 };
        println!(
            "  {:11} w {:4} (preprocessed {:2}) | interactions {:2} | degree {} | rows/compression {:3} | main cells/compression {:7.0}",
            t.name, t.width, pre, t.interactions.len(), deg, rows_per, t.width as f64 * rows_per
        );
        if i < 3 {
            let ni = t.interactions.len() as f64;
            cells += (t.width - pre) as f64 * rows_per;
            fr += ni * rows_per;
            lu += rows_per * (e * ((ni / 2.0).ceil() + 1.0) + e * 2.0);
        }
    }
    let committed = cells + lu;
    let work = committed + fr * 6.3;
    println!(
        "  per compression ({} B; rounds + sched + final; input and preprocessed columns excluded): main {:.0} cells, {:.0} fraction slots | committed U-logUp (E=10, degree-3 target) {:.0} | work cell-eq {:.0} | per byte: main {:.0}, work {:.0}",
        b.bytes_per_block, cells, fr, committed, work, cells / b.bytes_per_block as f64, work / b.bytes_per_block as f64
    );
    if !prove {
        return;
    }
    let opts = npudr::prover::ProveOptions { verbose: false };
    let t1 = Instant::now();
    let bytes = npudr::prover::prove_bytes(&b.air, b.traces.clone(), &[], &[], &opts).expect("honest proof");
    let dt = t1.elapsed().as_secs_f64();
    let r = npudr::verifier::verify(&b.air, &[], &[], &bytes);
    println!("  [honest] prove {dt:.1} s, proof {} KB, verify {:?}", bytes.len() / 1024, r.map(|_| "ACCEPT"));
    let mut tr = b.traces.clone();
    let wr = tr[0].width();
    let c = b.a0_col;
    tr[0].values[10 * wr + c] = F::ONE - tr[0].values[10 * wr + c];
    let nf = npudr::check::failing_constraints(&b.air.tables[0], &tr[0], &[], 3).len();
    set_env("NPUDR_FORGE", "2");
    let fb = npudr::prover::prove_bytes(&b.air, tr, &[], &[], &opts);
    clear_env();
    match fb {
        Ok(fb) => {
            let r = npudr::verifier::verify(&b.air, &[], &[], &fb);
            println!("  [forged: one state bit flipped ({nf} failing constraint(s)), OOD-consistent forger] verifier {}", if r.is_err() { format!("REJECTS ({})", r.unwrap_err()) } else { "ACCEPTS: UNSOUND".into() });
        }
        Err(e) => println!("  forger produced no proof: {e}"),
    }
}
