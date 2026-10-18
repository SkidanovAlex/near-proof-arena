//! SHA-512/384 compression AIR v4 (two base-4 words per row, degree 9) on the pinned SWIRL
//! backend (SHA-384 transcript/Merkle hash, BabyBear Ext12, WHIR).
//!
//! Usage:
//!   nearproof-sha384-air4 selftest [n_random]     correctness + debug checker + negative tests
//!   nearproof-sha384-air4 negative                negative tests only
//!   nearproof-sha384-air4 shape                   keygen census (columns, next-row columns, DAG)
//!   nearproof-sha384-air4 prove <n_compressions>  real proof, sizes, timings
//! Proof profile via the same env vars as native_sha384_driver.rs
//! (NEARPROOF_N_STACK, NEARPROOF_K, NEARPROOF_LOG_BLOWUP, NEARPROOF_ALL_LIST,
//! NEARPROOF_QUERY_BITS, NEARPROOF_INTERACTION_LOG).
mod air;
mod reference;
mod trace;

use openvm_stark_backend::{
    AirRef, StarkEngine, SystemParams,
    prover::{AirProvingContext, ColMajorMatrix, CpuColMajorBackend, DeviceDataTransporter, ProvingContext},
    test_utils::test_system_params_small,
};
use p3_field::PrimeCharacteristicRing;
use std::sync::Arc;

#[allow(dead_code, clippy::all)]
mod config {
    use super::*;
    include!("../../../airbender/direct-wasm/native_sha384_config.rs");

    use crate::air::*;
    use crate::trace::*;
    use openvm_stark_backend::{
        air_builders::debug::{AirProofRawInput, debug_constraints_and_interactions},
        codec::Encode,
        keygen::types::MultiStarkProvingKey,
        soundness::SoundnessCalculator,
    };
    use p3_matrix::dense::RowMajorMatrix;

    pub const DEGREE: usize = crate::air::DEGREE;

    fn setting(name: &str, default: usize) -> usize {
        std::env::var(name).map(|s| s.parse().unwrap()).unwrap_or(default)
    }

    fn airs() -> Vec<AirRef<SC>> {
        vec![Arc::new(Sha512Air4), Arc::new(TableAir4), Arc::new(HarnessAir)]
    }

    fn to_f(v: &[u32]) -> Vec<F> {
        v.iter().map(|&x| F::from_u32(x)).collect()
    }

    pub struct Mats {
        pub main: RowMajorMatrix<F>,
        pub table: RowMajorMatrix<F>,
        pub harness: RowMajorMatrix<F>,
    }
    fn mats(t: &Traces) -> Mats {
        Mats {
            main: RowMajorMatrix::new(to_f(&t.main), WIDTH),
            table: RowMajorMatrix::new(to_f(&t.table), T_WIDTH),
            harness: RowMajorMatrix::new(to_f(&t.harness), H_WIDTH),
        }
    }

    /// Engine with the native SHA-384/Ext12 profile; heights up to 2^log_h.
    fn engine(log_h: usize) -> Engine {
        let n_stack = setting("NEARPROOF_N_STACK", log_h.saturating_sub(2).max(8));
        let k = setting("NEARPROOF_K", 3);
        let blowup = setting("NEARPROOF_LOG_BLOWUP", 2);
        assert!((8..=22).contains(&n_stack) && (1..=5).contains(&k) && (1..=8).contains(&blowup));
        assert!(2 + n_stack + blowup <= 27);
        assert!(2 + n_stack >= log_h, "trace height 2^{log_h} exceeds 2^(l_skip+n_stack)");
        let mut params = test_system_params_small(2, n_stack, k);
        let interaction_log = setting("NEARPROOF_INTERACTION_LOG", 27);
        assert!((20..=30).contains(&interaction_log));
        params.max_constraint_degree = DEGREE;
        params.logup.max_interaction_count = 1 << interaction_log;
        params.logup.pow_bits = 0;
        params.log_blowup = blowup;
        if setting("NEARPROOF_ALL_LIST", 1) == 1 {
            params.whir.proximity = openvm_stark_backend::WhirProximityStrategy::ListDecoding { m: 3 };
        }
        let bits = setting("NEARPROOF_QUERY_BITS", 268);
        params.whir = openvm_stark_backend::WhirConfig::new(
            params.log_blowup,
            params.l_skip + params.n_stack,
            openvm_stark_backend::WhirParams {
                k: params.whir.k,
                log_final_poly_len: params.log_final_poly_len(),
                proximity: params.whir.proximity,
                query_phase_pow_bits: 0,
                folding_pow_bits: 0,
                mu_pow_bits: 0,
            },
            bits,
        );
        println!(
            "PROFILE v4 degree={} n_stack={} k={} log_blowup={} queries={:?} interaction_log={}",
            DEGREE,
            n_stack,
            k,
            blowup,
            params.whir.rounds.iter().map(|r| r.num_queries).collect::<Vec<_>>(),
            interaction_log
        );
        Engine::new(params)
    }

    fn ctx(m: Mats) -> ProvingContext<CpuColMajorBackend<SC>> {
        ProvingContext::new(vec![
            (0, AirProvingContext::simple(ColMajorMatrix::from_row_major(&m.main), vec![])),
            (1, AirProvingContext::simple(ColMajorMatrix::from_row_major(&m.table), vec![])),
            (2, AirProvingContext::simple(ColMajorMatrix::from_row_major(&m.harness), vec![])),
        ])
    }

    /// Backend debug checker (constraints, then LogUp multiset balance); Err = panic message.
    fn check(pk: &MultiStarkProvingKey<SC>, airs: &[AirRef<SC>], m: &[&RowMajorMatrix<F>]) -> Result<(), String> {
        let inputs: Vec<AirProofRawInput<F>> = m
            .iter()
            .map(|mat| AirProofRawInput {
                cached_mains: vec![],
                common_main: Some(Arc::new((*mat).clone())),
                public_values: vec![],
            })
            .collect();
        let pks: Vec<_> = pk.per_air.iter().collect();
        std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| debug_constraints_and_interactions(airs, &pks, &inputs)))
            .map_err(|e| {
                e.downcast_ref::<String>().cloned().or_else(|| e.downcast_ref::<&str>().map(|s| s.to_string())).unwrap_or_default()
            })
    }

    fn sha_vectors() -> Vec<(String, [u64; 8], Vec<[u64; 16]>, Vec<u8>)> {
        use sha2::Digest;
        let mut v = Vec::new();
        let long: Vec<u8> = (0..200u32).map(|i| (i * 7 + 3) as u8).collect();
        for (name, msg) in [("abc", b"abc".to_vec()), ("empty", vec![]), ("200B", long)] {
            v.push((format!("sha384({name})"), SHA384_IV, pad_message(&msg), sha2::Sha384::digest(&msg).to_vec()));
            v.push((format!("sha512({name})"), SHA512_IV, pad_message(&msg), sha2::Sha512::digest(&msg).to_vec()));
        }
        v
    }

    pub fn selftest(n_random: usize) {
        let mut rng = Rng(0x9e3779b97f4a7c15);
        // 1. Native round function vs sha2 (sanity of the generator's reference).
        for _ in 0..10_000 {
            let c = rng.comp();
            assert_eq!(round_words(&c).out, sha2_compress(&c));
        }
        println!("SELFTEST native_reference_vs_sha2 pass=10000");
        // 2. Build a trace: known vectors (chained multi-block) + random compressions.
        let mut comps = Vec::new();
        let mut vec_checks = Vec::new();
        for (name, iv, blocks, digest) in sha_vectors() {
            let mut st = iv;
            let first = comps.len();
            for blk in &blocks {
                let c = Comp { h: st, block: *blk };
                st = sha2_compress(&c);
                comps.push(c);
            }
            vec_checks.push((name, first, blocks.len(), digest));
        }
        let n_vec = comps.len();
        for _ in 0..n_random {
            comps.push(rng.comp());
        }
        let t = gen_all(&comps);
        // 3. Outputs read back from the AIR trace equal sha2's compression.
        let mut ok = 0;
        for (s, c) in comps.iter().enumerate() {
            assert_eq!(trace_output(&t.main, s), sha2_compress(c), "compression {s}");
            ok += 1;
        }
        for (name, first, nb, digest) in &vec_checks {
            let mut st = comps[*first].h;
            for b in 0..*nb {
                assert_eq!(comps[first + b].h, st);
                st = trace_output(&t.main, first + b);
            }
            let bytes: Vec<u8> = st.iter().flat_map(|w| w.to_be_bytes()).collect();
            assert_eq!(&bytes[..digest.len()], &digest[..], "{name}");
            println!("SELFTEST vector {name} blocks={nb} digest_ok");
        }
        println!("SELFTEST trace_outputs_vs_sha2 pass={ok} (vectors {n_vec} + random {n_random})");
        // 4. Backend debug checker on the full trace.
        let log_h = t.main_height.trailing_zeros() as usize;
        let eng = engine(log_h.max(10));
        let airs = airs();
        let kt = std::time::Instant::now();
        let (pk, _vk) = eng.keygen(&airs);
        println!("KEYGEN_SECONDS {:.2}", kt.elapsed().as_secs_f64());
        print_airs(&pk);
        let m = mats(&t);
        let start = std::time::Instant::now();
        check(&pk, &airs, &[&m.main, &m.table, &m.harness]).expect("debug checker rejected honest trace");
        println!(
            "SELFTEST debug_checker pass rows={} compressions={} secs={:.1}",
            t.main_height,
            comps.len(),
            start.elapsed().as_secs_f64()
        );
        // 5. Negative tests on a small trace.
        negative(&pk, &airs);
    }

    /// Columns referenced at the next row (offset 1) anywhere in constraints or interactions.
    fn next_row_columns(p: &openvm_stark_backend::keygen::types::StarkProvingKey<SC>) -> usize {
        use openvm_stark_backend::air_builders::symbolic::{SymbolicExpressionNode, symbolic_variable::Entry};
        let mut cols = std::collections::BTreeSet::new();
        for node in &p.vk.symbolic_constraints.constraints.nodes {
            if let SymbolicExpressionNode::Variable(v) = node {
                if let Entry::Main { offset: 1, .. } = v.entry {
                    cols.insert(v.index);
                }
            }
        }
        cols.len()
    }

    fn print_airs(pk: &MultiStarkProvingKey<SC>) {
        for p in &pk.per_air {
            println!(
                "AIR {} next_row_cols={} width={:?} degree={} constraints={} interactions={} need_rot={} dag_nodes={}",
                p.air_name,
                next_row_columns(p),
                p.vk.params.width.main_widths(),
                p.vk.max_constraint_degree,
                p.vk.symbolic_constraints.constraints.constraint_idx.len(),
                p.vk.symbolic_constraints.interactions.len(),
                p.vk.params.need_rot,
                p.vk.symbolic_constraints.constraints.nodes.len()
            );
        }
    }

    pub fn shape() {
        let eng = engine(10);
        let airs = airs();
        let (pk, _) = eng.keygen(&airs);
        print_airs(&pk);
        println!("SHAPE rows_per_compression={} width={} cells_per_compression={}", ROWS, WIDTH, ROWS * WIDTH);
    }

    fn category(col: usize) -> &'static str {
        if col < D1 {
            "digits_s0"
        } else if col < XA {
            "digits_s1"
        } else if col < XA + 6 {
            "aux_lo"
        } else if col < XA + 12 {
            "aux_carry"
        } else if col < C_R {
            "aux_hi"
        } else if col == C_R {
            "row_index"
        } else if col == C_G {
            "global_row"
        } else {
            "kind"
        }
    }

    fn by(res: &Result<(), String>) -> &'static str {
        match res {
            Ok(()) => "-",
            Err(s) if s.contains("LogUp") => "bus",
            Err(_) => "constraint",
        }
    }

    pub fn negative(pk: &MultiStarkProvingKey<SC>, airs: &[AirRef<SC>]) {
        let w = WIDTH;
        let mut rng = Rng(0x1234_5678_9abc_def1);
        let comps: Vec<Comp> = (0..3).map(|_| rng.comp()).collect();
        let t = gen_all(&comps);
        let m = mats(&t);
        check(pk, airs, &[&m.main, &m.table, &m.harness]).expect("honest small trace");
        let prev_hook = std::panic::take_hook();
        std::panic::set_hook(Box::new(|_| {}));
        let mut stats: std::collections::BTreeMap<String, (usize, usize, usize, usize)> = Default::default();
        let mut undetected = Vec::new();
        // rows: trace row 0, every kind of segment 1 (first/middle/last of each block), the first
        // padding row, one in the middle, and the last row
        let mut rows: Vec<usize> = vec![0];
        rows.extend(
            [0usize, 1, 2, 3, 20, 38, 39, 40, 41, 42, 43, 44, 45, 60, 80, 81, 82, 83, 84, 87, 88, 90, 91, 92, 100, 115, 116,
             119, 120, 122, 123, 124, 125, 126, 127]
                .iter()
                .map(|r| ROWS + r),
        );
        rows.extend([3 * ROWS, (3 * ROWS + t.main_height) / 2, t.main_height - 1]);
        assert!(t.main[3 * ROWS * w..].iter().all(|&v| v == 0), "padding must be all zero");
        let mut run = |label: String, which: usize, idx: usize, nv: &dyn Fn(F) -> F| {
            let mut mm = match which {
                0 => m.main.clone(),
                1 => m.table.clone(),
                _ => m.harness.clone(),
            };
            mm.values[idx] = nv(mm.values[idx]);
            let res = match which {
                0 => check(pk, airs, &[&mm, &m.table, &m.harness]),
                1 => check(pk, airs, &[&m.main, &mm, &m.harness]),
                _ => check(pk, airs, &[&m.main, &m.table, &mm]),
            };
            let e = stats.entry(label.clone()).or_default();
            e.0 += 1;
            match res {
                Ok(()) => undetected.push(format!("{label} idx={idx}")),
                Err(msg) if msg.contains("LogUp") => e.2 += 1,
                Err(_) => e.1 += 1,
            }
            e.3 = e.1 + e.2;
        };
        for &gi in &rows {
            for col in 0..w {
                let digit = col < XA;
                let kindc = col == C_K1 || col == C_K2;
                if digit {
                    // two in-range edits per digit: low bit and top bit
                    run(format!("main/{}", category(col)), 0, gi * w + col, &|v| F::from_u32(v.as_canonical_u32() ^ 1));
                    run(format!("main/{}_topbit", category(col)), 0, gi * w + col, &|v| F::from_u32(v.as_canonical_u32() ^ 2));
                } else if kindc {
                    // kind digits: every other in-range value
                    for d in 1..KD as u32 {
                        run(format!("main/{}", category(col)), 0, gi * w + col, &|v| {
                            F::from_u32((v.as_canonical_u32() + d) % KD as u32)
                        });
                    }
                } else {
                    run(format!("main/{}", category(col)), 0, gi * w + col, &|v| v + F::ONE);
                }
            }
        }
        // Out-of-range digit: +4 (the polynomial range check must reject).
        for &gi in &rows {
            for col in [D0 + 3, D0 + 10, D1 + 17, D1 + ND - 1] {
                run("main/digit_out_of_range".into(), 0, gi * w + col, &|v| v + F::from_u32(4));
            }
        }
        for i in [0usize, 1, 41, 42, 43, 60, 81, 82, 83, 84, 100, 123, 124, 127] {
            for col in 0..T_WIDTH {
                run("table".into(), 1, i * T_WIDTH + col, &|v| if col < T_BITS { F::ONE - v } else { v + F::ONE });
            }
        }
        for i in [0usize, 3, 4, 11, 12, 15, 16, 47] {
            for col in 0..H_WIDTH {
                run("harness".into(), 2, i * H_WIDTH + col, &|v| v + F::ONE);
            }
        }
        // Consistent output forgery: flip an output bit AND the interface consumer's copy.
        {
            let mut mm = m.main.clone();
            let mut hh = m.harness.clone();
            let gi = ROWS + OB; // O_0 of compression 1: s1 = H'0
            let idx = gi * w + D1;
            let old = mm.values[idx].as_canonical_u32();
            mm.values[idx] = F::from_u32(old ^ 1);
            let hrow = 16 + 12; // compression 1, pair 12 = (H'0, H'1); limb 0 of H'0
            let d = if old & 1 == 1 { -F::ONE } else { F::ONE };
            hh.values[hrow * H_WIDTH + 2] += d;
            let res = check(pk, airs, &[&mm, &m.table, &hh]);
            println!("NEGATIVE consistent_output_forgery detected={} by={}", res.is_err(), by(&res));
        }
        // Constraint-consistent edits: each keeps every AIR constraint satisfied (in-range carry
        // or stored value), so only a bus can reject it.
        {
            let at = |r: usize, col: usize| (ROWS + r) * w + col;
            let x = |i: usize| XA + i;
            let edits: Vec<(&str, Vec<(usize, F)>)> = vec![
                ("A_out_residual_via_carry", vec![(at(10, x(8)), F::ONE)]),
                ("A_in_residual_via_carry", vec![(at(11, x(11)), F::ONE)]),
                ("A_stored_Y", vec![(at(12, x(2)), F::ONE)]),
                ("A_stored_d_in", vec![(at(13, x(5)), F::ONE)]),
                ("A_stored_W_forward", vec![(at(14, x(14)), F::ONE)]),
                ("E_hpp_K_fold", vec![(at(EB + 10, x(2)), F::ONE)]),
                ("E_hp_K_fold", vec![(at(EB + 11, x(5)), F::ONE)]),
                ("E_stored_L_out", vec![(at(EB + 12, x(14)), F::ONE)]),
                ("E_out_residual_via_carry", vec![(at(EB + 13, x(8)), F::ONE)]),
                ("E_in_residual_via_carry", vec![(at(EB + 14, x(11)), F::ONE)]),
                ("W_stored_V0", vec![(at(WB + 10, x(2)), F::ONE)]),
                ("W_stored_V1", vec![(at(WB + 11, x(5)), F::ONE)]),
                ("W_residual0_via_carry", vec![(at(WB + 12, x(8)), F::ONE)]),
                ("W_residual1_via_carry", vec![(at(WB + 13, x(11)), F::ONE)]),
                ("W_stored_d_forward", vec![(at(WB + 14, x(14)), F::ONE)]),
                ("FF_A0_via_carry", vec![(at(0, x(8)), F::ONE)]),
                ("FF_A41_stored_H", vec![(at(41, x(2)), F::ONE)]),
                ("FF_E0_via_carry", vec![(at(EB, x(11)), F::ONE)]),
                ("FF_E41_stored_H", vec![(at(EB + 41, x(5)), F::ONE)]),
            ];
            for (name, ed) in edits {
                let mut mm = m.main.clone();
                for (idx, dv) in ed {
                    mm.values[idx] += dv;
                }
                let res = check(pk, airs, &[&mm, &m.table, &m.harness]);
                println!("NEGATIVE_BUS {name} detected={} by={}", res.is_err(), by(&res));
            }
            // Range check: flip W[79] bit 63 (feeds only round 79, via the W_39 forward) and
            // re-solve the top carries of the W check (row W_38) and of the E check (row E_40)
            // to ∓1/2 mod p: every bus residual is unchanged, only the carry range check can
            // reject.
            {
                use p3_field::Field;
                let mut mm = m.main.clone();
                // W_79 = W_39.s0 (swapped slots), digit 31 holds bits 62, 63
                let idx = at(WB + 39, D0 + 31);
                let v = mm.values[idx].as_canonical_u32();
                let up = (v >> 1) & 1 == 0;
                mm.values[idx] = F::from_u32(v ^ 2);
                let half = F::from_u32(2).inverse();
                let d = if up { half } else { -half };
                // W check on row W_38 for W_79 = next.s0: carries X[9..12]; lhs limb 2 += 2^21
                mm.values[at(WB + 38, x(11))] -= d;
                // E check on row E_40 for round 79 (slot 1): carries X[9..12]; dW limb 2 += 2^21
                mm.values[at(EB + 40, x(11))] += d;
                let res = check(pk, airs, &[&mm, &m.table, &m.harness]);
                println!("NEGATIVE carry_range_half detected={} by={}", res.is_err(), by(&res));
            }
            // Padding region: a copy of a real row placed in the zero tail, a fake complete
            // compression segment right after the last real one (consistent trace, no consumer
            // messages), and the same segment one row further (not contiguous).
            {
                let mut mm = m.main.clone();
                let (src, dst) = (ROWS + 20, (3 * ROWS + t.main_height) / 2);
                for col in 0..w {
                    mm.values[dst * w + col] = mm.values[src * w + col];
                }
                let res = check(pk, airs, &[&mm, &m.table, &m.harness]);
                println!("NEGATIVE_PAD fake_real_row_in_padding detected={} by={}", res.is_err(), by(&res));
                let mut c4 = comps.clone();
                c4.push(rng.comp());
                let t4 = gen_all(&c4);
                let m4 = mats(&t4);
                let res = check(pk, airs, &[&m4.main, &m4.table, &m.harness]);
                println!("NEGATIVE_PAD fake_segment_after_last detected={} by={}", res.is_err(), by(&res));
                {
                    // the same 4-segment trace in a taller matrix, segment 3 shifted one row down
                    let h2 = 2 * t4.main_height;
                    let main2 = gen_main(&c4, h2);
                    let mut mm = RowMajorMatrix::new(to_f(&main2), w);
                    let seg = 3 * ROWS * w;
                    let block: Vec<F> = mm.values[seg..seg + ROWS * w].to_vec();
                    for v in &mut mm.values[seg..seg + (ROWS + 1) * w] {
                        *v = F::ZERO;
                    }
                    mm.values[seg + w..seg + (ROWS + 1) * w].copy_from_slice(&block);
                    let tab = RowMajorMatrix::new(to_f(&gen_table(&main2, h2)), T_WIDTH);
                    let res = check(pk, airs, &[&mm, &tab, &m.harness]);
                    println!("NEGATIVE_PAD fake_segment_after_gap detected={} by={}", res.is_err(), by(&res));
                }
            }
            // A different (input state, block) with a fully consistent AIR trace but the
            // consumer's original messages: only the interface bus can reject it.
            for (name, edit_iv) in [("interface_block_word", false), ("interface_input_state", true)] {
                let mut c2 = comps.clone();
                if edit_iv {
                    c2[1].h[5] ^= 1 << 17
                } else {
                    c2[1].block[9] ^= 1 << 40
                }
                let t2 = gen_all(&c2);
                let m2 = mats(&t2);
                let res = check(pk, airs, &[&m2.main, &m2.table, &m.harness]);
                println!("NEGATIVE_BUS {name} detected={} by={}", res.is_err(), by(&res));
            }
        }
        std::panic::set_hook(prev_hook);
        let mut total = (0, 0);
        for (k, (n, c, b, d)) in &stats {
            println!("NEGATIVE {k} mutations={n} detected={d} by_constraint={c} by_bus={b}");
            total.0 += n;
            total.1 += d;
        }
        println!("NEGATIVE total mutations={} detected={} undetected={}", total.0, total.1, undetected.len());
        for u in undetected.iter().take(50) {
            println!("UNDETECTED {u}");
        }
    }

    pub fn negative_main() {
        let eng = engine(10);
        let airs = airs();
        let (pk, _) = eng.keygen(&airs);
        print_airs(&pk);
        negative(&pk, &airs);
    }

    fn peak_rss_kib() -> u64 {
        std::fs::read_to_string("/proc/self/status")
            .ok()
            .and_then(|s| s.lines().find(|l| l.starts_with("VmHWM")).and_then(|l| l.split_whitespace().nth(1)?.parse().ok()))
            .unwrap_or(0)
    }

    pub fn prove(n: usize) {
        let mut rng = Rng(0xdead_beef_cafe_f00d ^ n as u64);
        let comps: Vec<Comp> = (0..n).map(|_| rng.comp()).collect();
        let tg = std::time::Instant::now();
        let t = gen_all(&comps);
        let tracegen = tg.elapsed().as_secs_f64();
        let log_h = t.main_height.trailing_zeros() as usize;
        let eng = engine(log_h);
        let airs = airs();
        let kt = std::time::Instant::now();
        let (pk, vk) = eng.keygen(&airs);
        println!("KEYGEN_SECONDS {:.2}", kt.elapsed().as_secs_f64());
        print_airs(&pk);
        let bound = SoundnessCalculator::calculate_from_vk(&vk);
        let target = setting("NEARPROOF_QUERY_BITS", 268) as f64;
        println!(
            "SOUNDNESS target={} total={:.1} logup={:.1} proximity={:.1} query={:.1}",
            target, bound.total_bits, bound.logup_bits, bound.whir_details.proximity_gaps_bits, bound.whir_details.query_bits
        );
        assert!(bound.total_bits >= target, "component budget failed; not proving this profile");
        println!(
            "SHAPE n={} main_rows_used={} main_height={} main_width={} cells_per_compression_dense={} table={}x{} harness={}x{}",
            n,
            n * ROWS,
            t.main_height,
            WIDTH,
            ROWS * WIDTH,
            ROWS,
            T_WIDTH,
            t.harness_height,
            H_WIDTH
        );
        let m = mats(&t);
        drop(t);
        let c = ctx(m);
        let d_pk = eng.device().transport_pk_to_device(&pk);
        let pt = std::time::Instant::now();
        let proof = eng.prove(&d_pk, c).map_err(|e| format!("{e:?}")).expect("prove");
        let prove_s = pt.elapsed().as_secs_f64();
        let vt = std::time::Instant::now();
        eng.verify(&vk, &proof).expect("verify");
        let verify_s = vt.elapsed().as_secs_f64();
        fn size<T: Encode>(x: &T) -> usize {
            let mut b = Vec::new();
            x.encode(&mut b).unwrap();
            b.len()
        }
        let mut bytes = Vec::new();
        proof.encode(&mut bytes).unwrap();
        println!(
            "PROOF_BYTES total={} gkr={} relations={} stacking={} whir={}",
            bytes.len(),
            size(&proof.gkr_proof),
            size(&proof.batch_constraint_proof),
            size(&proof.stacking_proof),
            size(&proof.whir_proof)
        );
        println!("TIMES tracegen_s={:.2} prove_s={:.2} verify_s={:.3}", tracegen, prove_s, verify_s);
        println!("PEAK_RSS_KIB {}", peak_rss_kib());
    }

    #[cfg(test)]
    mod tests {
        use super::*;
        #[test]
        fn outputs_and_checker_small() {
            let mut rng = Rng(7);
            let comps: Vec<Comp> = (0..20).map(|_| rng.comp()).collect();
            let t = gen_all(&comps);
            for (s, c) in comps.iter().enumerate() {
                assert_eq!(trace_output(&t.main, s), sha2_compress(c));
            }
            let eng = engine(12);
            let airs = airs();
            let (pk, _) = eng.keygen(&airs);
            let m = mats(&t);
            check(&pk, &airs, &[&m.main, &m.table, &m.harness]).unwrap();
            // one corrupted state bit must be rejected
            let mut bad = m.main.clone();
            let idx = (ROWS + 20) * WIDTH + D1 + 3;
            bad.values[idx] = F::from_u32(bad.values[idx].as_canonical_u32() ^ 1);
            let prev = std::panic::take_hook();
            std::panic::set_hook(Box::new(|_| {}));
            let r = check(&pk, &airs, &[&bad, &m.table, &m.harness]);
            std::panic::set_hook(prev);
            assert!(r.is_err());
        }

        /// Every lookback-bus receive of a segment row matches exactly one sender row of the same
        /// segment with that tag, and every sender's count equals its number of receivers; the
        /// K lookup windows pin exactly the E rows whose X[0..6] hold h'' and h'.
        #[test]
        fn bus_map_consistent() {
            use crate::air::*;
            use std::collections::BTreeMap;
            let mut recv: BTreeMap<(i64, u64), u64> = BTreeMap::new();
            let mut add = |r: i64, t: u64| {
                assert!((0..ROWS as i64).contains(&r), "receive key outside the segment");
                *recv.entry((r, t)).or_default() += 1;
            };
            for r in 0..ROWS {
                let z = roles(kind_of(r));
                let r = r as i64;
                if let Some((o, t)) = z.r1 {
                    add(r + o, t);
                }
                if let Some((o, t)) = z.r2 {
                    add(r + o, t);
                }
                if z.r_a {
                    add(r + 43, TP);
                }
                if z.r_e {
                    add(r - 43, TF);
                    add(r + 41, TF);
                }
                if z.r_w {
                    add(r - 3, TW7);
                }
                if let Some(o) = z.r_ff {
                    add(r + o, TP);
                }
            }
            let mut send: BTreeMap<(i64, u64), u64> = BTreeMap::new();
            for r in 0..ROWS {
                let z = roles(kind_of(r));
                for (t, m) in [
                    (TP, z.s_pair),
                    (T1, z.s_slot1_fwd as u64),
                    (TF, z.s_slot1_fwd as u64),
                    (TY, z.s_y as u64),
                    (TL, z.s_l as u64),
                    (TV, z.s_v as u64),
                    (TW7, z.s_w7 as u64),
                ] {
                    if m > 0 {
                        send.insert((r as i64, t), m);
                    }
                }
            }
            assert_eq!(recv, send, "lookback bus: receivers != senders");
            // K lookup in window (r, r + 1) pins row r + 1's X[0..6]; those rows are exactly E_1..E_40
            let pinned: Vec<usize> = (0..ROWS - 1).filter(|&r| roles(kind_of(r)).k_lookup).map(|r| r + 1).collect();
            let expect: Vec<usize> = (EB + 1..=EB + 40).collect();
            assert_eq!(pinned, expect);
            for r in 0..ROWS {
                let z = roles(kind_of(r));
                // X[0..6] is pinned by exactly one of {R1, the K lookup of the window before}
                let by_k = pinned.contains(&r);
                assert_eq!(z.x_lo, z.r1.is_some() || by_k, "row {r}");
                assert!(!(z.r1.is_some() && by_k), "row {r}");
                // the checks use X[6..12] as carries, X[12..15] only when received
                assert_eq!(z.x_mid, z.r_a || z.r_e || z.r_w || z.r_ff.is_some());
                assert_eq!(z.x_hi, z.r2.is_some());
            }
            // interface: 16 pairs per segment, indices 0..15 once each
            let mut idx: Vec<u64> = (0..ROWS).filter_map(iface_idx).collect();
            idx.sort();
            assert_eq!(idx, (0..16).collect::<Vec<_>>());
            for r in 0..ROWS {
                assert_eq!(iface_idx(r).is_some(), roles(kind_of(r)).iface, "row {r}");
            }
        }

        #[test]
        fn sign_polynomials_exact() {
            use crate::air::*;
            use p3_field::Field;
            let coef = sign_coefs::<F>();
            for v in 0..4u32 {
                let w = word::<F, F>(&coef, &[F::from_u32(v); ND]);
                for t in 0..2 {
                    let expect = if (v >> t) & 1 == 1 { -F::ONE } else { F::ONE };
                    assert_eq!(w.sg[t], expect, "digit {v} bit {t}");
                }
            }
            // limbs and Σ/σ/Ch/Maj of random words
            let mut rng = Rng(99);
            for _ in 0..200 {
                let (a, b2, c2) = (rng.next(), rng.next(), rng.next());
                let wv = |x: u64| word::<F, F>(&coef, &digits(x).map(F::from_u64));
                let (wa, wb, wc) = (wv(a), wv(b2), wv(c2));
                let lim = |x: u64| limbs(x).map(F::from_u64);
                assert_eq!(wa.limbs, lim(a));
                let one = F::ONE;
                let half = F::from_u32(2).inverse();
                assert_eq!(limbs_of_signs::<F, F>(&big_sigma0(&wa.sg), one), lim(bsig0(a)));
                assert_eq!(limbs_of_signs::<F, F>(&big_sigma1(&wa.sg), one), lim(bsig1(a)));
                assert_eq!(limbs_of_signs::<F, F>(&small_sigma0(&wa.sg), one), lim(ssig0(a)));
                assert_eq!(limbs_of_signs::<F, F>(&small_sigma1(&wa.sg), one), lim(ssig1(a)));
                assert_eq!(limbs_of_signs::<F, F>(&ch2(&wa.sg, &wb.sg, &wc.sg), half), lim(chf(a, b2, c2)));
                assert_eq!(limbs_of_signs::<F, F>(&maj2(&wa.sg, &wb.sg, &wc.sg), half), lim(majf(a, b2, c2)));
            }
        }
    }
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    match args.get(1).map(|s| s.as_str()) {
        Some("selftest") => config::selftest(args.get(2).map(|s| s.parse().unwrap()).unwrap_or(1000)),
        Some("negative") => config::negative_main(),
        Some("shape") => config::shape(),
        Some("prove") => config::prove(args[2].parse().unwrap()),
        _ => eprintln!("usage: selftest [n] | negative | shape | prove <n>"),
    }
}
