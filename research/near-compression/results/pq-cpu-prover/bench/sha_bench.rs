//! lane/pq-cpu-prover: SHA-384 throughput, scalar (`sha2`) vs the 8-lane AVX-512 kernel.
//!   SHA_1T: one thread, 109-byte PoW messages (one compression each) and 768-byte coset leaves.
//!   GRIND:  PoW candidates/s at RAYON_NUM_THREADS (the T* wide message), both kernels; and the
//!           time of a full `grind_mb` at GRIND_BITS (default 24).
use openvm_recursion_circuit::sha384::{config::*, mb};
use p3_maybe_rayon::prelude::*;
use sha2::{Digest as _, Sha384};
use std::time::Instant;

fn main() {
    let st = [7u8; 48];
    let msg = pow_message(&st, &[0, 0]);
    let n = 2_000_000usize;
    // scalar
    let t = Instant::now();
    let mut acc = 0u8;
    for i in 0..n {
        let mut m = msg.clone();
        m[100..104].copy_from_slice(&(i as u32).to_le_bytes());
        acc ^= Sha384::digest(&m)[0];
    }
    let s = t.elapsed().as_secs_f64();
    println!("SHA_1T scalar len={} {:.2} M hashes/s ({acc})", msg.len(), n as f64 / s / 1e6);
    let t = Instant::now();
    let mut msgs = vec![msg.clone(); 8];
    for i in (0..n).step_by(8) {
        for (l, m) in msgs.iter_mut().enumerate() {
            m[100..104].copy_from_slice(&((i + l) as u32).to_le_bytes());
        }
        let refs: Vec<&[u8]> = msgs.iter().map(|m| m.as_slice()).collect();
        acc ^= mb::sha384_many(&refs)[3][0];
    }
    let s = t.elapsed().as_secs_f64();
    println!("SHA_1T mb8 len={} {:.2} M hashes/s ({acc}) mb_enabled={}", msg.len(), n as f64 / s / 1e6, mb::mb_enabled());
    for len in [768usize, 104] {
        let m0 = vec![0x5au8; len];
        let k = 400_000usize;
        let t = Instant::now();
        for i in 0..k {
            let mut m = m0.clone();
            m[0] = i as u8;
            acc ^= Sha384::digest(&m)[1];
        }
        let s1 = t.elapsed().as_secs_f64();
        let ms = vec![m0.clone(); 8];
        let t = Instant::now();
        for _ in 0..k / 8 {
            let refs: Vec<&[u8]> = ms.iter().map(|m| m.as_slice()).collect();
            acc ^= mb::sha384_many(&refs)[0][1];
        }
        let s2 = t.elapsed().as_secs_f64();
        let blocks = (len + 17).div_ceil(128);
        println!(
            "SHA_1T len={len} ({blocks} blocks) scalar {:.2} M compressions/s, mb8 {:.2} M compressions/s ({acc})",
            (k * blocks) as f64 / s1 / 1e6,
            (k * blocks) as f64 / s2 / 1e6
        );
    }
    // grind throughput
    let threads = current_num_threads();
    let cand = 1u32 << 24;
    let t = Instant::now();
    let c1 = (0..cand).into_par_iter().filter(|&w| pow_step(&st, &[0, w], 64).1).count();
    let s1 = t.elapsed().as_secs_f64();
    let t = Instant::now();
    let c2: usize = (0..cand / 8)
        .into_par_iter()
        .map(|g| {
            let ms: Vec<Vec<u8>> = (0..8).map(|l| pow_message(&st, &[0, 8 * g + l])).collect();
            let refs: Vec<&[u8]> = ms.iter().map(|m| m.as_slice()).collect();
            mb::sha384_many(&refs).iter().filter(|h| h[0] == 0 && h[1] == 0 && h[2] == 0 && h[3] == 0 && h[4] == 0 && h[5] == 0 && h[6] == 0 && h[7] == 0).count()
        })
        .sum();
    let s2 = t.elapsed().as_secs_f64();
    println!(
        "GRIND threads={threads} scalar(pow_step) {:.1} M/s, mb8 {:.1} M/s ({c1} {c2}); 2^32 mean: scalar {:.0} s, mb8 {:.0} s",
        cand as f64 / s1 / 1e6,
        cand as f64 / s2 / 1e6,
        4294967296.0 / (cand as f64 / s1),
        4294967296.0 / (cand as f64 / s2)
    );
    let bits: usize = std::env::var("GRIND_BITS").map(|v| v.parse().unwrap()).unwrap_or(24);
    let t = Instant::now();
    let w = grind_mb(&st, bits, true);
    println!("GRIND_MB bits={bits} witness={w:?} secs={:.2}", t.elapsed().as_secs_f64());
}
