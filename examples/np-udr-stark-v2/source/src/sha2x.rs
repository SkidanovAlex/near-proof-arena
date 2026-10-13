//! SHA-256 compression of the same blocks into two states at once.
//!
//! The wide hash `WH(tag, m) = H(tag‖1‖m) ‖ H(tag‖2‖m)` compresses every
//! block after the first into two states. With SHA-NI the two compressions
//! share the message schedule and their `sha256rnds2` dependency chains are
//! interleaved (each chain alone is latency-bound). Bit for bit the same as
//! two calls of `sha2::compress256` (tested); falls back to them without
//! SHA-NI.

/// `a ← compress(a, blocks)`, `b ← compress(b, blocks)`.
#[inline]
pub fn compress_pair(a: &mut [u32; 8], b: &mut [u32; 8], blocks: &[[u8; 64]]) {
    #[cfg(target_arch = "x86_64")]
    {
        if shani() {
            // SAFETY: the CPU supports the enabled features (checked above).
            unsafe { x86::compress_pair(a, b, blocks) };
            return;
        }
    }
    use sha2::digest::generic_array::GenericArray;
    for blk in blocks {
        let g = GenericArray::from_slice(blk);
        sha2::compress256(a, std::slice::from_ref(g));
        sha2::compress256(b, std::slice::from_ref(g));
    }
}

#[cfg(target_arch = "x86_64")]
fn shani() -> bool {
    use std::sync::OnceLock;
    static S: OnceLock<bool> = OnceLock::new();
    *S.get_or_init(|| {
        std::arch::is_x86_feature_detected!("sha")
            && std::arch::is_x86_feature_detected!("sse2")
            && std::arch::is_x86_feature_detected!("ssse3")
            && std::arch::is_x86_feature_detected!("sse4.1")
    })
}

#[cfg(target_arch = "x86_64")]
mod x86 {
    use core::arch::x86_64::*;

    const K32: [u32; 64] = [
        0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4,
        0xab1c5ed5, 0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe,
        0x9bdc06a7, 0xc19bf174, 0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f,
        0x4a7484aa, 0x5cb0a9dc, 0x76f988da, 0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7,
        0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967, 0x27b70a85, 0x2e1b2138, 0x4d2c6dfc,
        0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85, 0xa2bfe8a1, 0xa81a664b,
        0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070, 0x19a4c116,
        0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
        0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7,
        0xc67178f2,
    ];

    #[inline(always)]
    unsafe fn schedule(v0: __m128i, v1: __m128i, v2: __m128i, v3: __m128i) -> __m128i {
        let t1 = _mm_sha256msg1_epu32(v0, v1);
        let t2 = _mm_alignr_epi8(v3, v2, 4);
        let t3 = _mm_add_epi32(t1, t2);
        _mm_sha256msg2_epu32(t3, v3)
    }

    /// Four rounds on both states with the same message words.
    macro_rules! rounds4 {
        ($a0:ident, $c0:ident, $a1:ident, $c1:ident, $w:expr, $i:expr) => {{
            let kv = _mm_set_epi32(
                K32[4 * $i + 3] as i32,
                K32[4 * $i + 2] as i32,
                K32[4 * $i + 1] as i32,
                K32[4 * $i] as i32,
            );
            let t1 = _mm_add_epi32($w, kv);
            $c0 = _mm_sha256rnds2_epu32($c0, $a0, t1);
            $c1 = _mm_sha256rnds2_epu32($c1, $a1, t1);
            let t2 = _mm_shuffle_epi32(t1, 0x0E);
            $a0 = _mm_sha256rnds2_epu32($a0, $c0, t2);
            $a1 = _mm_sha256rnds2_epu32($a1, $c1, t2);
        }};
    }

    #[inline(always)]
    unsafe fn load(s: &[u32; 8]) -> (__m128i, __m128i) {
        let p = s.as_ptr() as *const __m128i;
        let dcba = _mm_loadu_si128(p);
        let efgh = _mm_loadu_si128(p.add(1));
        let cdab = _mm_shuffle_epi32(dcba, 0xB1);
        let efgh = _mm_shuffle_epi32(efgh, 0x1B);
        (
            _mm_alignr_epi8(cdab, efgh, 8),
            _mm_blend_epi16(efgh, cdab, 0xF0),
        )
    }

    #[inline(always)]
    unsafe fn store(s: &mut [u32; 8], abef: __m128i, cdgh: __m128i) {
        let feba = _mm_shuffle_epi32(abef, 0x1B);
        let dchg = _mm_shuffle_epi32(cdgh, 0xB1);
        let dcba = _mm_blend_epi16(feba, dchg, 0xF0);
        let hgef = _mm_alignr_epi8(dchg, feba, 8);
        let p = s.as_mut_ptr() as *mut __m128i;
        _mm_storeu_si128(p, dcba);
        _mm_storeu_si128(p.add(1), hgef);
    }

    #[target_feature(enable = "sha,sse2,ssse3,sse4.1")]
    pub unsafe fn compress_pair(a: &mut [u32; 8], b: &mut [u32; 8], blocks: &[[u8; 64]]) {
        let mask = _mm_set_epi64x(
            0x0C0D_0E0F_0809_0A0Bu64 as i64,
            0x0405_0607_0001_0203u64 as i64,
        );
        let (mut a0, mut c0) = load(a);
        let (mut a1, mut c1) = load(b);
        for block in blocks {
            let (sa0, sc0, sa1, sc1) = (a0, c0, a1, c1);
            let d = block.as_ptr() as *const __m128i;
            let mut w0 = _mm_shuffle_epi8(_mm_loadu_si128(d), mask);
            let mut w1 = _mm_shuffle_epi8(_mm_loadu_si128(d.add(1)), mask);
            let mut w2 = _mm_shuffle_epi8(_mm_loadu_si128(d.add(2)), mask);
            let mut w3 = _mm_shuffle_epi8(_mm_loadu_si128(d.add(3)), mask);
            let mut w4;
            rounds4!(a0, c0, a1, c1, w0, 0);
            rounds4!(a0, c0, a1, c1, w1, 1);
            rounds4!(a0, c0, a1, c1, w2, 2);
            rounds4!(a0, c0, a1, c1, w3, 3);
            w4 = schedule(w0, w1, w2, w3);
            rounds4!(a0, c0, a1, c1, w4, 4);
            w0 = schedule(w1, w2, w3, w4);
            rounds4!(a0, c0, a1, c1, w0, 5);
            w1 = schedule(w2, w3, w4, w0);
            rounds4!(a0, c0, a1, c1, w1, 6);
            w2 = schedule(w3, w4, w0, w1);
            rounds4!(a0, c0, a1, c1, w2, 7);
            w3 = schedule(w4, w0, w1, w2);
            rounds4!(a0, c0, a1, c1, w3, 8);
            w4 = schedule(w0, w1, w2, w3);
            rounds4!(a0, c0, a1, c1, w4, 9);
            w0 = schedule(w1, w2, w3, w4);
            rounds4!(a0, c0, a1, c1, w0, 10);
            w1 = schedule(w2, w3, w4, w0);
            rounds4!(a0, c0, a1, c1, w1, 11);
            w2 = schedule(w3, w4, w0, w1);
            rounds4!(a0, c0, a1, c1, w2, 12);
            w3 = schedule(w4, w0, w1, w2);
            rounds4!(a0, c0, a1, c1, w3, 13);
            w4 = schedule(w0, w1, w2, w3);
            rounds4!(a0, c0, a1, c1, w4, 14);
            w0 = schedule(w1, w2, w3, w4);
            rounds4!(a0, c0, a1, c1, w0, 15);
            a0 = _mm_add_epi32(a0, sa0);
            c0 = _mm_add_epi32(c0, sc0);
            a1 = _mm_add_epi32(a1, sa1);
            c1 = _mm_add_epi32(c1, sc1);
        }
        store(a, a0, c0);
        store(b, a1, c1);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use sha2::digest::generic_array::GenericArray;

    #[test]
    fn pair_matches_sha2() {
        let mut blocks = vec![[0u8; 64]; 7];
        for (i, b) in blocks.iter_mut().enumerate() {
            for (j, x) in b.iter_mut().enumerate() {
                *x = (i * 131 + j * 17 + 5) as u8;
            }
        }
        for n in 0..=blocks.len() {
            let mut a = [1u32, 2, 3, 4, 5, 6, 7, 8];
            let mut b = [
                0x6a09e667u32,
                0xbb67ae85,
                0x3c6ef372,
                0xa54ff53a,
                9,
                10,
                11,
                12,
            ];
            let (mut ra, mut rb) = (a, b);
            for blk in &blocks[..n] {
                let g = GenericArray::from_slice(blk);
                sha2::compress256(&mut ra, std::slice::from_ref(g));
                sha2::compress256(&mut rb, std::slice::from_ref(g));
            }
            compress_pair(&mut a, &mut b, &blocks[..n]);
            assert_eq!((a, b), (ra, rb), "{n} blocks");
        }
    }
}
