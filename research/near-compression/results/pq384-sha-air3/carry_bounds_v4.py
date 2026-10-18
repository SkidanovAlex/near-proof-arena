"""Exact integer ranges of every limb equation of SHA AIR v4 (FAITHFUL-v4.md C6).

Each addition check of v4 is a bus residual: the receiver's field element
    R_i = out_i + 2^{w_i}(c_i - off) - (c_{i-1} - off) - (operand limbs)          (or the FF form)
must equal the sender's field element S_i.  Write E_i = R_i - S_i, evaluated over the integers
with every operand replaced by its integer value (digits are 0..3 by C1, so limbs of words and of
Σ/σ/Ch/Maj sign forms are integers in [0, 2^w); stored cells equal, mod p, the integer their
sender's expression takes; carries are 0..7).  If max|E_i| < p then E_i ≡ 0 (mod p) forces
E_i = 0 over Z, and the telescoped sum gives the 64-bit addition mod 2^64.

Also checks completeness: the honest carries (from random SHA-512 compressions run through the
v4 equations) lie inside [0, 8) after their offsets.

Usage: python3 -I carry_bounds_v4.py
"""
import random

P = 2013265921
W = (21, 21, 22)
CR = 8  # carry range [0, 8)


def rng_word(w):
    return (0, (1 << w) - 1)


def add(*iv):
    return (sum(a for a, _ in iv), sum(b for _, b in iv))


def neg(iv):
    return (-iv[1], -iv[0])


def scale(iv, k):
    a, b = iv[0] * k, iv[1] * k
    return (min(a, b), max(a, b))


def lhs_terms(i, off, out=True):
    """out_i + 2^w (c_i - off) - (c_{i-1} - off), carries in [0, CR)."""
    w = W[i]
    terms = [rng_word(w) if out else (0, 0), scale((-off, CR - 1 - off), 1 << w)]
    if i > 0:
        terms.append(neg((-off, CR - 1 - off)))
    return terms


def word(i, n=1):
    return scale(rng_word(W[i]), n)


CHECKS = {
    # name: (offset, operand intervals subtracted, sender interval S, note)
    'A out: a = e + (M - d)   [Y = Σ0 + Maj - d stored]': (4, lambda i: [add(word(i, 2), neg(word(i)))], lambda i: word(i)),
    'A in:  a = e + M_in - d_in': (4, lambda i: [word(i, 2), neg(word(i))], lambda i: word(i)),
    'E out: e = (h + K) + (Σ1 + Ch) + (d + W)': (0, lambda i: [word(i, 2), word(i, 2)], lambda i: word(i, 2)),
    'E in:  e = (h + K) + (Σ1 + Ch) + (W + d)': (0, lambda i: [word(i, 2), word(i, 2)], lambda i: word(i, 2)),
    'W:     W = σ1 + (W16 + σ0) + W7': (0, lambda i: [word(i), word(i, 2)], lambda i: word(i)),
}


def table():
    rows = []
    for name, (off, ops, snd) in CHECKS.items():
        for i in range(3):
            iv = add(*lhs_terms(i, off), *[neg(o) for o in ops(i)], neg(snd(i)))
            rows.append((name, i, iv))
    # feed-forward: (local + stored) - 2^w c + c_{i-1} against the O row's canonical limb
    for i in range(3):
        w = W[i]
        terms = [word(i), word(i), scale((0, CR - 1), -(1 << w))]
        if i > 0:
            terms.append((0, CR - 1))
        iv = add(*terms, neg(word(i)))
        rows.append(('FF:    O = H + final (reduce form)', i, iv))
    return rows


# ---------------------------------------------------------------- completeness (honest carries)
M64 = (1 << 64) - 1
K = None


def rotr(x, r):
    return ((x >> r) | (x << (64 - r))) & M64


def limbs(x):
    out, o = [], 0
    for w in W:
        out.append((x >> o) & ((1 << w) - 1))
        o += w
    return out


def carries(out, rhs, off):
    ol = limbs(out)
    c, prev, res = 0, 0, []
    for i, w in enumerate(W):
        v = rhs[i] + prev - ol[i]
        assert v % (1 << w) == 0
        c = v >> w
        prev = c
        res.append(c + off)
    return res


def honest(n=300, seed=1):
    import hashlib  # noqa: F401  (only for parity with the Rust reference; not needed)
    kk = [int(x, 16) for x in K_HEX.split()]
    s0 = lambda x: rotr(x, 28) ^ rotr(x, 34) ^ rotr(x, 39)
    s1 = lambda x: rotr(x, 14) ^ rotr(x, 18) ^ rotr(x, 41)
    g0 = lambda x: rotr(x, 1) ^ rotr(x, 8) ^ (x >> 7)
    g1 = lambda x: rotr(x, 19) ^ rotr(x, 61) ^ (x >> 6)
    ch = lambda e, f, g: (e & f) ^ (~e & g & M64)
    mj = lambda a, b, c: (a & b) ^ (a & c) ^ (b & c)
    L = lambda *xs: [sum(limbs(x)[i] for x in xs) for i in range(3)]
    rnd = random.Random(seed)
    seen = {}
    for _ in range(n):
        h = [rnd.getrandbits(64) for _ in range(8)]
        w = [rnd.getrandbits(64) for _ in range(16)]
        for t in range(16, 80):
            w.append((g1(w[t - 2]) + w[t - 7] + g0(w[t - 15]) + w[t - 16]) & M64)
        a = {-1 - k: h[k] for k in range(4)}
        e = {-1 - k: h[4 + k] for k in range(4)}
        for t in range(80):
            t1 = (e[t - 4] + s1(e[t - 1]) + ch(e[t - 1], e[t - 2], e[t - 3]) + kk[t] + w[t]) & M64
            t2 = (s0(a[t - 1]) + mj(a[t - 1], a[t - 2], a[t - 3])) & M64
            a[t] = (t1 + t2) & M64
            e[t] = (a[t - 4] + t1) & M64
            # A: a = e + (Σ0 + Maj) - d   (signed limbs)
            m = L(s0(a[t - 1]), mj(a[t - 1], a[t - 2], a[t - 3]))
            rhs = [m[i] - limbs(a[t - 4])[i] + limbs(e[t])[i] for i in range(3)]
            seen.setdefault('A (offset 4)', []).extend(carries(a[t], rhs, 4))
            # E: e = (h + K) + (Σ1 + Ch) + (d + W)
            rhs = L(e[t - 4], kk[t], s1(e[t - 1]), ch(e[t - 1], e[t - 2], e[t - 3]), a[t - 4], w[t])
            seen.setdefault('E', []).extend(carries(e[t], rhs, 0))
        for t in range(16, 80):
            rhs = L(g1(w[t - 2]), w[t - 16], g0(w[t - 15]), w[t - 7])
            seen.setdefault('W', []).extend(carries(w[t], rhs, 0))
        fin = [a[79], a[78], a[77], a[76], e[79], e[78], e[77], e[76]]
        for k in range(8):
            seen.setdefault('FF', []).extend(carries((h[k] + fin[k]) & M64, L(h[k], fin[k]), 0))
    return {k: (min(v), max(v)) for k, v in seen.items()}


K_HEX = """428a2f98d728ae22 7137449123ef65cd b5c0fbcfec4d3b2f e9b5dba58189dbbc 3956c25bf348b538 59f111f1b605d019
923f82a4af194f9b ab1c5ed5da6d8118 d807aa98a3030242 12835b0145706fbe 243185be4ee4b28c 550c7dc3d5ffb4e2
72be5d74f27b896f 80deb1fe3b1696b1 9bdc06a725c71235 c19bf174cf692694 e49b69c19ef14ad2 efbe4786384f25e3
0fc19dc68b8cd5b5 240ca1cc77ac9c65 2de92c6f592b0275 4a7484aa6ea6e483 5cb0a9dcbd41fbd4 76f988da831153b5
983e5152ee66dfab a831c66d2db43210 b00327c898fb213f bf597fc7beef0ee4 c6e00bf33da88fc2 d5a79147930aa725
06ca6351e003826f 142929670a0e6e70 27b70a8546d22ffc 2e1b21385c26c926 4d2c6dfc5ac42aed 53380d139d95b3df
650a73548baf63de 766a0abb3c77b2a8 81c2c92e47edaee6 92722c851482353b a2bfe8a14cf10364 a81a664bbc423001
c24b8b70d0f89791 c76c51a30654be30 d192e819d6ef5218 d69906245565a910 f40e35855771202a 106aa07032bbd1b8
19a4c116b8d2d0c8 1e376c085141ab53 2748774cdf8eeb99 34b0bcb5e19b48a8 391c0cb3c5c95a63 4ed8aa4ae3418acb
5b9cca4f7763e373 682e6ff3d6b2b8a3 748f82ee5defb2fc 78a5636f43172f60 84c87814a1f0ab72 8cc702081a6439ec
90befffa23631e28 a4506cebde82bde9 bef9a3f7b2c67915 c67178f2e372532b ca273eceea26619c d186b8c721c0c207
eada7dd6cde0eb1e f57d4f7fee6ed178 06f067aa72176fba 0a637dc5a2c898a6 113f9804bef90dae 1b710b35131c471b
28db77f523047d84 32caab7b40c72493 3c9ebe0a15c9bebc 431d67c49c100d4c 4cc5d4becb3e42b6 597f299cfc657e2a
5fcb6fab3ad6faec 6c44198c4a475817"""


if __name__ == '__main__':
    worst = 0
    print(f"{'equation':52s} limb {'min E':>14} {'max E':>14}  max|E|/p")
    for name, i, (lo, hi) in table():
        m = max(-lo, hi)
        worst = max(worst, m / P)
        print(f"{name:52s} {i:4d} {lo:14,} {hi:14,}  {m / P:.4f}")
    print(f"worst max|E|/p = {worst:.4f} (< 1: every field equation is an integer equation)")
    hc = honest()
    for k, (lo, hi) in sorted(hc.items()):
        print(f"honest carries {k:14s} stored range [{lo}, {hi}] inside [0, {CR})")
    assert worst < 1 and all(0 <= lo and hi < CR for lo, hi in hc.values())
    print("OK")
