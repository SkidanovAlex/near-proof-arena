# Check the O-2 agreement thresholds A_i (AgreementTable::canonical rule) of real shapes against
# lane/pq-dkt-verify calc/dkt_certs.json (round codes and fold sub-codes s = 0..k_i).
# Usage: python3 dkt_cert_check.py <dkt_certs.json> [<exclusion keys file>]
import sys
import json, math
from decimal import Decimal, getcontext
from fractions import Fraction as Fr
getcontext().prec = 60
d = json.load(open(sys.argv[1]))
# top-level certificate keys only; entries listed in the optional exclusion file (no kernel
# proof, e.g. lean/DKTCertsO2_big.keys) do not count
certs = {k: v for k, v in d.items() if isinstance(v, dict) and 'B_jet' in v}
if len(sys.argv) > 2:
    for line in open(sys.argv[2]):
        certs.pop(line.strip(), None)
def a1(r):
    rc = 11 - 3 * math.sqrt(13)
    if r < rc:
        s, lo, hi = math.sqrt(r / 2), 0.0, 1.0
        for _ in range(200):
            mid = (lo + hi) / 2
            lo, hi = (mid, hi) if mid * mid * (mid + 3) < s else (lo, mid)
        return s * (1 + lo)
    return (3 * r + 2 * math.sqrt(r * (5 - r) * (2 - r))) / (8 - r)
def A_rust(n, k, margin=0.05, m=64):   # mirrors AgreementTable::canonical (f64)
    rho = k / n
    ratio = min(a1(rho) / math.sqrt(rho) + margin, 1 + 1 / (2 * m))
    return math.ceil(ratio * math.sqrt((k - 1) / n) * n)
def A_dec(n, k, margin=0.05):          # dkt_certs.py --grid rule (Decimal)
    ratio = a1(k / n) / math.sqrt(k / n) + margin
    return math.ceil(Decimal(ratio) * (Decimal(k - 1) / n).sqrt() * n)
SH = {
  'final (extrapolation optimum) b7 h20 k1=1 k4 lf7': dict(log_h=20, b=7, k1=1, k=4, lf=7),
  'final (bound.py) b8 h19 k1=1 k3 lf9':             dict(log_h=19, b=8, k1=1, k=3, lf=9),
  'inner NV b6 h19 k1=1 k4 lf6':                    dict(log_h=19, b=6, k1=1, k=4, lf=6),
  'base app stress b6 h21 k1=1 k4 lf8':             dict(log_h=21, b=6, k1=1, k=4, lf=8),
  'measured chain inner b2 h20 k1=1 k4 lf3':        dict(log_h=20, b=2, k1=1, k=4, lf=3),
  'measured chain final b2 h21 k1=1 k3 lf8':        dict(log_h=21, b=2, k1=1, k=3, lf=8),
  'penultimate b7 h20 k1=2 k4 lf6':                 dict(log_h=20, b=7, k1=2, k=4, lf=6),
  'penultimate b8 h19 k1=2 k4 lf9':                 dict(log_h=19, b=8, k1=2, k=4, lf=9),
}
for name, s in SH.items():
    nr = 1 + math.ceil((s['log_h'] - s['k1'] - s['lf']) / s['k'])
    ks = [s['k1']] + [s['k']] * (nr - 1)
    n = 15 * 2 ** (s['log_h'] + s['b'])
    mv = s['log_h']
    print(f"== {name}: n = 15*2^{s['log_h']+s['b']}")
    for i, ki in enumerate(ks):
        kd = 2 ** mv
        Ar, Ad = A_rust(n, kd), A_dec(n, kd)
        a = Fr(Ar, n)
        miss = []
        for sub in range(ki + 1):
            ns, kss = n >> sub, kd >> sub
            As = math.ceil(a * ns)
            key = f"{ns},{kss},{As},1"
            if key not in certs:
                miss.append(f"s={sub} ({ns},{kss},{As})")
        q = math.ceil(236 / -math.log2(Ar / n))
        flag = "OK" if not miss else "MISSING " + "; ".join(miss)
        print(f"  round {i}: k_i={ki} kdim=2^{mv} A={Ar}{'' if Ar == Ad else f' (Decimal rule {Ad})'} q={q}  certs: {flag}")
        mv -= ki
