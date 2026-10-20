# Check the O-2 agreement thresholds A_i (AgreementTable::canonical rule) of real shapes against
# lane/pq-dkt-verify calc/dkt_certs.json (round codes and fold sub-codes s = 0..k_i).
# Usage: python3 dkt_cert_check.py <dkt_certs.json | dkt_certs_o2.json>
# Copied from lane/pq-recursion-sha384 @ cf2262a24 results/pq-recursion-nv/dkt_cert_check.py; changes:
# '_grid' optional; penultimate candidate shapes added (3c4324e8c size_cut3.py); the first-curve (ell = W-1) round-0 certificates and '_no_certificate' are reported.
import sys
import json, math
from decimal import Decimal, getcontext
from fractions import Fraction as Fr
getcontext().prec = 60
d = json.load(open(sys.argv[1]))
certs = {k: v for k, v in d.items() if not k.startswith('_')}
certs.update(d.get('_grid', {}).get('certs', {}))
nocert = d.get('_no_certificate', {})
total_missing = 0
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
  'penultimate b8 h20 k1=2 k4 lf6 (n=15*2^28: NOT a BabyBear domain)': dict(log_h=20, b=8, k1=2, k=4, lf=6),
  'penultimate b8 h19 k1=2 k4 lf9':                 dict(log_h=19, b=8, k1=2, k=4, lf=9),
  'penultimate b7 h20 k1=2 k4 lf6':                 dict(log_h=20, b=7, k1=2, k=4, lf=6),
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
        total_missing += len(miss)
        flag = "OK" if not miss else "MISSING " + "; ".join(miss)
        if i == 0:
            ells = sorted(int(x.split(',')[3]) for x in certs if x.startswith(f"{n},{kd},{Ar},") and not x.endswith(',1'))
            flag += f"  first-curve ell={ells}" if ells else ""
        print(f"  round {i}: k_i={ki} kdim=2^{mv} A={Ar}{'' if Ar == Ad else f' (Decimal rule {Ad})'} q={q}  certs: {flag}")
        mv -= ki
print(f"missing certificates: {total_missing}; recorded as not certifiable: {len(nocert)}")
sys.exit(1 if total_missing else 0)
