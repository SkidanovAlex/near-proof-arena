#!/usr/bin/env python3
"""Final-layer bytes before/after the MCA upgrade, through the project's size models.

The size models compute every WHIR round's query count as
      q = ceil(target / bits(rate, m)),  bits(rate, m) = rate/2 - log2(1 + 1/(2m)),  rate = -log2 rho
(ext.py of lane/pq-native-hermetic models-C, also vendored by lane/pq-recursion-sha384).  This
driver replaces bits() by the per-query bits of each regime of bound_mca.py and re-runs:

  * extrapolate_nv.py   (lane/pq-recursion-sha384; the ~299 KB headline, padding-free heights)
  * extrapolate_nv2.py  (lane/pq-recursion-sha384; phase-2 measured laws)
  * ext2.py             (lane/pq-native-hermetic models-C; gate-5 laws, c_sha = 7,524 SHA AIR2)

Regimes:  bcgm  = today (m = 3);  O-1 = Johnson radius, backend ListDecoding(64)
          (bits = rate/2 - log2(1 + 1/128));  O-1+O-2 = first order at
          a = (a1(rho)/sqrt(rho) + 0.05) sqrt(rho)   (the rule certified on the grid in
          dkt_certs.json '_grid'), plus a conservative 48 B per later round for a possible
          second OOD answer.
The model files are read with `git show <branch>:<path>` into a temporary directory, so the
inputs are pinned to the branch heads named below.  Inner (penultimate) and final layers use
the same regime, as in the protocol (the NV circuit verifies the inner layer's queries).

Usage: python3 -I size_mca.py      (runs from any checkout of the repo; needs git)
"""
import json
import math
import os
import subprocess
import sys
import tempfile

REPO = subprocess.run(['git', 'rev-parse', '--show-toplevel'], capture_output=True, text=True,
                      cwd=os.path.dirname(os.path.abspath(__file__))).stdout.strip()
NV_BRANCH = 'lane/pq-recursion-sha384'
EXT2_BRANCH = 'lane/pq-native-hermetic'
NV_DIR = 'research/near-compression/results'
EXT2_DIR = 'research/near-compression/l4-study/models-C'
FILES = {
    NV_BRANCH: [f'{NV_DIR}/pq-recursion-nv/extrapolate_nv.py', f'{NV_DIR}/pq-recursion-nv/extrapolate_nv2.py',
                f'{NV_DIR}/pq384-sha-air2/score_designs.py', f'{NV_DIR}/pq384-sha-air2/model/ext.py',
                f'{NV_DIR}/pq384-sha-air2/model/levers_model.py', f'{NV_DIR}/pq384-sha-air2/model/final_layer_model.py'],
    EXT2_BRANCH: [f'{EXT2_DIR}/ext2.py', f'{EXT2_DIR}/ext.py', f'{EXT2_DIR}/levers_model.py',
                  f'{EXT2_DIR}/final_layer_model.py'],
}
MARGIN = 0.05

CHILD = r'''
import json, math, os, sys
regime, model, fin_target = sys.argv[1], sys.argv[2], int(sys.argv[3])
MARGIN = float(sys.argv[4])

def a1(r):
    rc = 11 - 3 * math.sqrt(13)
    if r < rc:
        s, lo, hi = math.sqrt(r / 2), 0.0, 1.0
        for _ in range(200):
            mid = (lo + hi) / 2
            lo, hi = (mid, hi) if mid * mid * (mid + 3) < s else (lo, mid)
        return s * (1 + lo)
    return (3 * r + 2 * math.sqrt(r * (5 - r) * (2 - r))) / (8 - r)

def bits_new(rate, m):
    if regime == 'bcgm':
        return rate / 2 - math.log2(1 + 1 / 6)
    if regime == 'O1':
        return rate / 2 - math.log2(1 + 1 / 128)
    rho = 2 ** -rate
    c = min(a1(rho) / math.sqrt(rho) + MARGIN, 1 + 1 / 128)
    return rate / 2 - math.log2(c)

if model in ('nv', 'nv2'):
    sys.path.insert(0, os.path.join(os.getcwd(), 'pq384-sha-air2', 'model'))
    sys.path.insert(0, os.path.join(os.getcwd(), 'pq384-sha-air2'))
    sys.path.insert(0, os.path.join(os.getcwd(), 'pq-recursion-nv'))
else:
    sys.path.insert(0, os.getcwd())
import ext
ext.bits = bits_new
out = {}
if model == 'nv':
    import extrapolate_nv as X, score_designs as SD
    orig = SD.settings
    def settings(kind, m=3):
        pen, fin = orig(kind, m)
        fin = dict(fin, target=fin_target)
        return pen, fin
    X.settings = settings
    r = X.nv_fixed_point('L', pad=False)
    rounds = len(r['shape']) and None
    out = dict(total=r['bytes'], whir=r['whir'], pen_q=r['q'], shape=r['shape'])
    # final-layer query schedule of the chosen final shape
elif model == 'nv2':
    import extrapolate_nv2 as X
    best = None
    for b in (1, 2, 3, 4, 5, 6):
        for n_stack in range(17, 25 - b):
            c, pb, q = X.fixed_point(236, fin_target, 42, b, n_stack)
            if best is None or pb['total'] < best[1]['total']:
                best = (b, pb, c, n_stack, q)
    b, pb, c, n_stack, q = best
    out = dict(total=pb['total'], whir=pb['whir'], fin_q=pb['q'], pen_q=q, fin_shape=pb['shape'], pen_b=b, n_stack=n_stack,
               rounds=len(pb['q']))
else:
    import ext2
    pen = ext.P(target=236, m=3, dedup='multiproof', extra=math.log2(15), shrink=0, leaf='seq')
    fin = ext.P(target=fin_target, m=3, digest=42, dedup='multiproof', extra=math.log2(15), shrink=0, leaf='seq', pack=31 / 32)
    cells, blocks, shape, f = ext2.fixed_point(7524, pen, fin, cols=262, gruen=True)
    out = dict(total=f['bytes'], whir=f['whir'], fin_q=f['shape']['q'], pen_shape=shape, rounds=len(f['shape']['q']))
print(json.dumps(out))
'''


def fetch(tmp):
    for br, paths in FILES.items():
        for p in paths:
            data = subprocess.run(['git', 'show', f'{br}:{p}'], capture_output=True, cwd=REPO, check=True).stdout
            rel = p.split('results/')[-1] if br == NV_BRANCH else os.path.join('ext2', os.path.basename(p))
            dst = os.path.join(tmp, rel)
            os.makedirs(os.path.dirname(dst), exist_ok=True)
            open(dst, 'wb').write(data)
    heads = {br: subprocess.run(['git', 'rev-parse', '--short', br], capture_output=True, text=True, cwd=REPO).stdout.strip()
             for br in FILES}
    return heads


def run(tmp, regime, model, fin_target):
    cwd = os.path.join(tmp, 'ext2') if model == 'ext2' else tmp
    r = subprocess.run([sys.executable, '-I', '-c', CHILD, regime, model, str(fin_target), str(MARGIN)],
                       capture_output=True, text=True, cwd=cwd, timeout=3000)
    if r.returncode:
        raise SystemExit(r.stderr)
    return json.loads(r.stdout.strip().splitlines()[-1])


def main():
    with tempfile.TemporaryDirectory() as tmp:
        heads = fetch(tmp)
        print(f"model sources: {NV_BRANCH}@{heads[NV_BRANCH]}, {EXT2_BRANCH}@{heads[EXT2_BRANCH]}")
        print(f"O-1+O-2 rule: a = (a1(rho)/sqrt(rho) + {MARGIN}) sqrt(rho); +48 B per later round reserved for a 2nd OOD answer\n")
        rows = []
        for model, label in (('nv', 'extrapolate_nv (headline, padding-free)'), ('nv2', 'extrapolate_nv2 (phase-2 laws)'),
                             ('ext2', 'ext2 (gate-5 laws, c_sha 7,524, 262 cols, Gruen)')):
            for fin_target in (226, 236):
                base = None
                for regime in ('bcgm', 'O1', 'O12'):
                    r = run(tmp, regime, model, fin_target)
                    tot = r['total'] + (48 * (r.get('rounds', 4) - 1) if regime == 'O12' else 0)
                    if base is None:
                        base = tot
                    q = r.get('fin_q', '')
                    print(f"{label:48} final target {fin_target}  {regime:5}: {tot:>9,} B  ({tot - base:+7,} B)  "
                          f"whir {r['whir']:,}  final q {q}  pen q {r.get('pen_q', '')}", flush=True)
                    rows.append(dict(model=model, fin_target=fin_target, regime=regime, total=tot, **{k: v for k, v in r.items() if k != 'total'}))
        print(json.dumps(dict(heads=heads, rows=rows)))


if __name__ == '__main__':
    main()
