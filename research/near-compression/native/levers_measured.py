"""Measured proof-size levers vs the size model (lane/pq-whir-levers).

Parses the run logs in results/pq-whir-levers/logs (produced by the levers driver,
airbender/direct-wasm/native_sha384_levers_driver.rs) and compares every measured
component with the model's prediction for the *same* parameters:

  * gas-failure5 child, one lever at a time and combined (bytes + verifier SHA-384
    compressions), against final_layer_model / levers_model / l4-study ext.py formulas;
  * gate 5: the shape-equivalent dummy final layer (460 columns, 2^h rows) at the
    shape levers_model.best() picks for 2^26.4 cells, measured at stacked width W <= 15
    and extrapolated to the model's W with the measured per-component scaling laws.

Measured numbers come from the logs; everything labelled "model" or "extrapolated"
is computed here. Run:  python3 native/levers_measured.py
"""
import math
import re
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
LOGS = HERE.parent / 'results' / 'pq-whir-levers' / 'logs'
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(HERE.parent / 'l4-study' / 'models-C'))
import final_layer_model as F  # noqa: E402
import levers_model as L       # noqa: E402
import ext as X                # noqa: E402  (multiproof expectations for any leaf count)

EXT, BASE = 48, 4


def parse(name):
    text = (LOGS / f'{name}.log').read_text()
    out = {}
    m = re.search(r'queries=\[([0-9, ]+)\]', text)
    out['q'] = [int(x) for x in m.group(1).split(',')]
    m = re.search(r'LEVERS_PROFILE (.*)', text)
    out['profile'] = dict(kv.split('=') for kv in m.group(1).split())
    m = re.search(r'NATIVE_SHA384_PROFILE n_stack=(\d+) k=(\d+) log_blowup=(\d+)', text)
    out['n_stack'], out['k'], out['b'] = map(int, m.groups())
    m = re.search(r'LEVERS_CENSUS (.*)', text)
    if m:
        c = {}
        for kv in re.findall(r'(\w+)=(\[[^\]]*\]|\S+)', m.group(1)):
            c[kv[0]] = eval(kv[1])
        out['census'] = c
    blocks = re.findall(r'NATIVE_SHA384_VERIFY_BLOCKS \[([0-9, ]+)\]', text)
    if blocks:
        out['blocks'] = [int(x) for x in blocks[-1].split(',')]
    m = re.search(r'NATIVE_SHA384_PROVE_SECONDS ([0-9.]+)', text)
    out['prove_s'] = float(m.group(1)) if m else None
    m = re.search(r'Maximum resident set size \(kbytes\): (\d+)', text)
    out['rss_gb'] = int(m.group(1)) / 1e6 if m else None
    out['neg'] = re.findall(r'LEVERS_NEGATIVE_PASS cases=(\d+)', text)
    return out


def leaf_blocks(nbytes):
    return -(-(nbytes + 58) // 128)          # 32 prefix + tag + 8 length + padding


def predict(q, n_stack, b, k, k1, log_final, width, cols, digest=48, coset=False, multiproof=False,
            keep=False, pub_bytes=0):
    """Model prediction for one proof with these exact parameters (queries taken as given)."""
    log_h = 2 + n_stack
    shrink = 0 if keep else 1
    ks = [k1] + [k] * (len(q) - 1)
    leaves = [2 ** (log_h + b - shrink * i - ks[i]) for i in range(len(q))]
    depths = [int(math.log2(n)) for n in leaves]
    if multiproof:
        digests = round(sum(X.mp_digests(qi, n) for qi, n in zip(q, leaves)))
    else:
        digests = sum(qi * d for qi, d in zip(q, depths))
    auth = digests * digest
    initial = q[0] * 2 ** k1 * width * BASE
    codeword = sum(q[1:]) * 2 ** k * EXT
    final_poly = 2 ** log_final * EXT
    leaf, node = 0, 0
    for i, qi in enumerate(q):
        row = width * BASE if i == 0 else EXT
        if coset:
            leaf += qi * leaf_blocks(2 ** ks[i] * row)
        else:
            leaf += qi * 2 ** ks[i] * leaf_blocks(row)
            node += qi * (2 ** ks[i] - 1)
        node += round(X.mp_internal(qi, leaves[i])) if multiproof else qi * depths[i]
    return dict(auth=auth, auth_digests=digests, initial=initial, codeword=codeword,
                final_poly=final_poly, leaf_blocks=leaf, node_blocks=node,
                relations=2 * cols * EXT + 3112, gkr=8456, stacking=1840)


def child_table():
    rows = [('default (upstream)', 'r-default', {}),
            ('coset-as-one-message leaf', 'r-coset', dict(coset=True)),
            ('digest 42 B', 'r-d42', dict(digest=42)),
            ('multiproof', 'r-mp', dict(multiproof=True)),
            ('list multiplicity m=8', 'r-m8', {}),
            ('k1=2 (log_final 3)', 'r-k1_2', dict(k1=2, log_final=3)),
            ('k1=1 (log_final 1)', 'r-k1_1', dict(k1=1, log_final=1)),
            ('non-halving domains (E5)', 'r-keep', dict(keep=True)),
            ('query grinding z=16', 'r-z16', {}),
            ('query grinding z=20', 'r-z20', {}),
            ('query grinding z=24', 'r-z24', {}),
            ('ALL: coset+42B+multiproof+m8+z24', 'r-all', dict(coset=True, digest=42, multiproof=True)),
            ('ALL + E5', 'r-allkeep', dict(coset=True, digest=42, multiproof=True, keep=True)),
            ('ALL + folding/mu PoW 16', 'r-all_fp', dict(coset=True, digest=42, multiproof=True))]
    print('## gas-failure5 child, one lever at a time (measured vs model at the measured query schedule)\n')
    print('| lever | queries | bytes | Δ bytes | auth meas / model | verify SHA total | leaf+node meas / model | prove s | neg |')
    print('|---|---|---:|---:|---:|---:|---:|---:|---:|')
    base = parse('r-default')['census']['total']
    for label, name, kw in rows:
        r = parse(name)
        c = r['census']
        kw = dict(dict(k1=r['k'], log_final=2), **kw)
        p = predict(r['q'], r['n_stack'], r['b'], r['k'], kw.pop('k1'), kw.pop('log_final'), 1, 295, **kw)
        bl = r['blocks']
        meas_merkle = bl[0] + bl[1] + bl[6]
        print(f"| {label} | {r['q']} | {c['total']:,} | {c['total'] - base:+,} | {c['auth']:,} / {p['auth']:,} | "
              f"{sum(bl):,} | {meas_merkle:,} / {p['leaf_blocks'] + p['node_blocks']:,} | {r['prove_s']:.1f} | {r['neg'][0] if r['neg'] else '-'} |")
    print()


def gkr_bytes(L):
    """GKR proof bytes vs GKR depth L. Fit on the dummy AIR (L = h + 1, exact at L = 13, 14, 15); it also
    reproduces the L3 SHA-384 AIR lane exactly (43 interactions/row, L = log2(height) + 5:
    31,256 / 37,544 / 44,408 B at heights 2^14 / 2^16 / 2^18)."""
    return 72 * L * L + 264 * L + 248


def gate5():
    print('## gate 5: shape-equivalent dummy final layer (460 columns), measured at W <= 15\n')
    cases = [('today 268-bit / 48 B, m=8, k1=1, coset, multiproof', ['g5-h12', 'g5-h13', 'g5-h14'], 268, 8, 48),
             ('z=32-equivalent (226-bit queries) / 42 B, same levers', ['g5z-h12', 'g5z-h14'], 226, 8, 42),
             ('z=32 at today 268 (236-bit queries) / 42 B', ['g5z236-h12'], 236, 8, 42),
             ('no levers (upstream, m=3, k=3, b=6, log_h=21)', ['g5base-h14'], 268, 3, 48)]
    print('| setting | run | h | W | total | auth | initial | codeword | final poly | whir small | relations | gkr | stacking | other | model total (same W) | Δ |')
    print('|---|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|')
    for label, names, target, m, digest in cases:
        for name in names:
            r = parse(name)
            c = r['census']
            h = int(r['profile'].get('dummy') == 'true') and int(re.search(r'h(\d+)', name).group(1))
            log_h = 2 + r['n_stack']
            W = -(-460 * 2 ** h // 2 ** log_h)
            k1 = int(r['profile']['k1'])
            lf = int(r['profile']['log_final'])
            if 'base' in name:
                mod = F.proof_bytes(r['b'], r['k'], log_h, W, 460, 'list', 0.0, lf)[1]
            else:
                mod = L.layer(460 * 2 ** h, 460, target, m, digest, r['b'], k1, r['k'], log_h, lf)['bytes']
            print(f"| {label} | {name} | {h} | {W} | {c['total']:,} | {c['auth']:,} | {c['initial']:,} | {c['codeword']:,} | "
                  f"{c['final_poly']:,} | {c['whir_small']:,} | {c['relations']:,} | {c['gkr']:,} | {c['stacking']:,} | {c['other']:,} | "
                  f"{mod:,} | {c['total'] - mod:+,} |")
    print()


def extrapolate(log_cells=26.4, L_values=(21, 23, 25)):
    """Extrapolate the measured W<=15 runs to the model's cell count, component by component."""
    print(f'## gate 5 extrapolated to 2^{log_cells} cells, 460 columns (log_h = 19 -> W = model W)\n')
    cells = 2 ** log_cells
    h_real = math.log2(cells / 460)
    for label, name, target, m, digest, z_extra in [
            ('today 268-bit / 48 B (m=8, k1=1, coset, multiproof)', 'g5-h14', 268, 8, 48, 0),
            ('z=32 / 42 B (226-bit queries; proved at z=24, +4 B/round for a 2-element z=32 witness)', 'g5z-h14', 226, 8, 42, 16)]:
        r = parse(name)
        c = r['census']
        best = L.best(cells, 460, target, m, digest, True)
        assert (best['b'], best['k1'], best['k'], best['log_h'], best['log_final']) == (8, 1, 3, 19, 9), best
        W, W0, h0 = best['width'], 15, 14
        q0, k1 = r['q'][0], 1
        ext = dict(auth=c['auth'], initial=q0 * 2 ** k1 * W * BASE, codeword=c['codeword'], final_poly=c['final_poly'],
                   whir_small=c['whir_small'] + z_extra,
                   relations=c['relations'] + 432 * (h_real - h0),
                   stacking=c['stacking'] + 48 * (W - W0), other=c['other'])
        fixed = sum(ext.values())
        print(f'**{label}** (model best shape b=8 k1=1 k=3 log_h=19 log_final=9, W={W}, q={best["q"]})\n')
        print('| component | extrapolated measurement | model (levers_model.layer) | basis |')
        print('|---|---:|---:|---|')
        model = dict(auth=best['auth'], initial=best['initial'], codeword=best['codeword'], final_poly=best['final_poly'],
                     whir_small=best['bytes'] - best['auth'] - best['initial'] - best['codeword'] - best['final_poly']
                     - best['relations'] - 8456 - 1840 - 861,
                     relations=best['relations'], stacking=1840, other=861)
        basis = dict(auth='measured (shape-fixed, W-independent)', initial='q0*2^k1*W*4 (exact at W=4,8,15)',
                     codeword='measured', final_poly='measured', whir_small='measured (+witness widening)',
                     relations=f'measured h=14 + 432 B/doubling (fit h=12..14) to h={h_real:.2f}',
                     stacking='measured + 48 B per stacked column (exact at W=4,8,15)', other='measured')
        for key in ext:
            print(f'| {key} | {round(ext[key]):,} | {model[key]:,} | {basis[key]} |')
        for Lv in L_values:
            g = gkr_bytes(Lv)
            print(f'| gkr (L = log2 interactions = {Lv}) | {g:,} | 8,456 | fit 72L^2+264L+248 (dummy L=13..15; SHA-AIR lane L=19,21,23 exact) |')
        print(f'| **total** (gkr at L={L_values[0]} / **23** / {L_values[-1]}) | {round(fixed + gkr_bytes(L_values[0])):,} / **{round(fixed + gkr_bytes(23)):,}** / {round(fixed + gkr_bytes(L_values[-1])):,} | **{best["bytes"]:,}** | L=23: SHA AIR (43 interactions/row) at 2^18 rows |')
        print()


def baseline_extrapolated(log_cells=26.4, L=23):
    """Upstream backend (no levers) at the model's 'today' best shape, extrapolated like extrapolate()."""
    r = parse('g5base-h14')
    c = r['census']
    cells = 2 ** log_cells
    W = -(-int(cells) // 2 ** 21)
    h_real = math.log2(cells / 460)
    tot = (c['auth'] + r['q'][0] * 8 * W * BASE + c['codeword'] + c['final_poly'] + c['whir_small']
           + c['relations'] + 432 * (h_real - 14) + c['stacking'] + 48 * (W - 4) + c['other'] + gkr_bytes(L))
    w, model = F.proof_bytes(6, 3, 21, W, 460, 'list', 0.0, 9)
    print(f'No levers (upstream; b=6 k=3 log_h=21 log_final=9, W={W}) at 2^{log_cells}: extrapolated '
          f'{round(tot):,} B with gkr(L={L}); final_layer_model {model:,} B (its gkr/stacking/relations constants).')
    print()


def round2(log_cells=26.4, L_gkr=23):
    """Round 2 (GKR/zerocheck/next-row/wide-PoW levers): gate 5 at W=15 and the SHA AIR at 2^18 rows."""
    import levers_laws as LW
    print('## round 2: all levers (coset, multiproof, k1=1, m=8, gruen GKR + derived claims, gruen zerocheck,')
    print('## next-row mask, max_constraint_degree 4; z=32 via the two-element PoW)\n')
    print('| run | total | auth | initial | codeword | final poly | whir small | relations (law) | gkr (law) | stacking (law) | other |')
    print('|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|')
    laws = {'g6-h14': (LW.relations_bytes(460, 460, 4, 12, gruen_rounds=12), LW.gkr_bytes(15), LW.stacking_bytes(15, 17)),
            'g6z32-h14': (LW.relations_bytes(460, 460, 4, 12, gruen_rounds=12), LW.gkr_bytes(15), LW.stacking_bytes(15, 17)),
            'sha18-lev': (LW.relations_bytes(467, 454, 4, 16, airs=3, gruen_rounds=4), LW.gkr_bytes(23), LW.stacking_bytes(28, 20))}
    for name in ['g6-h14', 'g6z32-h14', 'sha18-lev']:
        c = parse(name)['census']
        rl, gl, sl = laws[name]
        print(f"| {name} | {c['total']:,} | {c['auth']:,} | {c['initial']:,} | {c['codeword']:,} | {c['final_poly']:,} | {c['whir_small']:,} | "
              f"{c['relations']:,} ({rl:,}) | {c['gkr']:,} ({gl:,}) | {c['stacking']:,} ({sl:,}) | {c['other']:,} |")
    print()
    cells = 2 ** log_cells
    h_real = math.log2(cells / 460)
    n_rounds = h_real - 2
    print(f'Extrapolated to 2^{log_cells} cells (W=169, n = {n_rounds:.2f} zerocheck rounds, GKR at L={L_gkr} as for the SHA AIR at 2^18 rows):\n')
    print('| setting | auth | initial | codeword | final poly | whir small | relations | gkr | stacking | other | **total** | round 1 | model (levers_model) |')
    print('|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|')
    for label, name, target, digest, r1 in [('268-bit / 48 B', 'g6-h14', 268, 48, 479156), ('z=32 / 42 B (proved)', 'g6z32-h14', 226, 42, 408734)]:
        r = parse(name)
        c = r['census']
        best = L.best(cells, 460, target, 8, digest, True)
        W = best['width']
        comp = dict(auth=c['auth'], initial=r['q'][0] * 2 * W * BASE, codeword=c['codeword'], final_poly=c['final_poly'],
                    whir_small=c['whir_small'],
                    relations=round(LW.relations_bytes(460, 460, 4, n_rounds, gruen_rounds=n_rounds)),
                    gkr=LW.gkr_bytes(L_gkr), stacking=LW.stacking_bytes(W, 17), other=c['other'])
        tot = sum(comp.values())
        print(f"| {label} | " + ' | '.join(f'{v:,}' for v in comp.values()) + f" | **{tot:,}** | {r1:,} | {best['bytes']:,} |")
    print()


if __name__ == '__main__':
    round2()
    baseline_extrapolated(26.4)
    child_table()
    gate5()
    extrapolate(26.4)
    extrapolate(26.6)
