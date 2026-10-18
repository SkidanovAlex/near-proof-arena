#!/usr/bin/env python3
"""S-24: re-run the final-soundness calculator with PINNED base-layer (layer-0) parameters.

Loads calc/bound.py verbatim from lane/pq-final-soundness (pinned commit below, read with
`git show`, never copied), patches it in memory so that each shape may carry its own odd domain
factor c and list multiplicity m (bound.py's whir_schedule / log_mca already take them as
arguments; layer_moves just did not pass them), replaces the stress base shape by the pinned
base shapes of DESIGN-BASE.md §3, adds the 2-to-1 aggregation node shape, and runs bound.py's
own main() (which asserts PASS or prints the shortfall).

Usage: python3 -I base_bound.py            (stdlib only; writes nothing)
"""
import os
import re
import subprocess
import sys

BOUND_COMMIT = 'f8c168f98945a809f72ac32f4dcb48407fd29ae1'   # lane/pq-final-soundness
BOUND_PATH = 'research/near-compression/final-soundness/calc/bound.py'
HERE = os.path.dirname(os.path.abspath(__file__))

src = subprocess.run(['git', '-C', HERE, 'show', f'{BOUND_COMMIT}:{BOUND_PATH}'],
                     check=True, capture_output=True, text=True).stdout


def patch(s, old, new, count=1):
    assert s.count(old) == count, (old, s.count(old))
    return s.replace(old, new)


# per-shape c (odd domain factor) and m (list multiplicity); defaults = bound.py's constants
src = patch(src, "sch = whir_schedule(s['log_h'], s['b'], s['k1'], s['k'], s['lf'], s.get('keep', True))",
            "sch = whir_schedule(s['log_h'], s['b'], s['k1'], s['k'], s['lf'], s.get('keep', True), "
            "c=s.get('c', C_ODD), m=s.get('m', M_LIST))")
src = patch(src, "lsum(log_mca(W - 1, r0['log_n'], r0['log_rho']),",
            "lsum(log_mca(W - 1, r0['log_n'], r0['log_rho'], m=s.get('m', M_LIST)),")
src = patch(src, "lsum(log_mca(1, ln, r['log_rho']),", "lsum(log_mca(1, ln, r['log_rho'], m=s.get('m', M_LIST)),")
# do not run main() on exec
src = patch(src, "if __name__ == '__main__':\n    main()", "")

ns = {'__name__': 'bound'}
exec(compile(src, 'bound.py@' + BOUND_COMMIT[:9], 'exec'), ns)

NV = ns['NV_COMMON']
# ---------------------------------------------------------------------------------------------
# PINNED base-layer parameters (DESIGN-BASE.md §3).  One segment proof = one SWIRL proof of a
# fixed-shape segment AIR set (the WASM machine chips + host tables of V3-PERF-DESIGN §2-3 on
# the SWIRL backend; one stacked commitment).  Upper bounds (a real vk must be <= each):
#   stacked height 2^24 (l_skip 2, n_stack 22); W <= 24 stacked columns (adversarial segment:
#   2^23 WASM ops x 38 main cells = 2^28.25 cells -> 19.0 columns at 2^24 rows);
#   <= 32 AIRs; max constraint degree <= 8; <= 2^14 constraints; <= 1024 opened columns
#   (incl. rotations); interactions <= 2^28 (19 fractions/op adversarial = 2^27.25), message
#   length <= 16; T* transcript, 42-B digests, z = 32, target 268, keep-domain, k1 = 1, k = 4.
# WHIR domain: c = 1 (plain 2-adic), log_blowup b = 1 (rate 1/2), list multiplicity m = 16.
BASE = dict(log_int=28, msg_len=16, n_constraints=2**14, airs=32, degree=8, cols=1024,
            log_h=24, b=1, k1=1, k=4, lf=7, W=24, c=1, m=16, commits=1)
SHAPES = {
    'final (layer d)': ns['SHAPES']['final (layer d)'],
    'inner NV (layers 1..d-1)': ns['SHAPES']['inner NV (layers 1..d-1)'],
    # base, pinned (production segment shape)
    'base seg-v1 (c=1, b=1, m=16)': dict(BASE),
    # alternatives considered (DESIGN-BASE.md §3.2)
    'base alt (c=1, b=2, m=8)': dict(BASE, b=2, m=8),
    'base alt (c=15, b=0, m=8)': dict(BASE, b=0, c=15, m=8),
    # the only base AIR set measured on the PQ stack today: direct-wasm gas-failure5 vk
    # (EXEC 157 / CODE 114 / RANGE 24 cols, 3 AIRs, 531 constraints, 82 interactions/row,
    # degree <= 8, log_h 17), re-parameterised to U-10 (its recorded proof: b = 7, no PoW)
    'base gas-failure5 vk @ U-10 (c=1, b=7, m=3)': dict(log_int=26, msg_len=32, n_constraints=531, airs=3,
                                                      degree=8, cols=2 * 295, log_h=17, b=7, k1=1, k=3,
                                                      lf=7, W=3, c=1, m=3, commits=1),
    # 2-to-1 aggregation node: NV AIRs; 2 children -> ~2x cells; shape at the inner-NV settings
    'agg node N2 (2-to-1, NV AIRs)': dict(NV, log_int=25.4, log_h=20, b=6, k1=1, k=4, lf=7, W=141),
    # level-1 node N1 verifying k1 = 2 base segments (NV AIRs, its own WHIR at b = 3, c = 15)
    'agg node N1 (2 segments, NV AIRs)': dict(NV, log_int=27.4, log_h=21, b=3, k1=1, k=4, lf=8, W=141),
}
ns['SHAPES'] = SHAPES
ns['main'].__globals__['SHAPES'] = SHAPES

if __name__ == '__main__':
    print(f"bound.py @ {BOUND_COMMIT[:9]} (lane/pq-final-soundness), base shapes pinned by DESIGN-BASE.md §3\n")
    ok = True
    try:
        ns['main']()
    except AssertionError:
        ok = False
    # tree-shaped composition: the single-database theorem needs no union; a per-proof union
    # over every proof of a 1 Pgas tree (S segments + S - 1 nodes + tail) is shown for reference
    import math
    sch, mv = ns['layer_moves'](SHAPES['inner NV (layers 1..d-1)'])
    eps = max(e for shp in SHAPES.values() for _, e in ns['layer_moves'](shp)[1])
    tot = ns['fs_bound_k0'](eps, ns['T_LOG'])
    print(f"\ntree (S = 146 segments, 145 nodes, 4 tail layers = 295 proofs): single database 2^{tot:.2f}; "
          f"per-proof union 2^{tot + math.log2(295):.2f} ({'PASS' if tot + math.log2(295) <= -128 else 'FAIL'} as a union)")
    sys.exit(0 if ok else 1)
