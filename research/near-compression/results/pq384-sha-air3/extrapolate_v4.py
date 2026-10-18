"""extrapolate_nv2.py (results/pq-recursion-nv) re-run with the SHA AIR v4 shape.  MODEL.

The SHA terms of extrapolate_nv2 are replaced by v4's keygen census (objective.apply):
  Sha512Air4  128 rows/compression, 83 columns, 73 next-row, degree 9, 17 interactions/row,
              5,848 DAG nodes;
  TableAir4   128 rows, 9 columns, 7 next-row, 2 interactions/row (replaces v2.1's 64 x 13 table);
everything else (NvAir, byte table, program costs, WHIR/GKR/relations/stacking laws) unchanged.
Regimes: m = 3, m = 64, O-2, and O-2 + the program cut (-28 %), as size_cut_mca.py.

Usage: python3 extrapolate_v4.py
"""
import math
import objective as O

V4 = dict(airs=[dict(name='Sha512Air4', rows=128, cols=83, rot=73, ipr=17, deg=9, nodes=5848)],
          tables=[dict(name='TableAir4', rows=128, cols=9, rot=7, ipr=2, deg=8, nodes=1234)])

if __name__ == '__main__':
    for label, d in (('v2.1', O.V21), ('v4', V4)):
        for reg in ('m3', 'm64', 'O2', 'O2cut'):
            fb = O.final_bytes(d, reg)
            c, pb = fb['c'], fb['pb']
            print(f"{label:5s} {reg:6s} final {pb['total']:,} B (whir {pb['whir']:,} gkr {pb['gkr']:,} L={pb['L']} "
                  f"rel {pb['rel']:,} stk {pb['stk']:,} W={pb['W']}) | final shape {pb['shape']} q={pb['q']} | "
                  f"program {c['prog']:,} | comps {c['comps']:,} | NvAir {c['nv_rows']:,} SHA {c['sha_rows']:,} rows | "
                  f"cells 2^{math.log2(c['cells']):.2f} | interactions 2^{math.log2(c['inter']):.2f}")
    l0, l1 = O.latency(O.V21), O.latency(V4)
    print(f"latency (latency_model, design G, adversarial, N = 32, z = 24): tail {l0['tail_mid']:.2f} -> "
          f"{l1['tail_mid']:.2f} s mid ({l1['tail_mid'] - l0['tail_mid']:+.2f}), {l0['tail_opt']:.2f} -> "
          f"{l1['tail_opt']:.2f} s optimistic; final-layer zerocheck+GKR {l0['final_zc_mid']:.2f} -> "
          f"{l1['final_zc_mid']:.2f} GPU-s")
