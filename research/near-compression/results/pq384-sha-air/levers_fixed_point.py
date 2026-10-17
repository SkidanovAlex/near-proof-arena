"""Plug measured cells/compression into native/levers_model.fixed_point.

Usage: python3 levers_fixed_point.py <path to native/> 19448,28288
Rows reproduce the model log table: today = (268, 268, 48 B), all levers = (236, 226, 42 B), m = 8.
"""
import sys, math, json
sys.path.insert(0, sys.argv[1])
import levers_model as lm
lm.base.calibrate()
out = {}
for c in [int(x) for x in sys.argv[2].split(',')]:
    for name, (pt, ft, dg) in [('today', (268, 268, 48)), ('all_levers', (236, 226, 42))]:
        cells, blocks, shape, fin = lm.fixed_point(c, 2000, 1 << 20, pt, ft, 8, dg)
        out[f'{c}/{name}'] = dict(c_sha=c, pen_target=pt, fin_target=ft, digest=dg, pen_sha_blocks=blocks,
                                  final_cells_log2=round(math.log2(cells), 2), final_bytes=fin['bytes'],
                                  final_shape={k: fin[k] for k in ('b', 'k1', 'k', 'log_h', 'log_final', 'q', 'width')})
        print(c, name, blocks, round(math.log2(cells), 2), fin['bytes'], flush=True)
print(json.dumps(out))
