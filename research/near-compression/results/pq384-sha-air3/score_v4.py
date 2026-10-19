"""SHA AIR v4 design space, scored with objective.py.  MODEL (lane/pq-sha384-air3).

Each candidate is a shape (rows/compression, columns, rotated columns, degree, interactions/row,
DAG nodes) derived from its layout; the derivations are in DESIGN_NOTES below and in README.md
§ "Design space".  Measured rows are marked [M], the rest [E] (estimated from the layout, DAG
nodes from the per-function node counts of v2.1's keygen: bit signs ~7/digit, an XOR3 Σ/σ
function ~256, Maj/Ch ~450, range checks 3/digit).

Usage: python3 score_v4.py [regimes...]    (default: m3 O2cut; 'all' = m3 m64 O2 O2cut)
"""
import sys
import objective as O

T = O.V21['tables']
# control/K table of v4: 128 rows, 7 counter bits + 2 multiplicities (all bits rotated)
T4 = [dict(name='TableAir4', rows=128, cols=9, rot=7, ipr=2, deg=8, nodes=900)]


def one(name, rows, cols, rot, ipr, deg, nodes, tables=T, note=''):
    return name, dict(airs=[dict(name='sha', rows=rows, cols=cols, rot=rot, ipr=ipr, deg=deg, nodes=nodes)],
                      tables=tables), note


DESIGNS = [
    one('v2.1 k=3 [M]', 43, 171, 144, 14, 21, 12718, note='today: 6 words/row, base-8 digits'),
    one('v2.1 k=2 [M]', 43, 231, 204, 14, 9, 9513, note='same layout, base-4 digits'),
    one('v2.1 k=3, rot 40 [E]', 43, 171, 40, 14, 21, 12718, note='recursion agent\'s "rot <= 40" at today\'s cells'),
    one('deg 8 mixed {1,2}-bit digits [E]', 43, 290, 200, 14, 8, 11000,
        note='singles hit every XOR3/Maj triple: ~43 cells/word'),
    one('wide k=2 trimmed [E]', 43, 225, 150, 16, 9, 9500, note='6 words/row, W rotation replaced by bus'),
    one('Q4: (a,a,e,e) rows + 4-W rows [E]', 64, 159, 130, 16, 9, 6500, tables=T4,
        note='4-word rows, W block in the same AIR'),
    one('T3: 3-word single-type rows [E]', 86, 115, 96, 16, 9, 7000, tables=T4,
        note='A/E/W rows of 3 words; asym 1 per 3 rounds'),
    one('T2 k=3: 2-word rows, base 8 [E]', 128, 66, 47, 16, 21, 8000, tables=T4,
        note='tall layout but degree 21'),
    one('T2 k=2: 2-word rows = v4 [M keygen]', 128, 83, 73, 17, 9, 5848, tables=T4,
        note='A/E/W/O blocks, 15 aux, K folded into h, 5 control'),
]


if __name__ == '__main__':
    args = sys.argv[1:] or ['m3', 'O2cut']
    regs = ['m3', 'm64', 'O2', 'O2cut'] if args == ['all'] else args
    for name, d, note in DESIGNS:
        O.DESIGNS[name] = d
    base = {r: O.final_bytes(O.V21, r)['total'] for r in regs}
    lt0 = O.latency(O.V21)['tail_mid']
    print(f"{'design':40s} {'cells':>6} {'cols':>4} {'rot':>4} {'deg':>3} {'ipr':>3} {'nodes':>6} " +
          ' '.join(f'{r:>16}' for r in regs) + '   tail (mid)')
    for name, d, note in DESIGNS:
        pc = O.per_comp(d)
        fb = [O.final_bytes(d, r)['total'] for r in regs]
        lt = O.latency(d)['tail_mid']
        print(f"{name:40s} {pc['cells']:6,} {pc['cols']:4} {pc['rot']:4} {pc['deg']:3} {pc['ipr']:3} {pc['nodes']:6,} " +
              ' '.join(f'{b:>8,} ({b - base[r]:+6,})' for b, r in zip(fb, regs)) +
              f'   {lt:.2f} s ({lt - lt0:+.2f})')
