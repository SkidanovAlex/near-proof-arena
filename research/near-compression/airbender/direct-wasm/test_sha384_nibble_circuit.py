"""Complete compression witness parity and constrained-cell mutations."""
import argparse
import itertools
from collections import Counter
import hashlib
import json
from pathlib import Path
import random
import sha384_nibble_circuit as c
from measure_sha384_block_dag import Probe


def main():
    p = argparse.ArgumentParser(); p.add_argument('--probe-library', required=True); p.add_argument('--output', type=Path, required=True); a = p.parse_args()
    g = c.compile_graph(); probe = Probe(a.probe_library); rng = random.Random(8460384)
    cases = blocks = mutations = 0; used = set(); example = None
    for length in (0, 1, 111, 112, 127, 128, 129, 255, 256, 300, 1000):
        message = bytes(rng.randrange(256) for _ in range(length))
        padded, states = probe.run(message)
        for i in range(len(states)-1):
            source = c.inputs(states[i], padded[128*i:128*(i+1)])
            values = c.witness(g, source)
            assert c.check(g, source, values, states[i+1]); blocks += 1
            for op, ins, outs, bound in g.gates:
                if op not in ('const', 'add'): used.add((op, tuple(values[j] for j in ins), values[outs[0]]))
            example = source, values, states[i+1]
        cases += 1
    source, values, expected = example
    # Cover every operation and carry bound, both early and late instances,
    # boundary inputs/outputs and deterministic scattered wires. Avoid a
    # quadratic full-circuit replay for every internal cell.
    first = {}; last = {}
    owned = []
    for op, ins, outs, bound in g.gates:
        first.setdefault((op, bound), outs); last[(op, bound)] = outs
        owned.extend(outs)
    assert owned == list(range(384, g.size))
    selected = {0, 127, 128, 383, *g.outputs[-1], *rng.sample(range(g.size), 64)}
    for outs in list(first.values())+list(last.values()): selected.update(outs)
    for i in sorted(selected):
        old = values[i]; values[i] = (old+1) % 16
        try: c.check(g, source, values, expected)
        except AssertionError: mutations += 1
        else: raise AssertionError('unconstrained cell '+str(i))
        values[i] = old
    table_rows = 0
    for op in ('xor3', 'choose', 'majority', 'splice1', 'splice2', 'splice3'):
        for args in itertools.product(range(16), repeat=2 if op.startswith('splice') else 3):
            if op.startswith('splice'):
                expected_row = ((args[0]+16*args[1]) >> int(op[-1])) & 15
            else:
                expected_row = 0
                for bit in range(4):
                    x, y, z = [(v >> bit) & 1 for v in args]
                    out = (x+y+z) % 2 if op == 'xor3' else (y if x else z) if op == 'choose' else int(x+y+z >= 2)
                    expected_row += out << bit
            assert c.relation(op, args) == expected_row
            table_rows += 1
    counts = Counter(op for op, _, _, _ in g.gates)
    report = dict(status='COMPLETE_COMPRESSION_RELATION_CHECKED', messages=cases, compression_blocks=blocks,
        witness_cells=g.size, targeted_rejected_cell_mutations=mutations, every_internal_wire_has_unique_defining_gate=True, exhaustive_lookup_relation_rows=table_rows, gates=dict(counts),
        lookup_requests=sum(n for op,n in counts.items() if op not in ('const','add')),
        distinct_lookup_rows_observed=len(used),
        fixed_lookup_table_rows=3*4096+3*256,
        add_equations=counts['add'], nibble_range_obligations=g.size,
        baseline_unpadded_core_cells=80*5234,
        scope='Executable trusted graph and integer/lookup relation; all eight output state words checked with OpenSSL probe and final digests with hashlib. Wire cells exclude routing, lookup multiplicities, fixed-table proof, range arguments, AIR padding, auxiliary columns and PCS. Not directly comparable to an AIR cell count. No proof-size/performance, universal Lean, or PQ128 claim.',
        next_gate='Choose row layout and enforce fixed lookup tables plus wiring through an actual AIR/bus argument; include their full overhead before deciding whether cheaper than the existing core.',
        sha256={str(p.relative_to(c.REPO)):hashlib.sha256(p.read_bytes()).hexdigest() for p in [Path(__file__), Path(c.__file__), c.SPEC, Path(__file__).with_name('measure_sha384_block_dag.py')]})
    a.output.write_text(json.dumps(report, indent=2)+'\n'); print(json.dumps(report, indent=2))


if __name__ == '__main__': main()
