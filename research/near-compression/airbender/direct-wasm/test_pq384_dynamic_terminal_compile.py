"""Check dynamic terminal compilation against independent canonical AIR evaluation.

Uses public transcript replay, arbitrary private inputs and exceptional batching
coefficients. This is differential evidence, not a compiler correctness proof.
"""
import argparse
import hashlib
import json
import random
import sys
from pathlib import Path


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--implementation-dir', type=Path, required=True)
    ap.add_argument('--proof-directory', type=Path, required=True)
    ap.add_argument('--report', type=Path, required=True)
    args = ap.parse_args()
    sys.path.insert(0, str(args.implementation_dir.resolve()))
    import pq384_gkr_bus as new
    import pq384_global_bus as old
    from pq384_terminal_compile import compile_terminal
    from pq384_terminal_gkr import gate
    proof = json.loads((args.proof_directory/'proof.json').read_text())
    trusted = json.loads((args.proof_directory/'statement.json').read_text())
    spec = trusted['spec']
    roots = list(map(bytes.fromhex, trusted['roots']))
    _, t, alpha, gamma = new.begin(spec, roots)
    new.initialize_aux(t, spec, list(map(bytes.fromhex, proof['aux_roots'])), proof['finals'])
    terminals = [new.constraint_verify(spec, t, i, rounds) for i, rounds in enumerate(proof['tables'])]
    t.t.commit(b'all-constraint-proofs-complete', new.u64(len(terminals)))
    actual_rho = t.draw(1, True)[0]
    rng = random.Random(667125)
    def random_ext():
        return tuple(rng.randrange(old.P) for _ in range(4))
    checks = 0
    for rho in (actual_rho, old.ZERO, old.ONE, random_ext()):
        circuit = compile_terminal(spec, alpha, gamma, proof['finals'], terminals, rho)
        capacity = circuit['private_input_capacity']
        blocks = {b['table']: b for b in circuit['input_blocks']}
        inputs = [[old.ZERO]*capacity, [old.ONE]*capacity]
        inputs += [[random_ext() for _ in range(capacity)] for _ in range(3)]
        for private in inputs:
            values = []
            for i, node in enumerate(circuit['nodes']):
                if node[0] == 'const':
                    value = old.ext(node[1:])
                elif node[0] == 'input':
                    value = private[node[1]]
                else:
                    assert all(0 <= x < i for x in node[1:])
                    value = gate(node[0], values[node[1]], values[node[2]])
                values.append(value)
            expected, power = old.ZERO, old.ONE
            for ti, table in enumerate(spec['air']['tables']):
                b = blocks[ti]
                start, W = b['offset'], b['column_capacity']
                width = table['width']+4*old.aux.layout(table)['aux_columns']
                term = terminals[ti]
                result = old.weighted(spec, ti, alpha, gamma,
                    [old.ext(x) for x in proof['finals'][ti]], term['mixing'],
                    term['tau'], term['point'], private[start:start+width],
                    private[start+W:start+W+width])
                expected = old.add(expected, old.mul(power, old.sub(result, term['claim'])))
                power = old.mul(power, rho)
            assert expected == values[circuit['root']]
            checks += 1
    source = args.implementation_dir/'pq384_terminal_compile.py'
    report = dict(status='PASS', tables=len(terminals), aggregate_checks=checks,
                  compiler_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),
                  actual_transcript_rho=list(actual_rho),
                  scope='Dynamic compiler parity for zero, one and random private inputs; actual, zero, one and random rho',
                  limitations=['Not formal compiler correctness or protocol soundness'])
    args.report.write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps(report))


if __name__ == '__main__':
    main()
