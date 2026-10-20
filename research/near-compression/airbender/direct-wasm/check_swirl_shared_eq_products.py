"""Share r*x between the two children of each equality-table expansion."""
import collections
import gzip
import hashlib
import json
import random
from pathlib import Path

import compile_swirl_gkr_verifier as compiler
from export_fused_gkr_arithmetic import closure


class SharedEqCircuit(compiler.Circuit):
    def eqs(self, point):
        out = [self.one]
        for r in point:
            high = [self.mul(x, r) for x in out]
            out = [self.sub(x, y) for x, y in zip(out, high)] + high
        return out


def census(dag):
    roots = dag['checks'] + [dag['residual']] + [v for _, v in dag['pcs']]
    live = closure(dag['nodes'], roots)
    return dict(collections.Counter(dag['nodes'][i][0] for i in live))


def main():
    out = compiler.OUT.parent / 'shared-eq-gkr-verifier'
    original = json.loads(gzip.decompress(
        (compiler.OUT.parent / 'bdd-gkr-verifier/circuit.json.gz').read_bytes()))
    # Isolated candidate; baseline implementation and prior evidence stay intact.
    baseline_class = compiler.Circuit
    compiler.Circuit = SharedEqCircuit
    try:
        compiler.main('interleaved_012_high', out)
    finally:
        compiler.Circuit = baseline_class
    candidate = json.loads(gzip.decompress((out / 'circuit.json.gz').read_bytes()))
    assert original['inputs'] == candidate['inputs']
    assert [i for i, _ in original['pcs']] == [i for i, _ in candidate['pcs']]
    rng = random.Random(20261017)
    for mode in ('zero', 'one', 'random'):
        inputs = {name: ((0, 0, 0, 0) if mode == 'zero' else (1, 0, 0, 0)
                         if mode == 'one' else tuple(rng.randrange(2013265921) for _ in range(4)))
                  for name in original['inputs']}
        outputs = []
        for dag in (original, candidate):
            c = baseline_class()
            c.nodes, c.inputs = dag['nodes'], dag['inputs']
            values = c.evaluate(inputs)
            roots = dag['checks'] + [dag['residual']] + [v for _, v in dag['pcs']]
            outputs.append([values[i] for i in roots])
        assert outputs[0] == outputs[1], mode
    before, after = census(original), census(candidate)
    report = dict(before=before, after=after,
                  multiplications_removed=before['mul'] - after['mul'],
                  subtractions_added=after['sub'] - before['sub'],
                  multiplication_to_subtraction_break_even=(after['sub'] - before['sub']) / (before['mul'] - after['mul']),
                  implementation_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                  arbitrary_input_parity=['zero', 'one', 'random'],
                  scope='Arithmetic DAG only; no recursive proof-size or PQ128 claim.')
    (out / 'comparison.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
