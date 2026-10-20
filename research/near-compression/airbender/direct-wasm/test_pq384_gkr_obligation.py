"""Independent DAG replay and mandatory final-opening obligation regressions."""
import argparse
import copy
import json
import random
from pathlib import Path
import pq384_terminal_gkr as g


def dot(a, b):
    assert len(a) == len(b)
    result = g.ZERO
    for x, y in zip(a, b):
        result = g.add(result, g.mul(x, y))
    return result


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--circuit')
    ap.add_argument('--proof')
    ap.add_argument('--report', required=True)
    args = ap.parse_args()
    rng = random.Random(87132)
    checks = 0
    for trial in range(32):
        private = [tuple(rng.randrange(2013265921) for _ in range(4)) for _ in range(8)]
        # Only three slots are used. Remaining private slots and padded input
        # positions must contribute exactly as specified by the final weights.
        nodes = [['input', i] for i in range(3)]
        vals = private[:3]
        for _ in range(4):
            c = tuple(rng.randrange(2013265921) for _ in range(4))
            nodes.append(['const', *c]); vals.append(c)
        for step in range(24):
            i, j = rng.randrange(len(nodes)), rng.randrange(len(nodes))
            op = ('add', 'sub', 'mul')[step % 3]
            nodes.append([op, i, j]); vals.append(g.gate(op, vals[i], vals[j]))
        # Force a private dependency in the root, even if random sub-DAGs
        # happen to contain only public constants.
        nodes.append(['add', len(nodes)-1, 0])
        claim = g.add(vals[-1], private[0])
        circuit = dict(nodes=nodes, root=len(nodes)-1,
                       live_nodes=list(range(len(nodes))), private_input_capacity=8)
        layout = g.layer_circuit(circuit)
        assert g.values(layout, private)[-1][layout['root']] == claim
        proof, expected = g.prove(layout, b'constant-obligation', private, claim)
        obligation = g.verify(layout, b'constant-obligation', proof, claim)
        assert obligation == expected
        assert dot(obligation['private_weights'], private) == obligation['private_claim']
        changed = list(private)
        slot = next(i for i, w in enumerate(obligation['private_weights']) if w != g.ZERO)
        changed[slot] = g.add(changed[slot], g.ONE)
        assert dot(obligation['private_weights'], changed) != obligation['private_claim']
        bad_layout = copy.deepcopy(layout)
        index = next(iter(bad_layout['constants']))
        bad_layout['constants'][index] = g.add(bad_layout['constants'][index], g.ONE)
        try:
            g.verify(bad_layout, b'constant-obligation', proof, claim)
        except ValueError:
            pass
        else:
            raise AssertionError('accepted changed public constant')
        checks += 1
    report = dict(status='PASS',constant_padding_cases=checks,
                  scope='Reduction only; private opening obligation must be verified by PCS')
    if args.circuit or args.proof:
        assert args.circuit and args.proof
        circuit = json.loads(Path(args.circuit).read_text())
        proof = json.loads(Path(args.proof).read_text())
        obligation = g.verify(g.layer_circuit(circuit), b'actual-air-terminal-circuit', proof)
        report.update(actual_layers=len(proof['layers']),
                      private_weights=len(obligation['private_weights']),
                      witness_loaded=False,
                      field_message_bytes=16*sum(3*len(x['rounds'])+2 for x in proof['layers']))
    Path(args.report).write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps(report))


if __name__ == '__main__':
    main()
