"""Differential terminal-circuit checks beyond the original honest witness.

Replay supplies all public circuit parameters. Arbitrary Ext4 input vectors
are evaluated by the exported DAG and independent canonical AIR evaluator.
This validates tested transformations, not a compiler refinement theorem.
"""
import argparse
import copy
import hashlib
import json
import random
from pathlib import Path
import pq384_global_bus as bus
from check_whir_handoff import add, sub, mul


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('proof_directory', type=Path)
    ap.add_argument('circuit_directory', type=Path)
    ap.add_argument('output', type=Path)
    args = ap.parse_args()
    statement = json.loads((args.proof_directory/'statement.json').read_text())
    proof = json.loads((args.proof_directory/'proof.json').read_text())
    spec = statement['spec']
    roots = [bytes.fromhex(v) for v in statement['roots']]
    raw = (args.circuit_directory/'circuit.json').read_bytes()
    circuit = json.loads(raw)
    nodes = circuit['nodes']
    original_inputs = [bus.ext(v) for v in json.loads((args.circuit_directory/'input-values.json').read_text())]
    assert len(original_inputs) == circuit['private_input_capacity']
    st, transcript, alpha, gamma = bus.begin(spec, roots)
    aux = [bytes.fromhex(v) for v in proof['aux_roots']]
    bus.initialize_aux(transcript, spec, aux, proof['finals'])
    parameters = []
    for ti, (table, part) in enumerate(zip(spec['air']['tables'], proof['tables'])):
        local = copy.deepcopy(transcript)
        mixing, tau = bus.table_start(local, ti, spec['log_rows'][ti])
        point = []
        for rd in part['constraint_rounds']:
            local.commit_ext(rd)
            point.append(local.draw(1, True)[0])
        bus.verify_table_reduction(part, spec, st, transcript, alpha, gamma, ti,
                                   proof['finals'][ti], [roots[ti], aux[ti]])
        exported = circuit['tables'][ti]
        assert exported['table'] == ti
        assert json.loads(json.dumps([mixing, tau, point])) == [exported['mixing'], exported['tau'], exported['point']]
        parameters.append((mixing, tau, point, [bus.ext(v) for v in proof['finals'][ti]]))
    blocks = {b['table']: b for b in circuit['input_blocks']}
    rng = random.Random(20261015)
    capacity = circuit['private_input_capacity']
    samples = [('original', original_inputs), ('zero', [bus.ZERO]*capacity),
               ('one', [bus.ONE]*capacity)]
    for trial in range(4):
        samples.append((f'ext4-random-{trial}', [tuple(rng.randrange(bus.P) for _ in range(4)) for _ in range(capacity)]))
    checks = 0
    for name, inputs in samples:
        values = []
        for index, node in enumerate(nodes):
            kind = node[0]
            if kind == 'const':
                value = bus.ext(node[1:])
            elif kind == 'input':
                assert len(node) == 2 and 0 <= node[1] < capacity
                value = inputs[node[1]]
            else:
                assert kind in ('add', 'sub', 'mul') and len(node) == 3
                assert all(type(i) is int and 0 <= i < index for i in node[1:])
                value = {'add': add, 'sub': sub, 'mul': mul}[kind](values[node[1]], values[node[2]])
            values.append(value)
        total = bus.ZERO
        power = bus.ONE
        for ti, (mixing, tau, point, finals) in enumerate(parameters):
            block = blocks[ti]
            start, width = block['offset'], circuit['tables'][ti]['width']
            current = inputs[start:start+width]
            nxt = inputs[start+block['column_capacity']:start+block['column_capacity']+width]
            expected = bus.weighted(spec, ti, alpha, gamma, finals, mixing, tau, point, current, nxt)
            assert values[circuit['tables'][ti]['output']] == expected, (name, ti)
            total = add(total, mul(power, sub(expected, bus.ext(circuit['tables'][ti]['target']))))
            power = mul(power, bus.ext(circuit['public_batch_rho']))
            checks += 1
        assert values[circuit['root']] == total, name
    report = dict(status='PASS', input_cases=len(samples), independent_table_output_checks=checks,
        batched_output_checks=len(samples), circuit_sha256=hashlib.sha256(raw).hexdigest(),
        scope='Public parameters replayed; original, zero, one and arbitrary Ext4 inputs match independent canonical evaluator.',
        limits=['Finite differential tests, not formal compiler correctness.',
                'Fixed batching coefficient is for resource analysis only, not a security parameter.',
                'No GKR protocol or input-opening proof established.'])
    args.output.write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps(report))


if __name__ == '__main__':
    main()
