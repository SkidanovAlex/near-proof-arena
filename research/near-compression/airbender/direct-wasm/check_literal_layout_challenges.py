"""Captured compiler challenge sweep; not a proof over every transcript."""
import argparse
import copy
import hashlib
import json
import sys
from pathlib import Path


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--reference-dir', required=True)
    ap.add_argument('--fixture', type=Path, required=True)
    ap.add_argument('--output', type=Path, required=True)
    args = ap.parse_args()
    sys.path.insert(0, args.reference_dir)
    import pq384_gkr_bus as bus
    import pq384_gkr_bus_codec as codec
    from pq384_fixed_gkr_layout import fixed_layer_circuit
    from verify_whir_toy import ZERO, ONE, base

    statement = json.loads((args.fixture/'statement.json').read_text())
    proof = json.loads((args.fixture/'proof.json').read_text())
    spec = statement['spec']
    roots = [bytes.fromhex(r) for r in statement['roots']]
    _, alpha, gamma, _, terminals, captured, captured_layout, _, _, _ = codec.prefix(spec, roots, proof)
    cases = []
    # Values are public compiler inputs. Changed cases are not valid proof replays.
    variants = [('captured', None, None), ('rho-one', None, None)]
    for field in ('point', 'mixing', 'tau', 'claim'):
        for label, value in [('zero', ZERO), ('one', ONE)]:
            variants.append((field+'-'+label, field, value))
    fixed_log = captured_layout['input_size'].bit_length()-1
    for name, field, value in variants:
        ts = copy.deepcopy(terminals)
        if field:
            for t in ts:
                t[field] = [value]*len(t[field]) if isinstance(t[field], list) else value
        # Replay rho for the captured case rather than inventing its transcript.
        if name == 'captured':
            circuit = captured
        else:
            circuit = bus.compile_terminal(spec, alpha, gamma, proof['finals'], ts, ONE)
        layout = bus.gkr.layer_circuit(circuit)
        fixed = fixed_layer_circuit(circuit, input_log=fixed_log)
        assert circuit['input_blocks'] == captured['input_blocks']
        assert layout['private_capacity'] == captured_layout['private_capacity']
        assert fixed['input_size'] == 1 << fixed_log
        # Independent evaluation of both layouts on a deterministic nonzero input.
        private = [base((17*i+3) % 101) for i in range(layout['private_capacity'])]
        original_value = bus.gkr.values(layout, private)[-1][layout['root']]
        fixed_value = bus.gkr.values(fixed, private)[-1][fixed['root']]
        assert original_value == fixed_value
        enlarged = fixed_layer_circuit(circuit, input_log=fixed_log+1)
        assert bus.gkr.values(enlarged, private)[-1][enlarged['root']] == original_value
        try:
            fixed_layer_circuit(circuit, input_log=fixed_log-1)
        except ValueError:
            pass
        else:
            raise AssertionError('undersized trusted envelope accepted')
        cases.append(dict(name=name, input_size=layout['input_size'], constants=len(layout['constants']),
                          layers=len(layout['layers']), layer_sizes=[len(x) for x in layout['layers']],
                          input_blocks=circuit['input_blocks'], fixed_input_size=fixed['input_size'],
                          fixed_output_equal=True, enlarged_input_size=enlarged['input_size'],
                          enlarged_output_equal=True, undersized_envelope_rejected=True))
    report = dict(status='PASS', fixture=str(args.fixture),
                  statement_sha256=hashlib.sha256((args.fixture/'statement.json').read_bytes()).hexdigest(),
                  proof_sha256=hashlib.sha256((args.fixture/'proof.json').read_bytes()).hexdigest(),
                  tested_fixed_input_log=fixed_log, cases=cases,
                  observed_input_sizes=sorted({c['input_size'] for c in cases}),
                  observed_layer_counts=sorted({c['layers'] for c in cases}),
                  scope='Compiler metamorphic tests on captured and synthetic public inputs; altered inputs are not accepted transcript samples.',
                  remaining=['No universal fixed-envelope bound or compiler refinement proved.',
                             'Fixed layout helper remains experimental and is not deployed in this proof profile.',
                             'No change to proof bytes or security certification.'])
    args.output.write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps({k:report[k] for k in ('status','observed_input_sizes','observed_layer_counts')}))


if __name__ == '__main__':
    main()
