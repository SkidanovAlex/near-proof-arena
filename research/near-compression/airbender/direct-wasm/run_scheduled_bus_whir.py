#!/usr/bin/env python3
"""Exercise heterogeneous-height bus commitments against a canonical Lean AIR fixture.

Diagnostic variable-height profile only; no cryptographic security-level claim.
"""
import argparse
from copy import deepcopy
import hashlib
import json
from pathlib import Path
import subprocess
import time

import scheduled_bus_whir as protocol
import folded_prover
import bus_auxiliary as auxiliary
from reference import inspect, evaluate
from run_kernel import PIN


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('airbender', type=Path)
    ap.add_argument('--heavy', default='/data/illia/nearproof-deps/bin/heavy')
    args = ap.parse_args()
    here = Path(__file__).resolve().parent
    research = here.parent.parent
    out = research / 'results'
    repo = args.airbender.resolve()
    assert subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=repo, text=True).strip() == PIN
    subprocess.run(['git', 'diff', '--exit-code', 'HEAD', '--', 'prover', 'cs', 'field',
                    'fft', 'transcript', 'blake2s_u32'], cwd=repo, check=True)
    for name in ('near_scheduled_commitment.rs', 'near_scheduled_whir.rs'):
        src, dst = here / name, repo / 'prover/examples' / name
        if dst.exists() and dst.read_bytes() != src.read_bytes():
            raise ValueError('Different existing example: ' + name)
        dst.write_bytes(src.read_bytes())
    fixture_source = here.parent / 'generic-air/HeterogeneousBusFixture.lean'
    generated = subprocess.run([args.heavy, 'lake', 'env', 'lean', '--run', str(fixture_source)],
                               cwd=research, text=True, capture_output=True, check=True)
    fixture = json.loads(generated.stdout)
    assert fixture['field_modulus'] == auxiliary.P

    def save(name, value):
        path = out / name
        path.write_text(json.dumps(value, indent=2) + '\n')
        return path

    def run(example, *paths):
        with (out / 'scheduled-bus-run.log').open('a') as log:
            subprocess.run([args.heavy, 'cargo', 'run', '-p', 'prover', '--example', example,
                            '--', *map(str, paths)], cwd=repo, stdout=log,
                           stderr=subprocess.STDOUT, check=True)

    save('scheduled-bus-fixture.json', fixture)
    spec = {'air': fixture['air'], 'public': fixture['public'], 'log_rows': fixture['log_rows']}
    save('scheduled-bus-spec.json', spec)
    comparisons = 0
    for case in fixture['cases']:
        for ti, table in enumerate(spec['air']['tables']):
            for ri in range(len(case['rows_by_table'][ti])):
                for ci, expr in enumerate(table['constraints']):
                    assert evaluate(expr, case['rows_by_table'][ti], ri, case['public']) == case['residuals'][ti][ri][ci]
                    comparisons += 1

    timings = {}

    def generate(label, rows_by_table, expected_spec):
        started = time.monotonic()
        source_paths, roots = [], []
        for ti, rows in enumerate(rows_by_table):
            source = save(f'{label}-source-{ti}.json', {'rows': rows})
            commitment = out / f'{label}-source-{ti}-commitment.json'
            run('near_scheduled_commitment', source, commitment)
            source_paths.append(source)
            roots.append(json.loads(commitment.read_text())['root'])
        _, _, alpha, gamma = protocol.begin(expected_spec, roots)
        aux_rows, aux_paths, aux_roots, finals = [], [], [], []
        for ti, (table, rows) in enumerate(zip(expected_spec['air']['tables'], rows_by_table)):
            witness = auxiliary.generate(table, rows, expected_spec['public'], alpha, gamma)
            aux_rows.append(witness['aux_rows'])
            finals.append(witness['finals'])
            flat = [[c for value in row for c in value] for row in witness['aux_rows']]
            source = save(f'{label}-aux-{ti}.json', {'rows': flat})
            commitment = out / f'{label}-aux-{ti}-commitment.json'
            run('near_scheduled_commitment', source, commitment)
            aux_paths.append(source)
            aux_roots.append(json.loads(commitment.read_text())['root'])
        proof, handoffs = folded_prover.prove(expected_spec, roots, rows_by_table, aux_roots, aux_rows, finals, protocol_impl=protocol)
        for ti, table_proof in enumerate(proof['tables']):
            openings = []
            for branch, source in enumerate((source_paths[ti], aux_paths[ti])):
                handoff = save(f'{label}-handoff-{ti}-{branch}.json', handoffs[ti][branch])
                opening = out / f'{label}-opening-{ti}-{branch}.json'
                run('near_scheduled_whir', source, opening, handoff)
                openings.append(json.loads(opening.read_text()))
            table_proof['openings'] = openings
        save(label + '-proof.json', proof)
        save(label + '-statement.json', {'roots': roots})
        timings[label] = time.monotonic() - started
        return proof, roots

    rows = fixture['rows_by_table']
    assert inspect(spec['air'], rows, spec['public'])['accepted']
    proof, roots = generate('scheduled-bus', rows, spec)
    verify_started = time.monotonic()
    assert protocol.verify(proof, spec, roots)
    verify_seconds = time.monotonic() - verify_started
    rejected = []

    def reject(label, candidate, expected_spec=spec, expected_roots=roots):
        try:
            protocol.verify(candidate, expected_spec, expected_roots)
        except (ValueError, KeyError, TypeError, IndexError):
            rejected.append(label)
        else:
            raise AssertionError('Accepted ' + label)

    for ti, table_proof in enumerate(proof['tables']):
        for ri, coefficients in enumerate(table_proof['constraint_rounds']):
            for ci in range(len(coefficients)):
                bad = deepcopy(proof)
                bad['tables'][ti]['constraint_rounds'][ri][ci]['c0']['c0'] ^= 1
                reject(f'table{ti} round{ri} coefficient{ci}', bad)
        for field in ('current_evals', 'next_evals'):
            for ci in range(len(table_proof['shift_reduction'][field])):
                bad = deepcopy(proof)
                bad['tables'][ti]['shift_reduction'][field][ci]['c0']['c0'] ^= 1
                reject(f'table{ti} {field}{ci}', bad)
        for branch in range(2):
            bad = deepcopy(proof)
            bad['tables'][ti]['openings'][branch]['proof']['witness_commitment']['queries'][0]['path'][0][0] ^= 1
            reject(f'table{ti} branch{branch} Merkle path', bad)
        for fi in range(len(proof['finals'][ti])):
            bad = deepcopy(proof)
            bad['finals'][ti][fi]['c0']['c0'] ^= 1
            reject(f'table{ti} final{fi}', bad)
        bad = deepcopy(proof)
        bad['aux_roots'][ti][0] ^= 1
        reject(f'table{ti} auxiliary root', bad)
        bad_roots = deepcopy(roots)
        bad_roots[ti][0] ^= 1
        reject(f'table{ti} original root', proof, expected_roots=bad_roots)
        bad = deepcopy(proof)
        bad['tables'][ti]['openings'].reverse()
        reject(f'table{ti} source/aux branch swap', bad)
    bad = deepcopy(proof)
    bad['tables'].reverse()
    reject('table proof order', bad)
    badspec = deepcopy(spec)
    badspec['public'][5] += 1
    reject('public bus record substitution', proof, badspec)
    badspec = deepcopy(spec)
    badspec['air']['tables'][0]['interactions'][0]['send'] = False
    reject('AIR interaction direction substitution', proof, badspec)

    # A fresh, fully committed witness whose ONLY semantic failure is bus balance.
    bus_case = next(case for case in fixture['cases'] if case['label'] == 'bus-only-invalid')
    diagnostic = inspect(spec['air'], bus_case['rows_by_table'], spec['public'])
    assert diagnostic['violations'] and all(v[0] == 'bus' for v in diagnostic['violations'])
    invalid, invalid_roots = generate('scheduled-bus-invalid', bus_case['rows_by_table'], spec)
    protocol.verify_local(invalid, spec, invalid_roots)
    reject('fresh locally valid bus imbalance', invalid, expected_roots=invalid_roots)

    alternate = next(case for case in fixture['cases'] if case['label'] == 'alternate-public')
    alternate_spec = deepcopy(spec)
    alternate_spec['public'] = alternate['public']
    assert inspect(spec['air'], alternate['rows_by_table'], alternate['public'])['accepted']
    alt, alt_roots = generate('scheduled-bus-alternate', alternate['rows_by_table'], alternate_spec)
    assert protocol.verify(alt, alternate_spec, alt_roots)
    reject('valid proof for another public statement', alt, expected_roots=alt_roots)

    paths = [here / 'folded_prover.py', here / 'scheduled_bus_whir.py', here / 'run_scheduled_bus_whir.py', here / 'verify_whir_scheduled.py',
             here.parent / 'generic-air/bus_auxiliary.py', fixture_source,
             out / 'scheduled-bus-proof.json']
    report = {
        'status': 'PASS', 'honest_bus_proofs_accepted': 2, 'prover_implementation': 'partial-folding',
        'source_lean_residual_comparisons': comparisons,
        'mutations_rejected': len(rejected), 'rejection_labels': rejected,
        'fresh_bus_invalid_local_proofs_accepted': True,
        'fresh_bus_invalid_global_proof_rejected': True,
        'original_roots_before_bus_challenges': True,
        'auxiliary_roots_and_finals_before_constraint_challenges': True,
        'verifier_witness_used': False, 'tables': 2, 'rows_per_table': [len(r) for r in rows],
        'timing_seconds_including_subprocess_startup': timings,
        'honest_verify_seconds': verify_seconds,
        'complete_proof_compact_json_bytes': len(json.dumps(proof, separators=(',', ':')).encode()),
        'opening_only_bincode_bytes': sum(o['bincode_bytes'] for t in proof['tables'] for o in t['openings']),
        'limitations': ['Small heterogeneous-height diagnostic profile, not a full D1 or NEAR proof.',
                        'No 128-bit or post-quantum security claim; toy hash/field/sampling parameters.',
                        'No full Lean verifier refinement or cryptographic protocol composition theorem.',
                        'Recorded JSON size is diagnostic; no production proof-size claim.'],
        'upstream_commit': PIN,
        'sha256': {str(p.relative_to(research)): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}}
    save('scheduled-bus-verified.json', report)
    print(json.dumps(report))


if __name__ == '__main__':
    main()
